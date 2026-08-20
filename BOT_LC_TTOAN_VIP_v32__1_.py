#!/usr/bin/env python3
"""
TX Ensemble Tool — Python Backend (v28 - Real WS AutoBet + Exponential Win + Profit Target)
- Kết nối WS game: wss://wtxmd52.tele68.com/txmd5/
- HTTP server: http://localhost:2300
- 6 Logic Engine (L1–L6) + Session Tuner + Adaptive TT1/TT2 Grouping
  · 3 logic cũ: L1/L2/L3 (giữ nguyên công thức)
  · 3 logic mới: L4/L5/L6 (thêm v16)
  · WARMUP: chờ 10 phiên live trước khi bắt đầu dự đoán (chỉ chạy 1 LẦN khi bật tool)
            Sau khi đổi ttoan KHÔNG warmup lại — dự đoán tiếp ngay từ ván kế tiếp.
  · Tune chọn 3 logic mạnh nhất trong 6 → ensemble majority từ top-3
  · Tune kết hợp với session tuner offset (-1/0/+1)
  · BÙ TRỪ LÔ CHÉO ĐÃ XÓA — tool giờ luôn THEO majority thuần
  · Adaptive TT1/TT2 grouping vẫn còn (phân loại case, thống kê)
  · Correlation / pair tracker vẫn còn (thống kê tham khảo)
  · v25: TTOAN switching hoàn toàn dựa trên WR — KHÔNG có interval cố định nào
         ┌─ Mỗi ván có pred_ok → tích lũy vào history_since_swap + tăng bộ đếm
         ├─ Khi đã đủ TTOAN_CHECK_WINDOW (10) ván kể từ lần đổi ttoan:
         │    WR 10 ván cuối ≥ 60% → GIỮ ttoan, KHÔNG reset, tiếp đếm bình thường
         │    WR 10 ván cuối < 40% → ĐỔI ttoan NGAY LẬP TỨC:
         │       · Dùng đúng số ván đã đếm từ lần đổi ttoan trước (vans_since_swap)
         │         để tìm logic tốt nhất trong cửa sổ đó → tune logic
         │       · Reset bộ đếm vans_since_swap = 0, history_since_swap = []
         │       · BỎ các ván đúng liên tiếp đầu history_since_swap mới để tính từ
         │         ván SAI GẦN NHẤT trong 10 ván cuối → ttoan mới được "bù" đúng số
         │         ván đã bỏ trước khi kiểm tra giữ/đổi lần sau.
         │    WR 40%–60% → vùng trung tính, không làm gì, tiếp đếm
         └─ Sau khi đổi ttoan: bộ đếm bắt đầu lại từ 0, lần check tiếp theo
            tính từ ván đầu tiên của ttoan mới (không warmup lại)
  · v33: CONSEC LOSS BAIL — sai liên tiếp 4 ván thật → đổi ttoan ngay lập tức
         (không cần đợi đủ TTOAN_CHECK_WINDOW, ưu tiên cao hơn WR gate)
  · v35: /reloadlogic thêm vào /help admin — admin thấy đủ lệnh
         TTOAN_CONSEC_LOSS_BAIL = 3 (sai liên tiếp 3 ván → đổi ttoan khẩn)
         /reloadlogic reset sạch chuỗi sai liên tiếp, không carry-over
  · v36: TÁCH /reloadlogic và /clearlogic thành 2 lệnh độc lập:
         /reloadlogic → chỉ ép đổi ttoan ngay lập tức (giống khi sai 3 lần),
                        KHÔNG đụng rolling history 9 logic
         /clearlogic  → clear sạch rolling history 9 logic + re-tune từ full history,
                        reset session tuner, adaptive, pending — KHÔNG đổi ttoan
  · v23 FIX: pred_ok được truyền đúng vào logic_tuner_update_result
             → _ttoan_tracker hoạt động chính xác (v22 bị bug: pred_ok=None nên
               tracker không bao giờ được cập nhật → WR check không bao giờ chạy)
- History persistent: lưu file history.json (không giới hạn phiên, lưu mãi mãi)
- Ensemble dùng HIST_WINDOW=1000 phiên gần nhất (có thể chỉnh trong Config)
- Subscribers persistent (subs.json)
- Key system: admin tạo key 1-365 ngày, user nhập key mới dùng được
- Admin chatid: 8764934889 (duy nhất)
- Admin: /newkey <days> [users], /sub, /kick <id>, /ban <id> <days>, /reloadlogic, /clearlogic
- User: /tool <key>, /stop, /status, /help, /autobet, /stopbet, /betstatus
"""
import asyncio, json, os, time, hashlib, re, secrets, string, math, sys, base64, threading
from collections import defaultdict
from datetime import datetime, timezone
from aiohttp import web
import websockets
import aiohttp
try:
    import requests as _requests_lib
    _HAS_REQUESTS = True
except ImportError:
    _requests_lib = None
    _HAS_REQUESTS = False
    print("[WARN] 'requests' library not found — /autobet login will fail. Run: pip install requests")

# ─── AutoLogin & AutoBet (merged from lc79_auto_login) ────────────────────────
MULTI_BET    = 1.98   # hệ số nhân tiền thắng

LOGIN_HEADERS_LC = {
    "Content-Type": "application/json",
    "Accept":       "application/json",
    "User-Agent":   "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    "Origin":       "https://tele68.com",
    "Referer":      "https://tele68.com/",
}

# { chat_id: AutoBetSession }
_auto_bet_sessions: dict = {}

# Per-user pending bet ledger { chat_id: { 'entry': dict|None, 'waiting': bool } }
_auto_bet_pending: dict = {}


def _input_password_cli(prompt="  Password: ") -> str:
    print(prompt, end="", flush=True)
    if sys.platform == "win32":
        import msvcrt
        chars = []
        while True:
            ch = msvcrt.getwch()
            if ch in ("\r", "\n"):   print(); break
            elif ch == "\x08":
                if chars: chars.pop(); print("\b \b", end="", flush=True)
            elif ch == "\x03": raise KeyboardInterrupt
            else: chars.append(ch); print("*", end="", flush=True)
        return "".join(chars)
    else:
        import getpass as _gp; return _gp.getpass("")


async def lc79_auto_login(username: str, password: str) -> tuple:
    """
    Login LC79 bằng aiohttp (async) → trả (jwt, balance, nick_name)
    Trả (None, 0, username) nếu thất bại.
    """
    pw_md5 = hashlib.md5(password.encode()).hexdigest()

    access_token = ""; nick_name = username
    timeout = aiohttp.ClientTimeout(total=12)

    # ── STEP 1: Lấy accessToken + nickName ────────────────────────────────────
    try:
        async with aiohttp.ClientSession(headers=LOGIN_HEADERS_LC) as sess:
            async with sess.get(
                "https://apifo88daigia.tele68.com/api",
                params={"c":"3","un":username,"pw":pw_md5,"cp":"R","cl":"R","pf":"web","at":""},
                timeout=timeout,
            ) as r1:
                print(f"[LC79-LOGIN] STEP1 status={r1.status}")
                if r1.status == 200:
                    g = await r1.json(content_type=None)
                    access_token = g.get("accessToken") or ""
                    sk = g.get("sessionKey") or ""
                    if sk:
                        try:
                            pad      = sk + "=" * (-len(sk) % 4)
                            info_dec = base64.b64decode(pad).decode("utf-8", errors="ignore")
                            m        = re.search(r'"nicknam[eE]"\s*:\s*"([^"]+)"', info_dec, re.I)
                            if m: nick_name = m.group(1)
                        except Exception:
                            pass
                    if nick_name == username:
                        nick_name = g.get("nickName") or g.get("username") or username
    except Exception as e:
        print(f"[LC79-LOGIN STEP1] lỗi: {e}")

    print(f"[LC79-LOGIN] nick={nick_name} | accessToken={'OK' if access_token else 'EMPTY'}")

    # ── STEP 2: POST login → lấy JWT + balance ────────────────────────────────
    body = {
        "username":    username,
        "password":    password,
        "nickName":    nick_name,
        "accessToken": access_token,
        "isLogin":     bool(access_token),
        "money":       0,
    }
    try:
        async with aiohttp.ClientSession(headers=LOGIN_HEADERS_LC) as sess:
            async with sess.post(
                "https://wlb.tele68.com/v1/lobby/auth/login",
                params={"cp":"R","cl":"R","pf":"web","at":""},
                json=body,
                timeout=timeout,
            ) as r:
                print(f"[LC79-LOGIN] STEP2 status={r.status}")
                if r.status != 200:
                    txt = await r.text()
                    print(f"[LC79-LOGIN] STEP2 fail: {txt[:300]}")
                    return None, 0, nick_name
                data = await r.json(content_type=None)
    except Exception as e:
        print(f"[LC79-LOGIN STEP2] lỗi: {e}")
        return None, 0, username

    jwt     = data.get("token")
    remote  = data.get("remoteLoginResp", {})
    balance = remote.get("money", 0)
    nick    = remote.get("nickName", nick_name)

    if not jwt:
        print(f"[LC79-LOGIN] Không có token trong response: {str(data)[:200]}")
        return None, 0, nick

    print(f"[LC79-LOGIN] ✅ {nick} | balance={balance:,}")
    return jwt, balance, nick


async def lc79_place_bet_ws(ws, side: str, amount: int) -> bool:
    """
    v28: Đặt cược qua WebSocket đang kết nối — cùng kết nối với bàn MD5.
    Frame: 42/txmd5,["bet", {"type": "TAI"|"XIU", "amount": <int>}]
    Trả True nếu send ok, False nếu ws lỗi.
    """
    msg = f'42/txmd5,["bet",{{"type":"{side}","amount":{amount}}}]'
    try:
        await ws.send(msg)
        print(f"[LC79-BET] → {msg}")
        return True
    except Exception as e:
        print(f"[LC79-BET] WS send ERR: {e}")
        return False


class AutoBetLedger:
    """Theo dõi balance + lãi/lỗ theo phiên."""
    def __init__(self, start: int, nick: str):
        self.balance   = start
        self.start_bal = start
        self.nick      = nick
        self.rounds    = 0
        self.w = self.l = 0
        self.hist: list = []

    def bet(self, side: str, amount: int) -> dict:
        self.balance -= amount
        self.rounds  += 1
        entry = {"round": self.rounds, "side": side, "amount": amount,
                 "result": None, "pnl": -amount}
        self.hist.append(entry)
        return entry

    def resolve(self, entry: dict, result: str) -> bool:
        entry["result"] = result
        win = entry["side"] == result
        if win:
            payout = math.floor(entry["amount"] * MULTI_BET)
            self.balance += payout
            entry["pnl"] = payout - entry["amount"]
            self.w += 1
        else:
            self.l += 1
        return win

    def net(self) -> int:
        return self.balance - self.start_bal

    def summary_text(self) -> str:
        n = self.net()
        sign = "+" if n >= 0 else ""
        icon = "📈" if n >= 0 else "📉"
        last = self.hist[-10:] if self.hist else []
        streak = "".join("✅" if e["pnl"] > 0 else "❌" for e in last)
        return (
            f"{icon} <b>Tổng kết — {self.nick}</b>\n"
            f"━━━━━━━━━━━━━━\n"
            f"Vốn ban đầu : <b>{self.start_bal:,}</b>\n"
            f"Số dư hiện tại: <b>{self.balance:,}</b>\n"
            f"{sign}Lãi/Lỗ : <b>{sign}{n:,}</b>\n"
            f"Thắng: <b>{self.w}</b> | Thua: <b>{self.l}</b> | Tổng: <b>{self.rounds}</b>\n"
            f"10 ván cuối: {streak if streak else '—'}"
        )


class AutoBetSession:
    """
    State cho 1 user đang chạy auto-cược.
    v28: + profit_target (dừng khi đạt mục tiêu lãi)
    v31: + win_streak_x2  (thắng bao nhiêu ván liên tiếp mới x2 — thay vì x2 ngay lần đầu)
         + loss_streak_reduce / reduced_bet (thua N ván → giảm cược xuống mức reduced_bet)
         + loss_streak_stop / win_streak_cont vẫn còn (pause/resume như v29)
    """
    def __init__(
        self,
        chat_id: int,
        jwt: str,
        ledger: AutoBetLedger,
        base_bet: int,
        martingale: bool,
        double_on_win: bool,       # x2 khi THẮNG
        win_streak_x2: int,        # v31: thắng liên tiếp bao nhiêu ván mới x2 (0=ngay lần đầu)
        reset_on_win: bool,        # reset về base khi thắng?
        double_on_loss: bool,      # x2 khi THUA? (martingale)
        reset_on_loss: bool,       # reset về base khi thua?
        loss_streak_stop: int,     # pause khi thua liên tiếp N ván (0=không)
        win_streak_cont: int,      # resume khi thắng liên tiếp N ván (0=không lọc)
        profit_target: int = 0,    # dừng khi lãi >= target (0=không giới hạn)
        loss_streak_reduce: int = 0,  # v31: thua N ván liên tiếp → giảm cược (0=không)
        reduced_bet: int = 0,         # v31: mức cược giảm xuống khi đủ loss_streak_reduce
    ):
        self.chat_id            = chat_id
        self.jwt                = jwt
        self.ledger             = ledger
        self.base_bet           = base_bet
        self.current_bet        = base_bet
        self.martingale         = martingale
        self.double_on_win      = double_on_win
        self.win_streak_x2      = win_streak_x2      # v31
        self.reset_on_win       = reset_on_win
        self.double_on_loss     = double_on_loss
        self.reset_on_loss      = reset_on_loss
        self.loss_streak_stop   = loss_streak_stop
        self.win_streak_cont    = win_streak_cont
        self.profit_target      = profit_target
        self.loss_streak_reduce = loss_streak_reduce  # v31
        self.reduced_bet        = reduced_bet if reduced_bet > 0 else base_bet  # v31
        self.loss_streak        = 0
        self.win_streak         = 0
        self.active             = True
        self.paused             = False
        self.recovery_wins      = 0
        self.pending_entry      = None
        self._is_reduced        = False  # v31: đang ở chế độ cược giảm

    def on_win(self):
        self.win_streak  += 1
        self.loss_streak  = 0
        if self.paused:
            self.recovery_wins += 1
            return
        # v31: nếu đang ở reduced mode, thắng → về base (thoát reduced)
        if self._is_reduced:
            self._is_reduced = False
            self.current_bet = self.base_bet
            return
        if self.double_on_win:
            # v31: x2 chỉ khi đủ win_streak_x2 ván thắng liên tiếp
            threshold = self.win_streak_x2 if self.win_streak_x2 > 0 else 1
            if self.win_streak >= threshold:
                doubled = min(self.base_bet * 2, self.ledger.balance)
                if self.current_bet < doubled:
                    self.current_bet = doubled
            # chưa đủ streak → giữ nguyên current_bet (không thay đổi)
        elif self.reset_on_win or self.martingale:
            self.current_bet = self.base_bet
            self.win_streak  = 0

    def on_loss(self):
        self.loss_streak += 1
        self.win_streak   = 0
        if self.paused:
            self.recovery_wins = 0
            return
        # v31: kiểm tra giảm cược trước (ưu tiên cao hơn martingale/reset)
        if (self.loss_streak_reduce > 0
                and self.loss_streak >= self.loss_streak_reduce
                and not self._is_reduced):
            self._is_reduced = True
            self.current_bet = max(self.reduced_bet, 1)
            return
        if self.double_on_win:
            # double_on_win mode: thua → reset về base, clear reduced
            self._is_reduced = False
            self.current_bet = self.base_bet
        elif self.double_on_loss or self.martingale:
            self.current_bet = min(self.current_bet * 2, self.ledger.balance)
        elif self.reset_on_loss:
            self.current_bet = self.base_bet

    def should_stop_loss(self) -> bool:
        # v29: không dừng hẳn — chỉ báo cần pause
        return self.loss_streak_stop > 0 and self.loss_streak >= self.loss_streak_stop

    def should_resume(self) -> bool:
        # v29: resume sau khi thua N → thắng N liên tiếp (win_streak_cont)
        if not self.paused:
            return False
        if self.win_streak_cont <= 0:
            return False
        return self.recovery_wins >= self.win_streak_cont

    def should_stop_profit(self) -> bool:
        # v28: dừng khi lãi >= profit_target
        if self.profit_target <= 0:
            return False
        return self.ledger.net() >= self.profit_target

    def status_line(self) -> str:
        n    = self.ledger.net()
        sign = "+" if n >= 0 else ""
        icon = "📈" if n >= 0 else "📉"
        reduce_tag = " 🔻<i>giảm</i>" if self._is_reduced else ""
        return (
            f"{icon} Auto-cược | Ván #{self.ledger.rounds} | "
            f"Cược: <b>{self.current_bet:,}</b>{reduce_tag} | "
            f"Bal: <b>{self.ledger.balance:,}</b> | "
            f"{sign}Lãi/Lỗ: <b>{sign}{n:,}</b>"
        )


# ─── Config ───────────────────────────────────────────────────────────────────
PORT         = 2300
WS_URL       = 'wss://wtxmd52.tele68.com/txmd5/?EIO=4&transport=websocket'
MIN_HIST     = 0      # dự đoán ngay từ phiên đầu tiên (không cần chờ)
MIN_SUPPORT  = 4      # tối thiểu 4 lần match trong bucket → anti-noise
MAX_HISTORY  = 0      # 0 = không giới hạn lưu file (lưu tất cả)
HIST_WINDOW  = 1000   # số phiên gần nhất dùng cho ensemble (có thể chỉnh)
CONF_THRESH  = 0.50   # legacy — không dùng trực tiếp, giữ để compat
CONF_TAI     = 0.50   # ngưỡng conf cho dự đoán TAI (cao hơn vì TAI là base-rate ~53%)
CONF_XIU     = 0.55   # ngưỡng conf cho dự đoán XIU (thấp hơn — vượt base rate là có signal)
MIN_VOTERS   = 3      # tối thiểu 5 model vote mới ra kết quả (anti-noise)
WARMUP_COUNT = 10     # v16: chờ 10 phiên live để tinh chỉnh trước khi dự đoán
LOGIC_TUNE_INTERVAL = 10  # v16: legacy — không dùng trực tiếp nữa (giữ để compat)
# v21: WR-based ttoan switching (thay interval cố định)
TTOAN_WR_HOLD_THRESH  = 0.60   # WR 10 ván ≥ 60% → giữ ttoan, không đổi
TTOAN_WR_SWAP_THRESH  = 0.40   # WR 10 ván < 40% → đổi ttoan ngay lập tức
TTOAN_CHECK_WINDOW    = 10     # số ván gần nhất để tính WR kiểm tra
TTOAN_CONSEC_LOSS_BAIL = 3     # v35: sai liên tiếp 3 ván thật → đổi ttoan khẩn (không cần đủ window)
HISTORY_SAVE_INTERVAL = 1    # lưu file sau mỗi phiên (persistent ngay lập tức)

# ─── Telegram Config ──────────────────────────────────────────────────────────
TG_TOKEN     = '8943843485:AAF9Lhoa6DlGidZWoy8Ok_-fd5qWqau4bSs'
TG_API       = f'https://api.telegram.org/bot{TG_TOKEN}'
ADMIN_ID     = 8764934889          # duy nhất, cứng
ADMIN_USERNAME = '<a href="https://t.me/ddvipro">@ddvipro</a>'  # username admin Telegram

BASE_DIR     = os.environ.get('DATA_DIR', os.path.dirname(os.path.abspath(__file__)))
SUBS_FILE    = os.path.join(BASE_DIR, 'subs.json')      # persistent subscribers
KEYS_FILE    = os.path.join(BASE_DIR, 'keys.json')      # persistent keys
HISTORY_FILE = os.path.join(BASE_DIR, 'history.json')   # persistent history (không giới hạn)
# key_users.json lưu riêng: { chat_id_str: { key, key_exp, name, username, joined, notify } }
# Đây là nguồn truth duy nhất cho quyền truy cập — không bao giờ mất khi bot restart
KEY_USERS_FILE = os.path.join(BASE_DIR, 'key_users.json')

# Bộ đếm để save_history_async không ghi đĩa mỗi phiên
_history_unsaved_count = 0

# { chat_id(int): { 'name': str, 'username': str, 'joined': timestamp, 'key': str, 'key_exp': timestamp, 'notify': bool } }
# notify=True  → đang nhận dự đoán
# notify=False → đã /stop, không nhận nhưng key vẫn hợp lệ, bật lại bằng /tool
tg_subscribers = {}

# { key_str: { 'days': int, 'created': ts, 'expires': ts, 'used_by': chat_id|None,
#              'users': [chat_id, ...], 'max_users': int } }
tg_keys = {}

# { chat_id(int): unban_timestamp }
tg_banned = {}

# key_users: nguồn truth persistent cho "ai đã từng nhập key hợp lệ"
# { chat_id(int): { 'key': str, 'key_exp': ts, 'name': str, 'username': str,
#                   'joined': ts, 'notify': bool } }
# Không bao giờ xóa entry này trừ admin /kick hoặc admin xóa user khỏi key
key_users: dict = {}

tg_offset = 0

# ─── State (shared) ───────────────────────────────────────────────────────────
app_state = {
    'token':        '',
    'ws_task':      None,
    'tg_task':      None,
    'ws_status':    'disconnected',
    'ws_conn':      None,   # v28: live WS object để autobet gửi bet qua cùng kết nối
    'pending_bet':  None,   # v30: {sid, ensemble} chờ state BETTING mới gửi
    'sessions':     {},
    'history':      [],
    'results':      [],
    'current_pred': None,
    'sse_clients':  set(),
    'stats':        {'total': 0, 'tai': 0, 'xiu': 0, 'hoa': 0},
    'live_count':   0,   # số phiên live đã tích từ lúc khởi động (reset mỗi lần chạy)
    'warmup_done':  False,  # v25: True sau khi lần đầu đủ WARMUP_COUNT — không warmup lại sau đổi ttoan
}

# ─── Session Offset Tuner ─────────────────────────────────────────────────────
# Mặc định tool dùng newsession (offset=0), tức sid gốc không +1 hay -1
# Mỗi 10 phiên → test 3 offset: -1, 0, +1 → chọn offset có WR cao nhất
# WR được theo dõi riêng cho từng offset trong rolling window 30 phiên gần nhất
SESSION_TUNE_INTERVAL = 10    # test lại sau mỗi N phiên có dự đoán
SESSION_TUNE_WINDOW   = 30    # WR window để so sánh (phiên gần nhất)

# v16: ngưỡng WR cho flip logic
FLIP_THRESHOLD_LOW  = 0.45   # nếu cả 3 offset WR < 45% → bật flip mode (đảo chiều pred)
FLIP_THRESHOLD_HIGH = 0.50   # nếu bất kỳ 1 offset WR ≥ 50% → tắt flip mode, lock offset đó

# v18: Auto Reversed Newsession
# Sau mỗi SESSION_TUNE_INTERVAL phiên, so sánh:
#   reversed_wr = 1 - best_wr  (WR nếu đảo chiều toàn bộ newsession pred)
#   Nếu reversed_wr > best_normal_wr VÀ reversed_wr >= REVERSE_NEWSESSION_THRESHOLD
#   → bật reversed newsession (đảo chiều pred TRƯỚC flip_mode)
# Tắt khi best_normal_wr >= reversed_wr hoặc normal_wr đạt FLIP_THRESHOLD_HIGH
REVERSE_NEWSESSION_THRESHOLD = 0.55   # reversed WR phải >= 55% mới bật (tránh noise ~50%)

# Trạng thái tuner — tất cả persistent trong RAM (reset khi restart)
_session_tuner = {
    'active_offset':  0,       # offset đang dùng: -1 | 0 | 1
    'since_tune':     0,       # số phiên có pred kể từ lần tune cuối
    'last_tune_at':   0,       # live_count tại lần tune cuối
    # Rolling history của từng offset: list of bool (True=đúng, False=sai), max SESSION_TUNE_WINDOW
    'history': {
        -1: [],
        0:  [],
        1:  [],
    },
    # Snapshot pending: khi có pred, lưu tạm để update_tuner sau khi có kết quả
    # { sess_id: { offset_pred: { -1: 'TAI'/'XIU', 0: ..., 1: ... } } }
    'pending': {},
    # Lần test benchmark gần nhất
    'last_bench': None,   # { -1: wr, 0: wr, 1: wr, winner: offset, at: live_count }
    # v16: flip mode — bật khi cả 3 offset WR đều < FLIP_THRESHOLD_LOW
    # Tắt khi ít nhất 1 offset đạt FLIP_THRESHOLD_HIGH
    'flip_mode':      False,   # True → đảo chiều ensemble pred (TAI↔XIU)
    'flip_since':     0,       # số phiên đã flip (để log)
    # v18: reversed newsession — bật khi reversed_wr > best_normal_wr và >= ngưỡng
    # Đây là bước đảo chiều TRƯỚC flip_mode, áp dụng cho toàn bộ newsession pred
    'reversed_newsession': False,   # True → đảo chiều pred từ newsession (trước flip)
    'reversed_ns_since':   0,       # số phiên đã reversed newsession
    # Rolling history cho reversed newsession (giả định đảo chiều — 1 - kết quả thực)
    # Dùng history offset đang active, đảo bit → không cần history riêng
    'reversed_ns_bench':   None,    # { normal_wr, reversed_wr, at, changed }
}

def _tuner_sid(sess_id: str, offset: int) -> str:
    """Trả về sess_id đã áp offset: str(int(sess_id) + offset)"""
    try:
        return str(int(sess_id) + offset)
    except Exception:
        return sess_id

def _tuner_run_logic_for_offset(sess_id: str, md5h: str, offset: int) -> str | None:
    """
    Chạy 3 logic với sid đã áp offset, trả về ensemble prediction cho offset đó.
    Không cập nhật bất kỳ state nào — chỉ simulate.
    """
    try:
        sid_o = _tuner_sid(sess_id, offset)
        lr    = run_three_logic(sid_o, md5h)
        # Dùng majority đơn giản (không qua cross-comp để tránh nhiễu state)
        return lr['majority']
    except Exception:
        return None

def _tuner_wr(offset: int) -> float | None:
    """WR của offset trong SESSION_TUNE_WINDOW phiên gần nhất."""
    hist = _session_tuner['history'][offset]
    if not hist:
        return None
    return sum(hist) / len(hist)

def tuner_register_pred(sess_id: str, md5h: str):
    """
    Gọi khi có new-session — lưu prediction của cả 3 offset vào pending.
    Đây là dữ liệu để sau khi có kết quả thực, ta biết từng offset đúng/sai không.
    """
    offsets = {}
    for o in (-1, 0, 1):
        offsets[o] = _tuner_run_logic_for_offset(sess_id, md5h, o)
    _session_tuner['pending'][sess_id] = offsets
    # Giữ pending tối đa 200 phiên
    if len(_session_tuner['pending']) > 200:
        oldest = list(_session_tuner['pending'].keys())[0]
        del _session_tuner['pending'][oldest]

def tuner_update_result(sess_id: str, actual: str):
    """
    Gọi khi có session-result — cập nhật rolling history của từng offset.
    Sau đó kiểm tra nếu đã đủ SESSION_TUNE_INTERVAL phiên → chạy tune.
    """
    pend = _session_tuner['pending'].pop(sess_id, None)
    if not pend:
        return

    # Cập nhật history từng offset
    for o in (-1, 0, 1):
        pred = pend.get(o)
        if pred is None:
            continue
        is_ok = (pred == actual)
        hist  = _session_tuner['history'][o]
        hist.append(is_ok)
        if len(hist) > SESSION_TUNE_WINDOW:
            hist.pop(0)

    # Tăng bộ đếm
    _session_tuner['since_tune'] += 1

    # Trigger tune sau mỗi SESSION_TUNE_INTERVAL phiên
    if _session_tuner['since_tune'] >= SESSION_TUNE_INTERVAL:
        _run_session_tune()

def _run_session_tune():
    """
    So sánh WR của 3 offset → chọn offset tốt nhất làm active.
    v16: nếu cả 3 WR < FLIP_THRESHOLD_LOW → bật flip_mode (đảo chiều pred).
         Khi flip_mode và ít nhất 1 offset đạt FLIP_THRESHOLD_HIGH → tắt flip, lock offset đó.
    Chỉ chạy khi đủ dữ liệu (ít nhất 5 phiên trong window của mỗi offset).
    """
    _session_tuner['since_tune'] = 0

    wrs = {}
    for o in (-1, 0, 1):
        hist = _session_tuner['history'][o]
        if len(hist) >= 5:
            wrs[o] = sum(hist) / len(hist)
        else:
            wrs[o] = None

    # Cần ít nhất offset=0 có data để quyết định
    valid = {o: w for o, w in wrs.items() if w is not None}
    if not valid:
        print("[TUNER] Chưa đủ data để tune — giữ offset hiện tại")
        return

    best_offset = max(valid, key=lambda o: valid[o])
    old_offset  = _session_tuner['active_offset']
    old_flip    = _session_tuner['flip_mode']
    _session_tuner['active_offset'] = best_offset

    # ── v16: Flip mode evaluation ──────────────────────────────────────────
    best_wr = valid[best_offset]

    if _session_tuner['flip_mode']:
        # Đang flip → kiểm tra xem có offset nào vượt HIGH threshold chưa
        if best_wr >= FLIP_THRESHOLD_HIGH:
            _session_tuner['flip_mode']  = False
            _session_tuner['flip_since'] = 0
            print(f"[TUNER] ✅ Flip mode TẮT — offset{best_offset:+d} WR={best_wr*100:.1f}% ≥ {FLIP_THRESHOLD_HIGH*100:.0f}% → LOCK & THEO")
        else:
            _session_tuner['flip_since'] += 1
            print(f"[TUNER] 🔄 Flip mode vẫn BẬT — best WR={best_wr*100:.1f}% chưa đạt {FLIP_THRESHOLD_HIGH*100:.0f}%")
    else:
        # Chưa flip → kiểm tra xem cả 3 có đều dưới LOW threshold không
        all_low = all(w < FLIP_THRESHOLD_LOW for w in valid.values())
        if all_low:
            _session_tuner['flip_mode']  = True
            _session_tuner['flip_since'] = 0
            print(f"[TUNER] ⚠️ Flip mode BẬT — cả 3 offset WR đều < {FLIP_THRESHOLD_LOW*100:.0f}% → ĐẢO CHIỀU pred")

    # ── v18: Reversed Newsession evaluation ───────────────────────────────
    # Dùng history của best_offset để tính reversed WR
    old_rev_ns    = _session_tuner['reversed_newsession']
    best_hist     = _session_tuner['history'][best_offset]
    normal_wr     = valid.get(best_offset)     # đã tính ở trên
    reversed_wr   = (1.0 - normal_wr) if normal_wr is not None else None

    if normal_wr is not None and reversed_wr is not None:
        if _session_tuner['reversed_newsession']:
            # Đang reversed → tắt nếu normal_wr >= reversed_wr hoặc normal đạt FLIP_THRESHOLD_HIGH
            if normal_wr >= reversed_wr or normal_wr >= FLIP_THRESHOLD_HIGH:
                _session_tuner['reversed_newsession'] = False
                _session_tuner['reversed_ns_since']   = 0
                print(f"[TUNER] ✅ Reversed Newsession TẮT — normal_wr={normal_wr*100:.1f}% ≥ reversed={reversed_wr*100:.1f}%")
            else:
                _session_tuner['reversed_ns_since'] += 1
                print(f"[TUNER] 🔃 Reversed Newsession vẫn BẬT — normal={normal_wr*100:.1f}% < reversed={reversed_wr*100:.1f}%")
        else:
            # Chưa reversed → bật nếu reversed_wr > normal_wr VÀ >= ngưỡng
            if reversed_wr > normal_wr and reversed_wr >= REVERSE_NEWSESSION_THRESHOLD:
                _session_tuner['reversed_newsession'] = True
                _session_tuner['reversed_ns_since']   = 0
                print(f"[TUNER] ⚡ Reversed Newsession BẬT — reversed_wr={reversed_wr*100:.1f}% > normal={normal_wr*100:.1f}% ≥ {REVERSE_NEWSESSION_THRESHOLD*100:.0f}%")

    _session_tuner['reversed_ns_bench'] = {
        'normal_wr':   round(normal_wr * 100, 1)   if normal_wr   is not None else None,
        'reversed_wr': round(reversed_wr * 100, 1) if reversed_wr is not None else None,
        'active':      _session_tuner['reversed_newsession'],
        'changed':     _session_tuner['reversed_newsession'] != old_rev_ns,
        'at':          app_state['live_count'],
    }

    bench = {
        'wr': {str(o): (round(w * 100, 1) if w is not None else None) for o, w in wrs.items()},
        'winner':    best_offset,
        'at':        app_state['live_count'],
        'changed':   best_offset != old_offset,
        'flip_mode': _session_tuner['flip_mode'],
        'flip_changed': _session_tuner['flip_mode'] != old_flip,
        # v18
        'reversed_newsession': _session_tuner['reversed_newsession'],
        'reversed_ns_changed': _session_tuner['reversed_newsession'] != old_rev_ns,
        'normal_wr':   round(normal_wr * 100, 1)   if normal_wr   is not None else None,
        'reversed_wr': round(reversed_wr * 100, 1) if reversed_wr is not None else None,
    }
    _session_tuner['last_bench'] = bench

    wr_str = '  '.join(f"offset{o:+d}={round(w*100,1):.1f}%" if w else f"offset{o:+d}=—" for o, w in sorted(wrs.items()))
    changed_tag = f"  ← CHANGED {old_offset:+d} → {best_offset:+d}" if best_offset != old_offset else "  (no change)"
    flip_tag = f"  🔄 FLIP={'ON' if _session_tuner['flip_mode'] else 'OFF'}" if _session_tuner['flip_mode'] != old_flip else ""
    rev_ns_tag = f"  ⚡ REV-NS={'ON' if _session_tuner['reversed_newsession'] else 'OFF'}" if _session_tuner['reversed_newsession'] != old_rev_ns else ""
    print(f"[TUNER] Tune @ live#{app_state['live_count']} | {wr_str} | winner={best_offset:+d}{changed_tag}{flip_tag}{rev_ns_tag}")

def tuner_get_active_sid(sess_id: str) -> str:
    """Trả về sess_id đã áp active_offset để dùng khi tính logic."""
    return _tuner_sid(sess_id, _session_tuner['active_offset'])


# ─── Started Users (để broadcast đến tất cả user đã /start) ─────────────────
STARTED_USERS_FILE = os.path.join(BASE_DIR, 'started_users.json')
started_users: set = set()

def load_started_users():
    global started_users
    try:
        with open(STARTED_USERS_FILE) as f:
            data = json.load(f)
            started_users = set(data)
            print(f"[STARTED] Loaded {len(started_users)} user đã /start")
    except Exception:
        started_users = set()

def save_started_users():
    try:
        with open(STARTED_USERS_FILE, 'w') as f:
            json.dump(list(started_users), f)
    except Exception as e:
        print(f"[STARTED SAVE ERR] {e}")

# ─── History: Persistent file ────────────────────────────────────────────────
def load_history():
    """Load toàn bộ history từ file vào RAM. Không giới hạn số phiên lưu."""
    global _history_unsaved_count
    try:
        with open(HISTORY_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        hist = data if isinstance(data, list) else []
        # Validate từng entry: phải có sess, md5, result
        valid = [h for h in hist if h.get('sess') and h.get('md5') and h.get('result') in ('TAI', 'XIU')]
        app_state['history'] = valid
        _history_unsaved_count = 0
        print(f"[HISTORY] Loaded {len(valid)} phiên từ {HISTORY_FILE}")
        if len(valid) >= HIST_WINDOW:
            print(f"[HISTORY] Ensemble sẽ dùng {HIST_WINDOW} phiên gần nhất (HIST_WINDOW)")
    except FileNotFoundError:
        app_state['history'] = []
        print(f"[HISTORY] File chưa tồn tại — bắt đầu sạch, sẽ tạo {HISTORY_FILE}")
    except Exception as e:
        app_state['history'] = []
        print(f"[HISTORY] Load lỗi ({e}) — bắt đầu sạch")

def _save_history_sync():
    """Ghi toàn bộ history xuống file (chạy trong thread pool để không block event loop)."""
    try:
        tmp = HISTORY_FILE + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(app_state['history'], f, ensure_ascii=False, separators=(',', ':'))
        os.replace(tmp, HISTORY_FILE)   # atomic rename
    except Exception as e:
        print(f"[HISTORY SAVE ERR] {e}")

async def save_history_async(force: bool = False):
    """
    Lưu history xuống file.
    - Ghi sau mỗi HISTORY_SAVE_INTERVAL phiên (không ghi từng phiên để giảm I/O)
    - force=True → ghi ngay (dùng khi /clear hoặc shutdown)
    """
    global _history_unsaved_count
    _history_unsaved_count += 1
    if force or _history_unsaved_count >= HISTORY_SAVE_INTERVAL:
        _history_unsaved_count = 0
        loop = asyncio.get_event_loop()
        await loop.run_in_executor(None, _save_history_sync)
        print(f"[HISTORY] Saved {len(app_state['history'])} phiên → {HISTORY_FILE}")

def get_history_window():
    """Lấy HIST_WINDOW phiên gần nhất từ history để dùng cho ensemble."""
    h = app_state['history']
    if len(h) <= HIST_WINDOW:
        return h
    return h[-HIST_WINDOW:]

# ─── Subscribers + Keys persistence ──────────────────────────────────────────
def _now_ts():
    return int(time.time())

def load_subs_keys():
    global tg_subscribers, tg_keys, tg_banned, key_users

    # --- 1. Load keys.json ---
    try:
        with open(KEYS_FILE) as f:
            tg_keys = json.load(f)
            print(f"[KEYS] Loaded {len(tg_keys)} keys")
    except Exception:
        pass

    # --- 2. Load key_users.json (nguồn truth) ---
    try:
        with open(KEY_USERS_FILE) as f:
            raw = json.load(f)
            key_users = {}
            for k, v in raw.items():
                try:
                    cid = int(k)
                except ValueError:
                    continue
                # v27 FIX: notify default phải là False (user phải /tool lại sau restart)
                # NHƯNG nếu notify=True đã được lưu → giữ nguyên, restore subscriber
                if 'notify' not in v:
                    v['notify'] = False
                key_users[cid] = v
            print(f"[KEY_USERS] Loaded {len(key_users)} registered users")
    except Exception as e:
        print(f"[KEY_USERS] Load error: {e}")

    # --- 3. Load banned từ subs.json ---
    try:
        with open(SUBS_FILE) as f:
            data = json.load(f)
            tg_banned = {int(k): v for k, v in data.get('banned', {}).items()}
            print(f"[SUBS] Loaded {len(tg_banned)} banned entries")
    except Exception:
        pass

    # --- 4. Rebuild tg_subscribers từ key_users ---
    # Những user có notify=True VÀ key còn hạn → auto-restore vào subscribers
    now = _now_ts()
    restored = 0
    skipped_expired = 0
    skipped_notify  = 0
    for cid, info in key_users.items():
        key_exp = info.get('key_exp', 0)
        notify  = info.get('notify', False)  # v27 FIX: default False
        # Admin không cần key_exp
        if cid == ADMIN_ID:
            if notify:
                tg_subscribers[cid] = {
                    'name':     info.get('name', 'Admin'),
                    'username': info.get('username', ''),
                    'joined':   info.get('joined', now),
                    'key':      info.get('key', ''),
                    'key_exp':  key_exp,
                    'notify':   True,
                }
                restored += 1
            continue
        # Key hết hạn → skip (user phải /key lại)
        if not key_exp or now > key_exp:
            skipped_expired += 1
            continue
        # notify=False → skip (user phải /tool lại)
        if not notify:
            skipped_notify += 1
            continue
        tg_subscribers[cid] = {
            'name':     info.get('name', ''),
            'username': info.get('username', ''),
            'joined':   info.get('joined', now),
            'key':      info.get('key', ''),
            'key_exp':  key_exp,
            'notify':   True,
        }
        restored += 1
    print(f"[SUBS] Auto-restored {restored} active subscribers "
          f"(skipped: {skipped_expired} expired, {skipped_notify} notify=False)")

def save_subs():
    """Chỉ lưu banned list — subscribers được restore từ key_users khi bot restart"""
    try:
        data = {'banned': {str(k): v for k, v in tg_banned.items()}}
        with open(SUBS_FILE, 'w') as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception as e:
        print(f"[SUBS SAVE ERR] {e}")

def save_key_users():
    """Lưu key_users.json — nguồn truth cho quyền truy cập, persistent qua restart"""
    try:
        with open(KEY_USERS_FILE, 'w') as f:
            json.dump({str(k): v for k, v in key_users.items()}, f, ensure_ascii=False)
    except Exception as e:
        print(f"[KEY_USERS SAVE ERR] {e}")

def save_keys():
    try:
        with open(KEYS_FILE, 'w') as f:
            json.dump(tg_keys, f, ensure_ascii=False)
    except Exception as e:
        print(f"[KEYS SAVE ERR] {e}")

def gen_key(days: int, max_users: int = 1) -> str:
    """Tạo key ngẫu nhiên 12 ký tự dạng XXXX-XXXX-XXXX
    max_users: số người tối đa có thể dùng key này (1-100)
    """
    chars = string.ascii_uppercase + string.digits
    raw = ''.join(secrets.choice(chars) for _ in range(12))
    key = f"{raw[:4]}-{raw[4:8]}-{raw[8:]}"
    now = _now_ts()
    max_users = max(1, min(100, int(max_users)))
    tg_keys[key] = {
        'days': days, 'created': now,
        'expires': now + days * 86400,
        'used_by': None,        # legacy: first user (backward compat)
        'users': [],            # list of chat_id đã dùng
        'max_users': max_users, # giới hạn số người
    }
    save_keys()
    return key

def is_banned(chat_id: int) -> bool:
    if chat_id not in tg_banned:
        return False
    if tg_banned[chat_id] == -1:  # permanent
        return True
    if _now_ts() < tg_banned[chat_id]:
        return True
    # unban expired
    del tg_banned[chat_id]
    save_subs()
    return False

def validate_key(key: str, chat_id: int) -> tuple[bool, str]:
    """Returns (ok, message)"""
    k = tg_keys.get(key.upper().strip())
    if not k:
        return False, "❌ Key không tồn tại."
    if _now_ts() > k['expires']:
        return False, "❌ Key đã hết hạn."

    # Support cả format cũ (used_by) lẫn mới (users list)
    users_list = k.get('users', [])
    max_users  = k.get('max_users', 1)

    # Migrate từ format cũ nếu cần
    if not users_list and k.get('used_by') is not None:
        users_list = [k['used_by']]
        k['users'] = users_list

    # Nếu user này đã dùng key → cho phép (gia hạn)
    if chat_id in users_list:
        return True, "✅ Key hợp lệ."

    # Kiểm tra còn slot không
    if len(users_list) >= max_users:
        return False, f"❌ Key đã đạt giới hạn {max_users} người dùng."

    return True, "✅ Key hợp lệ."

def get_user_info(msg: dict) -> dict:
    chat = msg.get('chat', {})
    frm  = msg.get('from', {})
    name = frm.get('first_name', '') + (' ' + frm.get('last_name', '') if frm.get('last_name') else '')
    return {
        'name':     name.strip() or 'Unknown',
        'username': frm.get('username', ''),
        'chat_id':  chat.get('id'),
    }

# ─── 3-Logic Engine (từ HTML Vote Combo #21) ─────────────────────────────────
#
#  L1: K = |(X + 11) max (Y − 5)| ^ (Z ÷ 14)    chẵn→TÀI / lẻ→XỈU
#  L2: K = |(X + 13) ÷ (Y − 14)| × (Z min 8)    chẵn→XỈU / lẻ→TÀI
#  L3: K = |(X − 14) + (Y ÷ 9)| ÷ (Z mod 14)    chẵn→XỈU / lẻ→TÀI
#
#  X  = tổng chữ số session (sess+1 trước khi tính)
#  Y  = MD5[6:8] parsed as hex (byte index 3 trong 16-byte, tức char 6-7)
#  Z  = MD5[30:32] parsed as hex (byte index 15, tức char 30-31)
#
#  Vote → 4 trường hợp → 2 nhóm:
#    TT1: 3-0 đồng thuận  HOẶC  L2+L3 đồng thuận  → theo đa số
#    TT2: L1+L2 đồng thuận  HOẶC  L1+L3 đồng thuận → bẻ (thiểu số) khi TT1 đang active
#
#  Bẻ cầu state machine:
#    - Default: TT1 active (theo đa số của TT1-cases)
#    - TT1 sai 2 lần liên tiếp → switch sang TT2 active (theo đa số TT2-cases, không bẻ nữa)
#    - TT2 sai 2 lần liên tiếp → switch về TT1 active
# ─────────────────────────────────────────────────────────────────────────────

# ─── Cross-compensation: ĐÃ XÓA (v15) ───────────────────────────────────────
# Bù trừ lô chéo TT1/TT2 đã được gỡ bỏ — tool giờ luôn THEO majority thuần.
# Correlation tracker / pair tracker / adaptive grouping vẫn còn để thống kê.

# ─── Adaptive TT1/TT2 grouping ───────────────────────────────────────────────
# Mặc định: TT1 = {3-0, L2L3}  /  TT2 = {L1L2, L1L3}  (hardcode cũ)
# Sau 10 ván đầu → recompute dựa trên co-correct rate của 4 case
# Structure:
#   TT1 = set of case names hay đúng cùng nhau
#   TT2 = set còn lại (bù trừ: khi TT1 sai → TT2 hay đúng)
ADAPTIVE_WINDOW    = 10        # số ván để recompute (tính từ results có pred_ok)
_adaptive_groups   = {
    'TT1': {'3-0', 'L2L3'},    # default
    'TT2': {'L1L2', 'L1L3'},   # default
    'computed_at': 0,           # số ván đã xử lý lần cuối recompute
    'source': 'default',        # 'default' | 'adaptive'
}

# Per-phiên snapshot để recompute — lưu (case_type, pred_ok) cho mỗi ván có dự đoán
_adaptive_history = []   # list of {'case': str, 'ok': bool}

def recompute_adaptive_groups():
    """
    Phân tích ADAPTIVE_WINDOW ván gần nhất trong _adaptive_history.

    Thuật toán:
    1. Với mỗi cặp case (6 cặp từ 4 case), đếm số phiên cả 2 cùng đúng (đồng pha)
       so với số phiên 1 đúng 1 sai (ngược pha).
       - Nhưng vì mỗi phiên chỉ có 1 case → dùng proxy: đếm số ván hai case
         cùng OK (true trong window gần nhau).
       - Thực tế mỗi phiên có ĐÚNG 1 case → không thể 2 case cùng xảy ra một phiên.
       - Nên mình dùng cách khác: tính WR (win rate) của từng case riêng lẻ,
         rồi tìm 2 case có WR cao nhất → nhóm thành TT1.
         TT2 = 2 case còn lại.
         Khi TT1 sai → TT2 hay đúng vì TT1 gồm case "đang tốt", TT2 gồm case "phần bù".

    Điều kiện bù trừ thực sự:
    - TT1 = 2 case có WR cao nhất trong window
    - TT2 = 2 case còn lại
    → Khi TT1 case xảy ra và active=TT1, ta THEO (đa số).
      Khi TT2 case xảy ra và active=TT1, ta BẺ (thiểu số) → vì TT2 là phần bù.

    Nếu data quá ít (< 4 phiên tổng) → giữ nguyên default.
    """
    global _adaptive_groups

    window = _adaptive_history[-ADAPTIVE_WINDOW:]
    if len(window) < 4:
        return   # quá ít data

    # Đếm ok/total theo case
    case_stats = {}
    for entry in window:
        c = entry['case']
        if c not in case_stats:
            case_stats[c] = {'ok': 0, 'total': 0}
        case_stats[c]['total'] += 1
        if entry['ok']:
            case_stats[c]['ok'] += 1

    ALL_CASES = ['3-0', 'L2L3', 'L1L2', 'L1L3']

    # Tính WR cho từng case — case chưa xuất hiện → WR = 0.5 (neutral)
    def wr(c):
        s = case_stats.get(c)
        if not s or s['total'] == 0:
            return 0.5
        return s['ok'] / s['total']

    # Sắp xếp 4 case theo WR giảm dần
    ranked = sorted(ALL_CASES, key=wr, reverse=True)

    # TT1 = top 2 case có WR cao nhất
    # TT2 = bottom 2 case (bù trừ — khi TT1 sai thì TT2 hay đúng hơn)
    new_tt1 = set(ranked[:2])
    new_tt2 = set(ranked[2:])

    old_tt1 = _adaptive_groups['TT1']
    changed = new_tt1 != old_tt1

    _adaptive_groups['TT1']        = new_tt1
    _adaptive_groups['TT2']        = new_tt2
    _adaptive_groups['computed_at'] = len(_adaptive_history)
    _adaptive_groups['source']      = 'adaptive'

    wr_lines = '  '.join(f"{c}={wr(c)*100:.0f}%" for c in ranked)
    print(f"[ADAPTIVE] Recompute @ {len(_adaptive_history)} ván")
    print(f"[ADAPTIVE] WR: {wr_lines}")
    print(f"[ADAPTIVE] TT1={sorted(new_tt1)}  TT2={sorted(new_tt2)}"
          + ("  ← CHANGED" if changed else "  (no change)"))

def get_case_group(case_type: str) -> str:
    """Tra group của case_type theo _adaptive_groups hiện tại."""
    if case_type in _adaptive_groups['TT1']:
        return 'TT1'
    return 'TT2'

def _safe_div(a, b):
    return a / b if b != 0 else 0

def _calc_XYZ(sess_plus1, md5h):
    X = sum(int(c) for c in str(sess_plus1) if c.isdigit())
    Y = int(md5h[6:8], 16)
    Z = int(md5h[30:32], 16)
    return X, Y, Z

def _run_logic_L1(X, Y, Z):
    # L1: K = |(X + 11) max (Y − 5)| ^ (Z ÷ 14)  chẵn→TÀI / lẻ→XỈU
    # Y=MD5[6]  Z=MD5[30]
    inner = max(X + 11, Y - 5)
    z_div = _safe_div(Z, 14)
    K = int(abs(inner) ** z_div) if z_div != 0 else int(abs(inner))
    return 'TAI' if K % 2 == 0 else 'XIU'

def _run_logic_L2(X, Y, Z):
    # L2: K = |(X + 13) ÷ (Y − 14)| × (Z min 8)  chẵn→XỈU / lẻ→TÀI
    # Y=MD5[6]  Z=MD5[30]
    inner = _safe_div(X + 13, Y - 14)
    K = int(abs(inner) * min(Z, 8))
    return 'XIU' if K % 2 == 0 else 'TAI'

def _run_logic_L3(X, Y, Z):
    # L3: K = |(X − 14) + (Y ÷ 9)| ÷ (Z mod 14)  chẵn→XỈU / lẻ→TÀI
    # Y=MD5[6]  Z=MD5[30]
    inner = (X - 14) + _safe_div(Y, 9)
    K = int(abs(_safe_div(inner, Z % 14)))
    return 'XIU' if K % 2 == 0 else 'TAI'

# ─── v16: 3 Logic Mới (L4 / L5 / L6) ────────────────────────────────────────
# Y = MD5[6:8] hex  (index byte 3 → char 6-7)
# Z = MD5[30:32] hex (index byte 15 → char 30-31)
#
# L4: K = |(X + 7) min (Y + 14)| ÷ (Z ÷ 12)   chẵn→TÀI / lẻ→XỈU
# L5: K = |(X mod 11) ÷ (Y ÷ 10)| × (Z mod 11)  chẵn→TÀI / lẻ→XỈU
# L6: K = |(X mod 10) − (Y × 10)| ÷ (Z ÷ 10)   chẵn→XỈU / lẻ→TÀI

def _run_logic_L4(X, Y, Z):
    # L4: K = |(X + 7) min (Y + 14)| ÷ (Z ÷ 12)  chẵn→TÀI / lẻ→XỈU
    inner = min(X + 7, Y + 14)
    z_div = _safe_div(Z, 12)
    K = int(abs(_safe_div(inner, z_div))) if z_div != 0 else int(abs(inner))
    return 'TAI' if K % 2 == 0 else 'XIU'

def _run_logic_L5(X, Y, Z):
    # L5: K = |(X mod 11) ÷ (Y ÷ 10)| × (Z mod 11)  chẵn→TÀI / lẻ→XỈU
    y_div = _safe_div(Y, 10)
    inner = _safe_div(X % 11, y_div)
    K = int(abs(inner) * (Z % 11))
    return 'TAI' if K % 2 == 0 else 'XIU'

def _run_logic_L6(X, Y, Z):
    # L6: K = |(X mod 10) − (Y × 10)| ÷ (Z ÷ 10)  chẵn→XỈU / lẻ→TÀI
    inner = (X % 10) - (Y * 10)
    z_div = _safe_div(Z, 10)
    K = int(abs(_safe_div(inner, z_div))) if z_div != 0 else int(abs(inner))
    return 'XIU' if K % 2 == 0 else 'TAI'

# ─── v32: 3 Logic Mới (L7 / L8 / L9) ────────────────────────────────────────
# L7: K = |(X^5) ÷ (Y × 5)| × (Z ÷ 12)
#     Y=MD5[0..1]  Z=MD5[20..21]   chẵn→XỈU / lẻ→TÀI
#
# L8: K = |(X + 1) − (Y ÷ 3)| min (Z ÷ 7)
#     Y=MD5[6..7]  Z=MD5[30..31]   chẵn→TÀI / lẻ→XỈU
#
# L9: K = |(X − 7) ÷ (Y × 6)| × (Z + 15)
#     Y=MD5[6..7]  Z=MD5[30..31]   chẵn→XỈU / lẻ→TÀI

def _run_logic_L7(X, md5h):
    # L7: K = |(X^5) ÷ (Y × 5)| × (Z ÷ 12)
    # Y=MD5[0..1]  Z=MD5[20..21]  chẵn→XỈU / lẻ→TÀI
    Y = int(md5h[0:2], 16)
    Z = int(md5h[20:22], 16)
    y_mul = Y * 5
    inner = _safe_div(X ** 5, y_mul)
    z_div = _safe_div(Z, 12)
    K = int(abs(inner) * z_div)
    return 'XIU' if K % 2 == 0 else 'TAI'

def _run_logic_L8(X, md5h):
    # L8: K = |(X + 1) − (Y ÷ 3)| min (Z ÷ 7)
    # Y=MD5[6..7]  Z=MD5[30..31]  chẵn→TÀI / lẻ→XỈU
    Y = int(md5h[6:8], 16)
    Z = int(md5h[30:32], 16)
    inner = (X + 1) - _safe_div(Y, 3)
    z_div = _safe_div(Z, 7)
    K = int(abs(min(abs(inner), z_div)))
    return 'TAI' if K % 2 == 0 else 'XIU'

def _run_logic_L9(X, md5h):
    # L9: K = |(X − 7) ÷ (Y × 6)| × (Z + 15)
    # Y=MD5[6..7]  Z=MD5[30..31]  chẵn→XỈU / lẻ→TÀI
    Y = int(md5h[6:8], 16)
    Z = int(md5h[30:32], 16)
    y_mul = Y * 6
    inner = _safe_div(X - 7, y_mul)
    K = int(abs(inner) * (Z + 15))
    return 'XIU' if K % 2 == 0 else 'TAI'

# ─── v32: Logic Tuner — chọn top-3 trong 9 logic + BẺ CHIỀU khi reversed WR cao hơn ──
# Sau WARMUP_COUNT phiên, mỗi LOGIC_TUNE_INTERVAL phiên:
#   → đánh giá WR của từng logic (L1–L9) trên rolling window 30 phiên gần nhất
#   → tính thêm reversed WR = 1 - WR (nếu đảo chiều pred thì WR bao nhiêu?)
#   → chọn 3 "slot" có effective WR cao nhất — có thể là normal hoặc reversed
#   → logic bị bẻ sẽ đảo pred khi dùng trong ensemble
# BẺ ĐK: reversed_wr > REVERSE_THRESHOLD và reversed_wr > best_normal_wr_in_top3
# Mặc định ban đầu: dùng L1+L2+L3 (giống v15/v16)
# v32: pool mở rộng từ 6 → 9 logic (thêm L7/L8/L9)
LOGIC_TUNE_WINDOW    = 30    # rolling window để tính WR từng logic
REVERSE_THRESHOLD    = 0.55  # ngưỡng reversed WR tối thiểu để bẻ (tránh noise)

_logic_tuner = {
    'active_logics':   ['L1', 'L2', 'L3'],  # top-3 đang dùng
    'reversed_logics': set(),                # tên logic đang bị bẻ chiều
    'since_tune':    0,                    # phiên có pred kể từ lần tune cuối
    'total_preds':   0,                    # tổng phiên có pred (để biết đã qua warmup chưa)
    # Rolling history per-logic: list of bool (True=đúng, False=sai)
    'history': {
        'L1': [], 'L2': [], 'L3': [],
        'L4': [], 'L5': [], 'L6': [],
        'L7': [], 'L8': [], 'L9': [],   # v32: 3 logic mới
    },
    # Snapshot pending: lưu pred của tất cả 9 logic cho phiên chưa có kết quả
    # { sess_id: { 'L1': 'TAI'/'XIU', ..., 'L9': ... } }
    'pending': {},
    # Benchmark gần nhất
    'last_bench': None,  # { wr: {L1:%, ...}, top3: [...], at: live_count }
}

# v22: Ttoan WR Tracker — đổi ttoan hoàn toàn dựa trên WR, không có interval cố định
# Quy trình:
#   - Mỗi ván có pred_ok, tăng vans_since_swap và append vào history_since_swap
#   - Khi history_since_swap đã có đủ TTOAN_CHECK_WINDOW ván:
#       · Lấy TTOAN_CHECK_WINDOW ván cuối → tính recent_wr
#       · recent_wr ≥ TTOAN_WR_HOLD_THRESH (60%) → GIỮ ttoan, KHÔNG reset, tiếp đếm
#       · recent_wr < TTOAN_WR_SWAP_THRESH (40%) → ĐỔI ttoan ngay:
#           - Gọi _run_logic_tune_with_window(vans_since_swap) để tune logic
#             dùng đúng số ván đã đếm kể từ khi ttoan đổi trước
#           - Reset vans_since_swap = 0, history_since_swap = []
#           - Reset _logic_tuner['since_tune'] = 0
#       · 40% ≤ recent_wr < 60% → không làm gì (vùng trung tính)
_ttoan_tracker = {
    'vans_since_swap':    0,      # tổng ván kể từ khi ttoan đổi lần cuối (reset về 0 khi đổi)
    'history_since_swap': [],     # list bool (True=đúng) tích lũy từ khi ttoan đổi (không cắt)
    'last_swap_at_live':  0,      # live_count tại thời điểm đổi ttoan lần cuối
    'swap_count':         0,      # tổng số lần đã đổi ttoan
    'last_swap_reason':   None,   # 'wr_low' | 'init'
    # v25: sau khi đổi ttoan, pre_trim_count = số ván bị bỏ (ván đúng trước ván sai gần nhất
    #      trong 10 ván cuối của lần trước). Ttoan mới sẽ được "bù" đúng số ván này trước
    #      khi bắt đầu quyết định giữ/đổi, bằng cách khởi tạo history_since_swap với
    #      pre_trim_count ván True (giả sử đúng — chính là các ván đúng đã bị bỏ).
    'pre_trim_count':        0,   # số ván được pre-fill vào history sau khi đổi ttoan
    # v26: đếm ván THẬT (không tính pre_fill) kể từ khi đổi ttoan.
    # WR check chỉ được kích hoạt khi: real_vans_since_swap >= 1 AND ván thật cuối là SAI
    # → ttoan mới luôn đoán ít nhất 1 ván, không bị đổi ngay;
    #   nếu ván đầu đúng tiếp tục đoán; chỉ khi có ít nhất 1 ván sai thật mới xét WR.
    'real_vans_since_swap':  0,   # chỉ đếm ván thật (reset 0 khi đổi ttoan)
}

ALL_LOGICS = ['L1', 'L2', 'L3', 'L4', 'L5', 'L6', 'L7', 'L8', 'L9']

def _run_one_logic(name: str, X: int, Y: int, Z: int, md5h: str = '') -> str:
    """Chạy một logic theo tên, trả về 'TAI' hoặc 'XIU'.
    L7/L8/L9 cần md5h để tự lấy Y/Z từ vị trí riêng.
    """
    if name == 'L7':
        return _run_logic_L7(X, md5h)
    if name == 'L8':
        return _run_logic_L8(X, md5h)
    if name == 'L9':
        return _run_logic_L9(X, md5h)
    return {
        'L1': _run_logic_L1,
        'L2': _run_logic_L2,
        'L3': _run_logic_L3,
        'L4': _run_logic_L4,
        'L5': _run_logic_L5,
        'L6': _run_logic_L6,
    }[name](X, Y, Z)

def logic_tuner_register_pred(sess_id: str, X: int, Y: int, Z: int, md5h: str = ''):
    """Lưu pred của cả 9 logic cho phiên này vào pending (để so với kết quả thực sau)."""
    preds = {name: _run_one_logic(name, X, Y, Z, md5h) for name in ALL_LOGICS}
    _logic_tuner['pending'][sess_id] = preds
    # Giữ pending tối đa 200
    if len(_logic_tuner['pending']) > 200:
        oldest = list(_logic_tuner['pending'].keys())[0]
        del _logic_tuner['pending'][oldest]

def logic_tuner_update_result(sess_id: str, actual: str, pred_ok: bool | None = None):
    """
    v22: Khi có kết quả thực:
    1. Cập nhật rolling history của từng logic (L1–L6).
    2. Tăng tổng phiên có pred.
    3. Cập nhật ttoan tracker (chỉ khi pred_ok không phải None):
       - vans_since_swap += 1
       - history_since_swap.append(pred_ok)  ← tích lũy toàn bộ từ khi đổi ttoan
    4. Khi history_since_swap đã có đủ TTOAN_CHECK_WINDOW ván → kiểm tra WR:
       - Lấy TTOAN_CHECK_WINDOW ván cuối của history_since_swap để tính recent_wr
       - recent_wr ≥ 60% → GIỮ nguyên, KHÔNG reset, tiếp tục đếm bình thường
       - recent_wr < 40% → ĐỔI ttoan ngay:
           · Gọi _run_logic_tune_with_window(vans_since_swap) dùng đúng
             tổng số ván đã đếm từ lần đổi ttoan trước (không phải 10 ván)
           · Reset vans_since_swap = 0, history_since_swap = []
           · Reset _logic_tuner['since_tune'] = 0
       - 40% ≤ recent_wr < 60% → không làm gì (vùng trung tính)

    LƯU Ý v22: KHÔNG còn trigger _run_logic_tune() theo interval cố định.
    Chỉ ttoan WR check mới trigger tune logic.
    """
    pend = _logic_tuner['pending'].pop(sess_id, None)
    if not pend:
        return

    # 1. Cập nhật rolling history từng logic
    for name in ALL_LOGICS:
        pred = pend.get(name)
        if pred is None:
            continue
        hist = _logic_tuner['history'][name]
        hist.append(pred == actual)
        if len(hist) > LOGIC_TUNE_WINDOW:
            hist.pop(0)

    _logic_tuner['total_preds'] += 1
    # since_tune không dùng để trigger tự động nữa — chỉ dùng để hiển thị UI
    _logic_tuner['since_tune'] += 1

    # 2. Cập nhật ttoan tracker — chỉ khi có pred thực (pred_ok không phải None)
    if pred_ok is None:
        return   # không có pred → không cập nhật ttoan tracker

    _ttoan_tracker['vans_since_swap'] += 1
    _ttoan_tracker['history_since_swap'].append(bool(pred_ok))
    # v26: đếm ván thật riêng (không tính pre_fill)
    _ttoan_tracker['real_vans_since_swap'] += 1
    real_vans = _ttoan_tracker['real_vans_since_swap']

    # 3. v33: CONSECUTIVE LOSS EMERGENCY GATE
    # Nếu sai liên tiếp >= TTOAN_CONSEC_LOSS_BAIL ván thật → đổi ngay, không cần đủ window
    if not bool(pred_ok):
        consec_loss = 0
        for v in reversed(_ttoan_tracker['history_since_swap']):
            if not v:
                consec_loss += 1
            else:
                break
        if consec_loss >= TTOAN_CONSEC_LOSS_BAIL:
            vans_done = _ttoan_tracker['vans_since_swap']
            print(f"[TTOAN] 🚨 EMERGENCY — sai liên tiếp {consec_loss} ván thật "
                  f"→ ĐỔI ttoan ngay (không cần đủ {TTOAN_CHECK_WINDOW} ván)!")
            _run_logic_tune_with_window(vans_done)
            # trim = 0 vì vừa kết thúc bằng chuỗi sai, không có đuôi đúng
            _ttoan_tracker['vans_since_swap']      = 0
            _ttoan_tracker['history_since_swap']   = []
            _ttoan_tracker['pre_trim_count']       = 0
            _ttoan_tracker['real_vans_since_swap'] = 0
            _ttoan_tracker['last_swap_at_live']    = app_state['live_count']
            _ttoan_tracker['swap_count']          += 1
            _ttoan_tracker['last_swap_reason']     = 'consec_loss'
            _logic_tuner['since_tune']             = 0
            new_top3 = _logic_tuner['active_logics']
            asyncio.get_event_loop().create_task(
                _tg_notify_ttoan_swap(
                    swap_count = _ttoan_tracker['swap_count'],
                    vans_used  = vans_done,
                    recent_wr  = 0.0,
                    new_logics = new_top3,
                )
            )
            return

    # 3b. v26: FIRST-REAL-FAIL GATE
    # WR check chỉ được kích hoạt khi:
    #   a) Đã có ít nhất 1 ván thật (real_vans >= 1)  — luôn đúng ở đây vì vừa +1
    #   b) Ván thật vừa rồi là SAI (pred_ok == False)
    #   c) Đã đủ TTOAN_CHECK_WINDOW ván trong history_since_swap
    # → Nếu ván thật đầu tiên ĐÚNG → bỏ qua check, đoán tiếp
    # → Chỉ khi có ít nhất 1 ván sai thật mới xét WR → có thể đổi
    if bool(pred_ok):
        # Ván thật vừa đúng — không xét WR, tiếp đếm
        print(f"[TTOAN] ✅ Ván thật #{real_vans} ĐÚNG → bỏ qua WR check, tiếp đếm "
              f"(history={len(_ttoan_tracker['history_since_swap'])} ván)")
        return

    # Ván thật vừa SAI — kiểm tra WR khi đã đủ TTOAN_CHECK_WINDOW ván
    hist_all  = _ttoan_tracker['history_since_swap']
    n_total   = len(hist_all)

    if n_total < TTOAN_CHECK_WINDOW:
        # Chưa đủ ván để check — tiếp tục đếm
        print(f"[TTOAN] ❌ Ván thật #{real_vans} SAI → chưa đủ {TTOAN_CHECK_WINDOW} ván "
              f"({n_total} ván), tiếp đếm")
        return

    # Lấy TTOAN_CHECK_WINDOW ván cuối để tính recent WR
    recent_hist = hist_all[-TTOAN_CHECK_WINDOW:]
    recent_wr   = sum(recent_hist) / TTOAN_CHECK_WINDOW
    vans_done   = _ttoan_tracker['vans_since_swap']   # tổng ván từ lần đổi ttoan trước

    print(f"[TTOAN] ❌ Ván thật #{real_vans} SAI → WR check | "
          f"WR {TTOAN_CHECK_WINDOW} ván cuối = {recent_wr*100:.1f}% "
          f"| tổng ván kể từ đổi = {vans_done}")

    if recent_wr >= TTOAN_WR_HOLD_THRESH:
        # WR tốt (≥ 60%) → giữ nguyên ttoan, tiếp đếm, KHÔNG reset
        print(f"[TTOAN] ✅ WR={recent_wr*100:.1f}% ≥ {TTOAN_WR_HOLD_THRESH*100:.0f}% "
              f"→ GIỮ ttoan, tiếp đếm (tổng={vans_done})")

    elif recent_wr < TTOAN_WR_SWAP_THRESH:
        # WR xấu (< 40%) → đổi ttoan ngay lập tức
        print(f"[TTOAN] ⚠️ WR={recent_wr*100:.1f}% < {TTOAN_WR_SWAP_THRESH*100:.0f}% "
              f"→ ĐỔI ttoan! Tune logic từ {vans_done} ván đã đếm")
        # Tune logic dùng đúng số ván đã đếm từ lần đổi ttoan trước
        _run_logic_tune_with_window(vans_done)

        # ── v25: Tính last-fail trim ──────────────────────────────────────────
        # Trong 10 ván cuối (recent_hist), tìm vị trí ván SAI GẦN NHẤT (index từ phải sang)
        # Các ván đúng đứng TRƯỚC ván sai gần nhất sẽ bị bỏ khỏi history_since_swap mới
        # Ví dụ recent_hist = [✅,✅,❌,✅,❌,✅,✅,✅,✅,✅]  (index 0..9)
        #   → ván sai gần nhất ở index 4 → trim = số ván đúng từ index 5 đến 9 = 5
        # Sau khi đổi ttoan, history_since_swap khởi tạo với trim ván True (bù trước)
        # → ttoan mới chỉ cần đoán thêm (TTOAN_CHECK_WINDOW - trim) ván mới để check WR
        trim_count = 0
        for i in range(len(recent_hist) - 1, -1, -1):
            if not recent_hist[i]:   # tìm ván SAI gần nhất (False)
                # số ván từ i+1 đến cuối (toàn True) = len(recent_hist) - 1 - i
                trim_count = len(recent_hist) - 1 - i
                break
        # Nếu không có ván sai nào trong recent_hist (WR = 100%) → trim = 0
        print(f"[TTOAN] ✂️  last-fail trim = {trim_count} ván "
              f"(history_since_swap sẽ pre-fill {trim_count} True)")

        # Reset bộ đếm — pre-fill history với trim_count ván True
        pre_fill = [True] * trim_count
        _ttoan_tracker['vans_since_swap']       = trim_count
        _ttoan_tracker['history_since_swap']    = pre_fill
        _ttoan_tracker['pre_trim_count']        = trim_count
        _ttoan_tracker['real_vans_since_swap']  = 0   # v26: reset ván thật về 0
        _ttoan_tracker['last_swap_at_live']     = app_state['live_count']
        _ttoan_tracker['swap_count']           += 1
        _ttoan_tracker['last_swap_reason']      = 'wr_low'
        _logic_tuner['since_tune']              = 0
        print(f"[TTOAN] 🔄 Đổi ttoan #{_ttoan_tracker['swap_count']} "
              f"@ live#{app_state['live_count']} | bộ đếm reset → {trim_count} (pre-fill)")
        # Broadcast Telegram thông báo đổi ttoan + logic mới
        new_top3 = _logic_tuner['active_logics']
        asyncio.get_event_loop().create_task(
            _tg_notify_ttoan_swap(
                swap_count = _ttoan_tracker['swap_count'],
                vans_used  = vans_done,
                recent_wr  = recent_wr,
                new_logics = new_top3,
            )
        )

    else:
        # Vùng trung tính 40%–60% → không làm gì
        print(f"[TTOAN] ➖ WR={recent_wr*100:.1f}% (trung tính) → chờ thêm")

def _run_logic_tune_with_window(n_vans: int):
    """
    v21: Tune logic dựa trên lịch sử N ván kể từ khi ttoan đổi lần trước.
    Thay vì dùng toàn bộ LOGIC_TUNE_WINDOW, dùng đúng n_vans ván gần nhất
    trong history của từng logic để tìm top-3 mới.
    n_vans = số ván đã chơi kể từ lần đổi ttoan — đây là "cửa sổ thực tế".
    """
    # Lấy n_vans ván cuối trong history của từng logic
    wrs = {}
    for name in ALL_LOGICS:
        hist = _logic_tuner['history'][name]
        # Chỉ lấy n_vans ván gần nhất (không vượt quá số ván thực có)
        window = hist[-n_vans:] if n_vans > 0 else hist[-LOGIC_TUNE_WINDOW:]
        if window:
            wrs[name] = sum(window) / len(window)
        else:
            wrs[name] = 0.5   # neutral nếu không có data

    print(f"[TTOAN TUNE] Tune logic từ cửa sổ {n_vans} ván | "
          f"WR: { {n: round(w*100,1) for n,w in wrs.items()} }")

    # Từ đây dùng lại core của _run_logic_tune nhưng với wrs đã tính riêng
    _apply_logic_tune(wrs, reason=f'ttoan_swap_window={n_vans}')


def _apply_logic_tune(wrs: dict, reason: str = 'periodic'):
    """
    Core của logic tuner — tính effective WR, chọn top-3, cập nhật state.
    Tách ra riêng để cả _run_logic_tune lẫn _run_logic_tune_with_window đều dùng được.
    """
    old_top3     = _logic_tuner['active_logics'][:]
    old_reversed = set(_logic_tuner['reversed_logics'])

    effective = {}
    for name in ALL_LOGICS:
        wr = wrs.get(name, 0.5)
        rev_wr = 1.0 - wr
        if rev_wr > wr and rev_wr >= REVERSE_THRESHOLD:
            effective[name] = (rev_wr, True)
        else:
            effective[name] = (wr, False)

    ranked_eff = sorted(
        ALL_LOGICS,
        key=lambda n: (effective[n][0], 0 if not effective[n][1] else -1),
        reverse=True
    )

    new_top3 = []
    used     = set()
    for candidate in ranked_eff:
        if len(new_top3) == 3:
            break
        if candidate in used:
            continue
        eff_score, is_rev = effective[candidate]
        if is_rev:
            best_normal_remaining = max(
                (effective[n][0] for n in ALL_LOGICS
                 if n not in used and n != candidate and not effective[n][1]),
                default=0.0
            )
            if best_normal_remaining >= eff_score:
                continue
        new_top3.append(candidate)
        used.add(candidate)

    if len(new_top3) < 3:
        for candidate in ranked_eff:
            if candidate not in used:
                new_top3.append(candidate)
                used.add(candidate)
            if len(new_top3) == 3:
                break

    new_reversed = {n for n in new_top3 if effective[n][1]}

    _logic_tuner['active_logics']   = new_top3
    _logic_tuner['reversed_logics'] = new_reversed

    bench_wr     = {n: round(wrs.get(n, 0.5) * 100, 1) for n in ALL_LOGICS}
    bench_eff_wr = {n: round(effective[n][0] * 100, 1) for n in ALL_LOGICS}
    bench_rev_wr = {n: round((1.0 - wrs.get(n, 0.5)) * 100, 1) for n in ALL_LOGICS}
    bench_is_rev = {n: effective[n][1] for n in ALL_LOGICS}

    bench = {
        'wr':       bench_wr,
        'eff_wr':   bench_eff_wr,
        'rev_wr':   bench_rev_wr,
        'is_rev':   bench_is_rev,
        'top3':     new_top3,
        'reversed': list(new_reversed),
        'at':       app_state['live_count'],
        'changed':  new_top3 != old_top3 or new_reversed != old_reversed,
        'reason':   reason,
    }
    _logic_tuner['last_bench'] = bench

    wr_parts = []
    for n in ranked_eff:
        eff_s, is_r = effective[n]
        tag = '[BẺ]' if is_r else ''
        wr_parts.append(f"{n}={round(eff_s*100,1):.1f}%{tag}")
    wr_str = '  '.join(wr_parts)

    changed_tag = ''
    if new_top3 != old_top3 or new_reversed != old_reversed:
        changed_tag = f"  ← CHANGED {old_top3}(rev={list(old_reversed)}) → {new_top3}(rev={list(new_reversed)})"
    else:
        changed_tag = '  (no change)'

    print(f"[LOGIC TUNER v21/{reason}] @ live#{app_state['live_count']} | "
          f"{wr_str} | top3={new_top3} rev={list(new_reversed)}{changed_tag}")


def _run_logic_tune():
    """
    v17+: Chọn top-3 logic có effective WR cao nhất.
    Effective WR = max(WR, 1-WR) — nếu 1-WR thắng thì logic đó được chọn dưới dạng REVERSED.
    Điều kiện bẻ: reversed_wr >= REVERSE_THRESHOLD (tránh noise khi WR ~50%).

    Rule mới: logic bẻ chỉ được chọn vào top-3 khi effective WR của nó
    STRICTLY CAO HƠN tất cả logic thường (không bẻ) còn lại ngoài top-3.
    Nếu bằng hoặc thấp hơn → ưu tiên logic thường thay thế.
    """
    _logic_tuner['since_tune'] = 0

    # Tính WR gốc
    wrs = {}
    for name in ALL_LOGICS:
        hist = _logic_tuner['history'][name]
        if hist:
            wrs[name] = sum(hist) / len(hist)
        else:
            wrs[name] = 0.5   # neutral

    # Tính effective WR và quyết định reversed hay không
    effective = {}
    for name in ALL_LOGICS:
        wr = wrs[name]
        rev_wr = 1.0 - wr
        if rev_wr > wr and rev_wr >= REVERSE_THRESHOLD:
            effective[name] = (rev_wr, True)
        else:
            effective[name] = (wr, False)

    # Sort theo effective WR giảm dần (ưu tiên normal khi sama via key tuple)
    # (effective_wr DESC, is_reversed ASC) → normal logic diutamakan saat WR sama
    ranked_eff = sorted(
        ALL_LOGICS,
        key=lambda n: (effective[n][0], 0 if not effective[n][1] else -1),
        reverse=True
    )

    # Build top-3 dengan aturan: logic bẻ hanya masuk jika effective WR-nya
    # strictly lebih tinggi dari SEMUA logic normal yang bisa jadi pengganti.
    # Iterasi greedy: slot per slot, cek apakah kandidat (bẻ) layak.
    old_top3     = _logic_tuner['active_logics'][:]
    old_reversed = set(_logic_tuner['reversed_logics'])

    new_top3     = []
    used         = set()

    # Pisahkan kandidat normal dan bẻ (semua masuk pool, sudah sorted)
    for candidate in ranked_eff:
        if len(new_top3) == 3:
            break
        if candidate in used:
            continue

        eff_score, is_rev = effective[candidate]

        if is_rev:
            # Logic bẻ: cek apakah ada logic normal (non-bẻ) yang belum dipakai
            # dengan effective WR >= eff_score → jika ada, skip logic bẻ ini
            best_normal_remaining = max(
                (effective[n][0] for n in ALL_LOGICS
                 if n not in used and n != candidate and not effective[n][1]),
                default=0.0
            )
            if best_normal_remaining >= eff_score:
                # Ada logic normal dengan WR >= bẻ → skip, ambil yang normal duluan
                continue

        new_top3.append(candidate)
        used.add(candidate)

    # Jika belum 3 slot terisi (jarang terjadi), isi sisa dengan logic terbaik yang tersisa
    if len(new_top3) < 3:
        for candidate in ranked_eff:
            if candidate not in used:
                new_top3.append(candidate)
                used.add(candidate)
            if len(new_top3) == 3:
                break

    new_reversed = {n for n in new_top3 if effective[n][1]}

    _logic_tuner['active_logics']   = new_top3
    _logic_tuner['reversed_logics'] = new_reversed

    # Build bench data — lưu cả effective WR và reversed WR cho frontend
    bench_wr      = {n: round(wrs[n] * 100, 1) for n in ALL_LOGICS}
    bench_eff_wr  = {n: round(effective[n][0] * 100, 1) for n in ALL_LOGICS}
    bench_rev_wr  = {n: round((1.0 - wrs[n]) * 100, 1) for n in ALL_LOGICS}
    bench_is_rev  = {n: effective[n][1] for n in ALL_LOGICS}

    bench = {
        'wr':       bench_wr,          # WR gốc (thực tế)
        'eff_wr':   bench_eff_wr,      # effective WR (dùng để rank)
        'rev_wr':   bench_rev_wr,      # reversed WR (1 - wr)
        'is_rev':   bench_is_rev,      # True nếu logic đó đang bẻ
        'top3':     new_top3,
        'reversed': list(new_reversed),
        'at':       app_state['live_count'],
        'changed':  new_top3 != old_top3 or new_reversed != old_reversed,
    }
    _logic_tuner['last_bench'] = bench

    # Log
    wr_parts = []
    for n in ranked_eff:
        eff_s, is_r = effective[n]
        tag = '[BẺ]' if is_r else ''
        wr_parts.append(f"{n}={round(eff_s*100,1):.1f}%{tag}")
    wr_str = '  '.join(wr_parts)

    changed_tag = ''
    if new_top3 != old_top3 or new_reversed != old_reversed:
        changed_tag = f"  ← CHANGED {old_top3}(rev={list(old_reversed)}) → {new_top3}(rev={list(new_reversed)})"
    else:
        changed_tag = '  (no change)'

    print(f"[LOGIC TUNER v17] Tune @ live#{app_state['live_count']} | {wr_str} | top3={new_top3} rev={list(new_reversed)}{changed_tag}")

def get_active_logics() -> list[str]:
    """Trả về top-3 logic đang active."""
    return _logic_tuner['active_logics']

def get_reversed_logics() -> set:
    """Trả về set tên logic đang bị bẻ chiều."""
    return _logic_tuner['reversed_logics']

def run_three_logic(sess_str, md5h):
    """
    v16+: Tính cả 6 logic, chọn top-3 active từ logic tuner, ensemble majority từ top-3.
    Phân loại 4 case dựa trên top-3 logic đang active → 2 nhóm TT1/TT2.
    sess_str đã là sess+1 (được +1 trước khi gọi hàm này).

    Rule bẻ có điều kiện:
    Nếu top-3 có logic bẻ VÀ WR logic bẻ KHÔNG phải cao nhất trong top-3:
      - Nếu 2 logic normal đồng thuận nhau MÀ logic bẻ vote khác → đảo pred sang 2 normal thắng
      - Nếu logic bẻ đồng thuận với ít nhất 1 normal → majority bình thường (bẻ vẫn đóng góp)
    Nếu logic bẻ có WR cao nhất trong top-3 → bẻ hoạt động bình thường, không hạn chế.
    """
    X, Y, Z = _calc_XYZ(sess_str, md5h)

    # Tính cả 9 logic (v32: thêm L7/L8/L9)
    all_preds = {name: _run_one_logic(name, X, Y, Z, md5h) for name in ALL_LOGICS}
    l1 = all_preds['L1']
    l2 = all_preds['L2']
    l3 = all_preds['L3']

    # Lấy top-3 active từ logic tuner
    active    = get_active_logics()    # e.g. ['L1', 'L3', 'L5']
    reversed_ = get_reversed_logics()  # set logic đang bẻ chiều

    def _flip(v):
        return 'XIU' if v == 'TAI' else 'TAI'

    # Lấy effective WR từ last_bench để biết ai WR cao nhất trong top-3
    bench = _logic_tuner.get('last_bench') or {}
    eff_wr_map = bench.get('eff_wr', {})   # { 'L1': float%, 'L3': float%, ... }

    # ── Bẻ độc tôn — rule áp dụng khi ensemble ──────────────────────────────────
    # reversed_ có thể chứa 0, 1, 2, hoặc 3 logic (tuner giữ nguyên, không trim).
    # Rule:
    #   - 0 bẻ trong top-3          → chạy raw pred toàn bộ, không flip gì
    #   - 2+ bẻ trong top-3         → bỏ qua tất cả bẻ, chạy raw pred toàn bộ
    #   - Đúng 1 bẻ trong top-3     → chỉ áp bẻ khi nó là WR cao nhất trong top-3
    #                                  (bẻ độc tôn); nếu không phải WR cao nhất → cũng bỏ
    reversed_in_top3 = [n for n in active if n in reversed_]
    n_bẻ = len(reversed_in_top3)

    apply_flip: set = set()   # set tên logic thực sự được flip trong lần này

    if n_bẻ == 1:
        bẻ_name = reversed_in_top3[0]
        top3_wr = {n: eff_wr_map.get(n, 0.0) for n in active}
        max_wr  = max(top3_wr.values()) if top3_wr else 0.0
        if top3_wr.get(bẻ_name, 0.0) >= max_wr:
            # Bẻ độc tôn — WR cao nhất → flip
            apply_flip = {bẻ_name}
            print(f"[BẺ ĐỘC TÔN] {bẻ_name} WR={top3_wr[bẻ_name]:.1f}% là cao nhất → flip")
        else:
            print(f"[BẺ BỎ QUA] {bẻ_name} WR={top3_wr.get(bẻ_name,0):.1f}% không phải cao nhất "
                  f"(max={max_wr:.1f}%) → chạy raw")
    elif n_bẻ >= 2:
        print(f"[BẺ BỎ QUA] {n_bẻ} logic bẻ trong top-3 {reversed_in_top3} → chạy raw toàn bộ")
    # n_bẻ == 0: không làm gì, apply_flip rỗng

    active_preds = []
    for n in active:
        pred = all_preds[n]
        if n in apply_flip:
            pred = _flip(pred)
        active_preds.append(pred)

    # Build effective_preds dict để trả về (giá trị sau khi bẻ + guard)
    effective_preds = {}
    for i, n in enumerate(active):
        effective_preds[n] = active_preds[i]
    # Logics ngoài top-3: effective = raw pred mereka (no flip)
    for n in ALL_LOGICS:
        if n not in effective_preds:
            effective_preds[n] = _flip(all_preds[n]) if n in reversed_ else all_preds[n]

    tai_count = active_preds.count('TAI')
    xiu_count = active_preds.count('XIU')
    majority  = 'TAI' if tai_count >= xiu_count else 'XIU'
    minority  = 'XIU' if majority == 'TAI' else 'TAI'

    # Phân loại case dựa trên active[0], active[1], active[2]
    a0, a1, a2 = active_preds[0], active_preds[1], active_preds[2]
    la, lb, lc = active[0], active[1], active[2]
    if tai_count == 3 or xiu_count == 3:
        case_type = '3-0'
    elif a1 == a2 and a0 != a1:
        case_type = f'{lb}{lc}'
    elif a0 == a1 and a1 != a2:
        case_type = f'{la}{lb}'
    elif a0 == a2 and a0 != a1:
        case_type = f'{la}{lc}'
    else:
        case_type = '3-0'

    # Normalize case_type sang 4 bucket quen thuộc cho adaptive grouping
    # (adaptive grouping vẫn dùng tên cũ: '3-0', 'L2L3', 'L1L2', 'L1L3')
    _KNOWN_CASES = {'3-0', 'L2L3', 'L1L2', 'L1L3'}
    if case_type not in _KNOWN_CASES:
        case_type = '3-0'   # fallback khi top-3 dùng logic mới

    # Group từ adaptive mapping
    group = get_case_group(case_type)

    return {
        # Top-3 active — dùng effective pred (đã bẻ nếu reversed)
        'L1': active_preds[0],
        'L2': active_preds[1],
        'L3': active_preds[2],
        # Tên logic thực tế đang được dùng
        'active_logics':   active,
        # Logic đang bị bẻ chiều trong top-3
        'reversed_logics': list(reversed_),
        # Toàn bộ 6 logic — raw pred (chưa bẻ)
        'all_preds': all_preds,
        # Toàn bộ 6 logic — effective pred (đã bẻ nếu reversed)
        'effective_preds': effective_preds,
        'X': X, 'Y': Y, 'Z': Z,
        'tai_count': tai_count,
        'xiu_count': xiu_count,
        'majority':  majority,
        'minority':  minority,
        'case_type': case_type,
        'group':     group,
    }

# Correlation tracker — theo dõi khi case X xảy ra thì case Y đúng/sai
# Structure: { 'case_X': { 'case_Y': {'ok': int, 'fail': int} } }
# Đây là per-session: mỗi phiên có 1 case, ta so sánh case đó với kết quả thực
# rồi đếm xem các logic riêng lẻ (L1/L2/L3) + case đúng/sai thế nào
_corr_tracker = {
    # Với mỗi case (3-0, L2L3, L1L2, L1L3), track xem:
    # - L1 đúng/sai, L2 đúng/sai, L3 đúng/sai
    # - ensemble (sau bẻ cầu) đúng/sai
    # - majority (trước bẻ) đúng/sai
    case: {
        'L1':       {'ok': 0, 'fail': 0},
        'L2':       {'ok': 0, 'fail': 0},
        'L3':       {'ok': 0, 'fail': 0},
        'majority': {'ok': 0, 'fail': 0},
        'ensemble': {'ok': 0, 'fail': 0},
        'count':    0,
    }
    for case in ('3-0', 'L2L3', 'L1L2', 'L1L3')
}

# Lưu thêm: per-group TT1/TT2
_corr_tracker['_tt'] = {
    'TT1': {'ok': 0, 'fail': 0, 'count': 0},
    'TT2': {'ok': 0, 'fail': 0, 'count': 0},
}

# ─── Cross-logic pair tracker ────────────────────────────────────────────────
# Theo dõi: khi case X xảy ra (3-0 / L2L3 / L1L2 / L1L3)
#   → cặp L1L2 đúng/sai bao nhiêu lần?
#   → cặp L2L3 đúng/sai bao nhiêu lần?
#   → cặp L1L3 đúng/sai bao nhiêu lần?
# "đúng" = cả 2 logic trong cặp cùng vote đúng kết quả thực
# "sai"  = ít nhất 1 logic trong cặp sai
# "đồng thuận" = 2 logic trong cặp vote giống nhau (bất kể đúng/sai)
_pair_tracker = {
    case: {
        'L1L2': {'agree_ok': 0, 'agree_fail': 0, 'disagree': 0},
        'L2L3': {'agree_ok': 0, 'agree_fail': 0, 'disagree': 0},
        'L1L3': {'agree_ok': 0, 'agree_fail': 0, 'disagree': 0},
        'count': 0,
    }
    for case in ('3-0', 'L2L3', 'L1L2', 'L1L3')
}

def update_pair_tracker(case_type, l1, l2, l3, actual):
    """
    Tích lũy thống kê cặp logic khi case_type xảy ra.
    agree_ok   = 2 logic đồng thuận VÀ đúng kết quả
    agree_fail = 2 logic đồng thuận NHƯNG sai kết quả
    disagree   = 2 logic không đồng thuận (1 TAI 1 XIU)
    """
    c = _pair_tracker.get(case_type)
    if not c:
        return
    c['count'] += 1
    for pair_name, va, vb in [('L1L2', l1, l2), ('L2L3', l2, l3), ('L1L3', l1, l3)]:
        p = c[pair_name]
        if va == vb:           # đồng thuận
            if va == actual:
                p['agree_ok'] += 1
            else:
                p['agree_fail'] += 1
        else:                  # bất đồng
            p['disagree'] += 1

# ─── Correlation Matrix Tracker ──────────────────────────────────────────────
# Khi case X xảy ra (phiên đó có pred) và đúng/sai,
# đồng thời L1/L2/L3 riêng lẻ đúng/sai thế nào?
# → Từ đó tìm: "L_i hay đúng cùng case X" → gợi ý cặp tự nhiên
#
# Structure:
# { case_X: { 'L1': {'co_ok': int, 'co_fail': int},
#             'L2': {'co_ok': int, 'co_fail': int},
#             'L3': {'co_ok': int, 'co_fail': int},
#             'count_ok': int,   # số phiên case X ensemble đúng
#             'count_fail': int, # số phiên case X ensemble sai
#             'count': int } }
#
# co_ok   = case X đúng VÀ L_i cũng đúng kết quả thực
# co_fail = case X đúng NHƯNG L_i sai (hoặc case X sai VÀ L_i đúng)
# → ta track khi ensemble đúng thì L_i đúng bao nhiêu %
#   và khi ensemble sai thì L_i đúng bao nhiêu % (inverse signal)
_corr_matrix = {
    case: {
        'L1':  {'both_ok': 0, 'case_ok_li_fail': 0, 'case_fail_li_ok': 0, 'both_fail': 0},
        'L2':  {'both_ok': 0, 'case_ok_li_fail': 0, 'case_fail_li_ok': 0, 'both_fail': 0},
        'L3':  {'both_ok': 0, 'case_ok_li_fail': 0, 'case_fail_li_ok': 0, 'both_fail': 0},
        'count_ok':   0,
        'count_fail': 0,
        'count':      0,
    }
    for case in ('3-0', 'L2L3', 'L1L2', 'L1L3')
}

def update_corr_matrix(case_type, l1, l2, l3, ensemble_ok, actual):
    """
    Gọi mỗi phiên có dự đoán.
    ensemble_ok: bool — ensemble đúng hay sai
    actual:      'TAI' hoặc 'XIU' — kết quả thực
    """
    c = _corr_matrix.get(case_type)
    if not c:
        return
    c['count'] += 1
    if ensemble_ok:
        c['count_ok'] += 1
    else:
        c['count_fail'] += 1

    for key, pred in [('L1', l1), ('L2', l2), ('L3', l3)]:
        if pred is None:
            continue
        li_ok = (pred == actual)
        m = c[key]
        if ensemble_ok and li_ok:
            m['both_ok'] += 1
        elif ensemble_ok and not li_ok:
            m['case_ok_li_fail'] += 1
        elif not ensemble_ok and li_ok:
            m['case_fail_li_ok'] += 1
        else:
            m['both_fail'] += 1

def get_corr_matrix_data():
    """
    Tính correlation % cho từng (case, logic):
    - co_rate: khi ensemble đúng → L_i cũng đúng bao nhiêu % (đồng pha)
    - inv_rate: khi ensemble sai → L_i đúng bao nhiêu % (ngược pha — L_i là signal bẻ)
    - Gợi ý cặp tự nhiên: L_i nào có co_rate cao nhất với case X
    """
    out = {}
    for case, c in _corr_matrix.items():
        ok_total   = c['count_ok']
        fail_total = c['count_fail']
        out[case]  = {
            'count':      c['count'],
            'count_ok':   ok_total,
            'count_fail': fail_total,
            'logics':     {},
        }
        for key in ('L1', 'L2', 'L3'):
            m = c[key]
            # co_rate: trong những phiên ensemble đúng, L_i cũng đúng bao nhiêu %
            co_rate = round(m['both_ok'] / ok_total * 100, 1) if ok_total > 0 else None
            # inv_rate: trong những phiên ensemble sai, L_i lại đúng bao nhiêu %
            inv_rate = round(m['case_fail_li_ok'] / fail_total * 100, 1) if fail_total > 0 else None
            out[case]['logics'][key] = {
                'both_ok':          m['both_ok'],
                'case_ok_li_fail':  m['case_ok_li_fail'],
                'case_fail_li_ok':  m['case_fail_li_ok'],
                'both_fail':        m['both_fail'],
                'co_rate':          co_rate,
                'inv_rate':         inv_rate,
            }
        # Gợi ý: logic nào co_rate cao nhất → "đồng pha" với case này
        best = max(
            ((k, v['co_rate']) for k, v in out[case]['logics'].items() if v['co_rate'] is not None),
            key=lambda x: x[1],
            default=(None, None)
        )
        out[case]['best_logic']    = best[0]
        out[case]['best_co_rate']  = best[1]
    return out

def get_pair_suggestions():
    """
    Trả về gợi ý: với mỗi case, cặp nào có agree_ok cao nhất → nên theo?
    Output: { case: { pair: { agree_ok, agree_fail, disagree, wr_agree, suggestion } } }
    """
    out = {}
    for case, c in _pair_tracker.items():
        out[case] = {'count': c['count'], 'pairs': {}}
        best_pair = None
        best_wr   = -1
        for pair in ('L1L2', 'L2L3', 'L1L3'):
            p  = c[pair]
            tot_agree = p['agree_ok'] + p['agree_fail']
            wr = round(p['agree_ok'] / tot_agree * 100, 1) if tot_agree > 0 else None
            out[case]['pairs'][pair] = {
                **p,
                'wr_agree': wr,
            }
            if wr is not None and wr > best_wr:
                best_wr   = wr
                best_pair = pair
        out[case]['best_pair'] = best_pair
        out[case]['best_wr']   = best_wr if best_pair else None
    return out

def update_corr_tracker(case_type, l1, l2, l3, majority, ensemble, actual):
    """Gọi sau khi có kết quả thực. Tích lũy correlation stats."""
    c = _corr_tracker.get(case_type)
    if not c:
        return
    c['count'] += 1
    for key, pred in [('L1', l1), ('L2', l2), ('L3', l3),
                      ('majority', majority), ('ensemble', ensemble)]:
        if pred:
            if pred == actual:
                c[key]['ok'] += 1
            else:
                c[key]['fail'] += 1

    # TT group tracking
    group = 'TT1' if case_type in ('3-0', 'L2L3') else 'TT2'
    tg = _corr_tracker['_tt'][group]
    tg['count'] += 1
    if ensemble and ensemble == actual:
        tg['ok'] += 1
    elif ensemble:
        tg['fail'] += 1

def get_ensemble_cross_comp(logic_result):
    """
    v20 — Logic ưu tiên (theo thứ tự):

    1. TOP-3 FULL BẺ (3 logic bẻ) → theo bình thường (majority), không áp thiểu số.

    2. TOP-3 CÓ 2 LOGIC BẺ:
       2a. 2 logic bẻ ĐỒNG THUẬN nhau (cùng dự đoán TAI hoặc XIU)
           → THEO pred của 2 logic bẻ (bỏ qua logic thường).
       2b. 2 logic bẻ KHÔNG ĐỒNG THUẬN (1 bẻ đồng pred vs logic thường,
           BẺ2 bất đồng vs logic thường)
           → THEO BẺ2 (logic bẻ bất đồng vs logic thường).

    3. BẺ ĐỘC TÔN MẠNH (1 logic bẻ, WR bẻ > TẤT CẢ logic thuận trong top-3)
       → THEO hoàn toàn logic bẻ (giống v19).

    4. BẺ ĐỘC TÔN YẾU (1 logic bẻ, WR bẻ <= ít nhất 1 logic thuận trong top-3)
       → THEO THIỂU SỐ:
       - vote 2-1 → theo 1
       - vote 3-0 → bẻ ngược

    5. Không có logic bẻ (top-3 full thuận) → fallback majority + rev_ns + flip như cũ.
    """
    def _flip(v):
        return 'XIU' if v == 'TAI' else 'TAI'

    def _minority_vote(active_preds, majority):
        """
        Trả về pred theo THIỂU SỐ từ active_preds (list 3 phần tử đã effective).
        - 2-1: thiểu số = pred khác biệt
        - 3-0: thiểu số = đảo chiều majority
        """
        tai_c = active_preds.count('TAI')
        xiu_c = active_preds.count('XIU')
        if tai_c == 2:   # 2-1 bẻ → theo XIU (thiểu số)
            return 'XIU'
        if xiu_c == 2:   # 2-1 bẻ → theo TAI (thiểu số)
            return 'TAI'
        # 3-0 → bẻ ngược majority
        return _flip(majority)

    group        = logic_result['group']
    majority     = logic_result['majority']
    active       = logic_result['active_logics']         # e.g. ['L3', 'L4', 'L5']
    reversed_set = set(logic_result.get('reversed_logics', []))  # e.g. {'L3'}
    active_preds = [logic_result['L1'], logic_result['L2'], logic_result['L3']]
    # active_preds[i] là pred (đã flip nếu reversed) của active[i]

    n_be = len(reversed_set)   # số logic bẻ trong top-3

    # ── CASE 1: Không có logic bẻ trong top-3 ────────────────────────────────
    if n_be == 0:
        # Fallback thuần: reversed_newsession + flip như v18
        rev_ns = _session_tuner.get('reversed_newsession', False)
        if rev_ns:
            pred_after_rev = _flip(majority)
            print(f"[ENSEMBLE] {group} → ⚡ REV-NS: {majority} → {pred_after_rev}")
        else:
            pred_after_rev = majority

        flip = _session_tuner.get('flip_mode', False)
        if flip:
            ensemble = _flip(pred_after_rev)
            print(f"[ENSEMBLE] {group} → 🔄 FLIP {pred_after_rev} → {ensemble}")
        else:
            ensemble = pred_after_rev
            if not rev_ns:
                print(f"[ENSEMBLE] {group} → THEO majority = {ensemble}")

        return ensemble, group, False, 1.0

    # ── CASE 2: Top-3 full bẻ (3 logic đều bẻ) → theo bình thường ───────────
    if n_be == 3:
        rev_ns = _session_tuner.get('reversed_newsession', False)
        if rev_ns:
            pred_after_rev = _flip(majority)
            print(f"[ENSEMBLE] {group} → 🔁 FULL BẺ + REV-NS: {majority} → {pred_after_rev}")
        else:
            pred_after_rev = majority

        flip = _session_tuner.get('flip_mode', False)
        if flip:
            ensemble = _flip(pred_after_rev)
            print(f"[ENSEMBLE] {group} → 🔁 FULL BẺ + FLIP {pred_after_rev} → {ensemble}")
        else:
            ensemble = pred_after_rev
            if not rev_ns:
                print(f"[ENSEMBLE] {group} → 🔁 FULL BẺ (3/3) → THEO majority = {ensemble}")

        return ensemble, group, False, 1.0

    # ── CASE 3: Top-3 có 2 logic bẻ ─────────────────────────────────────────
    # Phân biệt 2 sub-case:
    #   3a. 2 logic bẻ ĐỒNG THUẬN nhau (cùng pred TAI hoặc cùng XIU)
    #       → THEO kết quả của 2 logic bẻ (không theo thiểu số).
    #   3b. 2 logic bẻ KHÔNG ĐỒNG THUẬN (1 bẻ đồng thuận vs logic thường,
    #       còn logic bẻ kia bất đồng) → theo THIỂU SỐ tức theo BẺ2.
    if n_be == 2:
        tai_c = active_preds.count('TAI')
        xiu_c = active_preds.count('XIU')
        vote_str = f"{max(tai_c,xiu_c)}-{min(tai_c,xiu_c)}"

        # Tìm pred của 2 logic bẻ và 1 logic thường
        be_indices    = [i for i, n in enumerate(active) if n in reversed_set]
        thuan_indices = [i for i, n in enumerate(active) if n not in reversed_set]

        be_preds    = [active_preds[i] for i in be_indices]    # pred 2 logic bẻ (đã flip)
        thuan_preds = [active_preds[i] for i in thuan_indices] # pred logic thường

        # Sub-case 3a: 2 logic bẻ đồng thuận nhau
        if be_preds[0] == be_preds[1]:
            consensus_be = be_preds[0]
            if tai_c == 3 or xiu_c == 3:
                # 3-0: cả 3 cùng đoán (2 bẻ + 1 thường cùng chiều) → bẻ ngược như cũ
                flip_pred = _flip(majority)
                print(f"[ENSEMBLE] {group} → 🔁 2-BẺ ĐỒNG THUẬN 3-0: vote=3-0 majority={majority} "
                      f"→ BẺ NGƯỢC = {flip_pred}")
                return flip_pred, group, False, 1.0
            else:
                # 2-1: 2 bẻ đồng thuận, logic thường khác chiều → theo 2 bẻ
                print(f"[ENSEMBLE] {group} → ✅ 2-BẺ ĐỒNG THUẬN 2-1: cả 2 bẻ đều dự đoán "
                      f"{consensus_be} (vote={vote_str} majority={majority}) → THEO 2-BẺ = {consensus_be}")
                return consensus_be, group, False, 1.0

        # Sub-case 3b: 2 logic bẻ không đồng thuận
        # BẺ1 đồng pred với logic thường → 2 người cùng chiều (majority)
        # BẺ2 đứng một mình → chính là thiểu số
        # → theo thiểu số (pred khác với 2 logic đồng thuận kia)
        minority_pred = _minority_vote(active_preds, majority)
        thuan_pred = thuan_preds[0] if thuan_preds else None
        print(f"[ENSEMBLE] {group} → ⚔️  2-BẺ KHÔNG ĐỒNG THUẬN: "
              f"thường={thuan_pred} bẻ1={be_preds[0]} bẻ2={be_preds[1]} "
              f"(vote={vote_str} majority={majority}) → THIỂU SỐ = {minority_pred}")
        return minority_pred, group, False, 1.0

    # ── CASE 4 & 5: Top-3 có đúng 1 logic bẻ ────────────────────────────────
    # n_be == 1
    lt_bench    = _logic_tuner.get('last_bench')
    be_dominant = False
    dominant_pred = None
    be_name = None
    be_wr   = None
    thuan_wrs = []

    if lt_bench:
        be_name   = list(reversed_set)[0]
        eff_wr    = lt_bench.get('eff_wr', {})
        be_wr     = eff_wr.get(be_name)

        if be_wr is not None:
            thuan_logics = [n for n in active if n not in reversed_set]
            thuan_wrs    = [eff_wr.get(n) for n in thuan_logics if eff_wr.get(n) is not None]

            # CASE 4 — BẺ ĐỘC TÔN MẠNH: WR bẻ cao hơn TẤT CẢ logic thuận > 15%
            # Điều kiện: be_wr phải hơn MỖI logic thuần ít nhất 15 điểm % (0.15)
            # Nếu chỉ hơn 1 trong 2 logic thuần, hoặc không đủ 15% → YẾU
            BE_DOMINANT_MIN_GAP = 0.15   # 15% gap so với mỗi logic thuần
            if thuan_wrs and all(be_wr - tw >= BE_DOMINANT_MIN_GAP for tw in thuan_wrs):
                try:
                    be_idx        = active.index(be_name)
                    dominant_pred = active_preds[be_idx]   # đã flip sẵn
                    be_dominant   = True
                except (ValueError, IndexError):
                    be_dominant = False

    # CASE 4: BẺ ĐỘC TÔN MẠNH → theo pred của logic bẻ (chỉ khi hơn 2 logic thuần ≥15%)
    if be_dominant and dominant_pred:
        gaps = [round((be_wr - tw) * 100, 1) for tw in thuan_wrs]
        print(f"[ENSEMBLE] {group} → 🔱 BẺ ĐỘC TÔN MẠNH [{be_name} eff_wr={be_wr:.1%}] "
              f"gap={gaps}% > thuận={[round(w,3) for w in thuan_wrs]} → THEO BẺ = {dominant_pred} "
              f"(bỏ majority={majority})")
        return dominant_pred, group, False, 1.0

    # CASE 5 — BẺ ĐỘC TÔN YẾU: WR bẻ chưa hơn đủ 15% so với tất cả logic thuần → THIỂU SỐ
    minority_pred = _minority_vote(active_preds, majority)
    tai_c = active_preds.count('TAI')
    xiu_c = active_preds.count('XIU')
    vote_str = f"{max(tai_c,xiu_c)}-{min(tai_c,xiu_c)}"
    if be_wr is not None and thuan_wrs:
        gaps = [round((be_wr - tw) * 100, 1) for tw in thuan_wrs]
        wr_tag = f"[{be_name} eff_wr={be_wr:.1%} gap={gaps}% <15%]"
    else:
        wr_tag = f"[{be_name}]"
    print(f"[ENSEMBLE] {group} → 🔻 BẺ ĐỘC TÔN YẾU {wr_tag} → "
          f"vote={vote_str} majority={majority} → THIỂU SỐ = {minority_pred}")
    return minority_pred, group, False, 1.0


def update_cross_comp(sess_id, case_type, actual_result, pred_made):
    """v15 — No-op: cross-compensation đã bị gỡ."""
    pass

# ─── SSE broadcast ────────────────────────────────────────────────────────────
async def broadcast(event: str, data: dict):
    payload = f"event: {event}\ndata: {json.dumps(data, ensure_ascii=False)}\n\n"
    dead = set()
    for q in list(app_state['sse_clients']):
        try:
            await q.put(payload)
        except Exception:
            dead.add(q)
    app_state['sse_clients'] -= dead

# ─── MD5 verify ──────────────────────────────────────────────────────────────
def verify_md5(sess_id, md5_raw, expected_md5):
    try:
        computed = hashlib.md5(md5_raw.encode()).hexdigest()
        return computed == expected_md5
    except Exception:
        return False

# ─── Telegram helpers ─────────────────────────────────────────────────────────
async def tg_send(chat_id: int, text: str):
    try:
        async with aiohttp.ClientSession() as session:
            await session.post(
                f'{TG_API}/sendMessage',
                json={'chat_id': chat_id, 'text': text, 'parse_mode': 'HTML'},
                timeout=aiohttp.ClientTimeout(total=10)
            )
    except Exception as e:
        print(f"[TG SEND ERR] {e}")

async def tg_broadcast(text: str):
    """Gửi đến tất cả subscriber còn hạn key VÀ notify=True"""
    dead = []
    now  = _now_ts()
    for chat_id, info in list(tg_subscribers.items()):
        # Skip nếu notify=False (đã /stop)
        if not info.get('notify', True):
            continue

        # Skip nếu key hết hạn (trừ admin)
        if chat_id != ADMIN_ID:
            key_exp = info.get('key_exp', 0)
            if key_exp and now > key_exp:
                dead.append(chat_id)
                await tg_send(chat_id, f'⏰ <b>Key của bạn đã hết hạn.</b>\nLiên hệ admin để gia hạn: {ADMIN_USERNAME}')
                continue

        try:
            async with aiohttp.ClientSession() as session:
                r = await session.post(
                    f'{TG_API}/sendMessage',
                    json={'chat_id': chat_id, 'text': text, 'parse_mode': 'HTML'},
                    timeout=aiohttp.ClientTimeout(total=10)
                )
                data = await r.json()
                if not data.get('ok'):
                    err_code = data.get('error_code', 0)
                    if err_code in (403, 400):
                        dead.append(chat_id)
        except Exception as e:
            print(f"[TG BROADCAST ERR] {chat_id}: {e}")

    for cid in dead:
        tg_subscribers.pop(cid, None)
    if dead:
        save_subs()

async def tg_poll_loop():
    """Long-polling Telegram updates — full command system"""
    global tg_offset
    print("[TG] Bot polling bắt đầu...")
    while True:
        try:
            async with aiohttp.ClientSession() as session:
                resp = await session.get(
                    f'{TG_API}/getUpdates',
                    params={'offset': tg_offset, 'timeout': 30, 'allowed_updates': ['message']},
                    timeout=aiohttp.ClientTimeout(total=40)
                )
                data = await resp.json()
                if not data.get('ok'):
                    await asyncio.sleep(5)
                    continue

                for update in data.get('result', []):
                    tg_offset = update['update_id'] + 1
                    msg     = update.get('message', {})
                    chat_id = msg.get('chat', {}).get('id')
                    raw_txt = msg.get('text', '').strip()
                    if not chat_id or not raw_txt:
                        continue

                    uinfo = get_user_info(msg)

                    # ── AutoBet multi-step input handler ────────────────────
                    if chat_id in _auto_bet_pending:
                        pend = _auto_bet_pending[chat_id]
                        step = pend.get('step', '')

                        if step == 'await_username':
                            pend['username'] = raw_txt.strip()
                            pend['step']     = 'await_password'
                            await tg_send(chat_id, '🔑 Nhập <b>mật khẩu</b> tài khoản LC79:')
                            continue

                        elif step == 'await_password':
                            username = pend.get('username', '')
                            password = raw_txt.strip()
                            await tg_send(chat_id, '⏳ Đang đăng nhập...')
                            jwt, balance, nick = await lc79_auto_login(username, password)
                            if not jwt:
                                await tg_send(chat_id,
                                    '❌ <b>Đăng nhập thất bại!</b>\n'
                                    'Kiểm tra lại tên đăng nhập / mật khẩu.\n'
                                    'Thử lại: /autobet')
                                del _auto_bet_pending[chat_id]
                                continue
                            pend['jwt']     = jwt
                            pend['balance'] = balance
                            pend['nick']    = nick
                            pend['step']    = 'await_bet_amount'
                            await tg_send(chat_id,
                                f'✅ <b>Đăng nhập thành công!</b>\n'
                                f'Tài khoản: <b>{nick}</b>\n'
                                f'Số dư: <b>{balance:,}</b> CHS\n'
                                f'━━━━━━━━━━━━━━\n'
                                f'Nhập <b>số tiền cược mỗi ván</b> (VD: 1000):')
                            continue

                        elif step == 'await_bet_amount':
                            try:
                                bet_amount = int(raw_txt.strip().replace(',', '').replace('.', ''))
                                if bet_amount <= 0: raise ValueError
                                pend['bet_amount'] = bet_amount
                                pend['step']       = 'await_loss_config'
                                await tg_send(chat_id,
                                    f'💰 Số tiền cược: <b>{bet_amount:,}</b>/ván\n'
                                    f'━━━━━━━━━━━━━━\n'
                                    f'Khi <b>THUA</b>, bạn muốn:\n'
                                    f'1️⃣ X2 tiền cược (Martingale)\n'
                                    f'2️⃣ Giữ nguyên số tiền cược\n'
                                    f'3️⃣ Reset về mức ban đầu\n'
                                    f'Nhập số lựa chọn (1/2/3):')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên dương. VD: 1000')
                            continue

                        elif step == 'await_loss_config':
                            choice = raw_txt.strip()
                            if choice == '1':
                                pend['double_on_loss'] = True
                                pend['reset_on_loss']  = False
                            elif choice == '3':
                                pend['double_on_loss'] = False
                                pend['reset_on_loss']  = True
                            else:
                                pend['double_on_loss'] = False
                                pend['reset_on_loss']  = False
                            pend['step'] = 'await_win_config'
                            await tg_send(chat_id,
                                f'Khi <b>THẮNG</b>, bạn muốn:\n'
                                f'1️⃣ X2 tiền cược\n'
                                f'2️⃣ Giữ nguyên số tiền cược\n'
                                f'3️⃣ Reset về mức ban đầu\n'
                                f'Nhập số lựa chọn (1/2/3):')
                            continue

                        elif step == 'await_win_config':
                            choice = raw_txt.strip()
                            if choice == '1':
                                pend['double_on_win'] = True
                                pend['reset_on_win']  = False
                            elif choice == '3':
                                pend['double_on_win'] = False
                                pend['reset_on_win']  = True
                            else:
                                pend['double_on_win'] = False
                                pend['reset_on_win']  = False
                            # v31: nếu chọn x2 khi thắng → hỏi thêm bao nhiêu ván
                            if pend.get('double_on_win'):
                                pend['step'] = 'await_win_streak_x2'
                                await tg_send(chat_id,
                                    '🔢 <b>Thắng liên tiếp bao nhiêu ván thì x2?</b>\n'
                                    'Ví dụ: nhập <b>3</b> → thắng 3 ván liên tiếp mới x2\n'
                                    '(Nhập 0 hoặc 1 = x2 ngay từ ván thắng đầu tiên):')
                            else:
                                pend['win_streak_x2'] = 0
                                pend['step'] = 'await_loss_reduce'
                                await tg_send(chat_id,
                                    '🔻 <b>Giảm cược khi thua liên tiếp?</b>\n'
                                    'Thua bao nhiêu ván liên tiếp thì giảm cược?\n'
                                    '(Nhập 0 nếu không muốn giảm cược):')
                            continue

                        elif step == 'await_win_streak_x2':
                            try:
                                wx2 = int(raw_txt.strip())
                                if wx2 < 0: raise ValueError
                                pend['win_streak_x2'] = max(wx2, 1) if wx2 > 0 else 1
                                pend['step'] = 'await_loss_reduce'
                                await tg_send(chat_id,
                                    '🔻 <b>Giảm cược khi thua liên tiếp?</b>\n'
                                    'Thua bao nhiêu ván liên tiếp thì giảm cược?\n'
                                    '(Nhập 0 nếu không muốn giảm cược):')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên ≥ 0. VD: 3')
                            continue

                        elif step == 'await_loss_reduce':
                            try:
                                lr = int(raw_txt.strip())
                                if lr < 0: raise ValueError
                                pend['loss_streak_reduce'] = lr
                                if lr > 0:
                                    pend['step'] = 'await_reduced_bet'
                                    base = pend.get('bet_amount', 0)
                                    await tg_send(chat_id,
                                        f'💸 <b>Mức cược giảm là bao nhiêu?</b>\n'
                                        f'Cược gốc của bạn: <b>{base:,}</b>\n'
                                        f'Nhập số tiền cược sau khi giảm (VD: {base//2:,}):')
                                else:
                                    pend['loss_streak_reduce'] = 0
                                    pend['reduced_bet']        = 0
                                    pend['step'] = 'await_loss_streak'
                                    await tg_send(chat_id,
                                        '🔴 <b>Dừng/Pause khi thua liên tiếp bao nhiêu ván?</b>\n'
                                        '(Nhập 0 nếu không muốn giới hạn):')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên ≥ 0.')
                            continue

                        elif step == 'await_reduced_bet':
                            try:
                                rb = int(raw_txt.strip().replace(',', '').replace('.', ''))
                                if rb <= 0: raise ValueError
                                base = pend.get('bet_amount', 0)
                                if rb >= base:
                                    await tg_send(chat_id,
                                        f'⚠️ Mức cược giảm phải nhỏ hơn cược gốc (<b>{base:,}</b>).\n'
                                        f'Nhập lại:')
                                    continue
                                pend['reduced_bet'] = rb
                                pend['step'] = 'await_loss_streak'
                                await tg_send(chat_id,
                                    '🔴 <b>Dừng/Pause khi thua liên tiếp bao nhiêu ván?</b>\n'
                                    '(Nhập 0 nếu không muốn giới hạn):')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên dương. VD: 2000')
                            continue

                        elif step == 'await_loss_streak':
                            try:
                                ls = int(raw_txt.strip())
                                if ls < 0: raise ValueError
                                pend['loss_streak_stop'] = ls
                                pend['step']             = 'await_win_streak'
                                await tg_send(chat_id,
                                    '🟢 Tiếp tục cược khi thắng liên tiếp bao nhiêu ván?\n'
                                    '(Nhập 0 nếu không quan tâm):')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên ≥ 0.')
                            continue

                        elif step == 'await_win_streak':
                            try:
                                ws_val = int(raw_txt.strip())
                                if ws_val < 0: raise ValueError
                                pend['win_streak_cont'] = ws_val
                                pend['step'] = 'await_profit_target'
                                await tg_send(chat_id,
                                    '🎯 <b>Mục tiêu lợi nhuận</b>\n'
                                    'Bot tự dừng khi lãi đủ số này.\n'
                                    '(VD: 200000 → dừng khi lãi ≥ 200,000)\n'
                                    'Nhập 0 nếu không giới hạn:')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên ≥ 0.')
                            continue

                        elif step == 'await_profit_target':
                            try:
                                pt = int(raw_txt.strip().replace(',', '').replace('.', ''))
                                if pt < 0: raise ValueError
                                pend['profit_target'] = pt
                                # Tất cả config đã xong — tạo session
                                ledger = AutoBetLedger(pend['balance'], pend['nick'])
                                martingale = pend.get('double_on_loss', False)
                                sess = AutoBetSession(
                                    chat_id             = chat_id,
                                    jwt                 = pend['jwt'],
                                    ledger              = ledger,
                                    base_bet            = pend['bet_amount'],
                                    martingale          = martingale,
                                    double_on_win       = pend.get('double_on_win', False),
                                    win_streak_x2       = pend.get('win_streak_x2', 0),
                                    reset_on_win        = pend.get('reset_on_win', False),
                                    double_on_loss      = pend.get('double_on_loss', False),
                                    reset_on_loss       = pend.get('reset_on_loss', False),
                                    loss_streak_stop    = pend.get('loss_streak_stop', 0),
                                    win_streak_cont     = pend.get('win_streak_cont', 0),
                                    profit_target       = pt,
                                    loss_streak_reduce  = pend.get('loss_streak_reduce', 0),
                                    reduced_bet         = pend.get('reduced_bet', 0),
                                )
                                _auto_bet_sessions[chat_id] = sess
                                del _auto_bet_pending[chat_id]
                                # Đảm bảo user đang nhận broadcast dự đoán
                                if chat_id not in tg_subscribers:
                                    ku = key_users.get(chat_id)
                                    if ku:
                                        ku['notify'] = True
                                        tg_subscribers[chat_id] = {
                                            'name': ku.get('name', str(chat_id)),
                                            'username': ku.get('username', ''),
                                            'joined': ku.get('joined', _now_ts()),
                                            'key': ku.get('key', ''),
                                            'key_exp': ku.get('key_exp', 0),
                                            'notify': True,
                                        }
                                _dow  = pend.get('double_on_win', False)
                                _wx2  = pend.get('win_streak_x2', 0)
                                _lsr  = pend.get('loss_streak_reduce', 0)
                                _rb   = pend.get('reduced_bet', 0)
                                mode_loss = ("x2 Martingale" if pend.get('double_on_loss')
                                             else ("Reset về gốc" if pend.get('reset_on_loss')
                                             else "Giữ nguyên"))
                                if _dow:
                                    _thr  = _wx2 if _wx2 > 0 else 1
                                    mode_win = f"x2 sau {_thr} ván thắng liên tiếp"
                                elif pend.get('reset_on_win'):
                                    mode_win = "Reset về gốc"
                                else:
                                    mode_win = "Giữ nguyên"
                                ls_txt   = f"{pend.get('loss_streak_stop')} ván" if pend.get('loss_streak_stop') else "Không giới hạn"
                                ws_txt   = f"{pend.get('win_streak_cont')} ván liên tiếp" if pend.get('win_streak_cont') else "Mọi ván"
                                pt_txt   = f"{pt:,}" if pt > 0 else "Không giới hạn"
                                lr_txt   = (f"Sau {_lsr} ván thua liên tiếp → giảm xuống {_rb:,}"
                                            if _lsr > 0 else "Không giảm cược")
                                await tg_send(chat_id,
                                    f'✅ <b>Auto-cược đã khởi động!</b>\n'
                                    f'━━━━━━━━━━━━━━\n'
                                    f'👤 Tài khoản: <b>{pend["nick"]}</b>\n'
                                    f'💰 Số dư: <b>{pend["balance"]:,}</b> CHS\n'
                                    f'🎲 Cược/ván: <b>{pend["bet_amount"]:,}</b>\n'
                                    f'🟢 Thắng → {mode_win}\n'
                                    f'🔴 Thua → {mode_loss}\n'
                                    f'🔻 Giảm cược: {lr_txt}\n'
                                    f'🚨 Pause khi thua liên tiếp: {ls_txt}\n'
                                    f'▶️ Resume khi thắng: {ws_txt}\n'
                                    f'🎯 Mục tiêu lãi: {pt_txt}\n'
                                    f'━━━━━━━━━━━━━━\n'
                                    f'Tool sẽ tự động cược theo dự đoán mỗi phiên.\n'
                                    f'Dùng /stopbet để dừng. /betstatus để xem tiến độ.')
                            except ValueError:
                                await tg_send(chat_id, '⚠️ Nhập số nguyên ≥ 0. VD: 200000')
                            continue

                        # Unknown step — reset
                        del _auto_bet_pending[chat_id]

                    # ── End AutoBet multi-step ──────────────────────────────

                    parts = raw_txt.split()
                    cmd   = parts[0].lower().split('@')[0]

                    # ── Ban check (skip admin) ───────────────────────────────
                    if chat_id != ADMIN_ID and is_banned(chat_id):
                        unban_ts = tg_banned.get(chat_id, 0)
                        if unban_ts == -1:
                            await tg_send(chat_id, '🚫 <b>Bạn đã bị cấm vĩnh viễn.</b>')
                        else:
                            dt = datetime.fromtimestamp(unban_ts).strftime('%d/%m/%Y %H:%M')
                            await tg_send(chat_id, f'🚫 <b>Bạn đang bị cấm</b> đến <code>{dt}</code>.')
                        continue

                    # ════════════════════════════════════════════════════════
                    # ADMIN COMMANDS
                    # ════════════════════════════════════════════════════════
                    if chat_id == ADMIN_ID:

                        # /newkey <days> [max_users]  — tạo key mới (chỉ admin)
                        if cmd == '/newkey':
                            if len(parts) < 2 or not parts[1].isdigit():
                                await tg_send(chat_id,
                                    '⚠️ Dùng:\n'
                                    '<code>/newkey &lt;số ngày&gt; [số người tối đa]</code>\n\n'
                                    'Ví dụ:\n'
                                    '• <code>/newkey 7</code> — key 7 ngày, 1 người\n'
                                    '• <code>/newkey 30 5</code> — key 30 ngày, tối đa 5 người\n'
                                    '• <code>/newkey 7 100</code> — key 7 ngày, tối đa 100 người')
                                continue
                            days      = min(max(int(parts[1]), 1), 365)
                            max_users = 1
                            if len(parts) >= 3 and parts[2].isdigit():
                                max_users = min(max(int(parts[2]), 1), 100)
                            key = gen_key(days, max_users)
                            exp = datetime.fromtimestamp(_now_ts() + days * 86400).strftime('%d/%m/%Y')
                            slot_txt = f'{max_users} người' if max_users > 1 else '1 người (riêng)'
                            await tg_send(chat_id,
                                f'🔑 <b>Key mới tạo:</b>\n'
                                f'<code>{key}</code>\n'
                                f'Hạn: <b>{days} ngày</b> (hết {exp})\n'
                                f'Slot: <b>{slot_txt}</b>\n'
                                f'Trạng thái: chưa có ai dùng')

                        # /sub  — danh sách subscriber
                        elif cmd == '/sub':
                            if not tg_subscribers:
                                await tg_send(chat_id, '📋 Chưa có ai đăng ký.')
                                continue
                            lines = []
                            for i, (cid, info) in enumerate(tg_subscribers.items(), 1):
                                name = info.get('name', 'Unknown')
                                uname = f"@{info['username']}" if info.get('username') else ''
                                key_exp = info.get('key_exp', 0)
                                if key_exp:
                                    exp_str = datetime.fromtimestamp(key_exp).strftime('%d/%m/%Y')
                                    exp_tag = f"key hết {exp_str}"
                                else:
                                    exp_tag = 'no key'
                                lines.append(f"{i}. <b>{name}</b> {uname}\n   ID: <code>{cid}</code> | {exp_tag}")
                            await tg_send(chat_id,
                                f'👥 <b>Subscribers ({len(tg_subscribers)}):</b>\n\n' + '\n\n'.join(lines))

                        # /kick <chat_id>  — xoá khỏi sub list + đánh dấu kicked (không gửi TB)
                        elif cmd == '/kick':
                            if len(parts) < 2 or not parts[1].lstrip('-').isdigit():
                                await tg_send(chat_id, '⚠️ Dùng: <code>/kick &lt;chat_id&gt;</code>')
                                continue
                            target = int(parts[1])
                            name = (tg_subscribers.get(target) or key_users.get(target) or {}).get('name', str(target))
                            removed = False
                            if target in tg_subscribers:
                                del tg_subscribers[target]
                                removed = True
                            # Đánh dấu notify=False trong key_users để không nhận dự đoán
                            # (user phải /tool lại mới nhận được — key vẫn còn hiệu lực)
                            if target in key_users:
                                key_users[target]['notify'] = False
                                key_users[target]['kicked'] = True   # flag: bị kick
                                save_key_users()
                                removed = True
                            save_subs()
                            if removed:
                                # Không gửi thông báo cho người bị kick
                                await tg_send(chat_id, f'👢 Đã kick <b>{name}</b> (<code>{target}</code>).\nUser sẽ không nhận dự đoán cho đến khi dùng /tool trở lại.')
                            else:
                                await tg_send(chat_id, f'⚠️ ID <code>{target}</code> không có trong danh sách.')

                        # /ban <chat_id> <days>  — ban tạm hoặc vĩnh viễn (days=0)
                        elif cmd == '/ban':
                            if len(parts) < 3 or not parts[1].lstrip('-').isdigit() or not parts[2].isdigit():
                                await tg_send(chat_id, '⚠️ Dùng: <code>/ban &lt;chat_id&gt; &lt;số ngày 1-10, hoặc 0=vĩnh viễn&gt;</code>')
                                continue
                            target = int(parts[1])
                            days   = min(int(parts[2]), 10)
                            name = (tg_subscribers.get(target) or key_users.get(target) or {}).get('name', str(target))
                            if target in tg_subscribers:
                                del tg_subscribers[target]
                            # Xóa notify trong key_users
                            if target in key_users:
                                key_users[target]['notify'] = False
                                save_key_users()
                            if days == 0:
                                tg_banned[target] = -1
                                label = 'vĩnh viễn'
                                # Không gửi TB cho người bị ban
                            else:
                                tg_banned[target] = _now_ts() + days * 86400
                                exp_dt = datetime.fromtimestamp(tg_banned[target]).strftime('%d/%m/%Y %H:%M')
                                label  = f'{days} ngày (đến {exp_dt})'
                                # Không gửi TB cho người bị ban
                            save_subs()
                            await tg_send(chat_id, f'🔨 Đã ban <b>{name}</b> (<code>{target}</code>) — {label}.')


                        # /broadcast <message> — gửi thông báo đến toàn bộ user đã /start
                        elif cmd in ('/broadcast', '/announce', '/tb'):
                            if len(parts) < 2:
                                await tg_send(chat_id,
                                    '📢 Dùng: <code>/broadcast &lt;nội dung thông báo&gt;</code>\n\n'
                                    'Bot sẽ gửi thông báo đến toàn bộ user đã /start.\n'
                                    'Ví dụ: <code>/broadcast Tool đang bảo trì, vui lòng chờ...</code>')
                                continue
                            msg_txt = raw_txt[len(parts[0]):].strip()
                            await tg_send(chat_id, f'📤 Đang gửi thông báo đến <b>{len(started_users)}</b> user...')
                            sent = 0
                            failed = 0
                            for uid in list(started_users):
                                try:
                                    async with aiohttp.ClientSession() as sess_http:
                                        r = await sess_http.post(
                                            f'{TG_API}/sendMessage',
                                            json={'chat_id': uid,
                                                  'text': f'📢 <b>Thông báo từ Admin</b>\n━━━━━━━━━━━━━━\n{msg_txt}',
                                                  'parse_mode': 'HTML'},
                                            timeout=aiohttp.ClientTimeout(total=10)
                                        )
                                        rd = await r.json()
                                        if rd.get('ok'):
                                            sent += 1
                                        else:
                                            failed += 1
                                except Exception:
                                    failed += 1
                            await tg_send(chat_id,
                                f'✅ <b>Đã gửi thông báo!</b>\n'
                                f'Thành công: <b>{sent}</b> user\n'
                                f'Thất bại: <b>{failed}</b> user')

                        # /help admin — full lệnh
                        elif cmd in ('/help', '/start'):
                            await tg_send(chat_id,
                                '⚙️ <b>ADMIN — Toàn bộ lệnh</b>\n\n'
                                '🔑 <b>Tạo Key</b>\n'
                                '/newkey &lt;ngày&gt; [số người] — Tạo key mới\n'
                                '  VD: /newkey 7 → 7 ngày, 1 người\n'
                                '  VD: /newkey 30 5 → 30 ngày, 5 người\n\n'
                                '👥 <b>Quản lý user</b>\n'
                                '/sub — Xem danh sách subscriber\n'
                                '/kick &lt;chat_id&gt; — Xoá user khỏi danh sách\n'
                                '/ban &lt;chat_id&gt; &lt;ngày&gt; — Ban user (0=vĩnh viễn)\n\n'
                                '📢 <b>Thông báo</b>\n'
                                '/broadcast &lt;nội dung&gt; — Gửi TB đến toàn bộ user\n\n'
                                '📊 <b>Thống kê</b>\n'
                                '/status — Xem trạng thái đầy đủ (DB, users, keys)\n'
                                '/history — Xem 30 phiên đúng/sai gần nhất\n\n'
                                '🛠 <b>Dùng tool (admin nhập key như user)</b>\n'
                                '/key &lt;XXXX-XXXX-XXXX&gt; — Kích hoạt key\n'
                                '/tool — Bật nhận dự đoán\n'
                                '/stop — Tắt nhận dự đoán\n'
                                '/autobet — Đăng nhập & thiết lập auto-cược LC79\n'
                                '/stopbet — Dừng auto-cược\n'
                                '/betstatus — Trạng thái auto-cược hiện tại\n\n'
                                '🔄 <b>Reload Logic (chỉ admin)</b>\n'
                                '/reloadlogic — Ép đổi ttoan ngay lập tức\n'
                                '  • Đổi ttoan ngay (giống khi sai 3 lần), kể cả đang chuỗi thắng\n'
                                '  • Reset TTOAN tracker (vans_since_swap, history_since_swap, real_vans)\n'
                                '  • Xóa chuỗi sai liên tiếp — không carry-over sang ttoan mới\n'
                                '  • KHÔNG đụng rolling history 9 logic\n\n'
                                '/clearlogic — Clear sạch rolling history 9 logic + re-tune\n'
                                '  • Reset rolling history 9 logic (clear sạch)\n'
                                '  • Reset active logics → re-tune từ history thật\n'
                                '  • Reset session offset tuner\n'
                                '  • Reset adaptive TT1/TT2\n'
                                '  • KHÔNG đổi ttoan\n'
                                '  ⚠️ User thường không thấy 2 lệnh này')

                        # ── /reloadlogic — CHỈ ép đổi ttoan ngay lập tức ──────────────
                        # (giống khi sai 3 lần liên tiếp, KHÔNG clear rolling history)
                        elif cmd == '/reloadlogic':
                            # ── Reset TTOAN tracker + đổi ttoan ngay ──────────────────
                            _ttoan_tracker['vans_since_swap']      = 0
                            _ttoan_tracker['history_since_swap']   = []
                            _ttoan_tracker['pre_trim_count']       = 0
                            _ttoan_tracker['real_vans_since_swap'] = 0
                            _ttoan_tracker['last_swap_at_live']    = app_state['live_count']
                            _ttoan_tracker['swap_count']          += 1
                            _ttoan_tracker['last_swap_reason']     = 'manual_reload'

                            swap_no  = _ttoan_tracker['swap_count']
                            cur_top3 = _logic_tuner.get('active_logics', [])
                            cur_rev  = list(_logic_tuner.get('reversed_logics', set()))
                            top3_str = ' · '.join(f'<code>{l}</code>' for l in cur_top3)
                            rev_str  = (', '.join(f'<code>{l}</code>' for l in cur_rev)
                                        if cur_rev else '—')

                            print(f"[RELOADLOGIC] Admin ép đổi ttoan #{swap_no} "
                                  f"@ live#{app_state['live_count']} "
                                  f"(rolling history GIỮ NGUYÊN)")

                            await tg_send(chat_id,
                                f'🔀 <b>RELOAD TTOAN — Hoàn tất</b>\n'
                                f'━━━━━━━━━━━━━━\n'
                                f'✅ Đã ép đổi ttoan ngay lập tức:\n'
                                f'  • TTOAN tracker reset (lần đổi #{swap_no})\n'
                                f'  • Chuỗi sai liên tiếp xóa sạch\n'
                                f'  • vans_since_swap, history_since_swap reset về 0\n\n'
                                f'🧠 <b>Logic hiện tại (GIỮ NGUYÊN):</b>\n'
                                f'  Top-3: {top3_str}\n'
                                f'  BẺ chiều: {rev_str}\n'
                                f'━━━━━━━━━━━━━━\n'
                                f'⚡ Ttoan mới có hiệu lực từ phiên kế tiếp.\n'
                                f'💡 Dùng /clearlogic để clear rolling history 9 logic.\n'
                                f'<i>(Lệnh này chỉ admin thấy)</i>')

                        # ── /clearlogic — Clear sạch rolling history 9 logic + re-tune ─
                        # (KHÔNG đổi ttoan)
                        elif cmd == '/clearlogic':
                            # ── Step 1: Reset toàn bộ rolling history của 9 logic ──────
                            for name in ALL_LOGICS:
                                _logic_tuner['history'][name].clear()
                            _logic_tuner['since_tune']      = 0
                            _logic_tuner['last_bench']      = None
                            _logic_tuner['active_logics']   = ['L1', 'L2', 'L3']
                            _logic_tuner['reversed_logics'] = set()
                            _logic_tuner['total_preds']     = 0
                            _logic_tuner['pending'].clear()

                            # ── Step 2: Reset session offset tuner ──────────────────────
                            for o in (-1, 0, 1):
                                _session_tuner['history'][o].clear()
                            _session_tuner['since_tune']          = 0
                            _session_tuner['last_bench']          = None
                            _session_tuner['pending'].clear()
                            _session_tuner['flip_mode']           = False
                            _session_tuner['flip_since']          = 0
                            _session_tuner['reversed_newsession'] = False
                            _session_tuner['reversed_ns_since']   = 0
                            _session_tuner['reversed_ns_bench']   = None

                            # ── Step 3: Reset adaptive history ──────────────────────────
                            _adaptive_history.clear()
                            _adaptive_groups['TT1']         = {'3-0', 'L2L3'}
                            _adaptive_groups['TT2']         = {'L1L2', 'L1L3'}
                            _adaptive_groups['source']      = 'default'
                            _adaptive_groups['computed_at'] = 0

                            # ── Step 4: Re-populate rolling history từ full history ──────
                            hist_w = get_history_window()
                            if len(hist_w) >= 5:
                                for entry in hist_w[-LOGIC_TUNE_WINDOW:]:
                                    sid_e = entry.get('sess', '')
                                    md5_e = entry.get('md5', '')
                                    act_e = entry.get('result', '')
                                    if not (sid_e and md5_e and act_e in ('TAI', 'XIU')):
                                        continue
                                    try:
                                        sid_plus1 = str(int(sid_e) + 1)
                                        X, Y, Z   = _calc_XYZ(int(sid_plus1), md5_e)
                                        for name in ALL_LOGICS:
                                            pred = _run_one_logic(name, X, Y, Z, md5_e)
                                            hist = _logic_tuner['history'][name]
                                            hist.append(pred == act_e)
                                            if len(hist) > LOGIC_TUNE_WINDOW:
                                                hist.pop(0)
                                    except Exception:
                                        continue

                            # ── Step 5: Re-tune logic ───────────────────────────────────
                            _run_logic_tune()

                            new_top3 = _logic_tuner['active_logics']
                            new_rev  = list(_logic_tuner.get('reversed_logics', set()))
                            top3_str = ' · '.join(f'<code>{l}</code>' for l in new_top3)
                            rev_str  = (', '.join(f'<code>{l}</code>' for l in new_rev)
                                        if new_rev else '—')
                            bench    = _logic_tuner.get('last_bench')
                            wr_lines = []
                            if bench and bench.get('eff_wr'):
                                for n in new_top3:
                                    eff     = bench['eff_wr'].get(n)
                                    rev_tag = ' 🔄[BẺ]' if n in (new_rev or []) else ''
                                    wr_lines.append(
                                        f'  {n}: <b>{eff:.1f}%</b>{rev_tag}' if eff else f'  {n}: —'
                                    )

                            swap_no = _ttoan_tracker['swap_count']
                            print(f"[CLEARLOGIC] Admin clear rolling history + re-tune "
                                  f"@ live#{app_state['live_count']} "
                                  f"→ top3={new_top3} rev={new_rev} "
                                  f"(ttoan GIỮ NGUYÊN, lần đổi #{swap_no})")

                            await tg_send(chat_id,
                                f'🧹 <b>CLEAR LOGIC — Hoàn tất</b>\n'
                                f'━━━━━━━━━━━━━━\n'
                                f'✅ Đã clear sạch:\n'
                                f'  • Rolling history 9 logic\n'
                                f'  • Active logics → re-tune từ history thật\n'
                                f'  • Session offset tuner\n'
                                f'  • Adaptive TT1/TT2\n'
                                f'  • Pending snapshots\n\n'
                                f'🔒 TTOAN GIỮ NGUYÊN (lần đổi #{swap_no})\n\n'
                                f'🧠 <b>Top-3 mới (re-tune từ history):</b>\n'
                                f'  {top3_str}\n'
                                + ('\n'.join(wr_lines) + '\n' if wr_lines else '')
                                + f'\n🔀 Logic BẺ chiều: {rev_str}\n'
                                f'━━━━━━━━━━━━━━\n'
                                f'💡 Dùng /reloadlogic để ép đổi ttoan.\n'
                                f'<i>(Lệnh này chỉ admin thấy)</i>')

                        else:
                            # admin dùng lệnh user bình thường
                            await _handle_user_cmd(chat_id, uinfo, cmd, parts)

                    # ════════════════════════════════════════════════════════
                    # USER COMMANDS
                    # ════════════════════════════════════════════════════════
                    else:
                        await _handle_user_cmd(chat_id, uinfo, cmd, parts)

        except asyncio.CancelledError:
            print("[TG] Poll task đã dừng")
            break
        except Exception as e:
            print(f"[TG POLL ERR] {e}")
            await asyncio.sleep(5)


async def _handle_user_cmd(chat_id: int, uinfo: dict, cmd: str, parts: list):
    """Xử lý lệnh user thường (và admin khi dùng lệnh user)"""
    is_sub = chat_id in tg_subscribers

    # ── Lệnh tự do: không cần key ──────────────────────────────────────────────
    FREE_CMDS = {'/start', '/key', '/help', '/history', '/autobet', '/stopbet', '/betstatus'}

    # /start — chào mừng + hướng dẫn cơ bản
    if cmd == '/start':
        # Ghi nhận user đã /start (để gửi broadcast)
        if chat_id not in started_users:
            started_users.add(chat_id)
            save_started_users()
        await tg_send(chat_id,
            '👋 <b>Chào mừng đến TX Tool!</b>\n\n'
            'Để bắt đầu, bạn cần nhập key:\n'
            '<code>/key XXXX-XXXX-XXXX</code>\n\n'
            f'💬 Liên hệ admin để mua key: {ADMIN_USERNAME}')
        return

    # /help — user thường thấy lệnh cơ bản
    if cmd == '/help':
        has_key = chat_id in key_users and _now_ts() <= key_users[chat_id].get('key_exp', 0)
        if has_key:
            await tg_send(chat_id,
                '📖 <b>Danh sách lệnh</b>\n\n'
                '📡 <b>Nhận dự đoán</b>\n'
                '/tool — Bật nhận dự đoán TX\n'
                '/stop — Tắt nhận dự đoán (key vẫn còn hạn)\n\n'
                '🤖 <b>Auto cược</b>\n'
                '/autobet — Đăng nhập & thiết lập auto-cược\n'
                '/stopbet — Dừng auto-cược và xem tổng kết\n'
                '/betstatus — Xem trạng thái auto-cược hiện tại\n\n'
                '📋 <b>Khác</b>\n'
                '/key &lt;KEY&gt; — Nhập / bật lại key\n'
                '/history — Xem kết quả đúng/sai 30 phiên gần nhất\n'
                '/help — Danh sách lệnh này\n\n'
                f'💬 Liên hệ admin để gia hạn key: {ADMIN_USERNAME}')
        else:
            await tg_send(chat_id,
                '📖 <b>Danh sách lệnh</b>\n\n'
                '/key &lt;KEY&gt; — Nhập key để kích hoạt tool\n'
                '/history — Xem kết quả đúng/sai 30 phiên gần nhất\n\n'
                f'💬 Liên hệ admin để mua key: {ADMIN_USERNAME}')
        return

    # ── Gate: lệnh khác bắt buộc phải có key hợp lệ ───────────────────────────
    if cmd not in FREE_CMDS:
        ku  = key_users.get(chat_id)
        now = _now_ts()
        if not ku:
            await tg_send(chat_id,
                f'🔒 <b>Bạn chưa có key.</b>\n'
                f'Nhập key để dùng tool:\n'
                f'<code>/key XXXX-XXXX-XXXX</code>\n\n'
                f'Liên hệ admin để mua key: {ADMIN_USERNAME}')
            return
        if now > ku.get('key_exp', 0):
            exp_dt = datetime.fromtimestamp(ku['key_exp']).strftime('%d/%m/%Y %H:%M')
            await tg_send(chat_id,
                f'⏰ <b>Key của bạn đã hết hạn</b> từ {exp_dt}.\n'
                f'Liên hệ admin để gia hạn: {ADMIN_USERNAME}')
            return

    # ── /key <KEY> — chỉ đăng ký / xác thực key, KHÔNG tự bật nhận dự đoán ───
    if cmd == '/key':
        if len(parts) < 2:
            await tg_send(chat_id,
                f'🔑 Nhập key theo cú pháp:\n'
                f'<code>/key XXXX-XXXX-XXXX</code>\n\n'
                f'Liên hệ admin để mua key: {ADMIN_USERNAME}')
            return

        key = parts[1].upper().strip()
        k   = tg_keys.get(key)
        now = _now_ts()

        # Key không tồn tại
        if not k:
            await tg_send(chat_id,
                f'❌ <b>Key không hợp lệ.</b>\n'
                f'Kiểm tra lại key hoặc liên hệ admin: {ADMIN_USERNAME}')
            return

        # Key hết hạn
        if now > k['expires']:
            await tg_send(chat_id,
                f'❌ <b>Key đã hết hạn.</b>\n'
                f'Liên hệ admin để gia hạn: {ADMIN_USERNAME}')
            return

        # Kiểm tra slot
        users_list = k.get('users', [])
        max_users  = k.get('max_users', 1)
        if not users_list and k.get('used_by') is not None:
            users_list = [k['used_by']]
            k['users'] = users_list

        if chat_id not in users_list and len(users_list) >= max_users:
            await tg_send(chat_id,
                f'❌ <b>Key đã đầy.</b>\n'
                f'Liên hệ admin để mua key khác: {ADMIN_USERNAME}')
            return

        # Ghi user vào key['users']
        if 'users' not in k:
            k['users'] = []
        if k.get('used_by') is not None and k['used_by'] not in k['users']:
            k['users'].append(k['used_by'])
        if chat_id not in k['users']:
            k['users'].append(chat_id)
        k['used_by'] = chat_id

        new_exp     = k['expires']
        existing_ku = key_users.get(chat_id, {})
        joined      = existing_ku.get('joined', now)

        # Ghi key_users — notify=False, chưa bật nhận dự đoán
        key_users[chat_id] = {
            'key':      key,
            'key_exp':  new_exp,
            'name':     uinfo['name'],
            'username': uinfo.get('username', ''),
            'joined':   joined,
            'notify':   False,
        }
        # KHÔNG thêm vào tg_subscribers — chưa bật nhận dự đoán

        save_keys()
        save_key_users()

        exp_dt   = datetime.fromtimestamp(new_exp).strftime('%d/%m/%Y %H:%M')
        days_rem = max(0, int((new_exp - now) / 86400))
        hrs_rem  = max(0, int(((new_exp - now) % 86400) / 3600))
        max_u    = k.get('max_users', 1)
        used_u   = len(k['users'])
        slot_info = f'Slot: {used_u}/{max_u} người\n' if max_u > 1 else ''
        await tg_send(chat_id,
            f'✅ <b>Key hợp lệ! Đã đăng ký.</b>\n\n'
            f'🔑 Key: <code>{key}</code>\n'
            f'📅 Hết hạn: <b>{exp_dt}</b>\n'
            f'⏳ Còn lại: <b>{days_rem} ngày {hrs_rem} giờ</b>\n'
            f'{slot_info}\n'
            f'Dùng /tool để bắt đầu nhận dự đoán TX.')
        print(f"[TG] {chat_id} ({uinfo['name']}) đăng ký key {key} [{used_u}/{max_u}] → exp {exp_dt}")
        return

    # ── /tool — bật nhận dự đoán (cần đã có key hợp lệ từ /key) ──────────────
    if cmd == '/tool':
        ku  = key_users.get(chat_id)
        now = _now_ts()
        # Guard: phải qua gate trước, nhưng double-check
        if not ku or now > ku.get('key_exp', 0):
            await tg_send(chat_id,
                '🔒 Bạn chưa có key hợp lệ.\n'
                'Dùng <code>/key KEY-XXXX-XXXX</code> để đăng ký trước.')
            return

        ku['notify'] = True
        ku.pop('kicked', None)   # xóa kicked flag nếu có
        save_key_users()

        tg_subscribers[chat_id] = {
            'name':     uinfo['name'],
            'username': uinfo.get('username', ''),
            'joined':   ku.get('joined', now),
            'key':      ku['key'],
            'key_exp':  ku['key_exp'],
            'notify':   True,
        }

        exp_dt   = datetime.fromtimestamp(ku['key_exp']).strftime('%d/%m/%Y %H:%M')
        days_rem = max(0, int((ku['key_exp'] - now) / 86400))
        hrs_rem  = max(0, int(((ku['key_exp'] - now) % 86400) / 3600))
        await tg_send(chat_id,
            f'🔔 <b>Đã bật nhận dự đoán!</b>\n\n'
            f'🔑 Key: <code>{ku["key"]}</code>\n'
            f'📅 Hết hạn: <b>{exp_dt}</b>\n'
            f'⏳ Còn lại: <b>{days_rem} ngày {hrs_rem} giờ</b>\n\n'
            f'Bạn sẽ nhận dự đoán TX mỗi phiên mới.\n'
            f'Dùng /stop để tạm ngừng.')
        print(f"[TG] {chat_id} ({uinfo['name']}) bật nhận dự đoán — key {ku['key']}")
        return

    # ── /stop — tắt nhận dự đoán ──────────────────────────────────────────────
    if cmd == '/stop':
        ku = key_users.get(chat_id)
        if ku:
            ku['notify'] = False
            save_key_users()
            tg_subscribers.pop(chat_id, None)
            key_str = ku.get('key', '')
            exp_dt  = datetime.fromtimestamp(ku.get('key_exp', 0)).strftime('%d/%m/%Y %H:%M') if ku.get('key_exp') else 'N/A'
            await tg_send(chat_id,
                f'🔕 <b>Đã tắt nhận dự đoán.</b>\n'
                f'Key <code>{key_str}</code> vẫn còn hạn đến <b>{exp_dt}</b>.\n'
                f'Dùng /tool để bật lại bất cứ lúc nào.')
        elif is_sub:
            tg_subscribers.pop(chat_id, None)
            await tg_send(chat_id, '🔕 <b>Đã tắt nhận dự đoán.</b>')
        else:
            await tg_send(chat_id, 'Bạn chưa kích hoạt key nào.')


    # ── /autobet — đăng nhập + chọn chế độ auto-cược ─────────────────────────
    if cmd == '/autobet':
        ku  = key_users.get(chat_id)
        now = _now_ts()
        if not ku or now > ku.get('key_exp', 0):
            await tg_send(chat_id,
                '🔒 Bạn cần có key hợp lệ để dùng auto-cược.\n'
                'Dùng <code>/key KEY-XXXX-XXXX</code> trước.')
            return
        # Nếu đang có session auto-cược chạy → chặn, báo trạng thái
        if chat_id in _auto_bet_sessions and _auto_bet_sessions[chat_id].active:
            sess = _auto_bet_sessions[chat_id]
            n    = sess.ledger.net()
            sign = "+" if n >= 0 else ""
            icon = "📈" if n >= 0 else "📉"
            await tg_send(chat_id,
                f'⚠️ <b>Auto-cược đang chạy!</b>\n'
                f'━━━━━━━━━━━━━━\n'
                f'{icon} Tài khoản: <b>{sess.ledger.nick}</b>\n'
                f'💰 Số dư: <b>{sess.ledger.balance:,}</b> CHS\n'
                f'🎲 Cược/ván: <b>{sess.current_bet:,}</b>\n'
                f'📊 Ván đã chơi: <b>{sess.ledger.rounds}</b> '
                f'(✅ {sess.ledger.w} | ❌ {sess.ledger.l})\n'
                f'{sign}Lãi/Lỗ: <b>{sign}{n:,}</b>\n'
                f'━━━━━━━━━━━━━━\n'
                f'Dùng /stopbet để dừng và xem tổng kết.\n'
                f'Dùng /betstatus để xem chi tiết.')
            return
        # Nếu đang ở giữa flow setup (chưa login xong) → reset + bắt đầu lại
        if chat_id in _auto_bet_pending:
            _auto_bet_pending.pop(chat_id, None)
        # Bắt đầu flow đăng nhập — lưu state vào pending
        _auto_bet_pending[chat_id] = {'step': 'await_username'}
        await tg_send(chat_id,
            '🤖 <b>AUTO CƯỢC — LC79</b>\n'
            '━━━━━━━━━━━━━━\n'
            'Nhập <b>tên đăng nhập</b> tài khoản LC79:')
        return

    # ── /stopbet — dừng auto-cược ─────────────────────────────────────────────
    if cmd == '/stopbet':
        sess = _auto_bet_sessions.pop(chat_id, None)
        _auto_bet_pending.pop(chat_id, None)
        if sess:
            sess.active = False
            await tg_send(chat_id, sess.ledger.summary_text() + '\n\n🔕 Auto-cược đã dừng.')
        else:
            await tg_send(chat_id, '⚠️ Bạn không có phiên auto-cược nào đang chạy.')
        return

    # ── /betstatus — xem trạng thái auto-cược hiện tại ───────────────────────
    if cmd == '/betstatus':
        sess = _auto_bet_sessions.get(chat_id)
        if sess and sess.active:
            pause_line = ''
            if sess.paused:
                _need = sess.win_streak_cont - sess.recovery_wins
                pause_line = f'\n⏸ <b>ĐANG PAUSE</b> — cần thắng thêm <b>{_need}</b> ván để cược lại'
            await tg_send(chat_id, sess.status_line() + pause_line)
        else:
            await tg_send(chat_id, '⚠️ Không có phiên auto-cược nào đang chạy.')
        return

    # ── /history — 30 phiên gần nhất đúng/sai (cả admin + user) ──────────────
    elif cmd == '/history':
        recent = [r for r in app_state['results'][-60:] if r.get('pred_ok') is not None][-30:]
        if not recent:
            await tg_send(chat_id,
                '📋 <b>Lịch sử dự đoán</b>\n\n'
                'Chưa có dữ liệu dự đoán nào.\n'
                'Kết nối tool và chờ vài phiên.')
            return
        lines = []
        for i, r in enumerate(reversed(recent), 1):
            ok_icon = '✅' if r['pred_ok'] else '❌'
            pred    = r.get('pred_ok')
            res     = r.get('result', '?')
            sess    = r.get('sess_id', '?')
            lines.append(f"{ok_icon} #{sess} → {res}")
        wins  = sum(1 for r in recent if r['pred_ok'])
        total = len(recent)
        pct   = wins / total * 100 if total else 0
        streak_icons = ''.join('✅' if r['pred_ok'] else '❌' for r in recent[-10:])
        msg = (
            f'📋 <b>Lịch sử 30 phiên gần nhất</b>\n'
            f'━━━━━━━━━━━━━━\n'
            + '\n'.join(lines) +
            f'\n━━━━━━━━━━━━━━\n'
            f'✅ Đúng: <b>{wins}/{total}</b> ({pct:.1f}%)\n'
            f'10 ván cuối: {streak_icons}'
        )
        await tg_send(chat_id, msg)

    # ── /status — CHỈ ADMIN ────────────────────────────────────────────────────
    elif cmd == '/status':
        if chat_id != ADMIN_ID:
            await tg_send(chat_id, '❌ Lệnh này không tồn tại.')
            return
        status      = app_state['ws_status']
        hist        = len(app_state['history'])
        live        = app_state['live_count']
        win_size    = min(hist, HIST_WINDOW)
        total_subs  = len(tg_subscribers)
        active_subs = sum(1 for s in tg_subscribers.values() if s.get('notify', True))
        total_keys  = len(tg_keys)
        active_keys = sum(1 for k in tg_keys.values() if _now_ts() <= k.get('expires', 0))
        total_users = len(key_users)
        # Win rate
        res_with_pred = [r for r in app_state['results'] if r.get('pred_ok') is not None]
        wr_txt = '—'
        if res_with_pred:
            wins   = sum(1 for r in res_with_pred if r['pred_ok'])
            wr_txt = f'{wins}/{len(res_with_pred)} ({wins/len(res_with_pred)*100:.1f}%)'
        # Logic info
        active_logics   = _logic_tuner.get('active_logics', [])
        reversed_logics = _logic_tuner.get('reversed_logics', set())
        logic_hist      = _logic_tuner.get('history', {})
        bench           = _logic_tuner.get('last_bench')
        logic_lines = []
        for name in ALL_LOGICS:
            h = logic_hist.get(name, [])
            if h:
                w   = sum(h)
                wr  = w / len(h) * 100
                tag = ' ✅' if name in active_logics else ''
                rev = ' 🔄(bẻ)' if name in reversed_logics else ''
                logic_lines.append(f'  <code>{name}</code>: {w}/{len(h)} ({wr:.1f}%){tag}{rev}')
            else:
                logic_lines.append(f'  <code>{name}</code>: chưa có dữ liệu')
        active_str = ', '.join(f'<code>{l}</code>' for l in active_logics) if active_logics else '—'
        bench_txt  = f'(bench tại live #{bench["at"]})' if bench else ''
        await tg_send(chat_id,
            f'📊 <b>ADMIN — Trạng thái TX Tool</b>\n'
            f'━━━━━━━━━━━━━━\n'
            f'🔌 WS: <code>{status}</code>\n'
            f'📦 DB tổng: <b>{hist}</b> phiên lưu\n'
            f'🪟 Window: <b>{win_size}/{HIST_WINDOW}</b> phiên\n'
            f'🎮 Live phiên: <b>{live}</b>\n'
            f'🎯 Win rate: <b>{wr_txt}</b>\n'
            f'━━━━━━━━━━━━━━\n'
            f'👥 Users đã đăng ký: <b>{total_users}</b>\n'
            f'🔔 Subscribers đang nhận: <b>{active_subs}/{total_subs}</b>\n'
            f'🔑 Keys: <b>{active_keys}/{total_keys}</b> còn hạn\n'
            f'━━━━━━━━━━━━━━\n'
            f'🧠 <b>Top-3 Logic đang dùng</b> {bench_txt}\n'
            f'{active_str}\n'
            f'━━━━━━━━━━━━━━\n'
            f'📈 <b>WR từng Logic</b> (✅ = đang active | 🔄 = đang bẻ)\n'
            + '\n'.join(logic_lines)
        )

# ─── WS Game client ──────────────────────────────────────────────────────────
async def ws_client(token: str):
    app_state['ws_status'] = 'connecting'
    await broadcast('status', {'status': 'connecting', 'text': 'Đang kết nối...'})
    print(f"[WS] Kết nối {WS_URL}")

    reconnect_delay = 2
    while True:
        ping_task = None
        try:
            async with websockets.connect(
                WS_URL,
                additional_headers={'Origin': 'https://wtxmd52.tele68.com'},
                open_timeout=10,       # FIX: timeout kết nối
                ping_interval=None,
                close_timeout=5
            ) as ws:
                app_state['ws_status'] = 'connected'
                app_state['ws_conn']   = ws    # v28: expose cho autobet dùng
                reconnect_delay = 2

                async def send_ping():
                    while True:
                        await asyncio.sleep(20)
                        try:
                            await ws.send('3')
                        except Exception:
                            break

                ping_task = asyncio.create_task(send_ping())

                async for raw in ws:
                    print(f"[WS←] {raw[:150]}")

                    # Engine.IO handshake
                    if raw.startswith('0'):
                        conn_msg = f'40/txmd5,{{"token":"{token}"}}'
                        await ws.send(conn_msg)
                        print(f"[WS→] {conn_msg[:80]}")
                        await broadcast('status', {'status': 'connecting', 'text': 'Xác thực...'})
                        continue

                    # Namespace connect OK
                    if raw.startswith('40/txmd5'):
                        app_state['ws_status'] = 'connected'
                        await broadcast('status', {'status': 'connected', 'text': 'Đã kết nối'})
                        print("[WS] Xác thực thành công!")
                        continue

                    # Ping/Pong
                    if raw in ('2', '3'):
                        continue

                    # Socket.IO event
                    if raw.startswith('42/txmd5,'):
                        json_str = raw[len('42/txmd5,'):]
                        try:
                            arr = json.loads(json_str)
                            event_name = arr[0]
                            data       = arr[1]

                            if event_name == 'new-session':
                                await handle_new_session(data)
                            elif event_name == 'session-result':
                                await handle_session_result(data)
                            elif event_name == 'tick-update':
                                await handle_tick_update(data)
                        except Exception as e:
                            print(f"[WS PARSE ERR] {e}")

        except asyncio.CancelledError:
            print("[WS] Task đã bị huỷ")
            break
        except Exception as e:
            print(f"[WS ERR] {e}")
            app_state['ws_status'] = 'error'
            app_state['ws_conn']   = None   # v28: clear khi lỗi
            await broadcast('status', {'status': 'error', 'text': f'Lỗi – thử lại sau {reconnect_delay}s'})
            await asyncio.sleep(reconnect_delay)
            reconnect_delay = min(reconnect_delay * 2, 30)
        finally:
            # FIX: luôn cancel ping_task khi thoát vòng lặp
            if ping_task and not ping_task.done():
                ping_task.cancel()
                try:
                    await ping_task
                except asyncio.CancelledError:
                    pass

    app_state['ws_status'] = 'disconnected'
    await broadcast('status', {'status': 'disconnected', 'text': 'Đã ngắt kết nối'})


# ─── Handle new-session ───────────────────────────────────────────────────────
async def handle_tick_update(data):
    """
    Event: 42/txmd5,["tick-update", {id, tick, subTick, state: "BETTING"|"CLOSED"|..., ...}]
    Khi state = BETTING → gửi pending_bet nếu có.
    Chỉ gửi 1 lần/phiên (xóa pending sau khi gửi).
    """
    state = data.get('state', '')
    sid   = str(data.get('id', ''))

    if state != 'BETTING':
        return

    pending = app_state.get('pending_bet')
    if not pending or pending['sid'] != sid:
        return

    # Xóa pending trước để tránh gửi 2 lần nếu có nhiều tick BETTING
    app_state['pending_bet'] = None

    ensemble = pending['ensemble']
    _ws = app_state.get('ws_conn')

    for _ab_cid, _ab_sess in list(_auto_bet_sessions.items()):
        if not _ab_sess.active:
            _auto_bet_sessions.pop(_ab_cid, None)
            continue
        if _ab_sess.paused:
            continue
        if _ab_sess.ledger.balance < _ab_sess.current_bet:
            _ab_sess.active = False
            await tg_send(_ab_cid,
                f'⛔ <b>Không đủ số dư để cược!</b>\n'
                + _ab_sess.ledger.summary_text())
            _auto_bet_sessions.pop(_ab_cid, None)
            continue
        if _ws is None:
            await tg_send(_ab_cid,
                f'⚠️ <b>Phiên #{sid}</b> — WS mất kết nối, bỏ qua ván này.')
            continue
        _sent = await lc79_place_bet_ws(_ws, ensemble, _ab_sess.current_bet)
        if not _sent:
            await tg_send(_ab_cid,
                f'⚠️ <b>Phiên #{sid}</b> — Gửi cược thất bại (WS lỗi), bỏ qua ván này.')
            continue
        _ab_entry = _ab_sess.ledger.bet(ensemble, _ab_sess.current_bet)
        _ab_sess.pending_entry = _ab_entry
        await tg_send(_ab_cid,
            f'🎲 <b>Phiên #{sid}</b> | ✅ Đã đặt cược (BETTING)\n'
            f'━━━━━━━━━━━━━━\n'
            f'Dự đoán: <b>{ensemble}</b>\n'
            f'Cược: <b>{_ab_sess.current_bet:,}</b> | Bal: <b>{_ab_sess.ledger.balance:,}</b>')


async def handle_new_session(data):
    """
    Event: 42/txmd5,["new-session", {id: 6986062, duration: 50000, md5: "9c902be..."}]
    """
    sid  = str(data.get('id', ''))
    md5h = data.get('md5', '')
    dur  = data.get('duration', 0)

    if not sid or not md5h:
        print(f"[NEW-SESSION] Thiếu dữ liệu: {data}")
        return

    app_state['sessions'][sid] = {'id': sid, 'md5': md5h}

    # Chỉ giữ 500 session gần nhất
    if len(app_state['sessions']) > 500:
        oldest = list(app_state['sessions'].keys())[0]
        del app_state['sessions'][oldest]

    live  = app_state['live_count']

    # Đăng ký pred cho cả 3 offset vào session tuner (phải gọi trước khi dùng active offset)
    tuner_register_pred(sid, md5h)

    # Dùng offset từ session tuner (mặc định 0, tức sid gốc)
    sid_plus1 = tuner_get_active_sid(sid)
    active_offset = _session_tuner['active_offset']

    # v32: Đăng ký pred cả 9 logic vào logic tuner (để tính WR và chọn top-3)
    X_reg, Y_reg, Z_reg = _calc_XYZ(sid_plus1, md5h)
    logic_tuner_register_pred(sid, X_reg, Y_reg, Z_reg, md5h)

    # v25: WARMUP GATE — chỉ warmup LẦN ĐẦU khi bật tool (live < WARMUP_COUNT)
    # Sau khi đổi ttoan KHÔNG warmup lại — warmup_done=True sau khi đủ lần đầu
    if not app_state['warmup_done'] and live < WARMUP_COUNT:
        warmup_left = WARMUP_COUNT - live
        print(f"[WARMUP] Phiên #{sid} — còn {warmup_left} phiên trước khi bắt đầu dự đoán")
        app_state['current_pred'] = None
        await broadcast('new_session', {
            'id': sid, 'md5': md5h, 'duration': dur,
            'prediction': None,
            'warmup': True,
            'warmup_left': warmup_left,
            'warmup_total': WARMUP_COUNT,
        })
        # Gửi Telegram thông báo warmup (chỉ lần đầu và mỗi 5 phiên)
        if live == 0 or (live + 1) % 5 == 0:
            if tg_subscribers:
                await tg_broadcast(
                    f"⏳ <b>Đang tinh chỉnh...</b>\n"
                    f"━━━━━━━━━━━━━━\n"
                    f"Phiên #{sid} — còn <b>{warmup_left}</b>/{WARMUP_COUNT} phiên warm-up\n"
                    f"Tool đang học dữ liệu, chưa dự đoán."
                )
        return

    # Chạy 6 logic qua run_three_logic (dùng top-3 active) — v16
    logic_result  = run_three_logic(sid_plus1, md5h)
    ensemble, group, is_reversed, group_wr = get_ensemble_cross_comp(logic_result)

    # v20: detect chế độ bẻ để gắn flag vào pred_result
    # Các mode: 'dominant_strong' | 'dominant_weak' | 'two_be' | 'full_be' | None
    _lt_bench_now  = _logic_tuner.get('last_bench')
    _reversed_set  = set(logic_result.get('reversed_logics', []))
    _be_dominant   = False   # True nếu bất kỳ mode bẻ nào active (để compat UI cũ)
    _be_logic_name = None
    _be_logic_wr   = None
    _be_mode       = None    # mode string mới

    _n_be = len(_reversed_set)
    if _n_be == 3:
        _be_mode = 'full_be'
    elif _n_be == 2:
        _be_dominant = True
        _be_mode     = 'two_be'
        _be_logic_name = '+'.join(sorted(_reversed_set))
    elif _n_be == 1 and _lt_bench_now:
        _bn         = list(_reversed_set)[0]
        _eff_wr_map = _lt_bench_now.get('eff_wr', {})
        _bn_wr      = _eff_wr_map.get(_bn)
        _thuan_l    = [n for n in logic_result['active_logics'] if n not in _reversed_set]
        _thuan_wrs  = [_eff_wr_map.get(n) for n in _thuan_l if _eff_wr_map.get(n) is not None]
        if _bn_wr is not None and _thuan_wrs:
            if all(_bn_wr > tw for tw in _thuan_wrs):
                _be_dominant   = True
                _be_mode       = 'dominant_strong'
                _be_logic_name = _bn
                _be_logic_wr   = round(_bn_wr * 100, 1)
            else:
                _be_dominant   = True
                _be_mode       = 'dominant_weak'
                _be_logic_name = _bn
                _be_logic_wr   = round(_bn_wr * 100, 1) if _bn_wr else None

    # Lấy thông tin logic tuner
    lt_bench  = _logic_tuner['last_bench']
    lt_active = _logic_tuner['active_logics']
    lt_since  = _logic_tuner['since_tune']

    pred_result = {
        'ensemble':       ensemble,
        'active_group':   group,
        'is_reversed':    False,      # session-level flip (tuner offset)
        'group_wr':       1.0,
        'case_type':      logic_result['case_type'],
        'group':          logic_result['group'],
        'L1':             logic_result['L1'],
        'L2':             logic_result['L2'],
        'L3':             logic_result['L3'],
        'majority':       logic_result['majority'],
        'minority':       logic_result['minority'],
        'sid_calc':       sid_plus1,
        'tt1_wr':         None,
        'tt2_wr':         None,
        'tt1_fails':      0,
        'tt2_fails':      0,
        'tt1_fail_sess':  [],
        'tt1_hist_size':  0,
        'tt2_hist_size':  0,
        # Session Tuner info
        'tuner_offset':   active_offset,
        'tuner_sid':      sid_plus1,
        'tuner_bench':    _session_tuner['last_bench'],
        'tuner_since':    _session_tuner['since_tune'],
        'tuner_next_in':  SESSION_TUNE_INTERVAL - _session_tuner['since_tune'],
        'tuner_flip':     _session_tuner.get('flip_mode', False),
        'tuner_flip_since': _session_tuner.get('flip_since', 0),
        # v18: reversed newsession
        'tuner_rev_ns':        _session_tuner.get('reversed_newsession', False),
        'tuner_rev_ns_since':  _session_tuner.get('reversed_ns_since', 0),
        'tuner_rev_ns_bench':  _session_tuner.get('reversed_ns_bench', None),
        # v17: Logic Tuner info + reversed logic support
        'active_logics':    lt_active,
        'reversed_logics':  list(logic_result.get('reversed_logics', [])),
        'all_preds':        logic_result.get('all_preds', {}),      # raw pred (chưa bẻ)
        'effective_preds':  logic_result.get('effective_preds', {}),# effective pred (đã bẻ)
        'logic_bench':      lt_bench,
        'logic_since':      lt_since,
        'logic_next_in':    LOGIC_TUNE_INTERVAL - lt_since,
        # v19/v20: BẺ ĐỘC TÔN / BẺ 2-CHIỀU flag
        'be_dominant':      _be_dominant,        # True = bất kỳ mode bẻ active
        'be_dominant_logic': _be_logic_name,     # tên logic bẻ (hoặc 'LX+LY' nếu 2-bẻ)
        'be_dominant_wr':   _be_logic_wr,        # effective WR logic bẻ (%) — None nếu 2-bẻ
        'be_mode':          _be_mode,            # 'dominant_strong'|'dominant_weak'|'two_be'|'full_be'|None
    }
    app_state['current_pred'] = {'sess': sid, 'md5': md5h, 'pred': pred_result}

    _mode_labels = {
        'dominant_strong': f"🔱 BẺ ĐỘC TÔN MẠNH [{_be_logic_name} {_be_logic_wr}%]",
        'dominant_weak':   f"🔻 BẺ ĐỘC TÔN YẾU [{_be_logic_name} {_be_logic_wr}%]→THIỂU SỐ",
        'two_be':          f"⚔️  2-BẺ [{_be_logic_name}]→THIỂU SỐ",
        'full_be':         "🔁 FULL BẺ→THEO majority",
    }
    _mode_tag = f" | {_mode_labels[_be_mode]}" if _be_mode and _be_mode in _mode_labels else ""
    print(f"[PRED] Phiên #{sid} | Active={lt_active} | "
          f"L1={logic_result['L1']} L2={logic_result['L2']} L3={logic_result['L3']} | "
          f"Case={logic_result['case_type']}({group}) → THEO {ensemble}{_mode_tag}")

    await broadcast('new_session', {
        'id': sid, 'md5': md5h, 'duration': dur,
        'prediction': pred_result
    })

    # Gửi Telegram
    if tg_subscribers and ensemble:
        recent = [r for r in app_state['results'][-20:] if r.get('pred_ok') is not None][-10:]
        streak_icons = ''.join('✅' if r['pred_ok'] else '❌' for r in recent)
        streak_line  = f"10 ván gần nhất: {streak_icons}" if streak_icons else "10 ván gần nhất: —"
        emoji = '📈' if ensemble == 'TAI' else '📉'
        msg = (
            f"{emoji} <b>Phiên #{sid}</b>\n"
            f"━━━━━━━━━━━━━━\n"
            f"Dự đoán: <b>{ensemble}</b>\n"
            f"{streak_line}"
        )
        await tg_broadcast(msg)

        # ── AutoBet v30: KHÔNG gửi ngay — lưu pending, chờ tick-update BETTING ──
        if ensemble and _auto_bet_sessions:
            app_state['pending_bet'] = {'sid': sid, 'ensemble': ensemble}
            print(f"[AUTOBET] Phiên #{sid} → pending bet {ensemble}, chờ state BETTING")


# ─── Handle session-result ────────────────────────────────────────────────────
async def handle_session_result(data):
    """
    Event: 42/txmd5,["session-result", {
        dices: [6,3,2],
        resultTruyenThong: "TAI",
        md5Raw: "6986062:tevx{6-3-2}jEc03waZqC9ymT"
    }]
    FIX: parse sess_id từ md5Raw đúng cách
    """
    dices   = data.get('dices', [])
    result  = data.get('resultTruyenThong', '')
    md5_raw = data.get('md5Raw', '')

    # FIX: parse sess_id từ phần trước dấu ':'
    sess_id = ''
    if ':' in md5_raw:
        try:
            sess_id = str(int(md5_raw.split(':')[0]))
        except ValueError:
            sess_id = md5_raw.split(':')[0]
    
    if not sess_id:
        print(f"[SESSION-RESULT] Không parse được sess_id từ md5Raw='{md5_raw}'")
        return

    session      = app_state['sessions'].get(sess_id, {})
    expected_md5 = session.get('md5') or data.get('md5', '')

    verified  = verify_md5(sess_id, md5_raw, expected_md5) if expected_md5 else False
    dice_sum  = sum(dices)

    # Chuẩn hoá kết quả
    result_up = result.upper().strip()
    if result_up in ('XỈU', 'XIU', 'XỈU'):
        result_up = 'XIU'
    elif result_up in ('TÀI', 'TAI', 'TÀI'):
        result_up = 'TAI'

    # Lưu lịch sử
    complete = bool(sess_id and expected_md5 and dices and result_up in ('TAI', 'XIU'))
    if complete:
        app_state['history'].append({
            'sess': sess_id, 'md5': expected_md5, 'result': result_up
        })
        # Không giới hạn số phiên trong RAM — lưu tất cả, file sẽ lớn dần theo thời gian
        # Ensemble chỉ dùng HIST_WINDOW phiên gần nhất (via get_history_window())

        s = app_state['stats']
        s['total'] += 1
        if result_up == 'TAI':
            s['tai'] += 1
        elif result_up == 'XIU':
            s['xiu'] += 1
        else:
            s['hoa'] += 1
        await save_history_async()  # ghi file sau mỗi HISTORY_SAVE_INTERVAL phiên

        # Tăng bộ đếm phiên live
        prev_live = app_state['live_count']
        app_state['live_count'] += 1
        cur_live  = app_state['live_count']

        # Thông báo khi vừa đạt đủ WARMUP_COUNT (lần đầu tiên)
        if prev_live < WARMUP_COUNT <= cur_live and not app_state['warmup_done']:
            app_state['warmup_done'] = True   # v25: đánh dấu warmup đã xong — không warmup lại
            print(f"[WARMUP] ✅ Đã đủ {WARMUP_COUNT} phiên live — bắt đầu dự đoán! (warmup_done=True)")
            await broadcast('status', {
                'status': 'connected',
                'text':   f'✅ Đủ {WARMUP_COUNT} phiên — bắt đầu dự đoán!'
            })
            if tg_subscribers:
                active_now = _logic_tuner['active_logics']
                await tg_broadcast(
                    f"✅ <b>Warm-up hoàn thành!</b>\n"
                    f"━━━━━━━━━━━━━━\n"
                    f"Đã tích đủ <b>{WARMUP_COUNT} phiên live</b>.\n"
                    f"Logic đang dùng: <b>{' + '.join(active_now)}</b>\n"
                    f"Tool sẽ bắt đầu dự đoán từ phiên tiếp theo! 🚀"
                )

    # Kiểm tra dự đoán đúng/sai
    pred_ok  = None
    pred_val = None
    if app_state['current_pred'] and app_state['current_pred']['sess'] == sess_id:
        cp       = app_state['current_pred']['pred']
        pred_val = cp['ensemble']
        pred_ok  = (pred_val == result_up) if pred_val else None
        # v15: cross_comp no-op (removed)
        update_cross_comp(sess_id, cp.get('case_type', ''), result_up, pred_val)
        # Cập nhật correlation tracker
        update_corr_tracker(
            case_type = cp.get('case_type', ''),
            l1        = cp.get('L1'),
            l2        = cp.get('L2'),
            l3        = cp.get('L3'),
            majority  = cp.get('majority'),   # v15: is_reversed=False always
            ensemble  = pred_val,
            actual    = result_up,
        )
        # Cập nhật cross-pair tracker
        update_pair_tracker(
            case_type = cp.get('case_type', ''),
            l1        = cp.get('L1'),
            l2        = cp.get('L2'),
            l3        = cp.get('L3'),
            actual    = result_up,
        )
        # Cập nhật correlation matrix (tham khảo — không can thiệp TT1/TT2)
        update_corr_matrix(
            case_type   = cp.get('case_type', ''),
            l1          = cp.get('L1'),
            l2          = cp.get('L2'),
            l3          = cp.get('L3'),
            ensemble_ok = bool(pred_ok),
            actual      = result_up,
        )

        # Cập nhật session tuner rolling history
        tuner_update_result(sess_id, result_up)

        # v23: Cập nhật logic tuner + ttoan tracker (truyền pred_ok để tracker hoạt động)
        logic_tuner_update_result(sess_id, result_up, pred_ok=pred_ok)

        # Ghi vào adaptive history để recompute TT1/TT2
        _adaptive_history.append({
            'case': cp.get('case_type', ''),
            'ok':   bool(pred_ok),
        })
        # Giữ tối đa 200 entry để không tràn RAM
        if len(_adaptive_history) > 200:
            del _adaptive_history[:-200]

        # Recompute mỗi ADAPTIVE_WINDOW ván
        if len(_adaptive_history) % ADAPTIVE_WINDOW == 0:
            recompute_adaptive_groups()

    record = {
        'sess_id': sess_id, 'dices': dices, 'sum': dice_sum,
        'result': result_up, 'md5': expected_md5, 'verified': verified,
        'pred_ok': pred_ok, 'time': int(time.time() * 1000)
    }
    app_state['results'].append(record)
    if len(app_state['results']) > 200:
        app_state['results'] = app_state['results'][-200:]

    await broadcast('session_result', {
        **record,
        'stats': app_state['stats'],
        'history_size': len(app_state['history'])
    })
    print(f"[RES] #{sess_id} {dices}={dice_sum} → {result_up} | "
          f"verified={verified} | pred={pred_val} | ok={pred_ok}")

    # Gửi kết quả về Telegram
    if tg_subscribers and pred_ok is not None:
        dice_str  = '-'.join(map(str, dices))
        ok_str    = '✅ ĐÚNG' if pred_ok else '❌ SAI'
        res_emoji = '📈' if result_up == 'TAI' else '📉'
        # Streak 10 ván gần nhất (tính sau khi record đã append vào results)
        recent = [r for r in app_state['results'][-20:] if r.get('pred_ok') is not None][-10:]
        streak_icons = ''.join('✅' if r['pred_ok'] else '❌' for r in recent)
        streak_line  = f"10 ván gần nhất: {streak_icons}" if streak_icons else "10 ván gần nhất: —"
        msg = (
            f"{res_emoji} <b>Kết quả #{sess_id}</b>\n"
            f"━━━━━━━━━━━━━━\n"
            f"Xúc xắc: {dice_str} = <b>{dice_sum}</b>\n"
            f"Kết quả: <b>{result_up}</b>\n"
            f"Dự đoán: {pred_val} → {ok_str}\n"
            f"{streak_line}"
        )
        await tg_broadcast(msg)

    # ── AutoBet v29: resolve kết quả, pause/resume thay vì dừng hẳn ────────────
    if result_up in ('TAI', 'XIU') and _auto_bet_sessions:
        for _ab_cid, _ab_sess in list(_auto_bet_sessions.items()):
            if not _ab_sess.active:
                _auto_bet_sessions.pop(_ab_cid, None)
                continue

            # ── Đang PAUSE: không có pending_entry, chỉ track virtual result ──
            if _ab_sess.paused:
                if result_up == 'TAI':
                    # giả định tool pred đúng/sai dựa trên kết quả thật để track streak
                    pass
                # Cập nhật win/loss streak dựa trên kết quả thật so với pred hiện tại
                # Lấy pred của ván này từ app_state current_pred
                _cur = app_state.get('current_pred')
                _virt_pred = _cur['pred']['ensemble'] if _cur else None
                _virt_win  = (_virt_pred == result_up) if _virt_pred else False
                if _virt_win:
                    _ab_sess.on_win()   # tăng recovery_wins
                else:
                    _ab_sess.on_loss()  # reset recovery_wins

                # Check resume
                if _ab_sess.should_resume():
                    _ab_sess.paused        = False
                    _ab_sess.recovery_wins = 0
                    _ab_sess.loss_streak   = 0
                    _ab_sess.current_bet   = _ab_sess.base_bet  # resume về base
                    await tg_send(_ab_cid,
                        f'✅ <b>Đã thắng {_ab_sess.win_streak_cont} ván liên tiếp!</b>\n'
                        f'Auto-cược <b>tiếp tục</b> từ phiên kế.\n'
                        f'Cược: <b>{_ab_sess.current_bet:,}</b>')
                else:
                    _remain = _ab_sess.win_streak_cont - _ab_sess.recovery_wins
                    _icon   = '✅' if _virt_win else '❌'
                    await tg_send(_ab_cid,
                        f'{_icon} <b>Đang chờ phục hồi</b> | Phiên #{sess_id}\n'
                        f'Còn cần thắng thêm: <b>{_remain}</b> ván liên tiếp để cược lại.')
                continue

            # ── Đang ACTIVE: có pending_entry ───────────────────────────────
            if _ab_sess.pending_entry is None:
                continue
            _ab_entry = _ab_sess.pending_entry
            _ab_sess.pending_entry = None
            if _ab_entry.get('result') is not None:
                continue

            _ab_win  = _ab_sess.ledger.resolve(_ab_entry, result_up)
            _ab_pnl  = _ab_entry['pnl']
            _ab_sign = "+" if _ab_pnl > 0 else ""
            _ab_icon = "✅" if _ab_win else "❌"

            if _ab_win:
                _was_reduced = _ab_sess._is_reduced
                _ab_sess.on_win()
                # check profit target
                if _ab_sess.should_stop_profit():
                    _ab_sess.active = False
                    await tg_send(_ab_cid,
                        f'🎉 <b>Đạt mục tiêu lợi nhuận!</b>\n'
                        f'━━━━━━━━━━━━━━\n'
                        f'Mục tiêu: +{_ab_sess.profit_target:,}\n'
                        + _ab_sess.ledger.summary_text()
                        + '\n\n✅ Auto-cược tự dừng.')
                    _auto_bet_sessions.pop(_ab_cid, None)
                    continue
                # v31: thoát reduced mode → thông báo
                if _was_reduced and not _ab_sess._is_reduced:
                    await tg_send(_ab_cid,
                        f'✅ <b>Đã thắng — về cược gốc!</b>\n'
                        f'Cược tiếp: <b>{_ab_sess.current_bet:,}</b>')
            else:
                _ab_sess.on_loss()
                # v31: vừa vào reduced mode → thông báo
                if _ab_sess._is_reduced and _ab_sess.loss_streak == _ab_sess.loss_streak_reduce:
                    await tg_send(_ab_cid,
                        f'🔻 <b>Giảm cược!</b>\n'
                        f'━━━━━━━━━━━━━━\n'
                        f'Thua liên tiếp <b>{_ab_sess.loss_streak}</b> ván.\n'
                        f'Cược giảm xuống: <b>{_ab_sess.current_bet:,}</b>\n'
                        f'Số dư: <b>{_ab_sess.ledger.balance:,}</b>')
                    continue
                # check thua liên tiếp → PAUSE (không dừng hẳn)
                if _ab_sess.should_stop_loss():
                    _ab_sess.paused        = True
                    _ab_sess.recovery_wins = 0
                    _need = _ab_sess.win_streak_cont if _ab_sess.win_streak_cont > 0 else '?'
                    await tg_send(_ab_cid,
                        f'⏸ <b>Tạm dừng cược!</b>\n'
                        f'━━━━━━━━━━━━━━\n'
                        f'Thua liên tiếp <b>{_ab_sess.loss_streak}</b> ván.\n'
                        f'Chờ thắng <b>{_need}</b> ván liên tiếp để tự động cược lại.\n'
                        f'Số dư: <b>{_ab_sess.ledger.balance:,}</b> | '
                        f'Lãi/Lỗ: <b>{"+" if _ab_sess.ledger.net()>=0 else ""}{_ab_sess.ledger.net():,}</b>')
                    continue

            # Check balance
            if _ab_sess.ledger.balance < _ab_sess.current_bet:
                _ab_sess.active = False
                await tg_send(_ab_cid,
                    f'{_ab_icon} Kết quả #{sess_id}: {result_up}\n'
                    f'{_ab_sign}{_ab_pnl:,}\n'
                    f'⛔ Không đủ số dư — Dừng!\n'
                    + _ab_sess.ledger.summary_text())
                _auto_bet_sessions.pop(_ab_cid, None)
                continue

            # Thông báo kết quả ván bình thường
            _ab_net      = _ab_sess.ledger.net()
            _ab_net_sign = "+" if _ab_net >= 0 else ""
            _pause_hint  = f'\n⏸ Đang pause — cần thắng {_ab_sess.win_streak_cont - _ab_sess.recovery_wins} ván để cược lại' if _ab_sess.paused else f'\nCược tiếp: <b>{_ab_sess.current_bet:,}</b>'
            await tg_send(_ab_cid,
                f'{_ab_icon} <b>Kết quả #{sess_id}</b>\n'
                f'━━━━━━━━━━━━━━\n'
                f'KQ: <b>{result_up}</b> | Cược: {_ab_entry["side"]} → {_ab_icon}\n'
                f'{_ab_sign}Ván: <b>{_ab_sign}{_ab_pnl:,}</b>\n'
                f'Số dư: <b>{_ab_sess.ledger.balance:,}</b> | '
                f'{_ab_net_sign}Tổng L/L: <b>{_ab_net_sign}{_ab_net:,}</b>'
                + _pause_hint)


# ─── HTTP Handlers ────────────────────────────────────────────────────────────
async def handle_sse(request):
    resp = web.StreamResponse(headers={
        'Content-Type': 'text/event-stream',
        'Cache-Control': 'no-cache',
        'Connection':    'keep-alive',
        'Access-Control-Allow-Origin': '*',
    })
    await resp.prepare(request)
    q = asyncio.Queue()
    app_state['sse_clients'].add(q)

    # Gửi state hiện tại ngay khi connect
    init = {
        'status':       app_state['ws_status'],
        'history_size': len(app_state['history']),
        'min_hist':     MIN_HIST,
        'stats':        app_state['stats'],
        'results':      app_state['results'][-30:]
    }
    await resp.write(
        f"event: init\ndata: {json.dumps(init, ensure_ascii=False)}\n\n".encode()
    )

    try:
        # FIX: vòng lặp liên tục, keepalive không ngắt SSE
        while True:
            try:
                msg = await asyncio.wait_for(q.get(), timeout=25)
                await resp.write(msg.encode())
            except asyncio.TimeoutError:
                # Gửi keepalive nhưng KHÔNG return
                await resp.write(b": keepalive\n\n")
    except Exception:
        pass
    finally:
        app_state['sse_clients'].discard(q)
    return resp


async def handle_connect(request):
    body  = await request.json()
    token = body.get('token', '').strip()
    if not token:
        return web.json_response({'ok': False, 'error': 'Thiếu token'})

    # Cancel task WS cũ
    if app_state['ws_task'] and not app_state['ws_task'].done():
        app_state['ws_task'].cancel()
        try:
            await app_state['ws_task']
        except Exception:
            pass

    app_state['token']   = token
    app_state['ws_task'] = asyncio.create_task(ws_client(token))
    return web.json_response({'ok': True})


async def handle_disconnect(request):
    if app_state['ws_task'] and not app_state['ws_task'].done():
        app_state['ws_task'].cancel()
    app_state['ws_status'] = 'disconnected'
    await broadcast('status', {'status': 'disconnected', 'text': 'Đã ngắt kết nối'})
    return web.json_response({'ok': True})


async def handle_clear(request):
    """Xoá history trong RAM VÀ file — cẩn thận, không thể khôi phục"""
    app_state['history'] = []
    app_state['results'] = []
    app_state['stats']   = {'total': 0, 'tai': 0, 'xiu': 0, 'hoa': 0}
    await save_history_async(force=True)   # ghi file ngay lập tức
    await broadcast('clear', {})
    return web.json_response({'ok': True})


async def handle_download(request):
    """Download toàn bộ history dưới dạng JSON (tất cả phiên đã lưu)"""
    fmt = request.rel_url.query.get('fmt', 'json')
    if fmt == 'txt':
        lines = [
            f"{h['sess']} {h['md5']} | {h['result']}"
            for h in app_state['history']
        ]
        content = '\n'.join(lines)
        return web.Response(
            body=content.encode(),
            content_type='text/plain',
            headers={'Content-Disposition': 'attachment; filename="txmd5_history.txt"'}
        )
    else:
        content = json.dumps(app_state['history'], ensure_ascii=False, indent=2)
        return web.Response(
            body=content.encode(),
            content_type='application/json',
            headers={'Content-Disposition': 'attachment; filename="txmd5_history.json"'}
        )


async def handle_admin_subs(request):
    """GET /api/admin/subs — danh sách TẤT CẢ users đã nhập key (từ key_users)
    Bao gồm: đang nhận (notify=True), đã /stop (notify=False), hết hạn
    """
    now  = _now_ts()
    data = []
    for cid, info in key_users.items():
        key_exp = info.get('key_exp', 0)
        notify  = info.get('notify', True)
        active  = key_exp == 0 or now <= key_exp
        data.append({
            'chat_id':     cid,
            'name':        info.get('name', ''),
            'username':    info.get('username', ''),
            'key':         info.get('key', ''),
            'key_exp':     key_exp,
            'key_exp_str': datetime.fromtimestamp(key_exp).strftime('%d/%m/%Y') if key_exp else '—',
            'active':      active,
            'notify':      notify,
            'joined':      info.get('joined', 0),
        })
    return web.json_response({'ok': True, 'subs': data, 'total': len(data)})

async def handle_admin_keys(request):
    """GET /api/admin/keys — danh sách keys"""
    data = []
    now  = _now_ts()
    for k, v in tg_keys.items():
        # Resolve users list (support cả format cũ)
        users_list = v.get('users', [])
        if not users_list and v.get('used_by') is not None:
            users_list = [v['used_by']]
        max_users = v.get('max_users', 1)

        # Build user detail: chat_id + name từ subscribers
        users_detail = []
        for uid in users_list:
            sub = tg_subscribers.get(uid, {})
            users_detail.append({
                'chat_id':  uid,
                'name':     sub.get('name', str(uid)),
                'username': sub.get('username', ''),
            })

        data.append({
            'key':          k,
            'days':         v['days'],
            'created':      datetime.fromtimestamp(v['created']).strftime('%d/%m/%Y %H:%M'),
            'expires':      datetime.fromtimestamp(v['expires']).strftime('%d/%m/%Y %H:%M'),
            'used_by':      v.get('used_by'),  # backward compat
            'users':        users_detail,
            'used_count':   len(users_list),
            'max_users':    max_users,
            'active':       now <= v['expires'],
        })
    return web.json_response({'ok': True, 'keys': data, 'total': len(data)})

async def handle_admin_genkey(request):
    """POST /api/admin/genkey  body: {days: int, max_users: int}"""
    body      = await request.json()
    days      = min(max(int(body.get('days', 7)), 1), 365)
    max_users = min(max(int(body.get('max_users', 1)), 1), 100)
    key       = gen_key(days, max_users)
    exp       = datetime.fromtimestamp(_now_ts() + days * 86400).strftime('%d/%m/%Y')
    return web.json_response({'ok': True, 'key': key, 'days': days,
                              'max_users': max_users, 'expires': exp})

async def handle_admin_kick(request):
    """POST /api/admin/kick  body: {chat_id: int}
    Admin kick: xóa hẳn khỏi tg_subscribers VÀ key_users (thu hồi quyền truy cập)
    Đồng thời xóa chat_id khỏi key['users'] tương ứng để giải phóng slot
    """
    body   = await request.json()
    target = int(body.get('chat_id', 0))

    name = (tg_subscribers.get(target) or key_users.get(target) or {}).get('name', str(target))

    # Xóa khỏi subscribers
    tg_subscribers.pop(target, None)

    # Xóa khỏi key_users
    ku = key_users.pop(target, None)
    if ku:
        save_key_users()
        # Giải phóng slot trong key['users']
        key_str = ku.get('key', '')
        if key_str and key_str in tg_keys:
            users_list = tg_keys[key_str].get('users', [])
            if target in users_list:
                users_list.remove(target)
                tg_keys[key_str]['users'] = users_list
                save_keys()

    save_subs()
    # Không gửi thông báo cho người bị kick
    return web.json_response({'ok': True, 'msg': f'Kicked {name} — removed from key_users & key slot'})

async def handle_admin_delete_key(request):
    """POST /api/admin/deletekey  body: {key: str}
    Xóa key khỏi tg_keys, kick toàn bộ user đang dùng key đó, notify họ.
    """
    body    = await request.json()
    key_str = body.get('key', '').upper().strip()
    if not key_str or key_str not in tg_keys:
        return web.json_response({'ok': False, 'msg': 'Key không tồn tại.'}, status=404)

    k          = tg_keys.pop(key_str)
    save_keys()

    # Kick tất cả user đang dùng key này
    users_list = k.get('users', [])
    if not users_list and k.get('used_by') is not None:
        users_list = [k['used_by']]

    kicked = []
    for uid in users_list:
        tg_subscribers.pop(uid, None)
        ku = key_users.pop(uid, None)
        if ku:
            kicked.append(ku.get('name', str(uid)))
        asyncio.create_task(
            tg_send(uid, f'❌ <b>Key không hợp lệ.</b>\nKey của bạn đã hết hiệu lực. Liên hệ admin để lấy key mới: {ADMIN_USERNAME}')
        )

    if users_list:
        save_key_users()
    save_subs()

    msg = f'Đã xóa key {key_str}'
    if kicked:
        msg += f' — kicked {len(kicked)} user: {", ".join(kicked)}'
    return web.json_response({'ok': True, 'msg': msg})

async def handle_admin_ban(request):
    """POST /api/admin/ban  body: {chat_id: int, days: int}  days=0 → vĩnh viễn"""
    body   = await request.json()
    target = int(body.get('chat_id', 0))
    days   = min(int(body.get('days', 1)), 10)
    name   = tg_subscribers.pop(target, {}).get('name', str(target))
    if days == 0:
        tg_banned[target] = -1
        label = 'vĩnh viễn'
        # Không gửi thông báo cho người bị ban
    else:
        tg_banned[target] = _now_ts() + days * 86400
        exp_dt = datetime.fromtimestamp(tg_banned[target]).strftime('%d/%m/%Y %H:%M')
        label  = f'{days} ngày (đến {exp_dt})'
        # Không gửi thông báo cho người bị ban
    save_subs()
    return web.json_response({'ok': True, 'msg': f'Banned {name} — {label}'})


async def handle_admin_broadcast(request):
    """POST /api/admin/broadcast
    body: {message: str, targets: [chat_id, ...] | null}
    - targets=null  → gửi đến toàn bộ user đã /start (hành vi cũ)
    - targets=[...] → chỉ gửi đến danh sách chat_id được chọn
    """
    body    = await request.json()
    msg_txt = body.get('message', '').strip()
    targets = body.get('targets', None)   # None = all, list = selective
    if not msg_txt:
        return web.json_response({'ok': False, 'error': 'Thiếu nội dung thông báo'}, status=400)

    # Xác định danh sách gửi
    if targets is None:
        send_to = list(started_users)   # bao gồm cả admin
    else:
        send_to = [int(uid) for uid in targets]   # gửi đúng ai được tích, kể cả admin

    sent   = 0
    failed = 0
    for uid in send_to:
        try:
            async with aiohttp.ClientSession() as sess_http:
                r = await sess_http.post(
                    f'{TG_API}/sendMessage',
                    json={'chat_id': uid,
                          'text': f'📢 <b>Thông báo từ Admin</b>\n━━━━━━━━━━━━━━\n{msg_txt}',
                          'parse_mode': 'HTML'},
                    timeout=aiohttp.ClientTimeout(total=10)
                )
                rd = await r.json()
                if rd.get('ok'):
                    sent += 1
                else:
                    failed += 1
        except Exception:
            failed += 1
    return web.json_response({
        'ok': True, 'sent': sent, 'failed': failed,
        'total': len(send_to), 'all_users': len(started_users)
    })

async def handle_adaptive(request):
    """GET /api/adaptive — trả về adaptive grouping hiện tại"""
    return web.json_response({
        'ok':     True,
        'TT1':    sorted(_adaptive_groups['TT1']),
        'TT2':    sorted(_adaptive_groups['TT2']),
        'source': _adaptive_groups['source'],
        'computed_at': _adaptive_groups['computed_at'],
        'window': ADAPTIVE_WINDOW,
    })

async def handle_corr(request):
    """GET /api/corr — trả về correlation tracker data"""
    out = {}
    for case in ('3-0', 'L2L3', 'L1L2', 'L1L3'):
        c = _corr_tracker[case]
        out[case] = {
            'count': c['count'],
            'L1':    c['L1'],
            'L2':    c['L2'],
            'L3':    c['L3'],
            'majority':  c['majority'],
            'ensemble':  c['ensemble'],
        }
    out['_tt'] = _corr_tracker['_tt']
    return web.json_response({'ok': True, 'data': out})

async def handle_pairs(request):
    """GET /api/pairs — trả về cross-pair suggestion data"""
    return web.json_response({'ok': True, 'data': get_pair_suggestions()})

async def handle_matrix(request):
    """GET /api/matrix — correlation matrix: khi case X đúng/sai → L_i đúng bao nhiêu %
    Chỉ để tham khảo, không can thiệp TT1/TT2."""
    return web.json_response({'ok': True, 'data': get_corr_matrix_data()})

async def handle_session_tuner(request):
    """GET /api/session_tuner — trả về trạng thái session offset tuner hiện tại"""
    t = _session_tuner
    wr_map = {}
    for o in (-1, 0, 1):
        hist = t['history'][o]
        wr_map[str(o)] = {
            'wr':    round(sum(hist)/len(hist)*100, 1) if hist else None,
            'n':     len(hist),
            'ok':    sum(hist),
            'fail':  len(hist) - sum(hist),
        }
    return web.json_response({
        'ok':            True,
        'active_offset': t['active_offset'],
        'since_tune':    t['since_tune'],
        'next_tune_in':  max(0, SESSION_TUNE_INTERVAL - t['since_tune']),
        'tune_interval': SESSION_TUNE_INTERVAL,
        'window':        SESSION_TUNE_WINDOW,
        'wr':            wr_map,
        'last_bench':    t['last_bench'],
        # v16: flip mode
        'flip_mode':     t.get('flip_mode', False),
        'flip_since':    t.get('flip_since', 0),
        'flip_thresh_low':  FLIP_THRESHOLD_LOW * 100,
        'flip_thresh_high': FLIP_THRESHOLD_HIGH * 100,
        # v18
        'reversed_newsession': t.get('reversed_newsession', False),
        'reversed_ns_since':   t.get('reversed_ns_since', 0),
        'reversed_ns_bench':   t.get('reversed_ns_bench', None),
        'reverse_ns_threshold': REVERSE_NEWSESSION_THRESHOLD * 100,
    })

async def handle_index(request):
    return web.Response(body=HTML_PAGE.encode(), content_type='text/html')


# ─── HTML Page ────────────────────────────────────────────────────────────────
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="vi">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>TX Vote Combo #21 — Live v12</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:'Consolas','Courier New',monospace;background:#04040c;color:#e2e8f0;min-height:100vh}
.header{background:linear-gradient(135deg,#0d1117,#1a1f2e);border-bottom:1px solid #1e2535;padding:14px 24px;display:flex;align-items:center;justify-content:space-between}
.header h1{font-size:17px;font-weight:700;color:#00ffcc;letter-spacing:2px;text-transform:uppercase;text-shadow:0 0 10px rgba(0,255,204,.3)}
.status-badge{display:flex;align-items:center;gap:8px;font-size:12px;padding:5px 13px;border-radius:20px;background:#111318;border:1px solid #1e2535}
.dot{width:8px;height:8px;border-radius:50%;background:#4a5568}
.dot.connected{background:#48bb78;box-shadow:0 0 6px #48bb78;animation:pulse 1.5s infinite}
.dot.connecting{background:#ecc94b;box-shadow:0 0 6px #ecc94b;animation:pulse .8s infinite}
.dot.error{background:#fc8181;box-shadow:0 0 6px #fc8181}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.3}}
.layout{display:grid;grid-template-columns:320px 1fr;height:calc(100vh - 53px)}
.sidebar{background:#090b12;border-right:1px solid #1e2535;padding:16px;overflow-y:auto;display:flex;flex-direction:column;gap:12px}
.card{background:#0d1117;border:1px solid #1e2535;border-radius:8px;padding:14px}
.card-title{font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#63b3ed;margin-bottom:10px;font-weight:700;padding-bottom:6px;border-bottom:1px solid #1e2535}
textarea,input{width:100%;background:#04040c;border:1px solid #2d3748;border-radius:6px;padding:8px 10px;color:#a0aec0;font-size:11px;font-family:'Consolas',monospace;resize:vertical}
textarea{min-height:70px}
textarea:focus,input:focus{outline:none;border-color:#4299e1}
.btn{width:100%;margin-top:8px;padding:8px;border:none;border-radius:6px;font-size:12px;font-weight:700;cursor:pointer;font-family:inherit;transition:.2s}
.btn-connect{background:#19e3a0;color:#04040c}.btn-connect:hover{background:#0fc88a}
.btn-disconnect{background:#fc8181;color:#04040c}.btn-disconnect:hover{background:#f56565}
.btn-dl{background:#4299e1;color:#fff}.btn-dl:hover{background:#3182ce}
.btn-clear{background:#2d3748;color:#a0aec0}.btn-clear:hover{background:#4a5568}
.stats-grid{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}
.stat-item{text-align:center;background:#04040c;border-radius:6px;padding:8px 4px;border:1px solid #1e2535}
.stat-value{font-size:20px;font-weight:900;color:#63b3ed}
.stat-value.tai{color:#fc8181}.stat-value.xiu{color:#63b3ed}.stat-value.hoa{color:#ecc94b}
.stat-label{font-size:9px;color:#4a5568;letter-spacing:1px;text-transform:uppercase;margin-top:2px}
.pred-box{background:#04040c;border-radius:8px;padding:14px;border:1px solid #1e2535;text-align:center}
.pred-big{font-size:52px;font-weight:900;letter-spacing:4px;margin:6px 0}
.pred-tai{color:#19e3a0;text-shadow:0 0 24px rgba(25,227,160,.5)}
.pred-xiu{color:#ffb020;text-shadow:0 0 24px rgba(255,176,32,.5)}
.pred-wait{color:#2d3748}
.pred-conf{font-size:11px;color:#4a5568;margin-bottom:6px}
.conf-bar-wrap{background:#111;border-radius:10px;height:6px;overflow:hidden;margin:4px 0}
.conf-bar{height:6px;border-radius:10px;transition:.5s;background:#2d3748}
.model-row{display:flex;justify-content:space-between;align-items:center;padding:4px 0;border-bottom:1px solid #0a0c14;font-size:11px}
.model-name{color:#718096;flex:1}
.model-wr{color:#4a5568;font-size:10px;width:38px;text-align:right;margin-right:8px}
.mp-tai{background:rgba(25,227,160,.12);color:#19e3a0;border:1px solid #19e3a040;padding:1px 8px;border-radius:3px;font-size:10px;font-weight:700}
.mp-xiu{background:rgba(255,176,32,.12);color:#ffb020;border:1px solid #ffb02040;padding:1px 8px;border-radius:3px;font-size:10px;font-weight:700}
.mp-wait{color:#2d3748;font-size:10px}
.main{display:flex;flex-direction:column;overflow:hidden}
.table-header{background:#0d1117;border-bottom:1px solid #1e2535;padding:10px 18px;display:flex;align-items:center;justify-content:space-between;font-size:11px;color:#4a5568;flex-shrink:0}
.table-wrap{flex:1;overflow-y:auto;padding:0 18px 16px}
table{width:100%;border-collapse:collapse;font-size:12px;margin-top:10px}
thead th{background:#0d1117;padding:9px 10px;text-align:left;font-size:9px;text-transform:uppercase;letter-spacing:1.5px;color:#3a4868;border-bottom:1px solid #1e2535;position:sticky;top:0;z-index:1}
tbody tr{border-bottom:1px solid #090b12;transition:background .15s}
tbody tr:hover{background:#0d1117}
tbody td{padding:8px 10px;color:#a0aec0;vertical-align:middle}
.tag{display:inline-block;padding:2px 9px;border-radius:3px;font-weight:700;font-size:11px;letter-spacing:.5px}
.tag-tai{background:rgba(252,129,129,.12);color:#fc8181;border:1px solid rgba(252,129,129,.25)}
.tag-xiu{background:rgba(99,179,237,.12);color:#63b3ed;border:1px solid rgba(99,179,237,.25)}
.tag-hoa{background:rgba(236,201,75,.12);color:#ecc94b;border:1px solid rgba(236,201,75,.25)}
.tag-pred-tai{background:rgba(25,227,160,.1);color:#19e3a0;border:1px solid rgba(25,227,160,.2)}
.tag-pred-xiu{background:rgba(255,176,32,.1);color:#ffb020;border:1px solid rgba(255,176,32,.2)}
.ok{color:#48bb78;font-size:14px}.fail{color:#fc8181;font-size:14px}.wait{color:#2d3748}
.dice-row{display:flex;gap:3px;align-items:center}
.die{width:20px;height:20px;background:#161b27;border:1px solid #2d3748;border-radius:3px;display:flex;align-items:center;justify-content:center;font-size:12px;font-weight:700}
.dice-sum{font-size:11px;color:#4a5568;margin-left:4px}
.log-panel{background:#060810;border-top:1px solid #1e2535;height:100px;overflow-y:auto;padding:8px 14px;font-size:10px;flex-shrink:0}
.log-line{padding:1px 0;border-bottom:1px solid #090b12;color:#3a4868}
.log-info{color:#4299e1}.log-success{color:#48bb78}.log-warn{color:#ecc94b}.log-error{color:#fc8181}
.empty{text-align:center;padding:50px 20px;color:#1e2535;font-size:14px}
.corr-table{width:100%;border-collapse:collapse;font-size:10px;margin-top:6px}
.corr-table th{color:#4a5568;padding:3px 6px;text-align:center;border-bottom:1px solid #1e2535;letter-spacing:.5px;text-transform:uppercase}
.corr-table td{padding:3px 6px;text-align:center;border-bottom:1px solid #090b12}
.corr-case{color:#b070ff;font-weight:700;text-align:left!important}
.wr-hi{color:#19e3a0;font-weight:700}.wr-mid{color:#ecc94b;font-weight:700}.wr-lo{color:#fc8181;font-weight:700}.wr-na{color:#2d3748}
.hist-info{text-align:center;font-size:10px;color:#2d3748;margin-top:4px}
.pair-table{width:100%;border-collapse:collapse;font-size:10px;margin-top:6px}
.pair-table th{color:#4a5568;padding:3px 5px;text-align:center;border-bottom:1px solid #1e2535;letter-spacing:.5px;text-transform:uppercase;font-size:9px}
.pair-table td{padding:3px 5px;text-align:center;border-bottom:1px solid #090b12}
.pair-case{color:#ecc94b;font-weight:700;text-align:left!important;font-size:10px}
.pair-best{background:rgba(25,227,160,.08);border-left:2px solid #19e3a0}
.suggestion-box{background:#04040c;border:1px solid #1e2535;border-radius:6px;padding:8px;margin-top:8px;font-size:10px}
.sug-row{display:flex;justify-content:space-between;align-items:center;padding:3px 0;border-bottom:1px solid #090b12}
.sug-case{color:#b070ff;font-weight:700;width:50px}
.sug-pair{color:#19e3a0;font-weight:700;width:40px}
.sug-wr{color:#ecc94b;width:38px;text-align:right}
.sug-bar{flex:1;margin:0 8px;height:4px;background:#1e2535;border-radius:2px;overflow:hidden}
.sug-bar-fill{height:100%;border-radius:2px;background:#19e3a0;transition:.4s}
.matrix-wrap{overflow-x:auto;margin-top:6px}
.matrix-table{width:100%;border-collapse:collapse;font-size:10px}
.matrix-table th{color:#4a5568;padding:4px 6px;text-align:center;border-bottom:1px solid #1e2535;font-size:9px;text-transform:uppercase;letter-spacing:.5px;white-space:nowrap}
.matrix-table td{padding:4px 6px;text-align:center;border-bottom:1px solid #090b12;vertical-align:middle}
.matrix-case{color:#ecc94b;font-weight:700;text-align:left!important;white-space:nowrap;font-size:10px}
.co-hi{color:#19e3a0;font-weight:700}
.co-mid{color:#ecc94b;font-weight:700}
.co-lo{color:#fc8181}
.co-na{color:#2d3748}
.badge-logic{display:inline-block;padding:1px 6px;border-radius:3px;font-size:9px;font-weight:700}
.badge-best{background:rgba(25,227,160,.15);color:#19e3a0;border:1px solid #19e3a040}
.badge-inv{background:rgba(255,176,32,.12);color:#ffb020;border:1px solid #ffb02040}
.matrix-note{font-size:9px;color:#4a5568;margin-top:6px;line-height:1.5}
.suggest-natural{background:#04040c;border:1px solid #19e3a030;border-radius:6px;padding:8px;margin-top:8px}
/* Session Tuner */
.tuner-badge{display:inline-flex;align-items:center;gap:6px;background:#04040c;border:1px solid #b070ff40;border-radius:6px;padding:6px 12px;margin-bottom:8px;width:100%}
.tuner-offset-val{font-size:22px;font-weight:900;color:#b070ff;letter-spacing:2px}
.tuner-sid-val{font-size:11px;color:#718096}
.tuner-offset-label{font-size:9px;color:#4a5568;text-transform:uppercase;letter-spacing:1px}
.tuner-bar-wrap{display:flex;gap:6px;margin:8px 0}
.tuner-bar-item{flex:1;text-align:center}
.tuner-bar-label{font-size:9px;color:#4a5568;margin-bottom:3px;text-transform:uppercase;letter-spacing:.8px}
.tuner-bar-track{background:#111;border-radius:4px;height:36px;position:relative;overflow:hidden}
.tuner-bar-fill{position:absolute;bottom:0;left:0;right:0;border-radius:4px;transition:.5s}
.tuner-bar-pct{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;font-size:11px;font-weight:700}
.tuner-active-ring{box-shadow:0 0 0 2px #b070ff,0 0 8px #b070ff60}
.tuner-next{font-size:10px;color:#4a5568;text-align:center;margin-top:4px}
.tuner-bench{background:#04040c;border:1px solid #1e2535;border-radius:6px;padding:6px 10px;margin-top:8px;font-size:10px}
.sn-row{display:flex;align-items:center;gap:6px;padding:3px 0;border-bottom:1px solid #090b12;font-size:10px}
.sn-case{color:#b070ff;font-weight:700;width:42px;flex-shrink:0}
.sn-arrow{color:#2d3748}
.sn-logic{color:#19e3a0;font-weight:700}
.sn-pct{color:#ecc94b;margin-left:auto;font-size:9px}
::-webkit-scrollbar{width:4px;height:4px}
::-webkit-scrollbar-track{background:#04040c}
::-webkit-scrollbar-thumb{background:#1e2535;border-radius:2px}
</style>
</head>
<body>
<div class="header">
  <h1>⚡ TX VOTE COMBO <span style="color:#ff3d7a">#21</span></h1>
  <div class="status-badge">
    <div class="dot" id="dot"></div>
    <span id="statusTxt">Chưa kết nối</span>
  </div>
</div>

<div class="layout">
  <div class="sidebar">
    <div class="card">
      <div class="card-title">🔑 Token JWT</div>
      <textarea id="tokenInput" placeholder="Dán token JWT vào đây..."></textarea>
      <button class="btn btn-connect" id="btnConnect" onclick="doConnect()">▶ Kết nối</button>
      <button class="btn btn-disconnect" id="btnDisconnect" onclick="doDisconnect()" style="display:none">■ Ngắt kết nối</button>
    </div>

    <div class="card">
      <div class="card-title">🎯 Dự Đoán Phiên Hiện Tại</div>
      <div class="pred-box">
        <div style="font-size:10px;color:#4a5568;margin-bottom:2px" id="predSessLabel">—</div>
        <div class="pred-big pred-wait" id="predBig">—</div>
        <div class="pred-conf" id="predConf">Chờ phiên mới...</div>
      </div>
    </div>

    <div class="card" style="border-color:#00f0d840">
      <div class="card-title" style="display:flex;justify-content:space-between;align-items:center">
        <span>🗳️ Logic Chi Tiết (6 Logic)</span>
        <span id="activeBadge" style="font-size:9px;background:#00f0d820;color:#00f0d8;border:1px solid #00f0d840;border-radius:4px;padding:2px 7px;letter-spacing:.5px">TOP-3: L1·L2·L3</span>
      </div>
      <div id="modelRows" style="display:grid;grid-template-columns:1fr 1fr;gap:5px;margin-bottom:8px">
        <!-- L1 -->
        <div class="model-row logic-row" id="lrow1" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname1" style="font-size:11px;font-weight:700">L1</span>
            <span class="mp-wait" id="lr1">—</span>
          </div>
          <span id="lwr1" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <!-- L2 -->
        <div class="model-row logic-row" id="lrow2" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname2" style="font-size:11px;font-weight:700">L2</span>
            <span class="mp-wait" id="lr2">—</span>
          </div>
          <span id="lwr2" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <!-- L3 -->
        <div class="model-row logic-row" id="lrow3" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname3" style="font-size:11px;font-weight:700">L3</span>
            <span class="mp-wait" id="lr3">—</span>
          </div>
          <span id="lwr3" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <!-- L4 -->
        <div class="model-row logic-row" id="lrow4" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname4" style="font-size:11px;font-weight:700">L4</span>
            <span class="mp-wait" id="lr4">—</span>
          </div>
          <span id="lwr4" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <!-- L5 -->
        <div class="model-row logic-row" id="lrow5" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname5" style="font-size:11px;font-weight:700">L5</span>
            <span class="mp-wait" id="lr5">—</span>
          </div>
          <span id="lwr5" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <!-- L6 -->
        <div class="model-row logic-row" id="lrow6" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname6" style="font-size:11px;font-weight:700">L6</span>
            <span class="mp-wait" id="lr6">—</span>
          </div>
          <span id="lwr6" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <div class="model-row logic-row" id="lrow7" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname7" style="font-size:11px;font-weight:700">L7</span>
            <span class="mp-wait" id="lr7">—</span>
          </div>
          <span id="lwr7" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <div class="model-row logic-row" id="lrow8" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname8" style="font-size:11px;font-weight:700">L8</span>
            <span class="mp-wait" id="lr8">—</span>
          </div>
          <span id="lwr8" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
        <div class="model-row logic-row" id="lrow9" style="flex-direction:column;align-items:flex-start;padding:6px 8px;border-radius:6px;border:1px solid #1e2535;background:#0d1117">
          <div style="display:flex;width:100%;justify-content:space-between;align-items:center">
            <span class="model-name" id="lname9" style="font-size:11px;font-weight:700">L9</span>
            <span class="mp-wait" id="lr9">—</span>
          </div>
          <span id="lwr9" style="font-size:9px;color:#4a5568;margin-top:2px">WR: —</span>
        </div>
      </div>
      <!-- Logic tune countdown -->
      <div id="logicTuneBar" style="margin-top:2px;display:none">
        <div style="display:flex;justify-content:space-between;font-size:9px;color:#4a5568;margin-bottom:2px">
          <span>Tune tiếp theo</span><span id="logicTuneNext">—</span>
        </div>
        <div style="background:#111;border-radius:4px;height:3px;overflow:hidden">
          <div id="logicTunePBar" style="height:100%;background:#00f0d8;border-radius:4px;transition:.4s;width:0%"></div>
        </div>
      </div>
      <div style="margin-top:8px;font-size:10px;color:#5b6886;border-top:1px solid #1e2535;padding-top:6px" id="caseInfo">Case: — · Group: — · Active: —</div>
    </div>

    <div class="card">
      <div class="card-title">📈 Thống Kê</div>
      <div class="stats-grid">
        <div class="stat-item"><div class="stat-value" id="sTotal">0</div><div class="stat-label">Tổng</div></div>
        <div class="stat-item"><div class="stat-value tai" id="sTai">0</div><div class="stat-label">TÀI</div></div>
        <div class="stat-item"><div class="stat-value xiu" id="sXiu">0</div><div class="stat-label">XỈU</div></div>
        <div class="stat-item"><div class="stat-value hoa" id="sHoa">0</div><div class="stat-label">HÒA</div></div>
      </div>
      <div style="margin-top:8px;font-size:11px;color:#4a5568;text-align:center" id="wrLive">Win Rate: —</div>
    </div>

    <div class="card">
      <div class="card-title">💾 Dữ Liệu</div>
      <button class="btn btn-dl" onclick="doDownload()">⬇ Tải TXT</button>
      <button class="btn btn-clear" onclick="doClear()">🗑 Xóa lịch sử</button>
    </div>

    <!-- Session Offset Tuner Card -->
    <div class="card" style="border-color:#b070ff40">
      <div class="card-title" style="display:flex;justify-content:space-between;align-items:center;color:#b070ff">
        <span>🎛️ Session Offset Tuner</span>
        <button onclick="loadTuner()" style="background:#1e2535;color:#b070ff;border:1px solid #2d3748;border-radius:4px;padding:2px 8px;cursor:pointer;font-size:10px">↺</button>
      </div>
      <div style="font-size:9px;color:#4a5568;margin-bottom:8px">
        Tự so sánh WR của offset -1 / 0 / +1 mỗi 10 phiên → tự chọn offset tốt nhất
      </div>

      <!-- Active offset + sid hiện tại -->
      <div class="tuner-badge">
        <div>
          <div class="tuner-offset-label">Offset đang dùng</div>
          <div class="tuner-offset-val" id="tunerOffsetVal">0</div>
        </div>
        <div style="flex:1;text-align:right">
          <div class="tuner-offset-label">Mã phiên tính</div>
          <div class="tuner-sid-val" id="tunerSidVal">—</div>
        </div>
      </div>

      <!-- 3 bars: offset -1 / 0 / +1 -->
      <div class="tuner-bar-wrap" id="tunerBars">
        <div class="tuner-bar-item" id="tunerBarM1">
          <div class="tuner-bar-label">-1</div>
          <div class="tuner-bar-track">
            <div class="tuner-bar-fill" id="tunerFillM1" style="background:#4a5568;height:0%"></div>
            <div class="tuner-bar-pct" id="tunerPctM1" style="color:#4a5568">—</div>
          </div>
        </div>
        <div class="tuner-bar-item" id="tunerBar0">
          <div class="tuner-bar-label">0 (def)</div>
          <div class="tuner-bar-track">
            <div class="tuner-bar-fill" id="tunerFill0" style="background:#4a5568;height:0%"></div>
            <div class="tuner-bar-pct" id="tunerPct0" style="color:#4a5568">—</div>
          </div>
        </div>
        <div class="tuner-bar-item" id="tunerBarP1">
          <div class="tuner-bar-label">+1</div>
          <div class="tuner-bar-track">
            <div class="tuner-bar-fill" id="tunerFillP1" style="background:#4a5568;height:0%"></div>
            <div class="tuner-bar-pct" id="tunerPctP1" style="color:#4a5568">—</div>
          </div>
        </div>
      </div>

      <!-- Tiến trình đến lần tune tiếp theo -->
      <div class="tuner-next" id="tunerNext">Tune tiếp theo sau — phiên</div>
      <div style="background:#111;border-radius:4px;height:4px;overflow:hidden;margin:4px 0">
        <div id="tunerProgressBar" style="height:100%;background:#b070ff;border-radius:4px;transition:.4s;width:0%"></div>
      </div>

      <!-- Kết quả lần benchmark gần nhất -->
      <div class="tuner-bench" id="tunerBench" style="display:none">
        <div style="font-size:9px;color:#4a5568;margin-bottom:4px;text-transform:uppercase;letter-spacing:.8px">📊 Benchmark gần nhất</div>
        <div id="tunerBenchContent" style="color:#a0aec0"></div>
      </div>
      <!-- v18: Reversed Newsession status -->
      <div id="revNsStatus" style="margin-top:8px;font-size:10px;border-radius:5px;padding:6px 8px;border:1px solid #1e2535;background:#04040c;color:#718096">
        <b>⚡ Auto Reversed NS</b>: <span id="revNsVal">Chờ dữ liệu...</span>
      </div>
      <!-- v18: Reversed NS bench detail -->
      <div class="tuner-bench" id="revNsBench" style="display:none;margin-top:6px">
        <div style="font-size:9px;color:#4a5568;margin-bottom:4px;text-transform:uppercase;letter-spacing:.8px">⚡ Reversed NS — Benchmark</div>
        <div id="revNsBenchContent" style="color:#a0aec0"></div>
      </div>
    </div>

    <div class="card">
      <div class="card-title" style="display:flex;justify-content:space-between;align-items:center">
        <span>🔗 Correlation Tracker</span>
        <button onclick="loadCorr()" style="background:#1e2535;color:#63b3ed;border:1px solid #2d3748;border-radius:4px;padding:2px 8px;cursor:pointer;font-size:10px">↺</button>
      </div>
      <div style="font-size:9px;color:#4a5568;margin-bottom:6px">Khi case X xảy ra → L1/L2/L3/majority/ensemble đúng bao nhiêu %</div>
      <table class="corr-table" id="corrTable">
        <thead>
          <tr>
            <th style="text-align:left">Case</th>
            <th>n</th>
            <th>L1</th>
            <th>L2</th>
            <th>L3</th>
            <th>Đa số</th>
            <th>Ensemble</th>
          </tr>
        </thead>
        <tbody id="corrBody">
          <tr><td colspan="7" class="wr-na" style="padding:8px;text-align:center">Chờ dữ liệu...</td></tr>
        </tbody>
      </table>
      <div style="margin-top:8px;border-top:1px solid #1e2535;padding-top:6px">
        <div style="font-size:9px;color:#4a5568;margin-bottom:4px">TT Group Win Rate (ensemble sau bẻ cầu)</div>
        <div id="ttStats" style="font-size:11px;color:#a0aec0">—</div>
      </div>
      <div style="margin-top:8px;border-top:1px solid #1e2535;padding-top:6px">
        <div style="font-size:9px;color:#4a5568;margin-bottom:4px">Phân nhóm hiện tại <span id="adaptiveSrc" style="color:#718096"></span></div>
        <div id="adaptiveGroups" style="font-size:11px;color:#a0aec0">—</div>
      </div>
    </div>

    <!-- Card: Quan sát cặp logic theo case -->
    <div class="card">
      <div class="card-title" style="display:flex;justify-content:space-between;align-items:center">
        <span>🔍 Quan Sát Cặp Logic</span>
        <button onclick="loadPairs()" style="background:#1e2535;color:#63b3ed;border:1px solid #2d3748;border-radius:4px;padding:2px 8px;cursor:pointer;font-size:10px">↺</button>
      </div>
      <div style="font-size:9px;color:#4a5568;margin-bottom:6px">
        Khi case X xảy ra → cặp L1L2 / L2L3 / L1L3 đồng thuận đúng/sai bao nhiêu %
      </div>
      <table class="pair-table" id="pairTable">
        <thead>
          <tr>
            <th style="text-align:left">Case</th>
            <th>Cặp</th>
            <th>Đồng✓</th>
            <th>Đồng✗</th>
            <th>Khác</th>
            <th>WR%</th>
          </tr>
        </thead>
        <tbody id="pairBody">
          <tr><td colspan="6" class="wr-na" style="padding:8px;text-align:center">Chờ dữ liệu...</td></tr>
        </tbody>
      </table>
    </div>

    <!-- Card: Gợi ý cặp tốt nhất theo lịch sử -->
    <div class="card">
      <div class="card-title">💡 Gợi Ý Cặp Theo Case</div>
      <div style="font-size:9px;color:#4a5568;margin-bottom:6px">
        Dựa lịch sử tích lũy — khi case X → nên theo cặp nào đồng thuận nhất?
      </div>
      <div id="suggestionBox">
        <div style="color:#2d3748;font-size:10px;text-align:center;padding:8px">Chờ dữ liệu...</div>
      </div>
    </div>

    <!-- Card: Correlation Matrix — chỉ tham khảo -->
    <div class="card" style="border-color:#19e3a020">
      <div class="card-title" style="display:flex;justify-content:space-between;align-items:center;color:#19e3a0">
        <span>📐 Correlation Matrix <span style="color:#4a5568;font-size:8px;font-weight:400;text-transform:none;letter-spacing:0">(tham khảo — không can thiệp TT)</span></span>
        <button onclick="loadMatrix()" style="background:#1e2535;color:#19e3a0;border:1px solid #2d3748;border-radius:4px;padding:2px 8px;cursor:pointer;font-size:10px">↺</button>
      </div>
      <div style="font-size:9px;color:#4a5568;margin-bottom:4px;line-height:1.5">
        Khi case X <b style="color:#19e3a0">đúng</b> → logic L_i cũng đúng bao nhiêu %?
        Giá trị cao = L_i <b>đồng pha</b> với case → gợi ý ghép cặp tự nhiên sau này.
      </div>
      <div class="matrix-wrap">
        <table class="matrix-table" id="matrixTable">
          <thead>
            <tr>
              <th style="text-align:left">Case</th>
              <th>n✓</th>
              <th>n✗</th>
              <th>L1<br><span style="color:#2d3748;font-size:8px">đồng%</span></th>
              <th>L2<br><span style="color:#2d3748;font-size:8px">đồng%</span></th>
              <th>L3<br><span style="color:#2d3748;font-size:8px">đồng%</span></th>
              <th>Best</th>
            </tr>
          </thead>
          <tbody id="matrixBody">
            <tr><td colspan="7" class="co-na" style="padding:8px;text-align:center">Chờ dữ liệu...</td></tr>
          </tbody>
        </table>
      </div>
      <div class="matrix-note">
        <b style="color:#19e3a0">Đồng%</b> = khi case đúng → L_i cũng đúng · 
        <b style="color:#ffb020">Ngược%</b> = khi case sai → L_i lại đúng (signal bẻ)
      </div>
      <!-- Gợi ý cặp tự nhiên từ matrix -->
      <div style="margin-top:8px;font-size:9px;color:#63b3ed;font-weight:700;text-transform:uppercase;letter-spacing:1px">
        💡 Cặp Tự Nhiên Từ Lịch Sử
      </div>
      <div class="suggest-natural" id="naturalPairs">
        <div style="color:#2d3748;font-size:10px;text-align:center">Chờ dữ liệu...</div>
      </div>
    </div>
  </div>

  <div class="main">
    <div class="table-header">
      <span>📋 Lịch sử kết quả live</span>
      <span id="recCount">0 bản ghi</span>
    </div>
    <div class="table-wrap">
      <div class="empty" id="emptyState">🔌 Kết nối để nhận dữ liệu live</div>
      <table id="resultsTable" style="display:none">
        <thead>
          <tr>
            <th>#</th><th>Session</th><th>Xúc xắc</th><th>Tổng</th>
            <th>Kết quả</th><th>Dự đoán</th><th>✓/✗</th>
          </tr>
        </thead>
        <tbody id="tableBody"></tbody>
      </table>
    </div>
    <div class="log-panel" id="logPanel"></div>
  </div>
</div>

<script>
let es = null;
let rowCount = 0;
let correct = 0, predicted = 0;
const pendingPreds = {};

// ── Token persistence ─────────────────────────────────────────────────────────
const TOKEN_KEY = 'tx_token_v1';
(function restoreToken() {
  try {
    const saved = localStorage.getItem(TOKEN_KEY);
    if (saved) {
      document.addEventListener('DOMContentLoaded', () => {
        const el = document.getElementById('tokenInput');
        if (el) el.value = saved;
      });
      // DOMContentLoaded có thể đã fire, set trực tiếp luôn
      const el = document.getElementById('tokenInput');
      if (el) el.value = saved;
    }
  } catch(e) {}
})();

function log(msg, cls='') {
  const p = document.getElementById('logPanel');
  const ts = new Date().toLocaleTimeString('vi-VN');
  const d = document.createElement('div');
  d.className = 'log-line log-' + cls;
  d.textContent = `[${ts}] ${msg}`;
  p.appendChild(d);
  p.scrollTop = p.scrollHeight;
  if (p.children.length > 300) p.removeChild(p.firstChild);
}

function setStatus(state, txt) {
  document.getElementById('dot').className = 'dot ' + state;
  document.getElementById('statusTxt').textContent = txt;
}

function doConnect() {
  const token = document.getElementById('tokenInput').value.trim();
  if (!token) { log('Cần nhập token!', 'error'); return; }
  // Lưu token persistent qua các lần đóng/mở tab
  try { localStorage.setItem(TOKEN_KEY, token); } catch(e) {}
  log('Đang kết nối...', 'info');
  fetch('/api/connect', {
    method: 'POST',
    headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({token})
  }).then(r => r.json()).then(r => {
    if (r.ok) {
      document.getElementById('btnConnect').style.display = 'none';
      document.getElementById('btnDisconnect').style.display = '';
      startSSE();
    } else log('Lỗi: ' + r.error, 'error');
  });
}

function doDisconnect() {
  fetch('/api/disconnect', {method: 'POST'}).then(() => {
    document.getElementById('btnConnect').style.display = '';
    document.getElementById('btnDisconnect').style.display = 'none';
    if (es) { es.close(); es = null; }
    // Xóa token khỏi storage khi chủ động ngắt kết nối
    try { localStorage.removeItem(TOKEN_KEY); } catch(e) {}
  });
}

function doDownload() { window.open('/api/download', '_blank'); }

function doClear() {
  if (!confirm('Xóa toàn bộ history tích lũy?')) return;
  fetch('/api/clear', {method: 'POST'}).then(() => {
    rowCount = 0; correct = 0; predicted = 0;
    document.getElementById('tableBody').innerHTML = '';
    document.getElementById('emptyState').style.display = '';
    document.getElementById('resultsTable').style.display = 'none';
    document.getElementById('recCount').textContent = '0 bản ghi';
    updateWR();
    log('Đã xóa lịch sử.', 'warn');
  });
}

function startSSE() {
  if (es) es.close();
  es = new EventSource('/api/events');

  es.addEventListener('init', e => {
    const d = JSON.parse(e.data);
    setStatus(d.status, d.status === 'connected' ? 'Đã kết nối' : 'Đang kết nối...');
    updateStats(d.stats);
    if (d.results && d.results.length > 0) d.results.forEach(r => appendRow(r, true));
    loadTuner();
  });

  es.addEventListener('status', e => {
    const d = JSON.parse(e.data);
    setStatus(d.status, d.text);
    log(d.text, d.status === 'connected' ? 'success' : 'warn');
  });

  es.addEventListener('new_session', e => {
    const d = JSON.parse(e.data);
    const pr = d.prediction;

    document.getElementById('predSessLabel').textContent = `Phiên #${d.id} (tính +1=${pr.sid_calc||'?'})`;
    const pb = document.getElementById('predBig');

    pendingPreds[d.id] = pr.ensemble;
    pb.textContent = pr.ensemble || '?';
    pb.className = 'pred-big ' + (pr.ensemble === 'TAI' ? 'pred-tai' : pr.ensemble === 'XIU' ? 'pred-xiu' : 'pred-wait');

    const revTag = pr.is_reversed ? ' [BẺ]' : '';
    document.getElementById('predConf').textContent =
      `${pr.ensemble || '?'}${revTag} · Active: ${pr.active_group || '?'}`;

    // Logic detail — v17: 6 logic, top-3 active highlighted, reversed shown with [BẺ]
    const lCls = v => v === 'TAI' ? 'mp-tai' : v === 'XIU' ? 'mp-xiu' : 'mp-wait';
    const activeLogics   = pr.active_logics   || ['L1','L2','L3'];
    const reversedLogics = new Set(pr.reversed_logics || []);
    const allPreds       = pr.all_preds       || {};   // raw (chưa bẻ)
    const effectivePreds = pr.effective_preds || allPreds; // effective (đã bẻ nếu reversed)
    const logicBench     = pr.logic_bench     || null;

    // Slot 1-3: top-3 active; Slot 4-9: inactive (v32: pool 9 logic)
    const ALL6 = ['L1','L2','L3','L4','L5','L6','L7','L8','L9'];
    const inactive3 = ALL6.filter(n => !activeLogics.includes(n));
    const displayOrder = [...activeLogics, ...inactive3];

    displayOrder.forEach((lname, idx) => {
      const slotIdx = idx + 1;
      const isActive  = idx < 3;
      const isReversed = reversedLogics.has(lname);

      // Dùng effective pred cho active, raw (hidden) cho inactive
      const val = isActive ? (effectivePreds[lname] || '—') : '—';

      const el     = document.getElementById('lr'    + slotIdx);
      const nameEl = document.getElementById('lname' + slotIdx);
      const rowEl  = document.getElementById('lrow'  + slotIdx);
      const wrEl   = document.getElementById('lwr'   + slotIdx);
      if (!el || !nameEl || !rowEl) return;

      // Tên logic + badge [BẺ] nếu đang bẻ chiều
      nameEl.textContent = isReversed ? `${lname} [BẺ]` : lname;

      // Value
      el.textContent = val;
      el.className   = lCls(val);

      // Row style
      if (isActive) {
        rowEl.style.borderColor = isReversed ? '#f6ad55' : '#00f0d8'; // cam khi bẻ, xanh khi normal
        rowEl.style.background  = isReversed ? '#f6ad5508' : '#00f0d808';
        nameEl.style.color      = isReversed ? '#f6ad55' : '#00f0d8';
      } else {
        rowEl.style.borderColor = '#1e2535';
        rowEl.style.background  = '#0d1117';
        nameEl.style.color      = '#4a5568';
        el.className = 'mp-wait';
      }

      // WR display:
      // - Nếu bẻ → hiển thị reversed WR (eff_wr) với label "BẺ-WR"
      // - Nếu normal → hiển thị WR gốc
      if (wrEl && logicBench) {
        if (isReversed && logicBench.eff_wr) {
          const wr = logicBench.eff_wr[lname];
          if (wr !== null && wr !== undefined) {
            wrEl.textContent = `BẺ-WR: ${wr.toFixed(1)}%`;
            wrEl.style.color = wr >= 60 ? '#48bb78' : wr >= 55 ? '#ecc94b' : '#fc8181';
          } else { wrEl.textContent = 'WR: —'; wrEl.style.color = '#4a5568'; }
        } else if (logicBench.wr) {
          const wr = logicBench.wr[lname];
          if (wr !== null && wr !== undefined) {
            wrEl.textContent = `WR: ${wr.toFixed(1)}%`;
            wrEl.style.color = wr >= 50 ? '#48bb78' : wr >= 45 ? '#ecc94b' : '#fc8181';
          } else { wrEl.textContent = 'WR: —'; wrEl.style.color = '#4a5568'; }
        }
      }
    });

    // Active badge — hiển thị reversed nếu có
    const badge = document.getElementById('activeBadge');
    if (badge) {
      const top3Labeled = activeLogics.map(n => reversedLogics.has(n) ? `${n}[BẺ]` : n);
      badge.textContent = 'TOP-3: ' + top3Labeled.join('·');
    }

    // v19: BẺ ĐỘC TÔN banner
    const beDom     = pr.be_dominant      || false;
    const beLogic   = pr.be_dominant_logic || '?';
    const beWr      = pr.be_dominant_wr    || 0;
    let beBanner = document.getElementById('beDomBanner');
    if (!beBanner) {
      beBanner = document.createElement('div');
      beBanner.id = 'beDomBanner';
      beBanner.style.cssText = [
        'margin:6px 0', 'padding:6px 10px', 'border-radius:6px',
        'font-size:11px', 'font-weight:700', 'letter-spacing:.6px',
        'display:none', 'text-align:center',
      ].join(';');
      // Chèn sau activeBadge
      if (badge && badge.parentNode) badge.parentNode.insertBefore(beBanner, badge.nextSibling);
    }
    if (beDom) {
      beBanner.style.display    = 'block';
      beBanner.style.background = 'rgba(246,173,85,.13)';
      beBanner.style.border     = '1px solid #f6ad55';
      beBanner.style.color      = '#f6ad55';
      beBanner.textContent      = `🔱 BẺ ĐỘC TÔN — ${beLogic} [${beWr}%] > cả 2 logic thuận`;
    } else {
      beBanner.style.display = 'none';
    }

    // Highlight từng logic: nếu BẺ ĐỘC TÔN đang bật → viền vàng đậm hơn cho be_logic
    displayOrder.forEach((lname, idx) => {
      const rowEl2 = document.getElementById('lrow' + (idx + 1));
      if (!rowEl2) return;
      if (beDom && lname === beLogic) {
        rowEl2.style.borderColor = '#f6ad55';
        rowEl2.style.boxShadow   = '0 0 6px #f6ad5566';
      } else if (!beDom) {
        rowEl2.style.boxShadow = '';
      }
    });

    // Logic tune bar
    if (pr.logic_next_in !== undefined && pr.logic_next_in !== null) {
      const logicBar = document.getElementById('logicTuneBar');
      if (logicBar) logicBar.style.display = '';
      const nxt = document.getElementById('logicTuneNext');
      const pb2 = document.getElementById('logicTunePBar');
      const interval = 10;
      const done = interval - (pr.logic_next_in || 0);
      if (nxt) nxt.textContent = `sau ${pr.logic_next_in} phiên`;
      if (pb2) pb2.style.width = Math.min(100, (done / interval) * 100).toFixed(0) + '%';
    }

    const ci = document.getElementById('caseInfo');
    // v16: cross-comp removed — always majority; v19: annotate BẺ ĐỘC TÔN khi active
    const modeNote = beDom ? ` · 🔱 BẺ ĐỘC TÔN [${beLogic}]` : ' · THEO';
    if (ci) ci.textContent = `Case: ${pr.case_type||'?'} · Group: ${pr.group||'?'} · Majority: ${pr.majority||'?'}${modeNote}`;

    log(`📌 Phiên #${d.id} | sid_calc=${pr.sid_calc} | Active=${activeLogics.join('+')} | ${pr.case_type}(${pr.group}) | ${pr.ensemble}`, 'success');
    updateTunerSid(pr);
    addPendingTableRow(d.id, d.md5);
  });

  es.addEventListener('session_result', e => {
    const d = JSON.parse(e.data);
    updateStats(d.stats);
    appendRow(d, false);
    updateWR();
    loadCorr();
    loadPairs();
    loadMatrix();
    loadAdaptive();
    loadTuner();
    log(`🎲 #${d.sess_id} [${d.dices.join('-')}] → ${d.result} | pred_ok=${d.pred_ok}`, 'success');
  });

  es.addEventListener('clear', () => {
    rowCount = 0; correct = 0; predicted = 0;
    document.getElementById('tableBody').innerHTML = '';
    updateStats({total: 0, tai: 0, xiu: 0, hoa: 0});
  });

  es.onerror = () => { log('SSE mất kết nối, thử lại...', 'warn'); };
}

function addPendingTableRow(sessId, md5) {
  document.getElementById('emptyState').style.display = 'none';
  document.getElementById('resultsTable').style.display = '';
  const tbody = document.getElementById('tableBody');
  const pred = pendingPreds[sessId] || '?';
  const predCls = pred === 'TAI' ? 'tag-pred-tai' : pred === 'XIU' ? 'tag-pred-xiu' : '';
  const tr = document.createElement('tr');
  tr.id = `row-${sessId}`;
  tr.innerHTML = `
    <td style="color:#2d3748">⏳</td>
    <td>#${sessId}</td>
    <td colspan="2" style="color:#2d3748">Đang chờ...</td>
    <td>—</td>
    <td><span class="tag ${predCls}">${pred}</span></td>
    <td class="wait">—</td>
  `;
  tbody.insertBefore(tr, tbody.firstChild);
}

function appendRow(r, prepend) {
  document.getElementById('emptyState').style.display = 'none';
  document.getElementById('resultsTable').style.display = '';

  rowCount++;
  if (r.pred_ok !== null && r.pred_ok !== undefined) {
    predicted++;
    if (r.pred_ok) correct++;
  }

  const tbody = document.getElementById('tableBody');
  const diceHtml = r.dices && r.dices.length
    ? `<div class="dice-row">${r.dices.map(d => `<div class="die">${d}</div>`).join('')}<span class="dice-sum">=${r.sum}</span></div>`
    : '—';

  const resCls  = r.result === 'TAI' ? 'tag-tai' : r.result === 'XIU' ? 'tag-xiu' : 'tag-hoa';
  const pred    = pendingPreds[r.sess_id] || '—';
  const predCls = pred === 'TAI' ? 'tag-pred-tai' : pred === 'XIU' ? 'tag-pred-xiu' : '';
  const okHtml  = r.pred_ok === true ? '<span class="ok">✓</span>' : r.pred_ok === false ? '<span class="fail">✗</span>' : '<span class="wait">—</span>';
  const md5Short = r.md5 ? r.md5.slice(0, 14) + '...' : '—';
  const ts = new Date(r.time || Date.now()).toLocaleTimeString('vi-VN');

  const newHtml = `
    <td>${rowCount}</td>
    <td>#${r.sess_id}</td>
    <td>${diceHtml}</td>
    <td style="font-weight:700">${r.sum || '—'}</td>
    <td><span class="tag ${resCls}">${r.result || '—'}</span></td>
    <td><span class="tag ${predCls}">${pred}</span></td>
    <td>${okHtml}</td>
  `;

  const existing = document.getElementById(`row-${r.sess_id}`);
  if (existing) {
    existing.innerHTML = newHtml;
  } else {
    const tr = document.createElement('tr');
    tr.id = `row-${r.sess_id}`;
    tr.innerHTML = newHtml;
    if (prepend) tbody.appendChild(tr);
    else tbody.insertBefore(tr, tbody.firstChild);
  }
  document.getElementById('recCount').textContent = `${rowCount} bản ghi`;
}

function wrClass(pct) {
  if (pct === null) return 'wr-na';
  if (pct >= 60) return 'wr-hi';
  if (pct >= 50) return 'wr-mid';
  return 'wr-lo';
}
function fmtWR(stat) {
  const tot = stat.ok + stat.fail;
  if (tot === 0) return '<span class="wr-na">—</span>';
  const pct = (stat.ok / tot * 100).toFixed(0);
  return `<span class="${wrClass(parseFloat(pct))}">${pct}%</span><span style="color:#4a5568;font-size:9px"> ${stat.ok}/${tot}</span>`;
}

async function loadCorr() {
  const r = await fetch('/api/corr');
  const d = await r.json();
  if (!d.ok) return;
  const data = d.data;
  const cases = ['3-0','L2L3','L1L2','L1L3'];
  const groups = {'3-0':'TT1','L2L3':'TT1','L1L2':'TT2','L1L3':'TT2'};
  const groupColor = {'TT1':'#00f0d8','TT2':'#b070ff'};
  const tbody = document.getElementById('corrBody');
  tbody.innerHTML = '';
  cases.forEach(c => {
    const cd = data[c];
    const gc = groupColor[groups[c]];
    const tr = document.createElement('tr');
    tr.innerHTML = `
      <td class="corr-case" style="color:${gc}">${c}<span style="color:#4a5568;font-size:9px;margin-left:3px">${groups[c]}</span></td>
      <td style="color:#718096">${cd.count}</td>
      <td>${fmtWR(cd.L1)}</td>
      <td>${fmtWR(cd.L2)}</td>
      <td>${fmtWR(cd.L3)}</td>
      <td>${fmtWR(cd.majority)}</td>
      <td>${fmtWR(cd.ensemble)}</td>
    `;
    tbody.appendChild(tr);
  });

  // TT stats
  const tt = data._tt;
  const ttEl = document.getElementById('ttStats');
  ['TT1','TT2'].forEach(g => {
    const s = tt[g];
    const tot = s.ok + s.fail;
    const pct = tot > 0 ? (s.ok/tot*100).toFixed(1) : '—';
    const cls = tot > 0 ? wrClass(parseFloat(pct)) : 'wr-na';
  });
  ttEl.innerHTML = ['TT1','TT2'].map(g => {
    const s = tt[g];
    const tot = s.ok + s.fail;
    const pct = tot > 0 ? (s.ok/tot*100).toFixed(1) : '—';
    const cls = tot > 0 ? wrClass(parseFloat(pct)) : 'wr-na';
    const color = g === 'TT1' ? '#00f0d8' : '#b070ff';
    return `<span style="color:${color};font-weight:700">${g}</span>: <span class="${cls}">${pct}%</span> <span style="color:#4a5568;font-size:10px">(${s.ok}/${tot} · ${s.count} phiên)</span>`;
  }).join('<br>');
}

// ── Session Tuner ────────────────────────────────────────────────────────────
async function loadTuner() {
  try {
    const r = await fetch('/api/session_tuner');
    const d = await r.json();
    if (!d.ok) return;
    renderTuner(d);
  } catch(e) {}
}

function renderTuner(d) {
  const active = d.active_offset;
  const offsetLabel = active === 0 ? '0 (default)' : (active > 0 ? `+${active}` : `${active}`);
  const offsetEl = document.getElementById('tunerOffsetVal');
  if (offsetEl) {
    offsetEl.textContent = active > 0 ? `+${active}` : `${active}`;
    offsetEl.style.color = active === 0 ? '#b070ff' : '#19e3a0';
  }

  // Bars
  const offsets = [-1, 0, 1];
  const idMap = { '-1': 'M1', '0': '0', '1': 'P1' };
  const wrVals = offsets.map(o => d.wr[String(o)]?.wr ?? null);
  const maxWR  = Math.max(...wrVals.filter(v => v !== null), 50);

  offsets.forEach(o => {
    const key   = idMap[String(o)];
    const info  = d.wr[String(o)];
    const wr    = info?.wr ?? null;
    const n     = info?.n  ?? 0;
    const isAct = o === active;

    const fill = document.getElementById(`tunerFill${key}`);
    const pct  = document.getElementById(`tunerPct${key}`);
    const bar  = document.getElementById(`tunerBar${key}`);

    if (!fill || !pct) return;

    const pctVal = wr !== null ? wr : 0;
    const height  = wr !== null ? Math.max(8, (pctVal / 100) * 100) : 8;
    const color   = wr === null ? '#2d3748' : pctVal >= 60 ? '#19e3a0' : pctVal >= 50 ? '#ecc94b' : '#fc8181';

    fill.style.height     = height + '%';
    fill.style.background = isAct ? color : color + '99';
    pct.textContent       = wr !== null ? `${wr.toFixed(1)}%` : '—';
    pct.style.color       = wr !== null ? color : '#2d3748';
    pct.style.fontWeight  = isAct ? '900' : '400';

    if (bar) {
      const track = bar.querySelector('.tuner-bar-track');
      if (track) {
        if (isAct) {
          track.classList.add('tuner-active-ring');
        } else {
          track.classList.remove('tuner-active-ring');
        }
      }
      // Thêm n nhỏ dưới
      let nEl = bar.querySelector('.tuner-n-label');
      if (!nEl) {
        nEl = document.createElement('div');
        nEl.className = 'tuner-n-label';
        nEl.style.cssText = 'font-size:9px;color:#4a5568;text-align:center;margin-top:2px';
        bar.appendChild(nEl);
      }
      nEl.textContent = n > 0 ? `${n} ván` : '—';
    }
  });

  // Progress bar đến tune tiếp theo
  const prog = d.tune_interval > 0
    ? Math.min(100, (d.since_tune / d.tune_interval) * 100)
    : 0;
  const progBar = document.getElementById('tunerProgressBar');
  if (progBar) progBar.style.width = prog + '%';

  const nextEl = document.getElementById('tunerNext');
  if (nextEl) {
    nextEl.textContent = d.next_tune_in > 0
      ? `Tune tiếp theo sau ${d.next_tune_in} phiên`
      : 'Tune ngay phiên này...';
  }

  // Bench gần nhất
  const bench   = d.last_bench;
  const benchEl = document.getElementById('tunerBench');
  const benchCt = document.getElementById('tunerBenchContent');
  if (bench && benchEl && benchCt) {
    benchEl.style.display = '';
    const winner = bench.winner;
    const wLabel = winner > 0 ? `+${winner}` : `${winner}`;
    const wrTxt  = Object.entries(bench.wr).sort((a,b)=>parseInt(a[0])-parseInt(b[0])).map(([o, w]) => {
      const lbl = parseInt(o) > 0 ? `+${o}` : o;
      const isW = parseInt(o) === winner;
      const col = isW ? '#19e3a0' : '#718096';
      return `<span style="color:${col};font-weight:${isW?'900':'400'}">${lbl}: ${w !== null ? w+'%' : '—'}</span>`;
    }).join('  ');
    const flipTag = bench.flip_mode ? ' · <span style="color:#fc8181;font-weight:700">🔄 FLIP ON</span>' : '';
    benchCt.innerHTML = `${wrTxt}<br><span style="color:#4a5568;font-size:9px">Winner → <span style="color:#19e3a0;font-weight:700">${wLabel}</span> ${bench.changed ? '✦ CHANGED' : '(same)'} · live#${bench.at}${flipTag}</span>`;
  }

  // v18: Reversed Newsession status block
  const revNsStatusEl  = document.getElementById('revNsStatus');
  const revNsValEl     = document.getElementById('revNsVal');
  const revNsBenchEl   = document.getElementById('revNsBench');
  const revNsBenchCtEl = document.getElementById('revNsBenchContent');
  if (revNsStatusEl && revNsValEl) {
    const revNs      = d.reversed_newsession || false;
    const revNsSince = d.reversed_ns_since   || 0;
    const bench      = d.reversed_ns_bench;
    const normWR     = bench?.normal_wr   ?? null;
    const revWR      = bench?.reversed_wr ?? null;
    const threshold  = d.reverse_ns_threshold ?? 55;

    if (revNs) {
      revNsStatusEl.style.borderColor = '#f6ad5540';
      revNsStatusEl.style.background  = '#f6ad5510';
      revNsStatusEl.style.color       = '#f6ad55';
      revNsValEl.innerHTML = '<b style="color:#f6ad55">⚡ BẬT</b> (' + revNsSince + ' phiên)'
        + (revWR !== null ? ' · Rev-WR <b>' + revWR + '%</b> > Normal <b>' + normWR + '%</b>' : '');
    } else {
      revNsStatusEl.style.borderColor = '#48bb7840';
      revNsStatusEl.style.background  = '#48bb7810';
      revNsStatusEl.style.color       = '#48bb78';
      const wrTxt = revWR !== null
        ? 'Rev-WR <b>' + revWR + '%</b> | Normal <b>' + normWR + '%</b> | Ngưỡng <b>' + threshold + '%</b>'
        : 'Chờ đủ dữ liệu (ngưỡng ' + threshold + '%)';
      revNsValEl.innerHTML = '✅ <b>THEO chiều bình thường</b> · ' + wrTxt;
    }

    if (bench && revNsBenchEl && revNsBenchCtEl) {
      revNsBenchEl.style.display = '';
      const normCls = normWR !== null ? (normWR >= 55 ? 'color:#19e3a0' : normWR >= 50 ? 'color:#ecc94b' : 'color:#fc8181') : 'color:#4a5568';
      const revCls  = revWR  !== null ? (revWR  >= 55 ? 'color:#19e3a0' : revWR  >= 50 ? 'color:#ecc94b' : 'color:#fc8181') : 'color:#4a5568';
      revNsBenchCtEl.innerHTML =
        '<span style="' + normCls + '">Normal: ' + (normWR !== null ? normWR + '%' : '—') + '</span>'
        + '  <span style="' + revCls + '">Reversed: ' + (revWR !== null ? revWR + '%' : '—') + '</span>'
        + '<br><span style="font-size:9px;color:#4a5568">live#' + bench.at + ' · ' + (bench.changed ? '✦ CHANGED' : '(same)') + '</span>';
    }
  }

  // v16: Flip mode status block
  let flipStatusEl = document.getElementById('tunerFlipStatus');
  if (!flipStatusEl) {
    flipStatusEl = document.createElement('div');
    flipStatusEl.id = 'tunerFlipStatus';
    flipStatusEl.style.cssText = 'margin-top:8px;font-size:10px;border-radius:5px;padding:6px 8px;border:1px solid transparent';
    const benchDiv = document.getElementById('tunerBench');
    if (benchDiv && benchDiv.parentElement) {
      benchDiv.parentElement.insertBefore(flipStatusEl, benchDiv);
    }
  }
  if (d.flip_mode) {
    flipStatusEl.style.display = '';
    flipStatusEl.style.background = '#fc818110';
    flipStatusEl.style.borderColor = '#fc818140';
    flipStatusEl.style.color = '#fc8181';
    flipStatusEl.innerHTML = `🔄 <b>FLIP MODE BẬT</b> (${d.flip_since} phiên)<br><span style="font-size:9px;color:#fc8181aa">Cả 3 offset WR &lt; ${d.flip_thresh_low}% → đang ĐẢO CHIỀU pred<br>Tắt khi 1 offset ≥ ${d.flip_thresh_high}%</span>`;
  } else {
    flipStatusEl.style.display = '';
    flipStatusEl.style.background = '#48bb7810';
    flipStatusEl.style.borderColor = '#48bb7840';
    flipStatusEl.style.color = '#48bb78';
    const bestWr = Math.max(...Object.values(d.wr).map(v => v?.wr ?? 0));
    flipStatusEl.innerHTML = `✅ <b>THEO chiều bình thường</b><br><span style="font-size:9px;color:#48bb78aa">Best WR = ${bestWr.toFixed(1)}% (ngưỡng flip &lt; ${d.flip_thresh_low}%)</span>`;
  }
}

// Cập nhật sid hiển thị khi có new_session
function updateTunerSid(pred) {
  const sidEl = document.getElementById('tunerSidVal');
  if (!sidEl) return;
  const offset = pred.tuner_offset ?? 0;
  const sid    = pred.tuner_sid   ?? '—';
  const offStr = offset > 0 ? `+${offset}` : `${offset}`;
  sidEl.textContent = `${sid}  (offset ${offStr})`;

  // v16: flip mode indicator
  const offsetValEl = document.getElementById('tunerOffsetVal');
  if (offsetValEl) {
    if (pred.tuner_flip) {
      offsetValEl.textContent = `${offStr} 🔄`;
      offsetValEl.style.color = '#fc8181';
      offsetValEl.title = `Flip mode BẬT — cả 3 offset WR < 45%, đang đảo chiều pred (${pred.tuner_flip_since || 0} phiên)`;
    } else {
      offsetValEl.textContent = offStr;
      offsetValEl.style.color = '';
      offsetValEl.title = '';
    }
  }

  // v18: reversed newsession badge in offset display
  const revNsBadge = document.getElementById('tunerRevNsBadge') || (() => {
    const el = document.createElement('span');
    el.id = 'tunerRevNsBadge';
    el.style.cssText = 'font-size:9px;border-radius:4px;padding:2px 7px;margin-left:4px;display:none';
    const sidEl2 = document.getElementById('tunerSidVal');
    if (sidEl2 && sidEl2.parentElement) sidEl2.parentElement.appendChild(el);
    return el;
  })();
  if (revNsBadge) {
    if (pred.tuner_rev_ns) {
      revNsBadge.textContent = '⚡ REV-NS';
      revNsBadge.style.display = 'inline-block';
      revNsBadge.style.background = '#f6ad5520';
      revNsBadge.style.color = '#f6ad55';
      revNsBadge.style.border = '1px solid #f6ad5540';
    } else {
      revNsBadge.style.display = 'none';
    }
  }

  // flip mode badge in tuner card title area
  let flipBadge = document.getElementById('tunerFlipBadge');
  if (!flipBadge) {
    // Create once
    const tunerTitle = document.querySelector('.card [style*="b070ff"] span:first-child');
    if (tunerTitle && tunerTitle.parentElement) {
      flipBadge = document.createElement('span');
      flipBadge.id = 'tunerFlipBadge';
      flipBadge.style.cssText = 'font-size:9px;border-radius:4px;padding:2px 7px;margin-left:6px;display:none';
      tunerTitle.parentElement.insertBefore(flipBadge, tunerTitle.nextSibling);
    }
  }
  if (flipBadge) {
    if (pred.tuner_flip) {
      flipBadge.textContent = '🔄 FLIP';
      flipBadge.style.display = '';
      flipBadge.style.background = '#fc818120';
      flipBadge.style.color = '#fc8181';
      flipBadge.style.border = '1px solid #fc818140';
    } else {
      flipBadge.style.display = 'none';
    }
  }
}

async function loadAdaptive() {
  const r = await fetch('/api/adaptive');
  const d = await r.json();
  if (!d.ok) return;
  const srcLabel = d.source === 'adaptive'
    ? `<span style="color:#19e3a0">🔄 Adaptive (recompute @ ${d.computed_at} ván)</span>`
    : `<span style="color:#718096">📌 Mặc định</span>`;
  document.getElementById('adaptiveSrc').innerHTML = '— ' + srcLabel;
  const tt1color = '#00f0d8';
  const tt2color = '#b070ff';
  document.getElementById('adaptiveGroups').innerHTML =
    `<span style="color:${tt1color};font-weight:700">TT1</span>: ` +
    d.TT1.map(c => `<code style="color:${tt1color}">${c}</code>`).join(' · ') +
    `&nbsp;&nbsp;<span style="color:${tt2color};font-weight:700">TT2</span>: ` +
    d.TT2.map(c => `<code style="color:${tt2color}">${c}</code>`).join(' · ');
}

async function loadMatrix() {
  const r = await fetch('/api/matrix');
  const d = await r.json();
  if (!d.ok) return;
  const data   = d.data;
  const cases  = ['3-0', 'L2L3', 'L1L2', 'L1L3'];
  const logics = ['L1', 'L2', 'L3'];
  const gcol   = {'3-0':'#00f0d8','L2L3':'#00f0d8','L1L2':'#b070ff','L1L3':'#b070ff'};

  // ── Matrix table ────────────────────────────────────────────────────────────
  const tbody = document.getElementById('matrixBody');
  tbody.innerHTML = '';

  cases.forEach(c => {
    const cd   = data[c];
    const best = cd.best_logic;
    const tr   = document.createElement('tr');

    const logicCells = logics.map(l => {
      const lg  = cd.logics[l];
      const co  = lg.co_rate;
      const inv = lg.inv_rate;
      const isBest = l === best;
      const cls = co === null ? 'co-na' : co >= 70 ? 'co-hi' : co >= 55 ? 'co-mid' : 'co-lo';
      const coTxt  = co  !== null ? co.toFixed(0)  + '%' : '—';
      const invTxt = inv !== null ? inv.toFixed(0) + '%' : '—';
      return `<td>
        <div class="${cls}" style="font-weight:${isBest?'900':'400'}">${coTxt}${isBest ? ' ★' : ''}</div>
        <div style="color:#ffb020;font-size:8px">${invTxt}↺</div>
      </td>`;
    }).join('');

    const bestBadge = best
      ? `<span class="badge-logic badge-best">${best}</span>`
      : `<span class="co-na">—</span>`;

    tr.innerHTML = `
      <td class="matrix-case" style="color:${gcol[c]}">${c}</td>
      <td style="color:#19e3a0;font-size:10px">${cd.count_ok}</td>
      <td style="color:#fc8181;font-size:10px">${cd.count_fail}</td>
      ${logicCells}
      <td>${bestBadge}</td>
    `;
    tbody.appendChild(tr);
  });

  // ── Natural pair suggestions ─────────────────────────────────────────────
  // Tìm cặp: 2 logic đều có co_rate cao với cùng 1 case → ghép thành cặp
  // Logic: với mỗi case, rank 3 logic theo co_rate → top 2 là cặp tự nhiên
  const npEl = document.getElementById('naturalPairs');
  let npHtml = '';

  cases.forEach(c => {
    const cd = data[c];
    if (cd.count_ok < 5) {
      npHtml += `<div class="sn-row"><span class="sn-case" style="color:${ {'3-0':'#00f0d8','L2L3':'#00f0d8','L1L2':'#b070ff','L1L3':'#b070ff'}[c]}">${c}</span><span class="co-na" style="font-size:9px">Chưa đủ dữ liệu (cần ≥5 phiên đúng)</span></div>`;
      return;
    }

    // Sort logics by co_rate desc
    const ranked = logics
      .map(l => ({ l, rate: cd.logics[l].co_rate }))
      .filter(x => x.rate !== null)
      .sort((a, b) => b.rate - a.rate);

    if (ranked.length < 2) {
      npHtml += `<div class="sn-row"><span class="sn-case">${c}</span><span class="co-na">—</span></div>`;
      return;
    }

    const top1 = ranked[0];
    const top2 = ranked[1];
    const pairName = [top1.l, top2.l].sort().join('+');
    const gcol2 = {'3-0':'#00f0d8','L2L3':'#00f0d8','L1L2':'#b070ff','L1L3':'#b070ff'}[c];
    const avgRate = ((top1.rate + top2.rate) / 2).toFixed(1);
    const avgCls  = parseFloat(avgRate) >= 70 ? 'co-hi' : parseFloat(avgRate) >= 55 ? 'co-mid' : 'co-lo';

    // Inverse signal: logic nào hay đúng khi case sai
    const invRanked = logics
      .map(l => ({ l, rate: cd.logics[l].inv_rate }))
      .filter(x => x.rate !== null)
      .sort((a, b) => b.rate - a.rate);
    const invTop = invRanked[0];
    const invBadge = invTop && invTop.rate >= 60
      ? `<span class="badge-logic badge-inv" style="margin-left:4px">${invTop.l} bẻ ${invTop.rate.toFixed(0)}%↺</span>`
      : '';

    npHtml += `
      <div class="sn-row">
        <span class="sn-case" style="color:${gcol2}">${c}</span>
        <span class="sn-arrow">→</span>
        <span class="sn-logic">${pairName}</span>
        ${invBadge}
        <span class="sn-pct"><span class="${avgCls}">đồng ${avgRate}%</span></span>
      </div>`;
  });

  npEl.innerHTML = npHtml || '<div style="color:#2d3748;font-size:10px;text-align:center">Chưa đủ dữ liệu</div>';
}

async function loadPairs() {
  const r = await fetch('/api/pairs');
  const d = await r.json();
  if (!d.ok) return;
  const data = d.data;
  const cases = ['3-0','L2L3','L1L2','L1L3'];
  const pairs = ['L1L2','L2L3','L1L3'];
  const groupColor = {'3-0':'#00f0d8','L2L3':'#00f0d8','L1L2':'#b070ff','L1L3':'#b070ff'};

  // ── Pair table ──────────────────────────────────────────────────────────────
  const tbody = document.getElementById('pairBody');
  tbody.innerHTML = '';
  cases.forEach(c => {
    const cd = data[c];
    const best = cd.best_pair;
    pairs.forEach((pair, pi) => {
      const p  = cd.pairs[pair];
      const wr = p.wr_agree !== null ? p.wr_agree.toFixed(0) + '%' : '—';
      const wrCls = p.wr_agree === null ? 'wr-na' : p.wr_agree >= 60 ? 'wr-hi' : p.wr_agree >= 50 ? 'wr-mid' : 'wr-lo';
      const isBest = pair === best;
      const tr = document.createElement('tr');
      if (isBest) tr.className = 'pair-best';
      tr.innerHTML = `
        <td class="pair-case" style="color:${groupColor[c]}">${pi === 0 ? c + '<span style="color:#4a5568;font-size:8px;display:block">n='+cd.count+'</span>' : ''}</td>
        <td style="color:${isBest?'#19e3a0':'#a0aec0'};font-weight:${isBest?'700':'400'}">${pair}${isBest?' ★':''}</td>
        <td style="color:#19e3a0">${p.agree_ok}</td>
        <td style="color:#fc8181">${p.agree_fail}</td>
        <td style="color:#4a5568">${p.disagree}</td>
        <td><span class="${wrCls}">${wr}</span></td>
      `;
      tbody.appendChild(tr);
    });
    // separator row
    const sep = document.createElement('tr');
    sep.innerHTML = `<td colspan="6" style="padding:0;border-bottom:1px solid #1e2535"></td>`;
    tbody.appendChild(sep);
  });

  // ── Suggestion box ──────────────────────────────────────────────────────────
  const box = document.getElementById('suggestionBox');
  let html = '';
  cases.forEach(c => {
    const cd = data[c];
    const best = cd.best_pair;
    const wr   = cd.best_wr;
    const wrTxt = wr !== null ? wr.toFixed(1) + '%' : '—';
    const wrFill = wr !== null ? Math.min(wr, 100) : 0;
    const wrCls  = wr === null ? 'wr-na' : wr >= 60 ? 'wr-hi' : wr >= 50 ? 'wr-mid' : 'wr-lo';
    const gc = {'3-0':'#00f0d8','L2L3':'#00f0d8','L1L2':'#b070ff','L1L3':'#b070ff'}[c];
    html += `
      <div class="sug-row">
        <span class="sug-case" style="color:${gc}">${c}</span>
        <span class="sug-pair">${best || '—'}</span>
        <div class="sug-bar"><div class="sug-bar-fill" style="width:${wrFill}%;background:${wr>=60?'#19e3a0':wr>=50?'#ecc94b':'#fc8181'}"></div></div>
        <span class="sug-wr"><span class="${wrCls}">${wrTxt}</span></span>
      </div>`;
  });
  box.innerHTML = html || '<div style="color:#2d3748;font-size:10px;text-align:center;padding:8px">Chưa đủ dữ liệu</div>';
}

function updateStats(s) {
  document.getElementById('sTotal').textContent = s.total;
  document.getElementById('sTai').textContent   = s.tai;
  document.getElementById('sXiu').textContent   = s.xiu;
  document.getElementById('sHoa').textContent   = s.hoa;
}

function updateWR() {
  const el = document.getElementById('wrLive');
  if (predicted > 0) {
    const pct = (correct / predicted * 100).toFixed(1);
    el.textContent = `Win Rate thực tế: ${pct}% (${correct}/${predicted})`;
    el.style.color = parseFloat(pct) >= 60 ? '#19e3a0' : '#fc8181';
  } else {
    el.textContent = 'Win Rate: —';
  }
}

// ══════════════════════════════════════════════════════
// ADMIN PANEL
// ══════════════════════════════════════════════════════
let adminTab = false;

function toggleAdmin() {
  adminTab = !adminTab;
  document.getElementById('adminPanel').style.display = adminTab ? 'block' : 'none';
  if (adminTab) { loadSubs(); loadKeys(); loadBroadcastList(); }
}

async function loadSubs() {
  const r = await fetch('/api/admin/subs');
  const d = await r.json();
  const tbody = document.getElementById('subsBody');
  tbody.innerHTML = '';
  // Đồng bộ broadcast list với dữ liệu mới nhất
  broadcastAllUsers = d.subs.map(s => ({
    chat_id: s.chat_id, name: s.name || String(s.chat_id), username: s.username || ''
  }));
  renderBroadcastList();
  const activeCount  = d.subs.filter(s => s.active && s.notify).length;
  const stoppedCount = d.subs.filter(s => s.active && !s.notify).length;
  document.getElementById('subsCount').textContent =
    `${d.total} người · 🔔${activeCount} 🔕${stoppedCount}`;
  d.subs.forEach(s => {
    const active = s.active;
    const notify = s.notify;
    const nameColor  = !active ? '#fc8181' : notify ? '#19e3a0' : '#ecc94b';
    const notifyHtml = !active
      ? '<span style="color:#fc8181;font-size:10px">Hết hạn</span>'
      : notify
        ? '<span style="color:#19e3a0;font-size:10px">🔔 Nhận</span>'
        : '<span style="color:#ecc94b;font-size:10px">🔕 Đã tắt</span>';
    const safeName = (s.name || '—').replace(/'/g, "\\'");
    const tr = document.createElement('tr');
    tr.innerHTML = `
      <td style="font-weight:700;color:${nameColor}">${s.name || '—'}</td>
      <td style="color:#63b3ed">${s.username ? '@'+s.username : '—'}</td>
      <td><code style="font-size:10px;color:#a0aec0">${s.chat_id}</code></td>
      <td><code style="font-size:10px;color:#ecc94b">${s.key || '—'}</code></td>
      <td style="color:${active?'#19e3a0':'#fc8181'};font-size:11px">${s.key_exp_str}</td>
      <td>${notifyHtml}</td>
      <td>
        <button onclick="kickUser(${s.chat_id},'${safeName}')" style="background:#ed8936;color:#000;border:none;border-radius:4px;padding:3px 8px;cursor:pointer;font-size:11px;font-weight:700;margin-right:4px">KICK</button>
        <button onclick="showBan(${s.chat_id},'${safeName}')" style="background:#fc8181;color:#000;border:none;border-radius:4px;padding:3px 8px;cursor:pointer;font-size:11px;font-weight:700">BAN</button>
      </td>`;
    tbody.appendChild(tr);
  });
}

async function deleteKey(keyStr) {
  if (!confirm(`Xóa key ${keyStr}?\nTất cả user đang dùng key này sẽ bị kick.`)) return;
  const r = await fetch('/api/admin/deletekey', {
    method: 'POST', headers: {'Content-Type':'application/json'},
    body: JSON.stringify({key: keyStr})
  });
  const d = await r.json();
  alert(d.msg);
  loadKeys();
  loadSubs();
}

async function loadKeys() {
  const r = await fetch('/api/admin/keys');
  const d = await r.json();
  const tbody = document.getElementById('keysBody');
  tbody.innerHTML = '';
  // Update key count badge
  const badge = document.getElementById('keyCount');
  if (badge) badge.textContent = `${d.total} key`;

  d.keys.slice().reverse().forEach(k => {
    const slotColor = k.used_count >= k.max_users ? '#fc8181' : '#19e3a0';
    const slotTxt   = `${k.used_count}/${k.max_users}`;

    // Build users HTML
    let usersTxt = '—';
    if (k.users && k.users.length > 0) {
      usersTxt = k.users.map(u =>
        `<div style="font-size:10px;line-height:1.6">
          <code style="color:#a0aec0">${u.chat_id}</code>
          <span style="color:#e2e8f0"> ${u.name || ''}${u.username ? ' @'+u.username : ''}</span>
        </div>`
      ).join('');
    }

    const tr = document.createElement('tr');
    tr.innerHTML = `
      <td><code style="font-size:11px;color:#00ffcc;letter-spacing:1px">${k.key}</code></td>
      <td style="color:#ecc94b">${k.days}d</td>
      <td style="font-size:10px;color:#a0aec0">${k.expires}</td>
      <td style="color:${slotColor};font-weight:700">${slotTxt}</td>
      <td>${usersTxt}</td>
      <td style="color:${k.active?'#19e3a0':'#718096'}">${k.active?'Còn hạn':'Hết hạn'}</td>
      <td><button onclick="deleteKey('${k.key}')" style="background:#7f1d1d;color:#fc8181;border:1px solid #fc8181;border-radius:4px;padding:3px 8px;cursor:pointer;font-size:10px;font-weight:700">🗑 Xóa</button></td>`;
    tbody.appendChild(tr);
  });
}

async function genKey() {
  const days      = parseInt(document.getElementById('keyDays').value) || 7;
  const max_users = parseInt(document.getElementById('keyMaxUsers').value) || 1;
  const r = await fetch('/api/admin/genkey', {
    method: 'POST', headers: {'Content-Type':'application/json'},
    body: JSON.stringify({days, max_users})
  });
  const d = await r.json();
  if (d.ok) {
    const slotTxt = d.max_users > 1 ? ` · ${d.max_users} người` : ' · 1 người';
    document.getElementById('newKeyResult').innerHTML =
      `🔑 <b style="color:#00ffcc">${d.key}</b> — ${d.days} ngày${slotTxt} (hết ${d.expires})`;
    loadKeys();
  }
}

async function kickUser(chatId, name) {
  if (!confirm(`Kick ${name} (${chatId})?`)) return;
  const r = await fetch('/api/admin/kick', {
    method: 'POST', headers: {'Content-Type':'application/json'},
    body: JSON.stringify({chat_id: chatId})
  });
  const d = await r.json();
  alert(d.msg);
  loadSubs();
}


// ── Broadcast: danh sách user với checkbox ─────────────────────────────────
let broadcastAllUsers = [];  // [{chat_id, name, username}, ...]

async function loadBroadcastList() {
  try {
    const r  = await fetch('/api/admin/subs');
    const d  = await r.json();
    // Gộp key_users + started_users — API trả key_users
    broadcastAllUsers = d.subs.map(s => ({
      chat_id:  s.chat_id,
      name:     s.name || String(s.chat_id),
      username: s.username || '',
    }));
    renderBroadcastList();
  } catch(e) {
    document.getElementById('broadcastUserList').innerHTML =
      '<div style="color:#fc8181;font-size:11px;padding:6px">Lỗi load danh sách</div>';
  }
}

function renderBroadcastList() {
  const container = document.getElementById('broadcastUserList');
  if (!broadcastAllUsers.length) {
    container.innerHTML = '<div style="color:#4a5568;font-size:11px;text-align:center;padding:8px">Chưa có user nào</div>';
    return;
  }
  container.innerHTML = broadcastAllUsers.map((u, i) => {
    const label = u.name + (u.username ? ` @${u.username}` : '') + ` (${u.chat_id})`;
    return `<label style="display:flex;align-items:center;gap:6px;padding:3px 2px;cursor:pointer;font-size:11px;color:#a0aec0;border-bottom:1px solid #0a0c14">
      <input type="checkbox" id="bcu_${i}" data-cid="${u.chat_id}" checked
        style="accent-color:#ffb020;cursor:pointer;width:13px;height:13px">
      <span>${label}</span>
    </label>`;
  }).join('');
}

function broadcastCheckAll(checked) {
  document.querySelectorAll('#broadcastUserList input[type=checkbox]')
    .forEach(cb => cb.checked = checked);
}

async function doBroadcast() {
  const msg = document.getElementById('broadcastMsg').value.trim();
  if (!msg) { alert('Nhập nội dung thông báo!'); return; }
  const res = document.getElementById('broadcastResult');

  // Lấy danh sách chat_id được tích
  const checkboxes = document.querySelectorAll('#broadcastUserList input[type=checkbox]');
  let targets = null;
  if (checkboxes.length > 0) {
    targets = [];
    checkboxes.forEach(cb => {
      if (cb.checked) targets.push(parseInt(cb.dataset.cid));
    });
    if (!targets.length) { alert('Chưa chọn người nhận nào!'); return; }
  }

  res.textContent = '⏳ Đang gửi...';
  res.style.color = '#ecc94b';
  try {
    const r = await fetch('/api/admin/broadcast', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({message: msg, targets})
    });
    const d = await r.json();
    if (d.ok) {
      res.textContent = `✅ Đã gửi: ${d.sent}/${d.total} user, thất bại: ${d.failed}`;
      res.style.color = '#19e3a0';
      document.getElementById('broadcastMsg').value = '';
    } else {
      res.textContent = '❌ Lỗi: ' + (d.error || 'Unknown');
      res.style.color = '#fc8181';
    }
  } catch(e) {
    res.textContent = '❌ Network error';
    res.style.color = '#fc8181';
  }
}

let banTarget = null;
function showBan(chatId, name) {
  banTarget = {chatId, name};
  document.getElementById('banLabel').textContent = `Ban: ${name} (${chatId})`;
  document.getElementById('banModal').style.display = 'flex';
}
async function doBan() {
  const days = parseInt(document.getElementById('banDays').value) || 1;
  const r = await fetch('/api/admin/ban', {
    method: 'POST', headers: {'Content-Type':'application/json'},
    body: JSON.stringify({chat_id: banTarget.chatId, days})
  });
  const d = await r.json();
  alert(d.msg);
  document.getElementById('banModal').style.display = 'none';
  loadSubs();
}
</script>

<!-- Admin Panel Overlay -->
<div id="adminPanel" style="display:none;position:fixed;top:0;right:0;width:700px;height:100vh;background:#090b12;border-left:2px solid #2d3748;z-index:999;overflow-y:auto;padding:20px">
  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:16px">
    <span style="color:#00ffcc;font-size:14px;font-weight:700;letter-spacing:2px">⚙ ADMIN PANEL</span>
    <button onclick="toggleAdmin()" style="background:#1e2535;color:#a0aec0;border:1px solid #2d3748;border-radius:4px;padding:4px 10px;cursor:pointer">✕ Đóng</button>
  </div>


  <!-- Broadcast Thông Báo -->
  <div style="background:#0d1117;border:1px solid #ffb020;border-radius:8px;padding:14px;margin-bottom:14px">
    <div style="font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#ffb020;margin-bottom:10px;font-weight:700">📢 Gửi Thông Báo</div>
    <textarea id="broadcastMsg" placeholder="Nhập nội dung thông báo..." 
      style="width:100%;min-height:70px;background:#04040c;border:1px solid #2d3748;border-radius:6px;padding:8px 10px;color:#e2e8f0;font-size:12px;font-family:inherit;resize:vertical"></textarea>

    <!-- Danh sách người nhận với checkbox -->
    <div style="margin-top:10px;margin-bottom:6px;display:flex;justify-content:space-between;align-items:center">
      <div style="font-size:10px;color:#ffb020;font-weight:700;text-transform:uppercase;letter-spacing:1px">📋 Chọn người nhận</div>
      <div style="display:flex;gap:6px">
        <button onclick="broadcastCheckAll(true)"  style="background:#1e2535;color:#19e3a0;border:1px solid #2d3748;border-radius:4px;padding:2px 8px;cursor:pointer;font-size:10px">✓ Tất cả</button>
        <button onclick="broadcastCheckAll(false)" style="background:#1e2535;color:#fc8181;border:1px solid #2d3748;border-radius:4px;padding:2px 8px;cursor:pointer;font-size:10px">✗ Bỏ hết</button>
      </div>
    </div>
    <div id="broadcastUserList" style="max-height:160px;overflow-y:auto;background:#04040c;border:1px solid #1e2535;border-radius:6px;padding:6px 8px">
      <div style="color:#4a5568;font-size:11px;text-align:center;padding:8px">Nhấn ↺ Reload ở Subscribers để tải danh sách...</div>
    </div>
    <div style="display:flex;gap:8px;margin-top:8px;align-items:center">
      <button onclick="doBroadcast()" style="background:#ffb020;color:#000;border:none;border-radius:6px;padding:8px 18px;font-weight:700;cursor:pointer;font-size:12px">📤 GỬI</button>
      <button onclick="loadBroadcastList()" style="background:#1e2535;color:#ffb020;border:1px solid #ffb020;border-radius:6px;padding:8px 12px;font-weight:700;cursor:pointer;font-size:11px">↺ Load danh sách</button>
      <span id="broadcastResult" style="font-size:11px;color:#4a5568"></span>
    </div>
    <div style="margin-top:6px;font-size:10px;color:#4a5568">Tích = nhận · Bỏ tích = không nhận · Mặc định: tất cả được tích</div>
  </div>

  <!-- Gen Key -->
  <div style="background:#0d1117;border:1px solid #1e2535;border-radius:8px;padding:14px;margin-bottom:14px">
    <div style="font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#63b3ed;margin-bottom:10px;font-weight:700">🔑 Tạo Key Mới</div>
    <div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap">
      <div style="display:flex;flex-direction:column;gap:3px">
        <label style="font-size:9px;color:#718096;letter-spacing:.8px;text-transform:uppercase">Số ngày</label>
        <input id="keyDays" type="number" min="1" max="365" value="7"
          style="width:100px;background:#04040c;border:1px solid #2d3748;border-radius:6px;padding:7px 10px;color:#e2e8f0;font-size:12px">
      </div>
      <div style="display:flex;flex-direction:column;gap:3px">
        <label style="font-size:9px;color:#718096;letter-spacing:.8px;text-transform:uppercase">Tối đa người dùng (1-100)</label>
        <input id="keyMaxUsers" type="number" min="1" max="100" value="1"
          style="width:130px;background:#04040c;border:1px solid #2d3748;border-radius:6px;padding:7px 10px;color:#e2e8f0;font-size:12px">
      </div>
      <div style="display:flex;flex-direction:column;justify-content:flex-end;padding-bottom:0">
        <label style="font-size:9px;color:transparent">_</label>
        <button onclick="genKey()" style="background:#19e3a0;color:#04040c;border:none;border-radius:6px;padding:7px 16px;font-weight:700;cursor:pointer;font-size:12px">TẠO KEY</button>
      </div>
    </div>
    <div style="margin-top:8px;font-size:10px;color:#4a5568">
      Telegram: <code style="color:#718096">/newkey &lt;ngày&gt; [số người]</code>
      &nbsp;·&nbsp; Ví dụ: <code style="color:#718096">/newkey 7 100</code>
    </div>
    <div id="newKeyResult" style="margin-top:10px;font-size:12px;color:#a0aec0;padding:8px;background:#04040c;border-radius:6px;min-height:28px;border:1px solid #1e2535"></div>
  </div>

  <!-- Subscribers -->
  <div style="background:#0d1117;border:1px solid #1e2535;border-radius:8px;padding:14px;margin-bottom:14px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
      <div style="font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#63b3ed;font-weight:700">👥 Subscribers — <span id="subsCount">—</span></div>
      <button onclick="loadSubs()" style="background:#1e2535;color:#63b3ed;border:1px solid #2d3748;border-radius:4px;padding:3px 10px;cursor:pointer;font-size:11px">↺ Reload</button>
    </div>
    <div style="overflow-x:auto">
    <table style="width:100%;border-collapse:collapse;font-size:11px">
      <thead><tr style="color:#718096;border-bottom:1px solid #1e2535">
        <th style="padding:6px 8px;text-align:left">Tên</th>
        <th style="padding:6px 8px;text-align:left">Username</th>
        <th style="padding:6px 8px;text-align:left">Chat ID</th>
        <th style="padding:6px 8px;text-align:left">Key</th>
        <th style="padding:6px 8px;text-align:left">Hết hạn</th>
        <th style="padding:6px 8px;text-align:left">Nhận TĐ</th>
        <th style="padding:6px 8px;text-align:left">Action</th>
      </tr></thead>
      <tbody id="subsBody"></tbody>
    </table>
    </div>
  </div>

  <!-- Keys List -->
  <div style="background:#0d1117;border:1px solid #1e2535;border-radius:8px;padding:14px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
      <div style="font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#63b3ed;font-weight:700">
        🗝 Tất Cả Keys — <span id="keyCount" style="color:#ecc94b">—</span>
      </div>
      <button onclick="loadKeys()" style="background:#1e2535;color:#63b3ed;border:1px solid #2d3748;border-radius:4px;padding:3px 10px;cursor:pointer;font-size:11px">↺ Reload</button>
    </div>
    <div style="overflow-x:auto">
    <table style="width:100%;border-collapse:collapse;font-size:11px">
      <thead><tr style="color:#718096;border-bottom:1px solid #1e2535">
        <th style="padding:6px 8px;text-align:left">Key</th>
        <th style="padding:6px 8px;text-align:left">Hạn</th>
        <th style="padding:6px 8px;text-align:left">Hết hạn</th>
        <th style="padding:6px 8px;text-align:left">Slot</th>
        <th style="padding:6px 8px;text-align:left">Người dùng (Chat ID · Tên)</th>
        <th style="padding:6px 8px;text-align:left">Status</th>
        <th style="padding:6px 8px;text-align:left">Action</th>
      </tr></thead>
      <tbody id="keysBody"></tbody>
    </table>
    </div>
  </div>
</div>

<!-- Ban Modal -->
<div id="banModal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.7);z-index:1000;align-items:center;justify-content:center">
  <div style="background:#0d1117;border:1px solid #fc8181;border-radius:10px;padding:24px;min-width:300px">
    <div id="banLabel" style="color:#fc8181;font-weight:700;margin-bottom:14px;font-size:13px"></div>
    <label style="color:#a0aec0;font-size:11px">Số ngày ban (0 = vĩnh viễn, tối đa 10):</label>
    <input id="banDays" type="number" min="0" max="10" value="1"
      style="width:100%;margin-top:6px;background:#04040c;border:1px solid #2d3748;border-radius:6px;padding:7px 10px;color:#e2e8f0;font-size:13px">
    <div style="display:flex;gap:8px;margin-top:14px">
      <button onclick="doBan()" style="flex:1;background:#fc8181;color:#000;border:none;border-radius:6px;padding:8px;font-weight:700;cursor:pointer">XÁC NHẬN BAN</button>
      <button onclick="document.getElementById('banModal').style.display='none'" style="flex:1;background:#1e2535;color:#a0aec0;border:1px solid #2d3748;border-radius:6px;padding:8px;cursor:pointer">Huỷ</button>
    </div>
  </div>
</div>

<!-- Admin Toggle Button -->
<button onclick="toggleAdmin()" style="position:fixed;bottom:20px;right:20px;z-index:998;background:#2d3748;color:#63b3ed;border:1px solid #4a5568;border-radius:50%;width:44px;height:44px;font-size:18px;cursor:pointer;box-shadow:0 4px 12px rgba(0,0,0,.4)">⚙</button>

</body>
</html>
"""

# ─── App setup ────────────────────────────────────────────────────────────────
async def on_startup(app):
    load_history()    # load persistent history từ file trước
    load_subs_keys()
    load_started_users()
    app_state['tg_task'] = asyncio.create_task(tg_poll_loop())
    print(f"[TG] Bot started — token: {TG_TOKEN[:20]}...")

async def on_cleanup(app):
    # Force-save history trước khi tắt (tránh mất phiên chưa được ghi)
    if app_state['history']:
        _save_history_sync()
        print(f"[SHUTDOWN] Saved {len(app_state['history'])} phiên history")
    if app_state['tg_task'] and not app_state['tg_task'].done():
        app_state['tg_task'].cancel()
    if app_state['ws_task'] and not app_state['ws_task'].done():
        app_state['ws_task'].cancel()

def create_app():
    app = web.Application()
    app.on_startup.append(on_startup)
    app.on_cleanup.append(on_cleanup)
    app.router.add_get('/',                    handle_index)
    app.router.add_get('/api/events',          handle_sse)
    app.router.add_post('/api/connect',        handle_connect)
    app.router.add_post('/api/disconnect',     handle_disconnect)
    app.router.add_post('/api/clear',          handle_clear)
    app.router.add_get('/api/download',        handle_download)
    app.router.add_get('/api/adaptive',       handle_adaptive)
    app.router.add_get('/api/corr',            handle_corr)
    app.router.add_get('/api/pairs',           handle_pairs)
    app.router.add_get('/api/matrix',          handle_matrix)
    app.router.add_get('/api/session_tuner',   handle_session_tuner)
    # Admin API
    app.router.add_get('/api/admin/subs',      handle_admin_subs)
    app.router.add_get('/api/admin/keys',      handle_admin_keys)
    app.router.add_post('/api/admin/genkey',   handle_admin_genkey)
    app.router.add_post('/api/admin/deletekey',  handle_admin_delete_key)
    app.router.add_post('/api/admin/kick',     handle_admin_kick)
    app.router.add_post('/api/admin/ban',      handle_admin_ban)
    app.router.add_post('/api/admin/broadcast', handle_admin_broadcast)
    return app

if __name__ == '__main__':
    import threading
    print("=" * 60)
    print("  TX v28 — 6 Logic Engine + Warmup 10 + Logic Tuner + AutoLogin + AutoBet WS Real")
    print("  + Auto Reversed Newsession + BẺ ĐỘC TÔN + THIỂU SỐ 2-BẺ")
    print("  + TTOAN WR Switch + Last-Fail Trim (bù ván khi đổi ttoan)")
    print("  [NO CROSS-COMP] Luôn THEO majority — không bù trừ lô chéo")
    print(f"  http://localhost:{PORT}")
    print(f"  History file : history.json (lưu không giới hạn)")
    print(f"  Logic: L1–L6 | Top-3 auto-tune theo WR | Warmup {WARMUP_COUNT} phiên (1 lần)")
    print(f"  TTOAN: giữ WR≥60% | đổi WR<40% + trim từ ván sai gần nhất")
    print(f"  Session Tuner offset auto | Majority follow")
    print(f"  Telegram Bot : /tool (dự đoán) | /autobet (auto-cược) | /stop /stopbet")
    print("=" * 60)

    web.run_app(create_app(), host='0.0.0.0', port=int(os.environ.get('PORT', PORT)), access_log=None)
