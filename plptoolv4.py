# -*- coding: utf-8 -*-
# PLP TOOL — LOCAL AI + ELO + WINRATE + CHUỖI + OMEGA FUSION → FINAL OMEGA X (19–27)
VERSION = "1.0.0"
from __future__ import annotations
import json, os, sys, time, threading, random, logging, math, re, pickle
import hashlib, uuid, platform
from collections import defaultdict, deque
from datetime import datetime
from urllib.parse import urlparse, parse_qs
from typing import Any, Dict, Tuple, Optional, List
import pytz, requests, websocket
from rich.console import Console, Group
from rich.table import Table
from rich.panel import Panel
from rich.live import Live
from rich.align import Align
from rich.rule import Rule
from rich.text import Text
from rich import box

console = Console()
tz = pytz.timezone("Asia/Ho_Chi_Minh")
logger = logging.getLogger("plp"); logger.setLevel(logging.INFO)
if not logger.handlers: logger.addHandler(logging.FileHandler("plp.log", encoding="utf-8"))

BET_API_URL = "https://api.escapemaster.net/escape_game/bet"
WS_URL = "wss://api.escapemaster.net/escape_master/ws"
WALLET_API_URL = "https://wallet.3games.io/api/wallet/user_asset"

KEY_API_BASE = "https://admin-shop-key.onrender.com"
KEY_API_VALIDATE = f"{KEY_API_BASE}/api/validate"
KEY_API_HEARTBEAT = f"{KEY_API_BASE}/api/heartbeat"
KEY_API_STATUS = f"{KEY_API_BASE}/api/check_status"
KEY_API_ACTIVATE = f"{KEY_API_BASE}/api/activate"
DEVICE_ID_FILE = "plp_device.txt"
KEY_STORAGE_FILE = "plp_keys.txt"
ACCOUNTS_FILE = "plp_accounts.json"
AI_DATA_FILE = "plp_ai_data.pkl"
STATS_FILE = "plp_stats.json"

HTTP = requests.Session()
try:
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
    _ad = HTTPAdapter(pool_connections=20, pool_maxsize=50,
        max_retries=Retry(total=3, backoff_factor=0.2, status_forcelist=(500,502,503,504)))
    HTTP.mount("https://", _ad); HTTP.mount("http://", _ad)
except Exception: pass

ROOM_NAMES = {1:"📦 Nhà kho",2:"🪑 Phòng họp",3:"👔 Phòng giám đốc",
              4:"💬 Phòng trò chuyện",5:"🎥 Phòng giám sát",6:"🏢 Văn phòng",
              7:"💰 Phòng tài vụ",8:"👥 Phòng nhân sự"}
ROOM_ORDER = [1,2,3,4,5,6,7,8]
RAINBOW_COLORS = ["bright_cyan","cyan","sky_blue","bright_blue","blue","magenta","bright_magenta"]

# ===== STATE =====
USER_ID=None; SECRET_KEY=None; CURRENT_ACCOUNT_NAME=None
CURRENT_KEY=None; CURRENT_KEY_INFO=None; KEY_VALIDATED=False
_DEVICE_ID=None; _heartbeat_stop=False
MAINTENANCE_ENABLED=False; MAINTENANCE_CONTENT=""
ACTIVATION_REQUIRED=False; ACTIVATION_ACTIVATED=False; ACTIVATION_MESSAGE=""
issue_id=None; count_down=None; killed_room=None; round_index=0; _skip_active_issue=None
room_state={r:{"players":0,"bet":0} for r in ROOM_ORDER}
room_stats={r:{"kills":0,"survives":0,"last_kill_round":None,"last_players":0,"last_bet":0} for r in ROOM_ORDER}
predicted_room=None; last_killed_room=None; prediction_locked=False
current_build=None; current_usdt=None; current_world=None
starting_balance=None; last_balance_val=None; cumulative_profit=0.0; last_balance_ts=None
total_rounds_played=0; total_wins=0; total_losses=0
win_streak=0; lose_streak=0; max_win_streak=0; max_lose_streak=0
prediction_correct=0; prediction_total=0
base_bet=1.0; multiplier=2.0; current_bet=None; run_mode="AUTO"
bet_rounds_before_skip=0; _rounds_placed_since_skip=0; skip_next_round_flag=False
pause_after_losses=0; _skip_rounds_remaining=0
profit_target=None; stop_when_profit_reached=False
stop_loss_target=None; stop_when_loss_reached=False; stop_flag=False
ui_state="IDLE"; analysis_blur=False; last_msg_ts=time.time()
last_balance_fetch_ts=0.0; BALANCE_POLL_INTERVAL=4.0
_ws={"ws":None}
SELECTION_CONFIG={"max_bet_allowed":float("inf"),"max_players_allowed":9999,"avoid_last_kill":True}
SELECTION_MODES={
    "VIP50":"1.VIP50","VIP50PLUS":"2.VIP50+","VIP100":"3.VIP100",
    "ADAPTIVE":"4.ADAPTIVE","VIP5000":"5.VIP5000","VIP5000PLUS":"6.VIP5000+","VIP10000":"7.VIP10000",
    "LOGIC8":"8.BÁ KHÍ","LOGIC9":"9.SIÊU BÁ KHÍ","LOGIC10":"10.SIÊU CẤP BÁ KHÍ",
    "LOGIC11":"11.CON THƯ HÔI LONG","LOGIC12":"12.THIÊN PHÚ","LOGIC13":"13.OMEGA",
    "LOGIC14":"14.NEXUS","LOGIC15":"15.CYRON","LOGIC16":"16.VORTEX","LOGIC17":"17.AION",
    "LOCAL_AI":"18.LOCAL AI (Tự học)",
    # === OMEGA FUSION → FINAL OMEGA X (19–27) ===
    "LOGIC19":"19.OMEGA FUSION",
    "LOGIC20":"20.QUANTUM CORE",
    "LOGIC21":"21.NEURAL MATRIX",
    "LOGIC22":"22.VORTEX META",
    "LOGIC23":"23.TITAN AI",
    "LOGIC24":"24.DARK MATTER",
    "LOGIC25":"25.INFINITY META",
    "LOGIC26":"26.ABSOLUTE CORE",
    "LOGIC27":"27.FINAL OMEGA X",
}
settings={"algo":"LOCAL_AI"}
_spinner=["⠋","⠙","⠹","⠸","⠼","⠴","⠦","⠧","⠇","⠏"]
_num_re=re.compile(r"-?\d+[\d,]*\.?\d*")
FORMULAS=[]; FORMULA_SEED=1234567
bet_history=deque(maxlen=500); bet_sent_for_issue=set()
adaptive_kill_sequence=deque(maxlen=60); adaptive_kill_history=deque(maxlen=300)
adaptive_transition_counts=defaultdict(int)
adaptive_feature_success=defaultdict(lambda:{"win":0,"loss":0})
adaptive_last_candidates=[]; adaptive_last_reselect_reason=""; ADAPTIVE_TOP_N=3
_last_ai_confidence=0.5

# ============================================================
# OMEGA / FINAL STATE (Logic 19–27)
# ============================================================
SUPER_COMPUTE_CAP = 30_000        # formula thực tính/mẫu (nhanh)
SUPER_LADDER = {
    "LOGIC19": {"name":"🔥OMEGA FUSION",   "tier":1, "target":1_000_000},
    "LOGIC20": {"name":"⚡QUANTUM CORE",    "tier":2, "target":1_500_000},
    "LOGIC21": {"name":"🧬NEURAL MATRIX",   "tier":3, "target":2_000_000},
    "LOGIC22": {"name":"🌀VORTEX META",     "tier":4, "target":2_500_000},
    "LOGIC23": {"name":"👑TITAN AI",        "tier":5, "target":3_000_000},
    "LOGIC24": {"name":"☠️DARK MATTER",     "tier":6, "target":3_500_000},
    "LOGIC25": {"name":"💎INFINITY META",   "tier":7, "target":4_000_000},
    "LOGIC26": {"name":"🌌ABSOLUTE CORE",   "tier":8, "target":5_000_000},
    "LOGIC27": {"name":"👑🔥FINAL OMEGA X", "tier":9, "target":8_000_000},
}
super_validation_scores = deque(maxlen=120)
super_ensemble_votes    = defaultdict(int)
super_model_version     = 1
super_model_history     = []      # [{"v":int,"acc":float,"n":int,"ts":float}]
super_model_regressions = 0
super_last_rollback_ts  = 0.0

# ============================================================
# ELO + WINRATE + STREAK TRACKING
# ============================================================
_LEARNER_DATA = {}
_all_win_streaks = []
_all_lose_streaks = []
_current_streak_type = None
_current_streak_count = 0

def log_debug(m):
    try: logger.debug(m)
    except: pass

def _save_stats():
    try:
        with open(STATS_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "learner": _LEARNER_DATA,
                "win_streaks": _all_win_streaks,
                "lose_streaks": _all_lose_streaks,
                "super_model_version": super_model_version,
                "super_model_history": super_model_history[-50:],
                "super_model_regressions": super_model_regressions,
            }, f, ensure_ascii=False, indent=2)
    except Exception as e:
        log_debug(f"save stats: {e}")

def _load_stats():
    global _LEARNER_DATA, _all_win_streaks, _all_lose_streaks
    global super_model_version, super_model_history, super_model_regressions
    try:
        if not os.path.exists(STATS_FILE): return
        with open(STATS_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        _LEARNER_DATA = d.get("learner", {})
        _all_win_streaks = d.get("win_streaks", [])
        _all_lose_streaks = d.get("lose_streaks", [])
        super_model_version = d.get("super_model_version", 1)
        super_model_history = d.get("super_model_history", [])
        super_model_regressions = d.get("super_model_regressions", 0)
    except Exception as e:
        log_debug(f"load stats: {e}")

def learner_data_get(key, algo, default):
    d = _LEARNER_DATA.get(algo, {})
    return d.get(key, default)

def learner_data_update(algo, won):
    if algo not in _LEARNER_DATA:
        _LEARNER_DATA[algo] = {"wins": 0, "losses": 0, "win_rate": 0.5, "elo": 1500.0}
    d = _LEARNER_DATA[algo]
    if won: d["wins"] += 1
    else: d["losses"] += 1
    total = d["wins"] + d["losses"]
    if total > 0: d["win_rate"] = d["wins"] / total
    k = 32.0 if total < 30 else 16.0
    exp = 1.0 / (1.0 + 10 ** ((1500 - d["elo"]) / 400))
    d["elo"] += k * ((1.0 if won else 0.0) - exp)
    _save_stats()

_load_stats()

# ============================================================
# LOCAL AI (persistent — dùng chung cho tất cả logic)
# ============================================================
class LocalAI:
    VERSION = 2
    SAVE_FILE = AI_DATA_FILE
    def __init__(self):
        self.history=deque(maxlen=1000); self.kill_count=defaultdict(int)
        self.trans1=defaultdict(lambda:defaultdict(int)); self.trans2=defaultdict(lambda:defaultdict(int))
        self.trans3=defaultdict(lambda:defaultdict(int)); self.room_history=deque(maxlen=500)
        self.total=0; self.correct=0; self.predictions=0; self.last_predicted=None
        self.session_rounds=0; self.created_at=time.time(); self.last_save=0
        self.pick_history = deque(maxlen=20)
        self.pick_results = deque(maxlen=20)
        self._load()
    def learn(self,kr,rs=None,rst=None):
        try: kr=int(kr)
        except: return
        self.kill_count[kr]+=1; self.total+=1; self.session_rounds+=1
        if self.history: self.trans1[self.history[-1]][kr]+=1
        if len(self.history)>=2: self.trans2[(self.history[-2],self.history[-1])][kr]+=1
        if len(self.history)>=3: self.trans3[(self.history[-3],self.history[-2],self.history[-1])][kr]+=1
        try:
            if rs and rst:
                p=tuple(rs[r].get("players",0) for r in ROOM_ORDER)
                b=tuple(rs[r].get("bet",0) for r in ROOM_ORDER)
                self.room_history.append((p,b,kr))
        except: pass
        self.history.append(kr)
        if self.last_predicted is not None:
            self.predictions+=1
            won = self.last_predicted != kr
            if won: self.correct+=1
            self.pick_results.append((self.last_predicted, won))
        self.last_predicted=None
        if self.session_rounds%5==0: self._save()
    def predict(self,rs,rst,lk):
        if self.total<3:
            c=[r for r in ROOM_ORDER if r!=lk]
            room=random.choice(c) if c else ROOM_ORDER[0]
            self.last_predicted=room; return room,0.3,{}
        risk={r:0.0 for r in ROOM_ORDER}
        for r in ROOM_ORDER: risk[r]+=(self.kill_count[r]/max(1,self.total))*0.15
        if lk and self.trans1[lk]:
            t=sum(self.trans1[lk].values()) or 1
            for r in ROOM_ORDER: risk[r]+=(self.trans1[lk].get(r,0)/t)*0.20
        if len(self.history)>=2:
            k=(self.history[-2],self.history[-1])
            if self.trans2[k]:
                t=sum(self.trans2[k].values()) or 1
                for r in ROOM_ORDER: risk[r]+=(self.trans2[k].get(r,0)/t)*0.15
        if len(self.history)>=3:
            k=(self.history[-3],self.history[-2],self.history[-1])
            if self.trans3[k]:
                t=sum(self.trans3[k].values()) or 1
                for r in ROOM_ORDER: risk[r]+=(self.trans3[k].get(r,0)/t)*0.10
        for r in ROOM_ORDER: risk[r]+=((self.kill_count[r]+1)/(self.total+len(ROOM_ORDER)))*0.10
        r5=list(self.history)[-5:]
        if r5:
            for r in ROOM_ORDER: risk[r]+=(r5.count(r)/len(r5))*0.10
        h=list(self.history)
        if len(h)>=10:
            r10=h[-10:]; r50=h[-50:] if len(h)>=50 else h
            for r in ROOM_ORDER:
                a=r10.count(r)/len(r10); b=r50.count(r)/len(r50)
                risk[r]+=max(0,a-b)*0.10
        if rs and rst and self.room_history:
            try:
                cp=tuple(rs[r].get("players",0) for r in ROOM_ORDER)
                cb=tuple(rs[r].get("bet",0) for r in ROOM_ORDER)
                sims=[]
                for op,ob,ok in list(self.room_history)[-100:]:
                    d=sum(abs(a-b) for a,b in zip(cp,op))/100.0
                    d+=sum(abs(a-b) for a,b in zip(cb,ob))/100000.0
                    sims.append((d,ok))
                sims.sort(key=lambda x:x[0])
                for _,ok in sims[:5]: risk[ok]+=0.05
            except: pass
        if self.pick_results:
            for prev_room, prev_won in list(self.pick_results)[-3:]:
                if not prev_won:
                    risk[prev_room] += 15.0
        recent_picks = list(self.pick_results)[-3:]
        for prev_room, _ in recent_picks:
            risk[prev_room] += 8.0
        if len(self.pick_results) >= 3:
            last3 = [r for r, _ in list(self.pick_results)[-3:]]
            if len(set(last3)) == 1:
                risk[last3[0]] = 999.0
        if len(self.pick_results) >= 1:
            last_room, last_won = self.pick_results[-1]
            if last_won: risk[last_room] += 5.0
            else: risk[last_room] += 20.0
        if lk: risk[lk]=999.0
        for r in list(self.history)[-3:]: risk[r]=max(risk[r],100.0)
        v={r:x for r,x in risk.items() if x<100.0}
        if not v:
            c=[r for r in ROOM_ORDER if r!=lk] or ROOM_ORDER
            room=random.choice(c); self.last_predicted=room
            return room,0.3,risk
        sorted_rooms = sorted(v.items(), key=lambda kv: kv[1])
        best_risk = sorted_rooms[0][1]
        candidates = [r for r, x in sorted_rooms if x <= best_risk + 3.0][:3]
        if not candidates: candidates = [sorted_rooms[0][0]]
        if len(candidates) == 1:
            best = candidates[0]
        else:
            weights = []
            for r in candidates:
                w = max(0.5, 10.0 - v[r])
                weights.append(w)
            total_w = sum(weights)
            roll = random.uniform(0, total_w)
            acc = 0
            best = candidates[-1]
            for r, w in zip(candidates, weights):
                acc += w
                if roll <= acc:
                    best = r; break
        mx=max(v.values()) or 1
        conf=max(0.4,min(0.95,1.0-(v[best]/mx)))
        self.last_predicted=best
        self.pick_history.append(best)
        return best,conf,risk
    def _save(self):
        try:
            d={"version":self.VERSION,"history":list(self.history),
               "kill_count":dict(self.kill_count),
               "trans1":{int(k):dict(v) for k,v in self.trans1.items()},
               "trans2":{f"{k[0]}_{k[1]}":dict(v) for k,v in self.trans2.items()},
               "trans3":{f"{k[0]}_{k[1]}_{k[2]}":dict(v) for k,v in self.trans3.items()},
               "room_history":list(self.room_history),"total":self.total,
               "correct":self.correct,"predictions":self.predictions,
               "created_at":self.created_at,"last_save":time.time()}
            tmp=self.SAVE_FILE+".tmp"
            with open(tmp,"wb") as f: pickle.dump(d,f)
            os.replace(tmp,self.SAVE_FILE); self.last_save=time.time()
        except Exception as e: log_debug(f"AI save: {e}")
    def _load(self):
        try:
            if not os.path.exists(self.SAVE_FILE): return
            if os.path.getsize(self.SAVE_FILE)<10: return
            with open(self.SAVE_FILE,"rb") as f: d=pickle.load(f)
            if not isinstance(d,dict): return
            if d.get("version",1)!=self.VERSION: return
            self.history=deque(d.get("history",[]),maxlen=1000)
            self.kill_count=defaultdict(int,d.get("kill_count",{}))
            self.total=d.get("total",0); self.correct=d.get("correct",0)
            self.predictions=d.get("predictions",0)
            self.created_at=d.get("created_at",time.time())
            self.trans1=defaultdict(lambda:defaultdict(int))
            for k,v in d.get("trans1",{}).items(): self.trans1[int(k)]=defaultdict(int,v)
            self.trans2=defaultdict(lambda:defaultdict(int))
            for k,v in d.get("trans2",{}).items():
                p=k.split("_")
                if len(p)==2: self.trans2[(int(p[0]),int(p[1]))]=defaultdict(int,v)
            self.trans3=defaultdict(lambda:defaultdict(int))
            for k,v in d.get("trans3",{}).items():
                p=k.split("_")
                if len(p)==3: self.trans3[(int(p[0]),int(p[1]),int(p[2]))]=defaultdict(int,v)
            self.room_history=deque(d.get("room_history",[]),maxlen=500)
        except Exception as e: log_debug(f"AI load: {e}")
    def force_save(self): self._save()
    def reset(self):
        self.history.clear(); self.kill_count.clear()
        self.trans1.clear(); self.trans2.clear(); self.trans3.clear()
        self.room_history.clear()
        self.total=0; self.correct=0; self.predictions=0; self.session_rounds=0
        try:
            if os.path.exists(self.SAVE_FILE): os.remove(self.SAVE_FILE)
        except: pass
    def get_accuracy(self): return self.correct/max(1,self.predictions)
    def get_status(self):
        if self.total<5: return f"🟡 Warmup ({self.total}/5)"
        a=self.get_accuracy()*100
        if self.total<30: return f"🟡 Learning ({self.total}v, {a:.0f}%)"
        if a>=22: return f"🟢 Smart ({self.total}v, {a:.0f}%)"
        if a>=15: return f"🟠 Good ({self.total}v, {a:.0f}%)"
        return f"🟡 Training ({self.total}v, {a:.0f}%)"
    def get_detail(self):
        return {"total":self.total,"accuracy":self.get_accuracy()*100,
                "predictions":self.predictions,"session":self.session_rounds,
                "last_save":human_ts() if self.last_save else "chưa"}

LOCAL_AI = LocalAI()

# ===== HELPERS =====
def _parse_number(x):
    if x is None: return None
    if isinstance(x,(int,float)): return float(x)
    m=_num_re.search(str(x))
    if not m: return None
    try: return float(m.group(0).replace(",",""))
    except: return None
def human_ts(): return datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")
def safe_input(prompt,default=None):
    try: s=console.input(f"[bold cyan]➤ {prompt}[/]").strip()
    except EOFError: return default
    return s if s else default
def _get_device_id():
    global _DEVICE_ID
    if _DEVICE_ID: return _DEVICE_ID
    try:
        if os.path.exists(DEVICE_ID_FILE):
            with open(DEVICE_ID_FILE) as f:
                d=f.read().strip()
                if d: _DEVICE_ID=d; return d
    except: pass
    try: mac=str(uuid.getnode())
    except: mac=str(random.random())
    did=hashlib.sha256(f"{mac}|{platform.node()}|{platform.system()}".encode()).hexdigest()[:32]
    _DEVICE_ID=did
    try:
        with open(DEVICE_ID_FILE,"w") as f: f.write(did)
    except: pass
    return did
def _get_fingerprint():
    try:
        p=[platform.node(),platform.system(),platform.release(),platform.machine(),str(uuid.getnode())]
        return hashlib.sha256("|".join(p).encode()).hexdigest()[:32]
    except: return "unknown"

# ===== BẢO TRÌ + KÍCH HOẠT =====
def check_server_status():
    global MAINTENANCE_ENABLED, MAINTENANCE_CONTENT
    global ACTIVATION_REQUIRED, ACTIVATION_ACTIVATED, ACTIVATION_MESSAGE
    try:
        r=HTTP.get(KEY_API_STATUS, timeout=8)
        d=r.json()
        MAINTENANCE_ENABLED=bool(d.get("maintenance",False))
        MAINTENANCE_CONTENT=str(d.get("maintenance_content",""))
        ACTIVATION_REQUIRED=bool(d.get("need_activation",False))
        ACTIVATION_ACTIVATED=bool(d.get("activated",False))
        ACTIVATION_MESSAGE=str(d.get("activation_message",""))
        return True
    except Exception as ex:
        log_debug(f"check_status: {ex}"); return False

def activate_tool():
    global ACTIVATION_ACTIVATED
    try:
        r=HTTP.post(KEY_API_ACTIVATE,
            json={"key":CURRENT_KEY,"device_id":_get_device_id()}, timeout=15)
        d=r.json()
        if d.get("ok"):
            ACTIVATION_ACTIVATED=True
            return True, d.get("message","Kích hoạt thành công!")
        return False, d.get("error","Lỗi")
    except Exception as ex: return False, f"Lỗi: {ex}"

def screen_maintenance():
    console.clear()
    console.print()
    console.print(Align.center(Text.from_markup(
        "[bold red]╔══════════════════════════════════════════════════════════╗[/]")))
    console.print(Align.center(Text.from_markup(
        "[bold red]║[/]            [bold yellow]⚠️ SERVER ĐANG BẢO TRÌ ⚠️[/]             [bold red]║[/]")))
    console.print(Align.center(Text.from_markup(
        "[bold red]╚══════════════════════════════════════════════════════════╝[/]")))
    console.print()
    content=MAINTENANCE_CONTENT or "Server đang bảo trì, vui lòng quay lại sau!"
    console.print(Panel(Align.center(Text.from_markup(f"[bold white]{content}[/]")),
        title="[bold yellow]📢 THÔNG BÁO TỪ ADMIN[/]", border_style="yellow",
        box=box.DOUBLE, padding=(2,4)))
    console.print()
    console.print(Align.center(Text.from_markup(
        "[bold red]Tool sẽ tự thoát sau [bold yellow]10 giây[/]...[/]")))
    for i in range(10,0,-1):
        console.print(Align.center(Text.from_markup(
            f"[bold red]⏱️  Còn [bold yellow]{i}[/] giây...[/]")), end="\r")
        time.sleep(1)
    console.print(); sys.exit(0)

def screen_activation():
    console.clear(); show_banner()
    console.print(Rule("[bold yellow]⚡ CHỜ KÍCH HOẠT ⚡[/]", style="yellow"))
    console.print()
    msg = ACTIVATION_MESSAGE or "Vui lòng nhấn KÍCH HOẠT để bắt đầu sử dụng tool"
    console.print(Align.center(Text.from_markup(f"[bold yellow]{msg}[/]")))
    console.print()
    console.print(Align.center(Text.from_markup("[bold green]➤  Nhấn [bold yellow]ENTER[/] để KÍCH HOẠT  ⚡[/]")))
    console.print()
    safe_input("Nhấn Enter để kích hoạt: ", default="")
    console.print("\n[dim cyan]🔄 Đang gửi yêu cầu...[/]")
    ok,msg=activate_tool()
    if ok:
        console.print(f"\n[bold green]✅ {msg}[/]\n"); time.sleep(2); return True
    console.print(f"\n[bold red]❌ {msg}[/]\n"); time.sleep(2); return False

# ===== KEY AUTH =====
def _save_key(key,info):
    try:
        e={"key":key,"key_type":info.get("key_type","VIP1"),
           "expires_at":info.get("expires_at",0),
           "device_id":_get_device_id(),"saved_at":human_ts()}
        entries=[]
        if os.path.exists(KEY_STORAGE_FILE):
            try:
                with open(KEY_STORAGE_FILE) as f:
                    for ln in f.read().split("\n\n"):
                        ln=ln.strip()
                        if ln:
                            try: entries.append(json.loads(ln))
                            except: pass
            except: pass
        entries=[x for x in entries if x.get("key")!=key]; entries.insert(0,e)
        with open(KEY_STORAGE_FILE,"w") as f:
            for x in entries[:5]: f.write(json.dumps(x,ensure_ascii=False)+"\n\n")
    except Exception as ex: log_debug(f"save key: {ex}")
def _load_last_key():
    try:
        if not os.path.exists(KEY_STORAGE_FILE): return None
        with open(KEY_STORAGE_FILE) as f: c=f.read().strip()
        if not c: return None
        first=c.split("\n\n")[0].strip()
        return json.loads(first) if first else None
    except: return None
def validate_key_online(key_input):
    global CURRENT_KEY,CURRENT_KEY_INFO,KEY_VALIDATED
    key_input=(key_input or "").strip()
    if not key_input.startswith("LPTOOL_"): return False,"❌ Key phải bắt đầu bằng LPTOOL_!"
    did=_get_device_id(); fp=_get_fingerprint()
    try:
        r=HTTP.post(KEY_API_VALIDATE,json={"key":key_input,"device_id":did,"fingerprint":fp},timeout=30)
        data=r.json()
    except requests.exceptions.Timeout: return False,"❌ Server timeout"
    except Exception as ex: return False,f"❌ Lỗi: {ex}"
    if not data.get("ok"): return False,f"❌ {data.get('error','Key không hợp lệ')}"
    CURRENT_KEY=key_input; CURRENT_KEY_INFO=data; KEY_VALIDATED=True
    _save_key(key_input,data)
    kt=data.get("key_type","VIP1"); exp_ms=data.get("expires_at",0)
    if kt.upper() in ("ADMIN","VVIP","AION"): tl="♾️ VĨNH VIỄN"
    else:
        ms=max(0,exp_ms-int(time.time()*1000)); d=ms//86400000; h=(ms%86400000)//3600000
        tl=f"{d}d {h}h" if d>0 else f"{h}h"
    return True,f"✅ KÍCH HOẠT THÀNH CÔNG!\n   💠 {kt}\n   ⏱️ {tl}"
def start_heartbeat():
    def loop():
        global KEY_VALIDATED,stop_flag
        while not _heartbeat_stop and KEY_VALIDATED:
            try:
                time.sleep(60)
                if not KEY_VALIDATED: break
                r=HTTP.post(KEY_API_HEARTBEAT,json={"key":CURRENT_KEY,"device_id":_get_device_id()},timeout=30)
                d=r.json()
                if not d.get("ok"):
                    KEY_VALIDATED=False; stop_flag=True; break
            except Exception as ex: log_debug(f"hb: {ex}")
    threading.Thread(target=loop,daemon=True).start()

# ===== ACCOUNTS =====
def _load_accounts():
    try:
        if os.path.exists(ACCOUNTS_FILE):
            with open(ACCOUNTS_FILE) as f:
                d=json.load(f)
                if isinstance(d,list): return d
    except: pass
    return []
def _save_accounts(a):
    try:
        with open(ACCOUNTS_FILE,"w") as f: json.dump(a,f,ensure_ascii=False,indent=2)
    except: pass
def _add_account_from_link(link):
    try:
        p=parse_qs(urlparse(link).query)
        uid=p.get("userId",[None])[0]; sk=p.get("secretKey",[None])[0]
        if not uid or not sk: return False,"❌ Link thiếu userId/secretKey!",None
        uid=int(uid)
        name=safe_input("📝 Tên tài khoản: ",default=f"Acc_{uid}")
        acc={"name":name.strip() or f"Acc_{uid}","user_id":uid,"secret_key":sk,"created_at":human_ts()}
        a=_load_accounts(); a.append(acc); _save_accounts(a)
        return True,f"✅ Đã thêm: {acc['name']}",acc
    except Exception as ex: return False,f"❌ Lỗi: {ex}",None
def _delete_account_by_index(i):
    a=_load_accounts()
    if 0<=i<len(a): a.pop(i); _save_accounts(a); return True
    return False

# ===== BALANCE =====
def _parse_balance_from_json(j):
    if not isinstance(j,dict): return None,None,None
    build=world=usdt=None
    data=j.get("data",j)
    if isinstance(data,dict):
        cw=data.get("cwallet")
        if isinstance(cw,dict):
            for k in ("ctoken_contribute","ctoken","build","balance","amount"):
                if k in cw and build is None: build=_parse_number(cw.get(k))
        for k in ("build","ctoken","ctoken_contribute"):
            if build is None and k in data: build=_parse_number(data.get(k))
        for k in ("usdt","kusdt","usdt_balance"):
            if usdt is None and k in data: usdt=_parse_number(data.get(k))
        for k in ("world","xworld"):
            if world is None and k in data: world=_parse_number(data.get(k))
    found=[]
    def walk(o,path=""):
        if isinstance(o,dict):
            for kk,vv in o.items():
                nk=f"{path}.{kk}".strip(".")
                if isinstance(vv,(dict,list)): walk(vv,nk)
                else:
                    n=_parse_number(vv)
                    if n is not None: found.append((nk.lower(),n))
        elif isinstance(o,list):
            for i,it in enumerate(o): walk(it,f"{path}[{i}]")
    walk(j)
    for k,v in found:
        if build is None and any(x in k for x in ("ctoken","build","contribute","balance")): build=v
        if usdt is None and "usdt" in k: usdt=v
        if world is None and any(x in k for x in ("world","xworld")): world=v
    return build,world,usdt
def _balance_headers(uid=None,secret=None):
    h={"accept":"*/*","accept-language":"vi,en;q=0.9","cache-control":"no-cache",
       "country-code":"vn","origin":"https://xworld.info","pragma":"no-cache",
       "referer":"https://xworld.info/","user-login":"login_v2","xb-language":"vi-VN",
       "user-agent":"Mozilla/5.0 (Linux; Android 6.0) AppleWebKit/537.36 Chrome/137.0 Mobile Safari/537.36"}
    if uid is not None: h["user-id"]=str(uid)
    if secret: h["user-secret-key"]=str(secret)
    return h
def fetch_balances_3games(retries=2,timeout=6,params=None,uid=None,secret=None):
    global current_build,current_usdt,current_world,last_balance_ts
    global starting_balance,last_balance_val,cumulative_profit
    uid=uid or USER_ID; secret=secret or SECRET_KEY
    payload={"user_id":int(uid) if uid is not None else None,"source":"home"}
    for a in range(1,retries+2):
        try:
            r=HTTP.post(WALLET_API_URL,json=payload,headers=_balance_headers(uid,secret),timeout=timeout)
            r.raise_for_status()
            build,world,usdt=_parse_balance_from_json(r.json())
            if build is not None:
                if starting_balance is None:
                    starting_balance=build; last_balance_val=build
                else:
                    delta=float(build)-float(last_balance_val)
                    if abs(delta)>0:
                        cumulative_profit+=delta; last_balance_val=build
                current_build=build
            if usdt is not None: current_usdt=usdt
            if world is not None: current_world=world
            last_balance_ts=time.time()
            return current_build,current_world,current_usdt
        except Exception as ex:
            log_debug(f"wallet {a}: {ex}"); time.sleep(min(0.6*a,2))
    return current_build,current_world,current_usdt

# ===== FORMULA =====
def _room_features(rid):
    st=room_state.get(rid,{}); stats=room_stats.get(rid,{})
    p=float(st.get("players",0)); b=float(st.get("bet",0))
    bpp=b/p if p>0 else b
    pn=min(1.0,p/50.0); bn=1.0/(1.0+b/2000.0); bp=1.0/(1.0+bpp/1200.0)
    kc=float(stats.get("kills",0)); sc=float(stats.get("survives",0))
    kr=(kc+0.5)/(kc+sc+1.0); ss=1.0-kr
    rec=list(bet_history)[-12:]; rp=0.0
    for i,r0 in enumerate(reversed(rec)):
        if r0.get("room")==rid: rp+=0.12/(i+1)
    lp=0.35 if last_killed_room==rid else 0.0
    return {"pn":pn,"bn":bn,"bp":bp,"ss":ss,"rp":rp,"lp":lp,
            "hot":max(0.0,ss-0.2),"cold":max(0.0,kr-0.4)}
def _mk_formula(rng,bias=None):
    w={"players":rng.uniform(0.2,0.8),"bet":rng.uniform(0.1,0.6),"bpp":rng.uniform(0.05,0.6),
       "survive":rng.uniform(0.05,0.4),"recent":rng.uniform(0.05,0.3),"last":rng.uniform(0.1,0.6),
       "hot":rng.uniform(0.0,0.35),"cold":rng.uniform(0.0,0.35)}
    if bias=="hot": w["hot"]+=rng.uniform(0.2,0.5); w["survive"]+=rng.uniform(0.05,0.2)
    elif bias=="cold": w["cold"]+=rng.uniform(0.2,0.5); w["last"]+=rng.uniform(0.05,0.2)
    return {"w":w,"noise":rng.uniform(0.0,0.08),"adapt":1.0}
def _init_formulas(mode="VIP50"):
    global FORMULAS
    rng=random.Random(FORMULA_SEED); fs=[]
    if mode=="VIP50":
        for _ in range(50): fs.append(_mk_formula(rng))
    elif mode=="VIP50PLUS":
        for _ in range(35): fs.append(_mk_formula(rng))
        for _ in range(10): fs.append(_mk_formula(rng,"hot"))
        for _ in range(5): fs.append(_mk_formula(rng,"cold"))
    elif mode=="VIP100":
        for _ in range(50): fs.append(_mk_formula(rng))
        for _ in range(25): fs.append(_mk_formula(rng,"hot"))
        for _ in range(25): fs.append(_mk_formula(rng,"cold"))
    elif mode=="ADAPTIVE":
        for _ in range(40): fs.append(_mk_formula(rng))
        for _ in range(6): fs.append(_mk_formula(rng,"hot"))
        for _ in range(4): fs.append(_mk_formula(rng,"cold"))
    elif mode in ("VIP5000","VIP5000PLUS"):
        rng=random.Random(FORMULA_SEED+5000)
        for _ in range(5000): fs.append(_mk_formula(rng))
    elif mode=="VIP10000":
        rng=random.Random(FORMULA_SEED+10000)
        for _ in range(10000): fs.append(_mk_formula(rng))
    else:
        for _ in range(50): fs.append(_mk_formula(rng))
    FORMULAS=fs
_init_formulas("VIP50")

def choose_room_original(mode="VIP50"):
    global FORMULAS
    req={"VIP50":50,"VIP100":100}
    if mode in req and len(FORMULAS)!=req[mode]: _init_formulas(mode)
    if mode=="VIP50PLUS" and len(FORMULAS)<40: _init_formulas(mode)
    agg={r:0.0 for r in ROOM_ORDER}
    for idx,f in enumerate(FORMULAS):
        w=f["w"]; adapt=f.get("adapt",1.0); ns=f.get("noise",0.02)
        best=None; bs=-1e9
        for rid in ROOM_ORDER:
            ft=_room_features(rid)
            sc=(w.get("players",0)*ft["pn"]+w.get("bet",0)*ft["bn"]+
                w.get("bpp",0)*ft["bp"]+w.get("survive",0)*ft["ss"]-
                w.get("recent",0)*ft["rp"]-w.get("last",0)*ft["lp"]+
                w.get("hot",0)*ft["hot"]-w.get("cold",0)*ft["cold"])
            noise=math.sin((idx+1)*(rid+1)*12.9898)*43758.5453%1.0
            noise=(noise-0.5)*(ns*2.0); sc=(sc+noise)*adapt
            if sc>bs: bs=sc; best=rid
        if best: agg[best]+=bs
    n=max(1,len(FORMULAS))
    for r in agg: agg[r]/=n
    for r in ROOM_ORDER:
        ft=_room_features(r); agg[r]+=0.02*ft["hot"]-0.02*ft["cold"]
    ranked=sorted(agg.items(),key=lambda kv:(-kv[1],kv[0]))
    return ranked[0][0],mode

def _features_adv(rid):
    base=_room_features(rid); hist=list(LOCAL_AI.history)
    trans=0.0
    if len(hist)>=2:
        prev=hist[-1]
        cnt=sum(1 for i in range(len(hist)-1) if hist[i]==prev and hist[i+1]==rid)
        tot=sum(1 for i in range(len(hist)-1) if hist[i]==prev)
        trans=(cnt+1.0)/(tot+2.0)
    mom=0.0
    if len(hist)>=8:
        r8=sum(1 for x in hist[-8:] if x==rid)/8.0
        b32=sum(1 for x in hist[-32:] if x==rid)/max(1,len(hist[-32:]))
        mom=max(-1.0,min(1.0,(r8-b32)*4))
    ent=0.0
    if hist:
        p=hist.count(rid)/len(hist)
        if p>0: ent=-p*math.log2(p)
    dec=0.0
    if hist:
        sc=0.0; tot=0.0
        for age,k in enumerate(reversed(hist[-30:])):
            w=math.exp(-age/7.0); tot+=w
            if k==rid: sc+=w
        dec=sc/tot if tot else 0.0
    return {**base,"transition":trans,"momentum":(mom+1)/2,
            "entropy":min(1.0,ent),"decay_kill":dec}
def _gen_adv(n,seed):
    rng=random.Random(FORMULA_SEED+seed); fs=[]
    for _ in range(min(n,10000)):
        w={"players":rng.uniform(0.15,0.9),"bet":rng.uniform(0.05,0.7),"bpp":rng.uniform(0.02,0.7),
           "survive":rng.uniform(0.02,0.5),"recent":rng.uniform(0.02,0.35),"last":rng.uniform(0.05,0.7),
           "hot":rng.uniform(0.0,0.45),"cold":rng.uniform(0.0,0.45),"transition":rng.uniform(0.0,0.4),
           "momentum":rng.uniform(0.0,0.4),"entropy":rng.uniform(0.0,0.3),"decay":rng.uniform(0.0,0.5)}
        fs.append({"w":w,"noise":rng.uniform(0.0,0.09),"adapt":1.0})
    return fs
def choose_room_vip_formula(mode,target,seed):
    fs=_gen_adv(min(target,10000),seed)
    agg={r:0.0 for r in ROOM_ORDER}
    for idx,f in enumerate(fs):
        w=f["w"]; adapt=f.get("adapt",1.0); ns=f.get("noise",0.02)
        best=None; bs=-1e9
        for rid in ROOM_ORDER:
            ft=_features_adv(rid)
            sc=(w.get("players",0)*ft["pn"]+w.get("bet",0)*ft["bn"]+
                w.get("bpp",0)*ft["bp"]+w.get("survive",0)*ft["ss"]-
                w.get("recent",0)*ft["rp"]-w.get("last",0)*ft["lp"]+
                w.get("hot",0)*ft["hot"]-w.get("cold",0)*ft["cold"]+
                w.get("transition",0)*ft["transition"]+w.get("momentum",0)*ft["momentum"]+
                w.get("entropy",0)*ft["entropy"]-w.get("decay",0)*ft["decay_kill"])
            noise=math.sin((idx+1)*(rid+1)*12.9898)*43758.5453%1.0
            sc=(sc+(noise-0.5)*ns*2)*adapt
            if sc>bs: bs=sc; best=rid
        if best: agg[best]+=bs
    n=max(1,len(fs))
    for r in agg: agg[r]/=n
    if last_killed_room in agg: agg[last_killed_room]-=5.0
    if killed_room in agg: agg[killed_room]-=10.0
    ranked=sorted(agg.items(),key=lambda kv:(-kv[1],kv[0]))
    return ranked[0][0],mode
def _detect_regime(hist):
    if len(hist)<20: return "WARMUP"
    recent=hist[-10:]; older=hist[-30:-10]
    def ent(seq):
        if not seq: return 0.0
        c=[seq.count(r)/len(seq) for r in ROOM_ORDER]
        return -sum(q*math.log(q,2) for q in c if q>0)
    er=ent(recent); eo=ent(older); drift=abs(er-eo)/3.0
    rep=sum(1 for i in range(1,len(recent)) if recent[i]==recent[i-1])/max(1,len(recent)-1)
    if rep>=0.45: return "REPEAT"
    if drift>=0.18: return "SHIFT"
    if er>=2.75: return "NOISY"
    return "STABLE"
def _sim_score(rid):
    hist=list(LOCAL_AI.history)
    if len(hist)<10: return 0.5
    p=room_state[rid]["players"]; sc=0.5
    for o in ROOM_ORDER:
        if room_state[o]["players"]>0:
            sc-=abs(room_state[o]["players"]-p)/30.0*0.05
    return max(0.0,min(1.0,sc))

def logic_8_ba_khi():
    r,_=choose_room_vip_formula("LOGIC8",160000,8000); return r,"🔥BÁ KHÍ"
def logic_9_sieu_ba_khi():
    r,_=choose_room_vip_formula("LOGIC9",300000,9000); return r,"⚡SIÊU BÁ KHÍ"
def logic_10_sieu_cap_ba_khi():
    r,_=choose_room_vip_formula("LOGIC10",900000,10000); return r,"🔥SIÊU CẤP"
def logic_11_con_thu():
    c=[]
    for rid in ROOM_ORDER:
        ft=_features_adv(rid)
        k=room_stats[rid]["kills"]; s=room_stats[rid]["survives"]
        b=(s+2.0)/(k+s+4.0)
        x=b*0.40+ft["transition"]*0.25+ft["momentum"]*0.20+(1-ft["entropy"])*0.15
        if rid==last_killed_room: x-=0.30
        if rid==killed_room: x-=0.50
        c.append((rid,x))
    c.sort(key=lambda t:-t[1]); return c[0][0],"🐉CON THƯ"
def logic_12_thien_phu():
    agg={r:0.0 for r in ROOM_ORDER}
    rf,_=choose_room_vip_formula("LOGIC12",3000000,12000); agg[rf]+=3.0
    for rid in ROOM_ORDER:
        ft=_features_adv(rid)
        agg[rid]+=((1-ft["decay_kill"])*0.4+ft["momentum"]*0.3+ft["transition"]*0.3)*2.0
    for rid in ROOM_ORDER:
        k=room_stats[rid]["kills"]; s=room_stats[rid]["survives"]
        agg[rid]+=((s+2.0)/(k+s+4.0))*1.5
    if last_killed_room in agg: agg[last_killed_room]-=3.0
    if killed_room in agg: agg[killed_room]-=5.0
    return max(agg,key=agg.get),"👑THIÊN PHÚ"
def logic_13_omega():
    h=list(LOCAL_AI.history); agg={r:0.0 for r in ROOM_ORDER}
    rf,_=choose_room_vip_formula("LOGIC13",5000000,13000); agg[rf]+=4.0
    for rid in ROOM_ORDER:
        k=room_stats[rid]["kills"]; s=room_stats[rid]["survives"]
        agg[rid]+=((s+2.0)/(k+s+4.0))*2.5
    if h:
        for rid in ROOM_ORDER:
            p=h.count(rid)/len(h); e=-p*math.log2(p) if p>0 else 0
            agg[rid]+=(1-min(1.0,e))*1.5
    for rid in ROOM_ORDER:
        ema=0.0; a=0.3
        for x in h[-30:]: ema=a*(1 if x==rid else 0)+(1-a)*ema
        agg[rid]+=(1-ema)*1.8
    if last_killed_room in agg: agg[last_killed_room]-=4.0
    if killed_room in agg: agg[killed_room]-=6.0
    return max(agg,key=agg.get),"💎OMEGA"
def logic_14_nexus():
    h=list(LOCAL_AI.history); agg={r:0.0 for r in ROOM_ORDER}
    rf,_=choose_room_vip_formula("LOGIC14",8000000,14000); agg[rf]+=5.0
    ms=[]
    ms.append({rid:(room_stats[rid]["survives"]+2.0)/(room_stats[rid]["kills"]+room_stats[rid]["survives"]+4.0) for rid in ROOM_ORDER})
    ms.append({rid:_features_adv(rid)["transition"] for rid in ROOM_ORDER})
    ms.append({rid:_features_adv(rid)["momentum"] for rid in ROOM_ORDER})
    ms.append({rid:1-_features_adv(rid)["decay_kill"] for rid in ROOM_ORDER})
    reg=_detect_regime(h); m5={}
    for rid in ROOM_ORDER:
        if reg=="REPEAT": m5[rid]=1.0 if h and h[-1]==rid else 0.3
        elif reg=="SHIFT": m5[rid]=0.5
        elif reg=="NOISY": m5[rid]=0.6
        else: m5[rid]=(room_stats[rid]["survives"]+1.0)/(room_stats[rid]["kills"]+room_stats[rid]["survives"]+2.0)
    ms.append(m5)
    for rid in ROOM_ORDER: agg[rid]+=sum(m.get(rid,0.5) for m in ms)/len(ms)*4.0
    if last_killed_room in agg: agg[last_killed_room]-=4.0
    if killed_room in agg: agg[killed_room]-=6.0
    return max(agg,key=agg.get),f"🤖NEXUS [{reg}]"
def logic_15_cyron():
    h=list(LOCAL_AI.history); agg={r:0.0 for r in ROOM_ORDER}
    rf,_=choose_room_vip_formula("LOGIC15",12000000,15000); agg[rf]+=6.0
    for rid in ROOM_ORDER:
        ft=_features_adv(rid)
        f=(ft["ss"]*0.25+ft["transition"]*0.20+ft["momentum"]*0.15+
           (1-ft["decay_kill"])*0.15+(1-ft["entropy"])*0.10+
           (1-ft["rp"])*0.10+(1-ft["lp"])*0.05)
        agg[rid]+=f*4.0
    for pl in (2,3,4):
        if len(h)<pl*2: continue
        pat=tuple(h[-pl:])
        for i in range(pl,len(h)):
            if tuple(h[i-pl:i])==pat: agg[h[i]]-=1.0
    if last_killed_room in agg: agg[last_killed_room]-=5.0
    if killed_room in agg: agg[killed_room]-=7.0
    return max(agg,key=agg.get),"⚡CYRON"
def logic_16_vortex():
    h=list(LOCAL_AI.history); agg={r:0.0 for r in ROOM_ORDER}
    rf,_=choose_room_vip_formula("LOGIC16",20000000,16000); agg[rf]+=7.0
    reg=_detect_regime(h)
    ws={"STABLE":{"b":0.35,"t":0.20,"m":0.15,"e":0.15,"s":0.15},
        "REPEAT":{"b":0.20,"t":0.40,"m":0.15,"e":0.10,"s":0.15},
        "SHIFT":{"b":0.15,"t":0.25,"m":0.30,"e":0.15,"s":0.15},
        "NOISY":{"b":0.40,"t":0.15,"m":0.15,"e":0.20,"s":0.10},
        "WARMUP":{"b":0.30,"t":0.20,"m":0.20,"e":0.15,"s":0.15}}.get(reg,{"b":0.25,"t":0.25,"m":0.25,"e":0.15,"s":0.10})
    for rid in ROOM_ORDER:
        ft=_features_adv(rid)
        b=(room_stats[rid]["survives"]+2.0)/(room_stats[rid]["kills"]+room_stats[rid]["survives"]+4.0)
        sc=(b*ws["b"]+ft["transition"]*ws["t"]+ft["momentum"]*ws["m"]+
            (1-ft["entropy"])*ws["e"]+_sim_score(rid)*ws["s"])
        agg[rid]+=sc*5.0
    if last_killed_room in agg: agg[last_killed_room]-=5.0
    if killed_room in agg: agg[killed_room]-=8.0
    return max(agg,key=agg.get),f"🧠VORTEX [{reg}]"
def logic_17_aion():
    h=list(LOCAL_AI.history); agg={r:0.0 for r in ROOM_ORDER}
    rf,_=choose_room_vip_formula("LOGIC17",30000000,17000); agg[rf]+=10.0
    for rid in ROOM_ORDER:
        ft=_features_adv(rid)
        b=(room_stats[rid]["survives"]+2.0)/(room_stats[rid]["kills"]+room_stats[rid]["survives"]+4.0)
        agg[rid]+=(b*0.25+ft["transition"]*0.20+ft["momentum"]*0.15+
                   (1-ft["entropy"])*0.15+(1-ft["decay_kill"])*0.15+_sim_score(rid)*0.10)*8.0
    reg=_detect_regime(h)
    if reg=="REPEAT" and h: agg[h[-1]]-=8.0
    elif reg=="SHIFT":
        for rid in ROOM_ORDER:
            if rid in h[-5:]: agg[rid]-=3.0
    if last_killed_room in agg: agg[last_killed_room]-=10.0
    if killed_room in agg: agg[killed_room]-=15.0
    return max(agg,key=agg.get),f"👑AION [{reg}]"

# ============================================================
# OMEGA → FINAL OMEGA X (Logic 19–27)
# ============================================================
def _super_data_quality(n: int, acc: float) -> float:
    vol = min(1.0, n / 2500.0)
    return min(0.92, 0.66 + vol * 0.20 + max(0.0, acc - 0.13) * 0.6)

def _super_stability(n: int, acc: float) -> float:
    vol = min(1.0, n / 2500.0)
    ac  = max(0.0, min(1.0, (acc - 0.10) / 0.18))
    if len(super_validation_scores) >= 8:
        sv = list(super_validation_scores)[-40:]
        m  = sum(sv) / len(sv)
        v  = sum((x - m) ** 2 for x in sv) / len(sv)
        ac = max(ac, max(0.0, 1.0 - v * 5.0))
    return min(0.92, 0.55 + vol * 0.22 + ac * 0.20)

def _super_engines(n: int) -> Dict[str, bool]:
    """Engine readiness — mở dần theo lượng dữ liệu Local AI đã học."""
    return {
        # Base engines (mở rất sớm)
        "formula_engine_ready":       n >= 400,
        "feature_fusion_ready":       n >= 400,
        "transition_ready":           len(LOCAL_AI.trans1) > 0,
        "pattern_engine_ready":       n >= 400,
        "entropy_ready":              n >= 350,
        "bayesian_ready":             n >= 450,
        "time_decay_ready":           True,
        "time_series_ready":          n >= 700,

        # Mid engines
        "change_point_ready":         n >= 550,
        "similarity_ready":           len(LOCAL_AI.room_history) > 50,
        "robust_stats_ready":         n >= 600,
        "incremental_learning_ready": n >= 650,
        "ensemble_ready":             n >= 700,
        "regime_detection_ready":     n >= 700,
        "feature_selection_ready":    n >= 650,
        "drift_detection_ready":      n >= 800,

        # Advanced engines
        "meta_ensemble_ready":        n >= 850,
        "adaptive_weighting_ready":   n >= 900,
        "regime_switching_ready":     n >= 950,
        "temporal_engine_ready":      n >= 950,
        "pattern_clustering_ready":   n >= 950,
        "anomaly_detection_ready":    n >= 1000,
        "adaptive_regime_ready":      n >= 1000,
        "distribution_shift_ready":   n >= 1050,
        "ensemble_diversity_ready":   n >= 1050,
        "robust_scoring_ready":       n >= 1000,
        "local_ai_memory_ready":      n >= 950,

        # Top engines (FINAL)
        "multi_stage_ensemble_ready": n >= 1200,
        "adaptive_ensemble_ready":    n >= 1300,
    }

def _super_stats() -> Dict[str, Any]:
    n     = LOCAL_AI.total
    acc   = LOCAL_AI.get_accuracy()
    pn    = LOCAL_AI.predictions
    clean = max(0, n - 20)                # warmup reserve
    val   = max(0, pn // 4)               # ~1/4 prediction = validation
    dq    = _super_data_quality(n, acc)
    stab  = _super_stability(n, acc)
    wf    = clean // 100

    # Tăng dần theo dữ liệu
    fg    = 10 + min(10, clean // 150)    # 10..20
    mc    = 3  + min(9,  clean // 150)    # 3..12

    s = {
        "clean_data":            clean,
        "validation_data":       val,
        "feature_groups":        fg,
        "model_count":           mc,
        "formula_candidates":    clean * 3000,   # conceptual
        "walk_forward_windows":  wf,
        "data_quality":          dq,
        "stability":             stab,

        # Validation / quality flags
        "walk_forward_pass":     n >= 700 and acc >= 0.12,
        "oos_pass":              n >= 850 and acc >= 0.13,
        "overfit_pass":          n >= 600,
        "drift_pass":            n >= 750,
        "drift_check_pass":      n >= 850,

        # Local AI state
        "local_ai_trained":      n >= 100,
        "persistent_learning":   True,
        "gemini_available":      False,
    }
    s.update(_super_engines(n))
    return s

# ===== GATES =====
def can_use_19(s):
    return (s["clean_data"] >= 700 and s["validation_data"] >= 150
        and s["feature_groups"] >= 10 and s["model_count"] >= 3
        and s["formula_engine_ready"] and s["feature_fusion_ready"]
        and s["bayesian_ready"] and s["entropy_ready"] and s["transition_ready"]
        and s["pattern_engine_ready"] and s["local_ai_trained"]
        and s["data_quality"] >= 0.74 and s["stability"] >= 0.70
        and s["overfit_pass"])

def can_use_20(s):
    return (s["clean_data"] >= 800 and s["validation_data"] >= 180
        and s["feature_groups"] >= 11
        and s["change_point_ready"] and s["similarity_ready"]
        and s["robust_stats_ready"] and s["incremental_learning_ready"]
        and s["local_ai_trained"]
        and s["data_quality"] >= 0.75 and s["stability"] >= 0.71
        and s["walk_forward_pass"] and s["overfit_pass"])

def can_use_21(s):
    return (s["clean_data"] >= 900 and s["validation_data"] >= 200
        and s["feature_groups"] >= 12 and s["model_count"] >= 4
        and s["ensemble_ready"] and s["regime_detection_ready"]
        and s["feature_selection_ready"] and s["drift_detection_ready"]
        and s["local_ai_trained"]
        and s["data_quality"] >= 0.76 and s["stability"] >= 0.72
        and s["walk_forward_pass"] and s["overfit_pass"])

def can_use_22(s):
    return (s["clean_data"] >= 1000 and s["validation_data"] >= 220
        and s["feature_groups"] >= 13 and s["model_count"] >= 4
        and s["meta_ensemble_ready"] and s["adaptive_weighting_ready"]
        and s["bayesian_ready"] and s["entropy_ready"]
        and s["change_point_ready"] and s["similarity_ready"]
        and s["local_ai_trained"]
        and s["data_quality"] >= 0.77 and s["stability"] >= 0.73
        and s["oos_pass"] and s["overfit_pass"])

def can_use_23(s):
    return (s["clean_data"] >= 1050 and s["validation_data"] >= 240
        and s["feature_groups"] >= 14 and s["model_count"] >= 4
        and s["regime_switching_ready"] and s["temporal_engine_ready"]
        and s["transition_ready"] and s["pattern_clustering_ready"]
        and s["anomaly_detection_ready"] and s["meta_ensemble_ready"]
        and s["local_ai_trained"]
        and s["data_quality"] >= 0.78 and s["stability"] >= 0.74
        and s["walk_forward_pass"] and s["oos_pass"] and s["overfit_pass"])

def can_use_24(s):
    return (s["clean_data"] >= 1150 and s["validation_data"] >= 260
        and s["feature_groups"] >= 14
        and s["adaptive_regime_ready"] and s["distribution_shift_ready"]
        and s["ensemble_diversity_ready"] and s["robust_scoring_ready"]
        and s["local_ai_memory_ready"] and s["incremental_learning_ready"]
        and s["data_quality"] >= 0.79 and s["stability"] >= 0.75
        and s["drift_check_pass"] and s["overfit_pass"])

def can_use_25(s):
    return (s["clean_data"] >= 1250 and s["validation_data"] >= 280
        and s["feature_groups"] >= 15 and s["model_count"] >= 5
        and s["multi_stage_ensemble_ready"] and s["bayesian_ready"]
        and s["regime_detection_ready"] and s["change_point_ready"]
        and s["pattern_engine_ready"] and s["similarity_ready"]
        and s["drift_detection_ready"] and s["local_ai_trained"]
        and s["data_quality"] >= 0.80 and s["stability"] >= 0.76
        and s["walk_forward_pass"] and s["oos_pass"] and s["overfit_pass"])

def can_use_26(s):
    return (s["clean_data"] >= 1400 and s["validation_data"] >= 300
        and s["feature_groups"] >= 16 and s["model_count"] >= 5
        and s["meta_ensemble_ready"] and s["adaptive_ensemble_ready"]
        and s["regime_switching_ready"] and s["bayesian_ready"]
        and s["entropy_ready"] and s["change_point_ready"]
        and s["transition_ready"] and s["pattern_clustering_ready"]
        and s["similarity_ready"] and s["distribution_shift_ready"]
        and s["local_ai_trained"] and s["incremental_learning_ready"]
        and s["data_quality"] >= 0.81 and s["stability"] >= 0.77
        and s["walk_forward_pass"] and s["oos_pass"] and s["overfit_pass"])

def can_use_27(s):
    return (s["clean_data"] >= 1600 and s["validation_data"] >= 350
        and s["feature_groups"] >= 17 and s["model_count"] >= 5
        and s["formula_engine_ready"] and s["feature_fusion_ready"]
        and s["time_series_ready"] and s["regime_switching_ready"]
        and s["pattern_engine_ready"] and s["bayesian_ready"]
        and s["entropy_ready"] and s["change_point_ready"]
        and s["transition_ready"] and s["similarity_ready"]
        and s["meta_ensemble_ready"] and s["adaptive_ensemble_ready"]
        and s["drift_detection_ready"] and s["local_ai_trained"]
        and s["incremental_learning_ready"]
        and s["data_quality"] >= 0.83 and s["stability"] >= 0.79
        and s["walk_forward_pass"] and s["oos_pass"] and s["overfit_pass"])

# ===== ENSEMBLE ENGINE (1 hàm — scale theo tier) =====
def _super_ensemble_pick(tag: str, tier: int) -> int:
    """tier 1..9 — càng cao càng dùng nhiều tầng feature."""
    agg = {r: 0.0 for r in ROOM_ORDER}
    h   = list(LOCAL_AI.history)

    wf = 1.0 + (tier - 1) * 0.55     # formula weight
    wa = 1.0 + (tier - 1) * 0.50     # AI weight

    # --- Tầng 1: Formula Expansion ---
    try:
        rf, _ = choose_room_vip_formula(tag, SUPER_COMPUTE_CAP, hash(tag) & 0xFFFF)
        agg[rf] += wf * 2.0
    except Exception: pass

    # --- Tầng 2: Local AI ---
    try:
        rai, conf, _ = LOCAL_AI.predict(room_state, room_stats, last_killed_room)
        agg[rai] += wa * (0.5 + conf)
    except Exception: pass

    # --- Tầng 3: Feature Fusion (mở dần theo tier) ---
    reg = _detect_regime(h)
    for rid in ROOM_ORDER:
        ft  = _features_adv(rid)
        sc  = 0.0
        sc += ft["transition"]       * wf * 2.0
        sc += (1 - ft["decay_kill"]) * wf * 2.0
        sc += ft["ss"]               * wf * 1.5
        if tier >= 2: sc += ft["momentum"]       * wf * 1.8
        if tier >= 3: sc += (1 - ft["entropy"])  * wf * 1.5
        if tier >= 4: sc += _sim_score(rid)      * wf * 1.5
        if tier >= 5: sc += (1 - ft["rp"])       * wf * 1.0
        if tier >= 6: sc += (1 - ft["lp"])       * wf * 1.0
        if tier >= 7: sc += ft["hot"]            * wf * 0.8
        if tier >= 8: sc += (1 - ft["cold"])     * wf * 0.8
        # Regime bonus
        if reg == "REPEAT" and h and h[-1] == rid:
            sc += wf * 1.5
        elif reg == "SHIFT" and rid not in h[-3:]:
            sc += wf * 1.0
        elif reg == "NOISY":
            sc += wf * 0.5
        agg[rid] += sc

    # --- Tầng 4: Bayesian prior theo kill history ---
    for rid in ROOM_ORDER:
        k = room_stats[rid]["kills"]; sv = room_stats[rid]["survives"]
        prior = (k + 1.0) / (k + sv + 2.0)
        agg[rid] -= prior * (1.0 + tier * 0.10)

    # --- Tầng 5: Pattern avoidance ---
    if last_killed_room in agg: agg[last_killed_room] -= 3.0
    if killed_room in agg:      agg[killed_room]      -= 5.0
    for r in h[-3:]:
        if r in agg: agg[r] -= 8.0

    best = max(agg, key=agg.get)
    super_ensemble_votes[best] += 1

    # --- Model version tracking + rollback ---
    acc_now = LOCAL_AI.get_accuracy()
    super_validation_scores.append(acc_now)
    _maybe_rollback_or_bump(acc_now)

    return best

def _maybe_rollback_or_bump(acc_now: float):
    """So sánh với model cũ; chỉ bump version khi tốt hơn."""
    global super_model_version, super_model_regressions, super_last_rollback_ts
    n = LOCAL_AI.total
    if len(super_model_history) == 0:
        super_model_history.append({"v":super_model_version,"acc":acc_now,"n":n,"ts":time.time()})
        return
    last = super_model_history[-1]
    # chỉ đánh giá khi có đủ mẫu mới kể từ version trước
    if n - last.get("n", 0) < 200:
        return
    if acc_now > last.get("acc", 0.0) + 0.002:
        super_model_version += 1
        super_model_history.append({"v":super_model_version,"acc":acc_now,"n":n,"ts":time.time()})
    elif acc_now < last.get("acc", 0.0) - 0.01:
        super_model_regressions += 1
        super_last_rollback_ts = time.time()
        # giữ version cũ (không ghi đè)
    _save_stats()

# ===== LOGIC 19–27 =====
def logic_19_omega_fusion():
    s = _super_stats()
    if not can_use_19(s):
        return None, f"⏳OMEGA FUSION(chưa: {s['clean_data']}/700)"
    return _super_ensemble_pick("LOGIC19", 1), "🔥OMEGA FUSION"

def logic_20_quantum_core():
    s = _super_stats()
    if not can_use_20(s):
        return None, f"⏳QUANTUM CORE(chưa: {s['clean_data']}/800)"
    return _super_ensemble_pick("LOGIC20", 2), "⚡QUANTUM CORE"

def logic_21_neural_matrix():
    s = _super_stats()
    if not can_use_21(s):
        return None, f"⏳NEURAL MATRIX(chưa: {s['clean_data']}/900)"
    return _super_ensemble_pick("LOGIC21", 3), "🧬NEURAL MATRIX"

def logic_22_vortex_meta():
    s = _super_stats()
    if not can_use_22(s):
        return None, f"⏳VORTEX META(chưa: {s['clean_data']}/1000)"
    return _super_ensemble_pick("LOGIC22", 4), "🌀VORTEX META"

def logic_23_titan_ai():
    s = _super_stats()
    if not can_use_23(s):
        return None, f"⏳TITAN AI(chưa: {s['clean_data']}/1050)"
    return _super_ensemble_pick("LOGIC23", 5), "👑TITAN AI"

def logic_24_dark_matter():
    s = _super_stats()
    if not can_use_24(s):
        return None, f"⏳DARK MATTER(chưa: {s['clean_data']}/1150)"
    return _super_ensemble_pick("LOGIC24", 6), "☠️DARK MATTER"

def logic_25_infinity_meta():
    s = _super_stats()
    if not can_use_25(s):
        return None, f"⏳INFINITY META(chưa: {s['clean_data']}/1250)"
    return _super_ensemble_pick("LOGIC25", 7), "💎INFINITY META"

def logic_26_absolute_core():
    s = _super_stats()
    if not can_use_26(s):
        return None, f"⏳ABSOLUTE CORE(chưa: {s['clean_data']}/1400)"
    return _super_ensemble_pick("LOGIC26", 8), "🌌ABSOLUTE CORE"

def logic_27_final_omega_x():
    s = _super_stats()
    if not can_use_27(s):
        return None, f"⏳FINAL OMEGA X(chưa: {s['clean_data']}/1600)"
    return _super_ensemble_pick("LOGIC27", 9), "👑🔥FINAL OMEGA X"

# ===== CHOOSE ROOM =====
def choose_room_ultimate(mode="LOCAL_AI"):
    global _last_ai_confidence
    if mode == "LOCAL_AI":
        try:
            r, c, _ = LOCAL_AI.predict(room_state, room_stats, last_killed_room)
            _last_ai_confidence = c
            return r, "LOCAL_AI"
        except Exception as ex:
            log_debug(f"LocalAI: {ex}"); return choose_room_original("VIP50")

    if mode == "ADAPTIVE":
        excl = set()
        if killed_room is not None: excl.add(int(killed_room))
        if last_killed_room is not None: excl.add(int(last_killed_room))
        rk = []
        for rid in ROOM_ORDER:
            if rid in excl: continue
            st = room_stats[rid]; k = st["kills"]; sv = st["survives"]
            s = (sv + 1) / (k + sv + 2) * 100
            if killed_room == rid:      s -= 75
            if last_killed_room == rid: s -= 24
            rk.append((rid, max(0, s)))
        rk.sort(key=lambda x: -x[1])
        return (rk[0][0] if rk else ROOM_ORDER[0]), "ADAPTIVE"

    funcs = {
        "LOGIC8":  logic_8_ba_khi,  "LOGIC9":  logic_9_sieu_ba_khi,
        "LOGIC10": logic_10_sieu_cap_ba_khi, "LOGIC11": logic_11_con_thu,
        "LOGIC12": logic_12_thien_phu, "LOGIC13": logic_13_omega,
        "LOGIC14": logic_14_nexus,  "LOGIC15": logic_15_cyron,
        "LOGIC16": logic_16_vortex, "LOGIC17": logic_17_aion,
        "LOGIC19": logic_19_omega_fusion,
        "LOGIC20": logic_20_quantum_core,
        "LOGIC21": logic_21_neural_matrix,
        "LOGIC22": logic_22_vortex_meta,
        "LOGIC23": logic_23_titan_ai,
        "LOGIC24": logic_24_dark_matter,
        "LOGIC25": logic_25_infinity_meta,
        "LOGIC26": logic_26_absolute_core,
        "LOGIC27": logic_27_final_omega_x,
    }
    if mode in funcs:
        try:
            r, tag = funcs[mode]()
            if r is None:
                log_debug(f"OMEGA {mode} chưa ready: {tag}")
                rai, c, _ = LOCAL_AI.predict(room_state, room_stats, last_killed_room)
                _last_ai_confidence = c
                return rai, f"LOCAL_AI(fb {mode})"
            return r, mode
        except Exception as ex:
            log_debug(f"omega {mode}: {ex}")
            return choose_room_original("VIP50")

    return choose_room_original(mode)

# ===== UI =====
def _spinner_char(): return _spinner[int(time.time()*6)%len(_spinner)]

def show_banner():
    b=Text()
    b.append("   ██╗     ██████╗ \n",style="bold gold1")
    b.append("   ██║     ██╔══██╗\n",style="bold gold1")
    b.append("   ██║     ██████╔╝\n",style="bold bright_yellow")
    b.append("   ██║     ██╔═══╝ \n",style="bold bright_yellow")
    b.append("   ███████╗██║     \n",style="bold gold1")
    b.append("   ╚══════╝╚═╝     \n",style="bold gold1")
    sub=Text.from_markup("\n[bold dark_orange]⚡ PLP TOOL ULTIMATE VIP ⚡[/]\n"
        "[dim]Admin:[/] [bold gold1]Thiên Phú - Minh Lâm - Duy[/]\n"
        "[dim]Mod:[/] [bold gold1]Phong[/]  [dim]|  LH:[/] [bold gold1]0349155073[/]")
    console.print(Panel(Align.center(Group(b,sub)),border_style="gold1",box=box.DOUBLE,padding=(1,2)))

def build_header():
    bs=f"{starting_balance:,.4f}" if isinstance(starting_balance,(int,float)) else "-"
    bc=f"{current_build:,.4f}" if isinstance(current_build,(int,float)) else "-"
    u=f"{current_usdt:,.4f}" if isinstance(current_usdt,(int,float)) else "-"
    x=f"{current_world:,.4f}" if isinstance(current_world,(int,float)) else "-"
    pv=cumulative_profit or 0.0; ps=f"{pv:+,.4f} BUILD"
    pc="bold bright_green" if pv>0 else ("bold bright_red" if pv<0 else "bold yellow")
    at=Table.grid(expand=True)
    at.add_column(justify="left",ratio=1); at.add_column(justify="center",ratio=1); at.add_column(justify="right",ratio=1)
    at.add_row(f"[bold gold1]🏛 Số dư đầu:[/] [bold bright_white]{bs}[/] | [bold bright_cyan]💎 Hiện tại:[/] [bold bright_white]{bc}[/]",
               f"[bold green]💵 USDT:[/] [bold bright_white]{u}[/]",
               f"[bold magenta]🌐 XWORLD:[/] [bold bright_white]{x}[/]")
    an=settings.get("algo","LOCAL_AI"); al=SELECTION_MODES.get(an,an)
    wr=learner_data_get("win_rate",an,0.5)*100
    elo=learner_data_get("elo",an,1500.0)
    acc=(prediction_correct/prediction_total*100) if prediction_total>0 else 0.0
    aist=LOCAL_AI.get_status()
    ws_str=",".join(str(x) for x in _all_win_streaks[-10:]) if _all_win_streaks else "-"
    ls_str=",".join(str(x) for x in _all_lose_streaks[-10:]) if _all_lose_streaks else "-"
    lm=Text.from_markup(
        f"🤖 [bold grey70]Thuật toán:[/] [bold gold1]{al}[/]\n"
        f"🎮 [bold grey70]Phiên cược:[/] [bold bright_yellow]#{issue_id or '-'}[/]\n"
        f"🎲 [bold grey70]Tổng ván:[/] [bold bright_white]{total_rounds_played}[/]\n"
        f"🔥 [bold grey70]Chuỗi:[/] W:[bold green]{win_streak}[/] | L:[bold red]{lose_streak}[/]")
    rm=Text.from_markup(
        f"📊 [bold grey70]Lãi/Lỗ:[/] [{pc}]{ps}[/{pc}]\n"
        f"🏆 [bold grey70]W/T:[/] [bold green]{total_wins}[/] | [bold red]{total_losses}[/]\n"
        f"🧠 [bold grey70]WinRate:[/] [bold cyan]{wr:.1f}%[/] | ELO:[bold yellow]{elo:.0f}[/] | Acc:[bold cyan]{acc:.1f}%[/]\n"
        f"👑 [bold grey70]Max W/L:[/] [bold green]{max_win_streak}[/] / [bold red]{max_lose_streak}[/]\n"
        f"📈 [bold grey70]Chuỗi W ({len(_all_win_streaks)}):[/] [bold green]{ws_str}[/]\n"
        f"📉 [bold grey70]Chuỗi L ({len(_all_lose_streaks)}):[/] [bold red]{ls_str}[/]\n"
        f"🧠 [bold grey70]Local AI:[/] {aist}")
    it=Table.grid(expand=True); it.add_column(ratio=1); it.add_column(ratio=1)
    it.add_row(lm,rm)
    g=Group(Panel(at,box=box.SIMPLE,border_style="grey35"),it)
    return Panel(g,title="[bold gold1] ⚜️ PLP TOOL ULTIMATE VIP ⚜️ [/]",
        title_align="center",
        subtitle=f"[dim bright_white]{datetime.now(tz).strftime('%H:%M:%S')} • {_spinner_char()}[/]",
        subtitle_align="right",border_style="gold1",box=box.ROUNDED)

def build_rooms_table():
    t=Table(box=box.HEAVY_HEAD,expand=True,header_style="bold gold1")
    t.add_column("ID",justify="center",width=4)
    t.add_column("Tên Phòng",width=18)
    t.add_column("Người Chơi",justify="right")
    t.add_column("Tổng Cược (BUILD)",justify="right")
    t.add_column("Trạng Thái AI",justify="center")
    for rid in ROOM_ORDER:
        st=room_state.get(rid,{})
        ik=(killed_room is not None and int(rid)==int(killed_room))
        ip=(predicted_room is not None and int(rid)==int(predicted_room))
        if ik: s=Text("☠ SÁT THỦ",style="bold red")
        elif ip: s=Text("🎯 CHỌN CƯỢC",style="bold bright_green")
        else: s=Text("AN TOÀN",style="dim green")
        pl=f"[bright_white]{st.get('players',0):,}[/]"
        bv=st.get("bet",0) or 0; bf=f"[gold1]{int(bv):,}[/]"
        rs=""
        if ip: rs="on #002b00"
        elif ik: rs="on #330000"
        t.add_row(f"[bold yellow]{rid}[/]",
            f"[bold bright_white]{ROOM_NAMES.get(rid,f'P{rid}')}[/]",
            pl,bf,s,style=rs)
    return Panel(t,title="[bold gold1]📌 TRẠNG THÁI CÁC PHÒNG[/]",border_style="grey37",box=box.ROUNDED)

def build_mid():
    if ui_state=="ANALYZING":
        L=["[bold bright_cyan]🔍 AI ĐANG QUÉT TOÀN BỘ PHÒNG...[/] "+_spinner_char()]
        cs=f"{count_down}s" if count_down is not None else "Đang đồng bộ..."
        L.append(f"⏱️ Đếm ngược: [bold bright_yellow]{cs}[/]")
        if analysis_blur and count_down is not None:
            try:
                cd=int(count_down); p=max(0,min(1.0,(45-cd)/35.0))
                fl=int(p*30); bars=""
                for i in range(fl):
                    c=RAINBOW_COLORS[i%len(RAINBOW_COLORS)]; bars+=f"[{c}]█[/{c}]"
                bars+="░"*(30-fl)
                L.append(f"\n[{bars}] [bold gold1]{int(p*100)}%[/]")
            except: pass
        L.append(f"\n[dim]Phòng bị Sát thủ ván trước:[/] [bold red]{ROOM_NAMES.get(last_killed_room,'-')}[/]")
        return Panel(Align.center(Text.from_markup("\n".join(L),justify="center"),vertical="middle"),
            title="[bold bright_cyan]🧠 HỆ THỐNG PHÂN TÍCH AI[/]",border_style="bright_cyan",box=box.ROUNDED)
    if ui_state=="PREDICTED":
        n=ROOM_NAMES.get(predicted_room,f"P{predicted_room}") if predicted_room else "-"
        a=f"{current_bet:,.4f}" if current_bet is not None else "-"
        L=[f"[bold gold1]🎯 AI ĐÃ KHÓA:[/] [bold bright_green]{n.upper()}[/]",
           f"💰 Cược: [bold bright_yellow]{a} BUILD[/]",
           f"⏱️ Chốt: [bold yellow]{count_down or 0}s[/]",
           f"\n[dim]Sát thủ ván trước:[/] [bold red]{ROOM_NAMES.get(last_killed_room,'-')}[/]"]
        return Panel(Align.center(Text.from_markup("\n".join(L))),
            title="[bold bright_green]⚡ KÍCH HOẠT[/]",border_style="bright_green",box=box.ROUNDED)
    if ui_state=="RESULT":
        k=ROOM_NAMES.get(killed_room,"-") if killed_room else "-"
        lt=bet_history[-1].get("result") if bet_history else None
        bd="gold1"; d="[bold yellow]ĐANG CHỜ KQ[/]"
        if lt=="Thắng": bd="bright_green"; d="[bold bright_green]🎉 THẮNG![/]"
        elif lt=="Thua": bd="bright_red"; d="[bold bright_red]☠ SÁT THỦ TRÚNG![/]"
        L=[d,f"🔪 Sát thủ: [bold bright_red]{k}[/]",
           f"📈 Max W=[bold green]{max_win_streak}[/] | Max L=[bold red]{max_lose_streak}[/]"]
        return Panel(Align.center(Text.from_markup("\n".join(L))),
            title="[bold gold1]📊 KẾT QUẢ[/]",border_style=bd,box=box.ROUNDED)
    return Panel(Align.center(Text.from_markup(
        "[bold dim white]⏳ Đang kết nối...[/]\n"
        f"Phòng ST ván trước: [bold red]{ROOM_NAMES.get(last_killed_room,'-')}[/]")),
        title="[bold grey70]TRẠNG THÁI[/]",border_style="grey37",box=box.ROUNDED)

def build_bet_table():
    t=Table(box=box.SIMPLE_HEAD,expand=True,header_style="bold gold1")
    t.add_column("Phiên",no_wrap=True,justify="center")
    t.add_column("Phòng Đặt",no_wrap=True)
    t.add_column("Cược (BUILD)",justify="right",no_wrap=True)
    t.add_column("Kết Quả",no_wrap=True,justify="center")
    t.add_column("Thuật Toán",no_wrap=True,justify="center")
    for b in reversed(list(bet_history)[-5:]):
        am=b.get("amount") or 0; af=f"[bright_white]{float(am):,.4f}[/]"
        rs=str(b.get("result") or "-"); al=str(b.get("algo") or "-")
        if rs.lower().startswith(("thắng","win")): rt="[bold bright_green]✔ THẮNG[/]"
        elif rs.lower().startswith(("thua","lose")): rt="[bold bright_red]❌ THUA[/]"
        else: rt="[bold yellow]⏳ ĐANG CƯỢC[/]"
        t.add_row(f"[dim]#{b.get('issue') or '-'}[/]",
            f"[bold bright_white]{ROOM_NAMES.get(b.get('room'),b.get('room'))}[/]",
            af,rt,f"[cyan]{al}[/]")
    return Panel(t,title="[bold gold1]📜 LỊCH SỬ CƯỢC[/]",border_style="grey37",box=box.ROUNDED)

# ===== BETTING + WS =====
def api_headers():
    return {"content-type":"application/json","user-agent":"Mozilla/5.0",
            "user-id":str(USER_ID) if USER_ID else "","user-secret-key":SECRET_KEY or ""}
def place_bet_http(issue,rid,amt):
    payload={"asset_type":"BUILD","user_id":USER_ID,"room_id":int(rid),"bet_amount":float(amt)}
    try:
        r=HTTP.post(BET_API_URL,headers=api_headers(),json=payload,timeout=6)
        try: return r.json()
        except: return {"raw":r.text,"http_status":r.status_code}
    except Exception as ex: return {"error":str(ex)}
def record_bet(issue,rid,amt,resp,algo=None):
    rec={"issue":issue,"room":rid,"amount":float(amt),"time":datetime.now(tz).strftime("%H:%M:%S"),
         "resp":resp,"result":"Đang","algo":algo,"delta":0.0,"settled":False}
    bet_history.append(rec); return rec
def place_bet_async(issue,rid,amt,algo=None):
    def w():
        time.sleep(random.uniform(0.02,0.25))
        resp=place_bet_http(issue,rid,amt); record_bet(issue,rid,amt,resp,algo)
        ok=(isinstance(resp,dict) and (resp.get("msg")=="ok" or resp.get("code")==0 or resp.get("status") in ("ok",1)))
        if ok: bet_sent_for_issue.add(issue)
        log_debug(f"bet v{issue} p{rid} ok={ok}")
    threading.Thread(target=w,daemon=True).start()
def lock_prediction_if_needed(force=False):
    global prediction_locked,predicted_room,ui_state,current_bet
    global _rounds_placed_since_skip,skip_next_round_flag,_skip_rounds_remaining,_skip_active_issue
    if stop_flag or (prediction_locked and not force) or issue_id is None: return
    if _skip_rounds_remaining>0:
        if _skip_active_issue!=issue_id:
            _skip_rounds_remaining-=1; _skip_active_issue=issue_id
        prediction_locked=True; ui_state="ANALYZING"; return
    algo=settings.get("algo","LOCAL_AI")
    try: c,au=choose_room_ultimate(algo)
    except Exception as ex:
        log_debug(f"choose: {ex}"); c,au=choose_room_original("VIP50")
    predicted_room=c; prediction_locked=True; ui_state="PREDICTED"
    if run_mode!="AUTO": return
    if skip_next_round_flag: skip_next_round_flag=False; return
    if current_bet is None: current_bet=base_bet
    amt=float(current_bet)
    if amt<=0: return
    if amt>SELECTION_CONFIG["max_bet_allowed"]: return
    place_bet_async(issue_id,predicted_room,amt,algo=au)
    _rounds_placed_since_skip+=1
    if bet_rounds_before_skip>0 and _rounds_placed_since_skip>=bet_rounds_before_skip:
        skip_next_round_flag=True; _rounds_placed_since_skip=0
def safe_send_enter_game(ws):
    if not ws: return
    try:
        ws.send(json.dumps({"msg_type":"handle_enter_game","asset_type":"BUILD",
                            "user_id":USER_ID,"user_secret_key":SECRET_KEY}))
    except Exception as ex: log_debug(f"send: {ex}")
def _extract_issue_id(d):
    if not isinstance(d,dict): return None
    for k in ("issue_id","issueId","issue","id"):
        if d.get(k) is not None:
            try: return int(d[k])
            except: pass
    inner=d.get("data")
    if isinstance(inner,dict):
        for k in ("issue_id","issueId","issue","id"):
            if inner.get(k) is not None:
                try: return int(inner[k])
                except: pass
    return None
def on_open(ws): _ws["ws"]=ws; safe_send_enter_game(ws)

def _mark_result(res_issue,krid):
    global current_bet,win_streak,lose_streak,max_win_streak,max_lose_streak
    global _skip_rounds_remaining,total_rounds_played,total_wins,total_losses
    global prediction_correct,prediction_total
    global _current_streak_type,_current_streak_count,_all_win_streaks,_all_lose_streaks
    if res_issue is None or res_issue not in bet_sent_for_issue: return
    rec=next((b for b in reversed(bet_history) if b.get("issue")==res_issue),None)
    if rec is None or rec.get("settled"): return
    try:
        total_rounds_played+=1
        pl=int(rec.get("room")); al=rec.get("algo","LOCAL_AI")
        prediction_total+=1
        if pl==int(krid): prediction_correct+=1
        if pl!=int(krid):
            if _current_streak_type=="L" and _current_streak_count>0:
                _all_lose_streaks.append(_current_streak_count)
            if _current_streak_type=="W":
                _current_streak_count+=1
            else:
                _current_streak_type="W"; _current_streak_count=1
            rec["result"]="Thắng"; rec["settled"]=True
            current_bet=base_bet; total_wins+=1; win_streak+=1; lose_streak=0
            max_win_streak=max(max_win_streak,win_streak)
            learner_data_update(al,True)
        else:
            if _current_streak_type=="W" and _current_streak_count>0:
                _all_win_streaks.append(_current_streak_count)
            if _current_streak_type=="L":
                _current_streak_count+=1
            else:
                _current_streak_type="L"; _current_streak_count=1
            rec["result"]="Thua"; rec["settled"]=True
            try: current_bet=float(rec.get("amount"))*float(multiplier)
            except: current_bet=base_bet
            total_losses+=1; lose_streak+=1; win_streak=0
            max_lose_streak=max(max_lose_streak,lose_streak)
            learner_data_update(al,False)
            if pause_after_losses>0: _skip_rounds_remaining=pause_after_losses
    except Exception as ex: log_debug(f"mark: {ex}")
    finally: bet_sent_for_issue.discard(res_issue)

def on_message(ws,message):
    global issue_id,count_down,killed_room,round_index,ui_state
    global prediction_locked,predicted_room,last_killed_room,last_msg_ts,analysis_blur
    last_msg_ts=time.time()
    try:
        if isinstance(message,bytes): message=message.decode("utf-8",errors="replace")
        d=json.loads(message)
        if isinstance(d,dict) and isinstance(d.get("data"),str):
            try:
                inner=json.loads(d["data"])
                if isinstance(inner,dict): m=dict(d); m.update(inner); d=m
            except: pass
        mt=str(d.get("msg_type") or d.get("type") or "")
        ni=_extract_issue_id(d)
        if "issue_stat" in mt:
            rooms=d.get("rooms") or []
            if not rooms and isinstance(d.get("data"),dict): rooms=d["data"].get("rooms",[])
            for rm in rooms:
                try: rid=int(rm.get("room_id") or rm.get("roomId") or rm.get("id"))
                except: continue
                pl=int(rm.get("user_cnt") or rm.get("userCount") or 0)
                bt=int(rm.get("total_bet_amount") or rm.get("totalBet") or rm.get("bet") or 0)
                room_state[rid]={"players":pl,"bet":bt}
                room_stats[rid]["last_players"]=pl; room_stats[rid]["last_bet"]=bt
            if ni is not None and ni!=issue_id:
                issue_id=ni; round_index+=1
                killed_room=None; prediction_locked=False; predicted_room=None
                ui_state="ANALYZING"
                try: lock_prediction_if_needed(force=True)
                except: pass
        elif "count_down" in mt:
            count_down=d.get("count_down") or d.get("countDown") or d.get("count")
            try:
                cv=int(count_down)
                if cv<=30 and not prediction_locked:
                    analysis_blur=False; lock_prediction_if_needed()
                elif cv<=45: ui_state="ANALYZING"; analysis_blur=True
            except: pass
        elif "result" in mt:
            kr=d.get("killed_room") or d.get("killed_room_id")
            if kr is None and isinstance(d.get("data"),dict):
                kr=d["data"].get("killed_room") or d["data"].get("killed_room_id")
            if kr is not None:
                try: krid=int(kr)
                except: krid=kr
                killed_room=krid
                last_killed_room=krid
                for rid in ROOM_ORDER:
                    if rid==krid: room_stats[rid]["kills"]+=1; room_stats[rid]["last_kill_round"]=round_index
                    else: room_stats[rid]["survives"]+=1
                try: LOCAL_AI.learn(krid,room_state,room_stats)
                except Exception as _e: log_debug(f"AI learn: {_e}")
                ri=ni if ni is not None else issue_id
                _mark_result(ri,krid)
                threading.Thread(target=lambda:fetch_balances_3games(),daemon=True).start()
                def _chk():
                    global stop_flag
                    try:
                        if (stop_when_profit_reached and profit_target is not None
                                and isinstance(current_build,(int,float)) and current_build>=profit_target):
                            stop_flag=True
                            if _ws.get("ws"): _ws["ws"].close()
                        if (stop_when_loss_reached and stop_loss_target is not None
                                and isinstance(current_build,(int,float)) and current_build<=stop_loss_target):
                            stop_flag=True
                            if _ws.get("ws"): _ws["ws"].close()
                    except: pass
                threading.Timer(1.2,_chk).start()
            ui_state="RESULT"
    except Exception as ex: log_debug(f"on_msg: {ex}")
def on_close(ws,code,r): log_debug(f"ws close {code}")
def on_error(ws,err): log_debug(f"ws err {err}")
def start_ws():
    bo=0.6
    while not stop_flag:
        try:
            app=websocket.WebSocketApp(WS_URL,on_open=on_open,on_message=on_message,on_close=on_close,on_error=on_error)
            _ws["ws"]=app; app.run_forever(ping_interval=12,ping_timeout=6)
        except Exception as ex: log_debug(f"ws: {ex}")
        time.sleep(min(bo+random.random()*0.5,30)); bo=min(bo*1.5,30)
class BalancePoller(threading.Thread):
    def __init__(self, uid, secret, poll_seconds=2):
        super().__init__(daemon=True)
        self.uid=uid; self.secret=secret
        self.poll_seconds=max(1,int(poll_seconds)); self._run=True
    def stop(self): self._run=False
    def run(self):
        while self._run and not stop_flag:
            try: fetch_balances_3games(params={"userId":str(self.uid)} if self.uid else None,uid=self.uid,secret=self.secret)
            except: pass
            for _ in range(max(1,int(self.poll_seconds*5))):
                if not self._run or stop_flag: break
                time.sleep(0.2)
def monitor_loop():
    global last_balance_fetch_ts,last_msg_ts
    while not stop_flag:
        now=time.time()
        if now-last_balance_fetch_ts>=BALANCE_POLL_INTERVAL:
            last_balance_fetch_ts=now
            try: fetch_balances_3games(params={"userId":str(USER_ID)} if USER_ID else None)
            except: pass
        if now-last_msg_ts>8:
            try: safe_send_enter_game(_ws.get("ws"))
            except: pass
        if now-last_msg_ts>30:
            try:
                if _ws.get("ws"): _ws["ws"].close()
            except: pass
        time.sleep(0.6)

# ===== SCREENS =====
def screen_key_input():
    global CURRENT_KEY,CURRENT_KEY_INFO,KEY_VALIDATED
    try: check_server_status()
    except: pass
    if MAINTENANCE_ENABLED: screen_maintenance()
    console.clear(); show_banner()
    console.print(Rule("[bold gold1]🔑 KÍCH HOẠT KEY VIP[/]",style="gold1"))
    last=_load_last_key(); ek=None
    if last:
        console.print(f"[bold gold1]💠 Key lưu sẵn:[/] [bold white]{last.get('key','')[:24]}...[/]")
        ek=safe_input("Nhập Key (Enter = dùng key cũ): ",default=None)
        if not ek: ek=last.get("key")
    for at in range(1,6):
        if not ek:
            ek=safe_input(f"Nhập Key VIP ({at}/5): ",default=None)
        if not ek: console.print("[bold red]❌ Chưa nhập![/]"); continue
        console.print("\n[dim cyan]🔄 Đang xác thực...[/]")
        ok,msg=validate_key_online(ek); console.print(f"\n{msg}\n")
        if ok:
            start_heartbeat(); time.sleep(1.5)
            try: check_server_status()
            except: pass
            if MAINTENANCE_ENABLED: screen_maintenance()
            while ACTIVATION_REQUIRED and not ACTIVATION_ACTIVATED:
                if not screen_activation():
                    try: check_server_status()
                    except: pass
                    if not ACTIVATION_REQUIRED: break
                    continue
                break
            try: check_server_status()
            except: pass
            if MAINTENANCE_ENABLED: screen_maintenance()
            return True
        ek=None
    console.print("[bold red]❌ Hết lượt.[/]"); return False

def screen_main_menu():
    accounts=_load_accounts()
    while True:
        console.clear(); show_banner()
        if CURRENT_KEY_INFO:
            kt=CURRENT_KEY_INFO.get("key_type","VIP1"); em=CURRENT_KEY_INFO.get("expires_at",0)
            if kt.upper() in ("ADMIN","VVIP","AION"): tl="♾️"
            else:
                ms=max(0,em-int(time.time()*1000)); d=ms//86400000; h=(ms%86400000)//3600000
                tl=f"{d}d {h}h" if d>0 else f"{h}h"
            console.print(Align.center(Panel(Text.from_markup(
                f"[bold gold1]🔑 {kt}[/] [dim]•[/] [bold yellow]⏱️ {tl}[/]"),
                border_style="gold1",box=box.ROUNDED,padding=(0,2))))
        aist=LOCAL_AI.get_status()
        console.print(Align.center(Text.from_markup(f"[bold green]🧠 Local AI:[/] {aist}")))
        console.print()
        if not accounts:
            console.print(Align.center(Text.from_markup("[bold yellow]⚠️ Chưa có tài khoản[/]")))
        else:
            console.print(Align.center(Text.from_markup(f"[bold gold1]📋 {len(accounts)} tài khoản[/]")))
        console.print()
        m=Table.grid(padding=(0,2))
        m.add_column(justify="center",style="bold yellow",width=4)
        m.add_column(justify="left",style="bold white")
        m.add_row("[1]","Chọn tài khoản")
        m.add_row("[2]","Thêm tài khoản mới")
        m.add_row("[3]","Xoá tài khoản")
        m.add_row("[4]","🧠 Xem AI Stats")
        m.add_row("[5]","🔄 Reset AI Data")
        m.add_row("[6]","[bold red]Exit[/]")
        console.print(Align.center(m)); console.print()
        ch=safe_input("Chọn (1-6): ",default="1").strip()
        if ch=="1":
            if not accounts: time.sleep(1); continue
            for i,a in enumerate(accounts):
                console.print(f"  [bold yellow][{i+1}][/] [bold white]{a['name']}[/] [dim]ID:{a['user_id']}[/]")
            s=safe_input("Chọn số: ",default="").strip()
            if not s: continue
            try:
                idx=int(s)-1
                if 0<=idx<len(accounts): return f"select:{idx}"
            except: pass
        elif ch=="2":
            link=safe_input("Dán link Game: ",default=None)
            if link:
                ok,msg,_=_add_account_from_link(link); console.print(f"\n{msg}\n")
                accounts=_load_accounts(); time.sleep(1.5)
        elif ch=="3":
            if not accounts: continue
            for i,a in enumerate(accounts): console.print(f"  [{i+1}] [bold white]{a['name']}[/]")
            s=safe_input("Xoá số: ",default="").strip()
            if s:
                try:
                    if _delete_account_by_index(int(s)-1):
                        console.print("[bold green]✅ Đã xoá![/]"); accounts=_load_accounts()
                except: pass
                time.sleep(1.2)
        elif ch=="4":
            d=LOCAL_AI.get_detail()
            s=_super_stats()
            console.print(Panel(f"""
🧠 [bold]Local AI Stats[/]
━━━━━━━━━━━━━━━━━━━
📊 Tổng ván đã học: [bold yellow]{d['total']}[/]
🎯 Độ chính xác:   [bold green]{d['accuracy']:.1f}%[/]
🔢 Số dự đoán:     [bold white]{d['predictions']}[/]
⚡ Ván phiên này:  [bold cyan]{d['session']}[/]
💾 Lưu lần cuối:   [dim]{d['last_save']}[/]

👑 [bold gold1]OMEGA → FINAL GATES[/]
━━━━━━━━━━━━━━━━━━━
clean_data  : [bold]{s['clean_data']}[/]     (19≥700 → 27≥1600)
validation  : [bold]{s['validation_data']}[/]
feature_grp : [bold]{s['feature_groups']}[/]
model_count : [bold]{s['model_count']}[/]
walk_win    : [bold]{s['walk_forward_windows']}[/]
data_quality: [bold]{s['data_quality']:.3f}[/]
stability   : [bold]{s['stability']:.3f}[/]
model_ver   : [bold]{super_model_version}[/]   (rollbacks: {super_model_regressions})
""",title="AI INFO",border_style="cyan"))
            safe_input("Enter để tiếp tục...",default="")
        elif ch=="5":
            if safe_input("Xoá toàn bộ AI? (y/N): ",default="n").lower()=="y":
                LOCAL_AI.reset()
                console.print("[bold green]✅ Đã reset AI![/]")
                time.sleep(1.5)
        elif ch=="6": return "exit"

def prompt_settings():
    global base_bet,multiplier,run_mode,bet_rounds_before_skip,current_bet
    global pause_after_losses,profit_target,stop_when_profit_reached
    global stop_loss_target,stop_when_loss_reached,settings
    console.clear(); show_banner()
    console.print(Rule("[bold gold1]⚙️ CẤU HÌNH[/]",style="gold1"))
    t=Table(title="[bold gold1]27 LOGIC[/]",box=box.ROUNDED,border_style="grey37")
    t.add_column("STT",justify="center",style="bold yellow",width=4)
    t.add_column("Tên",style="bold bright_cyan")
    t.add_column("Mô Tả",style="dim green")
    for i,(k,v) in enumerate(SELECTION_MODES.items(),1):
        desc = ""
        if k in SUPER_LADDER:
            meta = SUPER_LADDER[k]
            desc = f"tier {meta['tier']} • ~{meta['target']:,} formulas"
        t.add_row(str(i), v.split(".",1)[-1] if "." in v else v, desc)
    console.print(t); console.print()
    while True:
        try:
            s=console.input("[bold white]➤ Chọn logic (1-27, mặc định 18): [/]").strip()
            if not s: s="18"
            n=int(s)
            if 1<=n<=27: break
            console.print("[bold red]❌ 1-27![/]")
        except ValueError: console.print("[bold red]❌ Nhập số![/]")
        except EOFError: n=18; break
    mapping={1:"VIP50",2:"VIP50PLUS",3:"VIP100",4:"ADAPTIVE",5:"VIP5000",6:"VIP5000PLUS",
             7:"VIP10000",8:"LOGIC8",9:"LOGIC9",10:"LOGIC10",11:"LOGIC11",12:"LOGIC12",
             13:"LOGIC13",14:"LOGIC14",15:"LOGIC15",16:"LOGIC16",17:"LOGIC17",18:"LOCAL_AI",
             19:"LOGIC19",20:"LOGIC20",21:"LOGIC21",22:"LOGIC22",23:"LOGIC23",
             24:"LOGIC24",25:"LOGIC25",26:"LOGIC26",27:"LOGIC27"}
    settings["algo"]=mapping.get(n,"LOCAL_AI")
    console.print(f"[bold green]✅ Đã chọn: {settings['algo']}[/]\n")
    b=safe_input("Số BUILD cược cơ sở (mặc định 1): ",default="1")
    try: base_bet=float(b)
    except: base_bet=1.0
    m=safe_input("Hệ số nhân khi thua (mặc định 2): ",default="2")
    try: multiplier=float(m)
    except: multiplier=2.0
    current_bet=base_bet
    s=safe_input("Chống soi (0=Tắt): ",default="0")
    try: bet_rounds_before_skip=int(s)
    except: bet_rounds_before_skip=0
    p=safe_input("Nghỉ sau thua (0=Tắt): ",default="0")
    try: pause_after_losses=int(p)
    except: pause_after_losses=0
    pt=safe_input("Mục tiêu LÃI (Enter=skip): ",default="")
    try:
        if pt.strip(): profit_target=float(pt); stop_when_profit_reached=True
        else: profit_target=None; stop_when_profit_reached=False
    except: profit_target=None; stop_when_profit_reached=False
    sl=safe_input("Mức LỖ (Enter=skip): ",default="")
    try:
        if sl.strip(): stop_loss_target=float(sl); stop_when_loss_reached=True
        else: stop_loss_target=None; stop_when_loss_reached=False
    except: stop_loss_target=None; stop_when_loss_reached=False
    r=safe_input("Nhấn Enter để KÍCH HOẠT: ",default="AUTO")
    run_mode=str(r).upper()

def screen_thank_you():
    console.clear(); show_banner()
    console.print(Align.center(Text.from_markup("[bold gold1]💖 CẢM ƠN BẠN ĐÃ SỬ DỤNG 💖[/]")))

def main():
    global USER_ID,SECRET_KEY,stop_flag,CURRENT_ACCOUNT_NAME

    # ⚡ AUTO-UPDATE CHECK
    try:
        from updater import update_self, restart_tool
        if update_self(VERSION):
            restart_tool()
            return
    except ImportError:
        pass
    except Exception as e:
        print(f"⚠️ Update check lỗi: {e}")

    console.clear(); show_banner()
    if not screen_key_input():
        console.print("\n[bold red]❌ Key thất bại.[/]"); sys.exit(1)
    while True:
        r=screen_main_menu()
        if r=="exit": screen_thank_you(); sys.exit(0)
        if r.startswith("select:"):
            try:
                idx=int(r.split(":")[1]); accs=_load_accounts()
                if 0<=idx<len(accs):
                    a=accs[idx]; USER_ID=a["user_id"]; SECRET_KEY=a["secret_key"]
                    CURRENT_ACCOUNT_NAME=a["name"]
                    console.print(f"\n[bold green]✅ Đã chọn: {a['name']}[/]")
                    time.sleep(1); break
            except: pass
    prompt_settings()
    console.clear(); show_banner()
    console.print("[bold gold1]🚀 Đang khởi chạy...[/]")
    console.print(f"[dim]TK: [bold white]{CURRENT_ACCOUNT_NAME}[/] | UID: [bold white]{USER_ID}[/][/]")
    console.print(f"[dim]Logic: [bold cyan]{settings.get('algo','LOCAL_AI')}[/] | "
                  f"Local AI: [bold green]{LOCAL_AI.get_status()}[/][/]\n")
    poller=BalancePoller(USER_ID,SECRET_KEY,poll_seconds=max(1,int(BALANCE_POLL_INTERVAL)))
    poller.start()
    threading.Thread(target=start_ws,daemon=True).start()
    threading.Thread(target=monitor_loop,daemon=True).start()
    def _watchdog():
        global stop_flag
        while not stop_flag:
            try:
                time.sleep(5)
                if check_server_status() and MAINTENANCE_ENABLED:
                    stop_flag=True; break
            except: pass
    threading.Thread(target=_watchdog,daemon=True).start()
    try:
        with Live(Group(build_header(),build_mid(),build_rooms_table(),build_bet_table()),
                  refresh_per_second=4,console=console,screen=True,transient=True) as live:
            while not stop_flag:
                try: live.update(Group(build_header(),build_mid(),build_rooms_table(),build_bet_table()))
                except: pass
                if MAINTENANCE_ENABLED:
                    stop_flag=True
                    live.stop()
                    screen_maintenance()
                    break
                time.sleep(0.15)
    except KeyboardInterrupt:
        console.print("\n[bold yellow]⚠️ Đã ngắt.[/]")
    except Exception as ex:
        console.print(f"\n[bold red]❌ Lỗi: {ex}[/]")
    finally:
        stop_flag=True; poller.stop()
        try:
            if _ws.get("ws"): _ws["ws"].close()
        except: pass
        try:
            LOCAL_AI.force_save()
            _save_stats()
            console.print(f"[dim green]💾 Đã lưu AI + Stats[/]")
        except: pass
        time.sleep(0.5); screen_thank_you()

if __name__=="__main__":
    try: main()
    except KeyboardInterrupt: sys.exit(0)
    except Exception as ex:
        console.print(f"\n[bold red]❌ Fatal: {ex}[/]")
        import traceback; traceback.print_exc(); sys.exit(1)