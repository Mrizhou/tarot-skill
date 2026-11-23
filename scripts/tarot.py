#!/usr/bin/env python3
"""塔罗牌：洗牌锁定（SHA-256）→ 抽牌 → 补牌 → 揭晓验证。只用标准库。

  python3 tarot.py new                                      洗牌锁定，打印会话号和哈希
  python3 tarot.py spreads                                  列出所有牌阵
  python3 tarot.py draw <会话号> --spread 时间之流 --question 问题 --pick 7,23,51 [--topic 感情]
  python3 tarot.py draw <会话号> --spread 时间之流 --question 问题 --top 3     从牌堆顶发牌
  python3 tarot.py clarify <会话号> --for 2 (--pick 33 | --next)             给第 2 个位置补一张
  python3 tarot.py reveal <会话号> [--expect 第1步的哈希]                    公开牌序并验证
  python3 tarot.py show <会话号>                             查看某次的哈希和状态
  python3 tarot.py list                                     列出历史会话

占卜记录默认存在 ~/.tarot/records，可用环境变量 TAROT_RECORDS_DIR 改到别处。
"""
import argparse
import hashlib
import json
import os
import re
import secrets
import sys
import tempfile
import unicodedata
from collections import Counter
from contextlib import contextmanager
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CARDS_FILE = ROOT / "assets" / "cards.json"
SPREADS_FILE = ROOT / "assets" / "spreads.json"
RECORDS_ENV = "TAROT_RECORDS_DIR"
DECK_SIZE = 78
COMMIT_VERSION = "tarot-commit-v1"
ORIENTATION = {"U": "正位", "R": "逆位"}
TOPICS = {"感情": "love", "事业": "career", "财运": "money"}
YES_NO_VALUES = {"是", "否", "看情况"}
SUIT_BY_PREFIX = {"W": "权杖", "C": "圣杯", "S": "宝剑", "P": "星币"}
NUMBER_NAMES = {1: "王牌", 2: "二", 3: "三", 4: "四", 5: "五", 6: "六", 7: "七", 8: "八", 9: "九", 10: "十"}
MAX_CLARIFIERS = 3
EXIT_MISMATCH = 3
TIME_FMT = "%Y-%m-%d %H:%M:%S"
SESSION_RE = re.compile(r"\d{8}-\d{6}-[0-9a-f]{4}", re.ASCII)
HEX64_RE = re.compile(r"[0-9a-f]{64}", re.ASCII)
CARD_ID_RE = re.compile(r"M(?:[01][0-9]|2[01])|[WCSP](?:0[1-9]|1[0-4])", re.ASCII)


class TarotError(Exception):
    """预期内的错误：打印一行提示，退出码 1。"""


def fail(msg):
    raise TarotError(msg)


def circled(k):
    return chr(0x2460 + k - 1) if 1 <= k <= 20 else f"({k})"


def configure_output():
    """输出编码跟随调用方。

    Windows 控制台按它当前的代码页输出（简体中文系统默认 936），否则调用方按 936 解码 UTF-8 会乱码；
    没有控制台（被 Git Bash 等以管道方式调用）或其他系统用 UTF-8。设置了 PYTHONIOENCODING 时尊重它。
    """
    if os.environ.get("PYTHONIOENCODING"):
        return
    encoding = "utf-8"
    if sys.platform == "win32":
        try:
            import codecs
            import ctypes
            code_page = ctypes.windll.kernel32.GetConsoleOutputCP()
            if code_page and code_page != 65001:
                encoding = codecs.lookup(f"cp{code_page}").name
        except (OSError, AttributeError, LookupError):
            pass
    for stream in (sys.stdout, sys.stderr):
        stream.reconfigure(encoding=encoding, errors="replace")


def read_json(path):
    # utf-8-sig：兼容被 Windows PowerShell 5.1 等工具加了 BOM 的文件
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


# ---------- 牌库与牌阵 ----------

def load_cards():
    try:
        cards = read_json(CARDS_FILE)
    except (OSError, ValueError) as e:
        fail(f"读不了牌库 {CARDS_FILE}：{e}")
    if not isinstance(cards, list):
        fail(f"{CARDS_FILE} 应该是一个列表")
    by_id = {}
    for index, card in enumerate(cards, start=1):
        cid = card.get("id") if isinstance(card, dict) else None
        if not isinstance(cid, str) or not CARD_ID_RE.fullmatch(cid):
            fail(f"{CARDS_FILE.name} 第 {index} 条的编号不对：{cid!r}")
        if cid in by_id:
            fail(f"{CARDS_FILE.name} 里编号重复：{cid}")
        for key in ("name_zh", "name_en", "arcana", "image"):
            if not isinstance(card.get(key), str) or not card[key]:
                fail(f"{cid} 缺少 {key}")
        for key in ("upright", "reversed"):
            words = card.get(key)
            if not isinstance(words, list) or not words or not all(isinstance(w, str) and w for w in words):
                fail(f"{cid} 的 {key} 应该是非空的关键词列表")
        for key in ("love", "career", "money", "yes_no"):
            pair = card.get(key)
            if not isinstance(pair, dict) or set(pair) != {"U", "R"} or not all(isinstance(v, str) and v for v in pair.values()):
                fail(f"{cid} 的 {key} 必须正好有 U 和 R 两项文字")
        if not set(card["yes_no"].values()) <= YES_NO_VALUES:
            fail(f"{cid} 的 yes_no 只能是 是 / 否 / 看情况")
        if card.get("suit") != SUIT_BY_PREFIX.get(cid[0]):
            fail(f"{cid} 的 suit 应该是 {SUIT_BY_PREFIX.get(cid[0])!r}")
        by_id[cid] = card
    if len(by_id) != DECK_SIZE:
        fail(f"{CARDS_FILE.name} 应有 {DECK_SIZE} 张牌，实际 {len(by_id)} 张")
    return by_id


def load_spreads():
    try:
        spreads = read_json(SPREADS_FILE)
    except (OSError, ValueError) as e:
        fail(f"读不了牌阵库 {SPREADS_FILE}：{e}")
    if not isinstance(spreads, list):
        fail(f"{SPREADS_FILE} 应该是一个列表")
    by_name = {}
    for spread in spreads:
        name = spread.get("name") if isinstance(spread, dict) else None
        if not isinstance(name, str) or not name:
            fail(f"{SPREADS_FILE.name} 里有牌阵没有名字")
        if name in by_name:
            fail(f"牌阵名重复：{name}")
        positions = spread.get("positions")
        if (not isinstance(positions, list) or not positions
                or not all(isinstance(p, list) and len(p) == 2 and all(isinstance(x, str) for x in p) and p[0]
                           for p in positions)):
            fail(f"牌阵「{name}」的 positions 每项应为 [位置名, 含义]")
        layout = spread.get("layout")
        if not isinstance(layout, list) or not all(isinstance(row, list) and all(type(i) is int for i in row) for row in layout):
            fail(f"牌阵「{name}」的 layout 应为整数网格")
        cells = sorted(i for row in layout for i in row if i)
        if cells != list(range(1, len(positions) + 1)):
            fail(f"牌阵「{name}」的 layout 和位置数对不上")
        by_name[name] = spread
    return by_name


def get_spread(name):
    spreads = load_spreads()
    if name not in spreads:
        fail(f"没有叫「{name}」的牌阵。可选：{'、'.join(spreads)}")
    return spreads[name]


def slot_names(spread, when):
    names = [p[0] for p in spread["positions"]]
    if spread.get("monthly"):  # 第 1 个位置是年度主题，后面 12 个换成从本月起的实际年月
        for i in range(1, len(names)):
            months = when.month - 1 + i - 1
            names[i] = f"{when.year + months // 12} 年 {months % 12 + 1} 月"
    return names


# ---------- 记录 ----------

def records_dir():
    custom = os.environ.get(RECORDS_ENV)
    return Path(custom).expanduser() if custom else Path.home() / ".tarot" / "records"


def record_path(session_id):
    if not SESSION_RE.fullmatch(session_id):
        fail(f"会话号格式不对：{session_id}")
    return records_dir() / f"{session_id}.json"


def check_record(record, session_id, path):
    tampered = f"，记录可能被改动过：{path}"
    if not isinstance(record, dict):
        fail(f"记录格式不对{tampered}")
    if record.get("session") != session_id:
        fail(f"记录里的会话号和文件名对不上{tampered}")
    if record.get("version") != COMMIT_VERSION:
        fail(f"不认识的记录版本 {record.get('version')!r}：{path}")
    for key in ("nonce", "sha256"):
        if not isinstance(record.get(key), str) or not HEX64_RE.fullmatch(record[key]):
            fail(f"记录里的 {key} 格式不对{tampered}")
    deck = record.get("deck")
    if not isinstance(deck, list) or len(deck) != DECK_SIZE or not all(isinstance(e, dict) for e in deck):
        fail(f"牌组不是 {DECK_SIZE} 张{tampered}")
    ids = [e.get("id") for e in deck]
    if not all(isinstance(i, str) and CARD_ID_RE.fullmatch(i) for i in ids) or len(set(ids)) != DECK_SIZE:
        fail(f"牌组不是一副完整、不重复的 {DECK_SIZE} 张牌{tampered}")
    if not all(e.get("o") in ORIENTATION and isinstance(e.get("name"), str) and e["name"] for e in deck):
        fail(f"牌组里有牌的正逆位或牌名不对{tampered}")


def load_record(session_id):
    path = record_path(session_id)
    if not path.exists():
        fail(f"找不到会话 {session_id}（{path}）")
    try:
        record = read_json(path)
    except ValueError as e:
        fail(f"记录文件损坏：{path}（{e}）")
    check_record(record, session_id, path)
    return record


def save_record(record, create=False):
    """create=True 时独占创建（会话号撞了抛 FileExistsError）；否则先写临时文件再替换，中途断掉也不会留下半个文件。"""
    directory = records_dir()
    directory.mkdir(parents=True, exist_ok=True)
    path = record_path(record["session"])
    data = json.dumps(record, ensure_ascii=False, indent=2).encode("utf-8")
    if create:
        with open(path, "xb") as f:
            f.write(data)
        return
    fd, tmp = tempfile.mkstemp(dir=str(directory), prefix=".tmp-", suffix=".part")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        os.replace(tmp, str(path))
    except BaseException:
        try:
            os.remove(tmp)
        except FileNotFoundError:
            pass
        raise


@contextmanager
def session_lock(session_id):
    """同一会话同一时间只允许一个 draw / clarify / reveal，防止两个操作同时写，互相覆盖。"""
    record_path(session_id)
    directory = records_dir()
    directory.mkdir(parents=True, exist_ok=True)
    lock = directory / f"{session_id}.lock"
    try:
        os.close(os.open(str(lock), os.O_CREAT | os.O_EXCL | os.O_WRONLY))
    except FileExistsError:
        fail(f"这个会话正在被另一个操作使用。确定没有的话，删掉 {lock} 再试")
    try:
        yield
    finally:
        try:
            os.remove(str(lock))
        except FileNotFoundError:
            pass


def preimage_bytes(record):
    """被哈希的原文。只由记录本身决定，改 cards.json 不影响已锁定的会话。"""
    lines = [record["version"], f"nonce={record['nonce']}"]
    for pos, entry in enumerate(record["deck"], start=1):
        lines.append(f"{pos:02d} {entry['o']} {entry['id']} {entry['name']}")
    return "\n".join(lines).encode("utf-8")


def status_of(record):
    if record.get("revealed_at"):
        return "已揭晓"
    if record.get("draw"):
        return "已抽牌"
    return "未抽牌"


def used_positions(record):
    draw = record.get("draw") or {}
    return {c["position"] for c in draw.get("cards", [])} | {c["position"] for c in draw.get("clarifiers", [])}


def parse_positions(text, used=frozenset()):
    """解析用户报的牌堆位置。全角、带圈数字先规范成半角；中文数字（七、二十三）需要调用方先换成阿拉伯数字。"""
    normalized = unicodedata.normalize("NFKC", text)
    parts = [p for p in re.split(r"[\s,，、;；]+", normalized.strip()) if p]
    if not parts:
        fail("没有收到数字")
    positions = []
    for part in parts:
        if not re.fullmatch(r"[0-9]+", part, re.ASCII):
            fail(f"「{part}」不是 1–{DECK_SIZE} 之间的数字（中文数字请先换成阿拉伯数字）")
        n = int(part)
        if not 1 <= n <= DECK_SIZE:
            fail(f"{n} 超出范围，只能是 1–{DECK_SIZE}")
        if n in positions:
            fail(f"{n} 重复了，每个位置只能抽一次")
        if n in used:
            fail(f"牌堆第 {n} 位已经抽过了，换一个数字")
        positions.append(n)
    return positions


def normalize_hash(text):
    value = re.sub(r"\s+", "", unicodedata.normalize("NFKC", text)).lower()
    if not HEX64_RE.fullmatch(value):
        fail("--expect 应该是 64 位十六进制的 SHA-256 哈希")
    return value


# ---------- 输出 ----------

def print_card_detail(card, o, topic, indent="    "):
    kind = card["arcana"] + (f"·{card['suit']}" if card["suit"] else "")
    keywords = card["upright"] if o == "U" else card["reversed"]
    print(f"{indent}类别：{kind}")
    print(f"{indent}画面：{card['image']}")
    print(f"{indent}关键词：{'、'.join(keywords)}")
    for label, field in TOPICS.items():
        if topic in (None, label):
            print(f"{indent}{label}：{card[field][o]}")
    print(f"{indent}是非：{card['yes_no'][o]}")


def print_overview(drawn, cards):
    n = len(drawn)
    picked = [cards[d["id"]] for d in drawn]
    majors = sum(1 for c in picked if c["arcana"] == "大阿卡纳")
    reversed_count = sum(1 for d in drawn if d["o"] == "R")
    suits = Counter(c["suit"] for c in picked if c["suit"])
    minor_numbers = [int(c["id"][1:]) for c in picked if c["suit"]]
    courts = sum(1 for k in minor_numbers if k > 10)
    repeats = [f"{NUMBER_NAMES[k]}×{v}" for k, v in sorted(Counter(k for k in minor_numbers if k <= 10).items()) if v >= 2]
    suit_text = "、".join(f"{s} {v}" for s, v in suits.most_common()) or "无"
    print(f"全局：大阿卡纳 {majors}/{n}，逆位 {reversed_count}/{n}，花色 {suit_text}，"
          f"宫廷牌 {courts}，重复数字 {'、'.join(repeats) or '无'}")


def print_yes_no(drawn, cards):
    values = [cards[d["id"]]["yes_no"][d["o"]] for d in drawn]
    yes, no = values.count("是"), values.count("否")
    score, n = yes - no, len(values)
    if score == n:
        verdict = "目前明确倾向是"
    elif score == -n:
        verdict = "目前明确倾向否"
    elif score > 0:
        verdict = "目前倾向是"
    elif score < 0:
        verdict = "目前倾向否"
    else:
        verdict = "目前没有定论"
    print(f"是非判定：是 {yes}、否 {no}、看情况 {n - yes - no} → {verdict}")
    print("    （按每张牌的固定是非值计算。问题是「该不该离开、结束、放弃」这类时，先按 spreads.md 核对再下结论）")


def display_width(text):
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in text)


def pad(text, width):
    return text + " " * (width - display_width(text))


def render_layout(layout, drawn):
    """用纯 ASCII 边框画牌阵（制表符在中文终端宽度不定，会错位）。"""
    cells = {d["order"]: (f"{d['order']} {d['slot']}", f"{d['name']} {'正' if d['o'] == 'U' else '逆'}") for d in drawn}
    width = max(display_width(line) for pair in cells.values() for line in pair)
    border = "+" + "-" * (width + 2) + "+"
    blank = [" " * len(border)] * 4
    lines = []
    for row in layout:
        boxes = [[border, f"| {pad(cells[i][0], width)} |", f"| {pad(cells[i][1], width)} |", border] if i else blank
                 for i in row]
        lines.extend("  ".join(box[k] for box in boxes).rstrip() for k in range(4))
    return "\n".join(lines)


def ps_quote(text):
    return "'" + text.replace("'", "''") + "'"


def sh_quote(text):
    return "'" + text.replace("'", "'\"'\"'") + "'"


def verify_commands(path):
    """各系统自带的哈希命令，当前系统排在前面。路径用单引号包住，防止 $、反引号被展开。"""
    commands = {
        "win32": [("Windows PowerShell", f"Get-FileHash -Algorithm SHA256 -LiteralPath {ps_quote(str(path))}"),
                  ("Windows 命令提示符", f'cd /d "{path.parent}" && certutil -hashfile "{path.name}" SHA256')],
        "darwin": [("macOS", f"shasum -a 256 {sh_quote(str(path))}")],
        "linux": [("Linux", f"sha256sum {sh_quote(str(path))}")],
    }
    native = sys.platform if sys.platform in commands else "linux"
    return commands[native] + [c for key, group in commands.items() if key != native for c in group]


# ---------- 命令 ----------

def cmd_new(_args):
    cards = load_cards()
    rng = secrets.SystemRandom()
    for _ in range(10):
        ids = list(cards)
        rng.shuffle(ids)
        now = datetime.now()
        record = {
            "version": COMMIT_VERSION,
            "session": f"{now:%Y%m%d-%H%M%S}-{secrets.token_hex(2)}",
            "created_at": now.strftime(TIME_FMT),
            "nonce": secrets.token_hex(32),
            "deck": [{"id": cid, "name": cards[cid]["name_zh"], "o": rng.choice("UR")} for cid in ids],
        }
        record["sha256"] = hashlib.sha256(preimage_bytes(record)).hexdigest()
        try:
            save_record(record, create=True)
            break
        except FileExistsError:
            continue
    else:
        fail("会话号连续冲突，请稍后再试")
    print(f"牌已洗好，牌序已经锁定（{DECK_SIZE} 张，每张随机正/逆位）")
    print(f"会话号：{record['session']}")
    print(f"SHA-256：{record['sha256']}")
    print(f"生成时间：{record['created_at']}")
    print("（请记下这串哈希，验证时拿它来比）")
    print()
    print(f"牌序在这一刻锁定，这件事可能的走向，都在这 {DECK_SIZE} 张牌里了。")
    print()
    print("接下来请静下心，默想你要问的事；")
    print("你想着它报出的数字，会把属于这件事的那几张找出来。")


def cmd_spreads(_args):
    for s in load_spreads().values():
        print(f"【{s['name']}】{len(s['positions'])} 张")
        for k, (name, meaning) in enumerate(s["positions"], start=1):
            print(f"  {circled(k)} {name}" + (f"：{meaning}" if meaning else ""))


def cmd_draw(args):
    if not args.question.strip():
        fail("--question 不能为空，写用户确认后的问题")
    spread = get_spread(args.spread)
    cards = load_cards()
    size = len(spread["positions"])
    with session_lock(args.session):
        record = load_record(args.session)
        if record.get("revealed_at"):
            fail("这副牌已经公开过牌序，不能再抽。请 new 一个新会话")
        if record.get("draw"):
            fail(f"这副牌已在 {record['draw']['time']} 抽过，一副牌只抽一次。补牌用 clarify；算另一件事请 new 一个新会话")
        if args.top is not None:
            if args.top != size:
                fail(f"「{spread['name']}」要 {size} 张，--top 给的是 {args.top}")
            positions = list(range(1, size + 1))
        else:
            positions = parse_positions(args.pick)
            if len(positions) != size:
                fail(f"「{spread['name']}」要 {size} 个数字，收到 {len(positions)} 个")

        now = datetime.now()
        slots = slot_names(spread, now)
        drawn = [{"order": k, "slot": slots[k - 1], "position": pos, "id": record["deck"][pos - 1]["id"],
                  "name": cards[record["deck"][pos - 1]["id"]]["name_zh"], "o": record["deck"][pos - 1]["o"]}
                 for k, pos in enumerate(positions, start=1)]
        record["draw"] = {"time": now.strftime(TIME_FMT), "spread": spread["name"], "question": args.question,
                          "topic": args.topic, "cards": drawn, "clarifiers": []}
        save_record(record)  # 先落盘再打印：打印中途出错也不能让这副牌变回「未抽」

    meanings = [p[1] for p in spread["positions"]]
    print(f"会话号：{record['session']}　牌阵：{spread['name']}（{size} 张）" + (f"　侧重：{args.topic}" if args.topic else ""))
    print(f"问题：{args.question}")
    for d in drawn:
        card = cards[d["id"]]
        meaning = meanings[d["order"] - 1]
        print()
        print(f"{circled(d['order'])} {d['slot']}" + (f"（{meaning}）" if meaning else ""))
        print(f"    {card['name_zh']}（{card['name_en']}）· {ORIENTATION[d['o']]}　[牌堆第 {d['position']} 位]")
        print_card_detail(card, d["o"], args.topic)
    print()
    if size >= 2:
        print_overview(drawn, cards)
    if spread.get("yes_no"):
        print_yes_no(drawn, cards)
    print()
    print("牌阵摆放：")
    print(render_layout(spread["layout"], drawn))


def cmd_clarify(args):
    cards = load_cards()
    with session_lock(args.session):
        record = load_record(args.session)
        if record.get("revealed_at"):
            fail("这副牌已经公开过牌序，不能再补牌")
        draw = record.get("draw")
        if not draw:
            fail("这副牌还没抽过，先 draw")
        clarifiers = draw.setdefault("clarifiers", [])
        if len(clarifiers) >= MAX_CLARIFIERS:
            fail(f"一次占卜最多补 {MAX_CLARIFIERS} 张，已经补满了")
        if not 1 <= args.slot <= len(draw["cards"]):
            fail(f"--for 只能是 1–{len(draw['cards'])}")
        if any(c["for"] == args.slot for c in clarifiers):
            fail(f"位置 {circled(args.slot)} 已经补过一张，每个位置只补一次")
        used = used_positions(record)
        if args.next:
            pos = min(p for p in range(1, DECK_SIZE + 1) if p not in used)
        else:
            picked = parse_positions(args.pick, used)
            if len(picked) != 1:
                fail("补牌只报一个数字")
            pos = picked[0]
        entry = record["deck"][pos - 1]
        clarifiers.append({"for": args.slot, "position": pos, "id": entry["id"], "name": cards[entry["id"]]["name_zh"],
                           "o": entry["o"], "time": datetime.now().strftime(TIME_FMT)})
        save_record(record)

    card = cards[entry["id"]]
    target = draw["cards"][args.slot - 1]
    print(f"补牌：澄清 {circled(args.slot)} {target['slot']}（原牌 {target['name']} {ORIENTATION[target['o']]}）")
    print(f"    {card['name_zh']}（{card['name_en']}）· {ORIENTATION[entry['o']]}　[牌堆第 {pos} 位]")
    print_card_detail(card, entry["o"], draw.get("topic"))


def cmd_reveal(args):
    expected = normalize_hash(args.expect) if args.expect else None
    with session_lock(args.session):
        record = load_record(args.session)
        if not record.get("draw"):
            fail("这副牌还没抽过，不能揭晓")
        data = preimage_bytes(record)
        actual = hashlib.sha256(data).hexdigest()
        consistent = actual == record["sha256"]
        ok = consistent and (expected is None or expected == actual)
        out = records_dir() / f"{args.session}.preimage.txt"  # 路径只用命令行传入、已校验过的会话号拼
        with open(out, "wb") as f:  # 写字节：不能让 Windows 把 \n 换成 \r\n，否则外部哈希工具算出来对不上
            f.write(data)
        if ok and not record.get("revealed_at"):
            record["revealed_at"] = datetime.now().strftime(TIME_FMT)
            save_record(record)

    draw = record["draw"]
    marks = {c["position"]: f"{circled(c['order'])} {c['slot']}" for c in draw.get("cards", [])}
    marks.update({c["position"]: f"补牌（澄清 {circled(c['for'])}）" for c in draw.get("clarifiers", [])})
    print(f"会话号：{record['session']}　洗牌时间：{record['created_at']}")
    if expected:
        print(f"第 1 步给你的哈希：{expected}")
    print(f"记录里存的哈希：  {record['sha256']}")
    print(f"按牌序重新计算：  {actual}")
    if not ok:
        print("结果：不一致！牌序在锁定后被改动过")
    elif expected:
        print("结果：一致，牌序自第 1 步锁定后没有被改动")
    else:
        print("结果：记录本身前后一致。要确认没人动过，请拿第 1 步给你的哈希来比（加 --expect）")
    print()
    print("完整牌序（位置 正U/逆R 编号 牌名）：")
    for pos, entry in enumerate(record["deck"], start=1):
        mark = f"　← {marks[pos]}" if pos in marks else ""
        print(f"  {pos:02d} {entry['o']} {entry['id']} {entry['name']}{mark}")
    print()
    print(f"原像文件：{out}")
    print("（UTF-8、无 BOM、LF 换行、末尾无换行；不要用编辑器打开后另存，否则哈希会变）")
    print("自己验证（任选一条，结果不分大小写应与第 1 步的哈希相同）：")
    for label, command in verify_commands(out):
        print(f"  {label}：{command}")
    if not ok:
        sys.exit(EXIT_MISMATCH)


def cmd_show(args):
    record = load_record(args.session)
    draw = record.get("draw") or {}
    print(f"会话号：{record['session']}")
    print(f"记录里存的哈希：{record['sha256']}")
    print(f"洗牌时间：{record['created_at']}")
    print(f"状态：{status_of(record)}")
    if draw:
        print(f"牌阵：{draw.get('spread')}")
        print(f"问题：{draw.get('question')}")
        print(f"补牌：{len(draw.get('clarifiers', []))} 张")


def cmd_list(_args):
    directory = records_dir()
    files = sorted(p for p in directory.glob("*.json") if SESSION_RE.fullmatch(p.stem)) if directory.exists() else []
    if not files:
        print(f"还没有任何占卜记录（{directory}）")
        return
    for path in files:
        try:
            record = read_json(path)
            check_record(record, path.stem, path)
        except (OSError, ValueError, TarotError) as e:
            print(f"{path.stem}  （记录损坏或被改动：{e}）")
            continue
        draw = record.get("draw") or {}
        question = " ".join(str(draw.get("question") or "-").split())
        print(f"{record['created_at']}  {record['session']}  {status_of(record)}  {record['sha256']}  "
              f"{draw.get('spread') or '-'}  {question}")


def main():
    configure_output()
    parser = argparse.ArgumentParser(description="塔罗牌洗牌锁定 / 抽牌 / 补牌 / 验证")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("new", help="洗牌并锁定，打印哈希").set_defaults(func=cmd_new)
    sub.add_parser("spreads", help="列出所有牌阵").set_defaults(func=cmd_spreads)

    p_draw = sub.add_parser("draw", help="按牌阵抽牌")
    p_draw.add_argument("session")
    p_draw.add_argument("--spread", required=True, help="牌阵名称，必须和 spreads 列出的一致")
    p_draw.add_argument("--question", required=True, help="用户确认后的问题")
    how = p_draw.add_mutually_exclusive_group(required=True)
    how.add_argument("--pick", help="用户报的位置，如 7,23,51（按顺序对应牌阵位置）")
    how.add_argument("--top", type=int, help="从牌堆顶发 N 张，N 必须等于牌阵张数")
    p_draw.add_argument("--topic", choices=list(TOPICS), help="只打印这一方面的含义，不填则三方面都打印")
    p_draw.set_defaults(func=cmd_draw)

    p_clarify = sub.add_parser("clarify", help="给某个位置补一张澄清牌")
    p_clarify.add_argument("session")
    p_clarify.add_argument("--for", dest="slot", type=int, required=True, help="要澄清的牌阵位置编号")
    which = p_clarify.add_mutually_exclusive_group(required=True)
    which.add_argument("--pick", help="用户报的一个牌堆位置")
    which.add_argument("--next", action="store_true", help="取牌堆里最靠前的未用位置")
    p_clarify.set_defaults(func=cmd_clarify)

    p_reveal = sub.add_parser("reveal", help="公开牌序并验证哈希")
    p_reveal.add_argument("session")
    p_reveal.add_argument("--expect", help="第 1 步给用户看的哈希；给了就拿它来比")
    p_reveal.set_defaults(func=cmd_reveal)

    p_show = sub.add_parser("show", help="查看会话哈希与状态")
    p_show.add_argument("session")
    p_show.set_defaults(func=cmd_show)

    sub.add_parser("list", help="列出历史会话").set_defaults(func=cmd_list)

    args = parser.parse_args()
    try:
        args.func(args)
    except TarotError as e:
        print(f"错误：{e}", file=sys.stderr)
        sys.exit(1)
    except (OSError, ValueError, KeyError, TypeError) as e:
        print(f"错误：读写文件或数据出了问题（{type(e).__name__}: {e}）", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
