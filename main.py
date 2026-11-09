import math
import os
import random
import struct
import sys
import tempfile
import threading
import time
import wave
from copy import deepcopy

from kivy.config import Config

# Yuksek FPS: Window olusmadan once ayarlanmali
Config.set('graphics', 'maxfps', '144')
Config.set('graphics', 'vsync', '1')

from kivy.app import App
from kivy.animation import Animation
from kivy.clock import Clock
from kivy.core.audio import SoundLoader
from kivy.core.text import Label as CoreLabel
from kivy.core.window import Window
from kivy.graphics import (
    Color, RoundedRectangle, Ellipse, Line, Rectangle, Triangle,
    Fbo, ClearColor, ClearBuffers
)
from kivy.graphics.texture import Texture
from kivy.metrics import dp, sp
from kivy.properties import NumericProperty, StringProperty, ListProperty
from kivy.uix.behaviors import ButtonBehavior
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.floatlayout import FloatLayout
from kivy.uix.label import Label
from kivy.uix.widget import Widget
from kivy.utils import platform

Window.clearcolor = (0.035, 0.055, 0.09, 1)

if platform in ('win', 'linux', 'macosx'):
    Window.size = (430, 820)

# Arama thread'i arayuzu kasmasin
try:
    sys.setswitchinterval(0.0005)
except Exception:
    pass


# ==ENGINE_BEGIN==
# ==========================================
#        OYUN MOTORU + YAPAY ZEKA
#   (arayuzden bagimsiz, ayri thread'de calisir)
# ==========================================

INF = 10 ** 9
WIN = 100000

DIRS_KING = ((1, 0), (-1, 0), (0, 1), (0, -1))
DIRS_W = ((-1, 0), (0, 1), (0, -1))
DIRS_B = ((1, 0), (0, 1), (0, -1))

ADV = (0, 0, 5, 11, 19, 31, 52, 0)


def piece_dirs(piece):
    if len(piece) == 2:
        return DIRS_KING
    return DIRS_W if piece == 'w' else DIRS_B


def capture_opts(board, r, c, piece, last_dir):
    opts = []
    enemy = 'b' if piece[0] == 'w' else 'w'
    king = len(piece) == 2

    for dr, dc in piece_dirs(piece):

        if last_dir is not None and dr == -last_dir[0] and dc == -last_dir[1]:
            continue

        nr, nc = r + dr, c + dc

        if not (0 <= nr < 8 and 0 <= nc < 8):
            continue

        if not king:

            t = board[nr][nc]

            if t and t[0] == enemy:
                lr, lc = nr + dr, nc + dc

                if 0 <= lr < 8 and 0 <= lc < 8 and board[lr][lc] is None:
                    opts.append((lr, lc, nr, nc, (dr, dc)))

        else:

            while 0 <= nr < 8 and 0 <= nc < 8 and board[nr][nc] is None:
                nr += dr
                nc += dc

            if not (0 <= nr < 8 and 0 <= nc < 8):
                continue

            t = board[nr][nc]

            if not t or t[0] != enemy:
                continue

            cr, cc = nr, nc
            nr += dr
            nc += dc

            while 0 <= nr < 8 and 0 <= nc < 8 and board[nr][nc] is None:
                opts.append((nr, nc, cr, cc, (dr, dc)))
                nr += dr
                nc += dc

    return opts


def _caps(board, r, c, piece, last_dir, path, out):
    opts = capture_opts(board, r, c, piece, last_dir)

    if not opts:
        if path:
            out.append(tuple(path))
        return

    for nr, nc, cr, cc, d in opts:
        cap = board[cr][cc]

        board[r][c] = None
        board[cr][cc] = None
        board[nr][nc] = piece
        path.append((nr, nc, cr, cc))

        _caps(board, nr, nc, piece, d, path, out)

        path.pop()
        board[nr][nc] = None
        board[cr][cc] = cap
        board[r][c] = piece


def gen_captures(board, color):
    """[(r, c, route)] - en fazla tas alan rotalar (zorunlu)."""
    caps = []

    for r in range(8):
        row = board[r]

        for c in range(8):
            p = row[c]

            if p and p[0] == color:
                out = []
                _caps(board, r, c, p, None, [], out)

                for path in out:
                    caps.append((r, c, path))

    if not caps:
        return caps

    mx = max(len(x[2]) for x in caps)
    return [x for x in caps if len(x[2]) == mx]


def quiet_moves(board, r, c, piece):
    res = []
    king = len(piece) == 2

    for dr, dc in piece_dirs(piece):
        nr, nc = r + dr, c + dc

        while 0 <= nr < 8 and 0 <= nc < 8 and board[nr][nc] is None:
            res.append((nr, nc, None, None))

            if not king:
                break

            nr += dr
            nc += dc

    return res


def gen_moves(board, color):
    """[(r, c, move, is_capture)]"""
    caps = gen_captures(board, color)

    if caps:
        return [(r, c, path, True) for r, c, path in caps]

    moves = []

    for r in range(8):
        row = board[r]

        for c in range(8):
            p = row[c]

            if p and p[0] == color:
                for mv in quiet_moves(board, r, c, p):
                    moves.append((r, c, mv, False))

    return moves


def apply_move(board, m):
    r, c, mv, cap = m
    piece = board[r][c]

    if cap:
        removed = []
        board[r][c] = None
        lr, lc = r, c

        for nr, nc, cr, cc in mv:
            removed.append((cr, cc, board[cr][cc]))
            board[cr][cc] = None
            lr, lc = nr, nc

        newp = piece

        if piece == 'w' and lr == 0:
            newp = 'wk'
        elif piece == 'b' and lr == 7:
            newp = 'bk'

        board[lr][lc] = newp
        return (piece, removed, lr, lc)

    nr, nc = mv[0], mv[1]
    newp = piece

    if piece == 'w' and nr == 0:
        newp = 'wk'
    elif piece == 'b' and nr == 7:
        newp = 'bk'

    board[r][c] = None
    board[nr][nc] = newp
    return (piece, None, nr, nc)


def undo_move(board, m, info):
    r, c = m[0], m[1]
    piece, removed, lr, lc = info

    board[lr][lc] = None

    if removed:
        for cr, cc, p in removed:
            board[cr][cc] = p

    board[r][c] = piece


def evaluate(board):
    """Siyah (bilgisayar) acisindan puan."""
    score = 0

    for r in range(8):
        row = board[r]

        for c in range(8):
            p = row[c]

            if not p:
                continue

            black = p[0] == 'b'

            if len(p) == 2:
                v = 330 + 4 - (abs(3.5 - r) + abs(3.5 - c))
            else:
                adv = r if black else 7 - r
                v = 100 + ADV[adv]

                if c == 0 or c == 7:
                    v += 2

                br = r - 1 if black else r + 1

                if 0 <= br < 8:
                    b = board[br][c]

                    if b and b[0] == p[0]:
                        v += 4

                left = row[c - 1] if c > 0 else None
                right = row[c + 1] if c < 7 else None

                if (left and left[0] == p[0]) or (right and right[0] == p[0]):
                    v += 2

            score += v if black else -v

    return score


def eval_side(board, color):
    v = evaluate(board)
    return v if color == 'b' else -v


def order_moves(board, color, moves, tt_best):

    if len(moves) < 2 or moves[0][3]:
        return moves

    def key(m):
        if tt_best is not None and m[:3] == tt_best:
            return -1000

        r, c, mv, _ = m
        nr = mv[0]
        p = board[r][c]

        if len(p) == 1:
            if nr != r:
                prog = nr if color == 'b' else 7 - nr

                if prog == 7:
                    return -500

                return -100 - prog

            return 10

        return 0

    return sorted(moves, key=key)


class _Timeout(Exception):
    pass


class Searcher:

    def __init__(self, time_limit):
        self.deadline = time.perf_counter() + time_limit
        self.nodes = 0
        self.tt = {}
        self.limit_ply = 99

    def negamax(self, board, color, depth, alpha, beta, ply):

        self.nodes += 1

        if not (self.nodes & 63):
            if time.perf_counter() > self.deadline:
                raise _Timeout()
            time.sleep(0)

        if depth <= 0:
            # sadece zorunlu tas almalari uzat (ufuk etkisini azaltir)
            caps = gen_captures(board, color)

            if not caps or ply >= self.limit_ply:
                return eval_side(board, color)

            moves = [(r, c, p, True) for r, c, p in caps]
            key = None
            tt_best = None

        else:
            moves = gen_moves(board, color)

            if not moves:
                return -WIN + ply

            key = (tuple(map(tuple, board)), color)
            tt_best = None
            ent = self.tt.get(key)

            if ent:
                d, v, flag, bk = ent
                tt_best = bk

                if d >= depth and abs(v) < WIN - 500:
                    if flag == 0:
                        return v
                    if flag == 1 and v >= beta:
                        return v
                    if flag == 2 and v <= alpha:
                        return v

            moves = order_moves(board, color, moves, tt_best)

        opp = 'w' if color == 'b' else 'b'
        alpha0 = alpha
        best = -INF
        bk = None

        for m in moves:
            info = apply_move(board, m)
            v = -self.negamax(board, opp, depth - 1, -beta, -alpha, ply + 1)
            undo_move(board, m, info)

            if v > best:
                best = v
                bk = m[:3]

            if v > alpha:
                alpha = v

            if alpha >= beta:
                break

        if key is not None:
            if best <= alpha0:
                flag = 2
            elif best >= beta:
                flag = 1
            else:
                flag = 0

            if len(self.tt) > 400000:
                self.tt.clear()

            self.tt[key] = (depth, best, flag, bk)

        return best

    def root(self, board, color, moves, depth):

        self.limit_ply = depth + 8
        opp = 'w' if color == 'b' else 'b'
        alpha, beta = -INF, INF
        best_val, best_mv = -INF, moves[0]

        for m in moves:
            info = apply_move(board, m)
            v = -self.negamax(board, opp, depth - 1, -beta, -alpha, 1)
            undo_move(board, m, info)

            if v > best_val:
                best_val, best_mv = v, m

            if v > alpha:
                alpha = v

        return best_val, best_mv


def search_best(board, color, moves, max_depth, time_limit):
    """Iteratif derinlesen alfa-beta. Sure dolunca son tam derinligin sonucu."""
    s = Searcher(time_limit)
    moves = list(moves)
    random.shuffle(moves)
    best = moves[0]

    for depth in range(1, max_depth + 1):

        try:
            val, mv = s.root(board, color, moves, depth)
        except _Timeout:
            break

        best = mv
        moves.remove(mv)
        moves.insert(0, mv)

        if abs(val) >= WIN - 200:
            break

    return best


def choose_move(board, level):
    """Siyah icin hamle sec. board kopya olmali (thread icinde degisir)."""
    color = 'b'
    moves = gen_moves(board, color)

    if not moves:
        return None

    if len(moves) == 1:
        return moves[0]

    if level == 'KOLAY':
        if random.random() < 0.5:
            return random.choice(moves)
        return search_best(board, color, moves, 2, 0.25)

    if level == 'ORTA':
        return search_best(board, color, moves, 5, 0.8)

    return search_best(board, color, moves, 14, 2.2)

# ==ENGINE_END==


# ==========================================
#              YARDIMCI FONKSIYONLAR
# ==========================================

INTRO_END = 1.2


def clamp(x, a=0.0, b=1.0):
    return max(a, min(b, x))


def ease_out_cubic(t):
    t = clamp(t)
    return 1 - (1 - t) ** 3


def smootherstep(t):
    t = clamp(t)
    return t * t * t * (t * (t * 6 - 15) + 10)


def ease_out_back(t):
    t = clamp(t)
    c1 = 1.70158
    c3 = c1 + 1
    return 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2


def gradient_texture(top, bottom, steps=64):
    tex = Texture.create(size=(1, steps), colorfmt='rgba')
    buf = bytearray()
    for i in range(steps):
        k = i / (steps - 1)
        # i = 0 en alt satir
        col = [bottom[j] + (top[j] - bottom[j]) * k for j in range(4)]
        buf.extend(int(clamp(v) * 255) for v in col)
    tex.blit_buffer(bytes(buf), colorfmt='rgba', bufferfmt='ubyte')
    tex.mag_filter = 'linear'
    tex.min_filter = 'linear'
    return tex


def draw_shadow(cx, cy, d, alpha=1.0, lift=0.0):
    Color(0, 0, 0, 0.38 * alpha * (1 - min(lift / (d * 1.2), 0.5)))
    Ellipse(
        pos=(cx - d / 2 + d * 0.02, cy - d / 2 - d * 0.14),
        size=(d, d * 0.96)
    )


def draw_disc(cx, cy, d, white, alpha=1.0, lift=0.0, king=False,
              shadow=True):
    """Katmanli, hafif 3D gorunumlu tas cizer. Canvas baglaminda cagrilmali."""
    if d < 1 or alpha <= 0:
        return

    py = cy + lift

    # golge
    if shadow:
        draw_shadow(cx, cy, d, alpha, lift)

    th = d * 0.10

    if white:
        side = (0.52, 0.58, 0.70)
        rim = (0.88, 0.91, 0.97)
        face = (0.97, 0.98, 1.0)
        ring = (0.62, 0.68, 0.78)
    else:
        side = (0.01, 0.015, 0.03)
        rim = (0.24, 0.28, 0.37)
        face = (0.07, 0.09, 0.14)
        ring = (0.35, 0.40, 0.48)

    # tas kalinligi
    Color(*side, alpha)
    Ellipse(pos=(cx - d / 2, py - d / 2 - th), size=(d, d))

    # kenar
    Color(*rim, alpha)
    Ellipse(pos=(cx - d / 2, py - d / 2), size=(d, d))

    # yuz
    Color(*face, alpha)
    Ellipse(
        pos=(cx - d * 0.43, py - d * 0.43),
        size=(d * 0.86, d * 0.86)
    )

    # isik / golge
    if white:
        Color(0.78, 0.83, 0.92, 0.45 * alpha)
        Ellipse(
            pos=(cx - d * 0.30, py - d * 0.40),
            size=(d * 0.60, d * 0.22)
        )
        Color(1, 1, 1, 0.8 * alpha)
    else:
        Color(1, 1, 1, 0.12 * alpha)

    Ellipse(
        pos=(cx - d * 0.30, py + d * 0.05),
        size=(d * 0.42, d * 0.26)
    )

    # ic halka
    Color(*ring, alpha)
    Line(circle=(cx, py, d * 0.33), width=max(1.0, d * 0.025))

    if king:
        Color(1, 0.78, 0.22, 0.55 * alpha)
        Line(circle=(cx, py, d * 0.40), width=max(1.0, d * 0.03))

        s = d * 0.50
        bx = cx - s / 2
        by = py - s * 0.30
        top = by + s * 0.2

        # taban
        Color(0.82, 0.52, 0.08, alpha)
        Rectangle(pos=(bx, by), size=(s, s * 0.2))

        # sivri uclar
        Color(1, 0.78, 0.22, alpha)
        w3 = s / 3

        for k in range(3):
            x1 = bx + k * w3
            x2 = x1 + w3
            apex_y = top + s * (0.5 if k == 1 else 0.38)
            mid = (x1 + x2) / 2

            Triangle(points=[x1, top, x2, top, mid, apex_y])

            rr = s * 0.06
            Ellipse(
                pos=(mid - rr, apex_y - rr),
                size=(rr * 2, rr * 2)
            )

        # mucevher
        Color(0.92, 0.22, 0.32, alpha)
        rr = s * 0.045
        Ellipse(
            pos=(cx - rr, by + s * 0.1 - rr),
            size=(rr * 2, rr * 2)
        )


# ==========================================
#                 SES EFEKTLERI
#   (dosya gerekmez: kodla uretilir, ilk acilista kaydedilir)
# ==========================================

SR = 22050

# ('tone', baslangic, sure, f0, f1, genlik, sonum, 2.harmonik)
# ('noise', baslangic, sure, genlik, sonum)
SFX = {
    'select': ([
        ('tone', 0, 0.07, 720, 820, 0.5, 45, 0.2),
    ], 0.09),
    'move': ([
        ('tone', 0, 0.14, 210, 150, 0.8, 32, 0.35),
        ('tone', 0, 0.05, 1100, 900, 0.25, 90, 0.0),
        ('noise', 0, 0.012, 0.5, 200),
    ], 0.16),
    'capture': ([
        ('noise', 0, 0.03, 0.9, 120),
        ('tone', 0, 0.18, 190, 120, 0.9, 26, 0.4),
        ('tone', 0, 0.30, 95, 60, 0.8, 14, 0.2),
        ('tone', 0.075, 0.12, 260, 200, 0.5, 30, 0.3),
        ('noise', 0.075, 0.015, 0.4, 200),
    ], 0.34),
    'king': ([
        ('tone', 0.00, 0.60, 523.25, 523.25, 0.40, 6, 0.4),
        ('tone', 0.09, 0.60, 659.25, 659.25, 0.40, 6, 0.4),
        ('tone', 0.18, 0.60, 783.99, 783.99, 0.40, 6, 0.4),
        ('tone', 0.27, 0.80, 1046.5, 1046.5, 0.45, 4, 0.4),
    ], 1.1),
    'win': ([
        ('tone', 0.00, 0.60, 523.25, 523.25, 0.40, 4, 0.4),
        ('tone', 0.16, 0.60, 659.25, 659.25, 0.40, 4, 0.4),
        ('tone', 0.32, 0.60, 783.99, 783.99, 0.40, 4, 0.4),
        ('tone', 0.48, 1.10, 1046.5, 1046.5, 0.45, 3, 0.4),
        ('tone', 0.48, 1.10, 783.99, 783.99, 0.30, 3, 0.3),
        ('tone', 0.48, 1.10, 659.25, 659.25, 0.30, 3, 0.3),
    ], 1.7),
    'lose': ([
        ('tone', 0.00, 0.60, 440.0, 440.0, 0.40, 4, 0.3),
        ('tone', 0.24, 0.60, 349.23, 349.23, 0.40, 4, 0.3),
        ('tone', 0.48, 0.60, 293.66, 293.66, 0.40, 4, 0.3),
        ('tone', 0.72, 0.90, 220.0, 220.0, 0.45, 3, 0.3),
    ], 1.7),
    'error': ([
        ('tone', 0, 0.16, 140, 130, 0.5, 8, 1.0),
    ], 0.2),
    'newgame': ([
        ('tone', 0, 0.30, 280, 900, 0.35, 6, 0.2),
    ], 0.32),
}


def synth(events, length):
    n = int(SR * length)
    buf = [0.0] * n
    rnd = random.Random(7)

    for ev in events:
        i0 = int(ev[1] * SR)
        cnt = int(ev[2] * SR)

        if ev[0] == 'tone':
            _, _, _, f0, f1, amp, decay, harm = ev
            ph = 0.0

            for i in range(cnt):
                if i0 + i >= n:
                    break

                t = i / SR
                f = f0 + (f1 - f0) * (i / max(1, cnt))
                ph += 2 * math.pi * f / SR
                v = math.sin(ph) + harm * math.sin(2 * ph)
                a = amp * math.exp(-t * decay)

                if i < 40:
                    a *= i / 40.0

                buf[i0 + i] += v * a

        else:
            _, _, _, amp, decay = ev
            lp = 0.0

            for i in range(cnt):
                if i0 + i >= n:
                    break

                t = i / SR
                lp += (rnd.uniform(-1, 1) - lp) * 0.35
                buf[i0 + i] += lp * amp * math.exp(-t * decay)

    peak = max(0.001, max(abs(x) for x in buf))
    k = 0.9 / peak if peak > 0.9 else 1.0

    return struct.pack(
        '<%dh' % n,
        *[int(clamp(x * k, -1.0, 1.0) * 32767) for x in buf]
    )


class SoundBank:

    def __init__(self, folder):
        self.pool = {}
        self.pos = {}
        self.ready = False
        self.volume = 0.8

        # uretimi arka planda yap, acilisi geciktirme
        threading.Thread(
            target=self._prepare, args=(folder,), daemon=True
        ).start()

    def _prepare(self, folder):

        try:
            try:
                os.makedirs(folder, exist_ok=True)
            except Exception:
                folder = tempfile.gettempdir()

            paths = {}

            for name, (events, length) in SFX.items():
                path = os.path.join(folder, 'dama_%s_v1.wav' % name)

                if not os.path.exists(path):
                    data = synth(events, length)

                    with wave.open(path, 'wb') as w:
                        w.setnchannels(1)
                        w.setsampwidth(2)
                        w.setframerate(SR)
                        w.writeframes(data)

                paths[name] = path

            # SoundLoader ana thread'de yuklensin
            Clock.schedule_once(lambda dt: self._load(paths), 0)

        except Exception:
            pass

    def _load(self, paths):

        try:
            for name, path in paths.items():
                copies = []

                for _ in range(2):
                    s = SoundLoader.load(path)

                    if s:
                        copies.append(s)

                if copies:
                    self.pool[name] = copies
                    self.pos[name] = 0

            self.ready = True

        except Exception:
            pass

    def play(self, name, delay=0.0):

        if delay > 0:
            Clock.schedule_once(lambda dt: self.play(name), delay)
            return

        copies = self.pool.get(name)

        if not copies:
            return

        try:
            i = self.pos[name] % 