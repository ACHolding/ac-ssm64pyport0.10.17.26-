#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sm64pyport0.1x.py  --  SM64 Py Port
====================================
Unofficial Nintendo / Super Mario 64–style Python 3 port engine.
Single-file pygame-ce recreation of the SM64 PC-port *feel*:

  * locked 60 Hz simulation (N64 frame rate — fixed DT = 1/60)
  * software 3D renderer: flat-shaded polys, painter's sort, near clip,
    distance fog, numpy fast path (pure-Python fallback)
  * Peach's Castle hub with Power Star–gated course paintings
  * Mario moveset: run, skid, crouch, single / double / triple jump,
    long jump, backflip, wall kick, ground pound, dive + rollout, punch
  * Lakitu-style orbit camera, moving platforms, breakable boxes,
    Goomba walkers, orbiting spike balls, lava
  * 17 Power Stars, yellow/red/blue coins, 50-coin stars, 8-wedge HP,
    lives, save file, pause, synthesized SFX + course music

  This is a fan engine — not an official Nintendo product.
  No ROM dumping; original geometry + generated audio only.

Run:      python sm64pyport0.1x.py
Needs:    pip install pygame-ce numpy        (numpy optional but faster)
Test:     python sm64pyport0.1x.py --selftest

Controls (keyboard)
  Arrows / WASD .... move            Space / Z / K ... jump (A)
  Shift / X / J .... crouch / ground pound (in air)   (Z)
  C / L / Ctrl ..... punch / dive (while running or in air)  (B)
  Q / E ............ rotate camera   Right-mouse drag  rotate camera
  Mouse wheel ...... zoom            Esc / P ......... pause
  F1 ............... FPS counter     Enter ........... start / select
Moves (SM64)
  Triple jump ...... jump, jump, jump in rhythm while running
  Long jump ........ while running: hold crouch + jump
  Backflip ......... standing still: hold crouch + jump
  Wall kick ........ jump into a wall, press jump as you hit it
  Ground pound ..... crouch in mid-air (breaks boxes)
  Dive / rollout ... action while running, then jump to roll out
Gamepad: left stick move, right stick camera, A jump, B/X action,
         LB/RB/ZL crouch, Start pause.
"""
import math
import os
import sys
import json
import random
import time
from array import array
from operator import itemgetter

try:
    import pygame
except ImportError:
    print("SM64 Py Port needs pygame-ce:   pip install pygame-ce numpy")
    sys.exit(1)
try:
    import numpy as np
except ImportError:       # pure-Python renderer fallback
    np = None

# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------
TITLE = "SM64 Py Port"
NINTENDO = "NINTENDO"
GAME_FULL = "SUPER MARIO 64"
WIN_W, WIN_H = 1280, 720
RW, RH = 640, 360                      # internal render resolution
# N64 NTSC game clock: SM64 PC-port style — 60 logic frames / second.
# Every tick advances exactly FRAME_TIME; speed never scales with FPS.
N64_FPS = 60
FPS = N64_FPS
FRAME_TIME = 1.0 / N64_FPS             # 1/60 s per frame (exact)
DT = FRAME_TIME
FOVY = math.radians(62)
FOCAL = (RH / 2) / math.tan(FOVY / 2)
NEAR = 0.15
FAR = 78.0
FOG0 = 34.0
TILE = 4.0

GRAV = 34.0
TERM = -45.0
RUN = 8.5
AIRACC = 16.0
AIRMAX = 7.0
STEP = 0.45
MAX_HP = 8
TOTAL_STARS = 17

SAVE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "sm64pyport_save.json")

GROUNDED = ('ground', 'crouch', 'slide', 'punch')
AIRBORNE = ('air', 'gp', 'dive', 'hurt', 'burnt')
SOLID_KINDS = ('solid', 'lava', 'crate')
TAU = math.pi * 2

LIGHT = (0.36, 0.85, 0.38)
_ln = math.sqrt(sum(c * c for c in LIGHT))
LIGHT = tuple(c / _ln for c in LIGHT)

# palette
GRASS = (88, 182, 72)
DIRT = (150, 106, 62)
STONE = (170, 170, 178)
BRICK = (204, 160, 116)
ROOF = (60, 90, 200)
WOOD = (132, 88, 50)
LEAF = (46, 150, 62)
CLOUD = (238, 240, 252)
BASALT = (78, 68, 72)
ROCK = (120, 70, 56)
LAVA = (250, 96, 24)
CRATE = (196, 140, 64)
GOLD = (255, 214, 60)
STARC = (255, 230, 60)
STARDONE = (170, 186, 214)
WHITE = (255, 255, 255)
BLACK = (0, 0, 0)

FACE_K = {(0, 1, 0): 1.0, (0, -1, 0): 0.45, (1, 0, 0): 0.80,
          (-1, 0, 0): 0.66, (0, 0, 1): 0.88, (0, 0, -1): 0.60}


def clamp(v, a, b):
    return a if v < a else b if v > b else v


def approach(v, t, d):
    return min(v + d, t) if v < t else max(v - d, t)


def angdiff(a, b):
    return (a - b + math.pi) % TAU - math.pi


def shade(c, k):
    return (min(255, int(c[0] * k)), min(255, int(c[1] * k)),
            min(255, int(c[2] * k)))


def lerpc(a, b, t):
    return (int(a[0] + (b[0] - a[0]) * t), int(a[1] + (b[1] - a[1]) * t),
            int(a[2] + (b[2] - a[2]) * t))


# ----------------------------------------------------------------------------
# World geometry
# ----------------------------------------------------------------------------
def _splits(lo, hi, step):
    n = max(1, int(math.ceil((hi - lo) / step - 1e-9)))
    return [lo + (hi - lo) * i / n for i in range(n + 1)]


FACESPEC = ((1, 1, (0, 1, 0), 0, 2), (1, 0, (0, -1, 0), 0, 2),
            (0, 1, (1, 0, 0), 2, 1), (0, 0, (-1, 0, 0), 2, 1),
            (2, 1, (0, 0, 1), 0, 1), (2, 0, (0, 0, -1), 0, 1))


def build_faces(b):
    lo = (b.x0, b.y0, b.z0)
    hi = (b.x1, b.y1, b.z1)
    out = []
    for fa, side, n, a, c in FACESPEC:
        fv = hi[fa] if side else lo[fa]
        k = FACE_K[n]
        tl = b.tile
        sa = _splits(lo[a], hi[a], tl)
        sc = _splits(lo[c], hi[c], tl)
        floor = n[1] > 0
        for i in range(len(sa) - 1):
            for j in range(len(sc) - 1):
                vs = []
                for u, v in ((sa[i], sc[j]), (sa[i + 1], sc[j]),
                             (sa[i + 1], sc[j + 1]), (sa[i], sc[j + 1])):
                    p = [0.0, 0.0, 0.0]
                    p[fa] = fv
                    p[a] = u
                    p[c] = v
                    vs.append((p[0], p[1], p[2]))
                kk = k * (0.92 if (b.checker and (i + j) & 1) else 1.0)
                cen = (sum(q[0] for q in vs) / 4, sum(q[1] for q in vs) / 4,
                       sum(q[2] for q in vs) / 4)
                out.append((vs, n, shade(b.col, kk), cen, floor))
    return out


class Box:
    """Axis-aligned block. move = (axis, amp, period, phase); axis in
    'x','y','z' or 'xz' (circular orbit)."""

    def __init__(self, x0, y0, z0, x1, y1, z1, col, kind='solid', move=None,
                 checker=True, coins=0, tile=TILE):
        self.tile = tile
        self.x0, self.x1 = min(x0, x1), max(x0, x1)
        self.y0, self.y1 = min(y0, y1), max(y0, y1)
        self.z0, self.z1 = min(z0, z1), max(z0, z1)
        self.col = col
        self.kind = kind
        self.move = move
        self.checker = checker
        self.coins = coins
        self.ox = self.oy = self.oz = 0.0
        self.dx = self.dy = self.dz = 0.0
        self.faces = build_faces(self)
        if move:
            self.update(0.0)
            self.dx = self.dy = self.dz = 0.0

    def update(self, t):
        if not self.move:
            return
        ax, amp, per, ph = self.move
        a = TAU * t / per + ph
        nx, ny, nz = self.ox, self.oy, self.oz
        if ax == 'x':
            nx = amp * math.sin(a)
        elif ax == 'y':
            ny = amp * math.sin(a)
        elif ax == 'z':
            nz = amp * math.sin(a)
        else:
            nx = amp * math.cos(a)
            nz = amp * math.sin(a)
        self.dx, self.dy, self.dz = nx - self.ox, ny - self.oy, nz - self.oz
        self.ox, self.oy, self.oz = nx, ny, nz

    def aabb(self):
        return (self.x0 + self.ox, self.y0 + self.oy, self.z0 + self.oz,
                self.x1 + self.ox, self.y1 + self.oy, self.z1 + self.oz)


class Enemy:
    def __init__(self, kind, x, y, z, rad=4.0, spd=2.0, period=4.0,
                 phase=0.0):
        self.kind = kind
        self.hx, self.hy, self.hz = x, y, z
        self.x, self.y, self.z = x, y, z
        self.rad = rad
        self.spd = spd
        self.period = period
        self.phase = phase
        self.alive = True
        self.dead_t = -1.0
        self.yaw = random.uniform(0, TAU)
        self.t = random.uniform(0.5, 2.0)
        self.anim = random.uniform(0, 5)

    def update(self, L, P, t):
        self.anim += DT
        if self.kind == 'spike':
            a = TAU * t / self.period + self.phase
            self.x = self.hx + self.rad * math.cos(a)
            self.z = self.hz + self.rad * math.sin(a)
            self.y = self.hy + 0.35 * math.sin(t * 3 + self.phase)
            return
        if self.dead_t >= 0:
            self.dead_t += DT
            if self.dead_t > 0.6:
                self.alive = False
            return
        dx, dz = P.x - self.x, P.z - self.z
        d = math.hypot(dx, dz)
        sp = self.spd
        if d < 7.0 and abs(P.y - self.y) < 3.0:
            self.yaw += clamp(angdiff(math.atan2(dx, dz), self.yaw),
                              -4 * DT, 4 * DT)
            sp *= 1.9
        else:
            self.t -= DT
            if self.t <= 0:
                self.yaw += random.uniform(-2.0, 2.0)
                self.t = random.uniform(1.0, 3.0)
            hd = math.hypot(self.x - self.hx, self.z - self.hz)
            if hd > self.rad:
                self.yaw = math.atan2(self.hx - self.x, self.hz - self.z)
        nx = self.x + math.sin(self.yaw) * sp * DT
        nz = self.z + math.cos(self.yaw) * sp * DT
        fy, fb = L.floor_below(nx, self.y + 0.5, nz)
        if fb is None or fb.kind == 'lava' or abs(fy - self.y) > 0.6:
            self.yaw += math.pi
        else:
            self.x, self.z, self.y = nx, nz, fy


class Level:
    def __init__(self, key, name, sky, horizon, kill_y=-25.0):
        self.key = key
        self.name = name
        self.sky = sky
        self.horizon = horizon
        self.kill_y = kill_y
        self.boxes = []
        self.coins = []        # [x, y, z, value, alive]
        self.gems = []         # dicts
        self.enemies = []
        self.portals = []
        self.signs = []
        self.spawn = (0.0, 0.0, 0.0, 0.0)
        self.coin_star = None

    # builders
    def box(self, x0, y0, z0, x1, y1, z1, col, kind='solid', move=None,
            checker=True, coins=0, tile=TILE):
        b = Box(x0, y0, z0, x1, y1, z1, col, kind, move, checker, coins, tile)
        self.boxes.append(b)
        return b

    def crate(self, x, y, z, s=1.6, coins=3):
        h = s / 2
        return self.box(x - h, y, z - h, x + h, y + s, z + h, CRATE, 'crate',
                        checker=False, coins=coins)

    def coin(self, x, y, z, v=1):
        self.coins.append([x, y, z, v, True])

    def ring(self, cx, y, cz, r, n, v=1):
        for i in range(n):
            a = TAU * i / n
            self.coin(cx + r * math.cos(a), y, cz + r * math.sin(a), v)

    def line(self, x0, z0, x1, z1, y, n, v=1):
        for i in range(n):
            t = i / max(1, n - 1)
            self.coin(x0 + (x1 - x0) * t, y, z0 + (z1 - z0) * t, v)

    def gem(self, idx, x, y, z, name, crate=None, coin=False):
        self.gems.append({'id': f"{self.key}:{idx}", 'x': x, 'y': y, 'z': z,
                          'name': name, 'crate': crate, 'coin': coin})

    def tree(self, x, z, y=0.0, h=3.0):
        self.box(x - 0.35, y, z - 0.35, x + 0.35, y + h, z + 0.35, WOOD,
                 checker=False)
        self.box(x - 1.4, y + h, z - 1.4, x + 1.4, y + h + 2.2, z + 1.4, LEAF)

    def walker(self, x, y, z, rad=4.0):
        self.enemies.append(Enemy('walker', x, y, z, rad=rad))

    def spike(self, x, y, z, rad, period, phase=0.0):
        self.enemies.append(Enemy('spike', x, y, z, rad=rad, period=period,
                                  phase=phase))

    def portal(self, x0, y0, z0, x1, y1, z1, target, req, col, exit_sp,
               normal):
        self.box(x0, y0, z0, x1, y1, z1, col, 'deco', checker=False)
        cx, cy, cz = (x0 + x1) / 2, (y0 + y1) / 2, (z0 + z1) / 2
        self.portals.append({'aabb': (x0, y0, z0, x1, y1, z1),
                             'target': target, 'req': req, 'col': col,
                             'exit': exit_sp, 'c': (cx, cy, cz),
                             'n': normal})

    def finalize(self):
        self.solid = [b for b in self.boxes if b.kind in SOLID_KINDS]
        self.dyn = [b for b in self.boxes if b.move or b.kind == 'crate']
        self.static = [f for b in self.boxes
                       if not (b.move or b.kind == 'crate') for f in b.faces]
        if np is not None and self.static:
            st = self.static
            self.V = np.array([f[0] for f in st], dtype=np.float32)
            self.N = np.array([f[1] for f in st], dtype=np.float32)
            self.COL = np.array([f[2] for f in st], dtype=np.float32)
            self.C = np.array([f[3] for f in st], dtype=np.float32)
            self.F = np.array([f[4] for f in st], dtype=bool)
        return self

    def floor_below(self, x, y, z):
        best = None
        by = -1e9
        for b in self.solid:
            x0, y0, z0, x1, y1, z1 = b.aabb()
            if x0 <= x <= x1 and z0 <= z <= z1 and by < y1 <= y + 0.3:
                by = y1
                best = b
        return by, best

    def inside_solid(self, x, y, z, m):
        for b in self.solid:
            x0, y0, z0, x1, y1, z1 = b.aabb()
            if (x0 - m < x < x1 + m and y0 - m < y < y1 + m
                    and z0 - m < z < z1 + m):
                return True
        return False

    def remove_box(self, b):
        for lst in (self.boxes, self.solid, self.dyn):
            if b in lst:
                lst.remove(b)


# ----------------------------------------------------------------------------
# Levels (all original layouts)
# ----------------------------------------------------------------------------
def build_hub():
    L = Level('hub', "Peach's Castle", (104, 168, 240), (196, 226, 255), -20)
    L.spawn = (0.0, 0.0, -30.0, 0.0)
    L.box(-45, -3, -45, 45, 0, 45, GRASS, tile=7.5)
    L.box(-3, 0, -40, 3, 0.25, -14, STONE)                 # path
    # castle walls (lobby courtyard)
    L.box(-14, 0, 12, 14, 9, 14, BRICK)                    # back
    L.box(-14, 0, -14, -12, 9, 14, BRICK)                  # left
    L.box(12, 0, -14, 14, 9, 14, BRICK)                    # right
    L.box(-14, 0, -14, -4, 9, -12, BRICK)                  # front L
    L.box(4, 0, -14, 14, 9, -12, BRICK)                    # front R
    L.box(-4, 6, -14, 4, 9, -12, BRICK)                    # gate arch
    for x in (-13, -9, -6, 6, 9, 13):                      # merlons
        L.box(x - 0.8, 9, -14, x + 0.8, 10, -12, BRICK)
    for sx in (-1, 1):                                     # towers
        for sz in (-1, 1):
            cx, cz = sx * 14, sz * 14
            L.box(cx - 3, 0, cz - 3, cx + 3, 13, cz + 3, STONE)
            L.box(cx - 3.5, 13, cz - 3.5, cx + 3.5, 14.5, cz + 3.5, ROOF)
            L.box(cx - 2, 14.5, cz - 2, cx + 2, 16.5, cz + 2, ROOF)
    # course paintings
    L.portal(-2.5, 1, 11.75, 2.5, 6, 12, 'hills', 0, (80, 200, 90),
             (0.0, 0.0, 9.0, math.pi), (0, 0, -1))
    L.portal(-12, 1, -2.5, -11.75, 6, 2.5, 'ember', 3, (240, 90, 40),
             (-9.0, 0.0, 0.0, math.pi / 2), (1, 0, 0))
    L.portal(11.75, 1, -2.5, 12, 6, 2.5, 'cloud', 8, (150, 180, 255),
             (9.0, 0.0, 0.0, -math.pi / 2), (-1, 0, 0))
    # central pillar + spiral stairs -> star 0
    L.box(-1.5, 0, -1.5, 1.5, 10, 1.5, STONE)
    for i, h in enumerate((1.5, 3.0, 4.5, 6.0, 7.5)):
        a = i * 1.2
        px, pz = 4.2 * math.cos(a), 4.2 * math.sin(a)
        L.box(px - 1.1, h - 0.5, pz - 1.1, px + 1.1, h, pz + 1.1, GOLD)
    L.gem(0, 0, 11, 0, "To the Top of the Tower")
    # wall-kick corridor behind castle -> star 1
    L.box(-3, 0, 17, 3, 10, 18, STONE)
    L.gem(1, 0, 10.2, 13, "Castle Secret Star")
    for (x, z) in ((-25, -25), (25, -25), (-30, 5), (30, 8), (-22, 30),
                   (24, 30), (-36, -8), (36, -14)):
        L.tree(x, z)
    L.ring(0, 0.8, 0, 7, 10)
    L.line(0, -38, 0, -18, 1.05, 6)
    L.crate(6, 0, -24)
    L.crate(-6, 0, -24)
    L.signs.append((0, -24, "Welcome to Peach's Castle! Power Stars unlock "
                    "the paintings. Press Esc for moves."))
    return L.finalize()


def build_hills():
    L = Level('hills', "Bob-omb Battlefield", (120, 190, 250), (210, 236, 255), -20)
    L.spawn = (0.0, 0.0, -34.0, 0.0)
    L.box(-40, -4, -40, 40, 0, 10, GRASS, tile=6.25)
    L.box(0, -4, 10, 40, 0, 40, GRASS, tile=6.25)
    L.box(-40, -4, 22, 0, 0, 40, GRASS, tile=6.25)
    L.box(-20, -0.5, 10, -17, 0, 22, WOOD)                 # bridge
    # stepped hill -> gem 0
    for i, (a, b2) in enumerate(((8, 26), (10, 24), (12, 22), (14, 20),
                                 (15.5, 18.5))):
        L.box(a, i * 1.5, a, b2, (i + 1) * 1.5, b2, DIRT if i % 2 else GRASS)
    L.gem(0, 17, 8.5, 17, "Big Bob-omb on the Summit")
    # shrine on far plateau -> star 1
    L.box(-30, 0, 30, -26, 2.5, 34, STONE)
    for (x, z) in ((-31, 29), (-25, 29), (-31, 35), (-25, 35)):
        L.box(x - 0.4, 0, z - 0.4, x + 0.4, 4.5, z + 0.4, STONE)
    L.gem(1, -28, 3.5, 32, "Footrace with Koopa the Quick")
    # lifts to floating isle -> star 2
    L.box(-14, 3.5, -28, -11, 4, -25, GOLD, move=('y', 2.5, 5.0, 0.0))
    L.box(-20, 7, -28, -17, 7.5, -25, GOLD, move=('x', 3.0, 6.0, 0.0))
    L.box(-30, 8, -31, -23, 9, -23, GRASS)
    L.gem(2, -26.5, 10, -27, "Shoot to the Island in the Sky")
    # wall-kick canyon -> star 3
    L.box(24, 0, -30, 25, 12, -18, STONE)
    L.box(28, 0, -30, 29, 12, -18, STONE)
    L.box(24, 12, -30, 29, 12.6, -27, STONE)
    L.gem(3, 26.5, 13.6, -28.5, "Find the 8 Red Coins")
    L.gem(4, 0, 1.5, -28, "Mario Wings to the Sky", coin=True)
    for (x, z) in ((-8, -30), (8, -32), (-34, -10), (34, 0), (-12, 34),
                   (6, 30), (-36, 26)):
        L.tree(x, z)
    for (x, z) in ((5, -10), (10, 0), (-10, -5), (25, 25), (-20, 30),
                   (-30, 36)):
        L.walker(x, 0, z)
    L.ring(0, 0.8, -15, 3, 8)
    L.line(-18.5, 11, -18.5, 21, 0.8, 6)
    L.ring(-26.5, 9.8, -27, 2, 6)
    L.line(0, -30, 0, -20, 0.8, 6)
    L.ring(-25, 0.8, 0, 4, 10)
    L.ring(30, 0.8, 30, 3, 8)
    for (x, y, z) in ((26.5, 6, -24), (-17, 9, -26.5), (11, 3.8, 11),
                      (-35, 0.8, 38)):
        L.coin(x, y, z, 2)
    L.coin(26.5, 13.3, -27.5, 5)
    L.crate(-5, 0, -22)
    L.crate(14, 0, -10)
    L.signs.append((2, -32, "Bob-omb Battlefield: hunt Power Stars. "
                    "50 coins make one appear."))
    return L.finalize()


def build_ember():
    L = Level('ember', "Lethal Lava Land", (60, 28, 36), (150, 60, 40), -15)
    L.spawn = (0.0, 1.0, -33.0, 0.0)
    L.box(-45, -3, -45, 45, -1, 45, LAVA, 'lava', checker=False, tile=15)
    L.box(-6, -3, -38, 6, 1, -26, BASALT)                  # start
    L.box(-1.5, -3, -23, 1.5, 1, -20, BASALT)
    L.box(-1.5, 0.5, -17, 1.5, 1, -14, STONE, move=('x', 2.0, 3.0, 0.0))
    L.box(-1.5, -3, -11, 1.5, 1.5, -8, BASALT)
    L.box(-12, -3, -6, 12, 2, 28, BASALT)                  # island
    # volcano -> gem 0
    L.box(-6, 2, 12, 6, 3.5, 24, ROCK)
    L.box(-4, 3.5, 14, 4, 5, 22, ROCK)
    L.box(-2, 5, 16, 2, 6.5, 20, ROCK)
    L.gem(0, 0, 7.5, 18, "Boil the Big Bully")
    L.spike(0, 2.6, 18, 8, 7)
    L.spike(0, 4.1, 18, 5, 5, 2)
    L.spike(0, 5.6, 18, 3, 4, 4)
    # east lava run -> star 1
    L.box(9, -3, -34, 12, 1, -31, BASALT)
    L.box(15, 0.5, -34, 18, 1, -31, STONE, move=('x', 2.0, 3.5, 0.0))
    L.box(22, -3, -34, 25, 2.5, -31, BASALT)
    L.box(27, -3, -34, 30, 4, -31, BASALT)
    L.box(32, -3, -35, 37, 5.5, -30, BASALT)
    L.gem(1, 34.5, 6.5, -32.5, "Bully the Bullies")
    # backflip ledge -> star 2
    L.box(-12, 2, 8, -8, 10, 10, ROCK)
    L.box(-12, 5.5, 4, -8, 6, 8, ROCK)
    L.gem(2, -10, 7, 6, "8-Coin Puzzle with 15 Pieces")
    # west gauntlet -> star 3
    for i, x in enumerate((-15.5, -20.5, -25.5)):
        L.box(x - 1.5, 0.7, -1.5, x + 1.5, 1.2, 1.5, STONE,
              move=('y', 1.2, 3.0, i * 2.0))
    L.box(-34, -3, -3, -29, 4, 3, BASALT)
    L.gem(3, -31.5, 5, 0, "Red-Hot Log Rolling")
    L.gem(4, 0, 3, 0, "Hot-Foot-It into the Volcano", coin=True)
    for (x, z) in ((-5, 0), (6, 4), (8, 25), (-8, 24)):
        L.walker(x, 2, z)
    L.spike(0, 1.8, -15.5, 2.5, 3)
    L.ring(0, 2.8, 4, 4, 8)
    L.line(0, -36, 0, -9, 1.9, 8)
    L.ring(0, 4.3, 18, 5.2, 10)
    L.line(9, -32.5, 36, -32.5, 3.2, 8)
    L.line(-14, 0, -30, 0, 3.0, 6)
    L.ring(8, 2.8, -3, 2.5, 6)
    for (x, y, z) in ((34.5, 6.3, -34), (-31.5, 4.8, 1.5), (0, 7.3, 16),
                      (10, 2.8, 26)):
        L.coin(x, y, z, 2)
    L.coin(-9, 6.8, 7, 5)
    L.crate(9, 2, 10)
    L.crate(-6, 2, -3)
    return L.finalize()


def build_cloud():
    L = Level('cloud', "Rainbow Ride", (150, 200, 255), (236, 246, 255), -25)
    L.spawn = (0.0, 0.0, -3.0, 0.0)
    L.box(-5, -1, -5, 5, 0, 5, CLOUD)
    L.box(-2, 0.5, 9, 2, 1, 13, CLOUD)
    L.box(-2, 2, 17, 2, 2.5, 21, CLOUD)
    L.box(-8, 3.5, 25, 8, 4, 41, CLOUD)                    # midway cloud
    # long-jump gap -> gem 1
    L.box(14.5, 3.5, 28, 22, 4, 38, CLOUD)
    L.gem(1, 18, 5, 33, "The Big House in the Sky")
    # windmill orbit -> star 2
    L.box(-12, 3.8, 31, -10, 4.3, 33, CLOUD)
    L.box(-22, -10, 30, -19, 6, 33, STONE)
    L.box(-22, 4, 30, -19, 4.5, 33, GOLD, move=('xz', 6.0, 7.0, 0.0))
    L.gem(2, -20.5, 7, 31.5, "Cruiser Crossing the Rainbow")
    # north spire helix -> star 0
    L.box(-3, -10, 48, 3, 20, 54, STONE)
    for i in range(10):
        h = 5.5 + 1.5 * i
        a = -math.pi / 2 + 0.85 * i
        px, pz = 5.5 * math.cos(a), 51 + 5.5 * math.sin(a)
        L.box(px - 1.1, h - 0.5, pz - 1.1, px + 1.1, h, pz + 1.1, CLOUD)
        L.coin(px, h + 0.8, pz)
    L.gem(0, 0, 21, 51, "Coaster on the Rainbow")
    # crate star -> star 3
    c = L.crate(4.8, 4, 37.8, coins=0)
    L.gem(3, 4.8, 4.8, 37.8, "Somewhere Over the Rainbow", crate=c)
    L.gem(4, 0, 5, 33, "Rainbow...Stars?", coin=True)
    L.walker(-4, 4, 30, 3)
    L.walker(4, 4, 32, 3)
    L.walker(19, 4, 30, 2.5)
    L.spike(0, 8, 51, 7, 6)
    L.spike(18, 5, 33, 2.5, 3)
    L.line(0, 9.5, 0, 12.5, 1.8, 3)
    L.line(0, 17.5, 0, 20.5, 3.3, 3)
    L.ring(0, 4.8, 33, 5, 10)
    L.ring(18, 4.8, 33, 3, 8)
    L.line(8.5, 33, 14, 33, 5.2, 4)
    for (x, y, z) in ((-20.5, 6.8, 30.5), (1.5, 20.8, 50), (21, 4.8, 37),
                      (-7, 4.8, 40)):
        L.coin(x, y, z, 2)
    L.coin(0, 4.8, 26, 5)
    L.crate(-5, 4, 38)
    L.crate(6, 4, 27)
    return L.finalize()


BUILDERS = {'hub': build_hub, 'hills': build_hills, 'ember': build_ember,
            'cloud': build_cloud}
COURSE_ORDER = ['hub', 'hills', 'ember', 'cloud']


# ----------------------------------------------------------------------------
# Renderer
# ----------------------------------------------------------------------------
_K0 = itemgetter(0)
CUBE_FACES = ((0, 1, 3, 2), (4, 5, 7, 6), (0, 1, 5, 4), (2, 3, 7, 6),
              (0, 2, 6, 4), (1, 3, 7, 5))


def clip_near(cs):
    out = []
    n = len(cs)
    for i in range(n):
        a = cs[i]
        b = cs[(i + 1) % n]
        ain = a[2] >= NEAR
        bin_ = b[2] >= NEAR
        if ain:
            out.append(a)
        if ain != bin_:
            t = (NEAR - a[2]) / (b[2] - a[2])
            out.append((a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t,
                        NEAR))
    return out


class Renderer:
    def __init__(self, surf):
        self.surf = surf
        self.items = []
        self.sky = (0, 0, 0)

    def set_camera(self, pos, yaw, pitch, sky):
        self.cx, self.cy, self.cz = pos
        cy, sy = math.cos(yaw), math.sin(yaw)
        cp, sp = math.cos(pitch), math.sin(pitch)
        self.f = (sy * cp, -sp, cy * cp)
        self.r = (cy, 0.0, -sy)
        self.u = (sy * sp, cp, cy * sp)
        self.sky = sky
        self.items = []

    def to_cam(self, p):
        dx, dy, dz = p[0] - self.cx, p[1] - self.cy, p[2] - self.cz
        r, u, f = self.r, self.u, self.f
        return (dx * r[0] + dz * r[2],
                dx * u[0] + dy * u[1] + dz * u[2],
                dx * f[0] + dy * f[1] + dz * f[2])

    def fogc(self, col, z):
        t = (z - FOG0) / (FAR - FOG0)
        if t <= 0:
            return col
        return lerpc(col, self.sky, min(1.0, t))

    def poly(self, verts, col, floor=False, bias=0.0, fog=True):
        cs = [self.to_cam(v) for v in verts]
        zs = [c[2] for c in cs]
        zmax = max(zs)
        if zmax <= NEAR:
            return
        zav = sum(zs) / len(zs)
        if min(zs) < NEAR:
            cs = clip_near(cs)
            if len(cs) < 3:
                return
        hw, hh = RW * 0.5, RH * 0.5
        pts = [(hw + c[0] * FOCAL / c[2], hh - c[1] * FOCAL / c[2])
               for c in cs]
        depth = (zmax if floor else zav) + bias
        self.items.append((depth, 0, pts, self.fogc(col, zav) if fog else col,
                           0))

    def faces(self, faces, ox=0.0, oy=0.0, oz=0.0):
        cx, cy, cz = self.cx, self.cy, self.cz
        far2 = FAR * FAR
        for vs, n, col, c, floor in faces:
            rx, ry, rz = c[0] + ox - cx, c[1] + oy - cy, c[2] + oz - cz
            if rx * n[0] + ry * n[1] + rz * n[2] >= 0:
                continue
            if rx * rx + ry * ry + rz * rz > far2:
                continue
            if ox or oy or oz:
                vs = [(v[0] + ox, v[1] + oy, v[2] + oz) for v in vs]
            self.poly(vs, col, floor)

    def static(self, L):
        if np is None or not hasattr(L, 'V'):
            self.faces(L.static)
            return
        cam = np.array((self.cx, self.cy, self.cz), dtype=np.float32)
        fv = np.array(self.f, dtype=np.float32)
        rv = np.array(self.r, dtype=np.float32)
        uv = np.array(self.u, dtype=np.float32)
        rel = L.C - cam
        mask = ((rel * L.N).sum(1) < 0) & ((rel * rel).sum(1) < FAR * FAR) \
            & ((rel @ fv) > -TILE)
        idx = np.nonzero(mask)[0]
        if not len(idx):
            return
        Vt = L.V[idx] - cam
        X = Vt @ rv
        Y = Vt @ uv
        Z = Vt @ fv
        zmin = Z.min(1)
        zmax = Z.max(1)
        full = zmin >= NEAR
        fi = np.nonzero(full)[0]
        if len(fi):
            Zf = Z[fi]
            sx = RW * 0.5 + X[fi] * FOCAL / Zf
            sy = RH * 0.5 - Y[fi] * FOCAL / Zf
            onscr = ((sx.max(1) >= 0) & (sx.min(1) < RW)
                     & (sy.max(1) >= 0) & (sy.min(1) < RH))
            if not onscr.all():
                keep = np.nonzero(onscr)[0]
                fi, Zf, sx, sy = fi[keep], Zf[keep], sx[keep], sy[keep]
            zav = Zf.mean(1)
            depth = np.where(L.F[idx[fi]], Zf.max(1), zav)
            t = np.clip((zav - FOG0) / (FAR - FOG0), 0.0, 1.0)[:, None]
            sky = np.array(self.sky, dtype=np.float32)
            cols = (L.COL[idx[fi]] * (1 - t) + sky * t).astype(np.int32)
            pts = np.stack((sx, sy), axis=2).tolist()
            app = self.items.append
            for d, p, c in zip(depth.tolist(), pts, cols.tolist()):
                app((d, 0, p, c, 0))
        part = np.nonzero((~full) & (zmax > NEAR))[0]
        for k in part.tolist():
            j = idx[k]
            self.poly([tuple(v) for v in L.V[j].tolist()],
                      tuple(int(c) for c in L.COL[j]), bool(L.F[j]))

    def cuboids(self, px, py, pz, yaw, flip, parts, pivot=0.75, squash=1.0):
        cyw, syw = math.cos(yaw), math.sin(yaw)
        cf, sf = math.cos(flip), math.sin(flip)
        cam = (self.cx, self.cy, self.cz)
        for lx, ly, lz, hx, hy, hz, col in parts:
            cs = []
            for dx in (-hx, hx):
                for dy in (-hy, hy):
                    for dz in (-hz, hz):
                        x, y, z = lx + dx, ly + dy - pivot, lz + dz
                        y, z = y * cf - z * sf, y * sf + z * cf
                        y = (y + pivot) * squash
                        cs.append((px + x * cyw + z * syw, py + y,
                                   pz - x * syw + z * cyw))
            ccx = sum(c[0] for c in cs) / 8
            ccy = sum(c[1] for c in cs) / 8
            ccz = sum(c[2] for c in cs) / 8
            for fi in CUBE_FACES:
                vs = [cs[i] for i in fi]
                fx = (vs[0][0] + vs[2][0]) * 0.5
                fy = (vs[0][1] + vs[2][1]) * 0.5
                fz = (vs[0][2] + vs[2][2]) * 0.5
                nx, ny, nz = fx - ccx, fy - ccy, fz - ccz
                if (nx * (fx - cam[0]) + ny * (fy - cam[1])
                        + nz * (fz - cam[2])) >= 0:
                    continue
                ln = math.sqrt(nx * nx + ny * ny + nz * nz) or 1.0
                k = 0.55 + 0.5 * max(0.0, (nx * LIGHT[0] + ny * LIGHT[1]
                                           + nz * LIGHT[2]) / ln)
                self.poly(vs, shade(col, k))

    def circle(self, p, radius, col, bias=0.0, outline=None):
        c = self.to_cam(p)
        if c[2] < NEAR or c[2] > FAR:
            return
        r = max(1, int(radius * FOCAL / c[2]))
        sp = (RW * 0.5 + c[0] * FOCAL / c[2], RH * 0.5 - c[1] * FOCAL / c[2])
        self.items.append((c[2] + bias, 1, sp, self.fogc(col, c[2]),
                           (r, outline)))

    def ellipse(self, p, radius, sx, col, outline):
        c = self.to_cam(p)
        if c[2] < NEAR or c[2] > FAR:
            return
        r = radius * FOCAL / c[2]
        sp = (RW * 0.5 + c[0] * FOCAL / c[2], RH * 0.5 - c[1] * FOCAL / c[2])
        self.items.append((c[2], 2, sp, self.fogc(col, c[2]),
                           (max(2, r * 2 * sx), max(2, r * 2), outline)))

    def gem(self, p, radius, spin, col):
        c = self.to_cam(p)
        if c[2] < NEAR or c[2] > FAR:
            return
        r = radius * FOCAL / c[2]
        sx, sy = (RW * 0.5 + c[0] * FOCAL / c[2],
                  RH * 0.5 - c[1] * FOCAL / c[2])
        w = max(0.18, abs(math.cos(spin)))
        outer = [(sx, sy - r * 1.25), (sx + r * w, sy - r * 0.3),
                 (sx + r * 0.6 * w, sy + r), (sx - r * 0.6 * w, sy + r),
                 (sx - r * w, sy - r * 0.3)]
        inner = [(sx, sy - r * 0.8), (sx + r * 0.45 * w, sy - r * 0.2),
                 (sx, sy + r * 0.6), (sx - r * 0.45 * w, sy - r * 0.2)]
        self.items.append((c[2], 0, outer, shade(col, 0.75), 0))
        self.items.append((c[2] - 0.01, 0, inner, shade(col, 1.25), 0))

    def flush(self):
        self.items.sort(key=_K0, reverse=True)
        surf = self.surf
        dpoly = pygame.draw.polygon
        dcirc = pygame.draw.circle
        dell = pygame.draw.ellipse
        for it in self.items:
            t = it[1]
            if t == 0:
                if len(it[2]) >= 3:
                    dpoly(surf, it[3], it[2])
            elif t == 1:
                r, ol = it[4]
                dcirc(surf, it[3], it[2], r)
                if ol:
                    dcirc(surf, ol, it[2], r, 1)
            else:
                w, h, ol = it[4]
                rect = pygame.Rect(0, 0, int(w), int(h))
                rect.center = (int(it[2][0]), int(it[2][1]))
                dell(surf, it[3], rect)
                if ol and w > 3:
                    dell(surf, ol, rect, 1)
        self.items = []


# ----------------------------------------------------------------------------
# Audio (synthesized at startup: no external files)
# ----------------------------------------------------------------------------
class Audio:
    def __init__(self, enabled=True):
        self.ok = False
        self.sfx = {}
        self.music = {}
        self.cur = None
        if not enabled:
            return
        try:
            if not pygame.mixer.get_init():
                pygame.mixer.init(22050, -16, 1, 512)
            self.sr, _, self.ch = pygame.mixer.get_init()
            self.ok = True
        except Exception:
            return
        try:
            self._build()
        except Exception:
            self.ok = False

    def _mk(self, samples):
        if np is not None:
            a = (np.clip(np.asarray(samples, dtype=np.float32), -1, 1)
                 * 32000).astype(np.int16)
            if self.ch == 2:
                a = np.repeat(a, 2)
            return pygame.mixer.Sound(buffer=a.tobytes())
        a = array('h', (int(max(-1.0, min(1.0, v)) * 32000) for v in samples))
        if self.ch == 2:
            b = array('h')
            for v in a:
                b.append(v)
                b.append(v)
            a = b
        return pygame.mixer.Sound(buffer=a.tobytes())

    def _tone(self, f0, f1, dur, wave='sq', vol=0.25, decay=1.5):
        n = max(1, int(self.sr * dur))
        out = []
        ph = 0.0
        rnd = random.Random(7)
        for i in range(n):
            t = i / n
            f = f0 + (f1 - f0) * t
            ph += f / self.sr
            if wave == 'sq':
                w = 1.0 if (ph % 1.0) < 0.5 else -1.0
            elif wave == 'tri':
                w = 4 * abs((ph % 1.0) - 0.5) - 1
            elif wave == 'noise':
                w = rnd.uniform(-1, 1)
            else:
                w = math.sin(TAU * ph)
            out.append(w * vol * (1 - t) ** decay)
        return out

    def _build(self):
        T = self._tone
        s = self.sfx
        s['jump'] = self._mk(T(330, 620, 0.12, 'sq', 0.18))
        s['jump2'] = self._mk(T(390, 760, 0.13, 'sq', 0.18))
        s['jump3'] = self._mk(T(440, 990, 0.2, 'sq', 0.2))
        s['long'] = self._mk(T(300, 700, 0.22, 'tri', 0.3))
        s['coin'] = self._mk(T(988, 988, 0.05, 'sq', 0.15, 0)
                             + T(1319, 1319, 0.22, 'sq', 0.15))
        s['gem'] = self._mk(sum((T(f, f, 0.09, 'sq', 0.18, 0.3)
                                 for f in (523, 659, 784, 1047, 1319)), [])
                            + T(1568, 1568, 0.5, 'tri', 0.3))
        s['hurt'] = self._mk(T(320, 90, 0.3, 'sq', 0.22))
        s['stomp'] = self._mk(T(200, 520, 0.09, 'sq', 0.2))
        s['land'] = self._mk(T(140, 60, 0.06, 'sine', 0.35))
        s['gp'] = self._mk(T(700, 90, 0.25, 'tri', 0.35))
        s['dive'] = self._mk(T(250, 520, 0.12, 'tri', 0.3))
        s['wall'] = self._mk(T(500, 900, 0.1, 'sq', 0.18))
        s['warp'] = self._mk(T(200, 1300, 0.45, 'tri', 0.3))
        s['crate'] = self._mk(T(0, 0, 0.18, 'noise', 0.3, 2.5))
        s['die'] = self._mk(T(600, 100, 0.9, 'sq', 0.22, 0.8))
        s['punch'] = self._mk(T(180, 120, 0.06, 'noise', 0.25))
        s['select'] = self._mk(T(660, 660, 0.06, 'sq', 0.15))
        if np is not None:
            seeds = {'hub': (72, 0, 1), 'hills': (96, 2, 2),
                     'ember': (84, 9, 3), 'cloud': (88, 5, 4)}
            for k, (bpm, root, seed) in seeds.items():
                self.music[k] = self._mk(self._song(bpm, root, seed))

    def _song(self, bpm, root, seed):
        rng = random.Random(seed * 1013)
        sr = self.sr
        step = 60.0 / bpm / 2
        scale = [0, 2, 4, 7, 9, 12, 14, 16]
        n_steps = 64
        total = int(sr * step * n_steps)
        buf = np.zeros(total, dtype=np.float32)
        base = 261.63 * 2 ** (root / 12)
        mel = []
        idx = 3
        for i in range(n_steps):
            if i % 16 == 0:
                motif = [rng.choice((-2, -1, 0, 1, 1, 2)) for _ in range(8)]
            idx = clamp(idx + motif[i % 8], 0, len(scale) - 1)
            mel.append(None if rng.random() < 0.18 else scale[idx])
        prog = [0, 5, 7, 4]
        for i in range(n_steps):
            s0 = int(i * step * sr)
            n = int(step * sr)
            t = np.arange(n) / sr
            env = np.exp(-t * 7)
            if mel[i] is not None:
                f = base * 2 ** (mel[i] / 12)
                w = np.where((t * f) % 1.0 < 0.25, 1.0, -1.0)
                buf[s0:s0 + n] += (w * env * 0.07).astype(np.float32)
            if i % 2 == 0:
                fb = base / 2 * 2 ** (prog[(i // 16) % 4] / 12)
                tri = 4 * np.abs((t * fb) % 1.0 - 0.5) - 1
                buf[s0:s0 + n] += (tri * np.exp(-t * 3) * 0.13).astype(
                    np.float32)
            if i % 4 == 2:
                m = min(n, int(sr * 0.04))
                buf[s0:s0 + m] += (np.random.RandomState(i).uniform(-1, 1, m)
                                   * np.linspace(0.08, 0, m)).astype(
                    np.float32)
        return buf

    def play(self, name):
        if self.ok and name in self.sfx:
            try:
                self.sfx[name].play()
            except Exception:
                pass

    def music_play(self, key):
        if not self.ok or key == self.cur:
            return
        self.cur = key
        try:
            pygame.mixer.Channel(0).stop()
            if key in self.music:
                pygame.mixer.Channel(0).play(self.music[key], loops=-1)
        except Exception:
            pass


# ----------------------------------------------------------------------------
# Input
# ----------------------------------------------------------------------------
class Input:
    def __init__(self):
        self.mx = self.mz = 0.0
        self.jump_h = self.crouch_h = False
        self.cam = 0.0
        self.clear()

    def clear(self):
        self.jump_p = self.crouch_p = self.act_p = False
        self.start_p = self.pause_p = self.up_p = self.down_p = False
        self.back_p = False
        self.mdx = 0.0
        self.zoom = 0


# ----------------------------------------------------------------------------
# Player: Mario (Nintendo SM64 palette — fan recreation)
# ----------------------------------------------------------------------------
SKIN = (255, 204, 170)
HAT = (220, 40, 40)
OVERALL = (40, 80, 220)
SHIRT = (220, 40, 40)
BOOT = (90, 45, 25)
GLOVE = (245, 245, 245)
EYE = (30, 30, 40)
MUST = (70, 40, 20)
BUTTON = (255, 220, 40)


class Player:
    R = 0.35
    HGT = 1.5

    def __init__(self):
        self.reset((0.0, 0.0, 0.0, 0.0))

    def reset(self, sp):
        self.x, self.y, self.z, self.yaw = sp
        self.vx = self.vy = self.vz = 0.0
        self.spd = 0.0
        self.state = 'air'
        self.jkind = 'fall'
        self.ground = None
        self.jump_n = 0
        self.land_t = 1.0
        self.wall_t = 0.0
        self.wall_n = (0.0, 0.0)
        self.jbuf = 0.0
        self.timer = 0.0
        self.flip = 0.0
        self.flip_rate = 0.0
        self.inv = 0.0
        self.anim = 0.0
        self.cut = False
        self.squash = 1.0

    def hspeed(self):
        return math.hypot(self.vx, self.vz)

    # -- per-tick ---------------------------------------------------------
    def update(self, inp, L, G):
        self.inv = max(0.0, self.inv - DT)
        self.land_t += DT
        self.wall_t = max(0.0, self.wall_t - DT)
        self.jbuf = max(0.0, self.jbuf - DT)
        self.squash = approach(self.squash, 1.0, 3 * DT)
        self.anim += DT * (2 + self.spd * 0.9)
        g = self.ground
        if g is not None and g.move and self.state in GROUNDED:
            self.x += g.dx
            self.y += g.dy
            self.z += g.dz
        mag = min(1.0, math.hypot(inp.mx, inp.mz))
        cy, sy = math.cos(G.cam.yaw), math.sin(G.cam.yaw)
        wx = inp.mx * cy + inp.mz * sy
        wz = -inp.mx * sy + inp.mz * cy
        tyaw = math.atan2(wx, wz) if mag > 0.05 else self.yaw

        st = self.state
        if st in ('ground', 'crouch'):
            self._ground(inp, mag, tyaw, G)
        elif st == 'slide':
            self.spd = approach(self.spd, 0, 10 * DT)
            self.timer += DT
            self.vx = math.sin(self.yaw) * self.spd
            self.vz = math.cos(self.yaw) * self.spd
            self.vy = -2.0
            if (inp.jump_p or inp.act_p) and self.timer > 0.1:
                self.state = 'air'
                self.jkind = 'roll'
                self.vy = 9.0
                self.flip_rate = TAU / 0.5
                self.ground = None
                G.snd.play('jump')
            elif self.spd < 0.6 and self.timer > 0.35:
                self.state = 'ground'
        elif st == 'punch':
            self.timer -= DT
            self.spd = approach(self.spd, 0, 30 * DT)
            self.vx = math.sin(self.yaw) * self.spd
            self.vz = math.cos(self.yaw) * self.spd
            self.vy = -2.0
            if self.timer <= 0:
                self.state = 'ground'
        elif st == 'air':
            self._air(inp, mag, tyaw, G)
        elif st == 'gp_wind':
            self.vx = self.vz = self.vy = 0.0
            self.timer -= DT
            self.flip += TAU / 0.3 * DT
            if self.timer <= 0:
                self.state = 'gp'
                self.vy = -30.0
                self.flip = 0.0
        elif st == 'gp':
            self.vx = self.vz = 0.0
        elif st in ('hurt', 'burnt'):
            self.timer -= DT
            if self.timer <= 0:
                self.state = 'air'
                self.jkind = 'fall'

        if self.state in AIRBORNE:
            self.vy = max(TERM, self.vy - GRAV * DT)
        if self.flip_rate:
            self.flip += self.flip_rate * DT
            if abs(self.flip) >= TAU:
                self.flip = 0.0
                self.flip_rate = 0.0

        landed, wall = self._collide(L)

        if landed is not None:
            self.ground = landed
            if landed.kind == 'lava':
                G.lava_hit()
                return
            if self.state in AIRBORNE:
                self._land(G, landed)
        else:
            if self.state in GROUNDED:
                self.state = 'air'
                self.jkind = 'fall'
            self.ground = None

        if wall is not None:
            if self.state == 'air' and self.hspeed() + 4 > 2.5:
                self.wall_t = 0.2
                self.wall_n = wall
                if self.jbuf > 0:
                    self._wallkick(G)
            elif self.state == 'dive':
                self.vx = wall[0] * 2
                self.vz = wall[1] * 2
                self.state = 'hurt'
                self.timer = 0.3
            elif self.state == 'ground':
                if (math.sin(self.yaw) * wall[0]
                        + math.cos(self.yaw) * wall[1]) < -0.7:
                    self.spd = 0.0

    def _ground(self, inp, mag, tyaw, G):
        crouch = inp.crouch_h
        self.state = 'crouch' if crouch else 'ground'
        if crouch:
            self.spd = approach(self.spd, 0, 16 * DT)
        elif mag > 0.15:
            d = angdiff(tyaw, self.yaw)
            if abs(d) > 2.5 and self.spd > 6:
                self.spd = approach(self.spd, 0, 45 * DT)
                if self.spd < 1.5:
                    self.yaw = tyaw
            else:
                turn = (16.0 if self.spd < 4 else 8.0) * DT
                self.yaw += clamp(d, -turn, turn)
                tgt = RUN * mag
                self.spd = approach(self.spd, tgt,
                                    (20.0 if self.spd < tgt else 12.0) * DT)
        else:
            self.spd = approach(self.spd, 0, 30 * DT)
        fx, fz = math.sin(self.yaw), math.cos(self.yaw)
        self.vx, self.vz, self.vy = fx * self.spd, fz * self.spd, -2.0
        if inp.jump_p:
            self.ground = None
            self.cut = False
            if crouch:
                if self.spd > 3.0:
                    self.jkind = 'long'
                    self.vy = 9.5
                    self.vx, self.vz = fx * 13.5, fz * 13.5
                    G.snd.play('long')
                else:
                    self.jkind = 'back'
                    self.vy = 17.0
                    self.vx, self.vz = -fx * 3.0, -fz * 3.0
                    self.flip_rate = -TAU / 0.85
                    G.snd.play('jump3')
            else:
                if self.land_t < 0.25 and self.jump_n == 2 and self.spd > 4.5:
                    self.jkind = 'triple'
                    self.vy = 16.5
                    self.flip_rate = TAU / 0.7
                    G.snd.play('jump3')
                elif self.land_t < 0.25 and self.jump_n == 1:
                    self.jkind = 'double'
                    self.vy = 13.5
                    G.snd.play('jump2')
                else:
                    self.jkind = 'single'
                    self.vy = 11.0
                    G.snd.play('jump')
            self.state = 'air'
            self.jump_n = 0
        elif inp.act_p:
            if self.spd > 4.5:
                sp = min(self.spd + 4.0, 15.0)
                self.state = 'dive'
                self.vx, self.vz = fx * sp, fz * sp
                self.vy = 5.0
                self.ground = None
                G.snd.play('dive')
            else:
                self.state = 'punch'
                self.timer = 0.28
                G.punch(self)

    def _air(self, inp, mag, tyaw, G):
        hs = self.hspeed()
        if mag > 0.15:
            self.vx += math.sin(tyaw) * mag * AIRACC * DT
            self.vz += math.cos(tyaw) * mag * AIRACC * DT
            nhs = self.hspeed()
            cap = max(hs, AIRMAX)
            if nhs > cap:
                self.vx *= cap / nhs
                self.vz *= cap / nhs
        if self.jkind != 'back' and hs > 1.0:
            self.yaw += clamp(angdiff(math.atan2(self.vx, self.vz), self.yaw),
                              -6 * DT, 6 * DT)
        if (not inp.jump_h and not self.cut and self.vy > 3
                and self.jkind in ('single', 'double')):
            self.vy *= 0.5
            self.cut = True
        if inp.jump_p:
            if self.wall_t > 0:
                self._wallkick(G)
            else:
                self.jbuf = 0.12
        elif inp.crouch_p:
            self.state = 'gp_wind'
            self.timer = 0.3
            self.flip = 0.0
            self.flip_rate = 0.0
        elif inp.act_p:
            sp = min(max(hs, 6.0) + 3.0, 15.0)
            self.state = 'dive'
            self.vx = math.sin(self.yaw) * sp
            self.vz = math.cos(self.yaw) * sp
            self.vy = max(self.vy, 3.0)
            self.flip = 0.0
            self.flip_rate = 0.0
            G.snd.play('dive')

    def _wallkick(self, G):
        nx, nz = self.wall_n
        self.yaw = math.atan2(nx, nz)
        self.vx, self.vz = nx * 7.5, nz * 7.5
        self.vy = 13.5
        self.jkind = 'wallkick'
        self.wall_t = 0.0
        self.jbuf = 0.0
        self.cut = True
        self.flip = 0.0
        self.flip_rate = 0.0
        self.state = 'air'
        G.snd.play('wall')
        G.puff(self.x - nx * 0.4, self.y + 0.8, self.z - nz * 0.4, 5)

    def _land(self, G, b):
        st = self.state
        hs = self.hspeed()
        self.flip = 0.0
        self.flip_rate = 0.0
        if st == 'dive':
            self.state = 'slide'
            self.spd = hs
            self.timer = 0.0
            G.snd.play('land')
            return
        if st == 'gp':
            self.state = 'punch'
            self.timer = 0.3
            self.spd = 0.0
            G.ground_pound_land(self, b)
            return
        if st in ('hurt', 'burnt'):
            self.state = 'ground'
            self.spd = 0.0
            return
        if self.vy < -12 or self.jkind in ('triple', 'back', 'long'):
            G.snd.play('land')
        self.squash = 0.72
        self.jump_n = {'single': 1, 'double': 2}.get(self.jkind, 0)
        self.land_t = 0.0
        along = self.vx * math.sin(self.yaw) + self.vz * math.cos(self.yaw)
        self.spd = clamp(along, 0.0, 14.0)
        self.state = 'ground'

    def _collide(self, L):
        r, h = self.R, self.HGT
        landed = None
        wall = None
        grounded = self.state in GROUNDED
        boxes = L.solid
        # X axis
        self.x += self.vx * DT
        for b in boxes:
            x0, y0, z0, x1, y1, z1 = b.aabb()
            if (self.x + r > x0 and self.x - r < x1 and self.z + r > z0
                    and self.z - r < z1 and self.y + h > y0
                    and self.y < y1 - 1e-6):
                if grounded and y1 - self.y <= STEP:
                    self.y = y1
                    continue
                if self.vx > 0:
                    self.x = x0 - r - 1e-4
                    wall = (-1.0, 0.0)
                elif self.vx < 0:
                    self.x = x1 + r + 1e-4
                    wall = (1.0, 0.0)
                else:
                    if self.x < (x0 + x1) / 2:
                        self.x = x0 - r - 1e-4
                    else:
                        self.x = x1 + r + 1e-4
                self.vx = 0.0
        # Z axis
        self.z += self.vz * DT
        for b in boxes:
            x0, y0, z0, x1, y1, z1 = b.aabb()
            if (self.x + r > x0 and self.x - r < x1 and self.z + r > z0
                    and self.z - r < z1 and self.y + h > y0
                    and self.y < y1 - 1e-6):
                if grounded and y1 - self.y <= STEP:
                    self.y = y1
                    continue
                if self.vz > 0:
                    self.z = z0 - r - 1e-4
                    wall = (0.0, -1.0)
                elif self.vz < 0:
                    self.z = z1 + r + 1e-4
                    wall = (0.0, 1.0)
                else:
                    if self.z < (z0 + z1) / 2:
                        self.z = z0 - r - 1e-4
                    else:
                        self.z = z1 + r + 1e-4
                self.vz = 0.0
        # Y axis
        oy = self.y
        self.y += self.vy * DT
        best = -1e9
        for b in boxes:
            x0, y0, z0, x1, y1, z1 = b.aabb()
            if (self.x + r > x0 and self.x - r < x1 and self.z + r > z0
                    and self.z - r < z1 and self.y + h > y0
                    and self.y < y1):
                if self.vy <= 0 and oy >= y1 - 0.5:
                    if y1 > best:
                        best = y1
                        landed = b
                elif self.vy > 0 and oy + h <= y0 + 0.25:
                    self.y = y0 - h - 1e-4
                    self.vy = 0.0
                elif y1 - self.y < 0.6:
                    if y1 > best:
                        best = y1
                        landed = b
        if landed is not None:
            self.y = best
            self.vy = 0.0
        return landed, wall

    # -- drawing -----------------------------------------------------------
    def parts(self):
        st = self.state
        run = st == 'ground' and self.spd > 0.5
        sw = math.sin(self.anim * 2.2) * (0.22 if run else 0.0)
        air = st in ('air',)
        legz = 0.12 if air else 0.0
        arm_y = 0.95 if air and self.vy > 0 else 0.72
        p = [
            (-0.14, 0.22, sw + legz, 0.1, 0.22, 0.12, BOOT),
            (0.14, 0.22, -sw + legz, 0.1, 0.22, 0.12, BOOT),
            (0, 0.55, 0, 0.22, 0.18, 0.16, OVERALL),           # legs
            (0, 0.78, 0, 0.28, 0.22, 0.2, OVERALL),            # torso
            (0, 0.95, 0, 0.26, 0.1, 0.18, SHIRT),              # shirt
            (-0.12, 0.78, 0.12, 0.04, 0.04, 0.02, BUTTON),
            (0.12, 0.78, 0.12, 0.04, 0.04, 0.02, BUTTON),
            (0, 1.14, 0.02, 0.24, 0.2, 0.22, SKIN),            # head
            (0, 1.08, 0.22, 0.16, 0.06, 0.04, MUST),           # mustache
            (-0.09, 1.2, 0.24, 0.045, 0.06, 0.01, EYE),
            (0.09, 1.2, 0.24, 0.045, 0.06, 0.01, EYE),
            (0, 1.36, 0.0, 0.28, 0.1, 0.26, HAT),              # cap
            (0, 1.3, 0.28, 0.12, 0.04, 0.08, HAT),             # brim
            (-0.34, arm_y, -sw * 0.8, 0.07, 0.18, 0.08, SHIRT),
            (0.34, arm_y, sw * 0.8, 0.07, 0.18, 0.08, SHIRT),
            (-0.34, arm_y - 0.22, -sw * 0.8, 0.07, 0.08, 0.08, GLOVE),
            (0.34, arm_y - 0.22, sw * 0.8, 0.07, 0.08, 0.08, GLOVE),
        ]
        if st == 'punch' and self.timer > 0.1:
            p[14] = (0.3, 0.8, 0.35, 0.08, 0.08, 0.2, SHIRT)
            p[16] = (0.35, 0.75, 0.5, 0.08, 0.08, 0.08, GLOVE)
        return p

    def draw(self, R):
        if self.inv > 0 and int(self.inv * 20) % 2 == 0:
            return
        flip = self.flip
        squash = self.squash
        st = self.state
        if st in ('dive', 'slide'):
            flip = math.pi / 2 - 0.2
        elif st == 'crouch':
            squash = 0.7
        elif st == 'hurt' or st == 'burnt':
            flip = -0.6
        R.cuboids(self.x, self.y, self.z, self.yaw, flip, self.parts(),
                  pivot=0.75 if st not in ('dive', 'slide') else 0.25,
                  squash=squash)


# ----------------------------------------------------------------------------
# Camera
# ----------------------------------------------------------------------------
class Camera:
    def __init__(self):
        self.yaw = 0.0
        self.pitch = 0.36
        self.dist = 10.0
        self.cd = 10.0
        self.tgt = [0.0, 0.0, 0.0]
        self.pos = (0.0, 5.0, -10.0)
        self.manual_t = 0.0

    def snap(self, P, yaw):
        self.yaw = yaw
        self.tgt = [P.x, P.y + 1.3, P.z]
        self.cd = self.dist
        self._place(None)

    def forward(self):
        cp = math.cos(self.pitch)
        return (math.sin(self.yaw) * cp, -math.sin(self.pitch),
                math.cos(self.yaw) * cp)

    def _place(self, L):
        f = self.forward()
        d = self.dist
        if L is not None:
            n = 12
            for i in range(1, n + 1):
                t = d * i / n
                if L.inside_solid(self.tgt[0] - f[0] * t,
                                  self.tgt[1] - f[1] * t,
                                  self.tgt[2] - f[2] * t, 0.25):
                    d = max(1.2, t - d / n - 0.2)
                    break
        if d < self.cd:
            self.cd = d
        else:
            self.cd += (d - self.cd) * min(1.0, 3 * DT)
        self.pos = (self.tgt[0] - f[0] * self.cd, self.tgt[1] - f[1] * self.cd,
                    self.tgt[2] - f[2] * self.cd)

    def update(self, P, L, inp):
        rot = inp.cam * 2.6 * DT + inp.mdx * 0.006
        if rot:
            self.yaw += rot
            self.manual_t = 1.2
        if inp.zoom:
            self.dist = clamp(self.dist - inp.zoom * 1.0, 5.0, 18.0)
        self.manual_t -= DT
        hs = P.hspeed()
        if self.manual_t <= 0 and hs > 2 and P.state in ('ground', 'air'):
            d = angdiff(P.yaw, self.yaw)
            if abs(d) < 2.0:
                self.yaw += d * min(1.0, DT * 0.9)
        self.tgt[0] += (P.x - self.tgt[0]) * min(1.0, 12 * DT)
        self.tgt[2] += (P.z - self.tgt[2]) * min(1.0, 12 * DT)
        ty = P.y + 1.3
        rate = 6.0 if P.state in GROUNDED else 2.5
        if ty < self.tgt[1] - 2:
            rate = 8.0
        self.tgt[1] += (ty - self.tgt[1]) * min(1.0, rate * DT)
        self._place(L)

    def orbit(self, t):
        self.yaw = t * 0.12
        self.pitch = 0.3
        self.tgt = [0.0, 5.0, 0.0]
        f = self.forward()
        self.pos = (-f[0] * 34, 5 - f[1] * 34, -f[2] * 34)


# ----------------------------------------------------------------------------
# Save
# ----------------------------------------------------------------------------
def load_save():
    try:
        with open(SAVE_PATH, 'r', encoding='utf-8') as fh:
            d = json.load(fh)
        d.setdefault('gems', [])
        d.setdefault('best', {})
        return d
    except Exception:
        return {'gems': [], 'best': {}}


def write_save(d):
    try:
        with open(SAVE_PATH, 'w', encoding='utf-8') as fh:
            json.dump(d, fh, indent=1)
    except Exception:
        pass


# ----------------------------------------------------------------------------
# Game
# ----------------------------------------------------------------------------
STAR_NAMES = {}
for _k, _b in BUILDERS.items():
    STAR_NAMES[_k] = [g['name'] for g in _b().gems]


class Game:
    def __init__(self, screen, audio=True):
        self.screen = screen
        self.rs = pygame.Surface((RW, RH))
        self.R = Renderer(self.rs)
        self.snd = Audio(audio)
        self.save = load_save()
        self.player = Player()
        self.cam = Camera()
        self.font_big = pygame.font.Font(None, 84)
        self.font = pygame.font.Font(None, 40)
        self.font_s = pygame.font.Font(None, 28)
        self.mode = 'title'
        self.t = 0.0
        self.gt = 0.0
        self.lives = 4
        self.health = MAX_HP
        self.coins = 0
        self.msg = ''
        self.msg_t = 0.0
        self.banner = ''
        self.banner_t = 0.0
        self.fade = 0.0
        self.fade_dir = 0
        self.pending = None
        self.return_exit = None
        self.mode_t = 0.0
        self.menu_i = 0
        self.show_fps = False
        self.fps_val = 0.0
        self.shake = 0.0
        self.particles = []
        self.sky_cache = {}
        self.load_level('hub', None)

    # -- levels ------------------------------------------------------------
    def load_level(self, key, spawn):
        self.L = BUILDERS[key]()
        self.t = 0.0
        self.coins = 0
        self.coin_star_shown = False
        self.particles = []
        sp = spawn or self.L.spawn
        self.player.reset(sp)
        self.cam.snap(self.player, sp[3])
        self.banner = self.L.name
        self.banner_t = 2.5
        self.msg = ''
        self.msg_t = 0.0
        self.snd.music_play(key)

    def warp(self, key, spawn):
        if self.fade_dir:
            return
        self.fade_dir = 1
        self.pending = (key, spawn)
        self.snd.play('warp')

    def star_count(self):
        return len(self.save['gems'])

    def say(self, text, t=2.5):
        self.msg = text
        self.msg_t = t

    def puff(self, x, y, z, n, col=(250, 250, 250)):
        for _ in range(n):
            self.particles.append([x, y, z, random.uniform(-3, 3),
                                   random.uniform(1, 5), random.uniform(-3, 3),
                                   random.uniform(0.3, 0.6), col])

    # -- events from player -------------------------------------------------
    def hurt(self, n, sx, sz):
        P = self.player
        if P.inv > 0 or self.mode != 'play':
            return
        self.health -= n
        P.inv = 1.6
        dx, dz = P.x - sx, P.z - sz
        d = math.hypot(dx, dz) or 1.0
        P.vx, P.vz = dx / d * 6, dz / d * 6
        P.vy = 8.0
        P.state = 'hurt'
        P.timer = 0.5
        P.ground = None
        self.snd.play('hurt')
        if self.health <= 0:
            self.die()

    def lava_hit(self):
        P = self.player
        P.state = 'burnt'
        P.timer = 1.0
        P.vy = 19.0
        P.vx *= 0.3
        P.vz *= 0.3
        P.ground = None
        self.puff(P.x, P.y, P.z, 10, (255, 160, 40))
        if P.inv <= 0:
            self.health -= 3
            P.inv = 1.6
            self.snd.play('hurt')
            if self.health <= 0:
                self.die()

    def die(self):
        if self.mode != 'play':
            return
        self.mode = 'dying'
        self.mode_t = 1.6
        self.snd.play('die')

    def kill_enemy(self, e):
        e.dead_t = 0.0
        self.snd.play('stomp')
        self.puff(e.x, e.y + 0.5, e.z, 6)
        self.L.coin(e.x, e.y + 0.8, e.z, 1)

    def break_crate(self, c):
        x0, y0, z0, x1, y1, z1 = c.aabb()
        cx, cy, cz = (x0 + x1) / 2, (y0 + y1) / 2, (z0 + z1) / 2
        self.L.remove_box(c)
        self.snd.play('crate')
        self.puff(cx, cy, cz, 12, CRATE)
        for i in range(c.coins):
            a = TAU * i / max(1, c.coins)
            self.L.coin(cx + math.cos(a) * 1.2, y0 + 0.8, cz + math.sin(a) * 1.2)

    def punch(self, P):
        self.snd.play('punch')
        px = P.x + math.sin(P.yaw) * 0.8
        pz = P.z + math.cos(P.yaw) * 0.8
        py = P.y + 0.8
        for e in self.L.enemies:
            if (e.alive and e.kind == 'walker' and e.dead_t < 0
                    and math.hypot(e.x - px, e.z - pz) < 1.1
                    and abs(e.y + 0.4 - py) < 1.2):
                self.kill_enemy(e)
        for b in list(self.L.dyn):
            if b.kind == 'crate':
                x0, y0, z0, x1, y1, z1 = b.aabb()
                if (x0 - 0.4 < px < x1 + 0.4 and y0 - 0.4 < py < y1 + 0.4
                        and z0 - 0.4 < pz < z1 + 0.4):
                    self.break_crate(b)

    def ground_pound_land(self, P, b):
        self.snd.play('gp')
        self.shake = 0.25
        self.puff(P.x, P.y, P.z, 8)
        if b.kind == 'crate':
            self.break_crate(b)
            P.state = 'air'
            P.jkind = 'fall'
            P.ground = None
        for e in self.L.enemies:
            if (e.alive and e.kind == 'walker' and e.dead_t < 0
                    and math.hypot(e.x - P.x, e.z - P.z) < 1.8
                    and abs(e.y - P.y) < 1.2):
                self.kill_enemy(e)

    # -- simulation ---------------------------------------------------------
    def step(self, inp):
        self.gt += DT
        if self.fade_dir == 1:
            self.fade += DT / 0.35
            if self.fade >= 1:
                self.fade = 1.0
                key, sp = self.pending
                self.load_level(key, sp)
                if self.mode in ('starget', 'dying', 'title_start'):
                    self.mode = 'play'
                self.fade_dir = -1
            return
        if self.fade_dir == -1:
            self.fade -= DT / 0.35
            if self.fade <= 0:
                self.fade = 0.0
                self.fade_dir = 0
        self.msg_t = max(0.0, self.msg_t - DT)
        self.banner_t = max(0.0, self.banner_t - DT)
        self.shake = max(0.0, self.shake - DT)

        m = self.mode
        if m == 'title':
            self.cam.orbit(self.gt)
            self._tick_world(None)
            if inp.start_p or inp.jump_p:
                self.snd.play('select')
                self.lives = 4
                self.health = MAX_HP
                self.return_exit = None
                self.mode = 'title_start'
                self.warp('hub', None)
            return
        if m == 'title_start':
            return
        if m == 'pause':
            opts = self.pause_opts()
            if inp.up_p:
                self.menu_i = (self.menu_i - 1) % len(opts)
                self.snd.play('select')
            if inp.down_p:
                self.menu_i = (self.menu_i + 1) % len(opts)
                self.snd.play('select')
            if inp.pause_p or inp.back_p:
                self.mode = 'play'
            elif inp.start_p or inp.jump_p:
                o = opts[self.menu_i]
                self.mode = 'play'
                if o == 'Exit Course':
                    self.warp('hub', self.return_exit)
                elif o == 'Quit to Title':
                    self.mode = 'title'
                    self.load_level('hub', None)
            return
        if m == 'starget':
            self.mode_t -= DT
            self.player.vx = self.player.vz = 0.0
            if self.mode_t <= 0:
                if self.L.key != 'hub':
                    self.warp('hub', self.return_exit)
                else:
                    self.mode = 'play'
            return
        if m == 'dying':
            self.mode_t -= DT
            self.player.flip += 8 * DT
            if self.mode_t <= 0:
                self.lives -= 1
                self.health = MAX_HP
                if self.lives < 0:
                    self.mode = 'gameover'
                    self.mode_t = 3.5
                else:
                    self.warp(self.L.key, None)
            return
        if m == 'gameover':
            self.mode_t -= DT
            if self.mode_t <= 0 or (self.mode_t < 2.5 and inp.start_p):
                self.mode = 'title'
                self.load_level('hub', None)
            return

        # play
        if inp.pause_p:
            self.mode = 'pause'
            self.menu_i = 0
            self.snd.play('select')
            return
        self._tick_world(inp)

    def _tick_world(self, inp):
        self.t += DT
        L = self.L
        P = self.player
        for b in L.dyn:
            b.update(self.t)
        for p in self.particles:
            p[0] += p[3] * DT
            p[1] += p[4] * DT
            p[2] += p[5] * DT
            p[4] -= 12 * DT
            p[6] -= DT
        self.particles = [p for p in self.particles if p[6] > 0]
        for e in L.enemies:
            if e.alive:
                e.update(L, P, self.t)
        if inp is None:
            return
        if self.fade_dir == 0:
            P.update(inp, L, self)
        else:
            P.update(Input(), L, self)
        if self.mode != 'play':
            return
        self.cam.update(P, L, inp)
        self._interact()

    def _interact(self):
        L = self.L
        P = self.player
        pcx, pcy, pcz = P.x, P.y + 0.75, P.z
        if P.y < L.kill_y:
            self.health = 0
            self.die()
            return
        # coins
        for c in L.coins:
            if c[4] and abs(c[0] - pcx) < 0.9 and abs(c[2] - pcz) < 0.9 \
                    and abs(c[1] - pcy) < 1.1:
                c[4] = False
                self.coins += c[3]
                self.health = min(MAX_HP, self.health + c[3])
                self.snd.play('coin')
                if (self.coins >= 50 and not self.coin_star_shown
                        and L.key != 'hub'):
                    self.coin_star_shown = True
                    self.say("50 coins! A Power Star appeared at the start!")
        best = self.save['best']
        if self.coins > best.get(L.key, 0):
            best[L.key] = self.coins
        # gems
        for g in L.gems:
            if g['coin'] and not self.coin_star_shown:
                continue
            if g['crate'] is not None and g['crate'] in L.boxes:
                continue
            if (abs(g['x'] - pcx) < 1.1 and abs(g['z'] - pcz) < 1.1
                    and abs(g['y'] - pcy) < 1.4):
                self.collect_star(g)
                return
        # enemies
        for e in L.enemies:
            if not e.alive:
                continue
            if e.kind == 'spike':
                if (math.hypot(e.x - pcx, e.z - pcz) < 0.95
                        and abs(e.y - pcy) < 1.1):
                    self.hurt(2, e.x, e.z)
                continue
            if e.dead_t >= 0:
                continue
            if (abs(P.x - e.x) < 0.75 and abs(P.z - e.z) < 0.75
                    and P.y < e.y + 0.95 and P.y + P.HGT > e.y):
                if P.state == 'gp' or (P.vy < 0 and P.y > e.y + 0.35):
                    self.kill_enemy(e)
                    if P.state != 'gp':
                        P.vy = 12.0
                        P.state = 'air'
                        P.jkind = 'stomp'
                elif P.state in ('dive', 'slide'):
                    self.kill_enemy(e)
                else:
                    self.hurt(1, e.x, e.z)
        # portals
        for p in L.portals:
            x0, y0, z0, x1, y1, z1 = p['aabb']
            m = 0.6
            if (x0 - m < P.x < x1 + m and y0 - 1.5 < P.y < y1
                    and z0 - m < P.z < z1 + m):
                if self.star_count() >= p['req']:
                    self.return_exit = p['exit']
                    self.warp(p['target'], None)
                elif self.msg_t <= 0.5:
                    need = p['req'] - self.star_count()
                    self.say(f"Sealed. This painting needs {p['req']} Stars "
                             f"({need} more).")
        # signs
        for (sx, sz, text) in L.signs:
            if math.hypot(P.x - sx, P.z - sz) < 3.0 and self.msg_t < 0.2:
                self.say(text, 0.3)

    def collect_star(self, g):
        new = g['id'] not in self.save['gems']
        if new:
            self.save['gems'].append(g['id'])
            write_save(self.save)
        self.snd.play('gem')
        self.mode = 'starget'
        self.mode_t = 2.6
        self.say(("STAR GET!  " if new else "Star again!  ") + g['name'], 2.6)
        L = self.L
        L.gems.remove(g)

    def pause_opts(self):
        if self.L.key == 'hub':
            return ['Resume', 'Quit to Title']
        return ['Resume', 'Exit Course', 'Quit to Title']

    # -- drawing ------------------------------------------------------------
    def sky_surface(self):
        L = self.L
        key = (L.sky, L.horizon)
        s = self.sky_cache.get(key)
        if s is None:
            s = pygame.Surface((RW, RH))
            for y in range(RH):
                t = min(1.0, y / (RH * 0.62))
                pygame.draw.line(s, lerpc(L.sky, L.horizon, t), (0, y),
                                 (RW, y))
            self.sky_cache[key] = s
        return s

    def draw(self):
        L = self.L
        R = self.R
        P = self.player
        cam = self.cam
        self.rs.blit(self.sky_surface(), (0, 0))
        pos = cam.pos
        if self.shake > 0:
            pos = (pos[0], pos[1] + math.sin(self.gt * 70) * self.shake * 0.6,
                   pos[2])
        R.set_camera(pos, cam.yaw, cam.pitch, L.horizon)
        R.static(L)
        for b in L.dyn:
            R.faces(b.faces, b.ox, b.oy, b.oz)
        t = self.gt
        # portals emblems
        for p in L.portals:
            cx, cy, cz = p['c']
            nx, ny, nz = p['n']
            open_ = self.star_count() >= p['req']
            base = (cx + nx * 0.3, cy, cz + nz * 0.3)
            if open_:
                for i in range(3):
                    R.circle(base, 1.9 - i * 0.55,
                             shade(p['col'], 0.7 + 0.25 * i
                                   + 0.15 * math.sin(t * 4 + i)),
                             bias=-0.01 * i)
            else:
                R.circle(base, 1.4, (70, 70, 80))
                R.circle((base[0], base[1] + 0.2, base[2]), 0.5, (150, 150,
                                                                  160),
                         bias=-0.01)
        # coins
        for c in L.coins:
            if c[4]:
                col = GOLD if c[3] == 1 else (240, 60, 60) if c[3] == 2 \
                    else (70, 120, 255)
                R.ellipse((c[0], c[1] + 0.1 * math.sin(t * 3 + c[0]), c[2]),
                          0.32 if c[3] < 5 else 0.42,
                          max(0.12, abs(math.cos(t * 4 + c[2]))), col,
                          shade(col, 0.6))
        # gems
        for g in L.gems:
            if g['coin'] and not self.coin_star_shown:
                continue
            if g['crate'] is not None and g['crate'] in L.boxes:
                continue
            col = STARDONE if g['id'] in self.save['gems'] else STARC
            R.gem((g['x'], g['y'] + 0.15 * math.sin(t * 2), g['z']), 0.55,
                  t * 2.5, col)
        # enemies
        for e in L.enemies:
            if not e.alive:
                continue
            if e.kind == 'spike':
                R.circle((e.x, e.y, e.z), 0.55, (60, 60, 70),
                         outline=(200, 200, 210))
                for i in range(6):
                    a = TAU * i / 6 + t * 3
                    R.circle((e.x + math.cos(a) * 0.55, e.y + math.sin(a)
                              * 0.55, e.z), 0.14, (220, 220, 230),
                             bias=-0.02)
                continue
            sq = 1.0 if e.dead_t < 0 else max(0.15, 1 - e.dead_t * 3)
            bob = abs(math.sin(e.anim * 8)) * 0.06 if e.dead_t < 0 else 0
            R.cuboids(e.x, e.y + bob, e.z, e.yaw, 0.0, (
                (-0.2, 0.1, 0, 0.14, 0.1, 0.18, (60, 40, 30)),
                (0.2, 0.1, 0, 0.14, 0.1, 0.18, (60, 40, 30)),
                (0, 0.42, 0, 0.42, 0.24, 0.4, (110, 70, 160)),
                (0, 0.78, 0, 0.5, 0.14, 0.48, (60, 180, 120)),
                (-0.15, 0.5, 0.41, 0.07, 0.1, 0.02, WHITE),
                (0.15, 0.5, 0.41, 0.07, 0.1, 0.02, WHITE),
                (-0.15, 0.48, 0.43, 0.03, 0.05, 0.01, BLACK),
                (0.15, 0.48, 0.43, 0.03, 0.05, 0.01, BLACK),
            ), squash=sq)
        # particles
        for p in self.particles:
            R.circle((p[0], p[1], p[2]), 0.12, p[7])
        # player + shadow
        if self.mode != 'title':
            fy, fb = L.floor_below(P.x, P.y + 0.1, P.z)
            if fb is not None and P.y - fy < 20:
                rr = 0.42 * max(0.4, 1 - (P.y - fy) * 0.05)
                pts = [(P.x + math.cos(a) * rr, fy + 0.03,
                        P.z + math.sin(a) * rr)
                       for a in [TAU * i / 8 for i in range(8)]]
                R.poly(pts, (30, 30, 40), fog=False)
            P.draw(R)
        R.flush()
        pygame.transform.scale(self.rs, self.screen.get_size(), self.screen)
        self.hud()
        if self.fade > 0:
            ov = pygame.Surface(self.screen.get_size())
            ov.fill(BLACK)
            ov.set_alpha(int(255 * min(1.0, self.fade)))
            self.screen.blit(ov, (0, 0))

    # -- HUD ----------------------------------------------------------------
    def text(self, s, font, x, y, col=WHITE, center=False):
        img = font.render(s, True, col)
        sh = font.render(s, True, BLACK)
        r = img.get_rect()
        if center:
            r.center = (x, y)
        else:
            r.topleft = (x, y)
        self.screen.blit(sh, r.move(3, 3))
        self.screen.blit(img, r)
        return r

    def star_icon(self, x, y, r, col):
        pts = [(x, y - r * 1.25), (x + r, y - r * 0.3), (x + r * 0.6, y + r),
               (x - r * 0.6, y + r), (x - r, y - r * 0.3)]
        pygame.draw.polygon(self.screen, shade(col, 0.8), pts)
        pygame.draw.polygon(self.screen, BLACK, pts, 2)

    def health_meter(self, cx, cy, rad):
        scr = self.screen
        hp = max(0, self.health)
        col = ((70, 140, 255) if hp >= 7 else (80, 210, 90) if hp >= 5
               else (250, 210, 50) if hp >= 3 else (240, 60, 60))
        pygame.draw.circle(scr, (20, 20, 30), (cx, cy), rad + 6)
        for i in range(MAX_HP):
            a0 = -math.pi / 2 + TAU * i / MAX_HP
            a1 = a0 + TAU / MAX_HP
            pts = [(cx, cy)] + [(cx + math.cos(a0 + (a1 - a0) * k / 4) * rad,
                                 cy + math.sin(a0 + (a1 - a0) * k / 4) * rad)
                                for k in range(5)]
            pygame.draw.polygon(scr, col if i < hp else (60, 60, 70), pts)
            pygame.draw.polygon(scr, BLACK, pts, 2)
        pygame.draw.circle(scr, HAT, (cx, cy), int(rad * 0.38))
        pygame.draw.circle(scr, SKIN, (cx, cy + 2), int(rad * 0.22))
        pygame.draw.circle(scr, BLACK, (cx, cy), int(rad * 0.38), 2)

    def hud(self):
        W, H = self.screen.get_size()
        m = self.mode
        if m == 'title' or m == 'title_start':
            self.text(NINTENDO, self.font, W // 2, H // 5 - 20, (240, 60, 60),
                      True)
            self.text(GAME_FULL, self.font_big, W // 2, H // 3, GOLD, True)
            self.text(TITLE, self.font, W // 2, H // 3 + 64, WHITE, True)
            self.text("Peach's Castle  ·  Python 3 Port", self.font_s,
                      W // 2, H // 3 + 110, (200, 220, 255), True)
            if int(self.gt * 2) % 2 == 0:
                self.text("PRESS START", self.font, W // 2, H * 2 // 3,
                          WHITE, True)
            self.text(f"Power Stars: {self.star_count()} / {TOTAL_STARS}",
                      self.font_s, W // 2, H * 2 // 3 + 50, WHITE, True)
            self.text("Unofficial fan engine  ·  60 FPS N64 timing  ·  "
                      "not affiliated with Nintendo",
                      self.font_s, W // 2, H - 40, (180, 180, 190), True)
            return
        self.star_icon(46, 46, 16, STARC)
        self.text(f"x {self.star_count()}", self.font, 72, 30)
        pygame.draw.circle(self.screen, GOLD, (46, 98), 14)
        pygame.draw.circle(self.screen, BLACK, (46, 98), 14, 2)
        self.text(f"x {self.coins}", self.font, 72, 84)
        pygame.draw.circle(self.screen, HAT, (46, 150), 14)
        pygame.draw.circle(self.screen, SKIN, (46, 152), 7)
        pygame.draw.circle(self.screen, BLACK, (46, 150), 14, 2)
        self.text(f"x {max(0, self.lives)}", self.font, 72, 136)
        self.health_meter(W - 90, 90, 56)
        if self.banner_t > 0:
            a = min(1.0, self.banner_t)
            col = lerpc((0, 0, 0), GOLD, a)
            self.text(self.banner, self.font_big, W // 2, H // 4, col, True)
        if self.msg_t > 0 and self.msg:
            box = pygame.Rect(0, 0, min(W - 80, 60 + len(self.msg) * 15), 64)
            box.center = (W // 2, H - 80)
            s = pygame.Surface(box.size, pygame.SRCALPHA)
            s.fill((0, 0, 0, 170))
            self.screen.blit(s, box)
            self.text(self.msg, self.font_s, W // 2, H - 80, WHITE, True)
        if self.show_fps:
            self.text(f"{self.fps_val:5.1f} FPS  N64 {N64_FPS}Hz"
                      f"  dt={FRAME_TIME * 1000:.3f}ms", self.font_s,
                      W - 360, H - 36, (200, 255, 200))
        if m == 'pause':
            self.draw_pause(W, H)
        elif m == 'gameover':
            self.text("GAME OVER", self.font_big, W // 2, H // 2, (240, 60, 60),
                      True)

    def draw_pause(self, W, H):
        s = pygame.Surface((W, H), pygame.SRCALPHA)
        s.fill((0, 0, 20, 180))
        self.screen.blit(s, (0, 0))
        self.text("PAUSE", self.font_big, W // 2, 70, GOLD, True)
        y = 130
        for key in COURSE_ORDER:
            names = STAR_NAMES[key]
            got = sum(1 for i in range(len(names))
                      if f"{key}:{i}" in self.save['gems'])
            title = BUILDERS_NAMES[key]
            best = self.save['best'].get(key, 0)
            self.text(f"{title}   {got}/{len(names)}   best coins {best}",
                      self.font_s, 120, y, WHITE)
            x = 620
            for i, n in enumerate(names):
                self.star_icon(x + i * 34, y + 12, 10,
                              STARC if f"{key}:{i}" in self.save['gems']
                              else (70, 70, 90))
            y += 40
        y += 10
        for line in ("Triple jump: jump x3 while running   Long jump: run + "
                     "crouch + jump",
                     "Backflip: stand + crouch + jump   Wall kick: jump as you "
                     "hit a wall",
                     "Ground pound: crouch in air   Dive: action while "
                     "running, jump to roll out"):
            self.text(line, self.font_s, 120, y, (200, 210, 255))
            y += 32
        y += 20
        for i, o in enumerate(self.pause_opts()):
            sel = i == self.menu_i
            self.text(("> " if sel else "  ") + o, self.font, W // 2, y + i * 46,
                      GOLD if sel else WHITE, True)


BUILDERS_NAMES = {'hub': "Peach's Castle", 'hills': "Bob-omb Battlefield",
                  'ember': "Lethal Lava Land", 'cloud': "Rainbow Ride"}


# ----------------------------------------------------------------------------
# Main loop
# ----------------------------------------------------------------------------
JUMP_KEYS = (pygame.K_SPACE, pygame.K_z, pygame.K_k)
CROUCH_KEYS = (pygame.K_LSHIFT, pygame.K_RSHIFT, pygame.K_x, pygame.K_j)
ACT_KEYS = (pygame.K_c, pygame.K_l, pygame.K_LCTRL, pygame.K_RCTRL)


def poll_input(inp, events, joy):
    for ev in events:
        if ev.type == pygame.KEYDOWN:
            k = ev.key
            if k in JUMP_KEYS:
                inp.jump_p = True
            if k in CROUCH_KEYS:
                inp.crouch_p = True
            if k in ACT_KEYS:
                inp.act_p = True
            if k in (pygame.K_RETURN, pygame.K_KP_ENTER):
                inp.start_p = True
            if k in (pygame.K_ESCAPE, pygame.K_p):
                inp.pause_p = True
            if k in (pygame.K_UP, pygame.K_w):
                inp.up_p = True
            if k in (pygame.K_DOWN, pygame.K_s):
                inp.down_p = True
            if k == pygame.K_BACKSPACE:
                inp.back_p = True
        elif ev.type == pygame.MOUSEMOTION and ev.buttons[2]:
            inp.mdx += ev.rel[0]
        elif ev.type == pygame.MOUSEWHEEL:
            inp.zoom += ev.y
        elif ev.type == pygame.JOYBUTTONDOWN:
            b = ev.button
            if b == 0:
                inp.jump_p = True
            elif b in (1, 2):
                inp.act_p = True
            elif b in (4, 5):
                inp.crouch_p = True
            elif b in (6, 7, 9):
                inp.pause_p = True
                inp.start_p = True
        elif ev.type == pygame.JOYHATMOTION:
            if ev.value[1] == 1:
                inp.up_p = True
            elif ev.value[1] == -1:
                inp.down_p = True
    keys = pygame.key.get_pressed()
    mx = (keys[pygame.K_RIGHT] or keys[pygame.K_d]) - \
        (keys[pygame.K_LEFT] or keys[pygame.K_a])
    mz = (keys[pygame.K_UP] or keys[pygame.K_w]) - \
        (keys[pygame.K_DOWN] or keys[pygame.K_s])
    inp.jump_h = any(keys[k] for k in JUMP_KEYS)
    inp.crouch_h = any(keys[k] for k in CROUCH_KEYS)
    inp.cam = (keys[pygame.K_e] - keys[pygame.K_q]) * 1.0
    if joy is not None:
        try:
            ax, az = joy.get_axis(0), -joy.get_axis(1)
            if math.hypot(ax, az) > 0.2:
                mx, mz = ax, az
            if joy.get_numaxes() > 3:
                cx = joy.get_axis(2) if joy.get_numaxes() < 5 \
                    else joy.get_axis(3)
                if abs(cx) > 0.25:
                    inp.cam = cx
            inp.jump_h = inp.jump_h or bool(joy.get_button(0))
            if joy.get_numbuttons() > 5:
                inp.crouch_h = inp.crouch_h or bool(joy.get_button(4)) \
                    or bool(joy.get_button(5))
            if joy.get_numaxes() > 4 and joy.get_axis(4) > 0.5:
                inp.crouch_h = True
        except Exception:
            pass
    ln = math.hypot(mx, mz)
    if ln > 1:
        mx, mz = mx / ln, mz / ln
    inp.mx, inp.mz = mx, mz


def main():
    """N64 NTSC lock: 1 logic tick = 1/60 s, display paced to 60 FPS."""
    pygame.mixer.pre_init(22050, -16, 1, 512)
    pygame.init()
    pygame.display.set_caption(f"{TITLE}  ·  N64 {N64_FPS} FPS")
    flags = pygame.RESIZABLE
    try:
        screen = pygame.display.set_mode((WIN_W, WIN_H), flags, vsync=1)
    except TypeError:
        screen = pygame.display.set_mode((WIN_W, WIN_H), flags)
    pygame.joystick.init()
    joy = None
    if pygame.joystick.get_count():
        joy = pygame.joystick.Joystick(0)
        joy.init()
    game = Game(screen)
    inp = Input()
    clock = pygame.time.Clock()
    frames = 0
    fps_t = time.perf_counter()
    running = True
    while running:
        events = pygame.event.get()
        for ev in events:
            if ev.type == pygame.QUIT:
                running = False
            elif ev.type == pygame.KEYDOWN and ev.key == pygame.K_F1:
                game.show_fps = not game.show_fps
            elif ev.type == pygame.JOYDEVICEADDED and joy is None:
                joy = pygame.joystick.Joystick(ev.device_index)
                joy.init()
        poll_input(inp, events, joy)

        # Hard N64 frame lock: exactly one step of DT=1/60 per frame.
        # Speed is always N64 60 Hz — never scales with render FPS.
        game.step(inp)
        inp.clear()
        game.draw()
        pygame.display.flip()

        frames += 1
        now = time.perf_counter()
        if now - fps_t >= 0.5:
            game.fps_val = frames / (now - fps_t)
            frames = 0
            fps_t = now
        clock.tick_busy_loop(N64_FPS)   # hold real time to 60 FPS
    write_save(game.save)
    pygame.quit()


# ----------------------------------------------------------------------------
# Self-test (headless)
# ----------------------------------------------------------------------------
def selftest():
    global SAVE_PATH
    import tempfile
    os.environ['SDL_VIDEODRIVER'] = 'dummy'
    os.environ['SDL_AUDIODRIVER'] = 'dummy'
    SAVE_PATH = os.path.join(tempfile.gettempdir(), "sm64pyport_selftest.json")
    if os.path.exists(SAVE_PATH):
        os.remove(SAVE_PATH)
    pygame.init()
    screen = pygame.display.set_mode((WIN_W, WIN_H))
    g = Game(screen, audio=False)
    ok = True

    def check(name, cond, info=''):
        nonlocal ok
        ok &= bool(cond)
        print(f"  [{'PASS' if cond else 'FAIL'}] {name} {info}")

    def run(n, f=None):
        inp = Input()
        for i in range(n):
            inp.clear()
            inp.mx = inp.mz = 0.0
            inp.jump_h = inp.crouch_h = False
            inp.cam = 0.0
            if f:
                f(i, inp)
            g.step(inp)

    print(f"{TITLE} self-test   numpy={'yes' if np is not None else 'no'}")
    g.mode = 'play'
    g.load_level('hills', None)
    P = g.player
    run(30)
    check("spawn lands on ground", P.state == 'ground' and abs(P.y) < 1e-3,
          f"y={P.y:.3f}")

    # jump heights
    peaks = {}

    def measure(kind, setup):
        g.load_level('hills', (0.0, 0.0, -34.0, 0.0))
        run(20)
        y0 = P.y
        mx = [y0]

        def f(i, inp):
            setup(i, inp)
            mx[0] = max(mx[0], P.y)
        run(70, f)
        peaks[kind] = mx[0] - y0

    measure('single', lambda i, inp: (setattr(inp, 'jump_p', i == 0),
                                      setattr(inp, 'jump_h', i < 30)))

    def back(i, inp):
        inp.crouch_h = i < 3
        inp.jump_p = i == 2
        inp.jump_h = i < 40
    measure('backflip', back)
    check("single jump ~1.8u", 1.5 < peaks['single'] < 2.1,
          f"{peaks['single']:.2f}")
    check("backflip ~4.2u", 3.9 < peaks['backflip'] < 4.6,
          f"{peaks['backflip']:.2f}")

    # triple jump chain
    g.load_level('hills', (0.0, 0.0, -38.0, 0.0))
    run(10)
    seen = []

    def tri(i, inp):
        inp.mz = 1.0
        inp.jump_h = True
        if i == 50 or (i > 50 and P.state == 'ground' and P.land_t < 0.05
                       and len(seen) < 3):
            inp.jump_p = True
        if P.state == 'air' and (not seen or seen[-1] != P.jkind):
            seen.append(P.jkind)
    run(200, tri)
    check("triple jump chain", seen[:3] == ['single', 'double', 'triple'],
          str(seen[:4]))

    # long jump
    g.load_level('hills', (0.0, 0.0, -38.0, 0.0))
    run(10)
    st = {}

    def lj(i, inp):
        inp.mz = 1.0
        if i >= 60:
            inp.crouch_h = i < 63
            inp.jump_p = i == 62
        if i == 62:
            st['z0'] = P.z
        if i > 63 and P.state == 'ground' and 'z1' not in st:
            st['z1'] = P.z
    run(140, lj)
    d = st.get('z1', 0) - st.get('z0', 0)
    check("long jump distance > 6u", d > 6, f"{d:.2f}")

    # wall kick canyon
    g.load_level('hills', (26.5, 0.0, -24.0, math.pi / 2))
    run(5)
    P.state = 'air'
    P.jkind = 'single'
    P.vx, P.vy = 7.0, 11.0
    P.ground = None
    mxy = [0.0]
    kicks = [0]

    def wk(i, inp):
        if P.wall_t > 0 and P.state == 'air':
            inp.jump_p = True
            kicks[0] += 1
        mxy[0] = max(mxy[0], P.y)
    run(240, wk)
    check("wall kicks climb canyon", mxy[0] > 9, f"peak {mxy[0]:.1f} "
          f"kicks {kicks[0]}")

    # ground pound breaks crate
    g.load_level('hub', (6.0, 4.0, -24.0, 0.0))
    ncr = sum(1 for b in g.L.dyn if b.kind == 'crate')
    run(1, lambda i, inp: None)
    P.state = 'air'
    run(2, lambda i, inp: setattr(inp, 'crouch_p', i == 0))
    run(90)
    ncr2 = sum(1 for b in g.L.dyn if b.kind == 'crate')
    check("ground pound breaks crate", ncr2 == ncr - 1, f"{ncr}->{ncr2}")

    # coins
    g.load_level('hills', None)
    c = g.L.coins[0]
    P.x, P.y, P.z = c[0], c[1] - 0.75, c[2]
    P.vy = 0
    run(1)
    check("coin pickup", g.coins >= 1, f"coins={g.coins}")

    # portal lock
    g.load_level('hub', (11.0, 0.0, 0.0, math.pi / 2))
    run(20, lambda i, inp: setattr(inp, 'mx', 0) or setattr(inp, 'mz', 1.0))
    check("locked painting blocks", g.L.key == 'hub' and 'needs' in g.msg,
          repr(g.msg[:40]))

    # star + return to hub
    g.load_level('hills', None)
    g.return_exit = (0.0, 0.0, 9.0, math.pi)
    gm = g.L.gems[0]
    P.x, P.y, P.z = gm['x'], gm['y'] - 0.75, gm['z']
    run(1)
    check("star collected + saved", g.mode == 'starget'
          and 'hills:0' in load_save()['gems'])
    run(220)
    check("returned to hub", g.L.key == 'hub' and g.mode == 'play')

    # open portal enters course
    g.load_level('hub', (0.0, 0.0, 9.0, 0.0))
    run(80, lambda i, inp: setattr(inp, 'mz', 1.0))
    check("open portal warps to course", g.L.key == 'hills', g.L.key)

    # lava
    g.load_level('ember', (20.0, 1.0, 0.0, 0.0))
    hp0 = g.health
    run(40)
    check("lava burns + bounces", g.health < hp0, f"hp {hp0}->{g.health}")

    # benchmark
    print("  benchmark (logic step + full render + scale):")
    worst = 1e9
    for key in COURSE_ORDER:
        g.mode = 'play'
        g.health = MAX_HP
        g.load_level(key, None)
        inp = Input()
        times = []
        for i in range(240):
            inp.clear()
            inp.mz = 1.0 if (i // 60) % 2 == 0 else 0.0
            inp.mx = 0.3
            inp.cam = 1.0 if i % 120 < 30 else 0.0
            inp.jump_p = i % 45 == 0
            inp.jump_h = i % 45 < 20
            t0 = time.perf_counter()
            g.step(inp)
            g.draw()
            times.append(time.perf_counter() - t0)
            if g.mode != 'play':
                g.mode = 'play'
                g.health = MAX_HP
        avg = sum(times) / len(times)
        p95 = sorted(times)[int(len(times) * 0.95)]
        fps = 1 / avg
        worst = min(worst, fps)
        print(f"    {key:6s}  avg {avg * 1000:5.2f} ms  p95 {p95 * 1000:5.2f}"
              f" ms  -> ~{fps:5.0f} FPS")
    check("all levels sustain 60 FPS (avg)", worst >= 60, f"{worst:.0f}")
    pygame.image.save(g.screen, os.path.join(tempfile.gettempdir(),
                                             "sm64pyport_shot.png"))
    os.remove(SAVE_PATH)
    print("ALL PASS" if ok else "SOME CHECKS FAILED")
    pygame.quit()
    return 0 if ok else 1


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    main()
