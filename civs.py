#!/usr/bin/env python3
"""
LIFE OF CIVILISATIONS
=====================
Conway's Game of Life in your terminal that grows up into a civilisation game.

* Endless grid     - the world is a sparse dictionary, so it has no edges. Move the
                     cursor anywhere and the camera follows. Gliders really do fly forever.
* Endless timeline - it just keeps ticking (Year 1, 2, 3 ... through the Ages). You can
                     also rewind (b) and resume: that starts an alternate timeline.
* Random spawn     - auto-spawn drops new settlements/hordes in view; resurrects empty worlds.
* Live menu        - press m. The menu is an overlay: the world keeps running underneath.
* Two rule sets    - "Civilisation" (civilisations, wars, cities, events) and classic Conway B3/S23.

CIVILISATION RULES (each cell is a settlement belonging to a civilisation)
  Birth      empty tile with exactly 3 neighbours -> a new settlement of the biggest
             neighbouring civilisation (ties are random).  Embermages also breed at 6.
  Survival   2-3 neighbours (Conway's rule).
  Cities     a settlement that survives long enough becomes a CITY. Cities survive with
             1-5 neighbours (Stonekin 1-6), resist conquest, never die of loneliness,
             and periodically found colonies nearby.
  War        a settlement is conquered if an enemy civilisation has enough neighbours around it
             and outnumbers its defenders (cities count +2). Ironclad win ties.
  Civilisations     Ironclad (warriors), Greenfolk (farmers), Sunriders (nomads who wander),
             Tidewalkers (traders - found trade posts between rivals),
             Embermages (zealots - convert outnumbered foes), Stonekin (builders).
  Walls      cities fence themselves in, thickest where enemies are near. Walls block births and
             colonies, help adjacent defenders hold, crumble if abandoned, and must be besieged
             to break (Ironclad batter fastest). Stonekin build the most and the toughest.
  Nature     the world is generated endlessly as you explore: forests, rocks, ponds, berry
             patches and wild herds. Settlements can't be born on them. All of it regrows
             (stumps re-sprout, dry ponds refill, forests creep, herds breed).
  Workers    mature settlements send workers (loaded workers show filled) to fell trees, quarry
             stone, fetch water, pick berries and hunt game, and carry it home to the civilisation's
             stockpile. Walls cost wood + stone, colonies cost food, and civilisations that run out of
             food or water starve. Rich civilisations found FARMS: fenced pens that workers herd wild
             animals into; penned herds breed and feed the civilisation.
  Events     plague, famine, flood, meteor, golden age, barbarian hordes (random or manual).

PLAYING (the default: pick a civilisation when the game starts, or --play NAME)
  You start with a capital city, a crew of workers and EMPTY stores. Everything you build costs
  wood, stone and food that your workers gather (they head out on their own; v sets their focus).
    Space (or a mouse click) places the selected structure at the cursor; t or 1-4 chooses it:
      1 City (10 food, 6 wood, 2 stone)   2 Wall (wood+stone)   3 Fortify (a ring of walls)   4 Farm (8 wood)
    e city   b wall   r fortify   f farm   (direct shortcuts)      x pulls down your wall
    h hire workers   v worker focus   k Crusade (attack bonus, 8 stone)   g Bulwark (defence bonus, 8 wood)
    l advisors auto-build walls & farms     Menu: barter resources.     Tab: leave play mode.
    (w a s d always move the cursor, 8 tiles at a time; arrow keys move one tile)
  Win by completing all five goals shown in the panel, or by dominating the world. You lose if
  your civilisation is wiped out. Sandbox tools (editing cells, events, rewind...) lock while you rule.

CONTROLS (see the menu with m for everything)
  arrows / wasd  move cursor 1 / 8 cells     space  place/erase a cell    x  erase
  1-6 / t        choose brush civilisation          e  stamp pattern   f  next pattern
  r  found settlement at cursor              R  random burst in view
  g  cycle auto-spawn   v  events on/off     j  pick event   k  trigger event at cursor
  p  pause   n  step   b  rewind             + / -  speed
  l  switch rules       c  jump to civilisation    o  jump to origin
  u  nature on/off   z/N  pick/place nature   h  release herd at cursor
  B  build/remove wall at cursor   y  cities auto-build walls on/off
  i  toggle side panel  C  clear world       P  prune far-away cells
  m  menu               q  quit              mouse: left click = cell, right click = stamp

Run:  python3 life_of_civilisations.py            (Windows: pip install windows-curses)
      python3 life_of_civilisations.py --help
"""

import argparse
import curses
import heapq
import itertools
import locale
import math
import os
import random
import time
from bisect import bisect_right
from collections import Counter, deque, namedtuple

# --------------------------------------------------------------------------- #
# constants & data
# --------------------------------------------------------------------------- #

NEIGH = [(-1, -1), (0, -1), (1, -1), (-1, 0), (1, 0), (-1, 1), (0, 1), (1, 1)]
AGE_CAP = 250
SPEEDS = [1, 2, 4, 8, 15, 30, 60]
MAX_POP = 20000          # beyond this, the farthest cells fade into legend
HIST_MAX = 90            # ticks of rewind history
HIST_CELL_LIMIT = 5000   # don't record history for worlds bigger than this
PANEL_W = 37

Civilisation = namedtuple(
    "Civilisation",
    "name c256 c8 desc survive birth conquer tiewin city_age city_max wander colony trade wall wall_hp",
)

CIVILISATIONS = [
    Civilisation("Ironclad", 196, curses.COLOR_RED,
          "Warriors: win border ties and conquer weakly held land.",
          {2, 3}, {3}, 3, True, 14, 5, 0.0, 16, False, 0.12, 4),
    Civilisation("Greenfolk", 40, curses.COLOR_GREEN,
          "Farmers: fertile - their cities hold up to 6 neighbours and breed colonies fast.",
          {2, 3}, {3}, 99, False, 14, 6, 0.0, 14, False, 0.08, 3),
    Civilisation("Sunriders", 220, curses.COLOR_YELLOW,
          "Nomads: their settlements wander across the plains.",
          {2, 3}, {3}, 3, False, 16, 5, 0.025, 20, False, 0.03, 2),
    Civilisation("Tidewalkers", 33, curses.COLOR_BLUE,
          "Traders: found trade posts where two rival civilisations meet.",
          {2, 3}, {3}, 99, False, 12, 5, 0.0, 14, True, 0.12, 4),
    Civilisation("Embermages", 171, curses.COLOR_MAGENTA,
          "Zealots: convert outnumbered foes; also breed at 6 neighbours.",
          {2, 3}, {3, 6}, 2, False, 14, 5, 0.0, 18, False, 0.10, 3),
    Civilisation("Stonekin", 51, curses.COLOR_CYAN,
          "Builders: cities rise fast and are very hard to break.",
          {2, 3}, {3}, 4, False, 8, 6, 0.0, 10, False, 0.30, 7),
]

# pre-built (civilisation, age) tuples so we never allocate millions of tiny tuples
CELLS = [[(t, a) for a in range(AGE_CAP + 1)] for t in range(len(CIVILISATIONS))]

ERAS = [
    (0, "Dawn of Time"), (100, "Stone Age"), (300, "Bronze Age"), (600, "Iron Age"),
    (1000, "Classical Age"), (1600, "Middle Ages"), (2400, "Renaissance"),
    (3400, "Industrial Age"), (5000, "Atomic Age"), (8000, "Information Age"),
    (12000, "Starfaring Age"), (20000, "Age of Legends"),
]
ERA_STARTS = [e[0] for e in ERAS]


def era_name(year):
    return ERAS[max(0, bisect_right(ERA_STARTS, year) - 1)][1]


PATTERNS = {
    "Glider": ".O.\n..O\nOOO",
    "Spaceship": ".O..O\nO....\nO...O\nOOOO.",
    "R-pentomino": ".OO\nOO.\n.O.",
    "Acorn": ".O.....\n...O...\nOO..OOO",
    "Diehard": "......O.\nOO......\n.O...OOO",
    "Pentadecathlon": "..O....O..\nOO.OOOO.OO\n..O....O..",
    "Gosper gun": (
        "........................O...........\n"
        "......................O.O...........\n"
        "............OO......OO............OO\n"
        "...........O...O....OO............OO\n"
        "OO........O.....O...OO..............\n"
        "OO........O...O.OO....O.O...........\n"
        "..........O.....O.......O...........\n"
        "...........O...O....................\n"
        "............OO......................"
    ),
    "Block": "OO\nOO",
    "Blinker": "OOO",
}
PATTERN_NAMES = list(PATTERNS)


def _pattern_cells(name):
    rows = PATTERNS[name].split("\n")
    h, w = len(rows), max(len(r) for r in rows)
    return [(x - w // 2, y - h // 2)
            for y, r in enumerate(rows) for x, ch in enumerate(r) if ch == "O"]


PATTERN_CELLS = {n: _pattern_cells(n) for n in PATTERN_NAMES}

AUTOSPAWN = [("Off", 0.0), ("Low", 0.02), ("Med", 0.06), ("High", 0.15)]
EVENTS = ["Plague", "Famine", "Flood", "Meteor", "Golden age", "Barbarian horde",
          "Wildfire", "Drought"]

# --- nature, resources, workers -------------------------------------------------------
WOOD, STONE, FOOD, WATER = range(4)
TREE, ROCK, POND, BERRY = range(4)
NAT_NAMES = ["Forest", "Rock", "Pond", "Berries"]
NAT_MAX = {TREE: 4, ROCK: 5, POND: 6, BERRY: 3}
NAT_REGROW = {TREE: (150, 250), ROCK: (120, 220), POND: (30, 60), BERRY: (60, 120)}
NAT_RES = {TREE: WOOD, ROCK: STONE, POND: WATER, BERRY: FOOD}
RES_KIND = {WOOD: TREE, STONE: ROCK, WATER: POND}
CHUNK = 16                       # world is generated lazily in 16x16 chunks (>> 4)
EAT_FOOD, EAT_WATER = 0.0025, 0.002
CARRY = 4
START_STOCK = (12.0, 8.0, 25.0, 25.0)       # wood, stone, food, water
WALL_COST = {"Stonekin": (0, 1)}            # default: 1 wood + 1 stone per wall tile
FARM_COST = 8                               # wood for a pen's fences
PEN_MAX = 6
MAX_ANIMALS = 500
IDLE, GO, WORK, BACK, LEAD = range(5)
KRES, KHUNT, KHERD = range(3)

# --- playing a civilisation ------------------------------------------------------------
RES_NAMES = ("wood", "stone", "food", "water")
CP_CAP = 20.0                    # command points: your limited attention per turn
FOCUS_NAMES = ["Balanced", "Wood", "Stone", "Food", "Water", "Herding"]
BUILD_NAMES = ["City", "Wall", "Fortify", "Farm"]


def _ring(r):
    pts = []
    for dx in range(-r, r + 1):
        pts += [(dx, -r), (dx, r)]
    for dy in range(-r + 1, r):
        pts += [(-r, dy), (r, dy)]
    return pts


RINGS = [[]] + [_ring(r) for r in range(1, 31)]

GLYPHS = {
    "uni": dict(tree="♣♣", rock="▲▲", pond="≈≈", berry="∴∴", wild="òó", tame="ôô",
                worker="☺ ", loaded="☻ ", fence="╫╫", sprout="''"),
    "ascii": dict(tree="TT", rock="^^", pond="~~", berry="**", wild="a ", tame="A ",
                  worker="w ", loaded="W ", fence="++", sprout="''"),
    "emoji": dict(tree="🌲", rock="🗻", pond="🌊", berry="🍓", wild="🐗", tame="🐑",
                  worker="☺ ", loaded="☻ ", fence="╫╫", sprout="🌱"),
}

HELP = ("arrows/wasd move | space cell | e stamp | r settle | p pause | n/b step/rewind | "
        "+/- speed | l rules | i panel | m MENU | q quit")


def dominant(arr, rng, exclude=-1):
    """Index and count of the biggest non-zero entry (random among ties)."""
    best, tied = 0, []
    for i, v in enumerate(arr):
        if v == 0 or i == exclude:
            continue
        if v > best:
            best, tied = v, [i]
        elif v == best:
            tied.append(i)
    if not tied:
        return -1, 0
    return (tied[0] if len(tied) == 1 else rng.choice(tied)), best


# --------------------------------------------------------------------------- #
# the simulation (no curses in here)
# --------------------------------------------------------------------------- #

class Animal:
    __slots__ = ("x", "y", "pen", "follow", "alive", "owner")

    def __init__(self, x, y):
        self.x, self.y = x, y
        self.pen = None          # Farm this animal lives in (tame) or None (wild)
        self.follow = None       # Worker leading it to a pen
        self.alive = True
        self.owner = -1


class Worker:
    __slots__ = ("x", "y", "px", "py", "t", "state", "home", "tx", "ty", "kind", "res",
                 "carry", "target", "farm", "timer", "stuck")

    def __init__(self, x, y, t):
        self.x = self.px = x
        self.y = self.py = y
        self.t = t
        self.state = IDLE
        self.home = (x, y)
        self.tx = self.ty = 0
        self.kind = KRES
        self.res = 0
        self.carry = 0
        self.target = None
        self.farm = None
        self.timer = 0
        self.stuck = 0


class Farm:
    __slots__ = ("cx", "cy", "t", "ring", "built", "count", "alive")

    def __init__(self, cx, cy, t, ring):
        self.cx, self.cy, self.t, self.ring = cx, cy, t, ring
        self.built = 0
        self.count = 0
        self.alive = True


class Sim:
    def __init__(self, ncivilisations, rng):
        self.rng = rng
        self.nt = ncivilisations
        self.civilisations = CIVILISATIONS[:ncivilisations]
        self.trader = next((i for i, t in enumerate(self.civilisations) if t.trade), None)
        self.world = {}                 # (x, y) -> (civilisation, age); infinite & sparse
        self.walls = {}                 # (x, y) -> (civilisation, hit points)
        self.walls_on = True
        self.wallpop = [0] * ncivilisations
        self._cities = []
        self.nature_on = True
        self.player = -1                # index of the civilisation the human rules (-1 = none)
        self.cp = 10.0                  # command points
        self.focus = 0                  # worker focus (index into FOCUS_NAMES)
        self.autopilot = False          # advisors build walls/farms for the player
        self.worker_bonus = 0
        self.grace_until = 0            # no starvation deaths for the player before this year
        self.buffs = {}                 # "crusade"/"bulwark" -> year it ends
        self.nature = {}                # (x, y) -> (kind, amount); amount 0 = stump/sprout
        self.fences = {}                # (x, y) -> civilisation   (farm pens)
        self.pen_tiles = set()          # reserved 5x5 farm areas
        self.animals = []
        self.animal_at = {}
        self.workers = []
        self.farms = []
        self.stock = [list(START_STOCK) for _ in range(ncivilisations)]
        self.starving = [False] * ncivilisations
        self._starve_log = [-999] * ncivilisations
        self.regrow = []                # heap of (due_year, seq, tile, kind)
        self._seq = itertools.count()
        self.chunks = set()
        self.chunk_list = []
        self.nseed = rng.getrandbits(32)
        self._homes = [[] for _ in range(ncivilisations)]
        self.year = 0
        self.mode = "civ"               # "civ" or "life"
        self.events_on = True
        self.history = deque(maxlen=HIST_MAX)   # (world, walls, year); never holds the live dicts
        self.conquests = [0] * ncivilisations
        self.pop = [0] * ncivilisations
        self.cities = [0] * ncivilisations
        self.log = deque(maxlen=80)
        self.ever_city = set()
        self.era = era_name(0)

    # -- bookkeeping -------------------------------------------------------- #
    def say(self, msg):
        self.log.append((self.year, msg))

    def recount(self, announce=False):
        pop = [0] * self.nt
        cit = [0] * self.nt
        civ = self.mode == "civ"
        civilisations = self.civilisations
        for t, a in self.world.values():
            pop[t] += 1
            if civ and a >= civilisations[t].city_age:
                cit[t] += 1
        if announce:
            if sum(self.pop) > 0 and sum(pop) == 0:
                self.say("All life has vanished from the world.")
            for t in range(self.nt):
                name = civilisations[t].name
                if self.pop[t] > 0 and pop[t] == 0:
                    self.say(f"The {name} have perished.")
                if cit[t] > 0 and t not in self.ever_city:
                    self.ever_city.add(t)
                    self.say(f"The {name} found their first city!")
        self.pop, self.cities = pop, cit
        wp = [0] * self.nt
        for t, _ in self.walls.values():
            wp[t] += 1
        self.wallpop = wp

    def checkpoint(self):
        """Remember the current world so rewind can undo a destructive action."""
        self.history.append((self.world, self.walls, self.year))

    # -- one tick of time --------------------------------------------------- #
    def step(self):
        w = self.world
        if len(w) <= HIST_CELL_LIMIT:
            self.history.append((w, self.walls, self.year))
        else:
            self.history.clear()
        nt = self.nt
        counts = {}
        for (x, y), cell in w.items():
            t = cell[0]
            for dx, dy in NEIGH:
                p = (x + dx, y + dy)
                arr = counts.get(p)
                if arr is None:
                    arr = counts[p] = [0] * nt
                arr[t] += 1
        new = {}
        if self.mode == "civ":
            self._civ_rules(w, counts, new)
            self.world = new
            self._wall_rules(counts, new)
            if self.nature_on:
                self._nature_step()
        else:
            self._life_rules(w, counts, new)
            self.world = new
            self.walls = dict(self.walls)      # keep history's copy untouched
        self.year += 1
        era = era_name(self.year)
        if era != self.era:
            self.era = era
            if self.mode == "civ":
                self.say(f"The {era} begins.")
        if self.mode == "civ" and self.events_on and new and self.rng.random() < 0.010:
            self.trigger_event(self.rng.choice(EVENTS))
        self.recount(announce=True)
        if self.mode == "civ":
            self._player_tick()

    def _life_rules(self, w, counts, new):
        rng = self.rng
        for p, arr in counts.items():
            total = sum(arr)
            cell = w.get(p)
            if cell is None:
                if total == 3:
                    d, _ = dominant(arr, rng)
                    new[p] = CELLS[d][0]
            elif total == 2 or total == 3:
                t, a = cell
                new[p] = CELLS[t][a + 1 if a < AGE_CAP else a]

    def _civ_rules(self, w, counts, new):
        rng, civilisations, nt, trader = self.rng, self.civilisations, self.nt, self.trader
        taken = [0] * nt
        lost = [0] * nt
        pl = self.player
        crus = pl >= 0 and self.year < self.buffs.get("crusade", 0)
        bul = pl >= 0 and self.year < self.buffs.get("bulwark", 0)
        colonies = []
        walls = self.walls
        cities = self._cities = []
        nat = self.nature if self.nature_on else {}
        fences, pens = self.fences, self.pen_tiles
        homes = self._homes = [[] for _ in range(nt)]
        for p, arr in counts.items():
            total = sum(arr)
            cell = w.get(p)
            if cell is None:                                   # --- birth
                if (2 <= total <= 6 and p not in walls and p not in fences and p not in pens
                        and (p not in nat or nat[p][1] == 0)):
                    d, _ = dominant(arr, rng)
                    if total in civilisations[d].birth:
                        new[p] = CELLS[d][0]
                    elif (total == 2 and trader is not None and arr[trader]
                          and sum(1 for v in arr if v) >= 2
                          and rng.random() < 0.15):            # rare trade post
                        new[p] = CELLS[trader][0]
                continue
            t, a = cell
            tr = civilisations[t]
            friends = arr[t]
            city = a >= tr.city_age
            if total > friends:                                # --- war
                e, ev = dominant(arr, rng, t)
                et = civilisations[e]
                defence = friends + (2 if city else 0)
                if walls:                                      # walls help the defenders
                    n = 0
                    for dx, dy in NEIGH:
                        wv = walls.get((p[0] + dx, p[1] + dy))
                        if wv is not None and wv[0] == t:
                            n += 1
                    defence += min(2, (n + 1) // 2)
                if bul and t == pl:                            # Bulwark decree
                    defence += 2
                need = max(1, et.conquer - (1 if crus and e == pl else 0))   # Crusade decree
                tie = et.tiewin or (crus and e == pl)
                if ev >= need and (ev > defence or (ev == defence and tie)):
                    new[p] = CELLS[e][0]
                    self.conquests[e] += 1
                    taken[e] += 1
                    lost[t] += 1
                    continue
            alive = (1 <= total <= tr.city_max) if city else (total in tr.survive)
            if alive and city and rng.random() < 0.006:        # cities fall to ruin now and then
                alive = False
            if alive:                                          # --- survival
                na = a + 1 if a < AGE_CAP else a
                new[p] = CELLS[t][na]
                if city:
                    cities.append((p, t))
                if na >= 6 and rng.random() < 300.0 / max(300, self.pop[t]):
                    homes[t].append(p)
                if city and total <= 3 and na % tr.colony == 0 and rng.random() < 0.3:
                    colonies.append((p, t))                    # only uncrowded cities colonise
        # lonely cities do not die
        for p, (t, a) in w.items():
            if p not in counts and a >= civilisations[t].city_age:
                new[p] = CELLS[t][a + 1 if a < AGE_CAP else a]
                cities.append((p, t))
        # cities found colonies
        for (x, y), t in colonies:
            q = (x + rng.randint(-2, 2), y + rng.randint(-2, 2))
            if (q not in new and q not in w and q not in walls and q not in fences
                    and q not in pens and (q not in nat or nat[q][1] == 0)):
                if self.nature_on:                    # a colony costs food
                    fs = self.stock[t]
                    if fs[FOOD] < 2:
                        continue
                    fs[FOOD] -= 2
                new[q] = CELLS[t][0]
        # nomads wander
        if any(tr.wander for tr in civilisations):
            movers = [p for p, c in new.items() if civilisations[c[0]].wander]
            for p in movers:
                if rng.random() < civilisations[new[p][0]].wander:
                    dx, dy = rng.choice(NEIGH)
                    q = (p[0] + dx, p[1] + dy)
                    if (q not in new and q not in w and q not in walls and q not in fences
                            and q not in pens and (q not in nat or nat[q][1] == 0)):
                        new[q] = new.pop(p)
        if pl >= 0 and lost[pl] >= 3 and rng.random() < 0.4:
            self.say(f"ALERT: enemies overrun your lands - {lost[pl]} holdings lost!")
        for e in range(nt):
            if taken[e] >= 6 and rng.random() < 0.25:
                self.say(f"The {civilisations[e].name} seize {taken[e]} holdings in battle.")

    def _foe_near(self, q, t, cells, r):
        x0, y0 = q
        for yy in range(y0 - r, y0 + r + 1):
            for xx in range(x0 - r, x0 + r + 1):
                c = cells.get((xx, yy))
                if c is not None and c[0] != t:
                    return True
        return False

    def _supported(self, q, t, cells, r=2):
        x0, y0 = q
        for yy in range(y0 - r, y0 + r + 1):
            for xx in range(x0 - r, x0 + r + 1):
                c = cells.get((xx, yy))
                if c is not None and c[0] == t:
                    return True
        return False

    def _wall_rules(self, counts, new):
        """Siege damage, decay, and new construction. Builds a fresh walls dict."""
        rng, civilisations, old = self.rng, self.civilisations, self.walls
        nw = {}
        breached = [0] * self.nt
        for p, (t, hp) in old.items():
            if p in new:                       # a settlement now stands here
                continue
            hp0 = hp
            arr = counts.get(p)
            if arr:
                foes = sum(arr) - arr[t]
                if foes >= 2:                  # besieged
                    e, _ = dominant(arr, rng, t)
                    if rng.random() < 0.10 * foes * (2 if civilisations[e].tiewin else 1):
                        hp -= 1
                        if hp <= 0:
                            breached[t] += 1
                            continue
            if rng.random() < 0.01:            # weathering; abandoned walls crumble faster
                hp -= 1
            elif rng.random() < 0.02 and not self._supported(p, t, new):
                hp -= 1
            if hp > 0:
                nw[p] = old[p] if hp == hp0 else (t, hp)
        if self.walls_on:
            cap = 14 * len(self._cities) + 20
            for (x, y), t in self._cities:
                if t == self.player and not self.autopilot:
                    continue                      # the player builds their own walls
                tr = civilisations[t]
                if rng.random() >= tr.wall or len(nw) >= cap:
                    continue
                while True:
                    dx, dy = rng.randint(-2, 2), rng.randint(-2, 2)
                    if max(abs(dx), abs(dy)) == 2:
                        break
                q = (x + dx, y + dy)
                if (q in new or q in nw or q in self.fences or q in self.pen_tiles
                        or (q in self.nature and self.nature[q][1] > 0)):
                    continue
                if rng.random() < 0.3 or self._foe_near(q, t, new, 3):   # frontier first
                    if self.nature_on:                # walls cost wood and stone
                        cost = WALL_COST.get(tr.name, (1, 1))
                        fs = self.stock[t]
                        if fs[WOOD] < cost[0] or fs[STONE] < cost[1]:
                            continue
                        fs[WOOD] -= cost[0]
                        fs[STONE] -= cost[1]
                    nw[q] = (t, tr.wall_hp)
        self.walls = nw
        for t in range(self.nt):
            if breached[t] >= 3 and rng.random() < 0.3:
                self.say(f"The {civilisations[t].name} walls are breached!")

    # -- nature, animals, workers, farms ------------------------------------ #
    def _free(self, p):
        return (p not in self.nature and p not in self.world and p not in self.walls
                and p not in self.fences and p not in self.pen_tiles)

    def _schedule(self, p, kind, lo=None, hi=None):
        a, b = NAT_REGROW[kind]
        delay = self.rng.randint(lo or a, hi or b)
        heapq.heappush(self.regrow, (self.year + delay, next(self._seq), p, kind))

    def ensure_area(self, x0, y0, x1, y1):
        """Lazily generate terrain so the world is endless."""
        for cx in range((x0 >> 4) - 1, (x1 >> 4) + 2):
            for cy in range((y0 >> 4) - 1, (y1 >> 4) + 2):
                if (cx, cy) not in self.chunks:
                    self.ensure_chunk(cx, cy)

    def ensure_chunk(self, cx, cy):
        key = (cx, cy)
        if key in self.chunks:
            return
        self.chunks.add(key)
        self.chunk_list.append(key)
        r = random.Random(self.nseed ^ (cx * 73856093) ^ (cy * 19349663))
        ox, oy = cx * CHUNK, cy * CHUNK
        nat = self.nature

        def blob(kind, rad, dens):
            bx, by = ox + r.randrange(CHUNK), oy + r.randrange(CHUNK)
            r2 = rad * rad + rad
            mx = NAT_MAX[kind]
            for dy in range(-rad, rad + 1):
                for dx in range(-rad, rad + 1):
                    if dx * dx + dy * dy <= r2 and r.random() < dens:
                        p = (bx + dx, by + dy)
                        if self._free(p):
                            nat[p] = (kind, r.randint(max(1, mx - 2), mx))

        for _ in range(r.choice((0, 0, 1, 1, 1, 2))):
            blob(TREE, r.randint(3, 6), 0.55)
        if r.random() < 0.4:
            blob(POND, r.randint(2, 4), 0.95)
        if r.random() < 0.6:
            blob(ROCK, r.randint(1, 3), 0.6)
        if r.random() < 0.35:
            blob(BERRY, r.randint(2, 3), 0.35)
        if r.random() < 0.5:
            self._spawn_herd(ox + r.randrange(CHUNK), oy + r.randrange(CHUNK), r.randint(3, 7), r)

    def _spawn_herd(self, hx, hy, n, rng):
        for _ in range(n):
            p = (hx + rng.randint(-2, 2), hy + rng.randint(-2, 2))
            if (self._free(p) and p not in self.animal_at and len(self.animals) < MAX_ANIMALS):
                a = Animal(*p)
                self.animals.append(a)
                self.animal_at[p] = a

    def place_nature(self, cx, cy, kind):
        n = 0
        for dy in range(-2, 3):
            for dx in range(-2, 3):
                p = (cx + dx, cy + dy)
                if dx * dx + dy * dy <= 5 and self.rng.random() < 0.75 and self._free(p):
                    self.nature[p] = (kind, NAT_MAX[kind])
                    n += 1
        return n

    def release_herd(self, cx, cy):
        self._spawn_herd(cx, cy, 6, self.rng)

    def reset_civ(self):
        self.workers, self.farms = [], []
        self.fences, self.pen_tiles = {}, set()
        self.stock = [list(START_STOCK) for _ in range(self.nt)]
        self.starving = [False] * self.nt
        for a in self.animals:
            a.pen = a.follow = None
            a.owner = -1

    def _adjacent_kind(self, p):
        nat = self.nature
        for dx, dy in NEIGH:
            v = nat.get((p[0] + dx, p[1] + dy))
            if v is not None and v[1] > 0 and v[0] in (TREE, BERRY):
                return v[0]
        return None

    def _nature_step(self):
        rng, year, w, nat = self.rng, self.year, self.world, self.nature
        if year % 6 == 0:                       # make sure terrain exists near every settlement
            for cx, cy in {(x >> 4, y >> 4) for (x, y) in w}:
                for dx in (-1, 0, 1):
                    for dy in (-1, 0, 1):
                        self.ensure_chunk(cx + dx, cy + dy)
        heap = self.regrow                      # regrowth: stumps, dry ponds, picked bushes
        while heap and heap[0][0] <= year:
            _, _, p, kind = heapq.heappop(heap)
            cur = nat.get(p)
            if cur is None or cur[0] != kind:
                continue
            if p in w or p in self.walls or p in self.fences:
                del nat[p]                      # settled over: cleared land
                continue
            nat[p] = (kind, NAT_MAX[kind])
            if kind in (TREE, BERRY) and rng.random() < 0.3:        # seeds spread
                q = (p[0] + rng.randint(-1, 1), p[1] + rng.randint(-1, 1))
                if self._free(q):
                    nat[q] = (kind, 0)
                    self._schedule(q, kind)
        for _ in range(2):                      # wild saplings creep out of forests
            if not self.chunk_list:
                break
            cx, cy = rng.choice(self.chunk_list)
            q = (cx * CHUNK + rng.randrange(CHUNK), cy * CHUNK + rng.randrange(CHUNK))
            if rng.random() < 0.5 and self._free(q):
                kind = self._adjacent_kind(q)
                if kind is not None:
                    nat[q] = (kind, 0)
                    self._schedule(q, kind)
        self._animals_step()
        self._workers_step()
        self._farms_step()
        self._economy_step()

    # animals ----------------------------------------------------------------
    def _animal_ok(self, q, at):
        if q in at or q in self.world or q in self.walls or q in self.fences:
            return False
        v = self.nature.get(q)
        return v is None or v[1] == 0

    def _animals_step(self):
        rng = self.rng
        self.animals = [a for a in self.animals if a.alive]
        at = self.animal_at = {(a.x, a.y): a for a in self.animals}
        cnt = Counter((a.x >> 4, a.y >> 4) for a in self.animals if a.pen is None)
        wild = sum(cnt.values())
        born = []
        for a in self.animals:
            if a.follow is not None:
                continue
            if a.pen is not None:                       # tame: mill about inside the pen
                f = a.pen
                if rng.random() < 0.5:
                    nx, ny = a.x + rng.randint(-1, 1), a.y + rng.randint(-1, 1)
                    if abs(nx - f.cx) <= 1 and abs(ny - f.cy) <= 1 and (nx, ny) not in at:
                        at.pop((a.x, a.y), None)
                        a.x, a.y = nx, ny
                        at[(nx, ny)] = a
                if f.count < PEN_MAX and rng.random() < 0.004:
                    spots = [(f.cx + i, f.cy + j) for i in (-1, 0, 1) for j in (-1, 0, 1)
                             if (f.cx + i, f.cy + j) not in at]
                    if spots:
                        q = rng.choice(spots)
                        b = Animal(*q)
                        b.pen, b.owner = f, f.t
                        born.append(b)
                        at[q] = b
                        f.count += 1
                continue
            if rng.random() < 0.35:                     # wild: wander
                dx, dy = rng.choice(NEIGH)
                q = (a.x + dx, a.y + dy)
                if self._animal_ok(q, at):
                    at.pop((a.x, a.y), None)
                    a.x, a.y = q
                    at[q] = a
            if rng.random() < 0.004 and wild < MAX_ANIMALS and cnt[(a.x >> 4, a.y >> 4)] < 9:
                dx, dy = rng.choice(NEIGH)                  # wild herds slowly regrow
                q = (a.x + dx, a.y + dy)
                if self._animal_ok(q, at):
                    b = Animal(*q)
                    born.append(b)
                    at[q] = b
                    wild += 1
                    cnt[(a.x >> 4, a.y >> 4)] += 1
        self.animals.extend(born)
        if self.year % 40 == 0 and wild < MAX_ANIMALS * 0.3 and self.chunk_list:
            cx, cy = rng.choice(self.chunk_list)            # new herds wander in
            self._spawn_herd(cx * CHUNK + rng.randrange(CHUNK), cy * CHUNK + rng.randrange(CHUNK),
                             rng.randint(3, 5), rng)

    # workers ----------------------------------------------------------------
    def _walkable(self, x, y, t):
        p = (x, y)
        c = self.world.get(p)
        if c is not None and c[0] != t:
            return False
        wv = self.walls.get(p)
        if wv is not None and wv[0] != t:
            return False
        f = self.fences.get(p)
        if f is not None and f != t:
            return False
        v = self.nature.get(p)
        return v is None or v[1] <= 0

    def _step_toward(self, wk, tx, ty):
        sx = (tx > wk.x) - (tx < wk.x)
        sy = (ty > wk.y) - (ty < wk.y)
        opts = [(sx, sy)]
        if sx and sy:
            opts += [(sx, 0), (0, sy)]
        elif sx:
            opts += [(sx, 1), (sx, -1)]
        elif sy:
            opts += [(1, sy), (-1, sy)]
        for dx, dy in opts:
            if (dx or dy) and self._walkable(wk.x + dx, wk.y + dy, wk.t):
                wk.px, wk.py = wk.x, wk.y
                wk.x += dx
                wk.y += dy
                return True
        dx, dy = self.rng.choice(NEIGH)                     # blocked: shuffle sideways
        if self._walkable(wk.x + dx, wk.y + dy, wk.t):
            wk.px, wk.py = wk.x, wk.y
            wk.x += dx
            wk.y += dy
        return False

    def _drop_animal(self, wk):
        a = wk.target
        if a is not None and a.follow is wk:
            a.follow = None
        wk.target = None

    def _move(self, wk):
        if self._step_toward(wk, wk.tx, wk.ty):
            wk.stuck = 0
        else:
            wk.stuck += 1
            if wk.stuck > 12:                               # give up on this errand
                self._drop_animal(wk)
                wk.carry = 0
                wk.state = IDLE
                wk.timer = self.rng.randint(3, 8)
        return True

    def _nearest_nature(self, x, y, kind, R):
        nat, rng = self.nature, self.rng
        for r in range(1, R + 1):
            hits = []
            for dx, dy in RINGS[r]:
                v = nat.get((x + dx, y + dy))
                if v is not None and v[0] == kind and v[1] > 0:
                    hits.append((x + dx, y + dy))
            if hits:
                return rng.choice(hits), r
        return None

    def _nearest_animal(self, x, y, R):
        at, rng = self.animal_at, self.rng
        if not at:
            return None
        for r in range(1, R + 1):
            hits = []
            for dx, dy in RINGS[r]:
                a = at.get((x + dx, y + dy))
                if a is not None and a.alive and a.pen is None and a.follow is None:
                    hits.append(a)
            if hits:
                return rng.choice(hits), r
        return None

    def _find_cell(self, x, y, t, R):
        w = self.world
        for r in range(0, R + 1):
            for dx, dy in (RINGS[r] if r else [(0, 0)]):
                c = w.get((x + dx, y + dy))
                if c is not None and c[0] == t:
                    return (x + dx, y + dy)
        return None

    def _take(self, p):
        v = self.nature.get(p)
        if v is None or v[1] <= 0:
            return None
        kind, amt = v
        self.nature[p] = (kind, amt - 1)
        if amt - 1 <= 0:
            self._schedule(p, kind)
        return kind

    def _workers_step(self):
        rng = self.rng
        counts = [0] * self.nt
        for wk in self.workers:
            counts[wk.t] += 1
        for t in range(self.nt):
            homes = self._homes[t]
            cap = min(60, 4 + self.pop[t] // 15) + (self.worker_bonus if t == self.player else 0)
            if homes and counts[t] < cap and rng.random() < 0.25:
                hx, hy = rng.choice(homes)
                self.workers.append(Worker(hx, hy, t))
        self.workers = [wk for wk in self.workers if self._worker_act(wk)]

    def _choose_task(self, wk):
        rng, t = self.rng, wk.t
        st = self.stock[t]
        farms = [f for f in self.farms if f.t == t and f.alive and f.count < PEN_MAX]
        fo = self.focus if t == self.player else 0
        if farms and rng.random() < (0.9 if fo == 5 else 0.45):                   # go and herd a wild animal home
            hit = self._nearest_animal(wk.x, wk.y, 14)
            if hit:
                f = min(farms, key=lambda f: abs(f.cx - wk.x) + abs(f.cy - wk.y))
                wk.state, wk.kind, wk.target, wk.farm, wk.stuck = GO, KHERD, hit[0], f, 0
                return
        target = 30 + 0.03 * self.pop[t]
        wts = [1.0 * (1 - min(1.0, st[WOOD] / target)) + 0.05,
               1.2 * (1 - min(1.0, st[STONE] / target)) + 0.05,
               2.0 * (1 - min(1.0, st[FOOD] / target)) + 0.05,
               1.6 * (1 - min(1.0, st[WATER] / target)) + 0.05]
        if 1 <= fo <= 4:
            wts[fo - 1] *= 5                                    # worker focus
        first = rng.choices(range(4), weights=wts)[0]
        for res in [first] + [k for k in range(4) if k != first]:
            if res == FOOD:
                b = self._nearest_nature(wk.x, wk.y, BERRY, 12)
                an = self._nearest_animal(wk.x, wk.y, 12)
                if an and (not b or an[1] <= b[1]):
                    wk.state, wk.kind, wk.target, wk.stuck = GO, KHUNT, an[0], 0
                    return
                hit = b
            else:
                hit = self._nearest_nature(wk.x, wk.y, RES_KIND[res], 12)
            if hit:
                wk.state, wk.kind, wk.stuck = GO, KRES, 0
                wk.tx, wk.ty = hit[0]
                return
        wk.timer = rng.randint(6, 14)                       # nothing in reach: wait and retry

    def _worker_act(self, wk):
        t = wk.t
        c = self.world.get((wk.x, wk.y))
        if c is not None and c[0] != t:                     # overrun by an enemy settlement
            self._drop_animal(wk)
            return False
        st = wk.state
        if st == IDLE:
            wk.timer -= 1
            if wk.timer <= 0:
                self._choose_task(wk)
            return True
        if st == GO:
            return self._act_go(wk)
        if st == WORK:
            kind = self._take((wk.tx, wk.ty))
            if kind is not None:
                wk.carry += 1
                wk.res = NAT_RES[kind]
                if wk.carry >= CARRY:
                    wk.state = BACK
            else:
                wk.state = BACK if wk.carry else IDLE
                wk.timer = 0
            return True
        if st == BACK:
            return self._act_back(wk)
        return self._act_lead(wk)

    def _act_go(self, wk):
        a = wk.target
        if wk.kind == KRES:
            v = self.nature.get((wk.tx, wk.ty))
            if v is None or v[1] <= 0:
                wk.state, wk.timer = IDLE, 0
                return True
        else:
            if a is None or not a.alive or a.follow is not None or a.pen is not None:
                wk.state, wk.target, wk.timer = IDLE, None, 0
                return True
            wk.tx, wk.ty = a.x, a.y
        if max(abs(wk.tx - wk.x), abs(wk.ty - wk.y)) <= 1:
            wk.stuck = 0
            if wk.kind == KRES:
                wk.state = WORK
            elif wk.kind == KHUNT:                          # the hunt: food straight to the sack
                a.alive = False
                self.animal_at.pop((a.x, a.y), None)
                wk.carry, wk.res, wk.state, wk.target = 4, FOOD, BACK, None
            else:                                           # herding: the animal follows
                f = wk.farm
                if f is None or not f.alive:
                    wk.state, wk.timer, wk.target = IDLE, 0, None
                    return True
                a.follow = wk
                wk.state = LEAD
            return True
        return self._move(wk)

    def _act_back(self, wk):
        hc = self.world.get(wk.home)
        if hc is None or hc[0] != wk.t:
            h = self._find_cell(wk.x, wk.y, wk.t, 10)
            if h is None:
                return False                                # homeless: gone
            wk.home = h
        hx, hy = wk.home
        if max(abs(hx - wk.x), abs(hy - wk.y)) <= 1:
            cap = 60 + 12 * self.cities[wk.t]
            s = self.stock[wk.t]
            s[wk.res] = min(cap, s[wk.res] + wk.carry)
            wk.carry = 0
            wk.state = IDLE
            wk.timer = self.rng.randint(0, 2)
            return True
        wk.tx, wk.ty = hx, hy
        return self._move(wk)

    def _act_lead(self, wk):
        a, f = wk.target, wk.farm
        if a is None or not a.alive or f is None or not f.alive:
            self._drop_animal(wk)
            wk.state, wk.timer = IDLE, 2
            return True
        at = self.animal_at
        if max(abs(f.cx - wk.x), abs(f.cy - wk.y)) <= 1:    # reached the pen
            spots = [(f.cx + i, f.cy + j) for i in (-1, 0, 1) for j in (-1, 0, 1)
                     if (f.cx + i, f.cy + j) not in at]
            if spots and f.count < PEN_MAX:
                q = self.rng.choice(spots)
                at.pop((a.x, a.y), None)
                a.x, a.y = q
                at[q] = a
                a.pen, a.owner, a.follow = f, wk.t, None
                f.count += 1
                wk.target = None
            else:
                self._drop_animal(wk)
            wk.state, wk.timer = IDLE, 3
            return True
        ok = self._step_toward(wk, f.cx, f.cy)
        at.pop((a.x, a.y), None)
        a.x, a.y = wk.px, wk.py                             # the animal trots behind its herder
        at[(a.x, a.y)] = a
        if ok:
            wk.stuck = 0
        else:
            wk.stuck += 1
            if wk.stuck > 12:
                self._drop_animal(wk)
                wk.state, wk.timer = IDLE, 4
        return True

    # farms ------------------------------------------------------------------
    def _farms_step(self):
        rng = self.rng
        for f in self.farms:
            if f.built < len(f.ring):                       # fences go up one tile per tick
                q = f.ring[f.built]
                v = self.nature.get(q)
                if q not in self.world and (v is None or v[1] <= 0):
                    self.fences[q] = f.t
                f.built += 1
            if f.count:
                cap = 60 + 12 * self.cities[f.t]
                s = self.stock[f.t]
                s[FOOD] = min(cap, s[FOOD] + 0.06 * f.count)
        if self.year % 30 == 0:                             # abandoned farms are released
            for f in list(self.farms):
                if not self._supported((f.cx, f.cy), f.t, self.world, 9):
                    f.alive = False
                    self.farms.remove(f)
                    for q in f.ring:
                        if self.fences.get(q) == f.t:
                            del self.fences[q]
                    for i in range(-2, 3):
                        for j in range(-2, 3):
                            self.pen_tiles.discard((f.cx + i, f.cy + j))
                    for a in self.animals:
                        if a.pen is f:
                            a.pen, a.owner = None, -1
        counts = Counter(f.t for f in self.farms)
        for t in range(self.nt):
            if t == self.player and not self.autopilot:
                continue                              # the player founds their own farms
            if (self.cities[t] >= 2 and self.stock[t][WOOD] >= FARM_COST
                    and counts[t] < min(6, 1 + self.cities[t] // 4) and rng.random() < 0.03):
                self._found_farm(t)

    def _found_farm(self, t):
        rng = self.rng
        mine = [p for p, tt in self._cities if tt == t]
        if not mine:
            return
        bx, by = rng.choice(mine)
        for _ in range(10):
            dx, dy = rng.randint(-9, 9), rng.randint(-9, 9)
            if max(abs(dx), abs(dy)) < 4:
                continue
            cx, cy = bx + dx, by + dy
            if all(self._free((cx + i, cy + j)) for i in range(-2, 3) for j in range(-2, 3)):
                ring = ([(cx + i, cy - 2) for i in range(-2, 3)]
                        + [(cx + 2, cy + j) for j in range(-1, 3)]
                        + [(cx + i, cy + 2) for i in range(1, -3, -1)]
                        + [(cx - 2, cy + j) for j in range(1, -2, -1)])
                self.farms.append(Farm(cx, cy, t, ring))
                for i in range(-2, 3):
                    for j in range(-2, 3):
                        self.pen_tiles.add((cx + i, cy + j))
                self.stock[t][WOOD] -= FARM_COST
                self.say(f"The {self.civilisations[t].name} raise a farm near ({cx},{cy}).")
                return

    # food & water ------------------------------------------------------------
    def _economy_step(self):
        w = self.world
        starving = [False] * self.nt
        for t in range(self.nt):
            if self.pop[t] == 0:
                continue
            s = self.stock[t]
            s[FOOD] = max(0.0, s[FOOD] - self.pop[t] * EAT_FOOD)
            s[WATER] = max(0.0, s[WATER] - self.pop[t] * EAT_WATER)
            starving[t] = s[FOOD] <= 0 or s[WATER] <= 0
            if t == self.player and self.year < self.grace_until:
                starving[t] = False      # your people have time to get organised
            if starving[t] and not self.starving[t] and self.year - self._starve_log[t] > 80:
                self._starve_log[t] = self.year
                self.say("YOUR people are starving!" if t == self.player
                         else f"The {self.civilisations[t].name} are starving!")
        self.starving = starving
        if any(starving):
            rng, civilisations = self.rng, self.civilisations
            dead = [p for p, (t, a) in w.items()
                    if starving[t] and rng.random() < (0.01 if a >= civilisations[t].city_age else 0.035)]
            for p in dead:
                del w[p]

    # -- the player's civilisation ------------------------------------------- #
    def found_city(self, x, y, t):
        p = (x, y)
        self.walls.pop(p, None)
        self.nature.pop(p, None)
        self.world[p] = CELLS[t][self.civilisations[t].city_age]
        self.recount()

    def found_capital(self, x, y, t):
        """A city with two neighbours: a stable little cluster that can't be overcrowded."""
        for dy in range(-3, 4):
            for dx in range(-3, 4):
                q = (x + dx, y + dy)
                c = self.world.get(q)
                if c is not None and c[0] == t:
                    del self.world[q]
        self.found_city(x, y, t)
        for q in ((x + 1, y), (x, y + 1)):
            self.nature.pop(q, None)
            self.walls.pop(q, None)
            self.world[q] = CELLS[t][0]
        self.recount()

    def score(self, t):
        farms = sum(1 for f in self.farms if f.t == t)
        return self.pop[t] + 10 * self.cities[t] + 15 * farms + 2 * self.wallpop[t]

    def objectives(self, t):
        farms = sum(1 for f in self.farms if f.t == t)
        c, w, pop = self.cities[t], self.wallpop[t], self.pop[t]
        return [("Found 3 cities", c >= 3, f"{min(c, 3)}/3"),
                ("Raise 20 wall tiles", w >= 20, f"{min(w, 20)}/20"),
                ("Build 2 farms", farms >= 2, f"{min(farms, 2)}/2"),
                ("Reach 150 people", pop >= 150, f"{min(pop, 150)}/150"),
                ("Survive to year 1000", self.year >= 1000, f"{min(self.year, 1000)}/1000")]

    def _afford(self, cp=0.0, **cost):
        if self.cp < cp:
            return f"Need {cp:g} command points ({self.cp:.0f} available)"
        if self.nature_on:
            st = self.stock[self.player]
            for k, name in enumerate(RES_NAMES):
                need = cost.get(name, 0)
                if st[k] < need:
                    return f"Need {need} {name} (you have {int(st[k])})"
        return None

    def _spend(self, cp=0.0, **cost):
        self.cp -= cp
        if self.nature_on:
            st = self.stock[self.player]
            for k, name in enumerate(RES_NAMES):
                st[k] -= cost.get(name, 0)

    def _player_tick(self):
        t = self.player
        if t < 0:
            return
        if self.nature_on and self.year % 50 == 0 and self.pop[t]:
            s = self.stock[t]
            low = [RES_NAMES[k] for k in (FOOD, WATER, WOOD, STONE) if s[k] < (8 if k in (FOOD, WATER) else 3)]
            if low:
                self.say("Advisor: you are low on " + ", ".join(low) + ".")

    def _near_own(self, x, y, r):
        t = self.player
        return self.pop[t] == 0 or self._supported((x, y), t, self.world, r)

    def player_found_city(self, x, y):
        t, p = self.player, (x, y)
        v = self.nature.get(p)
        if p in self.world or p in self.walls or p in self.fences or p in self.pen_tiles or (v and v[1] > 0):
            return False, "That tile is occupied"
        if not self._near_own(x, y, 14):
            return False, "Too far from your lands (14 tiles max)"
        msg = self._afford(0, food=10, wood=6, stone=2)
        if msg:
            return False, msg
        self._spend(0, food=10, wood=6, stone=2)
        self.found_city(x, y, t)
        self.say(f"You found a city at ({x},{y}).")
        return True, f"City founded at ({x},{y})"

    def _wall_cost(self):
        return WALL_COST.get(self.civilisations[self.player].name, (1, 1))

    def player_wall(self, x, y):
        t, p = self.player, (x, y)
        if not self._free(p):
            return False, "That tile is occupied"
        if not self._near_own(x, y, 8):
            return False, "Too far from your lands (8 tiles max)"
        wc = self._wall_cost()
        msg = self._afford(0, wood=wc[0], stone=wc[1])
        if msg:
            return False, msg
        self._spend(0, wood=wc[0], stone=wc[1])
        self.walls[p] = (t, self.civilisations[t].wall_hp)
        self.recount()
        return True, "Wall built"

    def player_fortify(self, x, y):
        t = self.player
        c = self.world.get((x, y))
        if c is None or c[0] != t:
            return False, "Put the cursor on one of your settlements"
        tiles = [(x + dx, y + dy) for dx, dy in RINGS[2] if self._free((x + dx, y + dy))]
        if not tiles:
            return False, "Nothing left to wall in here"
        wc = self._wall_cost()
        wood, stone = wc[0] * len(tiles), wc[1] * len(tiles)
        msg = self._afford(0, wood=wood, stone=stone)
        if msg:
            return False, msg
        self._spend(0, wood=wood, stone=stone)
        hp = self.civilisations[t].wall_hp
        for q in tiles:
            self.walls[q] = (t, hp)
        self.recount()
        self.say(f"You fortify the settlement at ({x},{y}).")
        return True, f"Fortified: {len(tiles)} wall tiles"

    def player_farm(self, x, y):
        t = self.player
        if not all(self._free((x + i, y + j)) for i in range(-2, 3) for j in range(-2, 3)):
            return False, "A farm needs a clear 5x5 area"
        if not self._near_own(x, y, 12):
            return False, "Too far from your lands (12 tiles max)"
        msg = self._afford(0, wood=FARM_COST)
        if msg:
            return False, msg
        self._spend(0, wood=FARM_COST)
        ring = ([(x + i, y - 2) for i in range(-2, 3)] + [(x + 2, y + j) for j in range(-1, 3)]
                + [(x + i, y + 2) for i in range(1, -3, -1)] + [(x - 2, y + j) for j in range(1, -2, -1)])
        self.farms.append(Farm(x, y, t, ring))
        for i in range(-2, 3):
            for j in range(-2, 3):
                self.pen_tiles.add((x + i, y + j))
        self.say(f"You raise a farm at ({x},{y}). Workers will herd animals in.")
        return True, "Farm founded - your workers will herd animals into it"

    def player_hire(self):
        if self.worker_bonus >= 30:
            return False, "You already employ as many workers as you can feed"
        msg = self._afford(0, food=6, wood=2)
        if msg:
            return False, msg
        self._spend(0, food=6, wood=2)
        self.worker_bonus += 3
        return True, f"Hired more workers (+{self.worker_bonus} above normal)"

    def player_decree(self, name):
        cost = {"crusade": dict(stone=8), "bulwark": dict(wood=8)}[name]
        length = {"crusade": 25, "bulwark": 30}[name]
        if self.year < self.buffs.get(name, 0):
            return False, f"The {name.title()} decree is already in force"
        msg = self._afford(**cost)
        if msg:
            return False, msg
        self._spend(**cost)
        self.buffs[name] = self.year + length
        self.say(f"You proclaim a {name.title()} ({length} years).")
        return True, f"{name.title()} decreed for {length} years"

    def build_cost(self, kind):
        """Human-readable price of the selected structure."""
        wc = self._wall_cost() if self.player >= 0 else (1, 1)

        def fmt(**c):
            return ", ".join(f"{v} {k}" for k, v in c.items() if v)
        if kind == 0:
            return fmt(food=10, wood=6, stone=2)
        if kind == 1:
            return fmt(wood=wc[0], stone=wc[1]) + " per tile"
        if kind == 2:
            return fmt(wood=wc[0] * 16, stone=wc[1] * 16) + " for a full ring"
        return fmt(wood=FARM_COST)

    def player_demolish(self, x, y):
        wv = self.walls.get((x, y))
        if wv is None or wv[0] != self.player:
            return False, "No wall of yours here"
        del self.walls[(x, y)]
        self.recount()
        return True, "Wall pulled down"

    def player_barter(self, src, dst):
        msg = self._afford(0, **{RES_NAMES[src]: 8})
        if msg:
            return False, msg
        self._spend(0, **{RES_NAMES[src]: 8})
        cap = 60 + 12 * self.cities[self.player]
        st = self.stock[self.player]
        st[dst] = min(cap, st[dst] + 4)
        return True, f"Traded 8 {RES_NAMES[src]} for 4 {RES_NAMES[dst]}"

    # -- editing the world -------------------------------------------------- #
    def spawn_blob(self, cx, cy, t, radius, density, overwrite=False):
        w, rng, n = self.world, self.rng, 0
        r2 = radius * radius + radius
        for dy in range(-radius, radius + 1):
            for dx in range(-radius, radius + 1):
                if dx * dx + dy * dy <= r2 and rng.random() < density:
                    p = (cx + dx, cy + dy)
                    nv = self.nature.get(p)
                    if overwrite or (p not in w and p not in self.walls and p not in self.fences
                                     and (nv is None or nv[1] == 0)):
                        self.walls.pop(p, None)
                        self.nature.pop(p, None)
                        w[p] = CELLS[t][0]
                        n += 1
        return n

    def trigger_event(self, name, anchor=None, exact=False):
        w, rng, civilisations = self.world, self.rng, self.civilisations
        if anchor is None:
            anchor = rng.choice(list(w)) if w else (0, 0)
        ax, ay = anchor
        pop = Counter(c[0] for c in w.values())
        live = [t for t in range(self.nt) if pop[t] > 0]

        def kill(pred, prob=1.0, walls=False):
            dead = [p for p in w if pred(p) and (prob >= 1.0 or rng.random() < prob)]
            for p in dead:
                del w[p]
            if walls:
                for p in [p for p in self.walls if pred(p)]:
                    del self.walls[p]
            return len(dead)

        if name == "Plague":
            if not live:
                return
            t = rng.choices(live, weights=[pop[i] for i in live])[0]
            frac = rng.uniform(0.2, 0.45)
            dead = [p for p, c in w.items() if c[0] == t and rng.random() < frac]
            for p in dead:
                del w[p]
            self.say(f"Plague strikes the {civilisations[t].name}: {len(dead)} lost.")
        elif name == "Famine":
            r = rng.randint(8, 14)
            n = kill(lambda p: (p[0] - ax) ** 2 + (p[1] - ay) ** 2 <= r * r, 0.6)
            if n:
                self.say(f"Famine near ({ax},{ay}): {n} perish.")
        elif name == "Flood":
            half, width = rng.randint(15, 30), rng.randint(1, 2)
            if rng.random() < 0.5:
                n = kill(lambda p: abs(p[1] - ay) <= width and abs(p[0] - ax) <= half, walls=True)
            else:
                n = kill(lambda p: abs(p[0] - ax) <= width and abs(p[1] - ay) <= half, walls=True)
            if n:
                self.say(f"A great flood sweeps ({ax},{ay}): {n} lost.")
        elif name == "Meteor":
            r = rng.randint(4, 7)
            n = kill(lambda p: (p[0] - ax) ** 2 + (p[1] - ay) ** 2 <= r * r, walls=True)
            self.say(f"A meteor hits ({ax},{ay})! {n} lost.")
        elif name == "Golden age":
            if not live:
                return
            t = w[anchor][0] if anchor in w else rng.choice(live)
            mine = [p for p, c in w.items() if c[0] == t]
            cities = [p for p in mine if w[p][1] >= civilisations[t].city_age]
            centres = cities or rng.sample(mine, min(4, len(mine)))
            for cx, cy in centres[:12]:
                self.spawn_blob(cx + rng.randint(-3, 3), cy + rng.randint(-3, 3), t, 2, 0.6)
            self.say(f"A golden age blesses the {civilisations[t].name}!")
        elif name == "Barbarian horde":
            t = rng.randrange(self.nt)
            if exact:
                ox, oy = ax, ay
            else:
                ang, d = rng.uniform(0, 2 * math.pi), rng.randint(10, 20)
                ox, oy = int(ax + math.cos(ang) * d), int(ay + math.sin(ang) * d)
            self.spawn_blob(ox, oy, t, rng.randint(3, 5), 0.6, overwrite=True)
            self.say(f"A horde of {civilisations[t].name} appears near ({ox},{oy})!")
        elif name == "Wildfire":
            r = rng.randint(8, 12)
            burnt = 0
            for p, (k, amt) in list(self.nature.items()):
                if k == TREE and amt > 0 and (p[0] - ax) ** 2 + (p[1] - ay) ** 2 <= r * r:
                    self.nature[p] = (TREE, 0)
                    self._schedule(p, TREE)
                    burnt += 1
            n = kill(lambda p: (p[0] - ax) ** 2 + (p[1] - ay) ** 2 <= r * r, 0.3, walls=True)
            for a in self.animals:
                if (a.x - ax) ** 2 + (a.y - ay) ** 2 <= r * r and rng.random() < 0.5:
                    a.alive = False
            if burnt or n:
                self.say(f"Wildfire at ({ax},{ay}): {burnt} trees and {n} homes burn.")
        elif name == "Drought":
            n = 0
            for p, (k, amt) in list(self.nature.items()):
                if k == POND and amt > 0 and (p[0] - ax) ** 2 + (p[1] - ay) ** 2 <= 625:
                    self.nature[p] = (POND, 0)
                    self._schedule(p, POND, 80, 160)
                    n += 1
            if n:
                self.say(f"Drought near ({ax},{ay}): {n} ponds run dry.")

    def prune_radius(self, fx, fy, radius):
        w = self.world
        keep = {p: c for p, c in w.items()
                if max(abs(p[0] - fx), abs(p[1] - fy)) <= radius}
        removed = len(w) - len(keep)
        if removed:
            self.checkpoint()
            self.world = keep
            self.walls = {q: v for q, v in self.walls.items()
                          if max(abs(q[0] - fx), abs(q[1] - fy)) <= radius}
        return removed

    def prune_to(self, limit, fx, fy):
        w = self.world
        if len(w) <= limit:
            return 0
        order = sorted(w, key=lambda p: max(abs(p[0] - fx), abs(p[1] - fy)))
        self.world = {p: w[p] for p in order[:limit]}
        cut = max(abs(order[limit - 1][0] - fx), abs(order[limit - 1][1] - fy))
        self.walls = {q: v for q, v in self.walls.items()
                      if max(abs(q[0] - fx), abs(q[1] - fy)) <= cut}
        return len(w) - limit


# --------------------------------------------------------------------------- #
# the terminal front-end
# --------------------------------------------------------------------------- #

class Game:
    def __init__(self, args, rng):
        self.rng = rng
        self.sim = Sim(args.civilisations, rng)
        self.sim.mode = args.rules
        self.ascii = args.ascii or "utf" not in (locale.getpreferredencoding(False) or "").lower()
        self.glyphs = ("..", "oo", "##") if self.ascii else ("░░", "▓▓", "██")
        self.dot = ". " if self.ascii else "· "
        self.ng = GLYPHS["ascii" if self.ascii else ("emoji" if getattr(args, "emoji", False) else "uni")]
        self.nat_kind = 0
        self.nat_attr = {k: 0 for k in range(4)}
        self.animal_attr = 0
        self.use_mouse = not args.no_mouse
        self.speed_idx = SPEEDS.index(args.speed)
        self.paused = False
        self.brush = 0
        self.pat = 0
        self.auto = 1
        self.event_idx = 0
        self.cx = self.cy = 0           # cursor (world coordinates)
        self.camx = self.camy = 0       # world coordinate of the top-left visible cell
        self.vw = self.vh = 20
        self.rows = self.cols = 0
        self.panel_pref = None
        self.panel_w = 0
        self.menu_open = False
        self.menu_sel = 0
        self.menu_top = 0
        self.toast = None
        self.toast_until = 0.0
        self.running = True
        self.dirty = True
        self.last_mouse = 0.0
        self.last_tick = 0.0
        self.color_ok = False
        self.styles = []
        self.args = args
        self.outcome = None
        self.outcome_open = False
        self.reason = ""
        self.last_player = 0
        self.barter_pairs = list(itertools.permutations(range(4), 2))
        self.barter_idx = 0
        self.build_sel = 0
        self.start_player = -1 if args.sandbox else getattr(args, "play_idx", None)
        self._menu_base = self.build_menu()
        self._menu_play = self.build_play_menu()
        self.seed_world()

    # -- setup -------------------------------------------------------------- #
    def seed_world(self):
        n = self.sim.nt
        for i in range(n):
            ang = 2 * math.pi * i / n
            self.sim.spawn_blob(int(round(14 * math.cos(ang))), int(round(14 * math.sin(ang))),
                                i, 4, 0.55)
        self.sim.ensure_area(-60, -40, 60, 40)
        self.sim.recount()
        self.sim.say("Civilisations awaken. History begins.")

    def init_colors(self):
        try:
            curses.start_color()
            try:
                curses.use_default_colors()
                bg = -1
            except curses.error:
                bg = curses.COLOR_BLACK
            wide = curses.COLORS >= 256
            for i, tr in enumerate(self.sim.civilisations):
                curses.init_pair(i + 1, tr.c256 if wide else tr.c8, bg)
            for pid, c256, c8 in ((11, 34, curses.COLOR_GREEN), (12, 245, curses.COLOR_WHITE),
                                  (13, 39, curses.COLOR_BLUE), (14, 197, curses.COLOR_RED),
                                  (15, 180, curses.COLOR_YELLOW)):
                curses.init_pair(pid, c256 if wide else c8, bg)
            self.color_ok = True
        except curses.error:
            self.color_ok = False
        self.styles = []
        for i in range(self.sim.nt):
            base = curses.color_pair(i + 1) if self.color_ok else 0
            self.styles.append((base | curses.A_DIM, base, base | curses.A_BOLD))
        cp = (lambda n: curses.color_pair(n)) if self.color_ok else (lambda n: 0)
        self.nat_attr = {k: cp(11 + k) for k in range(4)}
        self.animal_attr = cp(15)

    def layout(self):
        self.rows, self.cols = self.scr.getmaxyx()
        show = self.panel_pref if self.panel_pref is not None else (
            self.cols >= 100 or (self.sim.player >= 0 and self.cols >= 70))
        self.panel_w = PANEL_W if show and self.cols >= PANEL_W + 30 else 0
        self.vw = max(1, (self.cols - self.panel_w) // 2)
        self.vh = max(1, self.rows - 2)
        self.follow()

    def follow(self):
        m = min(3, self.vw // 4, self.vh // 4)
        if self.cx < self.camx + m:
            self.camx = self.cx - m
        elif self.cx >= self.camx + self.vw - m:
            self.camx = self.cx - self.vw + m + 1
        if self.cy < self.camy + m:
            self.camy = self.cy - m
        elif self.cy >= self.camy + self.vh - m:
            self.camy = self.cy - self.vh + m + 1

    # -- main loop (never blocks on the menu: the world keeps ticking) ------ #
    def run(self, scr):
        self.scr = scr
        try:
            curses.curs_set(0)
        except curses.error:
            pass
        scr.keypad(True)
        self.init_colors()
        if self.use_mouse:
            try:
                curses.mousemask(curses.ALL_MOUSE_EVENTS)
            except curses.error:
                pass
        self.layout()
        self.camx, self.camy = -self.vw // 2, -self.vh // 2
        if self.start_player is None:
            self.start_player = self.choose_civ()
            if not self.running:
                return
        if self.start_player >= 0:
            self.set_player(self.start_player, fresh=True)
        self.last_tick = time.monotonic()
        while self.running:
            now = time.monotonic()
            interval = 1.0 / SPEEDS[self.speed_idx]
            wait = 0.05 if self.paused else interval - (now - self.last_tick)
            scr.timeout(int(max(1, min(40, wait * 1000))))
            k = scr.getch()
            while k != -1:
                self.layout()
                self.handle_key(k)
                self.dirty = True
                scr.timeout(0)
                k = scr.getch()
            self.layout()
            interval = 1.0 / SPEEDS[self.speed_idx]
            now = time.monotonic()
            if self.paused:
                self.last_tick = now
            else:
                due = 0
                while now - self.last_tick >= interval and due < 4:
                    self.tick()
                    self.last_tick += interval
                    due += 1
                    self.dirty = True
                if due == 4:                     # can't keep up: drop the backlog
                    self.last_tick = now
            if self.toast and now > self.toast_until:
                self.toast = None
                self.dirty = True
            if self.dirty:
                self.draw()
                self.dirty = False

    def tick(self):
        sim = self.sim
        sim.step()
        self.check_outcome()
        rate = AUTOSPAWN[self.auto][1]
        if rate:
            if not sim.world:
                self.random_spawn(3)
            elif sim.rng.random() < rate:
                self.random_spawn(1)
        if len(sim.world) > MAX_POP:
            n = sim.prune_to(int(MAX_POP * 0.7), self.cx, self.cy)
            sim.say(f"{n} distant souls fade into legend.")
            sim.recount()

    def say_toast(self, msg):
        self.toast = msg
        self.toast_until = time.monotonic() + 3.0

    # -- actions (shared by hotkeys, mouse and the menu) -------------------- #
    def toggle_pause(self):
        self.paused = not self.paused
        self.say_toast("Paused" if self.paused else "Running")

    def change_speed(self, d):
        self.speed_idx = max(0, min(len(SPEEDS) - 1, self.speed_idx + d))
        self.say_toast(f"Speed: {SPEEDS[self.speed_idx]} ticks/s")

    def toggle_rules(self):
        if self.locked():
            return
        sim = self.sim
        sim.mode = "life" if sim.mode == "civ" else "civ"
        sim.recount()
        self.say_toast("Rules: Classic Life (B3/S23)" if sim.mode == "life"
                       else "Rules: Civilisation")

    def change_brush(self, d):
        self.brush = (self.brush + d) % self.sim.nt
        self.say_toast(f"Brush: {self.sim.civilisations[self.brush].name}")

    def change_pattern(self, d):
        self.pat = (self.pat + d) % len(PATTERN_NAMES)
        self.say_toast(f"Pattern: {PATTERN_NAMES[self.pat]}")

    def change_auto(self, d):
        self.auto = (self.auto + d) % len(AUTOSPAWN)
        self.say_toast(f"Auto-spawn: {AUTOSPAWN[self.auto][0]}")

    def toggle_events(self):
        self.sim.events_on = not self.sim.events_on
        self.say_toast("Random events " + ("ON" if self.sim.events_on else "OFF"))

    def change_event(self, d):
        self.event_idx = (self.event_idx + d) % len(EVENTS)
        self.say_toast(f"Event: {EVENTS[self.event_idx]}")

    def trigger_event(self):
        if self.locked():
            return
        name = EVENTS[self.event_idx]
        self.sim.trigger_event(name, anchor=(self.cx, self.cy), exact=True)
        self.sim.recount()
        self.say_toast(f"{name} at ({self.cx},{self.cy})")

    def build_wall(self):
        if self.sim.player >= 0:
            self.play_wall()
            return
        sim, p = self.sim, (self.cx, self.cy)
        if p in sim.walls:
            del sim.walls[p]
            self.say_toast("Wall removed")
        elif p in sim.world:
            self.say_toast("A settlement stands here")
        else:
            tr = sim.civilisations[self.brush]
            sim.walls[p] = (self.brush, tr.wall_hp)
            self.say_toast(f"{tr.name} wall built")
        sim.recount()

    def toggle_nature(self):
        if self.locked():
            return
        self.sim.nature_on = not self.sim.nature_on
        self.say_toast("Nature, workers & resources " + ("ON" if self.sim.nature_on else "OFF"))

    def change_nat_kind(self, d):
        self.nat_kind = (self.nat_kind + d) % 4
        self.say_toast(f"Nature brush: {NAT_NAMES[self.nat_kind]}")

    def place_nature(self):
        if self.locked():
            return
        n = self.sim.place_nature(self.cx, self.cy, self.nat_kind)
        self.say_toast(f"Placed {NAT_NAMES[self.nat_kind]} ({n} tiles)")

    def release_herd(self):
        if self.locked():
            return
        self.sim.release_herd(self.cx, self.cy)
        self.say_toast("A herd wanders in")

    def toggle_walls(self):
        self.sim.walls_on = not self.sim.walls_on
        self.say_toast("Cities build walls: " + ("ON" if self.sim.walls_on else "OFF"))

    def move(self, dx, dy):
        self.cx += dx
        self.cy += dy
        self.follow()

    def toggle_cell(self):
        if self.locked():
            return
        w, p = self.sim.world, (self.cx, self.cy)
        if p in w:
            del w[p]
        else:
            self.sim.walls.pop(p, None)
            self.sim.nature.pop(p, None)
            w[p] = CELLS[self.brush][0]
        self.sim.recount()

    def erase_cell(self):
        if self.locked():
            return
        self.sim.world.pop((self.cx, self.cy), None)
        self.sim.recount()

    def stamp(self):
        if self.locked():
            return
        name, w = PATTERN_NAMES[self.pat], self.sim.world
        for dx, dy in PATTERN_CELLS[name]:
            p = (self.cx + dx, self.cy + dy)
            self.sim.walls.pop(p, None)
            self.sim.nature.pop(p, None)
            w[p] = CELLS[self.brush][0]
        self.sim.recount()
        self.say_toast(f"Stamped {name} ({self.sim.civilisations[self.brush].name})")

    def settle_here(self):
        if self.sim.player >= 0:
            self.play_found_city()
            return
        sim = self.sim
        n = sim.spawn_blob(self.cx, self.cy, self.brush, 3, 0.6, overwrite=True)
        sim.recount()
        sim.say(f"{sim.civilisations[self.brush].name} settle at ({self.cx},{self.cy}).")
        self.say_toast(f"Founded a settlement ({n} homes)")

    def random_spawn(self, count):
        sim, rng = self.sim, self.rng
        for _ in range(count):
            t = rng.randrange(sim.nt)
            x = rng.randint(self.camx - 5, self.camx + self.vw + 5)
            y = rng.randint(self.camy - 5, self.camy + self.vh + 5)
            if sim.pop[t] == 0 and sim.year > 0:
                sim.say(f"The {sim.civilisations[t].name} arrive near ({x},{y}).")
            sim.spawn_blob(x, y, t, rng.randint(2, 4), rng.uniform(0.4, 0.65))
        sim.recount()

    def burst(self):
        if self.locked():
            return
        self.random_spawn(4)
        self.say_toast("Random burst!")

    def step_once(self):
        self.tick()
        self.say_toast(f"Stepped to year {self.sim.year}")

    def rewind(self):
        if self.locked():
            return
        sim = self.sim
        if not sim.history:
            self.say_toast("Nothing further back in time")
            return
        sim.world, sim.walls, sim.year = sim.history.pop()
        sim.era = era_name(sim.year)
        sim.recount()
        self.say_toast(f"Rewound to year {sim.year} (resuming starts a new timeline)")

    def find_life(self):
        w = self.sim.world
        if not w:
            self.say_toast("Nothing alive anywhere")
            return
        xs = sorted(p[0] for p in w)
        ys = sorted(p[1] for p in w)
        self.cx, self.cy = xs[len(xs) // 2], ys[len(ys) // 2]
        self.camx, self.camy = self.cx - self.vw // 2, self.cy - self.vh // 2
        self.say_toast(f"Civilisation centred near ({self.cx},{self.cy})")

    def go_origin(self):
        self.cx = self.cy = 0
        self.camx, self.camy = -self.vw // 2, -self.vh // 2
        self.say_toast("Back at the origin")

    def prune_far(self):
        if self.locked():
            return
        n = self.sim.prune_radius(self.cx, self.cy, 120)
        self.sim.recount()
        self.say_toast(f"Pruned {n} far-away cells (rewind to undo)")

    def clear_world(self):
        if self.locked():
            return
        sim = self.sim
        sim.checkpoint()
        sim.world = {}
        sim.walls = {}
        sim.reset_civ()
        sim.recount()
        self.say_toast("World cleared (rewind to undo)")

    def quit(self):
        self.running = False

    # -- menu --------------------------------------------------------------- #
    def build_menu(self):
        sim = self.sim

        def kv(k, v):
            return f"{k:<20}{v}"

        return [
            (lambda: kv("Simulation", "[PAUSED]" if self.paused else "[RUNNING]"),
             lambda d: self.toggle_pause(), self.toggle_pause),
            (lambda: kv("Speed", f"< {SPEEDS[self.speed_idx]} ticks/s >"), self.change_speed, None),
            (lambda: kv("Rules", "< Civilisation >" if sim.mode == "civ" else "< Classic Life >"),
             lambda d: self.toggle_rules(), self.toggle_rules),
            (lambda: kv("Brush civilisation", f"< {sim.civilisations[self.brush].name} >"), self.change_brush, None),
            (lambda: kv("Pattern", f"< {PATTERN_NAMES[self.pat]} >"), self.change_pattern, self.stamp),
            ("Stamp pattern at cursor", None, self.stamp),
            ("Build / remove wall at cursor", None, self.build_wall),
            (lambda: kv("Cities build walls", "< On >" if sim.walls_on else "< Off >"),
             lambda d: self.toggle_walls(), self.toggle_walls),
            (lambda: kv("Nature & workers", "< On >" if sim.nature_on else "< Off >"),
             lambda d: self.toggle_nature(), self.toggle_nature),
            (lambda: kv("Nature brush", f"< {NAT_NAMES[self.nat_kind]} >"),
             self.change_nat_kind, self.place_nature),
            ("Place nature at cursor", None, self.place_nature),
            ("Release a herd at cursor", None, self.release_herd),
            ("Found settlement at cursor", None, self.settle_here),
            ("Random burst in view", None, self.burst),
            (lambda: kv("Auto-spawn", f"< {AUTOSPAWN[self.auto][0]} >"), self.change_auto, None),
            (lambda: kv("Random events", "< On >" if sim.events_on else "< Off >"),
             lambda d: self.toggle_events(), self.toggle_events),
            (lambda: kv("Trigger event", f"< {EVENTS[self.event_idx]} >"),
             self.change_event, self.trigger_event),
            ("Step forward one tick", None, self.step_once),
            ("Rewind one tick", None, self.rewind),
            ("Jump to civilisation", None, self.find_life),
            ("Jump to origin (0,0)", None, self.go_origin),
            ("Prune cells far from cursor", None, self.prune_far),
            ("Clear the world", None, self.clear_world),
            (lambda: kv("Rule a civilisation", "< " + self.ruler_name() + " >"),
             self.cycle_player, self.cycle_player),
            ("Quit", None, self.quit),
        ]

    def build_play_menu(self):
        sim = self.sim

        def kv(k, v):
            return f"{k:<20}{v}"

        return [
            (lambda: kv("Ruling", "< " + self.ruler_name() + " >"), self.cycle_player, None),
            (lambda: kv("Build  [t / 1-4]", f"< {BUILD_NAMES[self.build_sel]} >"), self.change_build, self.play_place),
            ("Place selected     [Space]", None, self.play_place),
            ("Found city at cursor [e]", None, self.play_found_city),
            ("Build wall at cursor [b]", None, self.play_wall),
            ("Fortify settlement   [r]", None, self.play_fortify),
            ("Found farm at cursor [f]", None, self.play_farm),
            ("Hire workers         [h]", None, self.play_hire),
            (lambda: kv("Worker focus [v]", f"< {FOCUS_NAMES[sim.focus]} >"), self.change_focus, None),
            ("Decree: Crusade      [k]", None, lambda: self.play_decree("crusade")),
            ("Decree: Bulwark      [g]", None, lambda: self.play_decree("bulwark")),
            (lambda: kv("Barter", "< %s -> %s >" % tuple(RES_NAMES[i] for i in self.barter_pairs[self.barter_idx])),
             self.change_barter, self.play_barter),
            (lambda: kv("Advisors [l]", "< On >" if sim.autopilot else "< Off >"),
             lambda d: self.toggle_autopilot(), self.toggle_autopilot),
        ]

    @property
    def menu(self):
        return (self._menu_play + self._menu_base) if self.sim.player >= 0 else self._menu_base

    # -- playing a civilisation --------------------------------------------- #
    def ruler_name(self):
        t = self.sim.player
        return self.sim.civilisations[t].name if t >= 0 else "Sandbox"

    def locked(self):
        if self.sim.player >= 0:
            self.say_toast("Sandbox tool - locked while you rule. Press Space to build, t to choose what (Tab = sandbox)")
            return True
        return False

    def set_player(self, p, fresh=False):
        sim = self.sim
        sim.player, sim.cp, sim.focus = p, 10.0, 0
        sim.autopilot, sim.worker_bonus, sim.buffs = False, 0, {}
        self.outcome, self.outcome_open = None, False
        self.menu_sel = self.menu_top = 0
        if p < 0:
            self.say_toast("Sandbox mode - every tool unlocked")
            return
        self.last_player, self.brush = p, p
        if fresh:                                        # give the new ruler a capital
            n = sim.nt
            x = int(round(14 * math.cos(2 * math.pi * p / n)))
            y = int(round(14 * math.sin(2 * math.pi * p / n)))
            sim.found_capital(x, y, p)
            sim.stock[p] = [0.0, 0.0, 0.0, 0.0]          # nothing: your workers must gather it all
            sim.worker_bonus = 8
            for _ in range(10):
                sim.workers.append(Worker(x, y, p))
            sim.ensure_area(x - 30, y - 30, x + 30, y + 30)
            self.cx, self.cy = x, y
            self.camx, self.camy = x - self.vw // 2, y - self.vh // 2
            sim.say(f"You rule the {sim.civilisations[p].name}. Your stores are empty: your workers must gather everything.")
        sim.grace_until = sim.year + 80
        self.say_toast(f"You rule the {sim.civilisations[p].name}. Your stores are empty - your workers are out gathering. "
                       f"Space builds, t chooses what.")

    def cycle_player(self, d=1):
        sim = self.sim
        opts = [-1] + list(range(sim.nt))
        self.set_player(opts[(opts.index(sim.player) + d) % len(opts)])

    def _report(self, res):
        self.say_toast(res[1])

    def play_found_city(self):
        self._report(self.sim.player_found_city(self.cx, self.cy))

    def play_wall(self):
        self._report(self.sim.player_wall(self.cx, self.cy))

    def play_fortify(self):
        self._report(self.sim.player_fortify(self.cx, self.cy))

    def play_farm(self):
        self._report(self.sim.player_farm(self.cx, self.cy))

    def play_place(self):
        (self.play_found_city, self.play_wall, self.play_fortify, self.play_farm)[self.build_sel]()

    def change_build(self, d):
        self.build_sel = (self.build_sel + d) % len(BUILD_NAMES)
        self.say_toast(f"Building: {BUILD_NAMES[self.build_sel]} - costs {self.sim.build_cost(self.build_sel)}. "
                       f"Space places it.")

    def play_demolish(self):
        self._report(self.sim.player_demolish(self.cx, self.cy))

    def play_help(self):
        sim = self.sim
        return (f"SPACE builds {BUILD_NAMES[self.build_sel]} [{sim.build_cost(self.build_sel)}] | t/1-4 choose | "
                "e city b wall r fortify f farm | h hire | v focus | k crusade g bulwark | l advisors | x pull wall | Tab sandbox | m menu")

    def play_hire(self):
        self._report(self.sim.player_hire())

    def play_decree(self, name):
        self._report(self.sim.player_decree(name))

    def change_focus(self, d):
        self.sim.focus = (self.sim.focus + d) % len(FOCUS_NAMES)
        self.say_toast(f"Workers now focus on: {FOCUS_NAMES[self.sim.focus]}")

    def change_barter(self, d):
        self.barter_idx = (self.barter_idx + d) % len(self.barter_pairs)

    def play_barter(self):
        a, b = self.barter_pairs[self.barter_idx]
        self._report(self.sim.player_barter(a, b))

    def toggle_autopilot(self):
        self.sim.autopilot = not self.sim.autopilot
        self.say_toast("Advisors build walls and farms for you" if self.sim.autopilot
                       else "Advisors dismissed - you build everything")

    def play_key(self, ch):
        if ch in ("1", "2", "3", "4"):
            self.build_sel = int(ch) - 1
            self.change_build(0)
            return True
        # none of these use w/a/s/d, which always move the cursor
        acts = {" ": self.play_place, "t": lambda: self.change_build(1), "x": self.play_demolish,
                "e": self.play_found_city, "b": self.play_wall, "r": self.play_fortify,
                "f": self.play_farm, "h": self.play_hire, "v": lambda: self.change_focus(1),
                "k": lambda: self.play_decree("crusade"), "g": lambda: self.play_decree("bulwark"),
                "l": self.toggle_autopilot}
        if ch in acts:
            acts[ch]()
            return True
        return False

    def check_outcome(self):
        sim, t = self.sim, self.sim.player
        if t < 0 or self.outcome:
            return
        total = sum(sim.pop)
        if sim.pop[t] == 0 and sim.year > 2:
            self.outcome = "lost"
            self.reason = f"The {sim.civilisations[t].name} are no more (year {sim.year})."
        elif all(done for _, done, _ in sim.objectives(t)):
            self.outcome = "won"
            self.reason = f"Every goal achieved by year {sim.year}. Score {sim.score(t)}."
        elif sim.year >= 300 and sim.pop[t] >= 400 and sim.pop[t] >= 0.6 * total:
            self.outcome = "won"
            self.reason = f"Your people dominate the world. Score {sim.score(t)}."
        if self.outcome:
            self.outcome_open = True
            self.paused = True

    def restart(self):
        old = self.sim
        self.sim = Sim(old.nt, self.rng)
        self.sim.mode = old.mode
        self._menu_base = self.build_menu()
        self._menu_play = self.build_play_menu()
        self.cx = self.cy = 0
        self.seed_world()
        self.paused = False
        self.outcome, self.outcome_open = None, False
        self.set_player(self.last_player, fresh=True)

    def choose_civ(self):
        scr, sim = self.scr, self.sim
        opts = list(range(sim.nt)) + [-1]
        sel = 0
        scr.timeout(-1)
        while True:
            scr.erase()
            rows, cols = scr.getmaxyx()
            self.put(1, 2, "LIFE OF CIVILISATIONS", curses.A_BOLD)
            self.put(2, 2, "Choose the civilisation you will rule. The others are run by fate."[:max(0, cols - 3)],
                     curses.A_DIM)
            y = 4
            for i, o in enumerate(opts):
                if o >= 0:
                    tr = sim.civilisations[o]
                    name, desc, st = tr.name, tr.desc, self.styles[o][2]
                else:
                    name, desc, st = "Sandbox", "Just watch the world unfold - every tool unlocked.", curses.A_BOLD
                self.put(y, 2, f"{'>' if i == sel else ' '} {i + 1}. {name}",
                         st | (curses.A_REVERSE if i == sel else 0))
                self.put(y + 1, 7, desc[:max(0, cols - 9)], curses.A_DIM)
                y += 2
            self.put(min(y + 1, rows - 1), 2, "Up/Down choose | Enter play | q quit", curses.A_DIM)
            scr.refresh()
            k = scr.getch()
            if k == curses.KEY_UP:
                sel = (sel - 1) % len(opts)
            elif k == curses.KEY_DOWN:
                sel = (sel + 1) % len(opts)
            elif 48 < k < 49 + len(opts):
                sel = k - 49
            elif k in (10, 13, curses.KEY_ENTER):
                return opts[sel]
            elif k in (ord("q"), ord("Q")):
                self.running = False
                return -1
            elif k == curses.KEY_RESIZE:
                scr.clear()

    # -- input -------------------------------------------------------------- #
    def handle_mouse(self):
        try:
            _, mx, my, _, b = curses.getmouse()
        except curses.error:
            return
        now = time.monotonic()
        if self.menu_open or now - self.last_mouse < 0.12:
            return
        if my < 1 or my > self.rows - 2 or mx >= self.vw * 2:
            return
        x, y = self.camx + mx // 2, self.camy + my - 1
        if self.sim.player >= 0:                     # while ruling: click = build the selected structure
            if b & (curses.BUTTON1_PRESSED | curses.BUTTON1_CLICKED):
                self.cx, self.cy = x, y
                self.last_mouse = now
                self.play_place()
            return
        if b & (curses.BUTTON1_PRESSED | curses.BUTTON1_CLICKED):
            self.cx, self.cy = x, y
            self.toggle_cell()
            self.last_mouse = now
        elif b & (curses.BUTTON3_PRESSED | curses.BUTTON3_CLICKED):
            self.cx, self.cy = x, y
            self.stamp()
            self.last_mouse = now

    def handle_key(self, k):
        if k == curses.KEY_RESIZE:
            self.scr.clear()
            return
        if k == curses.KEY_MOUSE:
            self.handle_mouse()
            return
        if self.outcome and self.outcome_open:
            if k in (10, 13, curses.KEY_ENTER):
                self.outcome_open = False
                self.paused = False
                if self.outcome == "lost":
                    self.set_player(-1)
            elif k in (ord("r"), ord("R")):
                self.restart()
            elif k in (ord("q"), ord("Q")):
                self.running = False
            return
        if k in (ord("q"), ord("Q")):
            self.running = False
            return
        if k == 9:                                       # Tab: take / leave control
            self.cycle_player(1)
            return
        if self.menu_open:
            n = len(self.menu)
            if k in (27, ord("m")):
                self.menu_open = False
                return
            if k == curses.KEY_UP:
                self.menu_sel = (self.menu_sel - 1) % n
                return
            if k == curses.KEY_DOWN:
                self.menu_sel = (self.menu_sel + 1) % n
                return
            if k in (curses.KEY_LEFT, curses.KEY_RIGHT):
                fn = self.menu[self.menu_sel][1]
                if fn:
                    fn(-1 if k == curses.KEY_LEFT else 1)
                return
            if k in (10, 13, curses.KEY_ENTER):
                fn = self.menu[self.menu_sel][2]
                if fn:
                    fn()
                return
            # anything else falls through to the normal hotkeys (the world is live!)
        ch = chr(k) if 32 <= k < 127 else ""
        if self.sim.player >= 0 and self.play_key(ch):
            return
        moves = {curses.KEY_UP: (0, -1), curses.KEY_DOWN: (0, 1),
                 curses.KEY_LEFT: (-1, 0), curses.KEY_RIGHT: (1, 0)}
        if k in moves:
            self.move(*moves[k])
        elif ch in ("w", "a", "s", "d"):
            dx, dy = {"w": (0, -8), "s": (0, 8), "a": (-8, 0), "d": (8, 0)}[ch]
            self.move(dx, dy)
        elif ch == " ":
            self.toggle_cell()
        elif ch == "x" or k in (curses.KEY_DC, curses.KEY_BACKSPACE, 127, 8):
            self.erase_cell()
        elif ch == "e":
            self.stamp()
        elif ch == "B":
            self.build_wall()
        elif ch == "y":
            self.toggle_walls()
        elif ch == "u":
            self.toggle_nature()
        elif ch == "z":
            self.change_nat_kind(1)
        elif ch == "N":
            self.place_nature()
        elif ch == "h":
            self.release_herd()
        elif ch == "f":
            self.change_pattern(1)
        elif ch.isdigit() and 1 <= int(ch) <= self.sim.nt:
            self.brush = int(ch) - 1
            self.say_toast(f"Brush: {self.sim.civilisations[self.brush].name}")
        elif ch == "t":
            self.change_brush(1)
        elif ch == "r":
            self.settle_here()
        elif ch == "R":
            self.burst()
        elif ch == "g":
            self.change_auto(1)
        elif ch == "v":
            self.toggle_events()
        elif ch == "j":
            self.change_event(1)
        elif ch == "k":
            self.trigger_event()
        elif ch == "p":
            self.toggle_pause()
        elif ch == "n":
            self.step_once()
        elif ch == "b":
            self.rewind()
        elif ch in ("+", "="):
            self.change_speed(1)
        elif ch in ("-", "_"):
            self.change_speed(-1)
        elif ch == "l":
            self.toggle_rules()
        elif ch == "c":
            self.find_life()
        elif ch == "o":
            self.go_origin()
        elif ch == "C":
            self.clear_world()
        elif ch == "P":
            self.prune_far()
        elif ch == "i":
            showing = self.panel_w > 0
            self.panel_pref = not showing
        elif ch == "m":
            self.menu_open = True

    # -- drawing ------------------------------------------------------------ #
    def put(self, y, x, text, attr=0):
        try:
            self.scr.addstr(y, x, text, attr)
        except curses.error:
            pass

    def draw(self):
        s, sim = self.scr, self.sim
        s.erase()
        rows, cols = self.rows, self.cols
        if rows < 12 or cols < 40:
            self.put(0, 0, "Terminal too small - please enlarge (min 40x12)"[:max(0, cols - 1)])
            s.refresh()
            return
        civ = sim.mode == "civ"
        label = "Year" if civ else "Gen"
        era = f" - {sim.era}" if civ else ""
        state = "PAUSED" if self.paused else f"{SPEEDS[self.speed_idx]} t/s"
        if sim.player >= 0:
            t = sim.player
            title = (f" YOU RULE THE {sim.civilisations[t].name.upper()} | {label} {sim.year}{era} | "
                     f"score {sim.score(t)} | pop {sim.pop[t]} | {state} ")
        else:
            title = (f" LIFE OF CIVILISATIONS | {label} {sim.year}{era} | pop {sum(sim.pop)} | "
                     f"{'Civilisation' if civ else 'Classic'} | {state} | auto {AUTOSPAWN[self.auto][0]} ")
        self.put(0, 0, title.ljust(cols - 1)[:cols - 1], curses.A_REVERSE)

        camx, camy, vw, vh = self.camx, self.camy, self.vw, self.vh
        if civ and sim.nature_on:
            sim.ensure_area(camx, camy, camx + vw, camy + vh)
        # orientation dots every 10 cells (makes the endless grid feel endless)
        for gy in range(camy + (-camy) % 10, camy + vh, 10):
            for gx in range(camx + (-camx) % 10, camx + vw, 10):
                self.put(gy - camy + 1, (gx - camx) * 2, self.dot, curses.A_DIM)

        w, gl, styles = sim.world, self.glyphs, self.styles
        ages = [tr.city_age for tr in sim.civilisations]
        walls = sim.walls if civ else {}
        fences = sim.fences if civ else {}
        nat = sim.nature if (civ and sim.nature_on) else {}
        wg = ("%%", "--") if self.ascii else ("╬╬", "┼┼")
        ng, nst = self.ng, self.nat_attr
        tglyph = (ng["tree"], ng["rock"], ng["pond"], ng["berry"])
        for y in range(camy, camy + vh):
            sy = y - camy + 1
            for x in range(camx, camx + vw):
                p = (x, y)
                sx = (x - camx) * 2
                c = w.get(p)
                if c is not None:
                    t, a = c
                    lv = 2 if (civ and a >= ages[t]) else (0 if a < 4 else 1)
                    self.put(sy, sx, gl[lv], styles[t][lv])
                    continue
                if not civ:
                    continue
                wv = walls.get(p)
                if wv is not None:
                    t, hp = wv
                    st = styles[t]
                    self.put(sy, sx, wg[1] if hp <= 1 else wg[0],
                             st[2] if hp >= 4 else (st[1] if hp > 1 else st[0]))
                    continue
                fv = fences.get(p)
                if fv is not None:
                    self.put(sy, sx, ng["fence"], styles[fv][1])
                    continue
                nv = nat.get(p)
                if nv is not None:
                    k, amt = nv
                    if amt <= 0:
                        self.put(sy, sx, ng["sprout"], nst[k] | curses.A_DIM)
                    else:
                        self.put(sy, sx, tglyph[k],
                                 nst[k] | (curses.A_BOLD if (k == TREE and amt >= 3) else 0))
        if civ and sim.nature_on:
            for an in sim.animals:
                if camx <= an.x < camx + vw and camy <= an.y < camy + vh:
                    tame = an.pen is not None or an.follow is not None
                    self.put(an.y - camy + 1, (an.x - camx) * 2, ng["tame"] if tame else ng["wild"],
                             self.animal_attr | (curses.A_BOLD if tame else 0))
            for wk in sim.workers:
                if camx <= wk.x < camx + vw and camy <= wk.y < camy + vh:
                    self.put(wk.y - camy + 1, (wk.x - camx) * 2,
                             ng["loaded"] if wk.carry else ng["worker"], styles[wk.t][2])

        # cursor
        if 0 <= self.cx - camx < vw and 0 <= self.cy - camy < vh:
            sx, sy = (self.cx - camx) * 2, self.cy - camy + 1
            c = w.get((self.cx, self.cy))
            if c is not None:
                t, a = c
                lv = 2 if (civ and a >= ages[t]) else (0 if a < 4 else 1)
                self.put(sy, sx, gl[lv], styles[t][lv] | curses.A_REVERSE)
            else:
                self.put(sy, sx, "[]", styles[self.brush][2])

        if self.panel_w:
            self.draw_panel()

        text, attr = ((self.toast, curses.A_BOLD) if self.toast
                      else ((self.play_help() if sim.player >= 0 else HELP), curses.A_DIM))
        self.put(rows - 1, 0, text[:cols - 1], attr)

        if self.menu_open:
            self.draw_menu()
        if self.outcome and self.outcome_open:
            self.draw_outcome()
        s.refresh()

    def draw_panel(self):
        sim = self.sim
        civ = sim.mode == "civ"
        x0 = self.cols - self.panel_w
        for y in range(1, self.rows - 1):
            self.put(y, x0, "|", curses.A_DIM)
        cw = self.panel_w - 3
        y = 1
        if sim.player >= 0:
            t = sim.player
            self.put(y, x0 + 1, f"YOUR REALM: {sim.civilisations[t].name}"[:cw], self.styles[t][2])
            y += 1
            buf = [f"{k.title()} {v - sim.year}y" for k, v in sim.buffs.items() if v > sim.year]
            if sim.autopilot:
                buf.append("Advisors")
            self.put(y, x0 + 1, f"Build: {BUILD_NAMES[self.build_sel]} ({sim.build_cost(self.build_sel)})"[:cw],
                     curses.A_BOLD)
            y += 1
            self.put(y, x0 + 1, f"Workers focus: {FOCUS_NAMES[sim.focus]}"[:cw], 0)
            y += 1
            self.put(y, x0 + 1, ("Decrees: " + (", ".join(buf) if buf else "none"))[:cw], curses.A_DIM)
            y += 1
            for label, done, prog in sim.objectives(t):
                self.put(y, x0 + 1, f"[{'x' if done else ' '}] {label} {prog}"[:cw],
                         curses.A_BOLD if done else 0)
                y += 1
            y += 1
        self.put(y, x0 + 5, f"{'Civ':<11}{'pop':>5}{'city':>5}{'wall':>5}{'war':>5}", curses.A_BOLD)
        y += 1
        for i, tr in enumerate(sim.civilisations):
            dead = sim.pop[i] == 0
            self.put(y, x0 + 1, ">" if i == self.brush else " ", curses.A_BOLD)
            self.put(y, x0 + 2, self.glyphs[1], self.styles[i][0 if dead else 1])
            self.put(y, x0 + 5,
                     f"{tr.name:<11}{sim.pop[i]:>5}{sim.cities[i]:>5}{sim.wallpop[i]:>5}{sim.conquests[i]:>5}",
                     curses.A_DIM if dead else 0)
            y += 1
        y += 1
        if civ and sim.nature_on:
            self.put(y, x0 + 5, f"{'Stock':<5}{'wood':>5}{'stn':>4}{'food':>5}{'h2o':>5}{'wk':>4}{'fm':>3}",
                     curses.A_BOLD)
            y += 1
            wcount = Counter(wk.t for wk in sim.workers)
            fcount = Counter(f.t for f in sim.farms)
            for i, tr in enumerate(sim.civilisations):
                s = sim.stock[i]
                nm = tr.name[:4] + ("!" if sim.starving[i] else " ")
                self.put(y, x0 + 2, self.glyphs[1], self.styles[i][1])
                self.put(y, x0 + 5, f"{nm:<5}{int(s[0]):>5}{int(s[1]):>4}{int(s[2]):>5}{int(s[3]):>5}"
                                    f"{wcount[i]:>4}{fcount[i]:>3}",
                         curses.A_BOLD if sim.starving[i] else 0)
                y += 1
            ng, lx = self.ng, x0 + 1
            for g, at, lab in (() if self.rows < 34 else ((ng["tree"], self.nat_attr[TREE], "wood"),
                               (ng["rock"], self.nat_attr[ROCK], "stone"),
                               (ng["pond"], self.nat_attr[POND], "water"),
                               (ng["berry"], self.nat_attr[BERRY], "berry"),
                               (ng["wild"], self.animal_attr, "game"),
                               (ng["tame"], self.animal_attr | curses.A_BOLD, "herd"),
                               (ng["worker"], curses.A_BOLD, "worker"))):
                if lx + len(lab) + 4 > self.cols - 1:
                    y += 1
                    lx = x0 + 1
                self.put(y, lx, g, at)
                self.put(y, lx + 3, lab, curses.A_DIM)
                lx += len(lab) + 4
            y += 2
        c = sim.world.get((self.cx, self.cy))
        wv = sim.walls.get((self.cx, self.cy))
        if c is None and wv is not None:
            info = f"{sim.civilisations[wv[0]].name} wall (hp {wv[1]})"
        elif c is None and civ and sim.nature_on and (self.cx, self.cy) in sim.nature:
            k, amt = sim.nature[(self.cx, self.cy)]
            info = f"{NAT_NAMES[k]} {amt}/{NAT_MAX[k]}"
        elif c is None:
            info = "empty land"
        else:
            t, a = c
            info = f"{sim.civilisations[t].name} age {a}"
            if civ and a >= sim.civilisations[t].city_age:
                info += " CITY"
        self.put(y, x0 + 1, f"({self.cx},{self.cy}) {info}"[:cw], curses.A_BOLD)
        y += 1
        if civ:
            desc = sim.civilisations[self.brush].desc
        else:
            desc = "Classic rules: civilisations are only colours (majority colour wins births)."
        for line in __import__("textwrap").wrap(desc, cw)[:3]:
            self.put(y, x0 + 1, line, curses.A_DIM)
            y += 1
        y += 1
        self.put(y, x0 + 1, "CHRONICLE", curses.A_BOLD)
        y += 1
        wrap = __import__("textwrap").wrap
        for yr, msg in reversed(sim.log):
            for j, line in enumerate(wrap(f"Y{yr}: {msg}", cw, subsequent_indent="  ")):
                if y >= self.rows - 1:
                    return
                self.put(y, x0 + 1, line, curses.A_BOLD if j == 0 and yr == sim.year else 0)
                y += 1

    def draw_outcome(self):
        won = self.outcome == "won"
        lines = ["VICTORY!" if won else "YOUR CIVILISATION HAS FALLEN", self.reason, "",
                 "Enter: " + ("keep playing" if won else "watch on") + "   R: new world   Q: quit"]
        w = min(self.cols - 2, max(len(l) for l in lines) + 6)
        h = len(lines) + 2
        x0, y0 = max(0, (self.cols - w) // 2), max(1, (self.rows - h) // 2)
        self.put(y0, x0, "+" + "-" * (w - 2) + "+", curses.A_BOLD)
        for i, l in enumerate(lines):
            self.put(y0 + 1 + i, x0, "|" + l.center(w - 2)[:w - 2] + "|", curses.A_BOLD if i == 0 else 0)
        self.put(y0 + h - 1, x0, "+" + "-" * (w - 2) + "+", curses.A_BOLD)

    def draw_menu(self):
        items = self.menu
        self.menu_sel = min(self.menu_sel, len(items) - 1)
        w = min(50, self.vw * 2)
        h = min(len(items) + 3, self.rows - 2)
        vis = h - 3
        if self.menu_sel < self.menu_top:
            self.menu_top = self.menu_sel
        if self.menu_sel >= self.menu_top + vis:
            self.menu_top = self.menu_sel - vis + 1
        x0, y0 = 1, 1
        self.put(y0, x0, "+" + " MENU - the world keeps running ".center(w - 2, "-")[:w - 2] + "+",
                 curses.A_BOLD)
        for i in range(vis):
            idx = self.menu_top + i
            lab = items[idx][0]
            lab = lab() if callable(lab) else lab
            y = y0 + 1 + i
            attr = curses.A_REVERSE if idx == self.menu_sel else 0
            self.put(y, x0, "|", curses.A_BOLD)
            self.put(y, x0 + 1, (" " + lab).ljust(w - 2)[:w - 2], attr)
            self.put(y, x0 + w - 1, "|", curses.A_BOLD)
        y = y0 + 1 + vis
        self.put(y, x0, "|" + " Up/Dn pick  L/R change  Enter do  m close".ljust(w - 2)[:w - 2] + "|",
                 curses.A_DIM)
        self.put(y + 1, x0, "+" + "-" * (w - 2) + "+", curses.A_BOLD)


# --------------------------------------------------------------------------- #

def main():
    ap = argparse.ArgumentParser(description="Game of Life that grows into a civilisation game.")
    ap.add_argument("--civilisations", type=int, default=6, choices=range(2, 7), metavar="2-6",
                    help="number of civilisations (default 6)")
    ap.add_argument("--rules", choices=["civ", "life"], default="civ",
                    help="start with civilisation rules or classic Conway")
    ap.add_argument("--speed", type=int, default=8, choices=SPEEDS, metavar="TPS",
                    help="starting ticks per second (default 8)")
    ap.add_argument("--seed", type=int, help="random seed for repeatable worlds")
    ap.add_argument("--ascii", action="store_true", help="use plain ASCII glyphs")
    ap.add_argument("--no-mouse", action="store_true", help="disable mouse support")
    ap.add_argument("--emoji", action="store_true", help="emoji trees/animals (needs emoji font)")
    ap.add_argument("--play", nargs="?", const="", metavar="NAME",
                    help="rule a civilisation by name (e.g. --play stonekin); no name opens the chooser")
    ap.add_argument("--sandbox", action="store_true", help="skip the chooser: watch and tinker, no ruler")
    args = ap.parse_args()

    locale.setlocale(locale.LC_ALL, "")
    os.environ.setdefault("ESCDELAY", "25")
    args.play_idx = None
    if args.play:
        hits = [i for i, c in enumerate(CIVILISATIONS[:args.civilisations])
                if c.name.lower().startswith(args.play.lower())]
        if not hits:
            ap.error("unknown civilisation %r (choose from %s)" % (
                args.play, ", ".join(c.name for c in CIVILISATIONS[:args.civilisations])))
        args.play_idx = hits[0]
    game = Game(args, random.Random(args.seed))
    try:
        curses.wrapper(game.run)
    except KeyboardInterrupt:
        pass
    sim = game.sim
    print(f"History ended in year {sim.year} ({sim.era}). Population {sum(sim.pop)}.")
    for i, tr in enumerate(sim.civilisations):
        print(f"  {tr.name:<12} pop {sim.pop[i]:>5}  cities {sim.cities[i]:>4}  conquests {sim.conquests[i]:>5}")


if __name__ == "__main__":
    main()