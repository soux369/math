#!/usr/bin/env python3
"""Yue's independent verification of Job A: A115807 subset A048719 (strict).

A115807 = {k : 15k = C(27,k)};  A048719 = {k : 3k = C(7,k) and 5k = C(5,k)},
C = carryless multiplication (A048720).
Checks: (1) brute-force inclusion + counts + witness 99 for k < 2^20;
(2) product state-pair BFS reachable set vs the claimed 14 states;
(3) semantic implication H15(s,k) => H3(s,k) and H5(s,k) on every
reachable state for k < 2^16; (4) dead-state justification (parity, or
k=0 failure with both successors parity-dead).
"""
from collections import deque

def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r

# ---------- (1) brute force ----------
LIM = 1 << 20
terms807 = []
viol = []
for k in range(LIM):
    if 15 * k == clmul(27, k):
        terms807.append(k)
        if not (3 * k == clmul(7, k) and 5 * k == clmul(5, k)):
            viol.append(k)
print(f"(1) A115807 terms < 2^20: {len(terms807)}, inclusion violations: {len(viol)}")
assert 3 * 99 == clmul(7, 99) == 297 and 5 * 99 == clmul(5, 99) == 495
assert 15 * 99 == 1485 and clmul(27, 99) == 1421 and 99 not in terms807
print("    witness 99: in A048719, not in A115807  OK")

# ---------- (2) BFS over product states ----------
# component (m, p, c, d); step on bit b of k:
#   bit-match iff (c + m*b) % 2 == ((d ^ (p*b)) & 1)
#   c' = (c + m*b)//2 ; d' = (d ^ (p*b))//2
COMPS = [(15, 27), (3, 7), (5, 5)]

def succ(state, b, comp_idx=0):
    out = []
    for (m, p), (c, d) in zip(COMPS, state):
        out.append(((c + m * b) // 2, (d ^ (p * b)) // 2))
    return tuple(out)

def bitmatch(state, b, idx):
    (m, p), (c, d) = COMPS[idx], state[idx]
    return (c + m * b) % 2 == ((d ^ (p * b)) & 1)

S0 = ((0, 0), (0, 0), (0, 0))
seen = {S0}
q = deque([S0])
trans = {}
while q:
    s = q.popleft()
    for b in (0, 1):
        if bitmatch(s, b, 0):  # hypothesis (15,27) drives reachability
            t = succ(s, b)
            trans[(s, b)] = t
            if t not in seen:
                seen.add(t)
                q.append(t)

claimed = {
    ((0,0),(0,0),(0,0)), ((7,13),(1,3),(2,2)), ((3,6),(0,1),(1,1)),
    ((11,11),(2,2),(3,3)), ((5,5),(1,1),(1,1)), ((13,8),(2,2),(4,3)),
    ((2,2),(0,0),(0,0)), ((10,15),(2,3),(3,2)), ((1,1),(0,0),(0,0)),
    ((8,12),(1,3),(2,2)), ((8,13),(1,3),(2,2)), ((4,6),(0,1),(1,1)),
    ((2,3),(0,0),(0,0)), ((9,14),(1,3),(3,2)),
}
print(f"(2) BFS reachable: {len(seen)} states; matches claimed 14: {seen == claimed}")
assert seen == claimed

claimed_trans = {
    (((0,0),(0,0),(0,0)),0): ((0,0),(0,0),(0,0)),
    (((0,0),(0,0),(0,0)),1): ((7,13),(1,3),(2,2)),
    (((7,13),(1,3),(2,2)),0): ((3,6),(0,1),(1,1)),
    (((7,13),(1,3),(2,2)),1): ((11,11),(2,2),(3,3)),
    (((11,11),(2,2),(3,3)),0): ((5,5),(1,1),(1,1)),
    (((11,11),(2,2),(3,3)),1): ((13,8),(2,2),(4,3)),
    (((5,5),(1,1),(1,1)),0): ((2,2),(0,0),(0,0)),
    (((5,5),(1,1),(1,1)),1): ((10,15),(2,3),(3,2)),
    (((2,2),(0,0),(0,0)),0): ((1,1),(0,0),(0,0)),
    (((2,2),(0,0),(0,0)),1): ((8,12),(1,3),(2,2)),
    (((1,1),(0,0),(0,0)),0): ((0,0),(0,0),(0,0)),
    (((1,1),(0,0),(0,0)),1): ((8,13),(1,3),(2,2)),
    (((8,12),(1,3),(2,2)),0): ((4,6),(0,1),(1,1)),
    (((8,12),(1,3),(2,2)),1): ((11,11),(2,2),(3,3)),
    (((4,6),(0,1),(1,1)),0): ((2,3),(0,0),(0,0)),
    (((4,6),(0,1),(1,1)),1): ((9,14),(1,3),(3,2)),
}
bad = [(k, trans.get(k), v) for k, v in claimed_trans.items() if trans.get(k) != v]
print(f"    claimed transitions checked: {len(claimed_trans)}, mismatches: {len(bad)}")
assert not bad

# ---------- (3) semantic implication on states ----------
def H(m, p, c, d, k):
    return m * k + c == (clmul(p, k) ^ d)

KLIM = 1 << 16
bad_imp = 0
live = set()
for s in seen:
    (c15, d27), (c3, d7), (c5, d5) = s
    for k in range(KLIM):
        if H(15, 27, c15, d27, k):
            live.add(s)
            if not (H(3, 7, c3, d7, k) and H(5, 5, c5, d5, k)):
                bad_imp += 1
print(f"(3) state-level implication violations (k < 2^16): {bad_imp}")
print(f"    states with an H15 witness k < 2^16: {len(live)}")
assert bad_imp == 0

# ---------- (4) dead-state justification ----------
def parity_dead(s):
    c, d = s[0]
    return (c % 2) != (d % 2)

unjustified = []
for s in seen - live:
    if parity_dead(s):
        continue
    # need: k=0 fails and both (15,27)-successors parity-dead
    c, d = s[0]
    ok = (c != d) and all(parity_dead(trans[(s, b)]) for b in (0, 1) if (s, b) in trans)
    if not ok:
        unjustified.append(s)
print(f"(4) non-live states without a deadness justification: {len(unjustified)}")
assert not unjustified
print("ALL CHECKS PASSED")
