#!/usr/bin/env python3
"""Yue's independent verification of Job D: A048715 = Detlefs's RHS.

A048715 = {x : 7x = C(7,x)}, C = carryless multiplication.
Detlefs (x >= 1): (x AND 5x) = x AND (x OR 3x)/x = 3 (exact division).
Bridge claim: 7x = C(7,x) iff no two 1-bits of x at distance 1 or 2.
Neon's text fully proves the bridge but SKETCHES conditions (i)/(ii);
checks (4)/(5) below close those steps with product automata.

(1) brute force x < 2^20; (2) bridge lemma semantically; (3) bridge
automaton table claims; (4) condition (i) product automaton:
(x AND 5x) = x  iff  no distance-2 pair; (5) condition (ii):
(x OR 3x) = 3x  iff  no distance-1 pair.
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

def bits(x):
    return [(x >> i) & 1 for i in range(x.bit_length() + 3)]

def has_pair(x, dist):
    bs = bits(x)
    return any(bs[i] and bs[i + dist] for i in range(len(bs) - dist))

def triple_ok(x):
    return not has_pair(x, 1) and not has_pair(x, 2)

def detlefs_rhs(x):
    if x == 0:
        return False
    return (x & (5 * x)) == x and (x | (3 * x)) % x == 0 and (x | (3 * x)) // x == 3

# ---------- (1) brute force ----------
LIM = 1 << 20
lhs = {x for x in range(LIM) if 7 * x == clmul(7, x)}
rhs = {x for x in range(1, LIM) if detlefs_rhs(x)}
print(f"(1) A048715 terms < 2^20: {len(lhs)}; Detlefs RHS (x>=1): {len(rhs)}; "
      f"symmetric difference: {len(lhs ^ rhs)} (0 in LHS only expected: {lhs - rhs})")
assert lhs - rhs == {0} and not (rhs - lhs)
# the two readings of the division condition agree
alt = {x for x in range(1, 1 << 16) if (x & (5 * x)) == x and (x | (3 * x)) == 3 * x}
assert alt == {x for x in rhs if x < (1 << 16)}
print("    division reading (x|3x)/x = 3  ==  (x|3x) = 3x on x < 2^16  OK")

# ---------- (2) bridge lemma, semantic ----------
bad = [x for x in range(LIM) if (7 * x == clmul(7, x)) != triple_ok(x)]
print(f"(2) bridge lemma mismatches < 2^20: {len(bad)}")
assert not bad

# ---------- (3) bridge automaton claims ----------
# state (c, a, b) = (carry into j, x_{j-1}, x_{j-2}); input x_j.
def btrans(state, xj):
    c, a, b = state
    s = xj + a + b + c
    bit = s % 2
    h_ok = (bit == (xj ^ a ^ b))
    return h_ok, bit, (s // 2, xj, a)

c1_fail = all(not btrans((1, a, b), xj)[0] for a in (0, 1) for b in (0, 1) for xj in (0, 1))
print(f"(3) every c=1 state fails H on both inputs: {c1_fail}")
assert c1_fail
reach = {(0, 0, 0)}
q = deque([(0, 0, 0)])
while q:
    s = q.popleft()
    for xj in (0, 1):
        ok, _, t = btrans(s, xj)
        if ok and t not in reach:
            reach.add(t)
            q.append(t)
print(f"    reachable under H: {sorted(reach)}")
assert all(s[0] <= 1 for s in reach), "c=2 reached under H"
into_c1 = [(s, xj) for s in reach if s[0] == 0
           for xj in (0, 1) if btrans(s, xj)[0] and btrans(s, xj)[2][0] == 1]
print(f"    H-ok transitions from c=0 into c=1 (die next step): {len(into_c1)}")

# ---------- (4) condition (i): (x AND 5x) = x  iff  no distance-2 pair ----------
# bit j of 5x = (x_j + x_{j-2} + d_j) mod 2, d = carry of x + 4x.
# state (d, p1, p2, violP, violD): p1 = x_{j-1}, p2 = x_{j-2}.
def step_i(state, xj):
    d, p1, p2, violP, violD = state
    bit5 = (xj + p2 + d) % 2
    if xj == 1 and bit5 == 0:
        violP = True
    if xj == 1 and p2 == 1:
        violD = True
    return ((xj + p2 + d) // 2, xj, p1, violP, violD)

start = (0, 0, 0, False, False)
seen = {start}
q = deque([start])
while q:
    s = q.popleft()
    for xj in (0, 1):
        t = step_i(s, xj)
        if t not in seen:
            seen.add(t)
            q.append(t)
disagree = [s for s in seen if s[3] != s[4]]
print(f"(4) condition (i) automaton: {len(seen)} reachable states, "
      f"violP != violD states: {len(disagree)}")
assert not disagree

# ---------- (5) condition (ii): (x OR 3x) = 3x  iff  no distance-1 pair ----------
# bit j of 3x = (x_j + x_{j-1} + e_j) mod 2, e = carry of x + 2x.
# state (e, p1, violP, violD).
def step_ii(state, xj):
    e, p1, violP, violD = state
    bit3 = (xj + p1 + e) % 2
    if xj == 1 and bit3 == 0:
        violP = True
    if xj == 1 and p1 == 1:
        violD = True
    return ((xj + p1 + e) // 2, xj, violP, violD)

start = (0, 0, False, False)
seen2 = {start}
q = deque([start])
while q:
    s = q.popleft()
    for xj in (0, 1):
        t = step_ii(s, xj)
        if t not in seen2:
            seen2.add(t)
            q.append(t)
disagree2 = [s for s in seen2 if s[2] != s[3]]
print(f"(5) condition (ii) automaton: {len(seen2)} reachable states, "
      f"violP != violD states: {len(disagree2)}")
assert not disagree2
print("ALL CHECKS PASSED")
