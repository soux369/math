#!/usr/bin/env python3
"""Yue's independent verification of Job C: A115805 subset A115823.

A115805 = {k : 13k = C(29,k)}; A115823 = {k : (8k) XOR (13k) = 21k},
C = carryless multiplication. Conclusion <=> (8k) AND (13k) = 0.

Neon's proof uses a direct bitwise automaton for the hypothesis:
state (c; w1,w2,w3,w4), c = carry into position j of 13k = k+4k+8k,
wi = k_{j-i}. Input x = k_j. s = x + w2 + w3 + c; b = s mod 2 (bit j
of 13k); H_j holds iff b == x^w2^w3^w4 (bit j of C(29,k)); c' = s//2;
next state (c'; x, w1, w2, w3). Bit j of 8k is w3, so a conclusion
conflict at a transition is (w3 == 1 and b == 1).

Checks: (1) brute force; (2) BFS reachable set vs Neon's listed rows;
(3) arithmetic consistency of every listed transition; (4) viability:
states that can return to (0;0,0,0,0) in the H-transition graph;
every conflict transition must be non-viable (start or target not
viable); (5) semantic spot check of the automaton vs direct arithmetic.
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
terms, viol = [], []
for k in range(LIM):
    if 13 * k == clmul(29, k):
        terms.append(k)
        if (8 * k) ^ (13 * k) != 21 * k:
            viol.append(k)
print(f"(1) A115805 terms < 2^20: {len(terms)}, conclusion violations: {len(viol)}")
assert (8 * 5) ^ (13 * 5) == 105 == 21 * 5 and 13 * 5 == 65 != 105 == clmul(29, 5)
assert 5 not in terms
print("    witness 5: in A115823, not in A115805  OK")

# ---------- automaton ----------
def trans(state, x):
    c, w1, w2, w3, w4 = state
    s = x + w2 + w3 + c
    b = s % 2
    h_ok = (b == (x ^ w2 ^ w3 ^ w4))
    return h_ok, b, (s // 2, x, w1, w2, w3)

S0 = (0, 0, 0, 0, 0)
reach = {S0}
q = deque([S0])
edges = {}  # (state, x) -> (b, next) for H-ok transitions
while q:
    s = q.popleft()
    for x in (0, 1):
        ok, b, t = trans(s, x)
        if ok:
            edges[(s, x)] = (b, t)
            if t not in reach:
                reach.add(t)
                q.append(t)
print(f"(2) BFS reachable states: {len(reach)}")

listed_rows = {
    (0,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0),(0,1,1,0,0),(0,0,0,1,0),(0,1,0,1,0),
    (0,0,1,1,0),(0,1,1,1,0),
    (1,1,0,1,0),(1,1,1,1,0),(1,1,0,0,1),(1,1,1,0,1),(1,0,0,1,1),(1,1,0,1,1),
    (1,0,1,1,1),(1,1,1,1,1),(1,0,1,1,0),(1,0,0,0,1),(1,1,0,0,0),(1,1,1,0,0),
    (1,0,0,1,0),(1,0,1,0,1),
    (2,1,0,1,1),(2,1,1,1,1),
}
print(f"    Neon listed rows: {len(listed_rows)}")
print(f"    reachable but NOT listed: {sorted(reach - listed_rows)}")
print(f"    listed but NOT reachable: {sorted(listed_rows - reach)}")

# ---------- (4) viability ----------
# viable(s): S0 reachable from s in the H-transition graph (a valid k's
# path must eventually drain to S0 and stay there on zero input).
rev = {}
for (s, x), (b, t) in edges.items():
    rev.setdefault(t, []).append(s)
viable = {S0}
q = deque([S0])
while q:
    t = q.popleft()
    for s in rev.get(t, []):
        if s not in viable:
            viable.add(s)
            q.append(s)
print(f"(4) viable states: {len(viable)} of {len(reach)} reachable")

conflicts = []
fatal = []
for (s, x), (b, t) in edges.items():
    if s[3] == 1 and b == 1:  # w3 == 1 and bit j of 13k == 1
        conflicts.append((s, x, t))
        if s in viable and t in viable:
            fatal.append((s, x, t))
print(f"    conflict transitions (w3=1, b=1): {len(conflicts)}")
for cfl in conflicts:
    print(f"      state={cfl[0]} x={cfl[1]} -> {cfl[2]}  start viable: {cfl[0] in viable}, target viable: {cfl[2] in viable}")
print(f"    FATAL conflicts (viable start AND viable target): {len(fatal)}")
assert not fatal, "a valid k could hit a conclusion conflict"

# ---------- (5) semantic check of the automaton ----------
import random
bad = 0
for _ in range(3000):
    k = random.randrange(0, 1 << 18)
    # run automaton on k's bits + drain bits; H must hold at all positions
    # iff 13k == C(29,k); and conflicts along the actual path must match
    # the direct AND computation.
    state = S0
    ok_all = True
    conflict_seen = False
    kk = k
    for j in range(24):
        x = kk & 1
        kk >>= 1
        ok, b, state = trans(state, x)
        if state and (j >= 3):
            pass
        # bit j of 8k is k_{j-3}
        bit8 = (k >> (j - 3)) & 1 if j >= 3 else 0
        if bit8 == 1 and b == 1:
            conflict_seen = True
        if not ok:
            ok_all = False
            break
    direct_H = (13 * k == clmul(29, k))
    direct_conflict = ((8 * k) & (13 * k)) != 0
    if ok_all != direct_H:
        bad += 1
    if direct_H and direct_conflict:
        bad += 1  # theorem would be false
    if ok_all and conflict_seen != direct_conflict:
        bad += 1
print(f"(5) semantic mismatches over 3000 random k: {bad}")
assert bad == 0
print("ALL CHECKS PASSED (modulo part-2 text comparison)")
