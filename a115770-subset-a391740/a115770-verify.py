#!/usr/bin/env python3
"""Independent verification: A115770 subset A391740 via 7k=C(11,k) => 5k=C(13,k).
Neon claim: 10 reachable state pairs, terminal implication holds, 0 violations k<200000.
Yue's own BFS + brute force to 2^20."""

def C(a, b):
    """Carryless multiplication A048720."""
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r

def succ(a_ord, a_car, c, x, b):
    """One bit step for a_ord*k + c = C(a_car,k) ^ x: returns (p_lhs, p_rhs, c', x')."""
    ab_o = a_ord * b
    p1 = (ab_o + c) & 1
    c2 = (ab_o + c) >> 1
    t = (a_car * b) ^ x
    p2 = t & 1
    x2 = t >> 1
    return p1, p2, c2, x2

# BFS over state pairs (c7, x11, c5, x13); transition on bit b allowed iff
# hypothesis parity matches (p1 == p1'); then require conclusion parity matches too.
from collections import deque
start = (0, 0, 0, 0)
seen = {start}
dq = deque([start])
parity_fail_states = []
while dq:
    c1, x1, c2, x2 = dq.popleft()
    for b in (0, 1):
        p1, p1r, c1n, x1n = succ(7, 11, c1, x1, b)
        if p1 != p1r:
            continue  # hypothesis impossible on this bit
        p2, p2r, c2n, x2n = succ(5, 13, c2, x2, b)
        if p2 != p2r:
            parity_fail_states.append(((c1, x1, c2, x2), b))
            continue
        ns = (c1n, x1n, c2n, x2n)
        if ns not in seen:
            seen.add(ns)
            dq.append(ns)

print(f"reachable states: {len(seen)}")
for s in sorted(seen):
    print("  ", s)
print(f"conclusion-parity failures on reachable transitions: {len(parity_fail_states)}")

# Terminal implication: c1 == x1  =>  c2 == x2 for all reachable states
bad = [s for s in seen if s[0] == s[1] and s[2] != s[3]]
print(f"terminal implication violations: {len(bad)}", bad if bad else "")

claimed = {(0,0,0,0),(3,5,2,6),(1,2,1,3),(5,7,3,5),(2,3,1,2),(6,6,4,4),
           (3,3,2,2),(1,1,1,1),(5,4,3,7),(4,5,3,6)}
print("reachable set == Neon claimed 10 states:", seen == claimed)

# Brute force to 2^20
terms = []
viol = []
for k in range(1 << 20):
    if 7 * k == C(11, k):
        terms.append(k)
        if 5 * k != C(13, k):
            viol.append(k)
print(f"A115770 terms below 2^20: {len(terms)}; first 11: {terms[:11]}")
print(f"brute-force violations of the implication: {len(viol)}")
print("prefix matches OEIS (0,7,14,15,28,30,31,56,60,62,63):",
      terms[:11] == [0, 7, 14, 15, 28, 30, 31, 56, 60, 62, 63])
# sample values from the claim
for k in (7, 15, 455):
    print(f"k={k}: 7k={7*k} C(11,k)={C(11,k)} | 5k={5*k} C(13,k)={C(13,k)}")
