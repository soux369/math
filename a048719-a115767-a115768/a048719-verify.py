#!/usr/bin/env python3
"""Yue's independent verification of Job E:
A048719 subset A115767 (strict) and A115768 = A115767 \\ A048719.

A048719 = {k: 3k = C(7,k) and 5k = C(5,k)}; A115767 = {k: (2k) XOR (5k)
= 3k}; A115768 = {k in A115767: (4k) XOR k != 5k}; C = carryless mult.

WARNING: Neon's prose proof is BROKEN (its Step 2/3/4 equivalences are
false; see checks (2)). The theorem statements are true. This script
verifies them independently: brute force + product-automaton checks of
the two real implications:
  P1:  H7 and H5  ==>  (2k) AND (3k) = 0   [the inclusion]
  CRUX: A115767 and H5  ==>  H7            [gives the (?) resolution
       with Step 5: (4k) XOR k = 5k iff no distance-2 pair, and
       H5 iff no distance-2 pair]
Automaton state (c, d, a, b): c = carry into j of k+2k, d = carry into
j of k+4k, a = k_{j-1}, b = k_{j-2}; input x = k_j.
  bit3 = (x+a+c)%2, c' = (x+a+c)//2;  bit5 = (x+b+d)%2, d' = (x+b+d)//2
  H7_j: bit3 == x^a^b ;  H5_j: bit5 == x^b ;  NC_j: not (a==1 and bit3==1)
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

def H7(k): return 3 * k == clmul(7, k)
def H5(k): return 5 * k == clmul(5, k)
def inA048719(k): return H7(k) and H5(k)
def inA115767(k): return (2 * k) ^ (5 * k) == 3 * k
def inA115768(k): return inA115767(k) and (4 * k) ^ k != 5 * k
def dist_pair(k, dist):
    n = k.bit_length() + 3
    return any(((k >> i) & 1) and ((k >> (i + dist)) & 1) for i in range(n))

# ---------- (1) brute force both parts ----------
LIM = 1 << 20
A = {k for k in range(LIM) if inA048719(k)}
B = {k for k in range(LIM) if inA115767(k)}
D = {k for k in range(LIM) if inA115768(k)}
print(f"(1) |A048719| = {len(A)}, |A115767| = {len(B)}, |A115768| = {len(D)} (< 2^20)")
print(f"    inclusion violations: {len(A - B)}; difference B\\A size {len(B - A)}, "
      f"smallest {min(B - A)}; A115768 == B\\A: {D == B - A}")
assert not (A - B) and D == B - A and min(B - A) == 11

# ---------- (2) Neon's intermediate claims are FALSE ----------
print(f"(2) k=3 in A048719: {inA048719(3)} but has adjacent pair: {dist_pair(3,1)}"
      f"  -> Step 2 'H7 iff no adjacent' is FALSE")
print(f"    k=3: (2k)^(5k) = {(2*3)^(5*3)} = 3k, but (2k)&(5k) = {(2*3)&(5*3)} != 0"
      f"  -> Step 3 equivalence is FALSE")
assert inA048719(3) and dist_pair(3, 1) and ((2 * 3) & (5 * 3)) != 0
# correct reformulation of A115767: (2k) XOR (5k) = 3k iff (2k) AND (3k) = 0
bad = [k for k in range(1 << 16) if inA115767(k) != ((2 * k) & (3 * k) == 0)]
print(f"    correct reformulation (2k)&(3k)=0 mismatches < 2^16: {len(bad)}")
assert not bad
# H5 iff no distance-2 pair (this part of Neon's Step 2 is right)
bad = [k for k in range(LIM) if H5(k) != (not dist_pair(k, 2))]
print(f"    H5 iff no distance-2 pair, mismatches < 2^20: {len(bad)}")
assert not bad
# Step 5: (4k) XOR k = 5k iff no distance-2 pair
bad = [k for k in range(1 << 16) if ((4 * k) ^ k == 5 * k) != (not dist_pair(k, 2))]
assert not bad
print("    Step 5 ((4k)^k = 5k iff no distance-2 pair)  OK")

# ---------- (3) product automaton: P1 and CRUX ----------
def trans(state, x):
    c, d, a, b = state
    bit3 = (x + a + c) % 2
    bit5 = (x + b + d) % 2
    h7 = (bit3 == (x ^ a ^ b))
    h5 = (bit5 == (x ^ b))
    nc = not (a == 1 and bit3 == 1)
    return h7, h5, nc, ((x + a + c) // 2, (x + b + d) // 2, x, a)

S0 = (0, 0, 0, 0)

def analyze(name, hyp, target):
    # hyp, target: functions (h7, h5, nc) -> bool
    reach = {S0}
    q = deque([S0])
    edges = {}
    while q:
        s = q.popleft()
        for x in (0, 1):
            h7, h5, nc, t = trans(s, x)
            if hyp(h7, h5, nc):
                edges[(s, x)] = (h7, h5, nc, t)
                if t not in reach:
                    reach.add(t)
                    q.append(t)
    rev = {}
    for (s, x), (_, _, _, t) in edges.items():
        rev.setdefault(t, []).append(s)
    viable = {S0}
    q = deque([S0])
    while q:
        t = q.popleft()
        for s in rev.get(t, []):
            if s not in viable:
                viable.add(s)
                q.append(s)
    bad = [(s, x) for (s, x), (h7, h5, nc, t) in edges.items()
           if s in viable and t in viable and not target(h7, h5, nc)]
    print(f"(3) {name}: reachable {len(reach)}, viable {len(viable)}, "
          f"violating viable transitions: {len(bad)}")
    assert not bad

analyze("P1: H7&H5 ==> NC (inclusion)", lambda h7, h5, nc: h7 and h5,
        lambda h7, h5, nc: nc)
analyze("CRUX: H5&NC ==> H7", lambda h7, h5, nc: h5 and nc,
        lambda h7, h5, nc: h7)
print("ALL CHECKS PASSED (theorem true; Neon's prose proof is not)")
