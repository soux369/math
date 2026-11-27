#!/usr/bin/env python3
"""Yue's independent verification of Job B: A115876 subset A115874 (strict).

A115876 = {k : 41k = C(105,k)};  A115874 = {k : 19k = C(55,k)},
C = carryless multiplication (A048720).
Neon's proof shape: DFA(41,105) has 40 parity-consistent reachable
states = 9 live L + 31 dead D (all c != m, closed under transitions
into D or parity-mismatch). The 9 live states couple to DFA(19,55)
states; terminal implication holds on all coupled pairs.
Checks: (1) brute force + witness 31; (2) BFS reachable set size and
split; (3) claimed dead set == computed; dead closure; (4) claimed
live coupled transitions; terminal implication; (5) semantic checks.
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

def succ(a, b, c, m, x):
    return ((c + a * x) // 2, (m ^ (b * x)) // 2)

def bitmatch(a, b, c, m, x):
    return (c + a * x) % 2 == ((m ^ (b * x)) & 1)

def parity_ok(s):
    return (s[0] % 2) == (s[1] % 2)

# ---------- (1) brute force ----------
LIM = 1 << 20
terms = []
viol = []
for k in range(LIM):
    if 41 * k == clmul(105, k):
        terms.append(k)
        if 19 * k != clmul(55, k):
            viol.append(k)
print(f"(1) A115876 terms < 2^20: {len(terms)}, inclusion violations: {len(viol)}")
assert 19 * 31 == clmul(55, 31) == 589
assert 41 * 31 == 1271 and clmul(105, 31) == 1223 and 31 not in terms
print("    witness 31: in A115874, not in A115876  OK")

# ---------- (2) BFS parity-consistent reachable states of DFA(41,105) ----------
A1, B1 = 41, 105
R = {(0, 0)}
q = deque([(0, 0)])
while q:
    s = q.popleft()
    for x in (0, 1):
        if bitmatch(A1, B1, s[0], s[1], x):
            t = succ(A1, B1, s[0], s[1], x)
            if parity_ok(t) and t not in R:
                R.add(t)
                q.append(t)
print(f"(2) parity-consistent reachable states: {len(R)} (claimed 40)")
assert len(R) == 40

L_claimed = [(0,0),(20,52),(30,46),(35,35),(17,17),(8,8),(4,4),(2,2),(1,1)]
L = set(L_claimed)
assert L <= R
D = R - L
print(f"    live L: {len(L)} (claimed 9); dead D = R - L: {len(D)} (claimed 31)")
assert len(D) == 31

# ---------- (3) claimed dead set and closure ----------
D_claimed = {
    (1,3),(2,6),(3,5),(3,7),(5,13),(6,12),(6,14),(7,11),(8,10),(10,26),(11,25),
    (11,27),(12,24),(12,28),(13,29),(15,23),(16,20),(16,22),(21,53),(21,55),
    (22,54),(23,51),
    (24,48),(25,57),(26,56),(26,58),(28,62),(31,47),(32,44),(33,41),(36,34),
}
print(f"(3) claimed D set == computed D set: {D_claimed == D}")
assert D_claimed == D
assert all(c != m for (c, m) in D), "dead state with c == m"
closure_bad = []
for s in D:
    for x in (0, 1):
        t = succ(A1, B1, s[0], s[1], x)
        if parity_ok(t) and t not in D:
            closure_bad.append((s, x, t))
print(f"    dead closure violations (successor parity-ok but not in D): {len(closure_bad)}")
assert not closure_bad

# ---------- (4) live coupled table ----------
A2, B2 = 19, 55
coupled = {
    (0,0):(0,0), (20,52):(9,27), (30,46):(14,22), (35,35):(16,16),
    (17,17):(8,8), (8,8):(4,4), (4,4):(2,2), (2,2):(1,1), (1,1):(0,0),
}
# claimed s1-successors: (state, x) -> ('L', next_live) | ('D', dead) | ('BOT',)
claimed_next = {
    ((0,0),0):('L',(0,0)),   ((0,0),1):('L',(20,52)),
    ((20,52),0):('D',(10,26)), ((20,52),1):('L',(30,46)),
    ((30,46),0):('D',(15,23)), ((30,46),1):('L',(35,35)),
    ((35,35),0):('L',(17,17)), ((35,35),1):('BOT',(38,37)),
    ((17,17),0):('L',(8,8)),  ((17,17),1):('BOT',(29,60)),
    ((8,8),0):('L',(4,4)),    ((8,8),1):('D',(24,48)),
    ((4,4),0):('L',(2,2)),    ((4,4),1):('D',(22,54)),
    ((2,2),0):('L',(1,1)),    ((2,2),1):('D',(21,53)),
    ((1,1),0):('L',(0,0)),    ((1,1),1):('BOT',(21,52)),
}
bad = []
for (s1, x), (kind, want) in claimed_next.items():
    t1 = succ(A1, B1, s1[0], s1[1], x)
    if t1 != want:
        bad.append((s1, x, t1, want))
        continue
    if kind == 'L':
        s2 = coupled[s1]
        t2 = succ(A2, B2, s2[0], s2[1], x)
        if coupled.get(t1) != t2:
            bad.append((s1, x, 's2 mismatch', t2, coupled.get(t1)))
    elif kind == 'D':
        if t1 not in D:
            bad.append((s1, x, 'not in D', t1))
    elif kind == 'BOT':
        if parity_ok(t1):
            bad.append((s1, x, 'claimed BOT but parity-ok', t1))
print(f"(4) live coupled transitions checked: {len(claimed_next)}, mismatches: {len(bad)}")
assert not bad
term_bad = [(s1, coupled[s1]) for s1 in L
            if s1[0] == s1[1] and coupled[s1][0] != coupled[s1][1]]
print(f"    terminal implication failures on coupled pairs: {len(term_bad)}")
assert not term_bad

# ---------- (5) semantic checks ----------
def H(a, b, c, m, k):
    return a * k + c == (clmul(b, k) ^ m)

KLIM = 1 << 15
bad_imp = 0
dead_witness = []
for s1 in L:
    s2 = coupled[s1]
    for k in range(KLIM):
        if H(A1, B1, s1[0], s1[1], k) and not H(A2, B2, s2[0], s2[1], k):
            bad_imp += 1
for s in D:
    for k in range(KLIM):
        if H(A1, B1, s[0], s[1], k):
            dead_witness.append((s, k))
            break
print(f"(5) coupled implication violations (k < 2^15): {bad_imp}")
print(f"    dead states with an H41 witness k < 2^15: {len(dead_witness)}")
assert bad_imp == 0 and not dead_witness

# bonus (soft): binary block structure of terms
import re
pat = re.compile(r'^0$|^(1110{6,})*111$')
odd_terms = [k for k in terms if k > 0]
nonconforming = [k for k in odd_terms if not pat.match(bin(k)[2:])]
print(f"    bonus: terms not of form (111 blocks, >=6 zeros apart): {len(nonconforming)}"
      + (f" e.g. {nonconforming[:5]}" if nonconforming else ""))
print("ALL CHECKS PASSED")
