#!/usr/bin/env python3
"""Yue's independent verification of Neon's brief-1 result:
A115801 subset A391850 via  9k = C(25,k)  <=>  15k = C(19,k).

Checks:
 1. Single-side BFS reachable sets: sizes 24 for (9,25), 14 for (15,19).
 2. Dead sets (reachable but unsatisfiable for every k) equal Neon's lists.
 3. Coupled BFS live pairs equal Neon's 8; every transition from a live pair
    lands in LivePair or in Dead9 x Dead15.
 4. Brute force: the two sets agree for k < 2^20.
 5. Neon's sample arithmetic.
"""

def C(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r

def succ(a, b, c, r, bit):
    """One step of  a k + c = C(b,k) xor r  consuming the LSB of k."""
    if bit == 0:
        if c % 2 != r % 2:
            return None
        return (c // 2, r // 2)
    if (a + c) % 2 != (b ^ r) % 2:
        return None
    return ((a + c) // 2, (b ^ r) // 2)

def bfs_single(a, b):
    seen, stack = {(0, 0)}, [(0, 0)]
    while stack:
        c, r = stack.pop()
        for bit in (0, 1):
            s = succ(a, b, c, r, bit)
            if s is not None and s not in seen:
                seen.add(s)
                stack.append(s)
    return seen

def satisfiable(a, b, c0, r0):
    """Some k satisfies the equation from state (c0,r0) iff an accepting
    state (c == r) is reachable via parity-valid transitions."""
    seen, stack = {(c0, r0)}, [(c0, r0)]
    while stack:
        c, r = stack.pop()
        if c == r:
            return True
        for bit in (0, 1):
            s = succ(a, b, c, r, bit)
            if s is not None and s not in seen:
                seen.add(s)
                stack.append(s)
    return False

DEAD9_CLAIM = {(0,1),(1,2),(1,3),(2,6),(2,7),(3,4),(3,5),(3,7),(5,12),
               (5,13),(5,15),(6,14),(6,15),(7,10),(7,11),(8,9)}
LIVE9_CLAIM = {(0,0),(4,12),(6,10),(7,9),(8,8),(4,4),(2,2),(1,1)}
DEAD15_CLAIM = {(3,4),(5,6),(6,7),(8,9),(9,8),(11,10)}
LIVE15_CLAIM = {(0,0),(7,9),(11,13),(13,15),(14,14),(7,7),(3,3),(1,1)}
LIVE_PAIRS_CLAIM = {((0,0),(0,0)), ((4,12),(7,9)), ((6,10),(11,13)),
                    ((7,9),(13,15)), ((8,8),(14,14)), ((4,4),(7,7)),
                    ((2,2),(3,3)), ((1,1),(1,1))}

reach9 = bfs_single(9, 25)
reach15 = bfs_single(15, 19)
dead9 = {s for s in reach9 if not satisfiable(9, 25, *s)}
dead15 = {s for s in reach15 if not satisfiable(15, 19, *s)}
print("1. reachable sizes:", len(reach9), "(claim 24),", len(reach15), "(claim 14)")
print("2. dead9 == claim:", dead9 == DEAD9_CLAIM, "| live9 == claim:", reach9 - dead9 == LIVE9_CLAIM)
print("   dead15 == claim:", dead15 == DEAD15_CLAIM, "| live15 == claim:", reach15 - dead15 == LIVE15_CLAIM)

# dead states must also be semantically dead: no solution k < 2^18
sem_dead_ok = True
for (a, b, dead) in ((9, 25, dead9), (15, 19, dead15)):
    for (c, r) in dead:
        for k in range(1 << 18):
            if a * k + c == (C(b, k) ^ r):
                sem_dead_ok = False
                print("   !! dead state has a solution:", a, b, c, r, k)
                break
print("   dead states solution-free for k < 2^18:", sem_dead_ok)

# 3. coupled BFS
start = ((0, 0), (0, 0))
seen, stack = {start}, [start]
bad_transition = []
while stack:
    (c1, r1), (c2, r2) = stack.pop()
    for bit in (0, 1):
        s1 = succ(9, 25, c1, r1, bit)
        s2 = succ(15, 19, c2, r2, bit)
        if s1 is None or s2 is None:
            continue
        nxt = (s1, s2)
        if nxt not in seen:
            seen.add(nxt)
            stack.append(nxt)
live_pairs = {p for p in seen if p[0] not in dead9 and p[1] not in dead15}
mixed = {p for p in seen if (p[0] in dead9) != (p[1] in dead15)}
print("3. coupled reachable pairs:", len(seen), "| live pairs == claim:", live_pairs == LIVE_PAIRS_CLAIM,
      "| mixed (one side dead) pairs:", len(mixed))
for p in live_pairs:
    for bit in (0, 1):
        s1 = succ(9, 25, *p[0], bit)
        s2 = succ(15, 19, *p[1], bit)
        if s1 is None and s2 is None:
            continue
        if (s1 is None) != (s2 is None):
            bad_transition.append((p, bit, "parity mismatch between sides"))
        elif (s1, s2) not in live_pairs and not (s1 in dead9 and s2 in dead15):
            bad_transition.append((p, bit, "lands outside live/dead x dead"))
print("   bad transitions from live pairs:", bad_transition)

# 4. brute force set equality
N = 1 << 20
s1 = {k for k in range(N) if 9 * k == C(25, k)}
s2 = {k for k in range(N) if 15 * k == C(19, k)}
print("4. brute force k < 2^20: |A115801| =", len(s1), "|15-side| =", len(s2), "| equal:", s1 == s2)
print("   A115801 prefix:", sorted(s1)[:8], "(OEIS: 0, 15, 30, 31, 60, 62, 63)")

# 5. samples
for k, v9, v15 in ((15, 135, 225), (30, 270, 450), (31, 279, 465), (3855, 34695, 57825)):
    print(f"5. k={k}: 9k={9*k} C(25,k)={C(25,k)} (claim {v9}) | 15k={15*k} C(19,k)={C(19,k)} (claim {v15})")
