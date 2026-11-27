#!/usr/bin/env python3
"""Independent verification of the claimed proof A115774 subset A115772.

Claim: for all i >= 0, 15*i = C(23, i)  ==>  13*i = C(21, i),
where C is carryless (GF(2)[X]) multiplication (OEIS A048720).

Method (recomputed from scratch, not copied from the claimant's table):
state (c, m) for equation a*i = C(b, i) after processing t low bits of i:
  c = floor(a*u / 2^t),  m = floor(C(b, u) / 2^t),  u = i mod 2^t.
Transition on bit x (requires c % 2 == m % 2, else the bit t mismatches):
  c' = (c + a*x) // 2,  m' = (m ^ (b*x)) // 2.
Terminal: a*i == C(b, i)  iff  final c == m (given all bits matched).

We BFS the reachable state pairs ((c1,m1),(c2,m2)) from ((0,0),(0,0)),
expanding only states where equation 1 has matching parity, and check:
  (P1) in every reachable state, c1 == m1 (mod 2) implies c2 == m2 (mod 2)
       -- in fact we check the stronger: the set of parity-ok states for eq1
          is a subset of parity-ok states for eq2 along reachable pairs;
  (P2) in every reachable state, c1 == m1 implies c2 == m2.
Then compare the reachable set and transitions against the claimant's
14-state table, and run a brute-force numeric check for i < 2^20.
"""

from collections import deque

A1, B1 = 15, 23   # equation 1: A115774
A2, B2 = 13, 21   # equation 2: A115772


def step(c, m, a, b, x):
    return (c + a * x) // 2, (m ^ (b * x)) // 2


def bfs():
    start = ((0, 0), (0, 0))
    seen = {start}
    trans = {}
    q = deque([start])
    while q:
        (c1, m1), (c2, m2) = q.popleft()
        if c1 % 2 != m1 % 2:
            trans[((c1, m1), (c2, m2))] = None  # eq1 dead: no outgoing
            continue
        outs = []
        for x in (0, 1):
            nxt = (step(c1, m1, A1, B1, x), step(c2, m2, A2, B2, x))
            outs.append(nxt)
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
        trans[((c1, m1), (c2, m2))] = outs
    return seen, trans


def carryless(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def main():
    seen, trans = bfs()
    print(f"reachable state pairs: {len(seen)}")

    ok = True
    # P1/P2 over all reachable pairs
    for (c1, m1), (c2, m2) in seen:
        if c1 % 2 == m1 % 2 and c2 % 2 != m2 % 2:
            print(f"P1 FAIL at {((c1,m1),(c2,m2))}: eq1 parity ok but eq2 broken")
            ok = False
        if c1 == m1 and c2 != m2:
            print(f"P2 FAIL at {((c1,m1),(c2,m2))}: eq1 terminal but eq2 not")
            ok = False
    print("P1 (parity preservation) and P2 (terminal implication):",
          "PASS" if ok else "FAIL")

    # Claimant's table (from the Gemini/Neon proof), as a set of pairs
    claimed = {
        ((0, 0), (0, 0)), ((7, 11), (6, 10)), ((3, 5), (3, 5)),
        ((11, 14), (9, 15)), ((1, 2), (1, 2)), ((9, 9), (8, 8)),
        ((4, 4), (4, 4)), ((12, 15), (10, 14)), ((2, 2), (2, 2)),
        ((1, 1), (1, 1)), ((8, 10), (7, 11)), ((8, 11), (7, 10)),
        ((4, 5), (3, 5)), ((11, 14), (10, 15)),
    }
    print("reachable set == claimed 14-state set:", seen == claimed)
    if seen != claimed:
        print("  only in mine:", sorted(seen - claimed))
        print("  only in claimed:", sorted(claimed - seen))

    # Compare transitions for the 8 parity-ok states
    claimed_trans = {
        ((0, 0), (0, 0)): [((0, 0), (0, 0)), ((7, 11), (6, 10))],
        ((7, 11), (6, 10)): [((3, 5), (3, 5)), ((11, 14), (9, 15))],
        ((3, 5), (3, 5)): [((1, 2), (1, 2)), ((9, 9), (8, 8))],
        ((9, 9), (8, 8)): [((4, 4), (4, 4)), ((12, 15), (10, 14))],
        ((4, 4), (4, 4)): [((2, 2), (2, 2)), ((9, 9), (8, 8))],
        ((2, 2), (2, 2)): [((1, 1), (1, 1)), ((8, 10), (7, 11))],
        ((1, 1), (1, 1)): [((0, 0), (0, 0)), ((8, 11), (7, 10))],
        ((8, 10), (7, 11)): [((4, 5), (3, 5)), ((11, 14), (10, 15))],
    }
    tmatch = all(trans.get(k) == v for k, v in claimed_trans.items())
    print("transitions match claimed table:", tmatch)

    # Brute-force numeric check
    bad = []
    members = []
    for i in range(1 << 20):
        if 15 * i == carryless(23, i):
            members.append(i)
            if 13 * i != carryless(21, i):
                bad.append(i)
    print(f"numeric check i < 2^20: A115774 members found: {len(members)}, "
          f"counterexamples to containment: {len(bad)}")
    print("first members:", members[:12])
    # OEIS A115774 starts 0,5,10,20,21,40,42,80,84,85,160,168,...
    print("members match OEIS prefix:",
          members[:12] == [0, 5, 10, 20, 21, 40, 42, 80, 84, 85, 160, 168])
    # strictness witness i = 15
    print("i=15: 15*15 =", 15 * 15, " C(23,15) =", carryless(23, 15),
          " 13*15 =", 13 * 15, " C(21,15) =", carryless(21, 15))


if __name__ == "__main__":
    main()
