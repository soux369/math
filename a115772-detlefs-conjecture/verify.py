#!/usr/bin/env python3
"""Independent verification of the A115772 / Detlefs result.

Claims under test:
 (A) A115772 = {i : 13i = C(21,i)} is a subset of OR4 = {x | (x<<2) : x >= 0}.
 (B) The containment is strict; smallest element of OR4 \\ A115772 is 325
     (next ones claimed: 335, 365, 367, 485).
 (C) The 24-pair state relation (equation automaton x subset DFA) is closed
     and satisfies the terminal implication c = m  ==>  (0,0) in S.

Automaton (suffix form, as in the Lean proof):
  E(c,m,i) : c + 13*i = m XOR C(21, i).  On LSB b of i: needs c = m (mod 2),
  next state ((c + 13b)//2, (m ^ (21b))//2) for i//2.
DFA for OR4: NFA states are pairs (b0,b1) = (x_{j-2}, x_{j-1}); subset transition
  d(S, b) = {(b1, xj) : exists b0 with (b0,b1) in S and (xj | b0) == b}.
Start pair: ((0,0), {(0,0)}). BFS expanding only pairs with c = m (mod 2);
successors with c != m (mod 2) are the boundary/fail pairs.
"""

from collections import deque


def carryless(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def in_or4(i):
    """Exists x >= 0 with i == x | (x << 2)?  Greedy bit DP over bits of i."""
    # state: (x_{j-1}, x_{j-2}) possibilities carried as a set of (prev1, prev2)
    states = {(0, 0)}
    j = 0
    while (1 << j) <= i or states:
        bit = (i >> j) & 1
        nxt = set()
        for (p1, p2) in states:  # p1 = x_{j-1}, p2 = x_{j-2}
            for xj in (0, 1):
                if (xj | p2) == bit:
                    nxt.add((xj, p1))
        states = nxt
        if not states:
            return False
        j += 1
        if j > i.bit_length() + 2:
            break
    # after processing enough bits, need a flush: x bits beyond must be 0,
    # which the loop enforces since i's bits are 0 there; accept if any state
    # can flush with xj = 0 repeatedly -- equivalent to state (0,0) reachable
    # after 2 extra zero bits, already covered by the loop bound.
    return (0, 0) in states or any(p1 == 0 and p2 == 0 for (p1, p2) in states)


def in_or4_bruteforce(i):
    return any(x | (x << 2) == i for x in range(i + 1))


def eq_step(c, m, b):
    return (c + 13 * b) // 2, (m ^ (21 * b)) // 2


def dfa_step(S, b):
    out = set()
    for (b0, b1) in S:
        for xj in (0, 1):
            if (xj | b0) == b:
                out.add((b1, xj))
    return frozenset(out)


def bfs_pairs():
    start = ((0, 0), frozenset({(0, 0)}))
    seen = {start}
    trans = {}
    q = deque([start])
    while q:
        (c, m), S = q.popleft()
        if c % 2 != m % 2:
            trans[((c, m), S)] = None
            continue
        outs = []
        for b in (0, 1):
            nxt = (eq_step(c, m, b), dfa_step(S, b))
            outs.append(nxt)
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
        trans[((c, m), S)] = outs
    return seen, trans


def main():
    # --- (B) numerics first: counterexample and minimality ---
    print("13*325 =", 13 * 325, " C(21,325) =", carryless(21, 325),
          " 325 == 65 | (65<<2):", 325 == 65 | (65 << 2))
    diff = [i for i in range(2000) if in_or4(i) and 13 * i != carryless(21, i)]
    print("OR4 \\ A115772 below 2000:", diff[:8])
    print("smallest counterexample == 325:", diff[0] == 325)

    # cross-check in_or4 against brute force on a range
    assert all(in_or4(i) == in_or4_bruteforce(i) for i in range(600))
    print("in_or4 agrees with brute force for i < 600")

    # --- (A) containment numerically to 2^20 ---
    bad = [i for i in range(1 << 20)
           if 13 * i == carryless(21, i) and not in_or4(i)]
    print(f"containment check i < 2^20: violations: {len(bad)}")

    # --- (C) state-pair relation ---
    seen, trans = bfs_pairs()
    print(f"reachable pairs: {len(seen)}")
    active = [p for p in seen if p[0][0] % 2 == p[0][1] % 2]
    print(f"parity-ok (active) pairs: {len(active)}, fail pairs: {len(seen) - len(active)}")
    term_ok = all(((c, m), S) and (c != m or (0, 0) in S) for ((c, m), S) in seen)
    print("terminal implication (c = m ==> (0,0) in S) on all pairs:", term_ok)

    claimed = {
        ((0, 0), frozenset({(0, 0)})),
        ((1, 1), frozenset({(0, 0)})),
        ((2, 2), frozenset({(0, 0)})),
        ((3, 3), frozenset({(0, 0)})),
        ((3, 5), frozenset({(1, 0)})),
        ((4, 4), frozenset({(0, 0), (1, 0)})),
        ((5, 7), frozenset({(1, 0)})),
        ((6, 6), frozenset({(0, 0), (1, 0)})),
        ((6, 10), frozenset({(0, 1)})),
        ((7, 11), frozenset({(0, 1)})),
        ((8, 8), frozenset({(0, 0), (0, 1)})),
        ((9, 9), frozenset({(0, 0), (0, 1)})),
        ((9, 15), frozenset({(1, 1)})),
        ((10, 14), frozenset({(0, 1), (1, 1)})),
        ((11, 13), frozenset({(1, 0), (1, 1)})),
        ((12, 12), frozenset({(0, 0), (0, 1), (1, 0), (1, 1)})),
        ((1, 2), frozenset()),
        ((2, 3), frozenset()),
        ((4, 7), frozenset()),
        ((5, 6), frozenset()),
        ((7, 10), frozenset({(0, 1)})),
        ((8, 11), frozenset({(0, 1)})),
        ((10, 15), frozenset({(1, 1)})),
        ((11, 14), frozenset({(0, 1), (1, 1)})),
    }
    print("reachable set == claimed 24-pair set:", seen == claimed)
    if seen != claimed:
        print("  only in mine:", sorted(seen - claimed, key=str))
        print("  only in claimed:", sorted(claimed - seen, key=str))


if __name__ == "__main__":
    main()
