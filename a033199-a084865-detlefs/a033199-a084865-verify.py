#!/usr/bin/env python3
"""Yue's independent verification of Job N (A033199 + A084865, Detlefs):
- A033199 (primes of form x^2+6y^2): p in seq iff p mod 6 = 1 and
  Fib(p) mod 6 = 1 — for ALL primes (2, 3: both sides false).
- A084865 (primes of form 2x^2+3y^2): for p > 3, p in seq iff
  (p mod 6)*(Fib(p) mod 6) = 25; exceptions exactly p = 2, 3.
Proof (Neon): Pisano period of Fib mod 6 is 24; both sides reduce to
residue classes mod 24; the form criteria are Cox's classical
theorems (cited): p = x^2+6y^2 iff p = 1,7 (mod 24);
p = 2x^2+3y^2 iff p = 5,11 (mod 24), for p > 3.
Yue checks: the Pisano table, the Cox criteria by DIRECT SEARCH,
both Detlefs equivalences, and the true OEIS prefixes (fetched from
oeis.org 2026-11-27 — Neon's answer reproduced both term lists
incorrectly; the proof does not use them).
"""
from math import isqrt

def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]

def fib_mod(n, m):
    # fast doubling: returns F(n) mod m
    def fd(k):
        if k == 0:
            return (0, 1)
        a, b = fd(k >> 1)
        c = a * ((b * 2 - a) % m) % m
        d = (a * a + b * b) % m
        return (d, (c + d) % m) if k & 1 else (c, d)
    return fd(n)[0]

# Pisano table mod 6
table = [fib_mod(n, 6) for n in range(24)]
claimed = [0,1,1,2,3,5,2,1,3,4,1,5,0,5,5,4,3,1,4,5,3,2,5,1]
print(f"Pisano table mod 6 matches Neon's: {table == claimed}")
assert table == claimed and fib_mod(24, 6) == 0 and fib_mod(25, 6) == 1

def rep1(p):  # x^2 + 6y^2 = p ?
    y = 0
    while 6 * y * y <= p:
        r = p - 6 * y * y
        x = isqrt(r)
        if x * x == r:
            return True
        y += 1
    return False

def rep2(p):  # 2x^2 + 3y^2 = p ?
    x = 0
    while 2 * x * x <= p:
        r = p - 2 * x * x
        if r % 3 == 0:
            y = isqrt(r // 3)
            if 3 * y * y == r:
                return True
        x += 1
    return False

P = primes_upto(50000)
cox1 = cox2 = det1 = det2 = 0
exc = []
for p in P:
    r1, r2 = rep1(p), rep2(p)
    f = fib_mod(p, 6)
    if p > 3:
        if r1 != (p % 24 in (1, 7)):
            cox1 += 1
        if r2 != (p % 24 in (5, 11)):
            cox2 += 1
    if r1 != (p % 6 == 1 and f == 1):
        det1 += 1
    if p > 3 and r2 != ((p % 6) * f == 25):
        det2 += 1
    if p <= 3 and r2 and (p % 6) * f != 25:
        exc.append(p)
print(f"primes <= 50000: {len(P)}; Cox x^2+6y^2 mismatches: {cox1}; "
      f"Cox 2x^2+3y^2 mismatches: {cox2}")
print(f"Detlefs A033199 mismatches (all primes): {det1}; "
      f"A084865 mismatches (p > 3): {det2}; exceptions: {exc}")
assert cox1 == cox2 == det1 == det2 == 0 and exc == [2, 3]

# true OEIS prefixes (fetched 2026-11-27)
seq1 = [p for p in P if rep1(p)][:18]
seq2 = [p for p in P if rep2(p)][:20]
assert seq1 == [7,31,73,79,97,103,127,151,193,199,223,241,271,313,337,367,409,433], seq1
assert seq2 == [2,3,5,11,29,53,59,83,101,107,131,149,173,179,197,227,251,269,293,317], seq2
print("OEIS prefixes for A033199 and A084865 match  OK")
print("ALL CHECKS PASSED")
