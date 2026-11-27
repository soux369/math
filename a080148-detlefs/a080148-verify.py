#!/usr/bin/env python3
"""Yue's independent verification of Job J (A080148, Detlefs):
the terms of A080148 (positions of primes = 3 mod 4 among all primes)
are exactly the indices k with binomial(prime(k), 3) odd.
Core claim: for every prime p, binomial(p, 3) odd iff p = 3 (mod 4).
Proof (Neon): Lucas mod 2 with m = 3 = 0b11: odd iff bits 0,1 of p
are both 1 iff p = 3 (mod 4). Yue checks the arithmetic exhaustively.
"""
from math import comb

def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]

P = primes_upto(100000)
bad = []
for p in P:
    odd = (comb(p, 3) % 2 == 1) if p >= 3 else False  # binom(2,3) = 0
    if odd != (p % 4 == 3):
        bad.append(p)
print(f"primes <= 100000: {len(P)}; claim mismatches: {len(bad)}")
assert not bad

# exact counts Neon left open (primes <= 5000)
P5 = [p for p in P if p <= 5000]
n3 = sum(1 for p in P5 if p % 4 == 3)
print(f"pi(5000) = {len(P5)}; primes = 3 (mod 4) up to 5000: {n3}")

# A080148 terms: positions (1-based) of primes = 3 mod 4, vs positions
# where binomial(prime(k),3) is odd
pos_mod = [k for k, p in enumerate(P, 1) if p % 4 == 3]
pos_bin = [k for k, p in enumerate(P, 1) if p >= 3 and comb(p, 3) % 2 == 1]
print(f"A080148 first 15 terms: {pos_mod[:15]}")
assert pos_mod == pos_bin
print("position sets identical  OK")
print("ALL CHECKS PASSED")
