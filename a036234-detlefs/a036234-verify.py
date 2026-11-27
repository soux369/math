#!/usr/bin/env python3
"""Yue's independent verification of Job K (A036234, Detlefs):
a(k) = pi(k) + 1 (1 counted as prime). Detlefs's two claims:
(1) a(k) = min{i : binomial(k*prime(i), prime(i)) mod prime(i) = k}
(2) for k >= 2: binomial(k*q, q) mod q = 0 iff k is prime,
    where q = prime(a(k)-1) = largest prime <= k.
Proof (Neon): Lucas gives binomial(kp, p) = k (mod p); part (1) is
then immediate; part (2) needs Bertrand's postulate (if q < k and
q | k then k >= 2q, and a prime lies strictly between q and 2q).
Yue checks both claims by direct exact computation.
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
Pset = set(P)
def prime(i):  # 1-based
    return P[i - 1]
def pi(n):
    import bisect
    return bisect.bisect_right(P, n)
def a(k):
    return pi(k) + 1
def is_prime(n):
    return n in Pset

# Lemma 1 spot check by exact computation
bad = [k for k in range(0, 60) for p in P[:25] if comb(k * p, p) % p != k % p]
print(f"Lemma 1 (binom(kp,p) mod p = k mod p), k<60, first 25 primes: {len(bad)} mismatches")
assert not bad

# Part (1)
bad1 = []
for k in range(1, 300):
    i = 1
    while comb(k * prime(i), prime(i)) % prime(i) != k:
        i += 1
    if i != a(k):
        bad1.append((k, i, a(k)))
print(f"Part (1), k < 300: {len(bad1)} mismatches")
assert not bad1

# Part (2)
bad2 = []
for k in range(2, 2000):
    q = prime(a(k) - 1)
    if (comb(k * q, q) % q == 0) != is_prime(k):
        bad2.append(k)
print(f"Part (2), 2 <= k < 2000: {len(bad2)} mismatches")
assert not bad2
print("ALL CHECKS PASSED")
