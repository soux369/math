#!/usr/bin/env python3
"""Yue's independent verification of Job L (A067793, Detlefs):
Detlefs claimed A067793 = {composite n : S(n) = sum k^2 = 0 (mod n)}.
FALSE. Correct picture (all checked here with exact arithmetic):
- S(n) = 0 (mod n)  iff  gcd(n, 6) = 1.
- n in A067793 (nonprime, phi(n) > 2n/3)  iff  prod_{p|n}(1 - 1/p) > 2/3.
- Hence A067793 is a PROPER subset of the S-set (within nonprimes);
  smallest counterexample 385 = 5*7*11.
- The phi condition has NO bound on the number of distinct prime
  factors: smallest 3-prime member is 715 = 5*11*13.
"""
from fractions import Fraction
from math import gcd

def S_mod(n):
    return (n * (n + 1) * (2 * n + 1) // 6) % n == 0

def prime_factors(n):
    fs = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fs.add(n)
    return fs

def phi(n):
    r = n
    for p in prime_factors(n):
        r = r // p * (p - 1)
    return r

def is_prime(n):
    if n < 2:
        return False
    return prime_factors(n) == {n}

def prod_cond(n):
    pr = Fraction(1, 1)
    for p in prime_factors(n):
        pr *= Fraction(p - 1, p)
    return pr

# S-set characterization
bad = [n for n in range(1, 100001) if S_mod(n) != (gcd(n, 6) == 1)]
print(f"S(n) = 0 (mod n) iff gcd(n,6)=1, n <= 100000: {len(bad)} mismatches")
assert not bad

# phi characterization + counterexample arithmetic
assert 385 * 386 * 771 // 6 == 19096385 == 385 * 49601
assert phi(385) == 240 and Fraction(240, 385) <= Fraction(2, 3)
assert phi(715) == 480 and Fraction(480, 715) > Fraction(2, 3)
print("385: S(385) = 19,096,385 = 385 x 49,601; phi(385) = 240 < 770/3  OK")
print("715: phi(715) = 480 > 1430/3  OK")

# A067793 membership vs product condition; one-directional mismatch count
mismatch_phi_not_S, mismatch_S_not_phi = [], []
terms = []
for n in range(1, 200001):
    if is_prime(n):
        continue
    inA = phi(n) * 3 > 2 * n
    if inA:
        terms.append(n)
        if prod_cond(n) <= Fraction(2, 3):
            raise AssertionError(f"product condition fails at {n}")
        if not S_mod(n):
            mismatch_phi_not_S.append(n)
    elif S_mod(n):
        mismatch_S_not_phi.append(n)
print(f"nonprime n <= 200000: phi-true but S-false: {len(mismatch_phi_not_S)}; "
      f"S-true but phi-false: {len(mismatch_S_not_phi)} (smallest {mismatch_S_not_phi[0]})")
assert not mismatch_phi_not_S and mismatch_S_not_phi[0] == 385

# 715 is the smallest member with 3 distinct prime factors
w3 = [n for n in terms if len(prime_factors(n)) == 3]
print(f"smallest A067793 member with omega = 3: {min(w3)}")
assert min(w3) == 715
# members with omega >= 4 exist (large primes)
w4 = [n for n in range(1, 200001) if not is_prime(n) and phi(n) * 3 > 2 * n
      and len(prime_factors(n)) >= 4]
print(f"members with omega >= 4 up to 200000: {len(w4)} (smallest {min(w4) if w4 else None})")
assert w4

# OEIS prefix check (fetched from oeis.org 2026-11-27; Neon's answer
# omitted 35 from its reproduced list — the entry itself has it)
prefix = [1, 25, 35, 49, 55, 65, 77, 85, 91, 95, 115, 119, 121, 125, 133, 143,
          145, 155, 161, 169, 175, 185, 187, 203, 205, 209, 215, 217, 221, 235]
assert terms[:len(prefix)] == prefix, (terms[:5], prefix[:5])
print("OEIS prefix (30 terms) matches  OK")
print("ALL CHECKS PASSED")
