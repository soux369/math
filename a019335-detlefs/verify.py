#!/usr/bin/env python3
"""Yue's independent verification of Job I (A019335, Detlefs).
Claim: (a) ord_k(5) = k-1 iff k is prime with primitive root 5
(k = 2 included); (b) all such primes are 2 or 3 mod 5."""
import math
def primes_upto(n):
    s = bytearray(b"\x01") * (n + 1); s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = b"\x00" * len(s[i*i::i])
    return [i for i, v in enumerate(s) if v]
def order_mod(a, m):
    if math.gcd(a, m) != 1: return None
    phi = m
    x = m; f = {}
    d = 2
    while d * d <= x:
        while x % d == 0: f[d] = f.get(d, 0) + 1; x //= d
        d += 1 if d == 2 else 2
    if x > 1: f[x] = f.get(x, 0) + 1
    # phi from factorization of m is wrong in general; use euler phi:
    phi = m
    for q in f: phi = phi // q * (q - 1)
    o = phi
    # factorize phi
    y = phi; fac = {}
    d = 2
    while d * d <= y:
        while y % d == 0: fac[d] = fac.get(d, 0) + 1; y //= d
        d += 1 if d == 2 else 2
    if y > 1: fac[y] = fac.get(y, 0) + 1
    for q in fac:
        while o % q == 0 and pow(a, o // q, m) == 1: o //= q
    return o

primes = set(primes_upto(3000))
lhs = set()
for k in range(2, 3000):
    if math.gcd(5, k) == 1 and order_mod(5, k) == k - 1:
        lhs.add(k)
rhs = {p for p in primes if order_mod(5, p) == p - 1}
print("k<3000: ord_k(5)=k-1 set == primes with prim. root 5:",
      lhs == rhs, "| count:", len(lhs))
print("all such primes are 2,3 mod 5:",
      all(p % 5 in (2, 3) for p in rhs))
print("k=2 included:", 2 in lhs, "(ord_2(5) =", order_mod(5, 2), ")")
print("first terms:", sorted(rhs)[:15])
assert lhs == rhs and all(p % 5 in (2, 3) for p in rhs) and 2 in lhs
assert sorted(rhs)[:10] == [2, 3, 7, 17, 23, 37, 43, 47, 53, 73]
print("ALL CHECKS PASS")
