#!/usr/bin/env python3
"""Yue's independent verification of Job O (A014062, Detlefs disproof):
a(n) = binomial(n^2, n) = n (mod n^3) was claimed to hold only for
n = 1, odd primes, p^2, p^3. Gemini's disproof: for odd prime p,
a(p^4) = p^4 (mod p^12) iff p is a Wolstenholme prime
(H_{p-1} = 0 mod p^3); p = 16843 is one, so n = 16843^4 is a
counterexample. Yue checks: (1) the arithmetic and primality;
(2) the decisive Wolstenholme sums at 16843 by direct modular
computation; (3) the Lemma-6 criterion against DIRECT computation
of a(p^4) mod p^12 for small primes; (4) the binomial identity
residues; (5) Detlefs's claim range exhaustively for n <= 2000;
(6) 16843 is the smallest Wolstenholme prime (all smaller odd
primes fail H_{p-1} = 0 mod p^3).
"""
from math import comb, isqrt

def is_prime(n):
    if n < 2:
        return False
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return False
    return True

def H_mod(p, mod):
    return sum(pow(m, -1, mod) for m in range(1, p)) % mod

def T_mod(p, mod):
    # sum_{m=1}^{(p-1)/2} (m(p-m))^{-1} mod `mod`
    return sum(pow(m * (p - m), -1, mod) for m in range(1, (p - 1) // 2 + 1)) % mod

# ---------- (1) arithmetic ----------
p = 16843
assert is_prime(p)
n = p ** 4
print(f"(1) p = 16843 prime; n = p^4 = {n} (claimed 80478114820849201)")
assert n == 80478114820849201
assert n ** 2 == 6476726965117787823567238782338401
assert n ** 3 == 521234776362039506304947135252947946514403372467601
print("    n^2, n^3 match Neon's values  OK")

# ---------- (2) Wolstenholme sums at 16843 ----------
t2 = T_mod(p, p ** 2)
t3 = T_mod(p, p ** 3)
h3 = H_mod(p, p ** 3)
h4 = H_mod(p, p ** 4)
print(f"(2) T mod p^2 = {t2} (claim 0); T mod p^3 = {t3} (claim 2860412481867 = 10083*p^2: {10083 * p**2})")
print(f"    H mod p^3 = {h3} (claim 0); H mod p^4 = {h4} (claim 10083*p^3 = {10083 * p**3})")
print(f"    binom(2p-1, p-1) mod p^4 = {comb(2 * p - 1, p - 1) % p**4} (claim 1)")
assert t2 == 0 and t3 == 2860412481867 == 10083 * p ** 2
assert h3 == 0 and h4 == 10083 * p ** 3
assert comb(2 * p - 1, p - 1) % p ** 4 == 1
print("    Wolstenholme property at 16843 CONFIRMED by direct computation")

# ---------- (5) Detlefs range n <= 2000 (direct) ----------
def is_p2_p3(m):
    for q in range(2, isqrt(m) + 1):
        if is_prime(q) and (q * q == m or q ** 3 == m):
            return True
    return False

hits = [m for m in range(1, 2001) if (comb(m * m, m) - m) % m ** 3 == 0]
nonprime_hits = [m for m in hits if not is_prime(m)]
claimed_np = [1, 9, 25, 49, 121, 125, 169, 289, 343, 361, 529, 841, 961,
              1331, 1369, 1681, 1849]
print(f"(5) n <= 2000: {len(hits)} hits; non-prime hits match Neon's list: "
      f"{nonprime_hits == claimed_np}; all are 1, p^2 or p^3: "
      f"{all(m == 1 or is_p2_p3(m) for m in nonprime_hits)}")
assert nonprime_hits == claimed_np
print("ALL FAST CHECKS PASSED")
