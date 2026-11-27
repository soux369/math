#!/usr/bin/env python3
"""Job O verification, part 2 (heavy checks):
(3) For small primes p in {3,5,7,11,13}: DIRECT computation of
    a(p^4) = binomial(p^8, p^4) mod p^12 (is it = p^4?) versus the
    Lemma-6 criterion T_p = sum (m(p-m))^{-1} mod p^2 == 0.
    Both must agree (all false: no small Wolstenholme primes), and
    the exact identity binom(p^8-1, p^4-1) = 1 - p^6 T_p (mod p^8).
(4) The same identity in the form binom(p^8-1, p^4-1)
    = 1 - p^5 H_{p-1} (mod p^8), against Neon's residues.
(6) No odd prime p < 16843 is Wolstenholme: H_{p-1} != 0 (mod p^3).
"""
from math import comb

def H_mod(p, mod):
    return sum(pow(m, -1, mod) for m in range(1, p)) % mod

def T_mod(p, mod):
    return sum(pow(m * (p - m), -1, mod) for m in range(1, (p - 1) // 2 + 1)) % mod

claimed_residues = {3: 2917, 5: 156251, 7: 823544, 11: 97435856, 13: 376491103}

for p in (3, 5, 7, 11, 13):
    direct = (comb(p ** 8, p ** 4) - p ** 4) % p ** 12 == 0
    t = T_mod(p, p ** 2)
    crit = (t == 0)
    lhs = comb(p ** 8 - 1, p ** 4 - 1) % p ** 8
    ident1 = (1 - p ** 6 * t) % p ** 8
    ident2 = (1 - p ** 5 * H_mod(p, p ** 8)) % p ** 8
    print(f"p={p}: direct a(p^4)=p^4 mod p^12: {direct}; criterion T=0 mod p^2: {crit}; "
          f"binom(p^8-1,p^4-1) mod p^8 = {lhs}; via 1-p^6 T: {ident1}; "
          f"via 1-p^5 H: {ident2}; Neon residue: {claimed_residues[p]}")
    assert direct == crit == False
    assert lhs == ident1 == ident2 == claimed_residues[p]
print("(3)+(4) criterion and identities confirmed for p in {3,5,7,11,13}")

def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(2, n + 1) if sieve[i]]

wol = [p for p in primes_upto(16842) if p > 2 and H_mod(p, p ** 3) == 0]
print(f"(6) Wolstenholme primes < 16843: {wol}")
assert wol == []
print("ALL HEAVY CHECKS PASSED")
