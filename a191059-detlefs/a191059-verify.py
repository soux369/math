#!/usr/bin/env python3
"""Yue's independent verification of Job H (A191059, Detlefs).
Claim: (p|6) = -1 (Kronecker) iff (p mod 6) * (F(p) mod 6) = 5."""
def primes_upto(n):
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i*i::i] = b"\x00" * len(s[i*i::i])
    return [i for i, v in enumerate(s) if v]

def kron6(n):
    if n % 2 == 0:
        a = 0
    else:
        a = 1 if n % 8 in (1, 7) else -1
    b = 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)
    return a * b

# Pisano table mod 6, period 24
F = [0, 1]
for _ in range(60):
    F.append((F[-1] + F[-2]) % 6)
claimed = [0, 1, 1, 2, 3, 5, 2, 1, 3, 4, 1, 5, 0,
           5, 5, 4, 3, 1, 4, 5, 3, 2, 5, 1]
assert F[:24] == claimed, F[:24]
assert F[24] == 0 and F[25] == 1
print("Pisano table mod 6 matches; period 24 confirmed")

# Main theorem for ALL n <= 5000 (three-way equivalence)
bad = 0
for n in range(1, 5001):
    c1 = kron6(n) == -1
    c2 = n % 24 in (13, 17, 19, 23)
    c3 = (n % 6) * F[n % 24] == 5
    if not (c1 == c2 == c3):
        bad += 1
        print("MISMATCH n =", n, c1, c2, c3)
print(f"all n <= 5000: three-way mismatches = {bad}")
assert bad == 0

# primes <= 50000: Detlefs equivalence + OEIS prefix
badp = [p for p in primes_upto(50000)
        if (kron6(p) == -1) != ((p % 6) * F[p % 24] == 5)]
print(f"primes <= 50000: mismatches = {len(badp)}")
assert not badp
pref = [p for p in primes_upto(150) if kron6(p) == -1]
print("A191059 prefix:", pref)
assert pref == [13, 17, 19, 23, 37, 41, 43, 47, 61, 67, 71, 89,
                109, 113, 137, 139]
print("ALL CHECKS PASS")
