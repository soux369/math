#!/usr/bin/env python3
"""Yue's independent verification of Job G (A045468, Detlefs).
Claim: for prime p, p mod 5 in {1,4} iff p^6 mod 210 == 1."""
def primes_upto(n):
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i*i::i] = b"\x00" * len(s[i*i::i])
    return [i for i, v in enumerate(s) if v]

# small-prime table (Lemma 2)
for p, q, r in [(2, 0, 64), (3, 3, 99), (5, 74, 85), (7, 560, 49)]:
    assert p ** 6 == q * 210 + r and pow(p, 6, 210) == r, p
# local tables (Lemma 5): r^6 mod q
assert [pow(r, 6, 2) for r in range(2)] == [0, 1]
assert [pow(r, 6, 3) for r in range(3)] == [0, 1, 1]
assert [pow(r, 6, 5) for r in range(5)] == [0, 1, 4, 4, 1]
assert [pow(r, 6, 7) for r in range(7)] == [0, 1, 1, 1, 1, 1, 1]
print("tables OK (Lemmas 2 and 5, all four moduli)")

bad = [p for p in primes_upto(50000)
       if (p % 5 in (1, 4)) != (pow(p, 6, 210) == 1)]
print(f"primes <= 50000: mismatches = {len(bad)}")
assert not bad
pref = [p for p in primes_upto(120) if p % 5 in (1, 4)]
print("A045468 prefix:", pref)
assert pref == [11, 19, 29, 31, 41, 59, 61, 71, 79, 89, 101, 109]
print("ALL CHECKS PASS")
