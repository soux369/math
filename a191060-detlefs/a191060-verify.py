#!/usr/bin/env python3
"""Yue's independent verification of Job F (A191060, Detlefs).
Claim: for prime p, a_p(n) = p^(5n) mod 11 has period 2 repeating
[1,10] (a_p(n) = 1 for even n, 10 for odd n) iff p is a quadratic
nonresidue mod 11."""
def primes_upto(n):
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i*i::i] = b"\x00" * len(s[i*i::i])
    return [i for i, v in enumerate(s) if v]

# Table checks
sq = sorted({(x * x) % 11 for x in range(11)})
assert sq == [0, 1, 3, 4, 5, 9], sq
r5 = {r: pow(r, 5, 11) for r in range(11)}
claimed = {0: 0, 1: 1, 2: 10, 3: 1, 4: 1, 5: 1, 6: 10, 7: 10,
           8: 10, 9: 1, 10: 10}
assert r5 == claimed, r5
for r, q, c in [(2, 2, 10), (3, 22, 1), (4, 93, 1), (5, 284, 1),
                (6, 706, 10), (7, 1527, 10), (8, 2978, 10),
                (9, 5368, 1), (10, 9090, 10)]:
    assert r ** 5 == 11 * q + c, (r, q, c)
print("tables OK: squares {0,1,3,4,5,9}; r^5 mod 11 all match")

def legendre(p):
    v = pow(p, 5, 11)
    return 0 if p % 11 == 0 else (1 if v == 1 else -1)

bad = 0
for p in primes_upto(50000):
    pattern = all(pow(p, 5 * n, 11) == (1 if n % 2 == 0 else 10)
                  for n in range(8))
    if pattern != (legendre(p) == -1):
        bad += 1
        print("MISMATCH", p)
print(f"primes <= 50000: mismatches = {bad}")
# p = 11 edge: sequence 1,0,0,... not the pattern; not a nonresidue
assert [pow(11, 5 * n, 11) for n in range(4)] == [1, 0, 0, 0]
assert legendre(11) == 0
# OEIS prefix of A191060
pref = [p for p in primes_upto(120) if legendre(p) == -1]
print("A191060 prefix:", pref)
assert pref == [2, 7, 13, 17, 19, 29, 41, 43, 61, 73, 79, 83,
                101, 107, 109]
print("ALL CHECKS PASS")
