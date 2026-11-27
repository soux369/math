# A067793: Detlefs's claim is false — disproof and corrected picture

**Statement.** A067793 = {nonprime n : φ(n) > 2n/3}. Detlefs
(Nov 16 2011, in the OEIS entry) claimed these are the composite n
with S(n) = Σ_{k≤n} k² = n(n+1)(2n+1)/6 ≡ 0 (mod n). The claimed
equality is **false**, but the inclusion A067793 ⊊ {n : S(n) ≡ 0
(mod n)} holds.

**Disproof.** n = 385 = 5·7·11: S(385) = 19,096,385 = 385 × 49,601,
so S(385) ≡ 0 (mod 385); but φ(385) = 240 < 770/3 = 2·385/3, so
385 ∉ A067793.

**Corrected characterizations.**
- S(n) ≡ 0 (mod n) ⟺ gcd(n, 6) = 1. (Since S(n)/n = (n+1)(2n+1)/6,
  the condition is 6 | (n+1)(2n+1), which holds iff n is odd and
  3 ∤ n.)
- φ(n) > 2n/3 ⟺ Π_{p | n} (1 − 1/p) > 2/3, the product over distinct
  prime divisors. In particular gcd(n, 6) = 1 is necessary (a factor
  2 or 3 already makes the product ≤ 2/3), which gives the inclusion;
  it is proper exactly at the n coprime to 6 with product ≤ 2/3
  (smallest: 385, then 455, 595, 665, 805, …).
- There is **no bound** on the number of distinct prime factors:
  prime powers and products of two distinct primes ≥ 5 always
  qualify, three distinct primes qualify iff the product exceeds
  2/3 (smallest example 715 = 5·11·13, φ(715) = 480 > 1430/3), and
  four or more can qualify with large primes (smallest example
  17017 = 7·11·13·17).

**Files.**
- `a067793-verify.py` — exact-arithmetic verification: the S-set
  characterization for n ≤ 100,000; the product characterization and
  the one-directional mismatch count for nonprime n ≤ 200,000
  (799 cases with S true but φ false, 0 in reverse, smallest 385);
  minimality of 715; the OEIS prefix.

**Attribution / priority note.** The disproof and corrected
characterizations are published here for the first time as far as we
know (checked 2026-11-27).
