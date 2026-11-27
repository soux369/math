# A019335: Detlefs's primitive-root characterization

Gary Detlefs (OEIS A019335 comment, May 21 2014) claimed:

- **(a)** For every integer k ≥ 2, the sequence (5^n mod k)_{n ≥ 0}
  has exact period k − 1 if and only if k is a prime with
  primitive root 5 (i.e. k ∈ A019335).
- **(b)** Every such prime satisfies p ≡ 2 or 3 (mod 5).

**Both parts are true.** Part (a) holds identically for pure and
for eventual periodicity, and for the 1-indexed sequence as well.

## Proof

Write the analysis by gcd(5, k):

- If gcd(5, k) = 1, the sequence is purely periodic with exact
  period ord_k(5), which divides φ(k) ≤ k − 1. Period k − 1
  therefore forces ord_k(5) = φ(k) = k − 1, and φ(k) = k − 1
  holds iff k is prime.
- If 5 | k, write k = 5^e·m with e ≥ 1 and gcd(5, m) = 1. The
  sequence is not purely periodic (a_0 = 1 ≢ 0 ≡ a_T (mod 5) for
  every T ≥ 1); by CRT its exact preperiod is e and its exact
  eventual period is ord_m(5) < k − 1. In particular the
  sequence is eventually 0 only when m = 1 (k = 5^e) — e.g.
  k = 10 gives 1, 5, 5, … and k = 15 gives 1, 5, 10, 5, 10, ….
- For (b): if p ≡ ±1 (mod 5) then (5|p) = (p|5) = +1 by
  quadratic reciprocity, so 5 is a quadratic residue mod p and
  ord_p(5) divides (p − 1)/2 < p − 1; p = 5 is excluded by
  gcd(5, p) = 1. Hence p ≡ 2 or 3 (mod 5). The condition is
  not sufficient: ord_13(5) = 4 and ord_67(5) = 22.

## Verification

`verify.py` checks, for all k < 3000, that
{k : ord_k(5) = k − 1} is exactly the set of primes with
primitive root 5 (181 values, k = 2 included), all of them
≡ 2, 3 (mod 5). The proof was read line by line, including its
explicit table for 19 values of k (spot-checked: k = 9, 11,
13, 14, 15, 17, 19, 23, 25, 75 all agree with direct
computation).

*Priority note:* no earlier proof found (checked 2026-11-27).
First published proof known to us.
