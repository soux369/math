# A045468: Detlefs's mod-210 characterization

**Statement.** A045468 is the sequence of primes p with
p mod 5 ∈ {1, 4}. Detlefs (Dec 29 2011, in the OEIS entry)
characterized them as the primes p with p^6 mod 210 = 1.
This is true, for every prime p without exception.

**Proof.** By the Chinese remainder theorem across
210 = 2 · 3 · 5 · 7: for q ∈ {2, 3, 7}, n^6 ≡ 1 (mod q) iff
q ∤ n (since φ(q) divides 6), while n^6 ≡ 1 (mod 5) iff
n mod 5 ∈ {1, 4}. The prime divisors of 210 fail both sides
(2^6, 3^6, 5^6, 7^6 ≡ 64, 99, 85, 49 mod 210), and every
other prime is automatically coprime to 2, 3, 7, so
p^6 ≡ 1 (mod 210) reduces to the mod-5 condition. In fact,
for p > 7, p^6 mod 210 is 1 or 169 according as
p mod 5 ∈ {1, 4} or {2, 3}, and exactly 24 residue classes
modulo 210 satisfy r^6 ≡ 1.

**Files.**
- `a045468-verify.py` — independent check: the small-prime
  table and the r^6 mod q tables for q ∈ {2, 3, 5, 7}, and
  the equivalence verified for all primes ≤ 50,000
  (0 mismatches), with the OEIS prefix reproduced.

**Attribution / priority note.** What is settled here is
Detlefs's 2011 characterization in the OEIS entry. No earlier
proof of the comment was found (checked 2026-11-27).
