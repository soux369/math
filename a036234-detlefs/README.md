# A036234: Detlefs's two binomial claims

**Statement.** A036234 is a(n) = π(n) + 1 (the number of primes ≤ n,
with 1 counted as a prime). Detlefs (Aug 05 2013, in the OEIS entry)
claimed:
1. a(k) = min{ i : binomial(k·prime(i), prime(i)) mod prime(i) = k }.
2. For k ≥ 2, binomial(k·q, q) mod q = 0 ⟺ k is prime, where
   q = prime(a(k) − 1) is the largest prime ≤ k.

Both claims are true.

**Proof.** By Lucas's theorem, binomial(kp, p) ≡ k (mod p) for prime
p (in base p, kp has digits (0, k₀, k₁, …) and p has digits (0, 1),
so the congruence picks out k mod p). Since the residue
binomial(kp, p) mod p lies in {0, …, p−1}, for k ≥ 1 it equals k
itself iff p > k. Hence the indices in claim 1 are exactly
{i : prime(i) > k}, whose minimum is π(k) + 1 = a(k). For claim 2,
binomial(kq, q) mod q = k mod q, and k mod q = 0 with q the largest
prime ≤ k forces k = q: otherwise q | k and q < k give k ≥ 2q, and
Bertrand's postulate supplies a prime strictly between q and 2q ≤ k,
contradicting the maximality of q. So the residue is 0 iff k = q,
i.e. iff k is prime.

**Files.**
- `a036234-verify.py` — exact-computation checks: the Lucas
  congruence for k < 60 over the first 25 primes, claim 1 for
  k < 300, claim 2 for 2 ≤ k < 2000 (0 mismatches throughout).

**Attribution / priority note.** What is settled here is Detlefs's
2013 comment in the OEIS entry; the proof cites Lucas's theorem and
Bertrand's postulate, both standard. No earlier proof of the comment
was found (checked 2026-11-27).
