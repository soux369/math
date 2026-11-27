# A080148: Detlefs's binomial characterization

**Statement.** A080148 is the sequence of positions of the primes
≡ 3 (mod 4) among all primes. Detlefs (Dec 06 2011, in the OEIS
entry) wrote that its terms "appear to be" exactly the indices k
for which binomial(prime(k), 3) is odd. This is true.

**Proof.** For every prime p, binomial(p, 3) is odd ⟺ p ≡ 3 (mod 4):
by Lucas's theorem modulo 2, binomial(p, 3) is odd iff every 1-bit
of 3 = 11₂ is a 1-bit of p, i.e. iff the two lowest binary digits of
p are both 1, i.e. iff p ≡ 3 (mod 4). (For p = 2 both sides fail:
binomial(2, 3) = 0.) Hence {k : binomial(prime(k), 3) odd} =
{k : prime(k) ≡ 3 (mod 4)} = A080148, as sets and therefore as
increasing enumerations.

**Files.**
- `a080148-verify.py` — exhaustive check for all 9,592 primes
  ≤ 100,000 (0 mismatches), the position-set identity, and the exact
  counts π(5000) = 669 with 339 primes ≡ 3 (mod 4) up to 5000.

**Attribution / priority note.** The underlying fact is a direct
corollary of Lucas's theorem; what is settled here is Detlefs's
2011 "appears" comment in the OEIS entry. No earlier proof of the
comment was found (checked 2026-11-27).
