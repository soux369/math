# A191059: Detlefs's Fibonacci characterization

**Statement.** A191059 is the sequence of primes p whose
Kronecker symbol (p|6) = (p|2)(p|3) equals -1. Detlefs
(May 26 2014, in the OEIS entry) wrote that these are the
primes p with (p mod 6) · (F(p) mod 6) = 5, where F is the
Fibonacci sequence. This is true — in fact the equivalence
holds for every natural number n, not only primes.

**Proof.** Both sides depend only on n mod 24: (n|2) depends
on n mod 8, (n|3) on n mod 3, and F(n) mod 6 has Pisano
period 24. Evaluating all 24 residue classes: the Kronecker
symbol is -1 exactly for n mod 24 ∈ {13, 17, 19, 23}, and
exactly for those classes is (n mod 6)(F(n) mod 6) = 5
(the classes {13, 19} give 1 · 5, the classes {17, 23} give
5 · 1; the other unit classes give products 1 and 25, and
the non-unit classes give symbol 0). Note the symbol is the
Kronecker symbol (p|6) = (-6|p), not the Jacobi symbol
(6|p); the two differ when p ≡ 3 (mod 4).

**Files.**
- `a191059-verify.py` — independent check: the Pisano table
  of F mod 6, the three-way equivalence (symbol = -1 ⟺
  n mod 24 ∈ {13, 17, 19, 23} ⟺ product = 5) for all
  n ≤ 5000, the prime equivalence for all primes ≤ 50,000
  (0 mismatches), and the OEIS prefix.

**Attribution / priority note.** What is settled here is
Detlefs's 2014 "appears"-style characterization in the OEIS
entry. No earlier proof of the comment was found
(checked 2026-11-27).
