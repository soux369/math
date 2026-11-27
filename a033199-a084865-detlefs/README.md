# A033199 + A084865: Detlefs's Fibonacci characterizations

**Statement.** Detlefs (May 26 2014, in the OEIS entries) claimed:
- A033199 (primes of the form x² + 6y²): p is a term ⟺
  p mod 6 = 1 and Fib(p) mod 6 = 1.
- A084865 (primes of the form 2x² + 3y²): for p > 3, p is a term ⟺
  (p mod 6)·(Fib(p) mod 6) = 25; the primes 2 and 3 are terms but
  are exceptions to the Fibonacci condition.

Both claims are true.

**Proof.** The Fibonacci sequence mod 6 has Pisano period 24, so
Fib(p) mod 6 depends only on p mod 24; the table gives
Fib(p) mod 6 = 1 exactly at residues {1, 2, 7, 10, 17, 23} and
Fib(p) mod 6 = 5 exactly at residues {5, 11, 13, 19, 22}.
Intersecting with p mod 6 = 1 (residues {1, 7, 13, 19} mod 24) leaves
{1, 7}; intersecting p mod 6 = 5 (residues {5, 11, 17, 23}) with the
Fib ≡ 5 set leaves {5, 11} (the product (p mod 6)·(Fib(p) mod 6)
equals 25 iff both factors are 5). By the classical criteria for
discriminant −24 (Cox, *Primes of the Form x² + ny²*, cited — not
reproved here), for p > 3: p = x² + 6y² ⟺ p ≡ 1, 7 (mod 24) and
p = 2x² + 3y² ⟺ p ≡ 5, 11 (mod 24). This proves both claims for
p > 3; for p = 2, 3 both sides of the A033199 claim are false, and
2 = 2·1² + 3·0², 3 = 2·0² + 3·1² are the stated A084865 exceptions
(their products are 2 and 6, not 25).

**Files.**
- `a033199-a084865-verify.py` — verification for all 5,133 primes
  ≤ 50,000: the Pisano table; both Cox criteria by direct
  representation search (0 mismatches); both Detlefs equivalences
  (0 mismatches, exceptions exactly {2, 3}); the OEIS prefixes.

**Attribution / priority note.** What is settled here is Detlefs's
2014 comment in the two OEIS entries; the proof cites Cox's
classical form criteria. No earlier proof of the comment was found
(checked 2026-11-27).
