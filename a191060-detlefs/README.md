# A191060: Detlefs's period-2 characterization

**Statement.** A191060 is the sequence of primes that are quadratic
nonresidues modulo 11 (equivalently, primes p with
p mod 11 ∈ {2, 6, 7, 8, 10}). Detlefs (May 18 2014, in the OEIS
entry) wrote: "It appears that these are the primes p such that
the sequence p^(5n) mod 11 has period length 2, repeating [1, 10]."
This is true, for every prime p without exception.

**Proof.** Let c = (p mod 11)^5 mod 11. The sequence
a_p(n) = p^(5n) mod 11 satisfies a_p(0) = 1 and
a_p(n+1) = (a_p(n) · c) mod 11. Checking all 11 residue classes
(equivalently, Euler's criterion modulo 11): c = 10 exactly for
the nonresidues {2, 6, 7, 8, 10}, giving a_p(2k) = 1,
a_p(2k+1) = 10 — minimal period 2, repeating [1, 10]; c = 1 for
the nonzero residues {1, 3, 4, 5, 9}, giving the constant
sequence (1, 1, 1, ...); and c = 0 for p = 11, giving
(1, 0, 0, ...), which is not purely periodic. The equivalence is
robust: it holds under the minimal-period, eventual-period, and
1-based-indexing readings of Detlefs's wording alike.

**Files.**
- `a191060-verify.py` — independent check: the squaring and
  fifth-power tables modulo 11 (including the exact decompositions
  r^5 = 11q + c), and the equivalence verified for all primes
  ≤ 50,000 (0 mismatches), with the OEIS prefix reproduced.

**Attribution / priority note.** The underlying fact is Euler's
criterion modulo 11; what is settled here is Detlefs's 2014
"appears" comment in the OEIS entry. No earlier proof of the
comment was found (checked 2026-11-27).
