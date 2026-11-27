# A048719 ⊊ A115767, and A115768 = A115767 ∖ A048719

**Statement.** A048719 = {k : 3k = C(7, k) and 5k = C(5, k)},
A115767 = {k : (2k) XOR (5k) = 3k}, and A115768 is the subsequence of
A115767 defined by (4k) XOR k ≠ 5k, where C = A048720 is carryless
multiplication. The OEIS entry for A115767 recorded A048719 as a
superset relation and the terms of A115768 as the "(?)" terms of
A115767 not in A048719. Both are now settled: the inclusion is proper
(smallest witness 11), and A115768 is *exactly* the difference.

**Proof.** One algebraic identity does everything: carryless
multiplication distributes over XOR in the left argument, and
7 = 2 XOR 5 as polynomials, so
C(7, k) = (2k) XOR C(5, k), while C(5, k) = (4k) XOR k.
- Inclusion: if 5k = C(5, k) and 3k = C(7, k), then
  (2k) XOR (5k) = (2k) XOR C(5, k) = C(7, k) = 3k.
- Difference: for k ∈ A115767, k ∈ A048719 ⟺ (4k) XOR k = 5k.
  (⇒) (4k) XOR k = C(5, k) = 5k. (⇐) (4k) XOR k = 5k gives
  5k = C(5, k), and then C(7, k) = (2k) XOR C(5, k) = (2k) XOR 5k
  = 3k by the A115767 assumption. Hence the terms of A115767 failing
  (4k) XOR k = 5k — exactly A115768 — are exactly A115767 ∖ A048719.
- Witness 11: (2·11) XOR (5·11) = 22 XOR 55 = 33 = 3·11, but
  C(7, 11) = 49 ≠ 33, so 11 ∉ A048719.

**Files.**
- `a048719_proof.lean` — self-contained Lean 4 formalization of the
  algebraic proof (Lean 4.36.0; compiles with no errors or warnings;
  all theorems depend only on axioms [propext, Quot.sound]).
- `a048719-verify.py` — independent verification by brute force
  (k < 2^20: |A048719| = 657, |A115767| = 3553, |A115768| = 2896,
  exact difference equality) and by product automata (carries of
  k + 2k and k + 4k) for the two implications.

**Attribution / priority note.** No earlier proof was found (checked
2026-11-27). First published proof and Lean formalization known to us.
