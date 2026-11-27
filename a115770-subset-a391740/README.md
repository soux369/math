# A115770 ⊆ A391740

**Statement.** A115770 = {k : 7k = C(11, k)} is a subset of
A391740 = {0} ∪ {k : C(m, k) = 5k for some m > 0},
where C = A048720 is carryless multiplication (multiplication in GF(2)[X]).

The OEIS cross-reference between these sequences recorded the inclusion only
"by conjecture". It follows from the implication

  7k = C(11, k) ⟹ 5k = C(13, k)   for all k,

with witness m = 13 (and 0 ∈ A391740 by definition).

**Proof.** (Carry, mask) state-pair binary induction over the 10 reachable
state pairs (c₇, m₁₁, c₅, m₁₃):

| State | (c₇, m₁₁) | (c₅, m₁₃) | Note |
|---|---|---|---|
| S₀ | (0, 0) | (0, 0) | accepting |
| S₁ | (3, 5) | (2, 6) | |
| S₂ | (1, 2) | (1, 3) | dead (parity mismatch) |
| S₃ | (5, 7) | (3, 5) | |
| S₄ | (2, 3) | (1, 2) | dead |
| S₅ | (6, 6) | (4, 4) | accepting |
| S₆ | (3, 3) | (2, 2) | accepting |
| S₇ | (1, 1) | (1, 1) | accepting |
| S₈ | (5, 4) | (3, 7) | dead |
| S₉ | (4, 5) | (3, 6) | dead |

In every reachable state, c₇ = m₁₁ implies c₅ = m₁₃, which closes the
induction. Full details are in the Lean file.

**Files.**
- `A115770_subset_A391740.lean` — self-contained Lean 4 formalization
  (Lean 4.36.0; compiles with no errors; the main theorem depends only on
  axioms [propext, Quot.sound]).
- `a115770-verify.py` — independent verification: BFS reproduction of the
  10-state automaton and brute force for k < 2^20 (1,999 terms of A115770,
  0 counterexamples).

**Attribution / priority note.** The underlying equivalence
7k = C(11, k) ⟺ 5k = C(13, k) was already proved in Lean by trureturing
(Omega Institute), so this inclusion was in principle already derivable.
The contribution here is a direct, self-contained proof of the inclusion
itself (10 state pairs) and its Lean formalization, which settles the
"by conjecture" note in the OEIS cross-references.
