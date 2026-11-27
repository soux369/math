# A115801 ⊆ A391850

**Statement.** A115801 = {k : 9k = C(25, k)} is a subset of
A391850 = {0} ∪ {k > 0 : C(m, k) = 15k for some m > 0},
where C = A048720 is carryless multiplication (multiplication in GF(2)[X]).

**Proof.** Via the equivalence

  9k = C(25, k) ⟺ 15k = C(19, k)   for all k,

so every k ∈ A115801 with k > 0 lies in A391850 with uniform witness
m = 19 (and 0 is in A391850 by definition). The equivalence is proved by
(carry, mask) state-pair binary induction: the equation (9, 25) has 24
reachable states (8 live, 16 dead), the equation (15, 19) has 14
(8 live, 6 dead — all immediate parity dead-ends), and the 8 coupled
live pairs have matching acceptance (c = r) and transitions that either
stay inside the live pairs or fall simultaneously into dead states on
both sides.

**Files.**
- `A115801_subset_A391850.lean` — self-contained Lean 4 formalization
  (Lean 4.36.0; compiles with no errors; both the equivalence and the
  inclusion depend only on axioms [propext, Quot.sound]).
- `a115801-verify.py` — independent verification: BFS reproduction of
  both automata and of the coupled live pairs, semantic dead-state
  checks, and brute-force set equality for k < 2^20 (650 terms).

**Attribution / priority note.** The equivalence above had previously
been asserted without proof in an unrefereed note; the OEIS entry for
A391850 recorded the connection only implicitly. This folder gives the
first published proof and Lean formalization known to us.
