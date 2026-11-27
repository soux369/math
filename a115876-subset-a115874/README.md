# A115876 ⊊ A115874

**Statement.** A115876 = {k : 41k = C(105, k)} is a proper subset of
A115874 = {k : 19k = C(55, k)},
where C = A048720 is carryless multiplication (multiplication in GF(2)[X]).
The OEIS entries recorded this only as cross-reference questions
("Subset of A115874?" / "Superset of A115876?").

**Proof.** (Carry, mask) state-pair binary induction. The automaton for
(41, 105) has 40 parity-consistent reachable states: 9 live and 31 dead.
Every dead state has c ≠ m and steps, on both input bits, only into
dead states or parity mismatch (c ≢ m mod 2, impossible for odd
multipliers), so no dead state satisfies its equation for any k.
The 9 live states couple uniquely to states of the (19, 55) automaton,
forming a single cycle; every coupled transition either stays in the
coupled live pairs or sends the (41, 105) side into a dead/parity state,
and the terminal implication c1 = m1 ⟹ c2 = m2 holds on all 9 pairs.
Strong induction on k gives 41k = C(105, k) ⟹ 19k = C(55, k).
Strictness witness 31: 19·31 = C(55, 31) = 589, but
41·31 = 1271 ≠ 1223 = C(105, 31).

**Files.**
- `A115876_subset_A115874.lean` — self-contained Lean 4 formalization
  (Lean 4.36.0; compiles with no errors or warnings; the inclusion
  depends on axioms [propext, Classical.choice, Quot.sound], the
  strictness witness on [propext]).
- `a115876-verify.py` — independent verification: BFS reproduction of
  the 40 reachable states and the 9/31 live/dead split, dead-closure
  and coupled-transition checks, semantic implication checks for
  k < 2^15, and brute-force inclusion for k < 2^20 (64 terms,
  0 violations).

**Attribution / priority note.** No earlier proof of this inclusion was
found (GitHub code search and the other 2026-11-27 publications in this
family were checked on 2026-11-27). First published proof and Lean
formalization known to us.
