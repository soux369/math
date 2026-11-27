# A115807 ⊊ A048719

**Statement.** A115807 = {k : 15k = C(27, k)} is a proper subset of
A048719 = {k : 3k = C(7, k) and 5k = C(5, k)},
where C = A048720 is carryless multiplication (multiplication in GF(2)[X]).
The OEIS entry for A115807 recorded this only as a cross-reference
question ("Subset of A048719?").

**Proof.** (Carry, mask) state-pair binary induction on the product
automaton ((c15, d27), (c3, d7), (c5, d5)). From the initial state,
14 states are reachable under (15, 27) bit-matching: 7 live and 7 dead.
Six dead states fail by parity (c15 ≢ d27 mod 2, with 15 and 27 odd);
the seventh, (4, 6 | 0, 1 | 1, 1), fails at k = 0 and steps only into
parity-dead states. On every live state the conclusion pairs bit-match
for both bits of k, and the terminal implication holds: c15 = d27
implies c3 = d7 and c5 = d5. Strong induction on k then gives
15k = C(27, k) ⟹ 3k = C(7, k) ∧ 5k = C(5, k).
Strictness witness 99: 3·99 = C(7, 99) = 297 and 5·99 = C(5, 99) = 495,
but 15·99 = 1485 ≠ 1421 = C(27, 99).

**Files.**
- `A115807.lean` — self-contained Lean 4 formalization (Lean 4.36.0;
  compiles with no errors or warnings; the inclusion, the witness, and
  the strictness theorem each depend only on axioms
  [propext, Quot.sound]).
- `a115807-verify.py` — independent verification: BFS reproduction of
  the 14-state product automaton and its transitions, semantic
  state-level implication checks for k < 2^16, dead-state
  justifications, and brute-force inclusion for k < 2^20 (401 terms,
  0 violations).

**Attribution / priority note.** No earlier proof of this inclusion was
found (GitHub code search and the other 2026-11-27 publications in this
family were checked on 2026-11-27). First published proof and Lean
formalization known to us.
