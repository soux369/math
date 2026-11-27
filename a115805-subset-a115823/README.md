# A115805 ⊊ A115823

**Statement.** A115805 = {k : 13k = C(29, k)} is a proper subset of
A115823 = {k : (8k) XOR (13k) = 21k},
where C = A048720 is carryless multiplication (multiplication in GF(2)[X]).
The OEIS entries recorded this only as "by conjecture" / "seems to be
a superset". Since 8k + 13k = 21k, the conclusion is equivalent to
(8k) AND (13k) = 0.

**Proof.** (Carry, mask) state-pair induction on the hypothesis
13k + c = C(29, k) XOR p, tracking also the carry c8 of the 8k side.
Of the reachable states, 13 are dead (the equation is unsatisfiable
from them for every k, by parity and one-step arguments) and 6 are
"trim" states (c, p, c8) ∈ {(0,0,0), (6,14,4), (9,9,6), (4,4,3),
(2,2,1), (1,1,0)}, on which (8k + c8) AND (13k + c) = 0 is proved by
strong induction: the lowest bits never conflict, and every step stays
inside the trim states or falls into a dead state. Note that the
no-conflict property is not a purely local consequence of the
hypothesis at a single bit position — a one-step lookahead (the trim /
dead distinction) is essential. Strictness witness 5:
(8·5) XOR (13·5) = 40 XOR 65 = 105 = 21·5, but 13·5 = 65 ≠ 105 = C(29, 5).

**Files.**
- `A115805_sub_A115823.lean` — self-contained Lean 4 formalization
  (Lean 4.36.0; compiles with no errors or warnings; the inclusion
  depends on axioms [propext, Classical.choice, Quot.sound], the
  strictness witness on [propext, Quot.sound]).
- `a115805-verify.py` — independent verification via a different
  formulation (bitwise automaton for the hypothesis with carry and a
  4-bit window): 19 reachable states, of which 6 are viable
  (backwards-reachable to the initial state); the 4 reachable
  transitions where the two conclusion bits collide all lead to
  non-viable states, so no valid k can use one. Also brute-force
  inclusion for k < 2^20 (196 terms, 0 violations).

**Attribution / priority note.** No earlier proof of this inclusion was
found (GitHub code search and the other 2026-11-27 publications in this
family were checked on 2026-11-27; trureturing's note on A115805
concerns a different containment, in A115803). First published proof
and Lean formalization known to us.
