# A048715 = Detlefs's characterization

**Statement.** A048715 = {x : 7x = C(7, x)}, where C = A048720 is
carryless multiplication. Detlefs (Jun 08 2024, in the OEIS entry)
wrote that this sequence "appears to be" the set of x with
(x AND 5x) = x and (x OR 3x)/x = 3. This is true for all x ≥ 1
(x = 0 lies in A048715 but is excluded from Detlefs's condition by
the division by x).

**Proof.** Both sides equal the bit-triple condition "no two 1-bits
of x at distance 1 or 2", i.e. (x AND 2x) = 0 and (x AND 4x) = 0:
- 7x = C(7, x): since C(7, x) = x XOR 2x XOR 4x and
  a + b = (a XOR b) + 2(a AND b), the equality 7x = x + 2x + 4x =
  C(7, x) holds iff the two AND terms vanish, which is the
  bit-triple condition.
- Detlefs's side: (x OR 3x)/x = 3 (exact, x ≥ 1) iff x OR 3x = 3x iff
  (x AND 3x) = x; with 3x = x + 2x and the lemma
  a AND (a + b) = a ⟺ a AND b = 0, this is (x AND 2x) = 0.
  Likewise (x AND 5x) = x with 5x = x + 4x gives (x AND 4x) = 0.

**Files.**
- `A048715.lean` — self-contained Lean 4 formalization (Lean 4.36.0;
  compiles with no errors or warnings; the main equivalence depends
  on axioms [propext, Classical.choice, Quot.sound]).
- `a048715-verify.py` — independent verification by finite automata:
  brute-force agreement for x < 2^20 (2745 terms; the only difference
  is x = 0), a carry-automaton proof of the bridge characterization,
  and product automata proving (x AND 5x) = x ⟺ no distance-2 pair
  (12 states) and (x OR 3x) = 3x ⟺ no distance-1 pair (6 states).

**Attribution / priority note.** The bit-triple description of
A048715 itself is classical (recorded in the OEIS entry); what is
proved here is Detlefs's 2024 "appears to be" characterization. No
earlier proof of it was found (checked 2026-11-27). First published
proof and Lean formalization known to us.
