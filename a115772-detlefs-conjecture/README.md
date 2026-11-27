# A115772 ⊊ { x OR 4x } — Detlefs's 2010 conjecture is false

**Result.** Let A115772 = { i : 13i = C(21, i) }, where C is carryless
(GF(2)[X]) multiplication ([OEIS A048720](https://oeis.org/A048720)) and the
left-hand side is the ordinary integer product.

Gary Detlefs conjectured in 2010 (comment in [OEIS A115772](https://oeis.org/A115772))
that A115772 "appears to be" the set of all `i` expressible as `x OR 4x`
(bitwise OR) for some `x ≥ 0`.

The equality is **false**. The correct statement is the strict inclusion

```
A115772 ⊊ { x OR 4x : x ≥ 0 }.
```

- **Inclusion (true):** every `i` with `13i = C(21, i)` has the form `x OR 4x`.
- **Strictness:** the smallest counterexample to the reverse inclusion is
  `i = 325 = 65 OR (4·65)`, but `13·325 = 4225 ≠ 4097 = C(21, 325)`,
  so `325 ∉ A115772`. The two sets agree below 325; the next counterexamples
  are 335, 365, 367, 485, …

## Proof outline

The inclusion is proved by a finite state-pair relation between

- the (carry, mask) automaton of the equation `13i = C(21, i)` (states
  `(c, m)`, bit transition `c' = ⌊(c + 13x)/2⌋`, `m' = ⌊(m ⊕ 21x)/2⌋`,
  terminal condition `c = m`), and
- the subset DFA of the property `i = x OR 4x` (NFA states `(x_{j-2}, x_{j-1})`,
  determinized by subsets).

Exactly **24 state pairs** are reachable from the initial pair; the relation is
closed under both input bits, and on every reachable pair `c = m` implies the
DFA component accepts. Binary induction finishes the proof. The disproof is
the explicit counterexample above. See `PROOF.md` for details.

## Verification

1. **Lean 4 formalization** — `A115772Detlefs.lean`, pure Lean 4.36.0
   (standard library only, no Mathlib):

   ```sh
   lean A115772Detlefs.lean
   ```

   Checks with no errors and no `sorry`. `#print axioms`:
   `a115772_subset_or4x` → [propext, Classical.choice, Quot.sound];
   `detlefs_conjecture_false` → [propext, Quot.sound].

2. **Independent recomputation** — `verify.py` recomputes the 24-pair reachable
   set by BFS from the definitions, checks the terminal implication, verifies
   the counterexample and its minimality, and brute-forces the inclusion for
   all `i < 2^20`:

   ```sh
   python3 verify.py
   ```

## Prior work / independent discovery

Independently, Blake Stone published a proof of this strict inclusion
earlier the same day, on 2026-11-27 (committed 03:53 UTC):
[Two strict containments for ordinary and carryless binary products](https://github.com/blakestone-x/math/blob/main/A115772/README.md).
Stone's proof of the inclusion uses a different argument (a bitwise-majority
/ track argument, which also generalizes to all strides), and the same
counterexample 325. The work in this repository was carried out without
knowledge of Stone's note; the agreement was noticed only after both were
public, and it serves as a strong cross-check. This repository's
contribution is the automaton-based proof and its Lean 4 formalization.

## Provenance

The proof, the counterexample search and the Lean formalization were produced
by an AI agent (Gemini 4 Neon, task mode) working from a brief by MONO; the
state-pair closure, the numeric checks, and the Lean compilation reported
above were independently reproduced and verified by a second AI agent
(Muse) before publication.

## Files

- `A115772Detlefs.lean` — Lean 4 proof (inclusion, disproof of equality, strictness).
- `verify.py` — independent BFS / brute-force verifier.
- `PROOF.md` — human-readable outline.
- `proof.pdf` — proof note (A4).
