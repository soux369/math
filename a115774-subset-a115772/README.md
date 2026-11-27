# A115774 ⊊ A115772 — proof of an OEIS inclusion conjecture (Lean-verified)

**Theorem.** For every natural number `i`,

```
15 * i = C(23, i)   ⟹   13 * i = C(21, i)
```

where `C` is carryless (GF(2)[X]) multiplication ([OEIS A048720](https://oeis.org/A048720))
and the left-hand sides are ordinary integer products. In OEIS terms:

- [A115774](https://oeis.org/A115774) = { i : 15i = C(23, i) }
- [A115772](https://oeis.org/A115772) = { i : 13i = C(21, i) }
- **A115774 ⊆ A115772**, and the inclusion is **strict**: `15 ∈ A115772 ∖ A115774`
  (13·15 = 195 = C(21, 15), but 15·15 = 225 ≠ 221 = C(23, 15)).

The cross-references between these OEIS entries had carried this inclusion as an
open question since 2006.

## Proof

The proof uses the (carry, mask) state-pair method, the same technique used for
the sibling cases A115770, A115805 ⊆ A115803 and A115809 ⊆ A115801.

For an equation `a·i = C(b, i)` processed bit by bit from the LSB, keep the state
`(c, m)` with `c = ⌊a·u / 2^t⌋` and `m = ⌊C(b, u) / 2^t⌋` after the low `t` bits `u`
of `i`. A bit can match only when `c ≡ m (mod 2)`, and the state then updates as
`c' = ⌊(c + a·x)/2⌋`, `m' = ⌊(m ⊕ b·x)/2⌋`. The equation holds iff the final state
satisfies `c = m`.

Running both equations in lockstep from `((0,0), (0,0))`, exactly **14 state pairs**
are reachable, and the set is closed under both input bits. On every reachable pair,
`c₁ = m₁` implies `c₂ = m₂`, and parity-validity of equation 1 implies
parity-validity of equation 2. Binary induction over the bits of `i` then gives the
inclusion. See `PROOF.md` for the full state table.

## Verification

Two independent layers:

1. **Lean 4 formalization** — `A115774SubsetA115772.lean`, pure Lean 4.36.0
   (standard library only, no Mathlib). Compile it yourself:

   ```sh
   lean A115774SubsetA115772.lean
   ```

   It checks with no errors and no `sorry`; `#print axioms` reports only the
   standard axioms `[propext, Classical.choice, Quot.sound]` for the main theorem.

2. **Independent recomputation** — `verify.py` re-derives the reachable state-pair
   set by BFS from the definitions (it does not copy the proof's table), compares
   it against the 14 pairs used in the proof, checks the parity/terminal
   implications, and brute-forces the inclusion for all `i < 2^20`
   (459 members of A115774, no counterexample; the member list matches the OEIS
   prefix exactly).

   ```sh
   python3 verify.py
   ```

## Prior work / independent discovery

Independently, Blake Stone published a proof of this inclusion (and of
A115772 ⊊ {x OR 4x}) earlier the same day, on 2026-11-27 (committed 03:53 UTC):
[Two strict containments for ordinary and carryless binary products](https://github.com/blakestone-x/math/blob/main/A115772/README.md).
The 14-state table there agrees with the one here pair for pair, and the
strictness witness (15) is the same. The work in this repository was carried
out without knowledge of Stone's note; the agreement was noticed only after
both were public, and it serves as a strong cross-check. This repository's
contribution is the Lean 4 formalization of the result.

## Provenance

The proof and the Lean formalization were produced by an AI agent
(Gemini 4 Neon, task mode) working from a brief by MONO; the state-pair closure,
the numeric checks, and the Lean compilation reported above were independently
reproduced and verified by a second AI agent (Muse) before publication.
The mathematical claim stands on the Lean kernel check and the independent
recomputation, not on either agent's say-so.

## Files

- `A115774SubsetA115772.lean` — the Lean 4 proof (main theorem + strictness).
- `verify.py` — independent BFS / brute-force verifier.
- `PROOF.md` — human-readable proof with the full 14-state table.
