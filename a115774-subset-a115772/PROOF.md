# Proof of A115774 ⊆ A115772

**Theorem.** For all `i ≥ 0`, `15i = C(23, i)` implies `13i = C(21, i)`, where `C`
is carryless (GF(2)[X]) multiplication (OEIS A048720). Moreover the inclusion is
strict, witnessed by `i = 15`.

## 1. The state machine for one equation

Fix odd `a, b` and process the bits of `i` from the LSB. After the low `t` bits
`u` of `i` have been processed, define

- carry: `c = ⌊a·u / 2^t⌋`
- mask: `m = ⌊C(b, u) / 2^t⌋`

Initially `(c, m) = (0, 0)`. On input bit `x ∈ {0, 1}` the next bit of `a·i` is
`(c + a·x) mod 2` and the next bit of `C(b, i)` is `(m ⊕ b·x) mod 2`. Since `a`
and `b` are odd, the two bits agree for either choice of `x` iff `c ≡ m (mod 2)`.
In that case the state updates to

```
c' = ⌊(c + a·x) / 2⌋,    m' = ⌊(m ⊕ (b·x)) / 2⌋.
```

If all bits match, then at the end (`t = L`, `u = i`) the equation `a·i = C(b, i)`
holds iff `c = m`.

## 2. The reachable state pairs

Run equation 1, `(a, b) = (15, 23)`, and equation 2, `(a, b) = (13, 21)`, in
lockstep on the same input bits. Starting from `((0,0), (0,0))` and following every
transition on which equation 1 does not break (parity condition `c₁ ≡ m₁ (mod 2)`),
exactly **14 state pairs** are reachable:

| ID | s₁ = (c₁, m₁) | s₂ = (c₂, m₂) | c₁≡m₁ (2) | c₂≡m₂ (2) | c₁=m₁ | c₂=m₂ | x=0 → | x=1 → |
|----|----|----|----|----|----|----|----|----|
| q₀ | (0, 0) | (0, 0) | ✓ | ✓ | ✓ | ✓ | q₀ | q₁ |
| q₁ | (7, 11) | (6, 10) | ✓ | ✓ | – | – | q₂ | q₃ |
| q₂ | (3, 5) | (3, 5) | ✓ | ✓ | – | – | q₄ | q₅ |
| q₃ | (11, 14) | (9, 15) | ✗ | ✓ | – | – | ⊥ | ⊥ |
| q₄ | (1, 2) | (1, 2) | ✗ | ✗ | – | – | ⊥ | ⊥ |
| q₅ | (9, 9) | (8, 8) | ✓ | ✓ | ✓ | ✓ | q₆ | q₇ |
| q₆ | (4, 4) | (4, 4) | ✓ | ✓ | ✓ | ✓ | q₈ | q₅ |
| q₇ | (12, 15) | (10, 14) | ✗ | ✓ | – | – | ⊥ | ⊥ |
| q₈ | (2, 2) | (2, 2) | ✓ | ✓ | ✓ | ✓ | q₉ | q₁₀ |
| q₉ | (1, 1) | (1, 1) | ✓ | ✓ | ✓ | ✓ | q₀ | q₁₁ |
| q₁₀ | (8, 10) | (7, 11) | ✓ | ✓ | – | – | q₁₂ | q₁₃ |
| q₁₁ | (8, 11) | (7, 10) | ✗ | ✗ | – | – | ⊥ | ⊥ |
| q₁₂ | (4, 5) | (3, 5) | ✗ | ✓ | – | – | ⊥ | ⊥ |
| q₁₃ | (11, 14) | (10, 15) | ✗ | ✗ | – | – | ⊥ | ⊥ |

(⊥ means equation 1's bit mismatches at that point regardless of the input bit,
so no `i` satisfying equation 1 ever continues from such a state.)

## 3. The two key observations

Reading the table:

- **Parity preservation.** In all 8 states where equation 1 can proceed
  (`c₁ ≡ m₁ (mod 2)`), equation 2 can also proceed (`c₂ ≡ m₂ (mod 2)`).
- **Terminal implication.** In all 14 states, `c₁ = m₁` implies `c₂ = m₂`
  (indeed on this reachable set the two equalities are equivalent).

## 4. Induction

Let `i = Σ x_t 2^t` satisfy `15i = C(23, i)`. We show by induction on `t` that
after `t` bits, both equations have matched on the low `t` bits and the joint
state is in the table. The base case is q₀. For the step: equation 1 matching
bit `t` forces `c₁ ≡ m₁ (mod 2)`, so the joint state is one of the 8 active
states; parity preservation gives `c₂ ≡ m₂ (mod 2)`, i.e. equation 2 also
matches bit `t`; and the table is closed under both bits, so the next joint
state is again in the table. At `t = L` the terminal condition for equation 1
gives `c₁ = m₁`, hence by the terminal implication `c₂ = m₂`, which is the
terminal condition for `13i = C(21, i)`. ∎

## 5. Strictness

`i = 15`: `13·15 = 195 = C(21, 15)`, while `15·15 = 225 ≠ 221 = C(23, 15)`.
So `15 ∈ A115772 ∖ A115774` and the inclusion is strict: **A115774 ⊊ A115772**.
