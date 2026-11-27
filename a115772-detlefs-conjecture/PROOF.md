# Detlefs's conjecture on A115772 is false: A115772 ⊊ { x OR 4x }

## Statement

Let C be carryless (GF(2)[X]) multiplication (OEIS A048720) and
A115772 = { i : 13i = C(21, i) } (ordinary product on the left).
Detlefs (2010, comment in OEIS A115772) conjectured

```
A115772 = { x OR 4x : x ≥ 0 }        (bitwise OR; 4x = x << 2).
```

**Theorem.** A115772 ⊊ { x OR 4x : x ≥ 0 }: the inclusion ⊆ holds, but the
equality fails, first at i = 325.

## Disproof of equality

Take x = 65 = 1000001₂. Then 4x = 260 = 100000100₂ and

```
i = x OR 4x = 101000101₂ = 325 ∈ { x OR 4x }.
```

But 325 = 5·(2⁶ + 1) and 13·5 = 65 = 2⁶ + 1, so as integers
13·325 = (2⁶ + 1)² = 2¹² + 2⁷ + 1 = 4225, whereas in GF(2)[X]
(with 21 = 1 + X² + X⁴ and 325 = (1 + X²)(1 + X⁶)) the cross terms cancel:

```
C(21, 325) = (1 + X² + X⁴)(1 + X²)(1 + X⁶) = (1 + X⁶)² = 1 + X¹² = 4097.
```

Hence 13·325 = 4225 ≠ 4097 = C(21, 325), so 325 ∉ A115772. A direct check shows
the two sets coincide for all i < 325, so 325 is the smallest counterexample
(the next ones are 335, 365, 367, 485, …).

## Proof of the inclusion

For the equation 13i = C(21, i) use the suffix state equation
E(c, m, i) ⟺ c + 13i = m ⊕ C(21, i), with E(c, m, 0) ⟺ c = m. Splitting off the
LSB b of i (13 and 21 are odd) gives

```
E(c, m, i) ⟺ (c ≡ m mod 2) ∧ E(δ_eq((c,m), b), ⌊i/2⌋),
δ_eq((c,m), b) = (⌊(c + 13b)/2⌋, ⌊(m ⊕ 21b)/2⌋).
```

For the right-hand side, bit j of x OR 4x is i_j = x_j ∨ x_{j-2}; the subset DFA
over NFA states (x_{j-2}, x_{j-1}) ∈ {0,1}² has transition
δ_DFA(S, b) = { (b₁, x_j) : ∃b₀, (b₀, b₁) ∈ S ∧ (x_j ∨ b₀) = b }.

Starting from ((0,0), {00}) and following transitions that keep c ≡ m (mod 2),
exactly **24 pairs** ((c, m), S) are reachable: 16 with c ≡ m (mod 2) and 8
boundary pairs with c ≢ m (mod 2). The full table is in the Lean file
(`R_list`) and is recomputed independently by `verify.py`. On all 24 pairs:

1. **Closure:** if c ≡ m (mod 2), then for both bits b,
   (δ_eq((c,m), b), δ_DFA(S, b)) is again in the relation.
2. **Terminal implication:** c = m implies (0,0) ∈ S.

A binary induction on i (strong induction, peeling the LSB and reconstructing
the witness x bit by bit via the DFA predecessor) then shows: whenever
E(c, m, i) holds for a pair in the relation, some (b₀, b₁) ∈ S has
i = x OR 4x OR b₀ OR 2b₁ for some x. Applied to the initial pair ((0,0), {00}),
every i ∈ A115772 is of the form x OR 4x. ∎

Combined with the counterexample: **A115772 ⊊ { x OR 4x : x ≥ 0 }**.
