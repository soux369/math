# Detlefs's Möbius-iteration identities (A003462, A007051, A168607, A152011)

Four claims of Gary Detlefs (OEIS comments, Nov 16 2010), all of the
shape: a first-order rational (Möbius) iteration s(n) has the closed
form s(n) = a(n)/(a(n) + c). **All four are true**, in the stated
domains — and (iii) in fact holds for all n ≥ 1.

| # | Sequence | a(n) | Iteration | Claim |
|---|----------|------|-----------|-------|
| (i) | A003462 | (3^n − 1)/2 | s(0) = 0, s(n) = (2s(n−1)+1)/(s(n−1)+2) | s(n) = a(n)/(a(n)+1), n ≥ 0 |
| (ii) | A007051 | (3^n + 1)/2 | s(1) = 2, same recurrence | s(n) = a(n)/(a(n)−1), n ≥ 1 |
| (iii) | A168607 | 3^n + 2 | s(1) = 5, same recurrence | s(n) = a(n)/(a(n)−4), n > 1 (indeed n ≥ 1) |
| (iv) | A152011 | (3^n − (−1)^n)/2 (n ≥ 1; a(0) = 1) | s(1) = 2, s(n) = (s(n−1)+2)/(2s(n−1)+1) | s(n) = a(n)/(a(n)+(−1)^n), n ≥ 1 |

## Proof

The two recurrences are the Möbius maps of the matrices
M₊ = [[2, 1], [1, 2]] (eigenvalues 3, 1) and M₋ = [[1, 2], [2, 1]]
(eigenvalues 3, −1), whose powers have the closed forms

    M₊^k = (1/2) [[3^k + 1, 3^k − 1], [3^k − 1, 3^k + 1]],
    M₋^k = (1/2) [[3^k + (−1)^k, 3^k − (−1)^k],
                  [3^k − (−1)^k, 3^k + (−1)^k]].

Applying M₊^{n−1} resp. M₋^{n−1} to the initial vector (p; q) with
p/q = s(1) gives (p_n; q_n) = (a(n); a(n) + c) with q_n ≥ 1 > 0 at
every step, which proves each identity; equivalently, each follows
by a one-step induction from a(n+1) = 3a(n) + d with
d = 1, −1, −4, 2(−1)^n respectively.

## Verification

`verify.py` recomputes all four identities in exact rational
arithmetic for n = 0..30 in claim (i) and n = 1..30 in claims
(ii)–(iv) (0 mismatches) and checks the closed
forms against the OEIS term lists. The proofs were also read and
checked line by line independently of the proving system.

*Priority note:* no earlier proof found (checked 2026-11-27).
First published proof known to us.
