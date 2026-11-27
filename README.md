# Math

Proofs and formalizations of open problems, mostly around OEIS sequences and
carryless arithmetic (A048720). All results are independently verified:
each folder carries a Lean 4 formalization and/or a stand-alone verification
script whose output was reproduced independently of the proof's author.

## Results

### A115774 ⊊ A115772 — `a115774-subset-a115772/`
An inclusion recorded as an open question ("Subset of A115772?") in the OEIS
cross-references since 2006. Proved by a 14-state (carry, mask) state-pair
argument; strictness witness 15. Lean 4 formalization included.
*Priority note:* Blake Stone published the same result earlier on
2026-11-27 (GitHub, `blakestone-x/math`). This folder is an independent
derivation and the first Lean formalization.

### Detlefs's conjecture is false; A115772 ⊊ {x OR 4x} — `a115772-detlefs-conjecture/`
Detlefs (2010) suggested {i : 13i = C(21, i)} equals {x OR 4x : x ≥ 0}.
The equality is false: the smallest counterexample is 325 = 65 OR (4·65)
(13·325 = 4225 ≠ 4097 = C(21, 325)). The inclusion
A115772 ⊆ {x OR 4x} holds (24 state pairs). Lean 4 formalization included.
*Priority note:* Blake Stone published the same result, with a different
proof of the inclusion, earlier on 2026-11-27. Independent derivation +
first Lean formalization here.

### A115770 ⊆ A391740 — `a115770-subset-a391740/`
Settles a "by conjecture" cross-reference: 7k = C(11, k) implies
5k = C(13, k) (10 state pairs), hence every term of A115770 is in A391740
with witness m = 13. Lean 4 formalization included.
*Priority note:* the underlying equivalence was already Lean-proved by
trureturing; the contribution is the direct proof of the inclusion and
its formalization.

### A115801 ⊆ A391850 — `a115801-subset-a391850/`
Proved via the equivalence 9k = C(25, k) ⟺ 15k = C(19, k) (8 coupled live
state pairs), giving the inclusion with uniform witness m = 19.
Lean 4 formalization included.
*Priority note:* the equivalence had only been asserted in an unrefereed
note; first proof + formalization here, as far as we know.

### A115807 ⊊ A048719 — `a115807-subset-a048719/`
Settles the "Subset of A048719?" cross-reference question: 15k = C(27, k)
implies both 3k = C(7, k) and 5k = C(5, k) (14 product states, 7 live);
strictness witness 99. Lean 4 formalization included.
*Priority note:* no earlier proof found; first published proof and
formalization known to us (checked 2026-11-27).

### A115876 ⊊ A115874 — `a115876-subset-a115874/`
Settles the "Subset of A115874?" cross-reference question: 41k = C(105, k)
implies 19k = C(55, k) (40 parity-consistent states, 9 live coupled
pairs); strictness witness 31. Lean 4 formalization included.
*Priority note:* no earlier proof found; first published proof and
formalization known to us (checked 2026-11-27).

### A115805 ⊊ A115823 — `a115805-subset-a115823/`
Settles the "by conjecture" containment: 13k = C(29, k) implies
(8k) XOR (13k) = 21k, i.e. (8k) AND (13k) = 0 (13 dead + 6 trim state
pairs; a one-step lookahead is essential); strictness witness 5.
Lean 4 formalization included.
*Priority note:* no earlier proof found; first published proof and
formalization known to us (checked 2026-11-27).

### A048715 = Detlefs's characterization — `a048715-detlefs-characterization/`
Proves Detlefs's 2024 "appears to be" description of A048715:
7x = C(7, x) ⟺ (x AND 5x) = x and (x OR 3x)/x = 3, for x ≥ 1
(both sides equal the bit-triple condition). Lean 4 formalization
included.
*Priority note:* no earlier proof found; first published proof and
formalization known to us (checked 2026-11-27).

### A048719 ⊊ A115767 and A115768 = A115767 ∖ A048719 — `a048719-a115767-a115768/`
Settles the "(?)" in OEIS A115767: A048719 is a proper subset
(witness 11), and A115768 is exactly the difference. One-line
algebraic proof via C(7, k) = (2k) XOR C(5, k). Lean 4 formalization
included.
*Priority note:* no earlier proof found; first published proof and
formalization known to us (checked 2026-11-27).

### A080148: Detlefs's binomial characterization — `a080148-detlefs/`
Proves Detlefs's 2011 "appears" comment: the positions of the
primes ≡ 3 (mod 4) are exactly the indices k with
binomial(prime(k), 3) odd (one application of Lucas's theorem).
*Priority note:* no earlier proof found (checked 2026-11-27).

## Conventions

- One folder per result, named after the statement.
- Every claim ships with machine-checkable evidence (Lean file and/or a
  verification script) and an explicit priority/attribution note.
- Notation: C(a, b) = A048720(a, b), carryless multiplication.
