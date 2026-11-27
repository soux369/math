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

## Conventions

- One folder per result, named after the statement.
- Every claim ships with machine-checkable evidence (Lean file and/or a
  verification script) and an explicit priority/attribution note.
- Notation: C(a, b) = A048720(a, b), carryless multiplication.
