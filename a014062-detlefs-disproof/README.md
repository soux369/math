# A014062: Detlefs's conjecture is false

**Statement.** A014062 is a(n) = binomial(n², n). Detlefs
(Aug 06 2013, corrected by Marcus May 29 2015, in the OEIS entry)
conjectured that a(n) ≡ n (mod n³) only if n is 1, an odd prime,
the square of an odd prime, or the cube of an odd prime.
This is **false**: n = 16843⁴ = 80478114820849201 satisfies
a(n) ≡ n (mod n³).

**Proof.** By absorption, a(n) ≡ n (mod n³) ⟺
binomial(n²−1, n−1) ≡ 1 (mod n²). For n = p⁴ (p an odd prime),
writing each j ∈ [1, p⁴−1] uniquely as j = p^{4−s}·m with p ∤ m
gives the exact identity D·binomial(p⁸−1, p⁴−1) = N in ℤ, hence in
R = ℤ/p⁸ℤ, binomial(p⁸−1, p⁴−1) = Π (1 − p^{4+s} m^{−1}). All
cross terms vanish mod p⁸ (square-zero linearization), leaving
binomial(p⁸−1, p⁴−1) = 1 − Σ_s p^{4+s} S_s with
S_s = Σ_{m ∈ A_s} m^{−1}. The involution m ↦ p^s − m gives
2S_s = p^s Σ m^{−1}(p^s − m)^{−1}, killing all terms with s ≥ 2,
so binomial(p⁸−1, p⁴−1) = 1 − p⁶ Σ_{m=1}^{(p−1)/2} (m(p−m))^{−1}
in ℤ/p⁸ℤ. Therefore
  a(p⁴) ≡ p⁴ (mod p¹²) ⟺ Σ_{m=1}^{(p−1)/2} (m(p−m))^{−1} ≡ 0 (mod p²)
                         ⟺ H_{p−1} = Σ_{m=1}^{p−1} m^{−1} ≡ 0 (mod p³),
i.e. ⟺ p is a Wolstenholme prime. The prime p = 16843 is one:
Σ_{m=1}^{8421} (m(16843−m))^{−1} ≡ 0 (mod 16843²) (indeed
≡ 10083·16843² mod 16843³), H_{16842} ≡ 0 (mod 16843³), and
binomial(2p−1, p−1) ≡ 1 (mod p⁴). Hence n = 16843⁴ works, and
v₁₆₈₄₃(n) = 4 excludes it from Detlefs's list.

**Scope.** 16843 is the smallest Wolstenholme prime (no smaller odd
prime satisfies H_{p−1} ≡ 0 mod p³ — verified exhaustively), so this
is the smallest counterexample among prime fourth powers.
Minimality among all integers is open: composite n with at least
two distinct prime factors are excluded only up to n ≤ 20000
(filtered search); n ≤ 2000 is verified exhaustively here.

**Files.**
- `a014062-verify.py` — the arithmetic (n, n², n³), primality of
  16843, the decisive Wolstenholme sums at 16843 by direct modular
  computation (matching the claimed residues exactly), and the
  exhaustive check for n ≤ 2000 (319 hits; the non-prime hits are
  exactly 1, p² and p³ forms).
- `a014062-verify2.py` — end-to-end validation of the criterion:
  for p ∈ {3, 5, 7, 11, 13}, direct computation of
  binomial(p⁸, p⁴) mod p¹² agrees with the criterion, and the
  identity binomial(p⁸−1, p⁴−1) ≡ 1 − p⁶T ≡ 1 − p⁵H_{p−1}
  (mod p⁸) holds exactly; plus the exhaustive check that no odd
  prime below 16843 is Wolstenholme.

**Attribution / priority note.** That 16843 is a Wolstenholme prime
is classical; the equivalence a(p⁴) ≡ p⁴ (mod p¹²) ⟺ p
Wolstenholme, and hence the disproof of Detlefs's conjecture, are
published here for the first time as far as we know
(checked 2026-11-27).
