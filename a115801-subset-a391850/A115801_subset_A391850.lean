/-
  Formal proof in Lean 4 (zero external dependencies) that
    A115801 ⊆ A391850
  via the bi-implication
    ∀ k : Nat, 9 * k = clmul 25 k ↔ 15 * k = clmul 19 k
  using the (carry, mask) state-pair / strong binary-induction method.

  Definitions (matching OEIS A048720, A115801, A391850, A280500):
  - clmul a k = A048720(a, k), carryless base-2 multiplication.
  - inA115801 k := 9 * k = clmul 25 k.
  - inA391850 k := k = 0 ∨ (k > 0 ∧ ∃ m : Nat, m > 0 ∧ clmul m k = 15 * k).
-/

namespace A115801SubsetA391850

/-- Carryless multiplication A048720(a, k) defined by binary recursion on k. -/
def clmul (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let half := clmul a ((k + 1) / 2)
    if (k + 1) % 2 = 1 then (2 * half) ^^^ a else 2 * half

theorem clmul_zero (a : Nat) : clmul a 0 = 0 := by
  rw [clmul]

theorem clmul_even (a q : Nat) : clmul a (2 * q) = 2 * clmul a q := by
  cases q with
  | zero => simp [clmul_zero]
  | succ q' =>
    have hpos : 2 * (q' + 1) = (2 * q' + 1) + 1 := by omega
    rw [hpos, clmul]
    have hdiv : ((2 * q' + 1) + 1) / 2 = q' + 1 := by omega
    have hmod : ((2 * q' + 1) + 1) % 2 = 0 := by omega
    rw [hdiv, hmod]
    simp

theorem clmul_odd (a q : Nat) : clmul a (2 * q + 1) = (2 * clmul a q) ^^^ a := by
  rw [clmul]
  have hdiv : (2 * q + 1) / 2 = q := by omega
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  rw [hdiv, hmod]
  simp

/-- Bit-level arithmetic helpers for splitting equations into mod 2 and div 2. -/
private theorem eq_iff_mod_div (x y : Nat) : x = y ↔ x % 2 = y % 2 ∧ x / 2 = y / 2 := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩; omega

private theorem xor_mod_two (x y : Nat) : (x ^^^ y) % 2 = (x % 2) ^^^ (y % 2) := by
  have h := Nat.testBit_xor x y 0
  simp only [Nat.testBit_zero] at h
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  have hxy : (x ^^^ y) % 2 = 0 ∨ (x ^^^ y) % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hxy with hxy | hxy <;>
    simp_all

private theorem xor_div_two (x y : Nat) : (x ^^^ y) / 2 = (x / 2) ^^^ (y / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two,
      Nat.testBit_xor]

private theorem two_mul_xor_mod_two (x y : Nat) : ((2 * x) ^^^ y) % 2 = y % 2 := by
  rw [xor_mod_two]
  have h : (2 * x) % 2 = 0 := by omega
  rw [h]
  simp

private theorem two_mul_xor_div_two (x y : Nat) : ((2 * x) ^^^ y) / 2 = x ^^^ (y / 2) := by
  rw [xor_div_two]
  have h : (2 * x) / 2 = x := by omega
  rw [h]

private theorem step_even (a b c r q : Nat) :
    a * (2 * q) + c = clmul b (2 * q) ^^^ r ↔
      c % 2 = r % 2 ∧ a * q + c / 2 = clmul b q ^^^ (r / 2) := by
  rw [clmul_even, eq_iff_mod_div, two_mul_xor_mod_two, two_mul_xor_div_two]
  have hmul : a * (2 * q) + c = 2 * (a * q) + c := by
    rw [Nat.mul_left_comm]
  rw [hmul]
  have hm : (2 * (a * q) + c) % 2 = c % 2 := by omega
  have hd : (2 * (a * q) + c) / 2 = a * q + c / 2 := by omega
  rw [hm, hd]

private theorem step_odd (a b c r q : Nat) :
    a * (2 * q + 1) + c = clmul b (2 * q + 1) ^^^ r ↔
      (a + c) % 2 = (b ^^^ r) % 2 ∧
        a * q + (a + c) / 2 = clmul b q ^^^ ((b ^^^ r) / 2) := by
  rw [clmul_odd, Nat.xor_assoc, eq_iff_mod_div, two_mul_xor_mod_two, two_mul_xor_div_two]
  have hmul : a * (2 * q + 1) + c = 2 * (a * q) + (a + c) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.add_assoc]
  rw [hmul]
  have hm : (2 * (a * q) + (a + c)) % 2 = (a + c) % 2 := by omega
  have hd : (2 * (a * q) + (a + c)) / 2 = a * q + (a + c) / 2 := by omega
  rw [hm, hd]

/-- The 16 reachable dead (carry, mask) states for (9, 25). -/
def Dead9 (c r : Nat) : Prop :=
  (c = 0 ∧ r = 1) ∨ (c = 1 ∧ r = 2) ∨ (c = 1 ∧ r = 3) ∨ (c = 2 ∧ r = 6) ∨
  (c = 2 ∧ r = 7) ∨ (c = 3 ∧ r = 4) ∨ (c = 3 ∧ r = 5) ∨ (c = 3 ∧ r = 7) ∨
  (c = 5 ∧ r = 12) ∨ (c = 5 ∧ r = 13) ∨ (c = 5 ∧ r = 15) ∨ (c = 6 ∧ r = 14) ∨
  (c = 6 ∧ r = 15) ∨ (c = 7 ∧ r = 10) ∨ (c = 7 ∧ r = 11) ∨ (c = 8 ∧ r = 9)

/-- No natural number k satisfies 9*k + c = clmul 25 k ^^^ r from any Dead9 state. -/
theorem dead9_unsat : ∀ k c r, Dead9 c r → 9 * k + c ≠ clmul 25 k ^^^ r := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro c r hdead heq
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.mul_zero, Nat.zero_add, clmul_zero, Nat.zero_xor] at heq
      rcases hdead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · have hq : k / 2 < k := by omega
      by_cases hpar : k % 2 = 0
      · have hk : k = 2 * (k / 2) := by omega
        rw [hk, step_even] at heq
        rcases hdead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals
          first
          | exact absurd heq.1 (by decide)
          | exact ih (k / 2) hq _ _ (by unfold Dead9; decide) heq.2
      · have hk : k = 2 * (k / 2) + 1 := by omega
        rw [hk, step_odd] at heq
        rcases hdead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals
          first
          | exact absurd heq.1 (by decide)
          | exact ih (k / 2) hq _ _ (by unfold Dead9; decide) heq.2

/-- The 6 immediate dead-end (carry, mask) states for (15, 19). -/
def Dead15 (c r : Nat) : Prop :=
  (c = 3 ∧ r = 4) ∨ (c = 5 ∧ r = 6) ∨ (c = 6 ∧ r = 7) ∨
  (c = 8 ∧ r = 9) ∨ (c = 9 ∧ r = 8) ∨ (c = 11 ∧ r = 10)

/-- No natural number k satisfies 15*k + c = clmul 19 k ^^^ r from any Dead15 state. -/
theorem dead15_unsat (k c r : Nat) (hdead : Dead15 c r) :
    15 * k + c ≠ clmul 19 k ^^^ r := by
  intro heq
  by_cases hpar : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    rw [hk, step_even] at heq
    rcases hdead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact absurd heq.1 (by decide)
  · have hk : k = 2 * (k / 2) + 1 := by omega
    rw [hk, step_odd] at heq
    rcases hdead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact absurd heq.1 (by decide)

/-- The 8 coupled live (carry, mask) state pairs between (9, 25) and (15, 19). -/
def LivePair (c1 r1 c2 r2 : Nat) : Prop :=
  (c1 = 0 ∧ r1 = 0 ∧ c2 = 0 ∧ r2 = 0) ∨
  (c1 = 4 ∧ r1 = 12 ∧ c2 = 7 ∧ r2 = 9) ∨
  (c1 = 6 ∧ r1 = 10 ∧ c2 = 11 ∧ r2 = 13) ∨
  (c1 = 7 ∧ r1 = 9 ∧ c2 = 13 ∧ r2 = 15) ∨
  (c1 = 8 ∧ r1 = 8 ∧ c2 = 14 ∧ r2 = 14) ∨
  (c1 = 4 ∧ r1 = 4 ∧ c2 = 7 ∧ r2 = 7) ∨
  (c1 = 2 ∧ r1 = 2 ∧ c2 = 3 ∧ r2 = 3) ∨
  (c1 = 1 ∧ r1 = 1 ∧ c2 = 1 ∧ r2 = 1)

/-- Main state-pair induction: the two shifted equations are equivalent on all 8 LivePairs. -/
theorem live_iff : ∀ k c1 r1 c2 r2, LivePair c1 r1 c2 r2 →
    (9 * k + c1 = clmul 25 k ^^^ r1 ↔ 15 * k + c2 = clmul 19 k ^^^ r2) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro c1 r1 c2 r2 hlive
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.mul_zero, Nat.zero_add, clmul_zero, Nat.zero_xor]
      rcases hlive with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
    · have hq : k / 2 < k := by omega
      by_cases hpar : k % 2 = 0
      · have hk : k = 2 * (k / 2) := by omega
        rw [hk, step_even, step_even]
        rcases hlive with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        all_goals
          first
          | (constructor
             · intro ⟨_, h⟩
               exact ⟨by decide, (ih (k / 2) hq _ _ _ _ (by unfold LivePair; decide)).mp h⟩
             · intro ⟨_, h⟩
               exact ⟨by decide, (ih (k / 2) hq _ _ _ _ (by unfold LivePair; decide)).mpr h⟩)
          | (constructor
             · intro ⟨_, h⟩
               exact False.elim (dead9_unsat (k / 2) _ _ (by unfold Dead9; decide) h)
             · intro ⟨_, h⟩
               exact False.elim (dead15_unsat (k / 2) _ _ (by unfold Dead15; decide) h))
      · have hk : k = 2 * (k / 2) + 1 := by omega
        rw [hk, step_odd, step_odd]
        rcases hlive with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        all_goals
          first
          | (constructor
             · intro ⟨_, h⟩
               exact ⟨by decide, (ih (k / 2) hq _ _ _ _ (by unfold LivePair; decide)).mp h⟩
             · intro ⟨_, h⟩
               exact ⟨by decide, (ih (k / 2) hq _ _ _ _ (by unfold LivePair; decide)).mpr h⟩)
          | (constructor
             · intro ⟨_, h⟩
               exact False.elim (dead9_unsat (k / 2) _ _ (by unfold Dead9; decide) h)
             · intro ⟨_, h⟩
               exact False.elim (dead15_unsat (k / 2) _ _ (by unfold Dead15; decide) h))

/-- Full equivalence: 9*k = C(25, k) ↔ 15*k = C(19, k) for all natural numbers k. -/
theorem equiv_9_25_15_19 (k : Nat) : 9 * k = clmul 25 k ↔ 15 * k = clmul 19 k := by
  have h := live_iff k 0 0 0 0 (by unfold LivePair; decide)
  simpa using h

/-- OEIS A115801 membership predicate. -/
def inA115801 (k : Nat) : Prop := 9 * k = clmul 25 k

/-- OEIS A391850 membership predicate (explicitly honoring the k = 0 and m > 0 conventions). -/
def inA391850 (k : Nat) : Prop :=
  k = 0 ∨ (k > 0 ∧ ∃ m : Nat, m > 0 ∧ clmul m k = 15 * k)

/-- Main theorem: A115801 ⊆ A391850, with explicit witness m = 19 for k > 0. -/
theorem A115801_subset_A391850 : ∀ k : Nat, inA115801 k → inA391850 k := by
  intro k hk
  by_cases h0 : k = 0
  · exact Or.inl h0
  · exact Or.inr ⟨Nat.pos_of_ne_zero h0, 19, by omega, ((equiv_9_25_15_19 k).mp hk).symm⟩

-- Spot checks on concrete terms of A115801
example : inA115801 0 ∧ inA391850 0 := ⟨by simp [inA115801, clmul], Or.inl rfl⟩
example : inA115801 15 ∧ clmul 19 15 = 15 * 15 := by simp [inA115801, clmul]
example : inA115801 30 ∧ clmul 19 30 = 15 * 30 := by simp [inA115801, clmul]
example : inA115801 31 ∧ clmul 19 31 = 15 * 31 := by simp [inA115801, clmul]
example : inA115801 3855 ∧ clmul 19 3855 = 15 * 3855 := by simp [inA115801, clmul]

end A115801SubsetA391850

#print axioms A115801SubsetA391850.equiv_9_25_15_19
#print axioms A115801SubsetA391850.A115801_subset_A391850
