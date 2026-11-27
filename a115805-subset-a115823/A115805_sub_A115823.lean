/-
  Proof of the OEIS inclusion A115805 ⊆ A115823 (strict, with witness k = 5).
  Self-contained Lean 4 (no Mathlib, no external dependencies).

  Definitions:
    clmul a b = A048720(a, b), carryless multiplication in GF(2)[X].
    A115805   = { k : Nat | 13 * k = clmul 29 k }
    A115823   = { k : Nat | (8 * k) ^^^ (13 * k) = 21 * k }
-/

def clmul (a b : Nat) : Nat :=
  if h : b = 0 then 0
  else
    let low := if b % 2 = 1 then a else 0
    low ^^^ (2 * clmul a (b / 2))
termination_by b

def inA115805 (k : Nat) : Prop := 13 * k = clmul 29 k
def inA115823 (k : Nat) : Prop := (8 * k) ^^^ (13 * k) = 21 * k

/-! ### Bitwise helper lemmas -/

private theorem div_mod_two (n : Nat) : n = 2 * (n / 2) + n % 2 := by omega

private theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  have h1 : (a ^^^ b) >>> 1 = (a >>> 1) ^^^ (b >>> 1) := Nat.shiftRight_xor_distrib
  simpa [Nat.shiftRight_eq_div_pow] using h1

private theorem and_div_two (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  have h1 : (a &&& b) >>> 1 = (a >>> 1) &&& (b >>> 1) := Nat.shiftRight_and_distrib
  simpa [Nat.shiftRight_eq_div_pow] using h1

private theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h1 : (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) := Nat.and_xor_distrib_right
  simpa [Nat.and_one_is_mod] using h1

private theorem and_mod_two (a b : Nat) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  have h : (a &&& b) &&& 1 = (a &&& 1) &&& (b &&& 1) := by
    calc (a &&& b) &&& 1
        = a &&& (b &&& 1) := Nat.and_assoc a b 1
      _ = a &&& ((1 &&& 1) &&& b) := by rw [Nat.and_comm b 1]; simp
      _ = (a &&& 1) &&& (1 &&& b) := by rw [Nat.and_assoc, Nat.and_assoc]
      _ = (a &&& 1) &&& (b &&& 1) := by rw [Nat.and_comm 1 b]
  simpa [Nat.and_one_is_mod] using h

private theorem add_eq_xor_add_two_and (a b : Nat) : a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction h : a + b using Nat.strongRecOn generalizing a b with
  | ind m ih =>
    by_cases h0 : a = 0 ∧ b = 0
    · rcases h0 with ⟨rfl, rfl⟩
      subst h
      rfl
    · have hlt : a / 2 + b / 2 < m := by omega
      have hrec := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl
      have hdivx := div_mod_two (a ^^^ b)
      have hdiva := div_mod_two (a &&& b)
      rw [xor_div_two, xor_mod_two] at hdivx
      rw [and_div_two, and_mod_two] at hdiva
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with ha0 | ha1
      · rcases hb2 with hb0 | hb1
        · simp [ha0, hb0] at hdivx hdiva; omega
        · simp [ha0, hb1] at hdivx hdiva; omega
      · rcases hb2 with hb0 | hb1
        · simp [ha1, hb0] at hdivx hdiva; omega
        · simp [ha1, hb1] at hdivx hdiva; omega

theorem xor_eq_add_iff_and_eq_zero (a b : Nat) : a ^^^ b = a + b ↔ a &&& b = 0 := by
  have h := add_eq_xor_add_two_and a b
  omega

theorem inA115823_iff (k : Nat) : inA115823 k ↔ (8 * k) &&& (13 * k) = 0 := by
  unfold inA115823
  have hsum : 8 * k + 13 * k = 21 * k := by omega
  rw [← hsum]
  exact xor_eq_add_iff_and_eq_zero (8 * k) (13 * k)

private theorem eq_zero_of_div_mod_zero {x : Nat} (hd : x / 2 = 0) (hm : x % 2 = 0) : x = 0 := by
  omega

private theorem and_eq_zero_of_step {a b : Nat}
    (hd : (a / 2) &&& (b / 2) = 0)
    (hm : (a % 2) &&& (b % 2) = 0) : a &&& b = 0 := by
  apply eq_zero_of_div_mod_zero
  · rw [and_div_two]; exact hd
  · rw [and_mod_two]; exact hm

/-! ### One-step unfolding of `clmul 29 k ^^^ p` -/

private theorem clmul_unfold_even {k : Nat} (hk : k ≠ 0) (he : k % 2 = 0) :
    clmul 29 k = 2 * clmul 29 (k / 2) := by
  rw [clmul]
  simp [hk, he]

private theorem clmul_unfold_odd {k : Nat} (hk : k ≠ 0) (ho : k % 2 = 1) :
    clmul 29 k = 29 ^^^ (2 * clmul 29 (k / 2)) := by
  rw [clmul]
  simp [hk, ho]

private theorem two_mul_div_two (x : Nat) : (2 * x) / 2 = x := by omega
private theorem two_mul_mod_two (x : Nat) : (2 * x) % 2 = 0 := by omega

private theorem step_hyp_even {k c p : Nat} (hk : k ≠ 0) (he : k % 2 = 0)
    (h : 13 * k + c = clmul 29 k ^^^ p) :
    c % 2 = p % 2 ∧ 13 * (k / 2) + c / 2 = clmul 29 (k / 2) ^^^ (p / 2) := by
  rw [clmul_unfold_even hk he] at h
  have hmod := congrArg (· % 2) h
  rw [xor_mod_two, two_mul_mod_two] at hmod
  have hdiv := congrArg (· / 2) h
  rw [xor_div_two, two_mul_div_two] at hdiv
  have h0x : ∀ n : Nat, 0 ^^^ n = n := Nat.zero_xor
  rw [h0x] at hmod
  constructor
  · omega
  · have h13 : (13 * k + c) / 2 = 13 * (k / 2) + c / 2 := by omega
    rw [h13] at hdiv
    exact hdiv

private theorem step_hyp_odd {k c p : Nat} (hk : k ≠ 0) (ho : k % 2 = 1)
    (h : 13 * k + c = clmul 29 k ^^^ p) :
    c % 2 = p % 2 ∧ 13 * (k / 2) + (c + 13) / 2 = clmul 29 (k / 2) ^^^ ((p ^^^ 29) / 2) := by
  rw [clmul_unfold_odd hk ho] at h
  have hrhs : (29 ^^^ (2 * clmul 29 (k / 2))) ^^^ p = (2 * clmul 29 (k / 2)) ^^^ (p ^^^ 29) := by
    rw [Nat.xor_comm 29 (2 * clmul 29 (k / 2)), Nat.xor_assoc, Nat.xor_comm 29 p]
  rw [hrhs] at h
  have hmod := congrArg (· % 2) h
  rw [xor_mod_two, two_mul_mod_two, Nat.zero_xor, xor_mod_two] at hmod
  have hdiv := congrArg (· / 2) h
  rw [xor_div_two, two_mul_div_two] at hdiv
  have h29m : 29 % 2 = 1 := rfl
  rw [h29m] at hmod
  have hp2 : p % 2 = 0 ∨ p % 2 = 1 := by omega
  constructor
  · rcases hp2 with hp0 | hp1
    · simp [hp0] at hmod; omega
    · simp [hp1] at hmod; omega
  · have h13 : (13 * k + c) / 2 = 13 * (k / 2) + (c + 13) / 2 := by omega
    rw [h13] at hdiv
    exact hdiv

/-! ### Finite automaton: 13 dead states and 6 live (trim) states -/

private def isDead (c p : Nat) : Prop :=
  (c = 0 ∧ p = 1) ∨ (c = 1 ∧ p = 3) ∨ (c = 2 ∧ p = 3) ∨
  (c = 3 ∧ p = 7) ∨ (c = 4 ∧ p = 6) ∨ (c = 5 ∧ p = 4) ∨
  (c = 7 ∧ p = 14) ∨ (c = 7 ∧ p = 15) ∨ (c = 8 ∧ p = 12) ∨
  (c = 8 ∧ p = 13) ∨ (c = 10 ∧ p = 8) ∨ (c = 10 ∧ p = 9) ∨
  (c = 11 ∧ p = 10)

private def isTrim (c p c8 : Nat) : Prop :=
  (c = 0 ∧ p = 0 ∧ c8 = 0) ∨
  (c = 6 ∧ p = 14 ∧ c8 = 4) ∨
  (c = 9 ∧ p = 9 ∧ c8 = 6) ∨
  (c = 4 ∧ p = 4 ∧ c8 = 3) ∨
  (c = 2 ∧ p = 2 ∧ c8 = 1) ∨
  (c = 1 ∧ p = 1 ∧ c8 = 0)

private theorem dead_unsat (k : Nat) :
    ∀ c p, isDead c p → 13 * k + c = clmul 29 k ^^^ p → False := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro c p hd h
    by_cases hk0 : k = 0
    · subst hk0
      simp [clmul] at h
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · have hlt : k / 2 < k := by omega
      have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hpar with he | ho
      · obtain ⟨hcm, hnext⟩ := step_hyp_even hk0 he h
        rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · omega
        · exact ih (k / 2) hlt 0 1 (by simp [isDead]) hnext
        · omega
        · exact ih (k / 2) hlt 1 3 (by simp [isDead]) hnext
        · exact ih (k / 2) hlt 2 3 (by simp [isDead]) hnext
        · omega
        · omega
        · exact ih (k / 2) hlt 3 7 (by simp [isDead]) hnext
        · exact ih (k / 2) hlt 4 6 (by simp [isDead]) hnext
        · omega
        · exact ih (k / 2) hlt 5 4 (by simp [isDead]) hnext
        · omega
        · omega
      · obtain ⟨hcm, hnext⟩ := step_hyp_odd hk0 ho h
        rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · omega
        · exact ih (k / 2) hlt 7 15 (by simp [isDead]) hnext
        · omega
        · exact ih (k / 2) hlt 8 13 (by simp [isDead]) hnext
        · exact ih (k / 2) hlt 8 13 (by simp [isDead]) hnext
        · omega
        · omega
        · exact ih (k / 2) hlt 10 9 (by simp [isDead]) hnext
        · exact ih (k / 2) hlt 10 8 (by simp [isDead]) hnext
        · omega
        · exact ih (k / 2) hlt 11 10 (by simp [isDead]) hnext
        · omega
        · omega

private theorem trim_disjoint (k : Nat) :
    ∀ c p c8, isTrim c p c8 → 13 * k + c = clmul 29 k ^^^ p →
      (8 * k + c8) &&& (13 * k + c) = 0 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro c p c8 ht h
    by_cases hk0 : k = 0
    · subst hk0
      simp [clmul] at h
      rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rfl
      · omega
      · rfl
      · rfl
      · rfl
      · rfl
    · have hlt : k / 2 < k := by omega
      have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hpar with he | ho
      · obtain ⟨_, hnext⟩ := step_hyp_even hk0 he h
        have hdiv8 : (8 * k + c8) / 2 = 8 * (k / 2) + c8 / 2 := by omega
        have hdiv13 : (13 * k + c) / 2 = 13 * (k / 2) + c / 2 := by omega
        have hmod8 : (8 * k + c8) % 2 = c8 % 2 := by omega
        have hmod13 : (13 * k + c) % 2 = c % 2 := by omega
        apply and_eq_zero_of_step
        · rw [hdiv8, hdiv13]
          rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact ih (k / 2) hlt 0 0 0 (by simp [isTrim]) hnext
          · exact False.elim (dead_unsat (k / 2) 3 7 (by simp [isDead]) hnext)
          · exact ih (k / 2) hlt 4 4 3 (by simp [isTrim]) hnext
          · exact ih (k / 2) hlt 2 2 1 (by simp [isTrim]) hnext
          · exact ih (k / 2) hlt 1 1 0 (by simp [isTrim]) hnext
          · exact ih (k / 2) hlt 0 0 0 (by simp [isTrim]) hnext
        · rw [hmod8, hmod13]
          rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl
      · obtain ⟨_, hnext⟩ := step_hyp_odd hk0 ho h
        have hdiv8 : (8 * k + c8) / 2 = 8 * (k / 2) + (c8 + 8) / 2 := by omega
        have hdiv13 : (13 * k + c) / 2 = 13 * (k / 2) + (c + 13) / 2 := by omega
        have hmod8 : (8 * k + c8) % 2 = c8 % 2 := by omega
        have hmod13 : (13 * k + c) % 2 = (c + 1) % 2 := by omega
        rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · apply and_eq_zero_of_step
          · rw [hdiv8, hdiv13]; exact ih (k / 2) hlt 6 14 4 (by simp [isTrim]) hnext
          · rw [hmod8, hmod13]; rfl
        · apply and_eq_zero_of_step
          · rw [hdiv8, hdiv13]; exact ih (k / 2) hlt 9 9 6 (by simp [isTrim]) hnext
          · rw [hmod8, hmod13]; rfl
        · exact False.elim (dead_unsat (k / 2) 11 10 (by simp [isDead]) hnext)
        · exact False.elim (dead_unsat (k / 2) 8 12 (by simp [isDead]) hnext)
        · exact False.elim (dead_unsat (k / 2) 7 15 (by simp [isDead]) hnext)
        · exact False.elim (dead_unsat (k / 2) 7 14 (by simp [isDead]) hnext)

/-! ### Main theorem and strictness witness -/

theorem A115805_subset_A115823 : ∀ k : Nat, inA115805 k → inA115823 k := by
  intro k hk
  rw [inA115823_iff]
  have h := trim_disjoint k 0 0 0 (by simp [isTrim]) (by simpa [inA115805] using hk)
  simpa using h

theorem witness_strict : inA115823 5 ∧ ¬ inA115805 5 := by
  unfold inA115823 inA115805
  constructor
  · decide
  · simp [clmul]

#print axioms A115805_subset_A115823
#print axioms witness_strict
