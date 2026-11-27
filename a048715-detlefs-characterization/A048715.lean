/-
  Self-contained Lean 4 formalization of Gary Detlefs's characterization
  of OEIS A048715 (Jun 08 2024):

    A048715 = { x : Nat | 7 * x = C(7, x) }
    For all x ≥ 1:
      7 * x = C(7, x)
        ↔ (x &&& (5 * x)) = x ∧ (x ||| (3 * x)) % x = 0 ∧ (x ||| (3 * x)) / x = 3
        ↔ (x &&& (2 * x)) = 0 ∧ (x &&& (4 * x)) = 0
        ↔ ∀ i, ¬(x.testBit i = true ∧ x.testBit (i + 1) = true) ∧
               ¬(x.testBit i = true ∧ x.testBit (i + 2) = true).

    For x = 0: 0 ∈ A048715, while Detlefs's condition excludes 0 due to division by x.
-/

/-- Carryless multiplication in GF(2)[X] (OEIS A048720). -/
def clmul : Nat → Nat → Nat
  | 0, _ => 0
  | a + 1, b =>
    let m := a + 1
    (if m % 2 = 1 then b else 0) ^^^ clmul (m / 2) (2 * b)
termination_by a _ => a
decreasing_by omega

/-- OEIS A048715 definition: 7x = C(7, x). -/
def inA048715 (x : Nat) : Prop :=
  7 * x = clmul 7 x

/-- Bit-triple characterization: no two 1-bits at distance 1 or 2. -/
def bitTriple (x : Nat) : Prop :=
  (x &&& (2 * x)) = 0 ∧ (x &&& (4 * x)) = 0

/-- Bitwise statement of "at most one 1-bit in every block of 3 consecutive bits". -/
def noTwoInTriple (x : Nat) : Prop :=
  ∀ i : Nat,
    ¬(x.testBit i = true ∧ x.testBit (i + 1) = true) ∧
    ¬(x.testBit i = true ∧ x.testBit (i + 2) = true)

/-- Gary Detlefs's characterization (exact division form for x ≥ 1). -/
def detlefs (x : Nat) : Prop :=
  x ≥ 1 ∧ (x &&& (5 * x)) = x ∧ (x ||| (3 * x)) % x = 0 ∧ (x ||| (3 * x)) / x = 3

/-! ### Helper lemmas on Nat bitwise operations -/

private theorem div_two_and (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_and]

private theorem mod_two_and (a b : Nat) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  have h0 : (a &&& b).testBit 0 = ((a % 2) &&& (b % 2)).testBit 0 := by
    simp [Nat.testBit_zero]
  rw [Nat.testBit_zero, Nat.testBit_zero] at h0
  have h1 : (a &&& b) % 2 = 0 ∨ (a &&& b) % 2 = 1 := by omega
  have hmods : (a % 2 = 0 ∨ a % 2 = 1) ∧ (b % 2 = 0 ∨ b % 2 = 1) := by omega
  rcases hmods with ⟨ha | ha, hb | hb⟩ <;> rcases h1 with h | h <;> simp_all

private theorem div_two_xor (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

private theorem mod_two_xor (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h0 : (a ^^^ b).testBit 0 = ((a % 2) ^^^ (b % 2)).testBit 0 := by
    simp [Nat.testBit_zero]
  rw [Nat.testBit_zero, Nat.testBit_zero] at h0
  have h1 : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  have hmods : (a % 2 = 0 ∨ a % 2 = 1) ∧ (b % 2 = 0 ∨ b % 2 = 1) := by omega
  rcases hmods with ⟨ha | ha, hb | hb⟩ <;> rcases h1 with h | h <;> simp_all

private theorem testBit_two_mul_succ (x i : Nat) : (2 * x).testBit (i + 1) = x.testBit i := by
  rw [Nat.testBit_succ, show (2 * x) / 2 = x by omega]

private theorem testBit_four_mul_succ_succ (x i : Nat) : (4 * x).testBit (i + 2) = x.testBit i := by
  rw [show 4 * x = 2 * (2 * x) by omega, testBit_two_mul_succ, testBit_two_mul_succ]

/-- Fundamental carry identity: a + b = (a ^^^ b) + 2 * (a &&& b). -/
theorem add_eq_xor_add_two_mul_and (a b : Nat) :
    a + b = (a ^^^ b) + 2 * (a &&& b) := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hih := add_eq_xor_add_two_mul_and (a / 2) (b / 2)
    have ha_eq : a = 2 * (a / 2) + a % 2 := by omega
    have hb_eq : b = 2 * (b / 2) + b % 2 := by omega
    have hxor_eq : a ^^^ b = 2 * ((a ^^^ b) / 2) + (a ^^^ b) % 2 := by omega
    have hand_eq : a &&& b = 2 * ((a &&& b) / 2) + (a &&& b) % 2 := by omega
    rw [div_two_xor, mod_two_xor] at hxor_eq
    rw [div_two_and, mod_two_and] at hand_eq
    have hmod : a % 2 + b % 2 = (a % 2 ^^^ b % 2) + 2 * (a % 2 &&& b % 2) := by
      have : (a % 2 = 0 ∨ a % 2 = 1) ∧ (b % 2 = 0 ∨ b % 2 = 1) := by omega
      rcases this with ⟨r | r, s | s⟩ <;> simp [r, s]
    omega
termination_by a
decreasing_by omega

/-- Carryless addition characterization: a + b = a ^^^ b ↔ a &&& b = 0. -/
theorem add_eq_xor_iff (a b : Nat) : a + b = a ^^^ b ↔ a &&& b = 0 := by
  have h := add_eq_xor_add_two_mul_and a b
  omega

/-- Key general lemma: a &&& (a + b) = a ↔ a &&& b = 0. -/
theorem and_add_eq_left_iff (a b : Nat) :
    (a &&& (a + b)) = a ↔ a &&& b = 0 := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hih := and_add_eq_left_iff (a / 2) (b / 2)
    have hmods : (a % 2 = 0 ∨ a % 2 = 1) ∧ (b % 2 = 0 ∨ b % 2 = 1) := by omega
    rcases hmods with ⟨ha0 | ha1, hb0 | hb1⟩
    · -- a % 2 = 0, b % 2 = 0
      have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
      have hmod : (a + b) % 2 = 0 := by omega
      constructor
      · intro h
        have h1 : (a &&& (a + b)) / 2 = a / 2 := congrArg (· / 2) h
        rw [div_two_and, hdiv] at h1
        have h2 : a / 2 &&& b / 2 = 0 := hih.mp h1
        have h3 : (a &&& b) / 2 = 0 := by rw [div_two_and]; exact h2
        have h4 : (a &&& b) % 2 = 0 := by rw [mod_two_and, ha0, hb0]; rfl
        omega
      · intro h
        have h1 : (a &&& b) / 2 = 0 := congrArg (· / 2) h
        rw [div_two_and] at h1
        have h2 : a / 2 &&& (a / 2 + b / 2) = a / 2 := hih.mpr h1
        have h3 : (a &&& (a + b)) / 2 = a / 2 := by rw [div_two_and, hdiv]; exact h2
        have h4 : (a &&& (a + b)) % 2 = a % 2 := by rw [mod_two_and, ha0, hmod]; rfl
        omega
    · -- a % 2 = 0, b % 2 = 1
      have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
      have hmod : (a + b) % 2 = 1 := by omega
      constructor
      · intro h
        have h1 : (a &&& (a + b)) / 2 = a / 2 := congrArg (· / 2) h
        rw [div_two_and, hdiv] at h1
        have h2 : a / 2 &&& b / 2 = 0 := hih.mp h1
        have h3 : (a &&& b) / 2 = 0 := by rw [div_two_and]; exact h2
        have h4 : (a &&& b) % 2 = 0 := by rw [mod_two_and, ha0, hb1]; rfl
        omega
      · intro h
        have h1 : (a &&& b) / 2 = 0 := congrArg (· / 2) h
        rw [div_two_and] at h1
        have h2 : a / 2 &&& (a / 2 + b / 2) = a / 2 := hih.mpr h1
        have h3 : (a &&& (a + b)) / 2 = a / 2 := by rw [div_two_and, hdiv]; exact h2
        have h4 : (a &&& (a + b)) % 2 = a % 2 := by rw [mod_two_and, ha0, hmod]; rfl
        omega
    · -- a % 2 = 1, b % 2 = 0
      have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
      have hmod : (a + b) % 2 = 1 := by omega
      constructor
      · intro h
        have h1 : (a &&& (a + b)) / 2 = a / 2 := congrArg (· / 2) h
        rw [div_two_and, hdiv] at h1
        have h2 : a / 2 &&& b / 2 = 0 := hih.mp h1
        have h3 : (a &&& b) / 2 = 0 := by rw [div_two_and]; exact h2
        have h4 : (a &&& b) % 2 = 0 := by rw [mod_two_and, ha1, hb0]; rfl
        omega
      · intro h
        have h1 : (a &&& b) / 2 = 0 := congrArg (· / 2) h
        rw [div_two_and] at h1
        have h2 : a / 2 &&& (a / 2 + b / 2) = a / 2 := hih.mpr h1
        have h3 : (a &&& (a + b)) / 2 = a / 2 := by rw [div_two_and, hdiv]; exact h2
        have h4 : (a &&& (a + b)) % 2 = a % 2 := by rw [mod_two_and, ha1, hmod]; rfl
        omega
    · -- a % 2 = 1, b % 2 = 1: both sides fail at bit 0
      have hmod : (a + b) % 2 = 0 := by omega
      constructor
      · intro h
        have h0 : (a &&& (a + b)) % 2 = a % 2 := congrArg (· % 2) h
        rw [mod_two_and, ha1, hmod] at h0
        simp at h0
      · intro h
        have h0 : (a &&& b) % 2 = 0 := congrArg (· % 2) h
        rw [mod_two_and, ha1, hb1] at h0
        simp at h0
termination_by a
decreasing_by omega

/-- Bitwise inclusion equivalence: (a ||| b) = b ↔ (a &&& b) = a. -/
theorem or_eq_right_iff (a b : Nat) : (a ||| b) = b ↔ (a &&& b) = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_or] at hi
    simp only [Nat.testBit_and]
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and] at hi
    simp only [Nat.testBit_or]
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

/-! ### Bridge 1: A048715 ↔ bitTriple ↔ noTwoInTriple -/

theorem clmul_seven (x : Nat) : clmul 7 x = x ^^^ (2 * x) ^^^ (4 * x) := by
  have h : clmul 7 x = x ^^^ (2 * x ^^^ (4 * x ^^^ 0)) := by
    unfold clmul
    simp only [show (7 : Nat) % 2 = 1 by rfl, ↓reduceIte, show (7 : Nat) / 2 = 3 by rfl]
    unfold clmul
    simp only [show (3 : Nat) % 2 = 1 by rfl, ↓reduceIte, show (3 : Nat) / 2 = 1 by rfl]
    unfold clmul
    simp only [show (1 : Nat) % 2 = 1 by rfl, ↓reduceIte, show (1 : Nat) / 2 = 0 by rfl]
    unfold clmul
    have : 2 * (2 * x) = 4 * x := by omega
    rw [this]
  rw [h, Nat.xor_zero, Nat.xor_assoc]

theorem inA048715_iff_bitTriple (x : Nat) : inA048715 x ↔ bitTriple x := by
  unfold inA048715 bitTriple
  rw [clmul_seven]
  have h1 := add_eq_xor_add_two_mul_and x (2 * x)
  have h2 := add_eq_xor_add_two_mul_and (x ^^^ (2 * x)) (4 * x)
  have h7 : 7 * x = (x + 2 * x) + 4 * x := by omega
  have heq : 7 * x = (x ^^^ (2 * x) ^^^ (4 * x)) + 2 * (x &&& (2 * x)) + 2 * ((x ^^^ (2 * x)) &&& (4 * x)) := by
    omega
  constructor
  · intro h
    have hzero1 : x &&& (2 * x) = 0 := by omega
    have hzero2 : (x ^^^ (2 * x)) &&& (4 * x) = 0 := by omega
    refine ⟨hzero1, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have hi1 := congrArg (fun n => n.testBit i) hzero1
    have hi2 := congrArg (fun n => n.testBit i) hzero2
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at hi1 hi2 ⊢
    cases hx : x.testBit i <;> cases h2x : (2 * x).testBit i <;> cases h4x : (4 * x).testBit i <;> simp_all
  · rintro ⟨h12, h14⟩
    have h24 : (2 * x) &&& (4 * x) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero =>
        simp [Nat.testBit_zero]
      | succ j =>
        have hi := congrArg (fun n => n.testBit j) h12
        simp only [Nat.testBit_and, Nat.zero_testBit] at hi ⊢
        rw [testBit_two_mul_succ, show 4 * x = 2 * (2 * x) by omega, testBit_two_mul_succ]
        exact hi
    have hxor4 : (x ^^^ (2 * x)) &&& (4 * x) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have hi1 := congrArg (fun n => n.testBit i) h14
      have hi2 := congrArg (fun n => n.testBit i) h24
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at hi1 hi2 ⊢
      cases hx : x.testBit i <;> cases h2x : (2 * x).testBit i <;> cases h4x : (4 * x).testBit i <;> simp_all
    omega

theorem bitTriple_iff_noTwoInTriple (x : Nat) : bitTriple x ↔ noTwoInTriple x := by
  unfold bitTriple noTwoInTriple
  constructor
  · rintro ⟨h12, h14⟩ i
    constructor
    · intro ⟨hi, hi1⟩
      have h := congrArg (fun n => n.testBit (i + 1)) h12
      simp only [Nat.testBit_and, Nat.zero_testBit] at h
      rw [hi1, testBit_two_mul_succ, hi] at h
      simp at h
    · intro ⟨hi, hi2⟩
      have h := congrArg (fun n => n.testBit (i + 2)) h14
      simp only [Nat.testBit_and, Nat.zero_testBit] at h
      rw [hi2, testBit_four_mul_succ_succ, hi] at h
      simp at h
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ i =>
        simp only [Nat.testBit_and, Nat.zero_testBit]
        rw [testBit_two_mul_succ]
        have hnot := (h i).1
        cases hx : x.testBit i <;> cases hx1 : x.testBit (i + 1) <;> simp_all
    · apply Nat.eq_of_testBit_eq
      intro k
      match k with
      | 0 =>
        simp only [Nat.testBit_zero]
        have : (4 * x) % 2 = 0 := by omega
        simp [this]
      | 1 =>
        simp only [Nat.testBit_and, Nat.zero_testBit]
        have h4x : (4 * x).testBit 1 = false := by
          rw [show 4 * x = 2 * (2 * x) by omega, testBit_two_mul_succ, Nat.testBit_zero]
          have : (2 * x) % 2 = 0 := by omega
          simp [this]
        rw [h4x]; simp
      | i + 2 =>
        simp only [Nat.testBit_and, Nat.zero_testBit]
        rw [testBit_four_mul_succ_succ]
        have hnot := (h i).2
        cases hx : x.testBit i <;> cases hx2 : x.testBit (i + 2) <;> simp_all

/-! ### Bridge 2: Detlefs ↔ bitTriple (for x ≥ 1) -/

theorem exact_div_three_iff (x n : Nat) (hx : x ≥ 1) :
    (n % x = 0 ∧ n / x = 3) ↔ n = 3 * x := by
  constructor
  · rintro ⟨hmod, hdiv⟩
    have h := Nat.div_add_mod n x
    rw [hdiv, hmod] at h
    omega
  · intro h
    subst h
    refine ⟨Nat.mul_mod_left 3 x, ?_⟩
    rw [Nat.mul_div_left 3 (by omega)]

theorem detlefs_iff_bitTriple (x : Nat) (hx : x ≥ 1) :
    detlefs x ↔ bitTriple x := by
  unfold detlefs bitTriple
  rw [exact_div_three_iff x (x ||| (3 * x)) hx]
  rw [or_eq_right_iff x (3 * x)]
  rw [show 5 * x = x + 4 * x by omega]
  rw [show 3 * x = x + 2 * x by omega]
  rw [and_add_eq_left_iff x (4 * x), and_add_eq_left_iff x (2 * x)]
  exact ⟨fun ⟨_, h4, h2⟩ => ⟨h2, h4⟩, fun ⟨h2, h4⟩ => ⟨hx, h4, h2⟩⟩

/-! ### Main Theorem and x = 0 edge case -/

/-- Main Theorem: For all x ≥ 1, Gary Detlefs's characterization equals OEIS A048715. -/
theorem detlefs_iff_A048715 (x : Nat) (hx : x ≥ 1) :
    detlefs x ↔ inA048715 x := by
  rw [detlefs_iff_bitTriple x hx, inA048715_iff_bitTriple]

theorem zero_in_A048715 : inA048715 0 := by
  unfold inA048715
  rw [clmul_seven]
  simp

theorem zero_not_detlefs : ¬ detlefs 0 := by
  intro ⟨hx, _⟩; omega

#print axioms detlefs_iff_A048715
#print axioms inA048715_iff_bitTriple
#print axioms bitTriple_iff_noTwoInTriple
#print axioms zero_in_A048715
#print axioms zero_not_detlefs
