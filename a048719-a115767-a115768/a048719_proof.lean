-- Self-contained Lean 4 formalization of the OEIS A048719 / A115767 / A115768 claims.
-- Carryless multiplication in GF(2)[X] (OEIS A048720):
def clmul (a b : Nat) : Nat :=
  if a = 0 then 0
  else (if a % 2 = 1 then b else 0) ^^^ clmul (a / 2) (2 * b)

-- OEIS sequence predicates:
def inA048719 (k : Nat) : Prop :=
  3 * k = clmul 7 k ∧ 5 * k = clmul 5 k

def inA115767 (k : Nat) : Prop :=
  (2 * k) ^^^ (5 * k) = 3 * k

def inA115768 (k : Nat) : Prop :=
  (2 * k) ^^^ (5 * k) = 3 * k ∧ (4 * k) ^^^ k ≠ 5 * k

private theorem clmul_zero_left (b : Nat) : clmul 0 b = 0 := by
  unfold clmul
  simp

private theorem clmul_one_left (b : Nat) : clmul 1 b = b := by
  unfold clmul
  simp [clmul_zero_left]

private theorem clmul_two_left (b : Nat) : clmul 2 b = 2 * b := by
  unfold clmul
  simp [clmul_one_left]

private theorem clmul_three_left (b : Nat) : clmul 3 b = b ^^^ (2 * b) := by
  unfold clmul
  simp [clmul_one_left]

theorem clmul_five (k : Nat) : clmul 5 k = (4 * k) ^^^ k := by
  have h4 : 2 * (2 * k) = 4 * k := by omega
  unfold clmul
  simp [clmul_two_left, h4, Nat.xor_comm]

theorem clmul_seven (k : Nat) : clmul 7 k = (2 * k) ^^^ clmul 5 k := by
  have h4 : 2 * (2 * k) = 4 * k := by omega
  have h7 : clmul 7 k = k ^^^ ((2 * k) ^^^ (4 * k)) := by
    unfold clmul
    simp [clmul_three_left, h4]
  rw [h7, clmul_five]
  rw [Nat.xor_comm k ((2 * k) ^^^ (4 * k))]
  rw [Nat.xor_assoc]

-- Claim (1): A048719 ⊆ A115767
theorem part1_subset (k : Nat) (h : inA048719 k) : inA115767 k := by
  rcases h with ⟨h7, h5⟩
  unfold inA115767
  rw [h7, clmul_seven, ← h5]

-- Claim (2): For k ∈ A115767, k ∈ A048719 ↔ (4k) XOR k = 5k
theorem part2_iff (k : Nat) (h : inA115767 k) :
    inA048719 k ↔ (4 * k) ^^^ k = 5 * k := by
  constructor
  · intro h48
    rw [← clmul_five, ← h48.2]
  · intro h4k
    have h5 : 5 * k = clmul 5 k := by rw [clmul_five, h4k]
    have h7 : 3 * k = clmul 7 k := by
      rw [clmul_seven, ← h5]
      exact h.symm
    exact ⟨h7, h5⟩

-- Equivalent formulation: A115768 = A115767 \ A048719
theorem part2_set_diff (k : Nat) :
    inA115768 k ↔ (inA115767 k ∧ ¬ inA048719 k) := by
  constructor
  · rintro ⟨h67, hne⟩
    refine ⟨h67, ?_⟩
    intro h48
    exact hne ((part2_iff k h67).mp h48)
  · rintro ⟨h67, hn48⟩
    refine ⟨h67, ?_⟩
    intro heq
    exact hn48 ((part2_iff k h67).mpr heq)

-- Strictness witness k = 11 and explicit arithmetic
theorem witness_arithmetic :
    (2 * 11) ^^^ (5 * 11) = 33 ∧
    3 * 11 = 33 ∧
    clmul 7 11 = 49 ∧
    5 * 11 = 55 ∧
    clmul 5 11 = 39 ∧
    (4 * 11) ^^^ 11 = 39 := by
  refine ⟨by decide, by decide, ?_, by decide, ?_, by decide⟩
  · rw [clmul_seven, clmul_five]; decide
  · rw [clmul_five]; decide

theorem strictness_witness :
    inA115767 11 ∧ ¬ inA048719 11 ∧ inA115768 11 := by
  have h11 : inA115767 11 := by
    unfold inA115767; decide
  have hne : (4 * 11) ^^^ 11 ≠ 5 * 11 := by decide
  have h68 : inA115768 11 := ⟨h11, hne⟩
  have hn48 : ¬ inA048719 11 := ((part2_set_diff 11).mp h68).2
  exact ⟨h11, hn48, h68⟩

#print axioms part1_subset
#print axioms part2_iff
#print axioms part2_set_diff
#print axioms witness_arithmetic
#print axioms strictness_witness
