/-
  Proof of OEIS inclusion A115807 ⊆ A048719 (strict, witness 99).
  Self-contained Lean 4 formalization (core library only, no extra axioms).
-/

/-- Carryless multiplication in GF(2)[X] (OEIS A048720). -/
def clmul (a b : Nat) : Nat :=
  if h : b = 0 then 0
  else
    have : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    (2 * clmul a (b / 2)) ^^^ (if b % 2 = 1 then a else 0)
termination_by b

def A115807 (k : Nat) : Prop := 15 * k = clmul 27 k
def A048717 (k : Nat) : Prop := 3 * k = clmul 7 k
def A048716 (k : Nat) : Prop := 5 * k = clmul 5 k
def A048719 (k : Nat) : Prop := A048717 k ∧ A048716 k

/-! ### Elementary bitwise and carry-reduction lemmas -/

private theorem clmul_zero (a : Nat) : clmul a 0 = 0 := by
  rw [clmul]; simp

private theorem clmul_unfold (a k : Nat) :
    clmul a k = (2 * clmul a (k / 2)) ^^^ (a * (k % 2)) := by
  by_cases h : k = 0
  · subst h; rw [clmul_zero]; simp
  · conv => lhs; rw [clmul]
    simp only [h, ↓reduceDIte]
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
    · simp [h0]
    · simp [h1]

private theorem two_mul_xor_mod_two (x y : Nat) :
    ((2 * x) ^^^ y) % 2 = y % 2 := by
  have h0 : (2 * x).testBit 0 = false := by
    simp [Nat.testBit_zero]
  have h : ((2 * x) ^^^ y).testBit 0 = y.testBit 0 := by
    rw [Nat.testBit_xor, h0, Bool.false_xor]
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one ((2 * x) ^^^ y) with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one y with hb | hb <;>
  simp_all

private theorem two_mul_xor_div_two (x y : Nat) :
    ((2 * x) ^^^ y) / 2 = x ^^^ (y / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two]
  have h2x : (2 * x).testBit (i + 1) = x.testBit i := by
    rw [Nat.testBit_succ]
    simp
  rw [h2x]

private theorem nat_eq_iff_mod_div_two (x y : Nat) :
    x = y ↔ x % 2 = y % 2 ∧ x / 2 = y / 2 := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨hm, hd⟩; omega

/-- Fundamental one-step LSB carry-pair reduction for `m * k + c = clmul p k ^^^ d`. -/
theorem step_iff (m p c d k : Nat) :
    m * k + c = clmul p k ^^^ d ↔
      (c + m * (k % 2)) % 2 = (d ^^^ (p * (k % 2))) % 2 ∧
      m * (k / 2) + (c + m * (k % 2)) / 2 =
        clmul p (k / 2) ^^^ ((d ^^^ (p * (k % 2))) / 2) := by
  have hlhs : m * k + c = 2 * (m * (k / 2)) + (c + m * (k % 2)) := by
    have hk : 2 * (k / 2) + k % 2 = k := Nat.div_add_mod k 2
    calc m * k + c
        = m * (2 * (k / 2) + k % 2) + c := by rw [hk]
      _ = m * (2 * (k / 2)) + m * (k % 2) + c := by rw [Nat.mul_add]
      _ = 2 * (m * (k / 2)) + (c + m * (k % 2)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]; omega
  have hrhs : clmul p k ^^^ d = (2 * clmul p (k / 2)) ^^^ (d ^^^ (p * (k % 2))) := by
    rw [clmul_unfold p k, Nat.xor_assoc, Nat.xor_comm (p * (k % 2)) d]
  rw [hlhs, hrhs, nat_eq_iff_mod_div_two]
  rw [Nat.mul_add_mod, two_mul_xor_mod_two]
  rw [Nat.mul_add_div (by decide : 0 < 2), two_mul_xor_div_two]

/-- Parity obstruction: if `m` and `p` are odd and `c % 2 ≠ d % 2`, then
    `m * k + c = clmul p k ^^^ d` has no solution `k : Nat`. -/
theorem parity_dead (m p c d k : Nat) (hm : m % 2 = 1) (hp : p % 2 = 1)
    (hcd : c % 2 ≠ d % 2) :
    m * k + c ≠ clmul p k ^^^ d := by
  intro h
  have hbit := (step_iff m p c d k).mp h |>.1
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · simp [hk] at hbit
    exact hcd hbit
  · simp only [hk, Nat.mul_one] at hbit
    have hxor : (d ^^^ p).testBit 0 = (d.testBit 0 ^^ p.testBit 0) := Nat.testBit_xor d p 0
    simp only [Nat.testBit_zero] at hxor
    have hcm : (c + m) % 2 = (c % 2 + 1) % 2 := by omega
    rw [hcm] at hbit
    rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;>
    rcases Nat.mod_two_eq_zero_or_one (d ^^^ p) with hdp | hdp <;>
    simp_all

/-! ### Reachable 14-state product automaton -/

/-- All 14 states reachable from `(0,0 | 0,0 | 0,0)` under `(15, 27)` bit-matching. -/
inductive State where
  | S0  -- ( 0, 0 | 0,0 | 0,0)  live, terminal
  | S1  -- ( 7,13 | 1,3 | 2,2)  live
  | S2  -- ( 3, 6 | 0,1 | 1,1)  dead (parity)
  | S3  -- (11,11 | 2,2 | 3,3)  live, terminal
  | S4  -- ( 5, 5 | 1,1 | 1,1)  live, terminal
  | S5  -- (13, 8 | 2,2 | 4,3)  dead (parity)
  | S6  -- ( 2, 2 | 0,0 | 0,0)  live, terminal
  | S7  -- (10,15 | 2,3 | 3,2)  dead (parity)
  | S8  -- ( 1, 1 | 0,0 | 0,0)  live, terminal
  | S9  -- ( 8,12 | 1,3 | 2,2)  live
  | S10 -- ( 8,13 | 1,3 | 2,2)  dead (parity)
  | S11 -- ( 4, 6 | 0,1 | 1,1)  dead (1-step to S12/S13)
  | S12 -- ( 2, 3 | 0,0 | 0,0)  dead (parity)
  | S13 -- ( 9,14 | 1,3 | 3,2)  dead (parity)
  deriving DecidableEq, Repr

def State.c15 : State → Nat
  | .S0 => 0  | .S1 => 7  | .S2 => 3  | .S3 => 11 | .S4 => 5  | .S5 => 13 | .S6 => 2
  | .S7 => 10 | .S8 => 1  | .S9 => 8  | .S10 => 8 | .S11 => 4 | .S12 => 2 | .S13 => 9

def State.d27 : State → Nat
  | .S0 => 0  | .S1 => 13 | .S2 => 6  | .S3 => 11 | .S4 => 5  | .S5 => 8  | .S6 => 2
  | .S7 => 15 | .S8 => 1  | .S9 => 12 | .S10 => 13 | .S11 => 6 | .S12 => 3 | .S13 => 14

def State.c3 : State → Nat
  | .S0 => 0 | .S1 => 1 | .S2 => 0 | .S3 => 2 | .S4 => 1 | .S5 => 2 | .S6 => 0
  | .S7 => 2 | .S8 => 0 | .S9 => 1 | .S10 => 1 | .S11 => 0 | .S12 => 0 | .S13 => 1

def State.d7 : State → Nat
  | .S0 => 0 | .S1 => 3 | .S2 => 1 | .S3 => 2 | .S4 => 1 | .S5 => 2 | .S6 => 0
  | .S7 => 3 | .S8 => 0 | .S9 => 3 | .S10 => 3 | .S11 => 1 | .S12 => 0 | .S13 => 3

def State.c5 : State → Nat
  | .S0 => 0 | .S1 => 2 | .S2 => 1 | .S3 => 3 | .S4 => 1 | .S5 => 4 | .S6 => 0
  | .S7 => 3 | .S8 => 0 | .S9 => 2 | .S10 => 2 | .S11 => 1 | .S12 => 0 | .S13 => 3

def State.d5 : State → Nat
  | .S0 => 0 | .S1 => 2 | .S2 => 1 | .S3 => 3 | .S4 => 1 | .S5 => 3 | .S6 => 0
  | .S7 => 2 | .S8 => 0 | .S9 => 2 | .S10 => 2 | .S11 => 1 | .S12 => 0 | .S13 => 2

def State.next0 : State → State
  | .S0 => .S0  | .S1 => .S2  | .S3 => .S4  | .S4 => .S6
  | .S6 => .S8  | .S8 => .S0  | .S9 => .S11 | .S11 => .S12
  | s => s

def State.next1 : State → State
  | .S0 => .S1  | .S1 => .S3  | .S3 => .S5  | .S4 => .S7
  | .S6 => .S9  | .S8 => .S10 | .S9 => .S3  | .S11 => .S13
  | s => s

def State.isLive : State → Bool
  | .S0 | .S1 | .S3 | .S4 | .S6 | .S8 | .S9 => true
  | _ => false

def H15 (s : State) (k : Nat) : Prop := 15 * k + s.c15 = clmul 27 k ^^^ s.d27
def H3  (s : State) (k : Nat) : Prop :=  3 * k + s.c3  = clmul  7 k ^^^ s.d7
def H5  (s : State) (k : Nat) : Prop :=  5 * k + s.c5  = clmul  5 k ^^^ s.d5

/-! Finite table checks for the 7 live states (kernel-verified by `cases s <;> decide`). -/

private theorem live_terminal (s : State) (hl : s.isLive = true) (h : s.c15 = s.d27) :
    s.c3 = s.d7 ∧ s.c5 = s.d5 := by
  cases s <;> simp_all [State.isLive, State.c15, State.d27, State.c3, State.d7, State.c5, State.d5]

private theorem live_step0 (s : State) (hl : s.isLive = true) :
    s.c15 / 2 = s.next0.c15 ∧ s.d27 / 2 = s.next0.d27 ∧
    s.c3 % 2 = s.d7 % 2 ∧ s.c3 / 2 = s.next0.c3 ∧ s.d7 / 2 = s.next0.d7 ∧
    s.c5 % 2 = s.d5 % 2 ∧ s.c5 / 2 = s.next0.c5 ∧ s.d5 / 2 = s.next0.d5 := by
  cases s <;> simp_all [State.isLive] <;> decide

private theorem live_step1 (s : State) (hl : s.isLive = true) :
    (s.c15 + 15) / 2 = s.next1.c15 ∧ (s.d27 ^^^ 27) / 2 = s.next1.d27 ∧
    (s.c3 + 3) % 2 = (s.d7 ^^^ 7) % 2 ∧ (s.c3 + 3) / 2 = s.next1.c3 ∧ (s.d7 ^^^ 7) / 2 = s.next1.d7 ∧
    (s.c5 + 5) % 2 = (s.d5 ^^^ 5) % 2 ∧ (s.c5 + 5) / 2 = s.next1.c5 ∧ (s.d5 ^^^ 5) / 2 = s.next1.d5 := by
  cases s <;> simp_all [State.isLive] <;> decide

/-- S11 is dead: every input `k` fails `H15 S11 k`. -/
private theorem H15_S11_false (k : Nat) : ¬ H15 .S11 k := by
  intro h
  have hstep := (step_iff 15 27 4 6 k).mp h
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have h2 : 15 * (k / 2) + 2 = clmul 27 (k / 2) ^^^ 3 := by
      simpa [hk] using hstep.2
    exact parity_dead 15 27 2 3 (k / 2) (by decide) (by decide) (by decide) h2
  · have h2 : 15 * (k / 2) + 9 = clmul 27 (k / 2) ^^^ 14 := by
      simpa [hk] using hstep.2
    exact parity_dead 15 27 9 14 (k / 2) (by decide) (by decide) (by decide) h2

/-- All 7 dead states fail `H15 s k` for every `k : Nat`. -/
private theorem dead_false (s : State) (hd : s.isLive = false) (k : Nat) : ¬ H15 s k := by
  cases s with
  | S2  => exact parity_dead 15 27  3  6 k (by decide) (by decide) (by decide)
  | S5  => exact parity_dead 15 27 13  8 k (by decide) (by decide) (by decide)
  | S7  => exact parity_dead 15 27 10 15 k (by decide) (by decide) (by decide)
  | S10 => exact parity_dead 15 27  8 13 k (by decide) (by decide) (by decide)
  | S11 => exact H15_S11_false k
  | S12 => exact parity_dead 15 27  2  3 k (by decide) (by decide) (by decide)
  | S13 => exact parity_dead 15 27  9 14 k (by decide) (by decide) (by decide)
  | S0 | S1 | S3 | S4 | S6 | S8 | S9 => simp [State.isLive] at hd

/-- Main automaton invariant across all 14 reachable states. -/
theorem state_invariant : ∀ (k : Nat) (s : State), H15 s k → H3 s k ∧ H5 s k := by
  intro k
  refine Nat.strongRecOn k ?_
  intro k ih s h15
  cases hlive : s.isLive with
  | false => exact False.elim (dead_false s hlive k h15)
  | true =>
    by_cases hk0 : k = 0
    · subst hk0
      have hterm : s.c15 = s.d27 := by simpa [H15, clmul_zero] using h15
      have ⟨h3, h5⟩ := live_terminal s hlive hterm
      exact ⟨by simpa [H3, clmul_zero] using h3, by simpa [H5, clmul_zero] using h5⟩
    · have hlt : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk0) (by decide)
      have hstep15 := (step_iff 15 27 s.c15 s.d27 k).mp h15
      rcases Nat.mod_two_eq_zero_or_one k with hb | hb
      · have ⟨hc15, hd27, hb3, hc3, hd7, hb5, hc5, hd5⟩ := live_step0 s hlive
        have hnext : H15 s.next0 (k / 2) := by
          unfold H15
          have h2 := hstep15.2
          simp only [hb, Nat.mul_zero, Nat.add_zero, Nat.xor_zero] at h2
          rwa [hc15, hd27] at h2
        have ⟨h3', h5'⟩ := ih (k / 2) hlt s.next0 hnext
        constructor
        · rw [H3, step_iff]
          simp only [hb, Nat.mul_zero, Nat.add_zero, Nat.xor_zero]
          exact ⟨hb3, by rw [hc3, hd7]; exact h3'⟩
        · rw [H5, step_iff]
          simp only [hb, Nat.mul_zero, Nat.add_zero, Nat.xor_zero]
          exact ⟨hb5, by rw [hc5, hd5]; exact h5'⟩
      · have ⟨hc15, hd27, hb3, hc3, hd7, hb5, hc5, hd5⟩ := live_step1 s hlive
        have hnext : H15 s.next1 (k / 2) := by
          unfold H15
          have h2 := hstep15.2
          simp only [hb, Nat.mul_one] at h2
          rwa [hc15, hd27] at h2
        have ⟨h3', h5'⟩ := ih (k / 2) hlt s.next1 hnext
        constructor
        · rw [H3, step_iff]
          simp only [hb, Nat.mul_one]
          exact ⟨hb3, by rw [hc3, hd7]; exact h3'⟩
        · rw [H5, step_iff]
          simp only [hb, Nat.mul_one]
          exact ⟨hb5, by rw [hc5, hd5]; exact h5'⟩

/-- Main inclusion theorem: A115807 ⊆ A048719. -/
theorem A115807_subset_A048719 : ∀ k : Nat, A115807 k → A048719 k := by
  intro k hk
  have h15 : H15 .S0 k := by simpa [H15, A115807, State.c15, State.d27] using hk
  have ⟨h3, h5⟩ := state_invariant k .S0 h15
  exact ⟨by simpa [H3, A048717, State.c3, State.d7] using h3,
         by simpa [H5, A048716, State.c5, State.d5] using h5⟩

/-- Witness 99 arithmetic and strictness: 99 ∈ A048719 \ A115807. -/
theorem witness_99_arith :
    3 * 99 = 297 ∧ clmul 7 99 = 297 ∧
    5 * 99 = 495 ∧ clmul 5 99 = 495 ∧
    15 * 99 = 1485 ∧ clmul 27 99 = 1421 := by
  have eval : ∀ a,
      clmul a 99 =
        (2 * (2 * (2 * (2 * (2 * (2 * (2 * 0 ^^^ a) ^^^ a) ^^^ 0) ^^^ 0) ^^^ 0) ^^^ a) ^^^ a) := by
    intro a
    rw [clmul_unfold a 99, clmul_unfold a 49, clmul_unfold a 24, clmul_unfold a 12,
        clmul_unfold a 6, clmul_unfold a 3, clmul_unfold a 1, clmul_zero]
    simp
  rw [eval 7, eval 5, eval 27]
  decide

theorem witness_99 : A048719 99 ∧ ¬ A115807 99 := by
  have ⟨h1, h2, h3, h4, h5, h6⟩ := witness_99_arith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold A048717; omega
  · unfold A048716; omega
  · unfold A115807; omega

theorem A115807_strict_subset_A048719 :
    (∀ k : Nat, A115807 k → A048719 k) ∧ ∃ k : Nat, A048719 k ∧ ¬ A115807 k :=
  ⟨A115807_subset_A048719, ⟨99, witness_99⟩⟩

#print axioms A115807_subset_A048719
#print axioms witness_99
#print axioms A115807_strict_subset_A048719
