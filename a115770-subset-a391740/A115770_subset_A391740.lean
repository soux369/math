/-
  Proof that OEIS A115770 ⊆ A391740 via the (carry, mask) state-pair method.

  Definitions:
  * C(a, k) = A048720(a, k): carryless multiplication in GF(2)[X].
  * A115770 = { k : Nat | 7 * k = C(11, k) }.
  * A391740 = { k : Nat | k = 0 ∨ ∃ m > 0, C(m, k) = 5 * k }.

  We prove the implication `7 * k = C(11, k) → 5 * k = C(13, k)` by strong
  binary induction over the 10 reachable state pairs `(c7, m11, c5, m13)`
  (6 live states + 4 dead-end parity-mismatch states), then discharge
  `A115770 ⊆ A391740` with witness `m = 13 > 0` (and `k = 0` directly).
-/

/-- Carryless binary multiplication `C(a, k) = A048720(a, k)` by recursion on `k`.
    Matches Henry Bottomley's recurrence:
      `C(a, 2*q) = 2 * C(a, q)` and `C(a, 2*q + 1) = (2 * C(a, q)) ^^^ a`. -/
def clmul (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let q := (k + 1) / 2
    let b := (k + 1) % 2
    (2 * clmul a q) ^^^ (if b = 1 then a else 0)
termination_by k => k

/-- OEIS A115770: `{k : Nat | 7 * k = A048720(11, k)}`. -/
def inA115770 (k : Nat) : Prop :=
  7 * k = clmul 11 k

/-- OEIS A391740: `{0} ∪ {k : Nat | ∃ m > 0, A048720(m, k) = 5 * k}`. -/
def inA391740 (k : Nat) : Prop :=
  k = 0 ∨ ∃ m : Nat, m > 0 ∧ clmul m k = 5 * k

/-! ### Helper bit-splitting lemmas -/

theorem clmul_zero (a : Nat) : clmul a 0 = 0 := by
  simp [clmul]

theorem clmul_step (a k : Nat) (hk : k > 0) :
    clmul a k = (2 * clmul a (k / 2)) ^^^ (if k % 2 = 1 then a else 0) := by
  cases k with
  | zero => contradiction
  | succ n => simp [clmul]

theorem two_mul_xor_eq (x y : Nat) :
    (2 * x) ^^^ y = 2 * (x ^^^ (y / 2)) + (y % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (2 * x).testBit (j + 1) = x.testBit j := by
      rw [Nat.testBit_succ]
      simp
    have h2 : (2 * (x ^^^ (y / 2)) + y % 2).testBit (j + 1) = (x ^^^ (y / 2)).testBit j := by
      have hdiv : (2 * (x ^^^ (y / 2)) + y % 2) / 2 = x ^^^ (y / 2) := by omega
      rw [Nat.testBit_succ, hdiv]
    rw [Nat.testBit_xor, h1, h2, Nat.testBit_xor, Nat.testBit_succ]

theorem mul_bit_split (a c k : Nat) :
    a * k + c = 2 * (a * (k / 2) + (a * (k % 2) + c) / 2) + ((a * (k % 2) + c) % 2) := by
  have h1 : a * k = a * (2 * (k / 2) + k % 2) := by rw [Nat.div_add_mod]
  have h2 : a * (2 * (k / 2) + k % 2) = 2 * (a * (k / 2)) + a * (k % 2) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]
  omega

theorem clmul_xor_bit_split (a m k : Nat) (hk : k > 0) :
    clmul a k ^^^ m =
      2 * (clmul a (k / 2) ^^^ (((if k % 2 = 1 then a else 0) ^^^ m) / 2)) +
      (((if k % 2 = 1 then a else 0) ^^^ m) % 2) := by
  rw [clmul_step a k hk, Nat.xor_assoc, two_mul_xor_eq]

/-! ### The 10 reachable (carry, mask) state pairs -/

/-- The 10 reachable state pairs `(c7, m11, c5, m13)` for `7k = C(11, k) → 5k = C(13, k)`:
    * Live states: `s0, s1, s3, s5, s6, s7`
    * Dead-end parity-mismatch states: `s2, s4, s8, s9` -/
inductive State
  | s0  -- (0, 0, 0, 0)  [acc7, acc5]
  | s1  -- (3, 5, 2, 6)
  | s2  -- (1, 2, 1, 3)  [dead for 7/11]
  | s3  -- (5, 7, 3, 5)
  | s4  -- (2, 3, 1, 2)  [dead for 7/11]
  | s5  -- (6, 6, 4, 4)  [acc7, acc5]
  | s6  -- (3, 3, 2, 2)  [acc7, acc5]
  | s7  -- (1, 1, 1, 1)  [acc7, acc5]
  | s8  -- (5, 4, 3, 7)  [dead for 7/11]
  | s9  -- (4, 5, 3, 6)  [dead for 7/11]
  deriving DecidableEq, Repr

def State.c7 : State → Nat
  | .s0 => 0 | .s1 => 3 | .s2 => 1 | .s3 => 5 | .s4 => 2
  | .s5 => 6 | .s6 => 3 | .s7 => 1 | .s8 => 5 | .s9 => 4

def State.m11 : State → Nat
  | .s0 => 0 | .s1 => 5 | .s2 => 2 | .s3 => 7 | .s4 => 3
  | .s5 => 6 | .s6 => 3 | .s7 => 1 | .s8 => 4 | .s9 => 5

def State.c5 : State → Nat
  | .s0 => 0 | .s1 => 2 | .s2 => 1 | .s3 => 3 | .s4 => 1
  | .s5 => 4 | .s6 => 2 | .s7 => 1 | .s8 => 3 | .s9 => 3

def State.m13 : State → Nat
  | .s0 => 0 | .s1 => 6 | .s2 => 3 | .s3 => 5 | .s4 => 2
  | .s5 => 4 | .s6 => 2 | .s7 => 1 | .s8 => 7 | .s9 => 6

/-- Transition function on live states for bit `b ∈ {0, 1}`. -/
def State.next : State → Bool → State
  | .s0, false => .s0 | .s0, true => .s1
  | .s1, false => .s2 | .s1, true => .s3
  | .s3, false => .s4 | .s3, true => .s5
  | .s5, false => .s6 | .s5, true => .s5
  | .s6, false => .s7 | .s6, true => .s8
  | .s7, false => .s0 | .s7, true => .s9
  | s,   _     => s   -- unused on dead states s2, s4, s8, s9

/-- Helper: one-step inductive reduction for a live state `s` and bit `b`. -/
theorem step_live (s : State) (b : Bool) (k : Nat) (hk : k > 0)
    (h_par7 : (7 * (k % 2) + s.c7) % 2 = ((if k % 2 = 1 then 11 else 0) ^^^ s.m11) % 2)
    (h_par5 : (5 * (k % 2) + s.c5) % 2 = ((if k % 2 = 1 then 13 else 0) ^^^ s.m13) % 2)
    (hc7 : (7 * (k % 2) + s.c7) / 2 = (s.next b).c7)
    (hm11 : ((if k % 2 = 1 then 11 else 0) ^^^ s.m11) / 2 = (s.next b).m11)
    (hc5 : (5 * (k % 2) + s.c5) / 2 = (s.next b).c5)
    (hm13 : ((if k % 2 = 1 then 13 else 0) ^^^ s.m13) / 2 = (s.next b).m13)
    (ih : 7 * (k / 2) + (s.next b).c7 = clmul 11 (k / 2) ^^^ (s.next b).m11 →
          5 * (k / 2) + (s.next b).c5 = clmul 13 (k / 2) ^^^ (s.next b).m13)
    (h : 7 * k + s.c7 = clmul 11 k ^^^ s.m11) :
    5 * k + s.c5 = clmul 13 k ^^^ s.m13 := by
  have h7split := mul_bit_split 7 s.c7 k
  have h11split := clmul_xor_bit_split 11 s.m11 k hk
  rw [h7split, h11split, hc7, hm11, h_par7] at h
  have hq7 : 7 * (k / 2) + (s.next b).c7 = clmul 11 (k / 2) ^^^ (s.next b).m11 := by omega
  have hq5 := ih hq7
  rw [mul_bit_split 5 s.c5 k, clmul_xor_bit_split 13 s.m13 k hk, hc5, hm13, h_par5, hq5]

/-- Helper: dead-end states fail parity immediately for any `k > 0`. -/
theorem step_dead (s : State) (k : Nat) (hk : k > 0)
    (hne : (7 * (k % 2) + s.c7) % 2 ≠ ((if k % 2 = 1 then 11 else 0) ^^^ s.m11) % 2)
    (h : 7 * k + s.c7 = clmul 11 k ^^^ s.m11) :
    5 * k + s.c5 = clmul 13 k ^^^ s.m13 := by
  rw [mul_bit_split 7 s.c7 k, clmul_xor_bit_split 11 s.m11 k hk] at h
  omega

/-- Main state-pair invariant proved by strong binary induction on `k`. -/
theorem state_invariant :
    ∀ k : Nat, ∀ s : State,
      7 * k + s.c7 = clmul 11 k ^^^ s.m11 →
      5 * k + s.c5 = clmul 13 k ^^^ s.m13 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro s h
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.mul_zero, Nat.zero_add, clmul_zero, Nat.zero_xor] at h ⊢
      cases s <;> simp_all [State.c7, State.m11, State.c5, State.m13]
    · have hkpos : k > 0 := Nat.pos_of_ne_zero hk
      have hlt : k / 2 < k := Nat.div_lt_self hkpos (by omega)
      have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hmod with hb0 | hb1
      · cases s with
        | s2 | s4 | s8 | s9 =>
          exact step_dead _ k hkpos (by simp [hb0, State.c7, State.m11]) h
        | s0 | s1 | s3 | s5 | s6 | s7 =>
          exact step_live _ false k hkpos
            (by simp [hb0, State.c7, State.m11])
            (by simp [hb0, State.c5, State.m13])
            (by simp [hb0, State.c7, State.next])
            (by simp [hb0, State.m11, State.next])
            (by simp [hb0, State.c5, State.next])
            (by simp [hb0, State.m13, State.next])
            (ih (k / 2) hlt _) h
      · cases s with
        | s2 | s4 | s8 | s9 =>
          exact step_dead _ k hkpos (by simp [hb1, State.c7, State.m11]) h
        | s0 | s1 | s3 | s5 | s6 | s7 =>
          exact step_live _ true k hkpos
            (by simp [hb1, State.c7, State.m11])
            (by simp [hb1, State.c5, State.m13])
            (by simp [hb1, State.c7, State.next])
            (by simp [hb1, State.m11, State.next])
            (by simp [hb1, State.c5, State.next])
            (by simp [hb1, State.m13, State.next])
            (ih (k / 2) hlt _) h

/-- Implication `7k = C(11, k) → 5k = C(13, k)` for all `k : Nat`. -/
theorem seven_eleven_imp_five_thirteen (k : Nat) (h : 7 * k = clmul 11 k) :
    5 * k = clmul 13 k := by
  have h0 : 7 * k + State.s0.c7 = clmul 11 k ^^^ State.s0.m11 := by
    simpa [State.c7, State.m11] using h
  have h5 := state_invariant k .s0 h0
  simpa [State.c5, State.m13] using h5

/-- Main theorem: `A115770 ⊆ A391740`. -/
theorem A115770_subset_A391740 (k : Nat) (h : inA115770 k) : inA391740 k := by
  by_cases hk : k = 0
  · exact Or.inl hk
  · exact Or.inr ⟨13, by omega, (seven_eleven_imp_five_thirteen k h).symm⟩

-- Concrete sanity checks
example : inA115770 0 ∧ 5 * 0 = clmul 13 0 := by simp [inA115770, clmul]
example : inA115770 7 ∧ 5 * 7 = clmul 13 7 := by simp [inA115770, clmul]
example : inA115770 15 ∧ 5 * 15 = clmul 13 15 := by simp [inA115770, clmul]
example : inA115770 455 ∧ 5 * 455 = clmul 13 455 := by simp [inA115770, clmul]

#print axioms A115770_subset_A391740
