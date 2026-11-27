/-
Formalization of OEIS inclusion conjecture: A115774 ⊆ A115772
For all natural numbers i, if 15 * i = C(23, i), then 13 * i = C(21, i),
where C(a, k) is carryless multiplication in GF(2)[X] (OEIS A048720).

Dependencies: None (pure Lean 4 standard library `Init`, no Mathlib required).
Tested with: Lean 4.36.0.
-/

namespace OEIS_A115774_A115772

/-- Carryless (GF(2)[X]) multiplication `C(a, k)` (OEIS A048720). -/
def clmul (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let rest := clmul a ((k + 1) / 2)
    if (k + 1) % 2 = 1 then (2 * rest) ^^^ a else 2 * rest
termination_by n => n

/-- Single-bit recurrence for `clmul`, valid for all `n : Nat` (including `0`). -/
theorem clmul_eq_step (a n : Nat) :
    clmul a n = (2 * clmul a (n / 2)) ^^^ (if n % 2 = 1 then a else 0) := by
  cases n with
  | zero =>
    simp [clmul]
  | succ k =>
    rw [clmul]
    split <;> simp

/-- Helper: if `x.testBit 0 = y.testBit 0`, then `x % 2 = y % 2`. -/
theorem mod_two_eq_of_testBit_zero {x y : Nat} (h : x.testBit 0 = y.testBit 0) :
    x % 2 = y % 2 := by
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
  simp [hx, hy] at h ⊢

/-- Helper: `(u ^^^ (2 * v)) % 2 = u % 2`. -/
theorem xor_two_mul_mod_two (u v : Nat) : (u ^^^ (2 * v)) % 2 = u % 2 := by
  apply mod_two_eq_of_testBit_zero
  rw [Nat.testBit_xor, Nat.testBit_zero]
  simp

/-- Helper: `(u ^^^ (2 * v)) / 2 = (u / 2) ^^^ v`. -/
theorem xor_two_mul_div_two (u v : Nat) : (u ^^^ (2 * v)) / 2 = (u / 2) ^^^ v := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two]
  have hv : (2 * v).testBit (k + 1) = v.testBit k := by
    have h2 : 2 * v = v * 2 ^ 1 := by omega
    rw [h2, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    simp
  rw [hv]

/-- Helper: `u ^^^ (v ^^^ w) = (u ^^^ v) ^^^ w`. -/
theorem xor_assoc' (u v w : Nat) : u ^^^ (v ^^^ w) = (u ^^^ v) ^^^ w :=
  (Nat.xor_assoc u v w).symm

/-- State equation `c + a * i = m ^^^ C(b, i)` for remaining suffix `i`. -/
def eqState (a b c m i : Nat) : Prop :=
  c + a * i = m ^^^ clmul b i

/-- Termination equivalence: at `i = 0`, `eqState a b c m 0` is `c = m`. -/
theorem eqState_zero (a b c m : Nat) : eqState a b c m 0 ↔ c = m := by
  simp [eqState, clmul]

/-- Bitwise step decomposition of `eqState`. -/
theorem eqState_iff_step (a b c m i : Nat) :
    eqState a b c m i ↔
      ((c + (if i % 2 = 1 then a else 0)) % 2 =
        (m ^^^ (if i % 2 = 1 then b else 0)) % 2) ∧
      eqState a b
        ((c + (if i % 2 = 1 then a else 0)) / 2)
        ((m ^^^ (if i % 2 = 1 then b else 0)) / 2)
        (i / 2) := by
  unfold eqState
  have hlhs : c + a * i =
      (c + (if i % 2 = 1 then a else 0)) + 2 * (a * (i / 2)) := by
    split
    · have hi : i = 2 * (i / 2) + 1 := by omega
      have hmul : a * i = 2 * (a * (i / 2)) + a := by
        calc a * i = a * (2 * (i / 2) + 1) := congrArg (a * ·) hi
        _ = a * (2 * (i / 2)) + a * 1 := Nat.mul_add a (2 * (i / 2)) 1
        _ = 2 * (a * (i / 2)) + a := by rw [Nat.mul_left_comm, Nat.mul_one]
      omega
    · have hi : i = 2 * (i / 2) := by omega
      have hmul : a * i = 2 * (a * (i / 2)) := by
        calc a * i = a * (2 * (i / 2)) := congrArg (a * ·) hi
        _ = 2 * (a * (i / 2)) := Nat.mul_left_comm a 2 (i / 2)
      omega
  have hrhs : m ^^^ clmul b i =
      (m ^^^ (if i % 2 = 1 then b else 0)) ^^^ (2 * clmul b (i / 2)) := by
    rw [clmul_eq_step b i]
    rw [Nat.xor_comm (2 * clmul b (i / 2)) (if i % 2 = 1 then b else 0), xor_assoc']
  rw [hlhs, hrhs]
  constructor
  · intro h
    constructor
    · have hmod := congrArg (· % 2) h
      rw [xor_two_mul_mod_two] at hmod
      omega
    · have hdiv := congrArg (· / 2) h
      rw [xor_two_mul_div_two] at hdiv
      omega
  · rintro ⟨hmod, hdiv⟩
    have hRmod : ((m ^^^ (if i % 2 = 1 then b else 0)) ^^^ (2 * clmul b (i / 2))) % 2 =
        (m ^^^ (if i % 2 = 1 then b else 0)) % 2 :=
      xor_two_mul_mod_two _ _
    have hRdiv : ((m ^^^ (if i % 2 = 1 then b else 0)) ^^^ (2 * clmul b (i / 2))) / 2 =
        (m ^^^ (if i % 2 = 1 then b else 0)) / 2 ^^^ clmul b (i / 2) :=
      xor_two_mul_div_two _ _
    omega

/-- State transition function for `(carry, mask)` on input bit `bit : Bool`. -/
def step (a b : Nat) (s : Nat × Nat) (bit : Bool) : Nat × Nat :=
  if bit then ((s.1 + a) / 2, (s.2 ^^^ b) / 2)
  else (s.1 / 2, s.2 / 2)

/-- Parity condition `c % 2 == m % 2` (equivalent to output-bit match when `a, b` are odd). -/
def parityOk (s : Nat × Nat) : Bool :=
  s.1 % 2 == s.2 % 2

/-- The 14 reachable state pairs `((c1, m1), (c2, m2))`:
    8 active (parity-consistent) pairs followed by 6 boundary parity-violation pairs. -/
def R_list : List ((Nat × Nat) × (Nat × Nat)) :=
  [ -- 8 active (parity-consistent) pairs:
    ((0, 0),   (0, 0)),
    ((7, 11),  (6, 10)),
    ((3, 5),   (3, 5)),
    ((9, 9),   (8, 8)),
    ((4, 4),   (4, 4)),
    ((2, 2),   (2, 2)),
    ((1, 1),   (1, 1)),
    ((8, 10),  (7, 11)),
    -- 6 boundary failure (parity-violating in Eq1) pairs:
    ((1, 2),   (1, 2)),
    ((4, 5),   (3, 5)),
    ((8, 11),  (7, 10)),
    ((11, 14), (9, 15)),
    ((11, 14), (10, 15)),
    ((12, 15), (10, 14))
  ]

/-- Finite state-pair relation `R`. -/
abbrev R (s1 s2 : Nat × Nat) : Prop :=
  (s1, s2) ∈ R_list

/-- Check that `R_list` has exactly 14 state pairs. -/
theorem R_card : R_list.length = 14 := by decide

/-- Initial state pair `((0, 0), (0, 0))` belongs to `R`. -/
theorem R_init : R (0, 0) (0, 0) := by decide

/-- Closure of `R` under input bits `false` (0) and `true` (1) whenever Eq1 is parity-valid. -/
theorem R_closed :
    ∀ p ∈ R_list, parityOk p.1 = true → ∀ bit : Bool,
      (step 15 23 p.1 bit, step 13 21 p.2 bit) ∈ R_list := by
  decide

/-- Whenever Eq1 is parity-valid in `R`, Eq2 is also parity-valid. -/
theorem R_parity :
    ∀ p ∈ R_list, parityOk p.1 = true → parityOk p.2 = true := by
  decide

/-- Termination condition implication on `R`: `c1 = m1 → c2 = m2`. -/
theorem R_term :
    ∀ p ∈ R_list, p.1.1 = p.1.2 → p.2.1 = p.2.2 := by
  decide

/-- Helper: XOR with an odd constant flips parity. -/
theorem xor_odd_mod_two (m b : Nat) (hb : b % 2 = 1) :
    (m ^^^ b) % 2 = (m + 1) % 2 := by
  apply mod_two_eq_of_testBit_zero
  rw [Nat.testBit_xor]
  simp only [Nat.testBit_zero, hb]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have h1 : (m + 1) % 2 = 1 := by omega
    simp [hm, h1]
  · have h1 : (m + 1) % 2 = 0 := by omega
    simp [hm, h1]

/-- Parity equivalence for odd `(15, 23)`: output-bit match implies `parityOk`. -/
theorem odd_step_mod_two_15_23 (c m : Nat) (b : Bool)
    (h : (c + (if b then 15 else 0)) % 2 = (m ^^^ (if b then 23 else 0)) % 2) :
    parityOk (c, m) = true := by
  cases b with
  | false =>
    simp [parityOk] at h ⊢
    exact h
  | true =>
    have hm : (m ^^^ 23) % 2 = (m + 1) % 2 := xor_odd_mod_two m 23 rfl
    simp [parityOk] at h ⊢
    omega

/-- Parity equivalence for odd `(13, 21)`: `parityOk` implies output-bit match. -/
theorem odd_step_mod_two_13_21 (c m : Nat) (b : Bool)
    (h : parityOk (c, m) = true) :
    (c + (if b then 13 else 0)) % 2 = (m ^^^ (if b then 21 else 0)) % 2 := by
  cases b with
  | false =>
    simp [parityOk] at h ⊢
    exact h
  | true =>
    have hm : (m ^^^ 21) % 2 = (m + 1) % 2 := xor_odd_mod_two m 21 rfl
    simp [parityOk] at h ⊢
    omega

/-- Main binary induction over `i : Nat` using the 14-pair relation `R`. -/
theorem main_ind : ∀ i : Nat, ∀ s1 s2 : Nat × Nat,
    R s1 s2 →
    eqState 15 23 s1.1 s1.2 i →
    eqState 13 21 s2.1 s2.2 i
  | 0, s1, s2, hR, h1 => by
    rw [eqState_zero] at h1 ⊢
    exact R_term (s1, s2) hR h1
  | k + 1, s1, s2, hR, h1 => by
    rw [eqState_iff_step] at h1 ⊢
    rcases h1 with ⟨hmod1, hrec1⟩
    by_cases hbit : (k + 1) % 2 = 1
    · -- Input bit x = 1
      simp only [hbit, ↓reduceIte] at hmod1 hrec1 ⊢
      have hpar1 : parityOk s1 = true :=
        odd_step_mod_two_15_23 s1.1 s1.2 true hmod1
      have hpar2 : parityOk s2 = true :=
        R_parity (s1, s2) hR hpar1
      have hmod2 : (s2.1 + 13) % 2 = (s2.2 ^^^ 21) % 2 :=
        odd_step_mod_two_13_21 s2.1 s2.2 true hpar2
      have hR' : R (step 15 23 s1 true) (step 13 21 s2 true) :=
        R_closed (s1, s2) hR hpar1 true
      have hrec2 := main_ind ((k + 1) / 2) (step 15 23 s1 true) (step 13 21 s2 true) hR' hrec1
      exact ⟨hmod2, hrec2⟩
    · -- Input bit x = 0
      simp only [hbit, ↓reduceIte, Nat.add_zero, Nat.xor_zero] at hmod1 hrec1 ⊢
      have hpar1 : parityOk s1 = true :=
        odd_step_mod_two_15_23 s1.1 s1.2 false (by simpa using hmod1)
      have hpar2 : parityOk s2 = true :=
        R_parity (s1, s2) hR hpar1
      have hmod2 : s2.1 % 2 = s2.2 % 2 := by
        simpa using odd_step_mod_two_13_21 s2.1 s2.2 false hpar2
      have hR' : R (step 15 23 s1 false) (step 13 21 s2 false) :=
        R_closed (s1, s2) hR hpar1 false
      have hrec2 := main_ind ((k + 1) / 2) (step 15 23 s1 false) (step 13 21 s2 false) hR' hrec1
      exact ⟨hmod2, hrec2⟩
termination_by i => i

/-- Main Theorem (OEIS A115774 ⊆ A115772):
    For every natural number `i`, `15 * i = C(23, i)` implies `13 * i = C(21, i)`. -/
theorem a115774_subset_a115772 (i : Nat) (h : 15 * i = clmul 23 i) :
    13 * i = clmul 21 i := by
  have h1 : eqState 15 23 0 0 i := by
    simpa [eqState] using h
  have h2 : eqState 13 21 0 0 i :=
    main_ind i (0, 0) (0, 0) R_init h1
  simpa [eqState] using h2

/-- The inclusion is strict: `15 ∈ A115772 \ A115774`. -/
theorem a115774_strict_subset_a115772 :
    ∃ i : Nat, 13 * i = clmul 21 i ∧ 15 * i ≠ clmul 23 i := by
  refine ⟨15, ?_, ?_⟩ <;> simp [clmul]

end OEIS_A115774_A115772

#print axioms OEIS_A115774_A115772.a115774_subset_a115772
#print axioms OEIS_A115774_A115772.a115774_strict_subset_a115772
