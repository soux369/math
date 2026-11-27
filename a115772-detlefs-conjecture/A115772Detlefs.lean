/-
Analysis and Formalization of Gary Detlefs's 2010 Conjecture on OEIS A115772:
  Conjecture: { i : 13 * i = C(21, i) } = { x ||| (4 * x) : x ≥ 0 }

Result proved in this file:
  1. The inclusion A115772 ⊆ { x ||| (4 * x) : x ≥ 0 } is TRUE
     (`a115772_subset_or4x`), proved via a 24-pair finite relation between
     the (carry, mask) automaton for (13, 21) and the 4-bit subset DFA for
     { x ||| (4 * x) }, verified by `decide` + binary induction.
  2. The reverse inclusion (and hence Detlefs's equality conjecture) is FALSE
     (`detlefs_conjecture_false`), disproved by the smallest counterexample
     i = 325 = 65 ||| (4 * 65), where 13 * 325 = 4225 ≠ 4097 = C(21, 325).
  3. Thus A115772 ⊊ { x ||| (4 * x) : x ≥ 0 } (`a115772_strict_subset_or4x`).

Dependencies: None (pure Lean 4 standard library `Init`, no Mathlib required).
Tested with: Lean 4.36.0.
-/

namespace OEIS_A115772_Detlefs

/-! ### 1. Carryless multiplication `clmul` (OEIS A048720) and `(carry, mask)` state -/

/-- Carryless (GF(2)[X]) multiplication `C(a, k)` (OEIS A048720). -/
def clmul (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let rest := clmul a ((k + 1) / 2)
    if (k + 1) % 2 = 1 then (2 * rest) ^^^ a else 2 * rest
termination_by n => n

/-- Single-bit recurrence for `clmul`, valid for all `n : Nat`. -/
theorem clmul_eq_step (a n : Nat) :
    clmul a n = (2 * clmul a (n / 2)) ^^^ (if n % 2 = 1 then a else 0) := by
  cases n with
  | zero => simp [clmul]
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

/-- State transition for `(carry, mask)` on `(13, 21)`. -/
def stepEq (s : Nat × Nat) (bit : Bool) : Nat × Nat :=
  if bit then ((s.1 + 13) / 2, (s.2 ^^^ 21) / 2)
  else (s.1 / 2, s.2 / 2)

/-- Parity condition `c % 2 == m % 2` for `(13, 21)`. -/
def parityOk (s : Nat × Nat) : Bool :=
  s.1 % 2 == s.2 % 2

/-- Output-bit match for odd `(13, 21)` implies `parityOk`. -/
theorem odd_step_mod_two_13_21 (c m : Nat) (b : Bool)
    (h : (c + (if b then 13 else 0)) % 2 = (m ^^^ (if b then 21 else 0)) % 2) :
    parityOk (c, m) = true := by
  cases b with
  | false =>
    simp [parityOk] at h ⊢
    exact h
  | true =>
    have hm : (m ^^^ 21) % 2 = (m + 1) % 2 := xor_odd_mod_two m 21 rfl
    simp [parityOk] at h ⊢
    omega

/-! ### 2. Subset DFA for `{ x ||| (4 * x) : x ≥ 0 }` and backward witness construction -/

/-- A subset of `{0,1}²` representing reachable NFA states `(x_{j-2}, x_{j-1})`,
    encoded as `(has00, has01, has10, has11)`. -/
abbrev DFAState := Bool × Bool × Bool × Bool

/-- Membership test `(b0, b1) ∈ S` for `S : DFAState`. -/
def memDFA (p : Bool × Bool) (S : DFAState) : Bool :=
  match p with
  | (false, false) => S.1
  | (false, true)  => S.2.1
  | (true,  false) => S.2.2.1
  | (true,  true)  => S.2.2.2

/-- Deterministic transition on input bit `ibit` for the NFA `i_j = x_j || x_{j-2}`.
    From `(b0, b1) ∈ S`, choosing `xj` with `(xj || b0) == ibit` moves to `(b1, xj)`. -/
def stepDFA (S : DFAState) (ibit : Bool) : DFAState :=
  let reach (b1 xj : Bool) : Bool :=
    (memDFA (false, b1) S && ((xj || false) == ibit)) ||
    (memDFA (true,  b1) S && ((xj || true)  == ibit))
  (reach false false, reach false true, reach true false, reach true true)

/-- Exact specification of `stepDFA` (proved for all 16×2×4 cases by `decide`). -/
theorem stepDFA_spec :
    ∀ (s00 s01 s10 s11 ibit b0' b1' : Bool),
      memDFA (b0', b1') (stepDFA (s00, s01, s10, s11) ibit) = true →
      ∃ b0 : Bool,
        memDFA (b0, b0') (s00, s01, s10, s11) = true ∧
        (b1' || b0) = ibit := by
  decide

/-- Generalized right-hand side predicate with pending shifted bits `(b0, b1)`:
    `i = x ||| (4 * x) ||| b0·1 ||| b1·2`. -/
def hasOr4x (b0 b1 : Bool) (i : Nat) : Prop :=
  ∃ x : Nat, i = x ||| (4 * x) ||| (if b0 then 1 else 0) ||| (if b1 then 2 else 0)

/-- Base case: `hasOr4x false false 0` holds via `x = 0`. -/
theorem hasOr4x_zero : hasOr4x false false 0 :=
  ⟨0, by decide⟩

/-- Helper: bit 0 of `2 * x + (if xj then 1 else 0)` is `xj`. -/
theorem testBit_two_mul_add_bit_zero (x : Nat) (xj : Bool) :
    (2 * x + (if xj then 1 else 0)).testBit 0 = xj := by
  cases xj <;> simp [Nat.testBit_zero] <;> omega

/-- Helper: bit `m + 1` of `2 * x + (if xj then 1 else 0)` is `x.testBit m`. -/
theorem testBit_two_mul_add_bit_succ (x : Nat) (xj : Bool) (m : Nat) :
    (2 * x + (if xj then 1 else 0)).testBit (m + 1) = x.testBit m := by
  rw [Nat.testBit_succ]
  have hdiv : (2 * x + (if xj then 1 else 0)) / 2 = x := by
    cases xj <;> simp <;> omega
  rw [hdiv]

/-- Helper: `testBit` of `4 * (2 * x + (if xj then 1 else 0))` at `m + 1`. -/
theorem testBit_four_mul_step (x : Nat) (xj : Bool) (m : Nat) :
    (4 * (2 * x + (if xj then 1 else 0))).testBit (m + 1) =
      ((4 * x) ||| (if xj then 2 else 0)).testBit m := by
  rw [Nat.testBit_succ, Nat.testBit_or]
  have hdiv : 4 * (2 * x + (if xj then 1 else 0)) / 2 =
      4 * x + (if xj then 2 else 0) := by
    cases xj <;> simp <;> omega
  rw [hdiv]
  cases m with
  | zero =>
    cases xj <;> simp [Nat.testBit_zero] <;> omega
  | succ m' =>
    cases m' with
    | zero =>
      cases xj <;> simp [Nat.testBit_succ, Nat.testBit_zero] <;> omega
    | succ m'' =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have hd1 : (4 * x + (if xj then 2 else 0)) / 2 / 2 = x := by
        cases xj <;> simp <;> omega
      have hd2 : (4 * x) / 2 / 2 = x := by omega
      have hd3 : (if xj then 2 else 0).testBit (m'' + 1 + 1) = false := by
        cases xj <;> simp [Nat.testBit_succ]
      rw [hd1, hd2, hd3]
      simp

/-- Backward step lemma: from `hasOr4x b1 xj (i / 2)` and `(xj || b0) = (i % 2 == 1)`,
    we construct `hasOr4x b0 b1 i` by setting `x' = 2 * x + xj`. -/
theorem hasOr4x_step (b0 b1 xj : Bool) (i : Nat)
    (hbit : (xj || b0) = (i % 2 == 1))
    (hq : hasOr4x b1 xj (i / 2)) :
    hasOr4x b0 b1 i := by
  rcases hq with ⟨x, hx⟩
  refine ⟨2 * x + (if xj then 1 else 0), ?_⟩
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
    rw [testBit_two_mul_add_bit_zero]
    have h4 : (4 * (2 * x + (if xj then 1 else 0))).testBit 0 = false := by
      simp [Nat.testBit_zero]; omega
    have hb0 : (if b0 then 1 else 0).testBit 0 = b0 := by cases b0 <;> decide
    have hb1 : (if b1 then 2 else 0).testBit 0 = false := by cases b1 <;> decide
    have hi0 : i.testBit 0 = (i % 2 == 1) := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    rw [h4, hb0, hb1, hi0, ← hbit]
    cases xj <;> cases b0 <;> rfl
  | succ m =>
    rw [Nat.testBit_succ, hx]
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
    rw [testBit_two_mul_add_bit_succ, testBit_four_mul_step, Nat.testBit_or]
    have hb0 : (if b0 then 1 else 0).testBit (m + 1) = false := by
      cases b0 <;> simp [Nat.testBit_succ]
    have hb1 : (if b1 then 2 else 0).testBit (m + 1) = (if b1 then 1 else 0).testBit m := by
      cases b1 <;> simp [Nat.testBit_succ]
    rw [hb0, hb1]
    cases x.testBit m <;>
    cases (4 * x).testBit m <;>
    cases (if b1 then 1 else 0).testBit m <;>
    cases (if xj then 2 else 0).testBit m <;>
    rfl

/-! ### 3. The 24-pair finite relation `R` and `decide` verification -/

/-- All 24 reachable pairs `((c, m), S)` from `((0, 0), {(0, 0)})`:
    16 active (parity-consistent in Eq(13,21)) pairs + 8 boundary failure pairs. -/
def R_list : List ((Nat × Nat) × DFAState) :=
  [ -- 16 active (parity-consistent) pairs:
    ((0, 0),   (true,  false, false, false)),
    ((1, 1),   (true,  false, false, false)),
    ((2, 2),   (true,  false, false, false)),
    ((3, 3),   (true,  false, false, false)),
    ((3, 5),   (false, false, true,  false)),
    ((4, 4),   (true,  false, true,  false)),
    ((5, 7),   (false, false, true,  false)),
    ((6, 6),   (true,  false, true,  false)),
    ((6, 10),  (false, true,  false, false)),
    ((7, 11),  (false, true,  false, false)),
    ((8, 8),   (true,  true,  false, false)),
    ((9, 9),   (true,  true,  false, false)),
    ((9, 15),  (false, false, false, true)),
    ((10, 14), (false, true,  false, true)),
    ((11, 13), (false, false, true,  true)),
    ((12, 12), (true,  true,  true,  true)),
    -- 8 boundary failure (parity-violating in Eq(13,21)) pairs:
    ((1, 2),   (false, false, false, false)),
    ((2, 3),   (false, false, false, false)),
    ((4, 7),   (false, false, false, false)),
    ((5, 6),   (false, false, false, false)),
    ((7, 10),  (false, true,  false, false)),
    ((8, 11),  (false, true,  false, false)),
    ((10, 15), (false, false, false, true)),
    ((11, 14), (false, true,  false, true))
  ]

/-- Finite state-pair relation `R`. -/
abbrev R (s : Nat × Nat) (S : DFAState) : Prop :=
  (s, S) ∈ R_list

/-- Check that `R_list` has exactly 24 state pairs. -/
theorem R_card : R_list.length = 24 := by decide

/-- Initial state pair `((0, 0), {(0, 0)})` belongs to `R`. -/
theorem R_init : R (0, 0) (true, false, false, false) := by decide

/-- Closure of `R` under input bits `false` (0) and `true` (1) whenever `(13, 21)` is parity-valid. -/
theorem R_closed :
    ∀ p ∈ R_list, parityOk p.1 = true → ∀ bit : Bool,
      (stepEq p.1 bit, stepDFA p.2 bit) ∈ R_list := by
  decide

/-- Termination condition implication on `R`: `c = m → (0, 0) ∈ S`. -/
theorem R_term :
    ∀ p ∈ R_list, p.1.1 = p.1.2 → memDFA (false, false) p.2 = true := by
  decide

/-! ### 4. Binary induction and main theorems -/

/-- Binary induction on `i : Nat`: for any `(s, S) ∈ R`, if `eqState 13 21 s.1 s.2 i`,
    then some state `(b0, b1) ∈ S` realizes `hasOr4x b0 b1 i`. -/
theorem main_ind : ∀ i : Nat, ∀ s : Nat × Nat, ∀ S : DFAState,
    R s S →
    eqState 13 21 s.1 s.2 i →
    ∃ p : Bool × Bool, memDFA p S = true ∧ hasOr4x p.1 p.2 i
  | 0, s, S, hR, h1 => by
    rw [eqState_zero] at h1
    exact ⟨(false, false), R_term (s, S) hR h1, hasOr4x_zero⟩
  | k + 1, s, S, hR, h1 => by
    rw [eqState_iff_step] at h1
    rcases h1 with ⟨hmod1, hrec1⟩
    by_cases hbit : (k + 1) % 2 = 1
    · -- Input bit = 1 (true)
      simp only [hbit, ↓reduceIte] at hmod1 hrec1
      have hpar : parityOk s = true :=
        odd_step_mod_two_13_21 s.1 s.2 true hmod1
      have hR' : R (stepEq s true) (stepDFA S true) :=
        R_closed (s, S) hR hpar true
      have hih := main_ind ((k + 1) / 2) (stepEq s true) (stepDFA S true) hR' hrec1
      rcases hih with ⟨⟨b0', b1'⟩, hmem', hOr'⟩
      rcases S with ⟨s00, s01, s10, s11⟩
      rcases stepDFA_spec s00 s01 s10 s11 true b0' b1' hmem' with ⟨b0, hmem, hor⟩
      refine ⟨(b0, b0'), hmem, hasOr4x_step b0 b0' b1' (k + 1) ?_ hOr'⟩
      simp [hbit, hor]
    · -- Input bit = 0 (false)
      simp only [hbit, ↓reduceIte, Nat.add_zero, Nat.xor_zero] at hmod1 hrec1
      have hpar : parityOk s = true :=
        odd_step_mod_two_13_21 s.1 s.2 false (by simpa using hmod1)
      have hR' : R (stepEq s false) (stepDFA S false) :=
        R_closed (s, S) hR hpar false
      have hih := main_ind ((k + 1) / 2) (stepEq s false) (stepDFA S false) hR' hrec1
      rcases hih with ⟨⟨b0', b1'⟩, hmem', hOr'⟩
      rcases S with ⟨s00, s01, s10, s11⟩
      rcases stepDFA_spec s00 s01 s10 s11 false b0' b1' hmem' with ⟨b0, hmem, hor⟩
      refine ⟨(b0, b0'), hmem, hasOr4x_step b0 b0' b1' (k + 1) ?_ hOr'⟩
      have hmod0 : (k + 1) % 2 = 0 := by omega
      simp [hmod0, hor]
termination_by i => i

/-- Direction 1 (TRUE): Every element of A115772 has the form `x ||| (4 * x)`. -/
theorem a115772_subset_or4x (i : Nat) (h : 13 * i = clmul 21 i) :
    ∃ x : Nat, i = x ||| (4 * x) := by
  have h1 : eqState 13 21 0 0 i := by simpa [eqState] using h
  rcases main_ind i (0, 0) (true, false, false, false) R_init h1 with ⟨⟨b0, b1⟩, hmem, hOr⟩
  cases b0 <;> cases b1 <;> simp [memDFA] at hmem
  rcases hOr with ⟨x, hx⟩
  exact ⟨x, by simpa using hx⟩

/-- Counterexample `i = 325 = 65 ||| (4 * 65)`: `325 ∈ { x ||| 4x }` but `325 ∉ A115772`. -/
theorem counterexample_325 :
    (∃ x : Nat, 325 = x ||| (4 * x)) ∧ 13 * 325 ≠ clmul 21 325 := by
  constructor
  · exact ⟨65, by decide⟩
  · simp [clmul]

/-- Disproof of Gary Detlefs's 2010 conjecture: the equality fails at `i = 325`. -/
theorem detlefs_conjecture_false :
    ¬ (∀ i : Nat, 13 * i = clmul 21 i ↔ ∃ x : Nat, i = x ||| (4 * x)) := by
  intro h
  rcases counterexample_325 with ⟨hR, hL⟩
  exact hL ((h 325).mpr hR)

/-- Combined result: strict inclusion `A115772 ⊊ { x ||| (4 * x) : x ≥ 0 }`. -/
theorem a115772_strict_subset_or4x :
    (∀ i : Nat, 13 * i = clmul 21 i → ∃ x : Nat, i = x ||| (4 * x)) ∧
    (∃ i : Nat, (∃ x : Nat, i = x ||| (4 * x)) ∧ 13 * i ≠ clmul 21 i) :=
  ⟨a115772_subset_or4x, ⟨325, counterexample_325⟩⟩

end OEIS_A115772_Detlefs

#print axioms OEIS_A115772_Detlefs.a115772_subset_or4x
#print axioms OEIS_A115772_Detlefs.detlefs_conjecture_false
#print axioms OEIS_A115772_Detlefs.a115772_strict_subset_or4x
