/-
  Self-contained Lean 4 proof of A115876 ⊊ A115874:
    ∀ k : Nat, 41 * k = clmulGF2 105 k → 19 * k = clmulGF2 55 k
  and strictness witness k = 31:
    19 * 31 = clmulGF2 55 31 ∧ 41 * 31 ≠ clmulGF2 105 31.
-/

/-- Carryless multiplication in GF(2)[X] (OEIS A048720), LSB recursion on the second argument. -/
def clmul (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let n := k + 1
    let half := clmul a (n / 2)
    (if n % 2 = 1 then a else 0) ^^^ (2 * half)
termination_by k => k

/-- Explicit GF(2)[X] shift-XOR sum: ⨁_{i < n, bit i of b = 1} (a <<< i). -/
def clmulShift (a b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => clmulShift a b n ^^^ (if b.testBit n then a <<< n else 0)

/-- OEIS A048720(a, b) defined directly via shift-XOR over all bit positions i < b. -/
def clmulGF2 (a b : Nat) : Nat :=
  clmulShift a b b

/-- Helper: XOR splits cleanly into low bit (mod 2) and high bits (div 2). -/
theorem xor_mod_two (x y : Nat) : (x ^^^ y) % 2 = (x % 2) ^^^ (y % 2) := by
  have h : (x ^^^ y).testBit 0 = (x.testBit 0 ^^ y.testBit 0) := Nat.testBit_xor x y 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
  rcases Nat.mod_two_eq_zero_or_one (x ^^^ y) with hxy | hxy <;>
  simp_all

theorem xor_div_two (x y : Nat) : (x ^^^ y) / 2 = (x / 2) ^^^ (y / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_div_two, Nat.testBit_div_two]

theorem two_mul_xor_div_two (u v : Nat) : (2 * u ^^^ v) / 2 = u ^^^ (v / 2) := by
  rw [xor_div_two, Nat.mul_div_right u (by decide : 0 < 2)]

theorem two_mul_xor_mod_two (u v : Nat) : (2 * u ^^^ v) % 2 = v % 2 := by
  rw [xor_mod_two, Nat.mul_mod_right, Nat.zero_xor]

theorem clmul_zero (a : Nat) : clmul a 0 = 0 := by
  rw [clmul]

theorem clmul_succ (a k : Nat) :
    clmul a (k + 1) = (if (k + 1) % 2 = 1 then a else 0) ^^^ (2 * clmul a ((k + 1) / 2)) := by
  rw [clmul]

theorem two_mul_xor_two_mul (x y : Nat) : 2 * (x ^^^ y) = (2 * x) ^^^ (2 * y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    simp only [Nat.testBit_zero, xor_mod_two, Nat.mul_mod_right]
    decide
  | succ i' =>
    rw [Nat.testBit_succ, Nat.testBit_succ, xor_div_two,
        Nat.mul_div_right _ (by decide : 0 < 2),
        Nat.mul_div_right _ (by decide : 0 < 2),
        Nat.mul_div_right _ (by decide : 0 < 2)]

theorem clmulShift_step (a b n : Nat) :
    clmulShift a b (n + 1) =
      (if b.testBit 0 then a else 0) ^^^ (2 * clmulShift a (b / 2) n) := by
  induction n with
  | zero =>
    simp [clmulShift]
  | succ n' ih =>
    change (clmulShift a b (n' + 1) ^^^ (if b.testBit (n' + 1) then a <<< (n' + 1) else 0)) =
      (if b.testBit 0 then a else 0) ^^^
        (2 * (clmulShift a (b / 2) n' ^^^ (if (b / 2).testBit n' then a <<< n' else 0)))
    rw [ih, two_mul_xor_two_mul, Nat.xor_assoc]
    congr 1
    have hbit : b.testBit (n' + 1) = (b / 2).testBit n' := Nat.testBit_succ b n'
    rw [hbit]
    cases (b / 2).testBit n' with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hsh : a <<< (n' + 1) = 2 * (a <<< n') := by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.pow_succ,
            ← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ n') 2]
      rw [hsh]

theorem clmulShift_eq_of_lt_pow (a b n : Nat) (h : b < 2 ^ n) :
    clmul a b = clmulShift a b n := by
  induction n generalizing b with
  | zero =>
    have hb : b = 0 := by omega
    subst hb
    simp [clmul_zero, clmulShift]
  | succ n' ih =>
    cases b with
    | zero =>
      rw [clmul_zero, clmulShift_step]
      have h0 : (0 : Nat) / 2 = 0 := by decide
      rw [h0]
      have hlt : 0 < 2 ^ n' := Nat.two_pow_pos n'
      rw [← ih 0 hlt, clmul_zero]
      simp
    | succ b' =>
      rw [clmul_succ, clmulShift_step]
      have hdiv : (b' + 1) / 2 < 2 ^ n' := by
        rw [Nat.pow_succ] at h
        omega
      rw [ih ((b' + 1) / 2) hdiv]
      simp [Nat.testBit_zero]

theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n' ih =>
    rw [Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ n' := Nat.two_pow_pos n'
    omega

/-- Verification that `clmul` equals the GF(2)[X] shift-XOR definition `clmulGF2`. -/
theorem clmul_eq_clmulGF2 (a b : Nat) : clmul a b = clmulGF2 a b :=
  clmulShift_eq_of_lt_pow a b b (lt_two_pow_self b)

/-- The (carry, mask) state predicate: a * k + c = C(b, k) ⊕ m. -/
def P (a b c m k : Nat) : Prop :=
  a * k + c = clmul b k ^^^ m

/-- Exact one-bit LSB reduction for P(a, b, c, m, k) when k > 0. -/
theorem P_step_iff (a b c m k : Nat) (hk : k > 0) :
    P a b c m k ↔
      (c + a * (k % 2)) % 2 = (m ^^^ (if k % 2 = 1 then b else 0)) % 2 ∧
      P a b ((c + a * (k % 2)) / 2) ((m ^^^ (if k % 2 = 1 then b else 0)) / 2) (k / 2) := by
  cases k with
  | zero => contradiction
  | succ k' =>
    unfold P
    rw [clmul_succ]
    have hdiv : k' + 1 = 2 * ((k' + 1) / 2) + (k' + 1) % 2 := (Nat.div_add_mod (k' + 1) 2).symm
    have hlhs : a * (k' + 1) + c = 2 * (a * ((k' + 1) / 2)) + (c + a * ((k' + 1) % 2)) := by
      calc a * (k' + 1) + c
          = a * (2 * ((k' + 1) / 2) + (k' + 1) % 2) + c := by rw [← hdiv]
        _ = a * (2 * ((k' + 1) / 2)) + a * ((k' + 1) % 2) + c := by rw [Nat.mul_add]
        _ = 2 * (a * ((k' + 1) / 2)) + (c + a * ((k' + 1) % 2)) := by
            rw [Nat.mul_left_comm a 2]; omega
    have hrhs : ((if (k' + 1) % 2 = 1 then b else 0) ^^^ (2 * clmul b ((k' + 1) / 2))) ^^^ m =
        2 * clmul b ((k' + 1) / 2) ^^^ (m ^^^ (if (k' + 1) % 2 = 1 then b else 0)) := by
      rw [Nat.xor_comm (if (k' + 1) % 2 = 1 then b else 0),
          Nat.xor_assoc,
          Nat.xor_comm (if (k' + 1) % 2 = 1 then b else 0) m]
    rw [hlhs, hrhs]
    constructor
    · intro h
      have hmod := congrArg (· % 2) h
      have hdiv2 := congrArg (· / 2) h
      rw [Nat.mul_add_mod, two_mul_xor_mod_two] at hmod
      rw [Nat.mul_add_div (by decide : 0 < 2), two_mul_xor_div_two] at hdiv2
      exact ⟨hmod, hdiv2⟩
    · rintro ⟨hmod, hdiv2⟩
      have hL : 2 * (a * ((k' + 1) / 2)) + (c + a * ((k' + 1) % 2)) =
          2 * (a * ((k' + 1) / 2) + (c + a * ((k' + 1) % 2)) / 2) +
            (c + a * ((k' + 1) % 2)) % 2 := by omega
      have hR : 2 * clmul b ((k' + 1) / 2) ^^^ (m ^^^ (if (k' + 1) % 2 = 1 then b else 0)) =
          2 * ((2 * clmul b ((k' + 1) / 2) ^^^ (m ^^^ (if (k' + 1) % 2 = 1 then b else 0))) / 2) +
            (2 * clmul b ((k' + 1) / 2) ^^^ (m ^^^ (if (k' + 1) % 2 = 1 then b else 0))) % 2 :=
        (Nat.div_add_mod _ 2).symm
      rw [two_mul_xor_div_two, two_mul_xor_mod_two] at hR
      rw [hL, hR, hmod, hdiv2]

/-- Parity obstruction: when a and b are odd, c % 2 ≠ m % 2 implies ¬ P a b c m k for all k. -/
theorem not_P_of_parity_ne {a b c m k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hpar : c % 2 ≠ m % 2) : ¬ P a b c m k := by
  cases k with
  | zero =>
    unfold P
    rw [clmul_zero]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_xor]
    intro h; exact hpar (congrArg (· % 2) h)
  | succ k' =>
    rw [P_step_iff a b c m (k' + 1) (Nat.succ_pos k')]
    rintro ⟨hmod, _⟩
    rcases Nat.mod_two_eq_zero_or_one (k' + 1) with hx | hx
    · simp only [hx, Nat.mul_zero, Nat.add_zero, show ¬(0 = 1) by decide, ↓reduceIte,
        Nat.xor_zero] at hmod
      exact hpar hmod
    · simp only [hx, Nat.mul_one, ↓reduceIte] at hmod
      rw [xor_mod_two, hb] at hmod
      have h1 : (c + a) % 2 = (c % 2 + 1) % 2 := by omega
      rw [h1] at hmod
      rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
      simp_all

/-- Transition function for a single (carry, mask) state on input bit x ∈ {0, 1}. -/
def step (a b : Nat) (s : Nat × Nat) (x : Bool) : Nat × Nat :=
  let (c, m) := s
  if x then ((c + a) / 2, (m ^^^ b) / 2) else (c / 2, m / 2)

/-- The 31 parity-consistent dead states of DFA(41, 105). -/
def deadStates : List (Nat × Nat) :=
  [ (1, 3), (2, 6), (3, 5), (3, 7), (5, 13), (6, 12), (6, 14), (7, 11),
    (8, 10), (10, 26), (11, 25), (11, 27), (12, 24), (12, 28), (13, 29),
    (15, 23), (16, 20), (16, 22), (21, 53), (21, 55), (22, 54), (23, 51),
    (24, 48), (25, 57), (26, 56), (26, 58), (28, 62), (31, 47), (32, 44),
    (33, 41), (36, 34) ]

/-- The 9 live coupled state pairs ((c1, m1), (c2, m2)) linking DFA(41, 105) to DFA(19, 55). -/
def livePairs : List ((Nat × Nat) × (Nat × Nat)) :=
  [ ((0, 0),   (0, 0)),
    ((1, 1),   (0, 0)),
    ((2, 2),   (1, 1)),
    ((4, 4),   (2, 2)),
    ((8, 8),   (4, 4)),
    ((17, 17), (8, 8)),
    ((20, 52), (9, 27)),
    ((30, 46), (14, 22)),
    ((35, 35), (16, 16)) ]

/-- Decidable check that every dead state has c ≠ m and transitions either to parity mismatch or deadStates. -/
def checkDead : Bool :=
  deadStates.all fun s =>
    s.1 != s.2 &&
    [false, true].all fun x =>
      let ns := step 41 105 s x
      (ns.1 % 2 != ns.2 % 2) || deadStates.contains ns

theorem checkDead_ok : checkDead = true := by decide

/-- Decidable check for the 9 live coupled pairs:
    (1) parity consistency on both sides,
    (2) terminal implication c1 = m1 → c2 = m2,
    (3) every bit transition either leads s1 to parity mismatch / deadStates,
        or leads (s1', s2') into livePairs. -/
def checkLive : Bool :=
  livePairs.all fun (s1, s2) =>
    (s1.1 % 2 == s1.2 % 2) &&
    (s2.1 % 2 == s2.2 % 2) &&
    (!(s1.1 == s1.2) || (s2.1 == s2.2)) &&
    [false, true].all fun x =>
      let ns1 := step 41 105 s1 x
      let ns2 := step 19 55 s2 x
      (ns1.1 % 2 != ns1.2 % 2) ||
      deadStates.contains ns1 ||
      livePairs.contains (ns1, ns2)

theorem checkLive_ok : checkLive = true := by decide

/-- Helper relating step to the arithmetic expressions in P_step_iff. -/
theorem step_eq_fst (a b c m n : Nat) :
    (step a b (c, m) (decide (n % 2 = 1))).1 = (c + a * (n % 2)) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [step, h]

theorem step_eq_snd (a b c m n : Nat) :
    (step a b (c, m) (decide (n % 2 = 1))).2 = (m ^^^ (if n % 2 = 1 then b else 0)) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [step, h]

/-- Lemma A: No dead state in deadStates can satisfy P 41 105 for any k. -/
theorem dead_impossible (k : Nat) :
    ∀ s ∈ deadStates, ¬ P 41 105 s.1 s.2 k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro s hs
    have hcheck : s.1 != s.2 ∧
        ∀ x ∈ [false, true],
          let ns := step 41 105 s x
          (ns.1 % 2 != ns.2 % 2) || deadStates.contains ns := by
      have h := List.all_eq_true.mp checkDead_ok s hs
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      exact h
    cases k with
    | zero =>
      unfold P
      rw [clmul_zero]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_xor]
      intro heq
      have hne : s.1 ≠ s.2 := by simpa using hcheck.1
      exact hne heq
    | succ k' =>
      rw [P_step_iff 41 105 s.1 s.2 (k' + 1) (Nat.succ_pos k')]
      rintro ⟨_, hnext⟩
      let x := decide ((k' + 1) % 2 = 1)
      have hx : x ∈ [false, true] := by cases x <;> simp
      have htr := hcheck.2 x hx
      rw [← step_eq_fst 41 105 s.1 s.2 (k' + 1),
          ← step_eq_snd 41 105 s.1 s.2 (k' + 1)] at hnext
      simp only [Bool.or_eq_true, bne_iff_ne, List.contains_eq_mem, decide_eq_true_eq] at htr
      cases htr with
      | inl hpar =>
        exact not_P_of_parity_ne (by decide) (by decide) hpar hnext
      | inr hmem =>
        exact ih ((k' + 1) / 2) (Nat.div_lt_self (Nat.succ_pos k') (by decide)) _ hmem hnext

/-- Lemma B: For every live coupled pair (s1, s2), P 41 105 s1 k implies P 19 55 s2 k. -/
theorem live_implies (k : Nat) :
    ∀ p ∈ livePairs, P 41 105 p.1.1 p.1.2 k → P 19 55 p.2.1 p.2.2 k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro ⟨s1, s2⟩ hp hP1
    have hcheck := List.all_eq_true.mp checkLive_ok (s1, s2) hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, beq_eq_false_iff_ne, bne_iff_ne, List.all_eq_true,
      List.contains_eq_mem, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨hs1par, hs2par⟩, hterm⟩, htrans⟩ := hcheck
    cases k with
    | zero =>
      unfold P at hP1 ⊢
      rw [clmul_zero] at hP1 ⊢
      simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_xor] at hP1 ⊢
      cases hterm with
      | inl hne => exact absurd hP1 hne
      | inr heq => exact heq
    | succ k' =>
      rw [P_step_iff 41 105 s1.1 s1.2 (k' + 1) (Nat.succ_pos k')] at hP1
      rw [P_step_iff 19 55 s2.1 s2.2 (k' + 1) (Nat.succ_pos k')]
      obtain ⟨_, hP1next⟩ := hP1
      let x := decide ((k' + 1) % 2 = 1)
      have hx : x ∈ [false, true] := by cases x <;> simp
      have htr := htrans x hx
      rw [← step_eq_fst 41 105 s1.1 s1.2 (k' + 1),
          ← step_eq_snd 41 105 s1.1 s1.2 (k' + 1)] at hP1next
      have hmod2 : (s2.1 + 19 * ((k' + 1) % 2)) % 2 =
          (s2.2 ^^^ (if (k' + 1) % 2 = 1 then 55 else 0)) % 2 := by
        rcases Nat.mod_two_eq_zero_or_one (k' + 1) with h0 | h1
        · simp [h0, hs2par]
        · simp only [h1, Nat.mul_one, ↓reduceIte]
          rw [xor_mod_two]
          rcases Nat.mod_two_eq_zero_or_one s2.1 with hc | hc <;>
          rcases Nat.mod_two_eq_zero_or_one s2.2 with hm | hm <;>
          simp_all <;> omega
      cases htr with
      | inl hdead =>
        cases hdead with
        | inl hpar =>
          exact absurd hP1next (not_P_of_parity_ne (by decide) (by decide) hpar)
        | inr hmem =>
          exact absurd hP1next (dead_impossible ((k' + 1) / 2) _ hmem)
      | inr hlive =>
        refine ⟨hmod2, ?_⟩
        rw [← step_eq_fst 19 55 s2.1 s2.2 (k' + 1),
            ← step_eq_snd 19 55 s2.1 s2.2 (k' + 1)]
        exact ih ((k' + 1) / 2) (Nat.div_lt_self (Nat.succ_pos k') (by decide)) _ hlive hP1next

/-- Main Theorem (stated directly against the GF(2)[X] shift-XOR definition clmulGF2):
    A115876 ⊆ A115874. -/
theorem A115876_subset_A115874 :
    ∀ k : Nat, 41 * k = clmulGF2 105 k → 19 * k = clmulGF2 55 k := by
  intro k hk
  rw [← clmul_eq_clmulGF2] at hk ⊢
  have h0 : ((0, 0), (0, 0)) ∈ livePairs := by decide
  have hP1 : P 41 105 0 0 k := by
    unfold P; simpa [Nat.add_zero, Nat.xor_zero] using hk
  have hP2 := live_implies k ((0, 0), (0, 0)) h0 hP1
  unfold P at hP2
  simpa [Nat.add_zero, Nat.xor_zero] using hP2

/-- Strictness Witness: 31 ∈ A115874 \ A115876 (with arithmetic values). -/
theorem strictness_witness_31 :
    19 * 31 = 589 ∧ clmulGF2 55 31 = 589 ∧
    41 * 31 = 1271 ∧ clmulGF2 105 31 = 1223 ∧
    19 * 31 = clmulGF2 55 31 ∧ 41 * 31 ≠ clmulGF2 105 31 := by
  decide

#print axioms A115876_subset_A115874
#print axioms strictness_witness_31
