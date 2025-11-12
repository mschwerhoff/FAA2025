import Mathlib.Tactic
set_option autoImplicit false
set_option tactic.hygienic false


--# Problem 1: Sum of Odd Numbers
 def SumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => SumOdd n + (2*n + 1)

theorem P1 (n : ℕ) : SumOdd (n) = n^2 := by
  induction' n with n ih
  · -- Base case: n = 0
    unfold SumOdd
    rfl
  · -- Inductive step: n → n+1
    unfold SumOdd
    rw [ih]
    ring

--# Problem 2: Factorial Parity
 def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

def isEven (n : ℕ) : Prop := ∃ k, n = 2*k

-- Solution 1: Using standard induction with case split
theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  · intro h
    by_contra hn
    have : n = 0 ∨ n = 1 := by omega
    cases this
    · rw [h_1, factorial] at h; obtain ⟨k, hk⟩ := h; omega
    · rw [h_1, factorial, factorial] at h; obtain ⟨k, hk⟩ := h; omega
  · intro h
    induction' n with n ih
    · omega
    · by_cases h2 : n ≥ 2
      · have : isEven (n)! := ih h2
        obtain ⟨k, hk⟩ := this
        unfold factorial
        use (n + 1) * k
        rw [hk]
        ring
      · have : n = 1 := by omega
        rw [this]
        repeat rw[factorial]
        use 1

-- Solution 2: Using Nat.le_induction (induction from base n=2)
theorem P2' (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  · intro h
    by_contra hn
    have : n = 0 ∨ n = 1 := by omega
    cases this with
    | inl h0 =>
      rw [h0, factorial] at h
      obtain ⟨k, hk⟩ := h
      omega
    | inr h1 =>
      rw [h1, factorial, factorial] at h
      obtain ⟨k, hk⟩ := h
      omega
  · intro h
    induction' n, h using Nat.le_induction with n ih
    · use 1; rw [factorial, factorial, factorial];
    · obtain ⟨k, hk⟩ := a
      rw [factorial, hk]
      use (n + 1) * k
      ring
--# Problem 3: 3^n > n^2 for n > 0
 theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by
  intro n hn
  induction' n, hn using Nat.le_induction with n ih
  · norm_num
  · by_cases h : n ≥ 2
    · calc 3^(n+1)
          = 3 * 3^n := by ring
          _ > 3 * n^2 := by nlinarith [ih]
          _ = n^2 + 2*n^2 := by ring
          _ ≥ n^2 + 2*n + 1 := by nlinarith [sq_nonneg n, h]
          _ = (n + 1)^2 := by ring
    · have : n = 1 := by omega
      rw [this]
      norm_num

--# Problem 4: g(n) = g(n/2) + 1, prove g(n) ≤ log₂(n) + 1

-- Definition using if-then-else (recommended)
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

-- Alternative definition using pattern matching
def g' : ℕ → ℕ
  | 0 => 0
  | n + 1 => g' ((n + 1) / 2) + 1

-- Solution 1: Using strong induction
theorem P4 (n : ℕ) : g n ≤ Nat.log 2 n + 1 := by
  induction' n using Nat.strong_induction_on with n ih
  unfold g
  if h : n ≤ 1 then
    split
    · simp  -- n = 0
    · have : n = 1 := by omega
      rw [this, g]
      simp
  else
    split <;> simp_all
    have h_pos : n > 1 := by omega
    have h_div : n / 2 < n := by omega
    specialize ih (n / 2) h_div
    grw [ih]
    rw [Nat.log_div_base 2 n]
    rw [Nat.sub_add_cancel]
    apply Nat.log_pos <;> omega

-- Solution 2: Using Nat.div2Induction
theorem P4' (n : ℕ) : g n ≤ Nat.log 2 n + 1 := by
  induction n using Nat.div2Induction
  unfold g
  if h : n_1 = 0 ∨ n_1 = 1 then
    cases h <;> simp_all [g]
  else
    simp at a
    split <;> simp_all
    have n_pos : 0 < n_1 := by omega
    grw [a n_pos]
    rw [Nat.sub_add_cancel]
    apply Nat.log_pos <;> omega

--# Problem 5: f(n) = 2*f(n-1) - f(n-2) + 2, prove f(n) = n^2 - n + 1

-- Solution 1: Define f : ℕ → ℕ (staying in naturals)
def f : ℕ → ℕ
  | 0   => 1
  | 1   => 1
  | n+2 => 2*f (n+1) - f (n) + 2

theorem P5 (n : ℕ) : f n = n^2 - n + 1 := by
  induction n using Nat.twoStepInduction
  · unfold f; ring
  · unfold f; ring
  · unfold f
    rw [a, a_1, add_sq n_1 2, add_sq n_1 1]
    simp; ring_nf
    have h : n_1 ≤ n_1^2 := by
      cases n_1
      · ring_nf; trivial
      · calc n + 1 = (n + 1) * 1 := by ring_nf
            _ ≤ (n + 1) * (n + 1) := by gcongr; omega
            _ = (n + 1)^2 := by ring
    nth_rw 1 [← one_mul 2]
    rw [← add_mul 1 (n_1 * 2 + n_1 ^ 2 - n_1) 2,
        Nat.add_sub_assoc h (n_1 * 2),
        Nat.add_left_comm 1 (n_1 * 2) (n_1 ^ 2 - n_1),
        mul_two, ← add_assoc,
        Nat.add_right_comm (n_1 * 2) (1 + (n_1 ^ 2 - n_1)) (n_1 * 2)]
    simp; ring_nf
    rw [Nat.add_sub_assoc h]

-- Solution 2: Define f : ℕ → ℤ (using integers, simplest approach)
def f_int : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * f_int (n + 1) - f_int n + 2

theorem P5_int (n : ℕ) : f_int n = n^2 - n + 1 := by
  induction' n using Nat.twoStepInduction with n ih1 ih2
  · simp [f_int]
  · simp [f_int]
  · simp [f_int, ih1, ih2]
    ring
