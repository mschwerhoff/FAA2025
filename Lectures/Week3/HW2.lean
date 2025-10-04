import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- Most tactics are welcome.
-- You are now allowed to use `aesop` and `grind` tactics.

-- Problem 1
def SumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => SumOdd n + (2*n +1)

theorem P1 (n : ℕ) : SumOdd (n) = n^2 := by
  induction' n with n ih
  · -- Base case
    unfold SumOdd
    norm_num
  · -- Proof goal: SumOdd (n + 1) = (n + 1) ^ 2
    --   using ih: SumOdd n = n ^ 2
    unfold SumOdd
    rw [ih]
    rw [add_sq n 1]
    simp
    rfl

-- Problem 2 and 3
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

def isEven (n : ℕ) : Prop := ∃ k, n = 2*k

#check Nat.one_le_iff_ne_zero

theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  . -- Direction isEven n! → n ≥ 2
    induction' n with n ih
    · unfold isEven
      norm_num
      intro x h
      unfold factorial at h
      omega
    · intro lhs
      unfold isEven at lhs
      obtain ⟨k1, hk1⟩ := lhs
      unfold factorial at hk1
      unfold isEven at ih
      by_cases (n = 0) -- QUESTION: I find this case split a bit annoying, in particular
                       --           since "simp_all" afterwards still feels like magic.
                       --           Would be great to see an alternative, more accessible proof.
      . simp_all
      . simp_all
        rename_i n_neq_zero
        exact Nat.one_le_iff_ne_zero.mpr n_neq_zero
  . -- Direction n ≥ 2 → isEven n!
    induction' n with n ih
    . intro lhs
      unfold isEven
      unfold factorial
      simp_all
    . intro lhs
      unfold isEven at ih
      by_cases n ≥ 2
      . unfold factorial isEven
        simp_all
        obtain ⟨k, hk⟩ := ih
        use (n + 1) * k
        simp_all
        ring_nf
      . unfold factorial isEven
        simp_all
        have n_eq_one : n = 1 := by decide +revert -- conclude from 1 ≤ n and n < 2
        rw [n_eq_one]
        -- simp_all -- suffices at this point
        unfold factorial factorial
        ring_nf
        use 1
        trivial
      ---- Alternative case split: split n < 2 into two (then slightly simpler cases) n = 0 and n = 1
      -- match n with
      -- | 0 =>
      --   simp_all
      -- | 1 =>  -- QUESTION: Can I merge cases 0 and 1? E.g. via a pattern like "m < 2"?
      --   unfold factorial isEven
      --   simp_all
      -- | m + 2 =>
      --   unfold factorial isEven
      --   simp_all
      --   obtain ⟨k, hk⟩ := ih
      --   use (m + 2 + 1) * k
      --   simp_all
      --   ring_nf


-- Helper lemma I need for proving P3
lemma L1 : ∀ n > 0 , 2*n + 1 ≤ 3^n * 2 := by
  intro n
  induction' n with n ih
  . trivial
  . intro lhs
    by_cases (n = 0)
    . simp_all
    . omega

#check L1
#check add_le_add_left
#check add_le_add_right

theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by
  intro n
  induction' n with n ih
  . simp_all
  . intro lhs
    simp_all
    by_cases (n = 0)
    . simp_all
    . rename_i n_not_zero
      have ih_lhs  : 0 < n := Nat.pos_of_ne_zero n_not_zero
      have ih_rhs := by exact ih ih_lhs
      have w : 2*n + 1 ≤ 3^n * 2 := by exact ((L1 n) ih_lhs)
      calc
        (n + 1)^2 = n^2 + 2 * n + 1 := by ring
        _         < 3^n + 2 * n + 1 := add_lt_add_right (add_lt_add_right ih_rhs _) _ -- or by gcongr
        _         = 3^n + (2 * n + 1) := by rw [add_assoc]
        _         ≤ 3^n + 2 * 3^n     := by omega -- QUESTION: How can I use "w" more explicitly,
                                                  -- without the magic of omega?
        _         = 2 * 3^n + 3^n     := by rw [Nat.add_comm]
        _         = 3 * 3^n           := by rw [← Nat.add_one_mul]
        _         = 3^n * 3           := by rw [Nat.mul_comm]
        _         = 3 ^ (n + 1)       := by rw [pow_succ]

-- # Problem 4:
-- in this problem, you are asked to solve the following recurrence relation.
-- g(n) = g(n/2) + 1, g(0) = 0
-- Prove that that g(n) ≤  Nat.log 2 n + 1 for all n
-- state the formal theorem and prove it

-- The following lemmas can be helpful
#check Nat.sub_add_cancel
#check Nat.le_log_of_pow_le

#check Nat.strong_induction_on
#check Nat.div_lt_of_lt
#check Nat.log_mono_right

def G : ℕ → ℕ
  | 0 => 0
  | n + 1 => G (n / 2) + 1

theorem P4 (n : ℕ) : G n ≤ Nat.log 2 (n + 1) := by
  induction n using Nat.strong_induction_on
  rename' n_1 => n, a => ih
  if h : n = 0 then
    unfold G
    simp_all
  else if h : n = 1 then
    unfold G
    simp_all
    norm_num
  else
    rename_i h'
    have n_geq_two : 2 ≤ n := by omega
    unfold G

    cases n with
    | zero =>
      contradiction
    | succ m =>
      simp_all
      rw [Nat.add_assoc m 1 1]
      unfold Nat.log
      simp
      -- Close proof by suitable IH instantiation
      have ih_lhs : m/2 < m + 1 := by calc -- omega suffices
        m/2 ≤ m := by exact Nat.div_le_self m 2
          _ < m + 1 := by exact lt_add_one m
      exact ih (m/2) ih_lhs -- Instantiate IH


-- # Problem 5
-- in this problem, you are asked to solve the following recurrence relation.
-- f(n) = 2*f(n-1) - f(n-2) + 2
-- where f(0) = 1 and f(1) = 1
-- Prove that that f(n) = n^2 - n + 1

-- state the formal theorem and prove it
-- Hint: you may find `zify` tactic useful
