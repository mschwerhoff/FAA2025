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

#eval SumOdd 0
#eval SumOdd 1
#eval SumOdd 2
#eval SumOdd 3
#eval SumOdd 4
#eval SumOdd 5
#eval SumOdd 6
#eval SumOdd 7

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

theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by sorry
theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by sorry

-- # Problem 4:
-- in this problem, you are asked to solve the following recurrence relation.
-- g(n) = g(n/2) + 1, g(0) = 0
-- Prove that that g(n) ≤  Nat.log 2 n + 1 for all n
-- state the formal theorem and prove it

-- The following lemmas can be helpful
#check Nat.sub_add_cancel
#check Nat.le_log_of_pow_le

-- # Problem 5
-- in this problem, you are asked to solve the following recurrence relation.
-- f(n) = 2*f(n-1) - f(n-2) + 2
-- where f(1) = 1 and f(2) = 4
-- Prove that that f(n) = n^2 - n + 1

-- state the formal theorem and prove it
-- Hint: you may find `zify` tactic useful
