import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- All tactics are welcome.

-- # Problem 1
-- Prove that the list reverse operation does not change the length of the list.
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

lemma len_over_concat (xs: List ℕ) (ys: List ℕ) : len (xs ++ ys) = len xs + len ys := by
  induction' xs with x xs ih
  . simp_all
    trivial
  . -- grind [len] suffices
    nth_rw 1 [len.eq_def] -- QUESTION: What is the difference of rewriting len vs len.eq_def?
    simp
    nth_rw 2 [len.eq_def]
    simp
    rw [ih]
    ring

theorem problem1 (xs: List ℕ): len xs = len (reverse xs) := by
  induction xs with
  | nil =>
    unfold reverse len
    rfl
  | cons x ys ih =>
    unfold reverse
    rw [len_over_concat (reverse ys) [x]]
    -- grind [len] suffices
    nth_rw 1 [len]
    rw [ih]
    rw [show len [x] = 1 from rfl]
    ring


-- # Problem 2: Consider the following rescursive function
def S : ℕ → ℕ  → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 0
  | n+1, k =>
    if n + 1 = k then 1
    else k* (S n k) + (S n (k-1))

#check Nat.twoStepInduction

-- Hint: use induction over n
theorem problem2 (n: ℕ) (h: 0 < n): (S n 1) = 1 := by
  induction n using Nat.twoStepInduction
  . trivial
  . trivial
  . unfold S
    simp_all
    trivial

theorem problem2' (n: ℕ) (h: 0 < n): (S n 1) = 1 := by
  induction' n with n ih
  . trivial
  . -- grind [S] suffices
    unfold S
    simp_all
    intro n_not_zero
    have h_pos : 0 < n := (Nat.eq_zero_or_pos n).resolve_left n_not_zero
    simp_all
    unfold S
     -- QUESTION: At this point, my proof goal has the shapen
     --               (match t with
     --                 | ...
     --                 | t => e
     --                 | ...
     --                ) = e
     --           Can I resolve only the match-block, i.e. can I perform
     --           a one-step simplification that rewrites the equality
     --           to "e = e", without closing the proof goal just yet?
    simp

#check mul_pow_sub_one
-- # Problem 3
-- This is a continuation of Problem 2
-- You may want to use the result from theorem problem2 to prove problem3
#check problem2
#check Nat.pow_le_pow_right
theorem problem3 (n: ℕ): (S n 2) = 2^(n-1) - 1  := by
  induction n with
  | zero =>
    trivial
  | succ m ih =>
    unfold S
    simp_all
    by_cases m_eq_zero : m = 0
    . simp_all
      unfold S
      rfl
    . by_cases m_eq_one : m = 1
      . simp_all
      . simp_all
        have zero_lt_m : 0 < m := by omega
        rw [Nat.mul_sub_one 2 (2 ^ (m - 1))]
        rw [problem2 m zero_lt_m]
        nth_rw 1 [mul_pow_sub_one m_eq_zero]
        rw [← Nat.sub_add_comm ?_]
        . trivial
        . have two_lte_m : 2 ≤ m := by omega
          exact calc 2 ≤ 4 := by trivial
                _ = 2^2 := by trivial
                _ ≤ 2^m := (Nat.pow_le_pow_right (by decide : 2 > 0) two_lte_m)

-- # Problem 4
/-
Define R(r,s):
  R(r,2) = r
  R(2,s) = s
  R(r,s) = R(m-1,n) + R(m,n-1)
  Prove that R(m,n) ≤ 2^{m+n}
-/

def R (r s : ℕ ): ℕ :=
  if r = 0 ∨ s = 0 then 0
  else if r ≤ 1 ∨ s ≤ 1 then 1
  else if r = 2 ∨ s = 2 then 2
  else (R (r-1) s) + (R r (s-1))

-- You may find this useful
#check Nat.choose_eq_choose_pred_add

-- Hint: you may find functional induction useful
lemma problem4 (r s : ℕ): R r s ≤ (r+s-2).choose (r-1) := by
  sorry


-- # Problem 5.1

-- Part 1: Defining interleave function
-- Define a function called interleave that takes two lists, xs and ys, and returns a new list where the elements of xs and ys are alternated.
-- If one list is longer than the other, the remaining elements of the longer list should be appended at the end.

def interleave : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => [x] ++ [y] ++ (interleave xs ys)

#eval interleave [1, 2, 3] [4, 5, 6]
#eval interleave [1, 2] [3, 4, 5, 6]
#eval interleave [1, 2, 3, 4] [5, 6]
#eval interleave [] [1, 2]
#eval interleave [1, 2] []
/--
 * interleave [1, 2, 3] [4, 5, 6] should produce [1, 4, 2, 5, 3, 6].
 * interleave [1, 2] [3, 4, 5, 6] should produce [1, 3, 2, 4, 5, 6].
 * interleave [1, 2, 3, 4] [5, 6] should produce [1, 5, 2, 6, 3, 4].
 * interleave [] [1, 2] should produce [1, 2].
 * interleave [1, 2] [] should produce [1, 2].
 --/

-- # Problem 5.2
-- Recall len and reverse functions from Problem 5.1
theorem problem5_part2 (xs ys: List ℕ): len (reverse (interleave xs ys)) = len (reverse (xs)) + len ys := by
  fun_induction interleave
  all_goals (expose_names)
  . -- grind [reverse, len, problem1] suffices
    nth_rw 1 [reverse]
    nth_rw 1 [len]
    norm_num
    rw [← problem1]
  . nth_rw 1 [len]
    ring
  . -- grind [reverse, len, len_over_concat] suffices
    simp_all
    simp [reverse]
    simp [len]
    rw [len_over_concat (reverse (interleave xs_1 ys_1)) [y, x]]
    simp [len]
    rw [len_over_concat (reverse xs_1) [x]]
    simp [len]
    rw [ih1]
    ring_nf
