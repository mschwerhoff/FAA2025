import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- All tactics are welcome.

-- # Problem 1
-- Prove the list reverse operation
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

-- First prove this helper function
theorem len_append (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  induction' l with y ys
  · aesop
  · simp only [List.cons_append, len]
    rw [tail_ih]

-- Hint: use induction over the list
theorem problem1 (xs: List ℕ): len xs = len (reverse xs) := by
  induction' xs
  · aesop
  · simp [len]
    simp [reverse]
    rw [len_append]
    simpa


-- # Problem 2
def S : ℕ → ℕ  → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 0
  | n+1, k =>
    if n + 1 = k then 1
    else k* (S n k) + (S n (k-1))

def F (n:ℕ ): ℕ := 2^(n-1)-1

#eval [S 12 2, S 1 2]
#eval [F 12]

#check Nat.twoStepInduction

-- Hint: use induction over n
theorem problem2 (n: ℕ) (h: 0 < n): (S n 1) = 1 := by
  induction' n with n ih
  · contradiction
  · unfold S
    split_ifs with h
    · rfl
    · have: 0 < n := by omega
      simp_all [S]


-- # Problem 3
-- This is a continuation of Problem 2
-- You may want to use the result from theorem problem2 to prove problem3
theorem problem3 (n: ℕ): (S n 2) = 2^(n-1) - 1  := by
  induction' n with n ih
  · simp [S]
  · expose_names
    unfold S
    split_ifs with h
    · simp at h
      subst h
      simp only [pow_one, Nat.add_one_sub_one]
    · by_cases hn: n = 0
      · subst hn
        simp [S]
      · rw [ih]
        simp
        simp at h
        have: 0 < n := by omega
        rw [problem2 n (by omega)]
        · rw [mul_tsub_one 2 (2 ^ (n - 1))]
          rw [mul_pow_sub_one (by omega) 2]
          rw [← Nat.sub_add_comm (?_)]
          simp
          exact Nat.le_pow this

-- # Problem 4
/-
Define R(r,s):
  R(r,2) = r
  R(2,s) = s
  R(r,s) = R(m-1,n) + R(m,n-1)
  Prove that T(m,n) ≤ 2^{m+n}
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
  fun_induction R <;> expose_names
  · exact Nat.zero_le ((r_1 + s_1 - 2).choose (r_1 - 1))
  · obtain h1 | h1 := h_1
    · simp_all only [not_or, Nat.sub_eq_zero_of_le, Nat.choose_zero_right, le_refl]
    · have: s_1 = 1 := by grind
      subst this
      simp only [one_ne_zero, or_false] at h
      apply Nat.choose_pos
      simp only [Nat.reduceSubDiff, le_refl]
  · obtain h1 | h1 := h_2
    · subst h1
      simp_all only [OfNat.ofNat_ne_zero, false_or, Nat.not_ofNat_le_one, not_le,
        add_tsub_cancel_left, Nat.add_one_sub_one, Nat.choose_one_right]
      exact h_1
    · subst h1
      simp_all
      rw [Nat.choose_symm (by omega)]
      simpa only [Nat.choose_one_right]
  · grw [ih1,ih2]
    nth_rw 3 [Nat.choose_eq_choose_pred_add (by omega) (by omega)]
    grind only [cases Or]



-- # Problem 5.1

-- Part 1: Defining interleave function
-- Define a function called interleave that takes two lists, xs and ys, and returns a new list where the elements of xs and ys are alternated.
-- If one list is longer than the other, the remaining elements of the longer list should be appended at the end.

def interleave : List ℕ → List ℕ → List ℕ
  | [], ys' => ys'
  | xs', [] => xs'
  | x :: xs', y :: ys' => x :: y :: interleave xs' ys'

/--
 * interleave [1, 2, 3] [4, 5, 6] should produce [1, 4, 2, 5, 3, 6].
 * interleave [1, 2] [3, 4, 5, 6] should produce [1, 3, 2, 4, 5, 6].
 * interleave [1, 2, 3, 4] [5, 6] should produce [1, 5, 2, 6, 3, 4].
 * interleave [] [1, 2] should produce [1, 2].
 * interleave [1, 2] [] should produce [1, 2].
 --/

-- # Problem 5.2
-- Recall len and reverse functions from Problem 5.1
theorem problem5_part2 (xs ys: List ℕ): len (reverse (interleave xs ys))  = len (reverse (xs)) + len ys  := by
  repeat rw [← problem1]
  fun_induction interleave <;> all_goals grind [len]
