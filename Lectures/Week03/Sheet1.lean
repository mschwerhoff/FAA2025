import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
-- import Lectures.Week3.Sheet0
set_option autoImplicit false



/-!
## Induction Proofs
  Let's say P: ℕ → Prop is a proposition indexed by a natural number. If you prove
  · P 0
  · ∀ i : ℕ, P i → P (i+1)
  then P n holds for all natural numbers

  In lean, you can use induction' tactics to do so.
-/

#check Nat.and_forall_add_one

-- Let's define a recursive funciton:
def I : ℕ → ℕ
  | 0 => 0
  | n + 1 => I n + 1

#eval [I 0, I 1, I 2]

-- running examples
example (n:ℕ): I n = n := by
  induction' n with n ih
  · rfl
  · unfold I
    rw [ih]

-- Exercise 1
def I2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => I2 n + 2

def I2' (n : ℕ) : ℕ := match n with
  | 0 => 0
  | n + 1 => I2 n + 2

#eval [I2 0, I2 1, I2 2]
example (n:ℕ): I2 n = 2*n := by
  induction' n with n ih
  · rw [I2] -- unfold def I2 --> done right away
  · rw [I2] -- unfold def I2
    rw [ih] -- substitute equality
    trivial -- done

-- Another example
example (n:ℕ): Even (I2 n) := by
  induction' n with n ih
  · rw [I2]
    rw [Even]
    use 0
  · unfold I2
    unfold Even
    rw [Even] at ih
    obtain ⟨r ,hr⟩ := ih
    use (r+1)
    rw [hr]
    omega

-- Exercise 2
theorem even_or_odd (n : ℕ) : (∃ k, n = 2*k) ∨ (∃ k, n = 2*k+1) := by sorry

def S : ℕ → ℕ
  | 0 => 0
  | n + 1 => S n + (n + 1)

#eval S 1
#eval S 2
#eval S 3

#check mul_comm
#check Nat.left_distrib

-- Exercise 3
lemma Sn_two (n : ℕ) : 2*(S n) = n * (n + 1)  := by
  induction' n with n ih
  · rw [S]
  · unfold S
    rw [Nat.left_distrib]
    rw [ih]
    -- ring_nf -- Suffices at this point
    -- goal: n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 1 + 1)
    calc  n * (n + 1) + 2 * (n + 1)
        = (n * n) + n + 2 * (n + 1) := by group
      _ = (n * n) + n + 2 * n + 2 := by group
      _ = n^2 + n + 2 * n + 2 := by group
      _ = n^2 + 2 * n + n + 2 := by group
      _ = n^2 + n + (n + 1) + (n + 1) := by group
      _ = (n + 1) * n + (n + 1) + (n + 1) := by group
      _ = (n + 1) * (n + 1 + 1) := by group -- syntactically the RHS of the desired equality

example (n : ℕ) : (S n) = n * (n + 1)/2  := by
  induction' n with n ih
  · unfold S
    trivial
  · unfold S
    rw [ih]
    ring_nf
    omega

-- It is much easier to work with type ℚ
-- Example
def SQ : ℕ → ℚ
  | 0 => 0
  | n + 1 => SQ n + (n + 1)

example (n : ℕ) : (SQ n) = n * (n + 1)/2  := by
  induction' n with n ih
  · simp [SQ]
  · simp [SQ,ih]
    linarith

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#eval [0!,1!,2!,3!,4!]

/- Induction principle starting at a non-zero number.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`). -/

#check Nat.le_induction

-- In general, you can choose a version of induction.
#check Nat.decreasingInduction
#check Nat.div2Induction

-- From Sheet0
theorem power_two_ih (n : ℕ) (ih : 5 ≤ n) (h : 2 ^ n > n ^ 2) : 2 ^ (n + 1) > (n + 1) ^ 2 := by sorry

-- Example
example : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  intro n h
  induction' n,h using Nat.le_induction with n ih
  · -- To show (base case): 2 ^ 5 > 5 ^ 2
    trivial
  · -- To show: 2 ^ (n + 1) > (n + 1) ^ 2
    rename_i h
    exact power_two_ih n ih h

-- Exercise 4
lemma le_fact (n : ℕ) : 1 ≤ (n)! := by
  induction' n with n ih
  · unfold factorial
    trivial
  · unfold factorial
    grw [← ih]
    simp
    -- rw [Nat.right_distrib]
    -- rw [Nat.one_mul]
    -- -- goal: 1 ≤ n * n ! + n !
    -- calc 1 ≤ (n)! := by exact ih
    --      _ ≤ (n)! + (n)! := by simp
    --      _ ≤ n * (n)! + (n)! := by ring_nf
    -- -- rw [Nat.Simproc.le_add_le 1 ih]
    -- -- trivial

-- Exercise 5
example (n : ℕ) : 2^n ≤ (n+1)! := by sorry
