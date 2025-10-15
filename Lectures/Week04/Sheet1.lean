import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
--set_option tactic.hygienic false


/-
# Function Induction
So far, we have seen induction over ℕ. This week we will cover functional induction.
The core idea is that if a function is recursively defined, then you can prove it recursively as long as you show termination.
On the other hand, functional induction formalizes recursive proofs and tells you exactly what is needed to complete the proof.
These two proofs are equivalent, but they may give you different perspective to think about a problem.
-/

-- functional induction
-- Pascal sum

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

-- In Lean, every recursively defined function is equipped with functional induction
#check factorial.induct
-- Recall induction proof
lemma fact (n :ℕ) : 1 ≤ n ! := by
  induction' n with n ih
  · rfl
  · unfold factorial
    grw [← ih]
    exact NeZero.one_le

--lemma fact' (n :ℕ) : 1 ≤ n ! := by
--  fun_induction


-- Pascal's triangle
def P : ℕ → ℕ → ℕ
  | x, 0 => 1
  | 0, y + 1 => 1
  | a + 1, b + 1 => P (a + 1) b + P a (b + 1)

-- Equivalently
def P' (a b :ℕ) : ℕ :=
  match a, b with
  | a, 0 => 1
  | 0, b + 1 => 1
  | a + 1, b + 1 => P' (a + 1) b + P' a (b + 1)

-- Equivalently
def P_ie (a b :ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 1
  else P_ie a (b-1) + P_ie (a-1) b

#check P_ie.induct

lemma P_eq: P = P_ie := by -- Will come back later
  ext a b
  fun_induction P a b <;> all_goals (expose_names)
  · simp [P_ie]
  · simp [P_ie]
  · rw [ih1,ih2]
    nth_rw 3 [P_ie]
    simp only [Nat.succ_eq_add_one, Nat.add_eq_zero, one_ne_zero, and_false, or_self, ↓reduceIte,
      add_tsub_cancel_right]

-- In Lean, every recursively defined function is equipped with functional induction
#check P_ie.induct
#check P_ie.induct_unfolding

#eval [P 0 0]
#eval [P 0 1,P 1 0]
#eval [P 2 0,P 1 1, P 2 0]
#eval [P 3 0,P 2 1, P 1 2, P 0 3]
#eval [P 4 0,P 3 1, P 2 2, P 1 3, P 0 4]

-- Example
lemma P_le_fact ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P
  all_goals (expose_names)
  · simp only [add_zero]
    exact fact x
  · simp only [Nat.succ_eq_add_one, zero_add]
    exact fact (y + 1)
  · grw [ih1,ih2]
    clear * -; grind [fact,factorial] -- grind for algebraic proofs

-- grind is a powerful automation
-- We will not be using grind for the rest of the week.
lemma P_le_fact'' ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P <;> all_goals grind only [fact, factorial]

-- This proof is more intuitive than the one-line proof
lemma P_le_fact' ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P <;> all_goals (try simp_all only [add_zero, fact])
  · expose_names
    calc
      P (a + 1) b + P a (b + 1) ≤ (a + 1 + b) ! + (a + (b + 1)) !                            := by rel [ih1, ih2]
                              _ ≤ (a + b) * (a + b + 1) ! + (a + 1 + b) ! + (a + (b + 1)) !  := by omega
                              _ = ((a + b + 1) + 1) * (a + b + 1)!                           := by ring_nf
                              _ = ((a + b + 1) + 1)!                                         := by bound
                              _ = (a + 1 + (b + 1))!                                         := by ring_nf

--#print P_le_fact'
--#print P_le_fact'._proof_1_5

-- # Exercise 1.1
/-
Define T(m,n):
  T(m,0) = T(0,n) = 1,
  T(m,n) = T(m-1,n) + T(m,n-1)
  Prove that T(m,n) ≤ 2^{m+n}
-/

def T : ℕ → ℕ → ℕ
  | _, 0 => 1 -- Single-line alternative:
  | 0, _ => 1 -- | _, 0 | 0, _ => 1
  | m+1, n+1 => T m (n+1) + T (m+1) n

theorem solve_T (m n: ℕ):  T m n ≤ 2^(m+n) := by
  fun_induction T
  all_goals (expose_names)
  . -- simp_all
    exact Nat.one_le_two_pow
  . -- simp_all
    exact Nat.one_le_two_pow
  . grw [ih2,ih1]
    --simp_all
    grind

-- # Exercise 1.2
/-
Define C(m,n):
  C(m,0) = C(0,n) = 1,
  C(m,n) = C(m-1,n)*C(m,n-1)
  Prove that C(m,n) = 2^{m*n}
-/

def C : ℕ → ℕ  → ℕ
  | _, 0 | 0, _ => 1
  | m+1, n+1 => C m (n+1) * C (m+1) n

#check Nat.log_mul_base
#check Nat.log_pow
#check Nat.log
#check Nat.add_left_inj
#check Nat.add_left_cancel

theorem solve_C (m n: ℕ):  C m n = 2^(m*n)  := by
  fun_induction C
  all_goals (expose_names)
  . norm_num
  . norm_num
  . grw [ih1, ih2]
    simp_all

    ring_nf
    rw [Nat.mul_right_comm (2 ^ m * 2 ^ (m * n)) (2 ^ n) 2]
    refine (Nat.mul_left_inj ?_).mpr ?_
    . simp
    . rw [mul_assoc (2 ^ m) (2 ^ (m * n)) 2]
      refine (Nat.mul_right_inj ?_).mpr ?_
      . simp
      . rw [← pow_succ 2 (m * n)]
        -- Remaining goal: 2 ^ (m * n * 2) = 2 ^ (m * n + 1) -- Why should that hold?
        sorry

    rw [← pow_add 2 (m * (n + 1)) ((m + 1) * n)]
    rw [Nat.pow_right_inj ?_]
    . ring_nf
      refine Nat.add_left_inj.mpr ?_
      rw [Nat.add_comm 1 m]
      rw [add_assoc m 1 (m * n)]
      refine Nat.add_left_cancel_iff.mpr ?_
      rw [Nat.mul_two (m * n)]
      refine Nat.add_left_inj.mpr ?_
      -- Remaining goal: m*n = 1 -- Why should that hold?
      sorry
    . trivial
