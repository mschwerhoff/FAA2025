import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Divisibility.Basic


/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics: `rfl`, `intro`, `exact`, `constructor`, `apply`, `rw`
- `rfl` - close the goal of the form a = b where a and b are definitionally equal.
- `intro` - introduce hypotheses for implications
- `exact` - provide exact proof terms
- `constructor` - split conjunctions and biconditionals
- `apply` - use implications and functions backwards
- `rw` / `rewrite` - rewrite using equalities
- `use` - provide witnesses for existentials
- `obtain` - extract components from conjunctions

**Instructions**: Replace each `sorry` with the appropriate proof tactics.
**Submission**: Submit your HW0.lean file in Moodle.
-/

section Logic

variable (P Q R : Prop)

-- Question 1: Fill-in-the-blank proof
-- Hint: Break down the compound implication step by step. You'll need to assume the conjunction,
/-
  Proof strategy for Q1:

  We prove that having both P → Q and Q → R implies P → R (function composition).

  Assume h : (P → Q) ∧ (Q → R) and hp : P.
  To show R, we apply h.2 (which is Q → R), but first we need Q.
  We obtain Q by applying h.1 (which is P → Q) to hp.
-/
theorem Q1 : (P → Q) ∧ (Q → R) → (P → R) := by
  intro h   -- "Assume we have both P → Q and Q → R"
  intro hp  -- "Assume P"
  apply h.2 -- "To prove R, use the second part Q → R, so we need Q"
  apply h.1 -- "To prove Q, use the first part P → Q, so we need P"
  exact hp  -- "We have P"

-- Solution 2: Using destructuring (cleaner)
theorem Q1_v2 : (P → Q) ∧ (Q → R) → (P → R) := by
  intro ⟨hpq, hqr⟩ hp  -- Destructure conjunction directly
  exact hqr (hpq hp)   -- Compose the functions



-- Question 2: Prove a logical equivalence
-- Hint: Split the biconditional into two directions.
/-
  Proof strategy for Q2:

  We prove the biconditional by showing both directions.

  (→) Given h : P → (Q → R) and a pair (P, Q), we can curry:
      Apply h to get Q → R, then apply to Q to get R.

  (←) Given h : (P ∧ Q) → R, we uncurry:
      From P and Q separately, construct the pair (P, Q) and apply h.
-/
theorem Q2 : P → (Q → R) ↔ (P ∧ Q) → R := by
  constructor
  · intro h      -- "Forward: assume P → (Q → R)"
    intro hpq    -- "Assume P ∧ Q"
    apply h      -- "Apply h to get Q → R, need to prove P"
    exact hpq.1  -- "P is the first part of P ∧ Q"
    exact hpq.2  -- "Q is the second part of P ∧ Q"
  · intro h      -- "Backward: assume (P ∧ Q) → R"
    intro hp     -- "Assume P"
    intro hq     -- "Assume Q"
    apply h      -- "Apply h, need to prove P ∧ Q"
    constructor  -- "Build the conjunction"
    exact hp     -- "We have P"
    exact hq     -- "We have Q"

-- Solution 2: Compact style (recommended)
theorem Q2_v2 : P → (Q → R) ↔ (P ∧ Q) → R := by
  constructor
  · intro h ⟨hp, hq⟩  -- Destructure argument directly
    exact h hp hq
  · intro h hp hq
    exact h ⟨hp, hq⟩  -- Construct pair directly


-- Question 3: Transitivity of divisibility
-- Hint: You can might need follow theorem:
#check Nat.dvd_trans
/-
  Proof strategy for Q3:

  We prove transitivity of divisibility: if a | b and b | c, then a | c.

  Method 1: Use Mathlib's built-in theorem dvd_trans.

  Method 2: Prove from definitions:
  - From a | b: ∃ k₁, b = a * k₁
  - From b | c: ∃ k₂, c = b * k₂
  - Therefore: c = (a * k₁) * k₂ = a * (k₁ * k₂)
  - So a | c with witness k₁ * k₂
-/

/-
  Proof strategy for Q3:

  We prove transitivity of divisibility: if a | b and b | c, then a | c.

  Method 1: Use Mathlib's built-in theorem dvd_trans.

  Method 2: Prove from definitions:
  - From a | b: ∃ k₁, b = a * k₁
  - From b | c: ∃ k₂, c = b * k₂
  - Therefore: c = (a * k₁) * k₂ = a * (k₁ * k₂)
  - So a | c with witness k₁ * k₂
-/
theorem Q3 (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  dvd_trans h1 h2  -- Mathlib has this theorem built-in

theorem Q3_v2 (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨k1, hk1⟩ := h1  -- b = a * k1
  obtain ⟨k2, hk2⟩ := h2  -- c = b * k2
  use k1 * k2              -- Witness for a | c
  rw [hk2, hk1]            -- c = (a * k1) * k2
  ring                     -- = a * (k1 * k2)


-- Question 4:  Proving Even Numbers
/-
  Proof strategy for Q4:

  To prove both 4 and 6 are even, we provide witnesses:
  - For 4: use k = 2, since 4 = 2 * 2
  - For 6: use k = 3, since 6 = 2 * 3

  Both equalities hold by reflexivity (definitional equality).
-/
def even_number (n : ℕ) : Prop := ∃ k, n = 2 * k
theorem Q4 : even_number 4 ∧ even_number 6 := by
  constructor
  · unfold even_number  -- "4 is even means ∃ k, 4 = 2 * k"
    use 2               -- "Take k = 2. Indeed, 4 = 2 * 2"
  · unfold even_number  -- "6 is even means ∃ k, 6 = 2 * k"
    use 3               -- "Take k = 3. Indeed, 6 = 2 * 3"

-- Solution 2: Direct term construction (most concise)
theorem Q4_v2 : even_number 4 ∧ even_number 6 :=
  ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩


-- Question 5: Some divisibility problem
-- The following lemma has partial proof on it. Fill in the sorry to finish the proof.
-- You may find these theorems helpful
#check Dvd.dvd.mul_left
#check Nat.dvd_add_right
-- 'have' tactics is basically a sub-claim that to be filled by the proof.
-- In this problem, you are asked to prove the subclaims and then finish the proof.
/-
  Proof strategy for Q5:

  The key algebraic insight: 3(14n + 3) - 2(21n + 4) = 1

  Given:
  - k | (21n + 4)
  - k | (14n + 3)

  We show k | 1 by the following steps:
  1. If k | a, then k | (c * a) for any c
     So k | 2(21n + 4) and k | 3(14n + 3)

  2. Verify algebraically: 3(14n + 3) = 2(21n + 4) + 1
     (Expanding: 42n + 9 = 42n + 8 + 1 ✓)

  3. If k divides both 2(21n + 4) and 2(21n + 4) + 1,
     then k must divide their difference, which is 1.
-/
-- Solution 1: Using helper lemmas (clearest structure)
lemma Q5 (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 := by
  -- Step 1: If k divides something, it also divides any multiple of that thing
  have h3 : k ∣ 2 * (21 * n + 4) := by
    exact h1.mul_left 2  -- "If k ∣ a, then k ∣ 2a"
  have h4 : k ∣ 3 * (14 * n + 3) := by
    exact h2.mul_left 3  -- "If k ∣ b, then k ∣ 3b"

  -- Step 2: The key arithmetic insight - this is why the problem works!
  have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by
    ring  -- "Let's check: 3(14n+3) = 42n+9 and 2(21n+4) = 42n+8, so the difference is 1"

  -- Step 3: If k divides both terms on the right, it divides their difference
  apply (Nat.dvd_add_right h3).1
  exact (h5 ▸ h4)
  -- "Since k ∣ 2(21n+4) and k ∣ 3(14n+3) = 2(21n+4) + 1, we get k ∣ 1"

-- Solution 2: More direct approach
lemma Q5_v2 (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 := by
  have h3 : k ∣ 3 * (14 * n + 3) := h2.mul_left 3
  have h4 : k ∣ 2 * (21 * n + 4) := h1.mul_left 2
  -- Since 3(14n+3) = 2(21n+4) + 1 and k divides both sides' terms
  have : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by ring
  rw [this] at h3
  exact (Nat.dvd_add_right h4).mp h3

