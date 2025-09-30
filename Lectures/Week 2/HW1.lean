import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false

/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics: `rfl`, `intro`, `exact`, `constructor`, `apply`, `rw`, `left`, `right`, `cases`, `by_cases`, `ext`, `trivial`,`contradiction`,`assumption`,`have`, `by_contra`, `rintro`

If you need to use different tactics, please justify why basic tactics in the list above are not sufficient.
In particular, you are not allowed to use automation (simp, aesop, grind, ring, omega, etc) to finish the goal.

**Instruction**:
(1) Fill each `sorry` with the appropriate tactics.
(2) For each problem, give an informal explanation of the proof strategy. This should correspond to your Lean proof.
**Submission**:  HW1.lean file in Moodle. The grading will be based on (1) and (2).

-/
section
open Set
variable {α : Type*}
variable (A B C : Set α)

/-
  Proof strategy for P1 is:
  Split iff into two implications
  1) Show B ∪ C ⊆ A  →  B ⊆ A ∧ C ⊆ A
      * Assume LHS
      * Prove both RHS conjuncts separately
      * Use definition of subset and union to conclude from B ∪ C ⊆ A that B ⊆ A (resp. C ⊆ A).
        Idea: B ∪ C ⊆ A means "all x in B or C are also in A", then chose suitable disjunct.
  2) Show B ⊆ A ∧ C ⊆ A  →  B ∪ C ⊆ A
      * Assume RHS
      * Treat RHS as disjunction (as in the previous directions), and branch over it
      * Pick suitable LHS conjunct to show current disjunct
-/

#check mem_union
#check Or.inl
#check Or.inr

-- I used mem_union and Or.inl to obtain from x ∈ A that then also x ∈ A ∪ B
-- QUESTION: I tried to make parameters x and α implicit, but then failed to apply union_left further done.
--           How to make implicit parameters work here?
lemma union_left (x : α) (h : x ∈ A) : x ∈ A ∪ B := by
  have h' := mem_union x A B
  obtain ⟨_, h''⟩ := h'
  exact (h'' (Or.inl h))

-- I used mem_union and Or.inr to obtain from x ∈ B that then also x ∈ A ∪ B
lemma union_right (x : α) (h : x ∈ B) : x ∈ A ∪ B := by
  have h' := mem_union x A B
  obtain ⟨_, h''⟩ := h'
  exact (h'' (Or.inr h))

#check union_left
#check union_right

lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by
  constructor -- Split iff into two implications
  . -- Show B ∪ C ⊆ A  →  B ⊆ A ∧ C ⊆ A
    intro lhs
    constructor -- Split B ⊆ A ∧ C ⊆ A into two conjuncts
    . -- Show B ⊆ A
      rewrite [subset_def]
      intro x x_in_B
      -- Construct x ∈ B ∪ C for applying lhs
      -- I used mem_union and Or.inl to obtain from x ∈ B that then also x ∈ B ∪ C
      have x_in_B_union_C : (x ∈ B ∪ C) := @union_left α B C x x_in_B
      -- have x_in_B_union_C : (x ∈ B ∪ C) := by -- No longer necessary due to union_left
      --   have h' := mem_union x B C
      --   obtain ⟨_, h''⟩ := h'
      --   have h''' := h'' (Or.inl x_in_B) -- Use disjunct x ∈ B
      --   exact h'''
      apply lhs at x_in_B_union_C
      exact x_in_B_union_C
    . -- Show C ⊆ A
      rewrite [subset_def]
      intro x x_in_C
      -- Construct x ∈ B ∪ C for applying lhs
      have x_in_B_union_C : (x ∈ B ∪ C) := @union_right α B C x x_in_C
      apply lhs at x_in_B_union_C
      exact x_in_B_union_C
  . -- Show B ⊆ A ∧ C ⊆ A  →  B ∪ C ⊆ A
    intro lhs
    obtain ⟨B_subset_A, C_subset_A⟩ := lhs
    rewrite [subset_def]
    intro x x_in_B_union_C
    cases x_in_B_union_C
    . -- Show x ∈ A using h: x ∈ B
      rewrite [subset_def] at B_subset_A
      apply B_subset_A at h
      exact h
    . -- Show x ∈ A using x ∈ C
      rewrite [subset_def] at C_subset_A
      apply C_subset_A at h
      exact h


/-
  Proof strategy for P2 is:
  Treat equality as iff, and prove both directions separately:
  1) Show x ∈ A ∩ (B ∪ C)  →  x ∈ A ∩ B ∪ A ∩ C
      * Assume LHS and treat "x ∈ A ∩ (B ∪ C) as "x ∈ A, and x ∈ B or x ∈ C"
      * Branch over whether x ∈ B (or ∈ C) is true
      * Treat RHS as "x ∈ A ∩ B, or x ∈ A ∩ C"
      * Per LHS branch, choose suitable RHS disjunct to prove
      * Use suitable assumptions to show chosen disjunct
  2) Show x ∈ A ∩ B ∪ A ∩ C  →  x ∈ A ∩ (B ∪ C)
      * Assume LHS and treat "x ∈ A ∩ B ∪ A ∩ C" as "x ∈ A ∩ B, or x ∈ A ∩ C"
      * Branch over LHS disjuncts
      * Treat LHS disjunct "x ∈ A ∩ B" as "x ∈ A, and x ∈ B" (and analogously for 2nd LHS disjunct)
      * Treat RHS "x ∈ A ∩ (B ∪ C)" as "x ∈ A, and x ∈ B ∪ C"
      * Use suitable LHS assumptions to show both RHS conjuncts
-/

theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  . -- Show x ∈ A ∩ (B ∪ C)  →  x ∈ A ∩ B ∪ A ∩ C
    intro lhs
    obtain ⟨x_in_A, x_in_B_union_C⟩ := lhs
    rewrite [mem_union] at x_in_B_union_C
    rewrite [mem_union]
    cases x_in_B_union_C
    . left
      -- trivial -- Would suffice
      constructor
      . exact x_in_A
      . exact h
    . right
      trivial
      -- constructor -- Explicit alternative
      -- . exact x_in_A
      -- . exact h
  . -- Show x ∈ A ∩ B ∪ A ∩ C  →  x ∈ A ∩ (B ∪ C)
    intro lhs
    rewrite [mem_union] at lhs
    cases lhs
    . obtain ⟨x_in_A, x_in_B⟩ := h
      constructor
      . exact x_in_A
      . have x_in_B_union_C : (x ∈ B ∪ C) := @union_left α B C x x_in_B
        exact x_in_B_union_C
    . obtain ⟨x_in_A, x_in_C⟩ := h
      constructor
      . exact x_in_A
      . have x_in_B_union_C : (x ∈ B ∪ C) := @union_right α B C x x_in_C
        exact x_in_B_union_C

/-
  Proof strategy for P3 is:
  Analogous to the strategy for P2, just with more (and nested) case distinctions.
-/

theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by
  ext x
  constructor
  . -- Show x ∈ (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C)  →  x ∈ A ∩ B ∪ A ∩ C ∪ B ∩ C
    intro lhs
    obtain ⟨⟨x_in_AB, x_in_AC⟩, x_in_BC⟩ := lhs
    rewrite [mem_union] at x_in_AB x_in_AC x_in_BC
    rewrite [mem_union, mem_union]
    cases x_in_AB
    . cases x_in_BC
      . left; left; trivial
      . left; right; trivial
    . cases x_in_AC
      . left; left; trivial
      . right; trivial
  . -- Show x ∈ A ∩ B ∪ A ∩ C ∪ B ∩ C  →  x ∈ (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C)
    intro lhs
    rewrite [mem_union, mem_union] at lhs
    constructor
    . -- Show x ∈ (A ∪ B) ∩ (A ∪ C)
      constructor
      . -- Show x ∈ A ∪ B
        rewrite [mem_union]
        cases lhs
        . cases h
          -- QUESTION: Both cases of h proceed identically. Can I exploit this to shorten the proof?
          . obtain ⟨x_in_A, _⟩ := h_1
            left; exact x_in_A
          . obtain ⟨x_in_A, _⟩ := h_1
            left; exact x_in_A
        . obtain ⟨x_in_B, _⟩ := h
          right; exact x_in_B
      . -- Show x ∈ A ∪ C   -- QUESTION: Same here — how to exploit structural overlap with constructor block line 179ff?
        rewrite [mem_union]
        cases lhs
        . cases h
          . obtain ⟨x_in_A, _⟩ := h_1
            left; exact x_in_A
          . obtain ⟨x_in_A, _⟩ := h_1
            left; exact x_in_A
        . obtain ⟨_, x_in_C⟩ := h
          right; exact x_in_C
    . -- Show x ∈ B ∪ C
      cases lhs
      . cases h -- More of the same ...
        . obtain ⟨_, x_in_B⟩ := h_1
          left; exact x_in_B
        . obtain ⟨_, x_in_C⟩ := h_1
          right; exact x_in_C
      . obtain ⟨x_in_B, _⟩ := h
        left; exact x_in_B

-- The set difference operation is denoted by B \ A
-- This can be simplified using rw [mem_diff] where
#check mem_diff

-- In this theorem, the partial proof has been outlined.
-- Your task is to fill in the sorry
-- the following theorem can be helpful
#check subset_union_left

/-
  Proof strategy for P4 is:
  * Forward direction
    * Use equality "A ∪ X = B" to make the proof goal "A ⊆ A ∪ X", then construct the latter via subset_union_left
  * Reverse direction
    * Treat proof goal "A ∪ B \ A = B" as bi-implication "x ∈ A ∪ B \ A ↔ x ∈ B"
    * Prove bi-implication in two directions
      1) Show "x ∈ A ∪ B \ A  →  x ∈ B" by
         * Assuming LHS
         * Treating LHS "x ∈ A ∪ B \ A" as disjunction "x ∈ A, or x ∈ B \ A"
         * Branching over disjunction, and using suitable assumptions to obtain required disjunct
      2) Show "x ∈ B  →  x ∈ A ∪ B \ A": similar, but more involved
-/

theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · -- Forward direction: if there exists X such that A ∪ X = B, then A ⊆ B
    intro lhs
    obtain ⟨X, hx⟩ := lhs
    have h := @subset_union_left α A X
    rewrite [hx] at h -- Use "hx : A ∪ X = B" to rewrite "h" from "A ⊆ A ∪ X" to "A ⊆ B".
                      -- I.e. in "h", replace "A ∪ X" with "B" by using the equality from "hx".
    exact h
  · -- Reverse direction: if A ⊆ B, then there exists X such that A ∪ X = B
    intro h           -- "Assume A ⊆ B"
    use B \ A         -- "Let X = B \ A"
    ext x
    constructor
    . -- Show x ∈ A ∪ B \ A  →  x ∈ B
      intro lhs
      cases lhs
      . apply h
        exact h_1
      . rewrite [mem_diff] at h_1
        obtain ⟨x_in_B, _⟩ := h_1
        exact x_in_B
    . -- Show x ∈ B  →  x ∈ A ∪ B \ A
      intro lhs
      rewrite [mem_union]
      rewrite [subset_def] at h
      rewrite [mem_diff]
      by_cases ha : x ∈ A
      . left
        exact ha
      . right
        exact (And.intro lhs ha)
end

section
variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset
-- Finset is a set whose cardinality is bounded
-- If A is a Finset, then #A is the cardinality of the set

/- Recall rw tactics:
If thm is a theorem a = b, then as a rewrite rule,
  rw [thm] means to replace a with b, and
  rw [← thm] means to replace b with a.
-/

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

-- you may find the following operations useful
#check card_union
#check card_eq_zero
#check Nat.two_mul


/-
  Proof strategy for P5 is:
  1. Obtain "#(A ∪ B) = #A + #B" by
      a) Using card_eq_zero to obtain #(A ∩ B) = 0 ↔ A ∩ B = ∅.
         Since A ∩ B = ∅ is known, we can conclude #(A ∩ B) = 0.
      b) Using card_union to obtain (A ∪ B) = #A + #B - #(A ∩ B)
         Since #(A ∩ B) = 0 is known, we can conclude (A ∪ B) = #A + #B - 0,
         which is trivially our proof goal.
  2. With #(A ∪ B) = #A + #B we (effectively) aim to prove #(A ∪ B) = 2 * k for some k.
     This means proving #A + #B = 2 * k, and since #A = #B, it means proving #B + #B = 2 * k.
     Using #B for k and Nat.two_mul, we can conclude the proof.
-/

theorem P5 (U : Finset α) (A B : Finset α)
(hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) : IsEven (#U) := by
  -- Hint: First prove the following claim:
  have AB_eq: #(A ∪ B) = #A + #B := by
    rewrite [IsDisjoint] at hAB
    have h1 := @card_eq_zero α (A ∩ B) -- QUESTION: I don't properly understand the difference between @foo ...
    have h2 := card_union A B          --           ... and just foo. Could you please explain this in the lecture?
    have h3 := h1.mpr hAB
    rewrite [h2]
    rewrite [h3]
    trivial
  -- Then use AB_eq to finish the proof
  rewrite [← htotal]
  rewrite [AB_eq]
  rewrite [IsEven]
  rewrite [hcard]
  use #B
  rewrite [Nat.two_mul]
  trivial
