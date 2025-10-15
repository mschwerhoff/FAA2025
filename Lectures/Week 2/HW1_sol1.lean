import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false

/- # HW1 Model Solution
This solution demonstrates good practices including:
- Clear proof strategies
- Appropriate use of basic tactics
- Clean code structure with proper indentation
- Helpful comments where needed
-/

section
open Set
variable {α : Type*}
variable (A B C : Set α)

/-
  Proof strategy for P1:

  We prove both directions of the biconditional separately.

  (→) Assume (B ∪ C) ⊆ A. We show B ⊆ A ∧ C ⊆ A by proving each conjunct:
      - For B ⊆ A: Take arbitrary x ∈ B. Then x ∈ B ∪ C (by left injection),
        so x ∈ A by the assumption.
      - For C ⊆ A: Similar, using right injection.

  (←) Assume B ⊆ A and C ⊆ A. To show (B ∪ C) ⊆ A:
      Take arbitrary x ∈ B ∪ C. Then x ∈ B or x ∈ C.
      - If x ∈ B, then x ∈ A by B ⊆ A.
      - If x ∈ C, then x ∈ A by C ⊆ A.
-/

lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by
  constructor
  · intro h
    constructor
    · intro x hx
      apply h
      left
      exact hx
    · intro x hx
      apply h
      right
      exact hx
  · intro ⟨hB, hC⟩ x hx
    cases hx
    · apply hB; exact h
    · apply hC; exact h

/-
  Proof strategy for P2:

  We use set extensionality to reduce the equality to showing that for all x,
  x ∈ A ∩ (B ∪ C) ↔ x ∈ (A ∩ B) ∪ (A ∩ C).

  (→) Assume x ∈ A ∩ (B ∪ C), so x ∈ A and x ∈ B ∪ C.
      Case analysis on x ∈ B ∪ C:
      - If x ∈ B: Then x ∈ A ∩ B, so x ∈ (A ∩ B) ∪ (A ∩ C).
      - If x ∈ C: Then x ∈ A ∩ C, so x ∈ (A ∩ B) ∪ (A ∩ C).

  (←) Assume x ∈ (A ∩ B) ∪ (A ∩ C).
      Case analysis:
      - If x ∈ A ∩ B: Then x ∈ A and x ∈ B, so x ∈ A and x ∈ B ∪ C.
      - If x ∈ A ∩ C: Then x ∈ A and x ∈ C, so x ∈ A and x ∈ B ∪ C.
-/

theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro ⟨hA, hBC⟩
    cases hBC
    · left
      exact ⟨hA, h⟩
    · right
      exact ⟨hA, h⟩
  · intro h
    cases h
    · obtain ⟨hA, hB⟩ := h_1
      constructor
      · exact hA
      · left; exact hB
    · obtain ⟨hA, hC⟩ := h_1
      constructor
      · exact hA
      · right; exact hC

/-
  Proof strategy for P3:

  We use set extensionality and prove both directions.

  (→) Assume x ∈ (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C).
      This means x ∈ A ∪ B, x ∈ A ∪ C, and x ∈ B ∪ C.

      We perform nested case analysis:
      - If x ∈ A: From x ∈ B ∪ C, we get x ∈ B or x ∈ C.
        Either way, we have x ∈ A ∩ B or x ∈ A ∩ C.
      - If x ∈ B: From x ∈ A ∪ C, we get x ∈ A or x ∈ C.
        If x ∈ A, then x ∈ A ∩ B. If x ∈ C, then x ∈ B ∩ C.

      In all cases, x is in the right-hand side.

  (←) Assume x ∈ (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C).
      We do case analysis on which intersection x belongs to:
      - If x ∈ A ∩ B: Then x ∈ A and x ∈ B, which easily gives all three unions.
      - If x ∈ A ∩ C: Then x ∈ A and x ∈ C, which easily gives all three unions.
      - If x ∈ B ∩ C: Then x ∈ B and x ∈ C, which gives all three unions.
-/

theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by
  ext x
  constructor
  · intro ⟨⟨hAB, hAC⟩, hBC⟩
    cases hAB
    · cases hBC
      · left; left; exact ⟨h, h_1⟩
      · left; right; exact ⟨h, h_1⟩
    · cases hAC
      · left; left; exact ⟨h_1, h⟩
      · right; exact ⟨h, h_1⟩
  · intro h
    cases h
    · cases h_1
      · obtain ⟨hA, hB⟩ := h
        constructor
        · constructor
          · left; exact hA
          · left; exact hA
        · left; exact hB
      · obtain ⟨hA, hC⟩ := h
        constructor
        · constructor
          · left; exact hA
          · left; exact hA
        · right; exact hC
    · obtain ⟨hB, hC⟩ := h_1
      constructor
      · constructor
        · right; exact hB
        · right; exact hC
      · left; exact hB

/-
  Proof strategy for P4:

  (→) Assume ∃ X, A ∪ X = B. We show A ⊆ B.
      Obtain witness X with A ∪ X = B.
      For any x ∈ A, we have x ∈ A ∪ X (by left injection),
      so x ∈ B by the equality.

  (←) Assume A ⊆ B. We show ∃ X, A ∪ X = B.
      Choose X = B \ A as witness.
      We prove A ∪ (B \ A) = B by set extensionality:

      (⊆) Take x ∈ A ∪ (B \ A).
          - If x ∈ A: Then x ∈ B by A ⊆ B.
          - If x ∈ B \ A: Then x ∈ B by definition of set difference.

      (⊇) Take x ∈ B.
          By case analysis on whether x ∈ A:
          - If x ∈ A: Then x ∈ A ∪ (B \ A) by left injection.
          - If x ∉ A: Then x ∈ B \ A, so x ∈ A ∪ (B \ A) by right injection.
-/

theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · intro ⟨X, hX⟩
    rw [← hX]
    exact subset_union_left
  · intro h
    use B \ A
    ext x
    constructor
    · intro hx
      cases hx
      · apply h; exact h_1
      · rw [mem_diff] at h_1
        exact h_1.left
    · intro hxB
      by_cases hxA : x ∈ A
      · left; exact hxA
      · right
        rw [mem_diff]
        exact ⟨hxB, hxA⟩

end

section
variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

/-
  Proof strategy for P5:

  First, we prove the helper claim that #(A ∪ B) = #A + #B:
  - By the inclusion-exclusion principle: #(A ∪ B) = #A + #B - #(A ∩ B)
  - Since A and B are disjoint: A ∩ B = ∅
  - Therefore #(A ∩ B) = 0
  - So #(A ∪ B) = #A + #B - 0 = #A + #B

  Then we prove IsEven(#U):
  - We need to show ∃ k, #U = 2 * k
  - From A ∪ B = U: #U = #(A ∪ B)
  - From the claim: #U = #A + #B
  - From #A = #B: #U = #B + #B
  - By definition of multiplication: #B + #B = 2 * #B
  - So we can choose k = #B as our witness
-/

theorem P5 (U : Finset α) (A B : Finset α)
(hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) : IsEven (#U) := by
  -- First prove the helper claim
  have AB_eq : #(A ∪ B) = #A + #B := by
    rw [card_union]
    rw [IsDisjoint] at hAB
    rw [← card_eq_zero] at hAB
    rw [hAB]
    rfl

  -- Now prove the main goal
  rw [IsEven]
  use #B
  rw [← htotal, AB_eq, hcard, Nat.two_mul]

end
