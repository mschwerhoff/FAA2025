import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

/-! New tactics
 * `left`  -- change the goal of the form P ∨ Q to P
 * `right` -- change the goal of the form P ∨ Q to Q
 * `cases` -- deal with cases. That is, if you have h: P ∨ Q then cases h will automatically split into two goals.
              One goal assume P and the other goal assume Q.
 * `by_cases` -- prove by cases
-/

open Set
variable {α : Type*} -- Asteriks means that the type is of kind 1 (the lowest in the type hierarchy)
variable (A B C D: Set α)

-- Example: Left/Right tactics
example : A ⊆ A ∪ B := by
  rw [@subset_def]
  intro x hx
  rw [@mem_union]
  left
  exact hx

-- Example: by_cases tactics
example (x : α) : x ∈ A ∨ x ∉ A := by
  by_cases h : x ∈ A
  · left; exact h
  · right; exact h

-- Example: cases tactics
example: ∀ x ∈ A ∪ B, x ∈ A ∪ B ∪ C:= by
  intro x hx
  cases hx
  left
  left
  exact h
  left
  right
  exact h

example: ∀ x ∈ A ∪ B, x ∈ A ∪ B ∪ C:= by
  intro x hx
  rewrite [mem_union]
  left
  exact hx

-- Exercise 5: Cases tactics. You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

lemma my_union_subset_imp :  A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by
  intro lhs
  obtain ⟨left, right⟩ := lhs
  rewrite [subset_def]
  intro x hx
  rewrite [subset_def] at left
  --obtain ⟨x1, hx1⟩ := left
  rewrite [subset_def] at right
  rewrite [mem_union] at hx
  cases hx
  . apply left
    exact h
  . apply right
    exact h

-- Extend my_union_subset_imp to my_union_subset_iff
-- You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

-- running example
lemma my_union_subset_iff:  A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  intro a
  exact my_union_subset_imp A B C a
  intro
  rw [Set.subset_def] at a
  constructor
  intro x hx
  apply a
  simp only [mem_union]
  left
  exact hx
  intro x hx
  apply a
  right
  exact hx

-- Exercise 6: you may want to use my_union_subset_iff
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  intro left mid
  rewrite [subset_def]
  intro x x_subset_B_union_C
  rewrite [subset_def] at left
  rewrite [subset_def] at mid
  rewrite [mem_union] at x_subset_B_union_C
  cases x_subset_B_union_C
  . apply left at h
    exact h
  . apply mid at h
    exact h

/-! New tactics
 * `ext`  -- extensionality. Proving that two functions are identical. Since sets are functions in Lean, `ext` can be used to prove set equality.
-/

-- example
lemma inter_comm: A ∩ B = B ∩ A := by
  ext x
  constructor
  . rintro ⟨a,b⟩
    exact ⟨b,a⟩
  . rintro ⟨a,b⟩
    exact ⟨b,a⟩

lemma inter_comm2: A ∩ B = B ∩ A := by
  ext x
  constructor
  . intro h
    rw [@mem_inter_iff]
    obtain ⟨h1, h2⟩ := h
    constructor
    exact h2
    exact h1
  . intro h
    rewrite [mem_inter_iff] at h
    -- Option 1
    obtain ⟨x_in_B, x_in_A⟩ := h
    constructor
    . exact x_in_A
    . exact x_in_B
    -- -- Option 2
    -- obtain ⟨x_in_B, x_in_A⟩ := h
    -- exact (mem_inter x_in_A x_in_B)

-- example
lemma absorption_law: A ∩ (A ∪ B) = A := by
  ext x
  constructor
  · intro
    exact a.1
  · intro
    constructor
    · exact a
    · left
      exact a

-- Exercise 7
lemma union_comm : A ∪ B = B ∪ A := by
  ext x
  constructor
  . intro lhs
    rewrite [mem_union] at lhs
    rewrite [mem_union]
    cases lhs
    . right
      exact h
    . left
      exact h
  . intro rhs
    rewrite [mem_union] at rhs
    rewrite [mem_union]
    exact (Or.symm rhs) -- alternative to the more manual proof used in the first case
