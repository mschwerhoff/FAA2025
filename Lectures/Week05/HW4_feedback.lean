import Mathlib.Tactic
set_option autoImplicit false
set_option tactic.hygienic false

-- All tactics are welcome.

-- # Problem 1: Predicate AllEven
-- Define Predicate `AllEven` is true if every number in the list is even.
-- e.g., [], [2], [8, 0, 4]
-- Complete the definition for AllEven. It should take a list of natural numbers (List ℕ) and return a Prop

def isEven (n :ℕ) : Prop := ∃k, n = 2*k

-- Your AllEven must use isEven function above
inductive AllEven : List ℕ → Prop
  | nil : AllEven []
  | singleton (x : ℕ) : isEven x → AllEven [x]
  | cons (x : ℕ) (xs : List ℕ) : isEven x → AllEven xs → AllEven (x :: xs)

-- Prove that your AllEven predicate is equivalent to checking if every element in the list is even.
-- Let's split into two parts

-- # Part 1
theorem Problem1_1 (l : List ℕ)  :
  AllEven l → ∀ n ∈ l, isEven n := by
    intro lhs n n_in_l
    induction' lhs
    -- all_goals grind suffices
    . -- base case n ∈ l = []
      unfold isEven
      trivial
    . -- base case n ∈ l = [x]
      unfold isEven
      unfold isEven at a
      -- grind suffices
      obtain ⟨k, h2⟩ := a
      use k
      rw [← h2]
      rw [List.mem_singleton] at n_in_l
      exact n_in_l
    . -- inductive case n ∈ l = x :: xs
      unfold isEven
      rw [List.mem_cons] at n_in_l
      -- grind [isEven] suffices
      rcases n_in_l
      . -- n = x
        unfold isEven at a
        obtain ⟨k, h2⟩ := a
        use k
        rw [← h2]
        exact h
      . -- n ∈ xs
        apply a_ih at h
        unfold isEven at h
        obtain ⟨k, h2⟩ := h
        use k

-- # Part 2
theorem Problem1_2 (l : List ℕ)  :
  (h : ∀ n ∈ l, isEven n) → AllEven l := by
    intro lhs
    unfold isEven at lhs
    induction' l
    . exact AllEven.nil
    . rw [List.forall_mem_cons] at lhs
      obtain ⟨h_head, h_tail⟩ := lhs
      have iseven_head : (isEven head) := h_head
      -- observe iseven_head : (isEven head) -- QUESTION: This yields "iseven_head : ∃ k, head = 2 * k",
      --                                     --           but not "iseven_head : (isEven head)". Why?
      apply tail_ih at h_tail
      exact (AllEven.cons head tail iseven_head h_tail)

-- # Sorted
-- We will use the following version of Sorted

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 2: Prove that a list of length at most 1 is sorted.
def len : List ℕ → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

theorem Problem2 (l : List ℕ) (h: len l ≤ 1): Sorted l := by
  unfold len at h
  split at h
  . -- grind [Sorted] suffices
    exact (Sorted.nil)
  . unfold len at h
    -- all_goals grind [Sorted] suffices
    split at h
    . exact (Sorted.single head)
    . linarith


-- # Problem 3: Prove basic properties of Sorted
theorem Problem3_1 {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  cases hxs
  . exact (Sorted.nil)
  . exact a_2
  . exact a_2

lemma drop_second {x y : ℕ} {zs: List ℕ} (hsort : Sorted (x :: y :: zs)) : Sorted (x :: zs) := by
  cases hsort
  . -- grind [Sorted, Nat.MinOfList] suffices
    cases a_2
    . exact Sorted.single x
    . have h : x ≤ b := by linarith
      exact Sorted.cons x b t h a_4
    . rw [Nat.MinOfList] at a_3
      have h : (∀ z ∈ zs, x ≤ z) := fun z hz => Nat.le_trans a_1 (a_3 z hz)
      exact Sorted.cons_min x zs h a_4
  . grind [Sorted, Nat.MinOfList]

lemma sorted_to_min {x : ℕ} {xs : List ℕ} (hsort : Sorted (x :: xs)) : x.MinOfList xs := by
  induction' xs
  . rw [Nat.MinOfList]
    have h : (∀ y ∈ [], x ≤ y) := fun y hemp => nomatch hemp
    exact h
  . cases hsort
    -- all_goals grind [Sorted, Nat.MinOfList] suffices
    . rw [Nat.MinOfList]
      rw [List.forall_mem_cons]
      constructor
      . exact a_1
      . have hh := Sorted.cons x head tail a_1 a_2
        apply drop_second at hh
        apply tail_ih at hh
        exact hh
    . exact a_1

theorem Problem3_2 {x y : ℕ} {t : List ℕ} (hsort : Sorted (x :: y :: t)) : y.MinOfList t := by
  induction' t
  . rw [Nat.MinOfList]
    simp
  . cases hsort
    -- all_goals grind [Sorted, Nat.MinOfList] suffices
    . exact sorted_to_min a_2
    . exact sorted_to_min a_2


-- # Problem 4: Alternate Definitions of Sorted
-- Consider the following inductive predicate
inductive Sorted2: List ℕ  → Prop
  | nil : Sorted2 []
  | single (a : ℕ) : Sorted2 [a]
  | cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → Sorted2 (b :: t) → Sorted2 (a :: b :: t)

-- Prove that Sorted2 is equivalent to Sorted
-- You may find `ext` tactic useful
theorem Problem4 : Sorted2 = Sorted := by
  ext
  constructor
  . -- Proof Sorted2 x → Sorted x
    intro lhs
    induction' x
    . exact Sorted.nil
    . cases lhs
      . exact Sorted.single head
      . apply tail_ih at a_2
        exact Sorted.cons head b t a_1 a_2
  . -- Proof Sorted x → Sorted2 x
    intro lhs
    induction' x
    . exact Sorted2.nil
    . cases lhs
      -- all_goals grind [Sorted2, Nat.MinOfList] suffices. I wonder, which reasoning steps it performs.
      . exact Sorted2.single head
      . apply tail_ih at a_2
        exact Sorted2.cons head b t a_1 a_2
      . have a_2' := a_2
        apply tail_ih at a_2
        rw [Nat.MinOfList] at a_1
        cases a_2
        . exact Sorted2.single head
        . rw [List.forall_mem_singleton] at a_1
          exact Sorted2.cons head a [] a_1 (Sorted2.single a)
        . rw [List.forall_mem_cons] at a_1
          obtain ⟨h, _⟩ := a_1
          apply tail_ih at a_2'
          exact Sorted2.cons head a (b :: t) h a_2'

-- # Problem 5: Binary Tree
-- Consider the following version of BinaryTree
inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

lemma mirror_preserves_nil1 (t : BinaryTree) : mirror t = BinaryTree.nil ↔ t = BinaryTree.nil := by
  -- grind [mirror, BinaryTree] suffices
  constructor
  . intro mt_is_nil
    cases t
    . rfl
    . cases mt_is_nil
  . intro t_is_nil
    simp_all
    trivial

lemma mirror_preserves_nil2 (l r : BinaryTree) : (mirror l = BinaryTree.nil ↔ mirror r = BinaryTree.nil) ↔ (l = BinaryTree.nil ↔ r = BinaryTree.nil) := by
  -- grind [mirror, BinaryTree] suffices
  constructor
  . intro ml_iff_mr
    constructor
    . intro l_is_nil
      have ml_is_nil := (mirror_preserves_nil1 l).mpr l_is_nil
      have mr_is_nil := ml_iff_mr.mp ml_is_nil
      have r_is_nil := (mirror_preserves_nil1 r).mp mr_is_nil
      exact r_is_nil
    . grind [mirror_preserves_nil1] -- analogous
  . grind [mirror_preserves_nil1] -- analogous

-- Prove that if a mirror of t is complete then t is complete
theorem Problem5: ∀t : BinaryTree, Complete (mirror t) → Complete t := by
  intro t lhs
  induction' t
  -- all_goals grind [Complete, mirror] suffices
  . exact Complete.leaf
  . cases lhs
    apply left_ih at hr
    apply right_ih at hl
    ----
    rw [iff_comm] at hiff
    have h := (mirror_preserves_nil2 left right).mp hiff
    exact Complete.node left key right hr hl h

/-! # GRADING FEEDBACK
   Score: 100/100
   Q1: 20/20
   Q2: 20/20
   Q3: 20/20
   Q4: 20/20
   Q5: 20/20

   Excellent work! Well-structured proofs with helpful helper lemmas.
-/
