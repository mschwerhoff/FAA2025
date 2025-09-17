import Mathlib.Tactic



section BasicLogic

/-! ## Basic Logic

These exercises practice the fundamental logical reasoning tactics.
Remember:
- Use `intro` to introduce hypotheses for implications
- Use `exact` when you have exactly what you need
- Use `constructor` to split goals like `P ∧ Q` or `P ↔ Q`
-/

variable (P Q R : Prop)

-- Example: reflexivity of implication
example : P → P := by
  intro h
  exact h

-- Exercise 3: Simple implication chain
example : P → (Q → P) := by
  intro hP hQ
  exact hP

-- Exercise 4: Transitivity of implication
example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ
  intro hQR
  intro hP
  apply hPQ at hP
  apply hQR at hP
  exact hP

example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ
  intro hQR
  intro hP
  apply hQR
  apply hPQ
  apply hP

-- Exercise 5: Conjunction introduction
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  . exact hP
  . exact hQ

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  . apply hP
  . apply hQ

-- Exercise 6: Conjunction commutativity
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  . intro hPQ
    symm
    exact hPQ
  . intro hQP
    symm
    exact hQP

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  . intro hPQ
    exact (And.symm hPQ)
  . intro hQP
    exact (And.symm hQP)

-- Exercise 7: More complex logical reasoning
example : (P → Q) ∧ (P → R) → (P → Q ∧ R) := by
  intro lhs
  intro hP
  obtain ⟨hPQ, hPR⟩ := lhs
  constructor
  . apply hPQ
    exact hP
  . apply hPR
    exact hP


end BasicLogic


section ApplyTactic

variable (P Q R S : Prop)

-- Example: basic apply usage
example (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  exact h2

example (h1 : P → Q) (h2 : P) : Q := by
  apply h1 at h2
  exact h2

example (h1 : P → Q) (h2 : P) : Q := by
  have hQ: Q := by
    apply h1 at h2
    exact h2
  exact hQ

-- Exercise 8: Chaining apply
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  apply h2
  apply h1
  apply h3

-- Exercise 9: Apply with multiple premises (from w1sheet2 style)
example (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by
  obtain ⟨hP, hQ, hR⟩ := h0
  apply h
  --apply hP
  --apply hQ
  --apply hR
  all_goals trivial


-- Exercise 10: Mixed apply and intro
example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ
  intro hQR
  intro hP
  apply hPQ at hP
  apply hQR at hP
  exact hP

example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  apply hP

example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  exact hQR (hPQ hP)

example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  -- have hQ : Q := (hPQ hP)
  -- have hQ := (hPQ hP)
  -- obtain hQ : Q := (hPQ hP)
  obtain hQ := (hPQ hP)
  obtain hR := (hQR hQ)
  exact hR

example : (P → Q) → (Q → R) → (P → R) := by
  exact fun a1 a2 a3 => a2 (a1 a3)



-- Hint: Chain the implications by working backwards from the goal
example (P Q R : Prop) : ((P → Q) ∧ (Q → R)) → (P → R) := by
  sorry


end ApplyTactic

section Functions

def f := fun x : ℕ ↦ fun y : ℕ ↦ x = y

-- Exercise 11: Basic function application
example : f 0 0 := by
  rewrite [f]
  rfl

-- Exercise 12: Function reasoning
example (x : ℕ) : f 0 x → x = 0 := by
  rewrite [f]
  intro lhs
  symm
  exact lhs

-- Exercise 13: Function with inequality
example (x : ℕ) : f x 1 → x ≠ 2 := by
  rewrite [f]
  intro lhs
  intro not_rhs -- by_contra not_rhs
  rewrite [lhs] at not_rhs -- rewrite [not_rhs] at lhs
  contradiction


-- Exercise 14: More complex function reasoning
example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by
  rewrite [f, f]
  intro lhs
  obtain ⟨xzero, yzero⟩ := lhs
  symm at xzero
  rewrite [xzero]
  exact yzero

end Functions
