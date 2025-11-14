
import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Problem 1: Finding Min Recursively
def minimum (a b:ℕ ): ℕ := if a < b then a else b

-- Consider the following FindMin function
def FindMin (l : List ℕ) : ℕ :=
  match h: l with
  | [] => 0   -- Base case for empty list (0 is minimum in ℕ)
  | x::xs =>
      if he: xs = [] then x
      else
        have: 1 < l.length := by
          simp [h]
          by_contra!
          observe: xs.length = 0
          simp_all only [le_refl, List.length_eq_zero_iff]
        let n := l.length
        let left  := l.take (n / 2)
        let right := l.drop (n / 2)
        -- Recursive step: find max of each half and compare
        minimum (FindMin left) (FindMin right)
termination_by l.length decreasing_by all_goals grind

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- You can use the following APIs.
-- # In this problem, prove that the FindMin algorithm correctly returns the minimum element for any non-empty input list of size n.
-- You may find the following theorems useful
theorem x_minlist_of_x_lt_minlist {x y: ℕ} {l: List ℕ }
      (h1: x ≤ y)
      (h2: y.MinOfList l)
    : x.MinOfList l := by
  grind [Nat.MinOfList]

theorem min_list_of_left_right {x : ℕ} {l : List ℕ}
      (left right: List ℕ)
      (h_lr: left ++ right = l)
      (h_min_left: x.MinOfList left)
      (h_min_right: x.MinOfList right)
    : x.MinOfList l := by
  grind [Nat.MinOfList]

theorem Problem1 (l : List ℕ) (h_nonempty : l.length > 0) :
    let z := FindMin l
    z.MinOfList l := by
  fun_induction FindMin l
  . trivial
  . simp
    unfold Nat.MinOfList
    rw [List.forall_mem_singleton]
  . simp_all
    -- TODO: Replace grind by manual steps to understand what happens here
    have hll : 0 < left.length := by grind
    have hrl : 0 < right.length := by grind
    -- apply ih1 at hrl
    -- apply ih2 at hll
    simp_all -- also performs preceding IH applications
    unfold minimum
    split_ifs
    . rename_i min_is_left
      change (FindMin left).MinOfList (x :: xs)
      have h' : n = xs.length + 1 := by trivial
      rw [← h'] at min_is_left

      have hleft : left = List.take (n / 2) (x :: xs) := by rfl
      have hright : right = List.drop (n / 2) (x :: xs) := by rfl
      rw [← hleft] at min_is_left
      rw [← hright] at min_is_left

      have h'' : (left ++ right) = (x :: xs) := by aesop -- TODO: Manual steps?
      -- grind [Nat.MinOfList] suffices
      have min_is_left' : FindMin left ≤ FindMin right := Nat.le_of_lt min_is_left
      have ih1' : (FindMin left).MinOfList right := by exact x_minlist_of_x_lt_minlist min_is_left' ih1
      have h''' := @min_list_of_left_right (FindMin left) (x :: xs) left right h'' ih2 ih1'
      exact h'''
    . rename_i min_is_right
      simp at min_is_right
      have h'' : (left ++ right) = (x :: xs) := by aesop
      grind [Nat.MinOfList]

-- # Problem 2: Finding Min Sequentially
-- Define minimum property
def Option.MinOfList (result : Option ℕ) (l : List ℕ) : Prop :=
  match result with
  | none => l = []
  | some m => m ∈ l ∧ ∀ x ∈ l, m ≤ x

def List.minHelper (xs : List ℕ)(val_so_far : ℕ) : ℕ := match xs with
  | [] => val_so_far
  | x :: xs => xs.minHelper (min x val_so_far)

def List.FindMin : List ℕ → Option ℕ
  | [] => none
  | x :: xs => some (xs.minHelper x)

-- # In problem 2, prove that FindMIn function correctly compute the mininmum
lemma Problem2 (l : List ℕ) : l.FindMin.MinOfList l := by sorry


-- For problem 3 and 4, we will use the following version of Merge and Sorted
-- # Merge
def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

-- # Sorted
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 3: Prove that y ∈ Merge xs (y :: ys)
-- You may find this List functions helpful
#check List.mem_cons_of_mem
#check List.mem_cons_self

theorem Problem3 (y : ℕ) (xs ys: List ℕ) : y ∈ Merge xs (y :: ys) := by sorry

-- # Problem 4: Prove that Merge function is commutative on sorted inputs
-- `nth_rewrite` tactic can be useful to rewrite a specific occurence
-- You may find this function useful and you may find the API about merge and sorted helpful
#check Merge.eq_def

-- # API about Merge
-- In this homework, let's assume you have access to the following theorems.
-- Proving these theorems are optional.
theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := sorry
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by sorry
theorem merge_min_out (x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) : Merge (x :: ys) xs = x :: Merge ys xs := sorry
theorem merge_min_out_sym(x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) (h_min_in_ys : ∀ y ∈ ys, x ≤ y) : Merge ys (x ::xs)  = x :: Merge ys xs := by sorry

theorem Problem4  (xs ys: List ℕ) (h1: Sorted xs) (h2: Sorted ys): Merge xs ys = Merge ys xs := by sorry

-- # Problem 5: Prove that the index returned by this contain_bs correctly corresponds to q
-- Consider the following SortedArrayFun and contain_bs function

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

def contains_bs {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1) (by omega)
  where bs_aux (a b :ℕ) (h: a ≤ b): Option ℕ  :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 :ℕ )
    if      q < arr.get mid then bs_aux a mid  (by omega)
    else if  arr.get mid < q then bs_aux (mid+1) b (by omega)
    else some mid

lemma Problem5_aux (n q :ℕ)(arr : SortedArrayFun n) (a b :ℕ)(h_le : a ≤ b) :
    ∀ i, contains_bs.bs_aux arr q a b h_le = some i → arr.get i = q := by
  fun_induction contains_bs.bs_aux <;> simp_all -- discharges all but one goal - grind discharges all
  linarith

theorem Problem5 (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
    ∀ i, contains_bs arr q = some i → arr.get i = q := by
  intro i lhs
  -- grind [contains_bs, Problem5_aux] suffices
  unfold contains_bs at lhs
  have h_aux := Problem5_aux n q arr 0 (n-1) (by linarith) i
  apply h_aux at lhs
  exact lhs
