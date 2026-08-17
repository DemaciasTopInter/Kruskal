import Algolean.QueryModel
-- import Mathlib.Algebra.Order.Monoid.Prod

open Algolean Algorithms

#check "Hello World!"
#check 16
def t : Fin 32 := { val := 16, isLt := by omega }
#check t
#check 16 < 32
#check t.val
#check t.isLt
#check Nat
#check Prop
#check Fin
#check Type 1

def myType : Type := Nat × String

def f (x : Nat) : Nat := 3*x^2 - 4*x + 5

structure edge : Type where
  make_edge ::
  node1 : Nat
  node2 : Nat
  nodesLt : node1 < node2

#check edge.make_edge

class Group (α : Type) (add : α → α → α) where
  e : α
  add_assoc (a b c : α) : add (add a b) c = add a (add b c)
  ex_neutral : ∀ (a : α), add a e = a
  ex_invers : ∀ (a : α), ∃ (h : α), add a h = e

instance int_Group : Group Int Add.add where
  e := 0
  add_assoc := Int.add_assoc
  ex_neutral := Int.add_zero
  ex_invers := by
    intro a
    refine ⟨-a, by grind⟩

inductive Tree (α : Type) : Type where
    | Leaf (a : α) : Tree α
    | Brach (a : α) (children : List (Tree α)) : Tree α

inductive myList (α : Type) : Type where
  | nil : myList α
  | cons (head : α) (tail : myList α) : myList α

theorem length_of_filter_mem {α : Type} {l : List α} {a : α} [DecidableEq α] (h_mem : a ∈ l) : l.length ≥ 1 + (l.filter (fun b => b ≠ a)).length := by
  induction l with
  | nil =>
    simp at h_mem
  | cons b l ih =>
    by_cases h_eq : b = a
    · simp [h_eq]
      rw [Nat.add_comm]
      simp
      exact List.length_filter_le (fun b => !decide (b = a)) l
    · simp
      rw [Nat.add_comm]
      simp
      simp [h_eq]
      simp [ne_comm.mp h_eq] at h_mem
      simp [h_mem] at ih
      rw [Nat.add_comm] at ih
      exact ih

def isZero (n : Nat) : Bool :=
  match n with
  | .zero   => true
  | .succ _ => false

def isZero' : Nat → Bool
  | .zero   => true
  | .succ _ => false

#check isZero' t
#eval isZero' t

#check Nat.gcd

def List.search {α : Type} [BEq α] (l : List α) (x : α) : Bool :=
  match l with
  | [] => false
  | head :: tail =>
    if head == x
    then true
    else search tail x

inductive ListSearch (α : Type) : Type → Type _ where
  | compare (x y : α) : ListSearch α Bool

def ListSearch.natCost {α : Type} [BEq α] : Model (ListSearch α) ℕ where
  evalQuery
    | compare x y => x == y
  cost _ := 1

def listLinearSearch {α : Type} (l : List α) (x : α) : Prog (ListSearch α) Bool := do
  match l with
  | [] => return false
  | head :: tail =>
    let cmp : Bool ← ListSearch.compare head x
    if cmp then
      return true
    else
      listLinearSearch tail x

lemma listLinearSearch_eval {α : Type} [BEq α] (l : List α) (x : α) :
    (listLinearSearch l x).eval ListSearch.natCost = l.search x := by
  fun_induction l.search x with
  | case1 =>
    simp [listLinearSearch]
  | case2 head tail h =>
    simp [listLinearSearch, ListSearch.natCost]
    simp [h]
  | case3 head tail h ih =>
    unfold listLinearSearch
    simp [ListSearch.natCost] at ⊢ ih
    simp [h]
    rw [← ih]

lemma listLinearSearchM_time_complexity_upper_bound {α : Type} [BEq α] (l : List α) (x : α) :
    (listLinearSearch l x).time ListSearch.natCost ≤ l.length := by
  fun_induction l.search x with
  | case1 =>
    simp [listLinearSearch]
  | case2 head tail h =>
    simp [listLinearSearch, ListSearch.natCost]
    simp [h]
  | case3 head tail h ih =>
    simp [listLinearSearch, ListSearch.natCost, h] at ⊢ ih
    lia
