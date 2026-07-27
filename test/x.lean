def hello := "Kruskal"
#check hello
def t : Fin 32 := { val := 16, isLt := by omega }
#check Type 1
abbrev succc (x : Nat) : Nat := x.succ.succ
#check succc
inductive Vacant : Type where
#check Vacant
-- def v : Vacant := sorry
-- #check v
-- #eval! v





def myType : Type := Nat × String
abbrev myType' : Type := Nat × String
def myFun (m : myType') : String := m.2
def test : myType' := (3, "test")
#check test
#eval test

class Group (α : Type) (add : α → α → α) where
    e : α
    add_assoc (a b c : α) : add (add a b) c = add a (add b c)
    ex_nutral : ∀ (a : α), add a e = a
    ex_invers : ∀ (a : α), ∃ (h : α), add a h = e

inductive Tree (α : Type) : Type where
    | Leaf (a : α) : Tree α
    | Brach (a : α) (children : List (Tree α)) : Tree α

universe u

inductive myList (α : Type) : Type where
  | nil : myList α
  | cons (head : α) (tail : myList α) : myList α

#check myList myType


inductive myPropList (α : Prop) : Prop where
  | nil : myPropList α
  | cons (head : α) (tail : myPropList α) : myPropList α


#check myPropList (3 = 2 + 1)

theorem test_myPropList : myPropList (3 = 2 + 1) := .cons (by omega) .nil

#check test_myPropList
-- #eval test_myPropList
