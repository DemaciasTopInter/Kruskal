import Mathlib

variable {m n : Nat} {α β : Type}


structure node where
  mk ::
  id : Nat

-- instance node_BEq : BEq node where
--   beq x y := x.id = y.id

-- instance node_Eq : Eq (node (n := n)) (node (n := n)) :=
--   fun x y => x.id = y.id

-- instance node_DecidableEq : DecidableEq (node (n := n.succ)) :=
--     fun x y => if h : x.id == y.id then isTrue h else isFalse h

structure edge where
  mk ::
  id : Nat
  node1 : Nat
  node2 : Nat
  cost : Nat
  nodesLt : node1 < node2

instance edge_LE : LE edge where
  le a b := LE.le a.cost b.cost

def graph_of_edges (edges : Set edge) : Graph node edge where
    vertexSet := {x | ∃ e ∈ edges, x.id = e.node1 ∨ x.id = e.node2}
    IsLink (e : edge) (x y :node) := e ∈ edges ∧ ((e.node1 = x.id ∧ e.node2 = y.id) ∨ (e.node1 = y.id ∧ e.node2 = x.id))
    isLink_symm := by
        intro e h_e_in x y h_eq
        rcases h_eq with ⟨h_in, h_eq⟩
        rcases h_eq with ⟨h⟩ | ⟨h⟩
        simp [h_in, h]
        simp [h_in, h]
    eq_or_eq_of_isLink_of_isLink := by
        intro e x y v w h_eq1 h_eq2
        rcases h_eq1 with ⟨h_in1, h_eq1⟩
        rcases h_eq2 with ⟨h_in2, h_eq2⟩
        rcases h_eq1 with ⟨h11, h12⟩ | ⟨h11, h12⟩
        rcases h_eq2 with ⟨h21, h22⟩ | ⟨h21, h22⟩
        left
        rw [h11] at h21
        cases x
        cases v
        cases h21
        rfl

        right
        rw [h11] at h21
        cases x
        cases w
        cases h21
        rfl

        rcases h_eq2 with ⟨h21, h22⟩ | ⟨h21, h22⟩
        right
        rw [h12] at h22
        cases x
        cases w
        cases h22
        rfl

        left
        rw [h12] at h22
        cases x
        cases w
        cases h22
        rfl
    left_mem_of_isLink := by
        intro e x y h_eq
        rcases h_eq with ⟨h_in_edges, h_eq⟩
        simp
        refine ⟨e, h_in_edges, ?_⟩
        rcases h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        simp [h1]
        simp [h2]

theorem edgeSet_of_graph_of_edges_eq_edges (edges : Set edge) : (graph_of_edges edges).edgeSet = edges := by
    simp [graph_of_edges]
    intro e h_in
    let x : node := ⟨e.node1⟩
    let y : node := ⟨e.node2⟩
    refine ⟨x, y, ?_⟩
    simp [x, y]

def path (G : Graph α β) (l : List α) : Prop :=
    match l with
    | [] => true
    | _::[] => true
    | x::(y::xs) => (∃ e ∈ G.edgeSet, G.IsLink e x y) ∧ path G (y::xs)

def connected (G : Graph α β) : Prop :=
    ∀ x ∈ G.vertexSet, ∀ y ∈ G.vertexSet, ∃ l : List α, ∀ a ∈ l, a ∈ G.vertexSet ∧ path G l






-- l : List α
-- l.set (l.idxOf x) y

-- funktion von Node auf Zusammenhangskomponennte
def unionFind : Type := node → Nat



def kruskal (edgeList : List edge) (h : connected (graph_of_edges {e | e ∈ edgeList})) : Set edge :=
    let edgeListSorted := edgeList.mergeSort
    let init : unionFind := fun x => x.id
    {e | e ∈ edgeList}
