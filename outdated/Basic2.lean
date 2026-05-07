import Mathlib

-- set_option trace.Meta.synthInstance true

namespace Kruskal

variable {m n : Nat} {α β : Type}


structure node : Type where
  mk ::
  id : Nat
deriving instance DecidableEq for node

structure edge : Type where
  mk ::
  id : Nat
  node1 : Nat
  node2 : Nat
  cost : Nat
  nodesLt : node1 < node2
deriving instance DecidableEq for edge
instance edge_LE : LE edge where
  le a b := LE.le a.cost b.cost

def nodes_of_edges (edges : Set edge) : Set node :=
  {x | ∃ e ∈ edges, x.id = e.node1 ∨ x.id = e.node2}

def List_nodes_of_edges (edges : List edge) : List node :=
  match edges with
    | [] => []
    | e::es => ⟨e.node1⟩::⟨e.node2⟩::(List_nodes_of_edges es)

noncomputable def Finset_nodes_of_edges (edges : Finset edge) : Finset node := -- muss irgentwie besser gehen
  -- Finset.fold (fun a b => a ∪ b) ∅ (fun e => {⟨e.node1⟩, ⟨e.node2⟩}) edges
  List.toFinset (List_nodes_of_edges edges.toList)

def graph_of_edges (edges : Set edge) : Graph node edge where
    vertexSet := nodes_of_edges edges
    IsLink (e : edge) (x y :node) := e ∈ edges ∧ ((e.node1 = x.id ∧ e.node2 = y.id) ∨ (e.node1 = y.id ∧ e.node2 = x.id))
    isLink_symm := by
        intro e h_e_in x y h_eq
        rcases h_eq with ⟨h_in, h_eq⟩
        rcases h_eq with ⟨h⟩ | ⟨h⟩
        · simp [h_in, h]
        · simp [h_in, h]
    eq_or_eq_of_isLink_of_isLink := by
        intro e x y v w h_eq1 h_eq2
        rcases h_eq1 with ⟨h_in1, h_eq1⟩
        rcases h_eq2 with ⟨h_in2, h_eq2⟩
        rcases h_eq1 with ⟨h11, h12⟩ | ⟨h11, h12⟩
        · rcases h_eq2 with ⟨h21, h22⟩ | ⟨h21, h22⟩
          · left
            rw [h11] at h21
            cases x
            cases v
            cases h21
            rfl

          · right
            rw [h11] at h21
            cases x
            cases w
            cases h21
            rfl

        · rcases h_eq2 with ⟨h21, h22⟩ | ⟨h21, h22⟩
          · right
            rw [h12] at h22
            cases x
            cases w
            cases h22
            rfl

          · left
            rw [h12] at h22
            cases x
            cases w
            cases h22
            rfl
    left_mem_of_isLink := by
        intro e x y h_eq
        rcases h_eq with ⟨h_in_edges, h_eq⟩
        refine ⟨e, h_in_edges, ?_⟩
        rcases h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1]
        · simp [h2]

theorem edgeSet_of_graph_of_Finset_edges_eq_Finset_edges (edges : Finset edge) : (graph_of_edges edges).edgeSet = edges := by
    have h : ∀ x ∈ (graph_of_edges edges).edgeSet, x ∈ edges := by
      simp  [graph_of_edges]
      intro x h_in
      simp [h_in]
    have h' : ∀ x ∈ edges, x ∈ (graph_of_edges edges).edgeSet := by
      simp  [graph_of_edges]
      intro e h_in
      let x : node := ⟨e.node1⟩
      let y : node := ⟨e.node2⟩
      refine ⟨h_in, x, y, ?_⟩
      simp [x, y]
    ext e
    constructor
    · apply h
    · apply h'

theorem vertexSet_of_graph_of_Finset_edges_eq_Finset_nodes_of_edges (edges : Finset edge) : (graph_of_edges edges).vertexSet = Finset_nodes_of_edges edges := by
  ext x
  simp [graph_of_edges, nodes_of_edges, Finset_nodes_of_edges]
  -- constructor
  -- · intro h
  --   rcases h with ⟨e, h_in, h_eq⟩
  --   rcases h_eq with ⟨h_eq⟩
  --   · simp [Finset.fold]
  --   · t
  -- · t
  sorry




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
structure unionFindLink (nodeSet : Finset node) : Type where
  mk ::
  /--
  The `id` of the node it belongs to.
  -/
  nodeId : Nat
  /--
  The `id` of the first node in the connected component.

  The `ccId` is initialized with the nod's own `id`.
  -/
  ccId : Nat
  /--
  The number of nodes pointing at this one.
  -/
  rank : Fin nodeSet.card

structure unionFind (nodeSet : Finset node) : Type where
  mk ::
  linkList : List (unionFindLink nodeSet)
  matching_nodeId : ∀ x ∈ nodeSet, ∃! y ∈ linkList, x.id = y.nodeId
  matching_ccId : ∀ y ∈ linkList, ∃! x ∈ nodeSet, x.id = y.ccId
  matching_length : nodeSet.card = linkList.length
  -- matching_rank : ∀ y ∈ linkList, y.nodeId = y.ccId ∨ y.rank < (List.choose (fun x => x.nodeId = y.ccId) linkList h?).rank -- irgentwie sowas

noncomputable def init_unionFind_helper (nodeSet : Finset node) (h : nodeSet.card ≠ 0) : List (unionFindLink (nodeSet : Finset node)) :=
  let nodes := nodeSet.toList
  helper nodes where
    helper
      | [] => []
      | x::xs => ⟨x.id, x.id, ⟨0, zero_lt_iff.mpr h⟩⟩ :: (helper xs)

def init_unionFind (nodeSet : Finset node) : unionFind (nodeSet : Finset node) :=
  if h : nodeSet.card ≠ 0
    then
      let a : List (unionFindLink nodeSet) := (init_unionFind_helper nodeSet h)
      ⟨a, by
        intro x h_in
        simp [a, init_unionFind_helper]
        sorry
      , by
        simp [a]
        sorry
      , by
        simp at h; simp [h, a]
        sorry
      ⟩
    else
      let a : List (unionFindLink nodeSet) := []
      ⟨a, by simp at h; simp [h], by simp [a], by simp at h; simp [h, a]⟩

-- def init_unionFind (nodes : List node) (h : nodes.length ≠ 0) : List (unionFind (nodes : List node)) :=
--   helper nodes where
--     helper
--       | [] => []
--       | x::xs => ⟨x.id, x.id, ⟨0, zero_lt_iff.mpr h⟩⟩ :: (helper xs)


def connected_component_of_unionFind_of_id_helper {nodeSet : Finset node} (u : unionFind nodeSet) (id : Nat) (h : ∃ x ∈ nodeSet, x.id = id) (r : Fin (nodeSet.card)): Nat :=
  have h' : ∃ x ∈ u.linkList, x.nodeId = id := by
    rcases h with ⟨x, h_in, h_eq⟩
    have h'' := u.matching_nodeId x h_in
    rw [h_eq] at h''
    rcases h'' with ⟨y, h_in', h_unique⟩
    refine ⟨y, ?_⟩
    simp [h_in']
  let x := List.choose (fun x => x.nodeId = id) u.linkList h'
  if x.ccId = x.nodeId
    then
      x.ccId
    else
      have h'' := u.matching_ccId x sorry
      have h''' : ∃ x_1 ∈ nodeSet, x_1.id = x.ccId := by
        rcases h'' with ⟨y, h_in_and_eq, h_rest⟩
        refine ⟨y, ?_⟩
        simp [h_in_and_eq]
      have h_r : x.rank > r := by sorry
      connected_component_of_unionFind_of_id_helper u x.ccId h''' x.rank -- TODO fix
termination_by {z : Fin (nodeSet.card) | z > r}.toFinset.card

def connected_component_of_unionFind_of_id {nodeSet : Finset node} (u : unionFind nodeSet) (id : Nat) (h : ∃ x ∈ nodeSet, x.id = id): Nat :=
  have h' : ∃ x ∈ u.linkList, x.nodeId = id := by
    rcases h with ⟨x, h_in, h_eq⟩
    have h'' := u.matching_nodeId x h_in
    rw [h_eq] at h''
    rcases h'' with ⟨y, h_in', h_unique⟩
    refine ⟨y, ?_⟩
    simp [h_in']
  let x := List.choose (fun x => x.nodeId = id) u.linkList h'
  if x.ccId = x.nodeId
    then
      x.ccId
    else
      have h'' := u.matching_ccId x sorry
      have h''' : ∃ x_1 ∈ nodeSet, x_1.id = x.ccId := by
        rcases h'' with ⟨y, h_in_and_eq, h_rest⟩
        refine ⟨y, ?_⟩
        simp [h_in_and_eq]
      connected_component_of_unionFind_of_id_helper u x.ccId h''' x.rank




def kruskal_helper (edgeList : List edge) (nodeSet : Finset node) (uF : unionFind nodeSet) : List edge :=
  match edgeList with
  | [] => []
  | e::es =>
    let x := (connected_component_of_unionFind_of_id uF e.node1 sorry)
    let y := (connected_component_of_unionFind_of_id uF e.node2 sorry)
    if x = y
      then
        kruskal_helper es nodeSet uF
      else
        -- let updated_uF := update_unionFind uF x y
        e::(kruskal_helper es nodeSet uF)

def kruskal (edgeList : List edge) : Set edge :=
    let edgeListSorted := edgeList.mergeSort
    let edgeSet : Finset edge := edgeList.toFinset
    let G := graph_of_edges edgeSet
    let nodeSet := G.vertexSet.toFinset
    -- let nodeList : List node := sorry -- nodeSet.toList
    let init : unionFind nodeSet := init_unionFind nodeSet
    {e | e ∈ kruskal_helper edgeList nodeSet init}
