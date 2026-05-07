import Mathlib
import «Kruskal».Lists

-- set_option trace.Meta.synthInstance true

namespace Kruskal

variable {m n : Nat} {α β : Type}


structure node : Type where
  mk ::
  id : Nat
deriving instance DecidableEq for node
instance node_LT : LT node where
  lt := (fun x y => x.id < y.id)
instance node_LE : LE node where
  le := (fun x y => x.id ≤ y.id)
instance node_Preorder : Preorder node where
  le x y := x.id ≤ y.id
  le_refl x := Nat.le_refl x.id
  le_trans _ _ _ h₁ h₂ := Nat.le_trans h₁ h₂
  lt x y := x.id < y.id
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge

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





-- l : List α
-- l.set (l.idxOf x) y

-- funktion von Node auf Zusammenhangskomponennte
structure unionFindLink (nodeList : List node) : Type where
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
  rank : Fin nodeList.length

theorem exists_parent_link {nodeList : List node} (linkList : List (unionFindLink nodeList)) (matching_nodeId : ∀ x ∈ nodeList, ∃! y ∈ linkList, x.id = y.nodeId) (matching_ccId : ∀ y ∈ linkList, ∃! x ∈ nodeList, x.id = y.ccId) : ∀ x ∈ linkList, ∃ y ∈ linkList, y.nodeId = x.ccId := by
  intro x h_x_in
  have h := ExistsUnique.exists (matching_ccId x h_x_in)
  rcases h with ⟨z, h_z_in, h_z_eq⟩
  have h := ExistsUnique.exists (matching_nodeId z h_z_in)
  rcases h with ⟨y, h_y_in, h_y_eq⟩
  refine ⟨y, h_y_in, ?_⟩
  simp [← h_y_eq, h_z_eq]

structure unionFind (nodeList : List node) : Type where
  mk ::
  linkList : List (unionFindLink nodeList)
  matching_nodeId : ∀ x ∈ nodeList, ∃! y ∈ linkList, x.id = y.nodeId
  matching_ccId : ∀ y ∈ linkList, ∃! x ∈ nodeList, x.id = y.ccId
  matching_length : nodeList.length = linkList.length
  matching_rank (y : unionFindLink nodeList) (h : y ∈ linkList) : y.nodeId = y.ccId ∨ y.rank < (List.choose (fun x => x.nodeId = y.ccId) linkList (exists_parent_link linkList matching_nodeId matching_ccId y h)).rank -- irgentwie sowas

def init_unionFind_helper (nodeList : List node) (h : nodeList.length ≠ 0) : List (unionFindLink (nodeList : List node)) :=
  helper nodeList where
    helper : List node → List (unionFindLink (nodeList : List node))
      | [] => []
      | x::xs => ⟨x.id, x.id, ⟨0, zero_lt_iff.mpr h⟩⟩ :: (helper xs)

theorem init_unionFind_helper.helper_split (nodeList l₁ l₂ : List node) (h : nodeList.length ≠ 0) : init_unionFind_helper.helper nodeList h (l₁ ++ l₂) = (init_unionFind_helper.helper nodeList h l₁) ++ (init_unionFind_helper.helper nodeList h l₂) := by
  induction l₁ with
  | nil =>
    simp [init_unionFind_helper.helper]
  | cons y ys ih =>
    simp [init_unionFind_helper.helper, ih]

theorem init_unionFind_helper.helper_all_self_connected (nodeList l : List node) (h : nodeList.length ≠ 0) : ∀ x ∈ (init_unionFind_helper.helper nodeList h l), x.nodeId = x.ccId := by
  intro x h_in
  induction l with
  | nil =>
    simp [init_unionFind_helper.helper] at h_in
  | cons y ys ih =>
    simp [init_unionFind_helper.helper] at h_in
    rcases h_in with ⟨h_eq⟩ | ⟨h_in⟩
    · simp [h_eq]
    · exact ih h_in

theorem init_unionFind_helper.helper_all_rank_zero (nodeList l : List node) (h : nodeList.length ≠ 0) : ∀ x ∈ (init_unionFind_helper.helper nodeList h l), x.rank = ⟨0, zero_lt_iff.mpr h⟩ := by
  intro x h_in
  induction l with
  | nil =>
    simp [init_unionFind_helper.helper] at h_in
  | cons y ys ih =>
    simp [init_unionFind_helper.helper] at h_in
    rcases h_in with ⟨h_eq⟩ | ⟨h_in⟩
    · simp [h_eq]
    · exact ih h_in

theorem init_unionFind_helper.helper_eq_length (nodeList : List node) (h : nodeList.length ≠ 0) (l : List node) : (init_unionFind_helper.helper nodeList h l).length = l.length := by
  induction l with
  | nil =>
    simp [init_unionFind_helper.helper]
  | cons x xs ih =>
    simp [init_unionFind_helper.helper, ih]

theorem init_unionFind_helper.helper_eq_input (nodeList : List node) (h₁ : nodeList.length ≠ 0) (l₁ l₂ : List node) (h₂ : init_unionFind_helper.helper nodeList h₁ l₁ = init_unionFind_helper.helper nodeList h₁ l₂) : l₁ = l₂ := by
  have h_eq_length : l₁.length = l₂.length := by
    have h := init_unionFind_helper.helper_eq_length nodeList h₁
    simp [← h l₁, ← h l₂, h₂]
  induction l₁ generalizing l₂ with
  | nil =>
    induction l₂ with
    | nil =>
      rfl
    | cons y ys ih₂ =>
      simp [init_unionFind_helper.helper] at h₂
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      simp [init_unionFind_helper.helper] at h₂
    | cons y ys =>
      simp [init_unionFind_helper.helper] at h₂
      have h_eq : ⟨x.id⟩ = y := by
        simp [h₂.left]
      simp
      constructor
      · simp [← h_eq]
      · simp at h_eq_length
        exact ih ys h₂.right h_eq_length

def nodeList_of_unionFindLinkList (nodeList : List node) : List (unionFindLink nodeList) → List node
  | [] => []
  | x::xs => ⟨x.nodeId⟩ :: (nodeList_of_unionFindLinkList nodeList xs)

theorem init_unionFind_helper.helper_split_reverse (nodeList : List node) (h₁ : nodeList.length ≠ 0) (l₁ l₂ : List (unionFindLink nodeList)) (h₂ : init_unionFind_helper.helper nodeList h₁ nodeList = l₁ ++ l₂) : ∃ k₁ k₂, nodeList = k₁ ++ k₂ ∧ init_unionFind_helper.helper nodeList h₁ k₁ = l₁ ∧ init_unionFind_helper.helper nodeList h₁ k₂ = l₂ := by
  set k₁ := nodeList_of_unionFindLinkList nodeList l₁
  set k₂ := nodeList_of_unionFindLinkList nodeList l₂
  refine ⟨k₁, k₂, ?_⟩
  have h_eq₂ : helper nodeList h₁ k₁ = l₁ := by
    have h_in : ∀ x ∈ l₁, x ∈ helper nodeList h₁ nodeList := by
      simp [h₂]
      intro x h_in
      left
      exact h_in
    clear h₂
    induction l₁ with
    | nil =>
      simp [k₁, nodeList_of_unionFindLinkList, init_unionFind_helper.helper]
    | cons x xs ih =>
      simp [k₁, nodeList_of_unionFindLinkList, init_unionFind_helper.helper]
      constructor
      · have h_in' : x ∈ helper nodeList h₁ nodeList := by
          simp [h_in]
        nth_rewrite 2 [init_unionFind_helper.helper_all_self_connected nodeList nodeList h₁ x h_in']
        rw [← init_unionFind_helper.helper_all_rank_zero nodeList nodeList h₁ x h_in']
      · have h_in' : ∀ x ∈ xs, x ∈ helper nodeList h₁ nodeList := by
          intro y h_y_in
          have h_y_in' : y ∈ x :: xs := by
            simp [h_y_in]
          simp [h_in y h_y_in']
        simp at ih
        have ih := ih h_in'
        exact ih

  have h_eq₃ : helper nodeList h₁ k₂ = l₂ := by
    have h_in : ∀ x ∈ l₂, x ∈ helper nodeList h₁ nodeList := by
      simp [h₂]
      intro x h_in
      right
      exact h_in
    clear h₂
    induction l₂ with
    | nil =>
      simp [k₂, nodeList_of_unionFindLinkList, init_unionFind_helper.helper]
    | cons x xs ih =>
      simp [k₂, nodeList_of_unionFindLinkList, init_unionFind_helper.helper]
      constructor
      · have h_in' : x ∈ helper nodeList h₁ nodeList := by
          simp [h_in]
        nth_rewrite 2 [init_unionFind_helper.helper_all_self_connected nodeList nodeList h₁ x h_in']
        rw [← init_unionFind_helper.helper_all_rank_zero nodeList nodeList h₁ x h_in']
      · have h_in' : ∀ x ∈ xs, x ∈ helper nodeList h₁ nodeList := by
          intro y h_y_in
          have h_y_in' : y ∈ x :: xs := by
            simp [h_y_in]
          simp [h_in y h_y_in']
        simp at ih
        have ih := ih h_in'
        exact ih

  have h_eq₁ : nodeList = k₁ ++ k₂ := by
    have h := init_unionFind_helper.helper_split nodeList k₁ k₂ h₁
    rw [h_eq₂, h_eq₃, ← h₂] at h
    have h_eq := init_unionFind_helper.helper_eq_input nodeList h₁ nodeList (k₁ ++ k₂) h.symm
    exact h_eq

  refine ⟨h_eq₁, h_eq₂, h_eq₃⟩

def init_unionFind (nodeList : List node) : unionFind (nodeList : List node) :=
  if h : nodeList.length ≠ 0
    then
      let a : List (unionFindLink nodeList) := (init_unionFind_helper nodeList h)
      have h_a₁ : ∀ x ∈ nodeList, ∃! y, y ∈ a ∧ x.id = y.nodeId := by
        intro x h_in
        -- simp [a, init_unionFind_helper]
        set y : unionFindLink nodeList := ⟨x.id, x.id, ⟨0, zero_lt_iff.mpr h⟩⟩
        rcases (mem_split h_in) with ⟨l₁, l₂, h_split, h_nin⟩
        have h_y_in : y ∈ a := by
          simp [a, init_unionFind_helper, y, h_split, init_unionFind_helper.helper_split]
          right
          simp [init_unionFind_helper.helper]
        refine ⟨y, ?_⟩
        constructor
        · constructor
          · exact h_y_in
          · simp [y]
        · intro z h_z
          rcases h_z with ⟨h_z_in, h_z_eq_id⟩
          simp [a, init_unionFind_helper] at h_z_in
          have h_z_eq_self := init_unionFind_helper.helper_all_self_connected nodeList nodeList h z h_z_in
          have h_z_eq_cc : x.id = z.ccId := by
            rw [← h_z_eq_self]
            exact h_z_eq_id
          have h_z_rank_zero := init_unionFind_helper.helper_all_rank_zero nodeList nodeList h z h_z_in
          simp [y]
          nth_rewrite 1 [h_z_eq_id]
          rw [h_z_eq_cc, ← h_z_rank_zero]

      have h_a₂ : ∀ y ∈ a, ∃! x, x ∈ nodeList ∧ x.id = y.ccId := by
        intro y h_in
        set x : node := ⟨y.nodeId⟩
        refine ⟨x, ?_⟩
        constructor
        · simp
          constructor
          · rcases (mem_split h_in) with ⟨l₁,l₂, h_a_eq, h_nin⟩
            simp [a, init_unionFind_helper] at h_a_eq
            have h_split := init_unionFind_helper.helper_split_reverse nodeList h l₁ (y::l₂) h_a_eq
            rcases h_split with ⟨k₁, k₂, h_eq₁, h_eq₂,h_eq₃⟩
            cases k₂ with
            | nil =>
              simp [init_unionFind_helper.helper] at h_eq₃
            | cons z k₂ =>
              simp [init_unionFind_helper.helper] at h_eq₃
              rcases h_eq₃ with ⟨h_y_eq, h_eq₃⟩
              have h_x_eq : x = z := by
                simp [x, ← h_y_eq]
              rw [h_x_eq]
              simp [h_eq₁]
          · simp [a, init_unionFind_helper] at h_in
            simp [x, init_unionFind_helper.helper_all_self_connected nodeList nodeList h y h_in]
        · simp
          intro z h_z_in h_z_eq
          simp [x, init_unionFind_helper.helper_all_self_connected nodeList nodeList h y h_in, ← h_z_eq]

      have h_a₃ : nodeList.length = a.length := by
        simp [a, init_unionFind_helper]
        exact (init_unionFind_helper.helper_eq_length nodeList h nodeList).symm

      ⟨a, h_a₁, h_a₂, h_a₃, by
        intro y h_y_in
        left
        exact init_unionFind_helper.helper_all_self_connected nodeList nodeList h y h_y_in
      ⟩
    else
      let a : List (unionFindLink nodeList) := []
      ⟨a, by simp at h; simp [h], by simp [a], by simp at h; simp [h, a], by intro y h_y_in; simp [a] at h_y_in⟩

theorem self_connected_of_max_rank {nodeList : List node} (u : unionFind nodeList) (x : unionFindLink nodeList) (h_x_in : x ∈ u.linkList) : x.rank.succ = nodeList.length → x.nodeId = x.ccId := by
  rcases u.matching_rank x h_x_in with ⟨h_eq⟩ | ⟨h_lt⟩
  · simp [h_eq]
  · intro h_eq
    let y : unionFindLink nodeList := List.choose (fun y => y.nodeId = x.ccId) u.linkList (exists_parent_link u.linkList u.matching_nodeId u.matching_ccId x h_x_in)
    have h_y_eq : y = List.choose (fun y => y.nodeId = x.ccId) u.linkList (exists_parent_link u.linkList u.matching_nodeId u.matching_ccId x h_x_in) := by rfl
    simp [← h_y_eq] at h_lt
    have h_lt_succ : nodeList.length < y.rank.succ := by
      simp [← h_eq, h_lt]
    simp at h_lt_succ
    contrapose! h_lt_succ
    exact y.rank.isLt

def connected_component_of_unionFind_of_id_helper {nodeList : List node} (u : unionFind nodeList) (x : unionFindLink nodeList) (h_x_in : x ∈ u.linkList): Nat :=
  if h_self_connected : x.ccId = x.nodeId
    then
      x.ccId
    else
      let y : unionFindLink nodeList := List.choose (fun y => y.nodeId = x.ccId) u.linkList (exists_parent_link u.linkList u.matching_nodeId u.matching_ccId x h_x_in)
      have h_y_in : y ∈ u.linkList := List.choose_mem (fun y => y.nodeId = x.ccId) u.linkList (exists_parent_link u.linkList u.matching_nodeId u.matching_ccId x h_x_in)

      have h_r : y.rank > x.rank := by
        rcases u.matching_rank x h_x_in with ⟨h⟩ | ⟨h⟩
        · simp [h] at h_self_connected
        · have h_y_eq : y = List.choose (fun y => y.nodeId = x.ccId) u.linkList (exists_parent_link u.linkList u.matching_nodeId u.matching_ccId x h_x_in) := by rfl
          rw [← h_y_eq] at h
          exact h

      connected_component_of_unionFind_of_id_helper u y h_y_in
termination_by x.rank

def connected_component_of_unionFind_of_id {nodeList : List node} (u : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id): Nat :=
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
      have h_x_in : x ∈ u.linkList := by
        exact List.choose_mem (fun x => x.nodeId = id) u.linkList h'
      have h'' := u.matching_ccId x h_x_in
      have h''' : ∃ x_1 ∈ nodeList, x_1.id = x.ccId := by
        rcases h'' with ⟨y, h_in_and_eq, h_rest⟩
        refine ⟨y, ?_⟩
        simp [h_in_and_eq]
      connected_component_of_unionFind_of_id_helper u x h_x_in



def matching_edge  (edgeList : List edge) (nodeList : List node) : Prop := ∀ x ∈ edgeList, (∃ y ∈ nodeList, x.node1 = y.id) ∧ (∃ z ∈ nodeList, x.node2 = z.id)



def kruskal_helper (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (matching_edge : matching_edge edgeList nodeList) : List edge :=
  match edgeList with
  | [] => []
  | e::es =>
    have h : ∃ x ∈ nodeList, x.id = e.node1 := by
      have h : (∃ x ∈ nodeList, e.node1 = x.id) → (∃ x ∈ nodeList, x.id = e.node1) := by simp [eq_comm]
      simp [h (matching_edge e List.mem_cons_self).left]
    let x := (connected_component_of_unionFind_of_id uF e.node1 h)
    have h' : ∃ x ∈ nodeList, x.id = e.node2 := by
      have h' : (∃ x ∈ nodeList, e.node2 = x.id) → (∃ x ∈ nodeList, x.id = e.node2) := by simp [eq_comm]
      simp [h' (matching_edge e List.mem_cons_self).right]
    let y := (connected_component_of_unionFind_of_id uF e.node2 h')
    have matching_edge' : ∀ x ∈ es, (∃ y ∈ nodeList, x.node1 = y.id) ∧ ∃ z ∈ nodeList, x.node2 = z.id := by
      intro z h_in
      simp [matching_edge z (List.mem_cons_of_mem e h_in)]
    if x = y
      then
        kruskal_helper es nodeList uF matching_edge'
      else
        -- let updated_uF := update_unionFind uF x y
        e::(kruskal_helper es nodeList uF matching_edge')

def kruskal (edgeList : List edge) (nodeList : List node) (matching_edge : matching_edge edgeList nodeList): List edge :=
    let edgeListSorted := edgeList.mergeSort
    let uF : unionFind nodeList := init_unionFind nodeList
    kruskal_helper edgeList nodeList uF matching_edge





def nodeList_of_edgeList_helper (edgeList : List edge) (nodeList : List node) : List node :=
  match edgeList with
  | [] => nodeList
  | e::es =>
    let x : node := ⟨e.node1⟩
    let y : node := ⟨e.node2⟩
    if x ∈ nodeList ∧ y ∈ nodeList
      then
        nodeList_of_edgeList_helper es nodeList
      else
        if x ∈ nodeList
          then
            nodeList_of_edgeList_helper es (y::nodeList)
          else
            if y ∈ nodeList
              then
                nodeList_of_edgeList_helper es (x::nodeList)
              else
                if x = y
                  then
                    nodeList_of_edgeList_helper es (x::nodeList)
                  else
                    nodeList_of_edgeList_helper es (x::y::nodeList)

def nodeList_of_edgeList (edgeList : List edge) : List node :=
  nodeList_of_edgeList_helper edgeList []

theorem nodeList_of_edgeList_helper_eq (edgeList : List edge) (nodeList : List node) : nodeList_of_edgeList_helper edgeList nodeList = ((nodeList_of_edgeList_helper edgeList []).filter (fun x => x ∉ nodeList)) ++ nodeList := by
  induction edgeList generalizing nodeList with -- generalizing nodeList
  | nil =>
    simp [nodeList_of_edgeList_helper]
  | cons x edgeList ih =>
    simp [nodeList_of_edgeList_helper]
    by_cases h_both_in : { id := x.node1 } ∈ nodeList ∧ { id := x.node2 } ∈ nodeList
    · simp [h_both_in]
      by_cases h_eq : x.node1 = x.node2
      · simp [h_eq, ih [{ id := x.node2 }]]
        simp [h_both_in.right]
        have h : (fun a => !decide (a ∈ nodeList) && !decide (a = { id := x.node2 })) = (fun a => !decide (a ∈ nodeList)) := by
          funext a
          by_cases h : a = { id := x.node2 }
          · simp [h, h_both_in]
          · simp [h]
        simp [h, ih nodeList]
      · simp [h_eq, ih [{ id := x.node1 }, { id := x.node2 }]]
        simp [h_both_in]
        have h : (fun a => !decide (a ∈ nodeList) && (!decide (a = { id := x.node1 }) && !decide (a = { id := x.node2 }))) = (fun a => !decide (a ∈ nodeList)) := by
          funext a
          by_cases h : a = { id := x.node1 }
          · simp [h, h_both_in]
          · by_cases h' : a = { id := x.node2 }
            · simp [h', h_both_in]
            · simp [h, h']
        simp [h, ih nodeList]
    · simp [h_both_in]
      by_cases h_1_in : { id := x.node1 } ∈ nodeList
      · simp [h_1_in]
        by_cases h_eq : x.node1 = x.node2
        · simp [h_eq] at h_1_in
          simp [h_eq, h_1_in] at h_both_in
        · simp [h_1_in] at h_both_in
          simp [h_eq, ih [{ id := x.node1 }, { id := x.node2 }], h_1_in, h_both_in]
          have h : (fun a => !decide (a ∈ nodeList) && (!decide (a = { id := x.node1 }) && !decide (a = { id := x.node2 }))) = (fun a => !decide (a ∈ { id := x.node2 }::nodeList)) := by
            funext a
            by_cases h : a = { id := x.node1 }
            · simp [h, h_1_in]
            · simp [h]
              by_cases h' : a = { id := x.node2 }
              · simp [h']
              · simp [h']
          simp [h, ih ({ id := x.node2 } :: nodeList)]
      · simp [h_1_in]
        by_cases h_2_in : { id := x.node2 } ∈ nodeList
        · simp [h_2_in]
          by_cases h_eq : x.node1 = x.node2
          · simp [h_eq] at h_1_in
            simp [h_1_in] at h_2_in
          · simp [h_eq, ih [{ id := x.node1 }, { id := x.node2 }], h_1_in, h_2_in]
            have h : (fun a => !decide (a ∈ nodeList) && (!decide (a = { id := x.node1 }) && !decide (a = { id := x.node2 }))) = (fun a => !decide (a ∈ { id := x.node1 }::nodeList)) := by
              funext a
              by_cases h : a = { id := x.node2 }
              · simp [h, h_2_in]
              · simp [h, Bool.and_comm]
            simp [h, ih ({ id := x.node1 } :: nodeList)]
        · simp [h_2_in]
          by_cases h_eq : x.node1 = x.node2
          · simp [h_eq, ih [{ id := x.node2 }], h_2_in, ih ({ id := x.node2 } :: nodeList), Bool.and_comm]
          · simp [h_eq, ih [{ id := x.node1 }, { id := x.node2 }], h_1_in, h_2_in, ih ({ id := x.node1 }::{ id := x.node2 } :: nodeList), Bool.and_comm]
            have h : (fun x_1 => !decide (x_1 = { id := x.node1 }) && (!decide (x_1 ∈ nodeList) && !decide (x_1 = { id := x.node2 }))) = (fun a => !decide (a ∈ nodeList) && (!decide (a = { id := x.node1 }) && !decide (a = { id := x.node2 }))) := by
              funext a
              rw [← Bool.and_assoc]
              nth_rewrite 2 [Bool.and_comm]
              simp [Bool.and_assoc]
            simp [h]

theorem mem_nodeList_of_edgeList_helper_iff_node_in_edgeList (edgeList : List edge) (x : node) : x ∈ nodeList_of_edgeList_helper edgeList [] ↔ ∃ y ∈ edgeList, y.node1 = x.id ∨ y.node2 = x.id := by
  sorry

theorem mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList (edgeList : List edge) (nodeList : List node) (x : node) : x ∈ nodeList_of_edgeList_helper edgeList nodeList ↔ x ∈ nodeList_of_edgeList_helper edgeList [] ∨ x ∈ nodeList := by
  constructor
  · intro h_in
    have h := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList x).mpr
    by_cases h_ex_edge : ∃ y ∈ edgeList, y.node1 = x.id ∨ y.node2 = x.id
    · left
      exact h h_ex_edge
    · right
      by_cases h_in_nodeList : x ∈ nodeList
      · exact h_in_nodeList
      · contrapose! h_in
        clear h
        induction nodeList with
        | nil =>
          simp [Iff.not (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList x), h_ex_edge]
        | cons y nodeList ih =>
          have h := nodeList_of_edgeList_helper_eq edgeList (y::nodeList)
          simp at h_in
          simp [h, h_in]
          simp [Iff.not (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList x), h_ex_edge]
  · intro h_in
    rcases h_in with ⟨h_in⟩ | ⟨h_in⟩
    · simp [nodeList_of_edgeList_helper_eq edgeList nodeList, h_in]
      by_cases h_in : x ∈ nodeList
      · simp [h_in]
      · simp [h_in]
    · simp [nodeList_of_edgeList_helper_eq edgeList nodeList, h_in]

theorem matching_edge_for_nodeList_of_edgeList (edgeList : List edge) : matching_edge edgeList (nodeList_of_edgeList edgeList) := by
  simp [matching_edge]
  intro e h_e_in
  constructor
  · simp [nodeList_of_edgeList]
    let x : node := ⟨e.node1⟩
    refine ⟨x, ?_, by simp [x]⟩
    induction edgeList with
    | nil =>
      simp at h_e_in
    | cons f es ih =>
      by_cases h_eq : e = f
      · simp [nodeList_of_edgeList_helper]
        by_cases h : f.node1 = f.node2
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node2 }] x).mpr
          right
          rw [← h]
          simp [← h_eq, x]
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node1 }, { id := f.node2 }] x).mpr
          right
          simp [← h_eq, x]
      · simp [h_eq] at h_e_in
        simp [h_e_in] at ih
        simp [nodeList_of_edgeList_helper]
        by_cases h : f.node1 = f.node2
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node2 }] x).mpr
          left
          exact ih
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node1 }, { id := f.node2 }] x).mpr
          left
          exact ih
  · simp [nodeList_of_edgeList]
    let x : node := ⟨e.node2⟩
    refine ⟨x, ?_, by simp [x]⟩
    induction edgeList with
    | nil =>
      simp at h_e_in
    | cons f es ih =>
      by_cases h_eq : e = f
      · simp [nodeList_of_edgeList_helper]
        by_cases h : f.node1 = f.node2
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node2 }] x).mpr
          right
          simp [← h_eq, x]
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node1 }, { id := f.node2 }] x).mpr
          right
          simp [← h_eq, x]
      · simp [h_eq] at h_e_in
        simp [h_e_in] at ih
        simp [nodeList_of_edgeList_helper]
        by_cases h : f.node1 = f.node2
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node2 }] x).mpr
          left
          exact ih
        · simp [h]
          apply (mem_nodeList_of_edgeList_helper_iff_mem_nodeList_of_edgeList_helper_of_nil_or_mem_nodeList es [{ id := f.node1 }, { id := f.node2 }] x).mpr
          left
          exact ih
