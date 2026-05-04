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

structure unionFind (nodeList : List node) : Type where
  mk ::
  linkList : List (unionFindLink nodeList)
  matching_nodeId : ∀ x ∈ nodeList, ∃! y ∈ linkList, x.id = y.nodeId
  matching_ccId : ∀ y ∈ linkList, ∃! x ∈ nodeList, x.id = y.ccId
  matching_length : nodeList.length = linkList.length
  -- matching_rank : ∀ y ∈ linkList, y.nodeId = y.ccId ∨ y.rank < (List.choose (fun x => x.nodeId = y.ccId) linkList h?).rank -- irgentwie sowas

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

      ⟨a, h_a₁, h_a₂, h_a₃⟩
    else
      let a : List (unionFindLink nodeList) := []
      ⟨a, by simp at h; simp [h], by simp [a], by simp at h; simp [h, a]⟩



def connected_component_of_unionFind_of_id_helper {nodeList : List node} (u : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) (r : Fin (nodeList.length)): Nat :=
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
      have h''' : ∃ x_1 ∈ nodeList, x_1.id = x.ccId := by
        rcases h'' with ⟨y, h_in_and_eq, h_rest⟩
        refine ⟨y, ?_⟩
        simp [h_in_and_eq]
      have h_r : x.rank > r := by sorry
      connected_component_of_unionFind_of_id_helper u x.ccId h''' x.rank -- TODO fix
termination_by sorry

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
      have h'' := u.matching_ccId x sorry
      have h''' : ∃ x_1 ∈ nodeList, x_1.id = x.ccId := by
        rcases h'' with ⟨y, h_in_and_eq, h_rest⟩
        refine ⟨y, ?_⟩
        simp [h_in_and_eq]
      connected_component_of_unionFind_of_id_helper u x.ccId h''' x.rank




def kruskal_helper (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) : List edge :=
  match edgeList with
  | [] => []
  | e::es =>
    let x := (connected_component_of_unionFind_of_id uF e.node1 sorry)
    let y := (connected_component_of_unionFind_of_id uF e.node2 sorry)
    if x = y
      then
        kruskal_helper es nodeList uF
      else
        -- let updated_uF := update_unionFind uF x y
        e::(kruskal_helper es nodeList uF)

def kruskal (edgeList : List edge) : Set edge :=
    let edgeListSorted := edgeList.mergeSort
    let nodeList : List node := sorry
    let init : unionFind nodeList := init_unionFind nodeList
    {e | e ∈ kruskal_helper edgeList nodeList init}
