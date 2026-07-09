-- import Mathlib
import «Kruskal».Lists

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.SuccPred

-- set_option trace.Meta.synthInstance true

namespace Kruskal

variable {m n : Nat} {α β : Type}


structure node : Type where
  mk ::
  id : Nat
deriving instance Repr for node
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
instance node_Max : Max node where
  max := fun a b => if a ≥ b then a else b
instance node_PartialOrder : PartialOrder node where
  le_antisymm := by
    intro a b
    cases a
    cases b
    rename_i a b
    intro h₁ h₂
    have h₁ : a ≤ b := h₁
    have h₂ : a ≥ b := h₂
    simp [le_antisymm h₁ h₂]
instance node_LinearOrder : LinearOrder node where
  le_antisymm := by
    intro a b h₁ h₂
    exact le_antisymm h₁ h₂
  le_total := by
    intro a b
    by_cases h : a.id ≤ b.id
    · left
      exact h
    · right
      simp at h
      exact le_of_lt h
  toDecidableLE := fun a b => inferInstance
  max_def := by
    intro a b
    by_cases h : a ≤ b
    · simp [h, max]
      intro h'
      exact le_antisymm h h'
    · simp [h, max]
      intro h'
      cases a with
      | mk a =>
      cases b with
      | mk b =>
      have h : ¬a ≤ b := h
      have h' : ¬b ≤ a := h'
      have h_contra := Nat.le_total a b
      simp [h, h'] at h_contra


  -- by
  --   simp [DecidableLE, DecidableRel]
  --   intro a b
  --   dsimp [node_LE]
  --   by_cases h : a ≤ b
  --   · simp [h, Decidable]
  --     sorry

structure edge : Type where
  mk ::
  id : Nat
  node1 : Nat
  node2 : Nat
  cost : Nat
  nodesLt : node1 < node2
deriving instance Repr for edge
instance edge_ToString : ToString edge where
  toString := fun e => s!"{'{'} id = {e.id}, node1 = {e.node1}, node2 = {e.node2}, cost = {e.cost}, nodesLt = … {'}'}\n"
deriving instance DecidableEq for edge
instance edge_LE : LE edge where
  le a b := LE.le a.cost b.cost
instance edge_DecidableLE : DecidableLE edge := inferInstance
instance edge_Preorder : Preorder edge where
  le_refl := by
    intro a
    have h : a.cost ≤ a.cost := by
      simp
    exact h
  le_trans := by
    intro a b c h1 h2
    have h3 : a.cost ≤ b.cost := by
      exact h1
    have h4 : b.cost ≤ c.cost := by
      exact h2
    exact le_trans h3 h4
-- instance edge_LinearOrder : LinearOrder edge where
--   le_antisymm := by
--     intro a b h1 h2
--     have h3 : a.cost ≤ b.cost := by
--       exact h1
--     have h4 : b.cost ≤ a.cost := by
--       exact h2
--     exact le_antisymm h3 h4 -- falsch
--   le_total := by sorry
--   toDecidableLE := by sorry
theorem edge_LinearOrder.le_total : ∀ (a b : edge), a ≤ b ∨ b ≤ a := by
  intro a b
  by_cases h : a.cost ≤ b.cost
  · left
    exact h
  · right
    have h' : b.cost ≤ a.cost := by
      simp at h
      exact le_of_lt h
    exact h'


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
  The `id` of the parent node in the unionFind strukture.

  The `ccId` is initialized with the nod's own `id`.
  -/
  ccId : Nat
  /--
  The number of nodes pointing at this one.
  -/
  rank : Fin nodeList.length
deriving instance Repr for unionFindLink
instance unionFindLink_ToString {nodeList : List node} : ToString (unionFindLink nodeList) where
  toString := fun uFL => s!"{'{'} nodeId = {uFL.nodeId}, ccId = {uFL.ccId}, rank = {uFL.rank} {'}'}\n"
deriving instance DecidableEq for unionFindLink
-- deriving instance BEq for unionFindLink
instance unionFindLink_BEq {nodeList : List node} : BEq (unionFindLink nodeList) where
  beq a b := Bool.and (Bool.and (a.nodeId == b.nodeId) (a.ccId == b.ccId)) (a.rank == b.rank)
-- deriving instance ReflBEq for unionFindLink
instance unionFindLink_ReflBEq {nodeList : List node} : ReflBEq (unionFindLink nodeList) where
  rfl {a : unionFindLink nodeList} : a == a := by
    cases a
    simp [BEq.beq]
instance unionFindLink_LawfulBEq {nodeList : List node} : LawfulBEq (unionFindLink nodeList) where
  eq_of_beq {a b : unionFindLink nodeList} : a == b → a = b := by
    simp [BEq.beq]
    intro h_nodeId h_ccId h_rank
    cases a
    cases b
    simp_all

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
  matching_rank (y : unionFindLink nodeList) (h : y ∈ linkList) : y.nodeId = y.ccId ∨ y.rank < (List.choose (fun x => x.nodeId = y.ccId) linkList (exists_parent_link linkList matching_nodeId matching_ccId y h)).rank
  nodup : linkList.Nodup
  -- rank_succ_isLt (x : unionFindLink nodeList) (y : unionFindLink nodeList) : x ≠ y → x ∈ linkList → y ∈ linkList → x.nodeId = x.ccId → y.nodeId = y.ccId → x.rank = y.rank → x.rank.val.succ < nodeList.length
  -- stattdessen: wenn es ein uFl mit Rank x gibt, dann gibt es für jedes y < x uFL mit rang y
  rankInvariant (x : unionFindLink nodeList) : x ∈ linkList → (linkList.filter (fun y => y.rank < x.rank ∧ ¬y.nodeId = y.ccId)).length ≥ x.rank

theorem unionFind.rank_succ_isLt  {nodeList : List node} (uF : unionFind nodeList) (x y : unionFindLink nodeList) : x ≠ y → x ∈ uF.linkList → y ∈ uF.linkList → x.nodeId = x.ccId → y.nodeId = y.ccId → x.rank = y.rank → x.rank.val.succ < nodeList.length := by
  intro h_ne h_x_in h_y_in h_x_selfcon h_y_selfcon h_rank_eq
  have h_rankInvariant := uF.rankInvariant x h_x_in
  set p : unionFindLink nodeList → Prop := (fun (z : unionFindLink nodeList) => decide (z.rank < x.rank ∧ ¬z.nodeId = z.ccId))
  have h_not_p_x : ¬p x := by
    simp [p]
  have h_not_p_y : ¬p y := by
    simp [p, h_rank_eq]
  have h_filter_eq : List.filter p uF.linkList = List.filter p ((uF.linkList.erase x).erase y) := by
    simp [filter_erase_eq_self_of_not_prop h_not_p_x (p := p) (l := uF.linkList)]
    simp [filter_erase_eq_self_of_not_prop h_not_p_y (p := p) (l := uF.linkList.erase x)]
  have h_length_eq : uF.linkList.length = ((uF.linkList.erase x).erase y).length + 2 := by
    have h_y_in : y ∈ (uF.linkList.erase x) := by
      simp [h_ne.symm, h_y_in]
    simp [← List.length_erase_add_one h_x_in, ← List.length_erase_add_one h_y_in]
  simp [uF.matching_length, h_length_eq]
  apply le_trans h_rankInvariant
  simp [p] at h_filter_eq
  simp
  rw [h_filter_eq]
  have h_le := List.length_filter_le p ((uF.linkList.erase x).erase y)
  simp [p] at h_le
  simp [h_le]

def init_unionFind.linkList (nodeList : List node) (h_nonempty : nodeList.length ≠ 0) : List (unionFindLink (nodeList : List node)) :=
  helper nodeList where
    helper : List node → List (unionFindLink (nodeList : List node))
      | [] => []
      | x::xs => { nodeId := x.id, ccId := x.id, rank := ⟨0, zero_lt_iff.mpr h_nonempty⟩ } :: (helper xs)

theorem init_unionFind.linkList.helper_append (nodeList l₁ l₂ : List node) (h_nonempty : nodeList.length ≠ 0) : init_unionFind.linkList.helper nodeList h_nonempty (l₁ ++ l₂) = (init_unionFind.linkList.helper nodeList h_nonempty l₁) ++ (init_unionFind.linkList.helper nodeList h_nonempty l₂) := by
  induction l₁ with
  | nil =>
    simp [init_unionFind.linkList.helper]
  | cons y ys ih =>
    simp [init_unionFind.linkList.helper, ih]

theorem init_unionFind.linkList.helper_all_self_connected (nodeList l : List node) (h_nonempty : nodeList.length ≠ 0) : ∀ x ∈ (init_unionFind.linkList.helper nodeList h_nonempty l), x.nodeId = x.ccId := by
  intro x h_in
  induction l with
  | nil =>
    simp [init_unionFind.linkList.helper] at h_in
  | cons y ys ih =>
    simp [init_unionFind.linkList.helper] at h_in
    rcases h_in with ⟨h_eq⟩ | ⟨h_in⟩
    · simp [h_eq]
    · exact ih h_in

theorem init_unionFind.linkList.helper_all_rank_zero (nodeList l : List node) (h_nonempty : nodeList.length ≠ 0) : ∀ x ∈ (init_unionFind.linkList.helper nodeList h_nonempty l), x.rank = ⟨0, zero_lt_iff.mpr h_nonempty⟩ := by
  intro x h_in
  induction l with
  | nil =>
    simp [init_unionFind.linkList.helper] at h_in
  | cons y ys ih =>
    simp [init_unionFind.linkList.helper] at h_in
    rcases h_in with ⟨h_eq⟩ | ⟨h_in⟩
    · simp [h_eq]
    · exact ih h_in

theorem init_unionFind.linkList.matching_nodeId {nodeList : List node} (h_nonempty : nodeList.length ≠ 0) : ∀ x ∈ nodeList, ∃! y, y ∈ (init_unionFind.linkList nodeList h_nonempty) ∧ x.id = y.nodeId := by
  intro x h_in
  set y : unionFindLink nodeList := ⟨x.id, x.id, ⟨0, zero_lt_iff.mpr h_nonempty⟩⟩
  rcases (mem_split h_in) with ⟨l₁, l₂, h_split, h_nin⟩
  have h_y_in : y ∈ (init_unionFind.linkList nodeList h_nonempty) := by
    simp [init_unionFind.linkList, y, h_split, init_unionFind.linkList.helper_append]
    right
    simp [init_unionFind.linkList.helper]
  refine ⟨y, ?_⟩
  constructor
  · constructor
    · exact h_y_in
    · simp [y]
  · intro z h_z
    rcases h_z with ⟨h_z_in, h_z_eq_id⟩
    simp [init_unionFind.linkList] at h_z_in
    have h_z_eq_self := init_unionFind.linkList.helper_all_self_connected nodeList nodeList h_nonempty z h_z_in
    have h_z_eq_cc : x.id = z.ccId := by
      rw [← h_z_eq_self]
      exact h_z_eq_id
    have h_z_rank_zero := init_unionFind.linkList.helper_all_rank_zero nodeList nodeList h_nonempty z h_z_in
    simp [y]
    nth_rewrite 1 [h_z_eq_id]
    rw [h_z_eq_cc, ← h_z_rank_zero]

theorem init_unionFind.linkList.helper_eq_length (nodeList : List node) (h_nonempty : nodeList.length ≠ 0) (l : List node) : (init_unionFind.linkList.helper nodeList h_nonempty l).length = l.length := by
  induction l with
  | nil =>
    simp [init_unionFind.linkList.helper]
  | cons x xs ih =>
    simp [init_unionFind.linkList.helper, ih]

theorem init_unionFind.linkList.helper_eq_input (nodeList : List node) (h_nonempty : nodeList.length ≠ 0) (l₁ l₂ : List node) (h_init_eq : init_unionFind.linkList.helper nodeList h_nonempty l₁ = init_unionFind.linkList.helper nodeList h_nonempty l₂) : l₁ = l₂ := by
  have h_eq_length : l₁.length = l₂.length := by
    have h := init_unionFind.linkList.helper_eq_length nodeList h_nonempty
    simp [← h l₁, ← h l₂, h_init_eq]
  induction l₁ generalizing l₂ with
  | nil =>
    induction l₂ with
    | nil =>
      rfl
    | cons y ys ih₂ =>
      simp [init_unionFind.linkList.helper] at h_init_eq
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      simp [init_unionFind.linkList.helper] at h_init_eq
    | cons y ys =>
      simp [init_unionFind.linkList.helper] at h_init_eq
      have h_eq : ⟨x.id⟩ = y := by
        simp [h_init_eq.left]
      simp
      constructor
      · simp [← h_eq]
      · simp at h_eq_length
        exact ih ys h_init_eq.right h_eq_length

def nodeList_of_unionFindLinkList (nodeList : List node) : List (unionFindLink nodeList) → List node
  | [] => []
  | x::xs => ⟨x.nodeId⟩ :: (nodeList_of_unionFindLinkList nodeList xs)

theorem init_unionFind.linkList.helper_append_reverse (nodeList : List node) (h_nonempty : nodeList.length ≠ 0) (l₁ l₂ : List (unionFindLink nodeList)) (h_split : init_unionFind.linkList.helper nodeList h_nonempty nodeList = l₁ ++ l₂) : ∃ k₁ k₂, nodeList = k₁ ++ k₂ ∧ init_unionFind.linkList.helper nodeList h_nonempty k₁ = l₁ ∧ init_unionFind.linkList.helper nodeList h_nonempty k₂ = l₂ := by
  set k₁ := nodeList_of_unionFindLinkList nodeList l₁
  set k₂ := nodeList_of_unionFindLinkList nodeList l₂
  refine ⟨k₁, k₂, ?_⟩
  have h_eq₂ : helper nodeList h_nonempty k₁ = l₁ := by
    have h_in : ∀ x ∈ l₁, x ∈ helper nodeList h_nonempty nodeList := by
      simp [h_split]
      intro x h_in
      left
      exact h_in
    clear h_split
    induction l₁ with
    | nil =>
      simp [k₁, nodeList_of_unionFindLinkList, init_unionFind.linkList.helper]
    | cons x xs ih =>
      simp [k₁, nodeList_of_unionFindLinkList, init_unionFind.linkList.helper]
      constructor
      · have h_in' : x ∈ helper nodeList h_nonempty nodeList := by
          simp [h_in]
        nth_rewrite 2 [init_unionFind.linkList.helper_all_self_connected nodeList nodeList h_nonempty x h_in']
        rw [← init_unionFind.linkList.helper_all_rank_zero nodeList nodeList h_nonempty x h_in']
      · have h_in' : ∀ x ∈ xs, x ∈ helper nodeList h_nonempty nodeList := by
          intro y h_y_in
          have h_y_in' : y ∈ x :: xs := by
            simp [h_y_in]
          simp [h_in y h_y_in']
        simp at ih
        have ih := ih h_in'
        exact ih

  have h_eq₃ : helper nodeList h_nonempty k₂ = l₂ := by
    have h_in : ∀ x ∈ l₂, x ∈ helper nodeList h_nonempty nodeList := by
      simp [h_split]
      intro x h_in
      right
      exact h_in
    clear h_split
    induction l₂ with
    | nil =>
      simp [k₂, nodeList_of_unionFindLinkList, init_unionFind.linkList.helper]
    | cons x xs ih =>
      simp [k₂, nodeList_of_unionFindLinkList, init_unionFind.linkList.helper]
      constructor
      · have h_in' : x ∈ helper nodeList h_nonempty nodeList := by
          simp [h_in]
        nth_rewrite 2 [init_unionFind.linkList.helper_all_self_connected nodeList nodeList h_nonempty x h_in']
        rw [← init_unionFind.linkList.helper_all_rank_zero nodeList nodeList h_nonempty x h_in']
      · have h_in' : ∀ x ∈ xs, x ∈ helper nodeList h_nonempty nodeList := by
          intro y h_y_in
          have h_y_in' : y ∈ x :: xs := by
            simp [h_y_in]
          simp [h_in y h_y_in']
        simp at ih
        have ih := ih h_in'
        exact ih

  have h_eq₁ : nodeList = k₁ ++ k₂ := by
    have h := init_unionFind.linkList.helper_append nodeList k₁ k₂ h_nonempty
    rw [h_eq₂, h_eq₃, ← h_split] at h
    have h_eq := init_unionFind.linkList.helper_eq_input nodeList h_nonempty nodeList (k₁ ++ k₂) h.symm
    exact h_eq

  refine ⟨h_eq₁, h_eq₂, h_eq₃⟩

theorem init_unionFind.linkList.matching_ccId {nodeList : List node} (h_nonempty : nodeList.length ≠ 0) : ∀ y ∈ (init_unionFind.linkList nodeList h_nonempty), ∃! x, x ∈ nodeList ∧ x.id = y.ccId := by
  intro y h_in
  set x : node := ⟨y.nodeId⟩
  refine ⟨x, ?_⟩
  constructor
  · simp
    constructor
    · rcases (mem_split h_in) with ⟨l₁,l₂, h_linkList_eq, h_nin⟩
      simp [init_unionFind.linkList] at h_linkList_eq
      have h_split := init_unionFind.linkList.helper_append_reverse nodeList h_nonempty l₁ (y::l₂) h_linkList_eq
      rcases h_split with ⟨k₁, k₂, h_eq₁, h_eq₂,h_eq₃⟩
      cases k₂ with
      | nil =>
        simp [init_unionFind.linkList.helper] at h_eq₃
      | cons z k₂ =>
        simp [init_unionFind.linkList.helper] at h_eq₃
        rcases h_eq₃ with ⟨h_y_eq, h_eq₃⟩
        have h_x_eq : x = z := by
          simp [x, ← h_y_eq]
        rw [h_x_eq]
        simp [h_eq₁]
    · simp [init_unionFind.linkList] at h_in
      simp [x, init_unionFind.linkList.helper_all_self_connected nodeList nodeList h_nonempty y h_in]
  · simp
    intro z h_z_in h_z_eq
    simp [x, init_unionFind.linkList.helper_all_self_connected nodeList nodeList h_nonempty y h_in, ← h_z_eq]

theorem init_unionFind.linkList.helper_nodup_of_nodup (nodeList : List node) (h_nonempty : nodeList.length ≠ 0) (l : List node) (h_nodup : l.Nodup) : (init_unionFind.linkList.helper nodeList h_nonempty l).Nodup := by
  induction l with
  | nil =>
    simp [init_unionFind.linkList.helper]
  | cons a as ih₁ =>
    simp [init_unionFind.linkList.helper]
    simp at h_nodup
    simp [ih₁ h_nodup.right]
    induction as with
    | nil =>
      have h : init_unionFind.linkList.helper nodeList h_nonempty [] = [] := by
        simp [init_unionFind.linkList.helper]
      simp [h]
    | cons b as ih₂ =>
      simp [init_unionFind.linkList.helper]
      simp at h_nodup
      constructor
      · cases a
        cases b
        have h := h_nodup.left.left
        simp at h
        simp [h]
      · simp [h_nodup.right.left, init_unionFind.linkList.helper, h_nodup.right.right] at ih₁
        simp [h_nodup.right.right, ih₁, h_nodup.left.right] at ih₂
        exact ih₂

def init_unionFind (nodeList : List node) (h_nodup : nodeList.Nodup) : unionFind (nodeList : List node) :=
  if h : nodeList.length ≠ 0
    then
      let linkList : List (unionFindLink nodeList) := (init_unionFind.linkList nodeList h)
      have h_matching_nodeId : ∀ x ∈ nodeList, ∃! y, y ∈ linkList ∧ x.id = y.nodeId := init_unionFind.linkList.matching_nodeId h

      have h_matching_ccId : ∀ y ∈ linkList, ∃! x, x ∈ nodeList ∧ x.id = y.ccId := init_unionFind.linkList.matching_ccId h

      have h_matching_length : nodeList.length = linkList.length := by
        simp [linkList, init_unionFind.linkList]
        exact (init_unionFind.linkList.helper_eq_length nodeList h nodeList).symm

      have h_matching_rank : ∀ (y : unionFindLink nodeList) (h : y ∈ linkList), y.nodeId = y.ccId ∨ y.rank < (List.choose (fun x => x.nodeId = y.ccId) linkList (exists_parent_link linkList h_matching_nodeId h_matching_ccId y h)).rank := by
        intro y h_y_in
        left
        exact init_unionFind.linkList.helper_all_self_connected nodeList nodeList h y h_y_in

      have h_nodup : linkList.Nodup := by
        simp [linkList, init_unionFind.linkList]
        apply init_unionFind.linkList.helper_nodup_of_nodup nodeList h nodeList h_nodup

      have h_rankInvariant : (z : unionFindLink nodeList) → z ∈ linkList → (linkList.filter (fun y => y.rank < z.rank ∧ ¬y.nodeId = y.ccId)).length ≥ z.rank := by
        simp [linkList, init_unionFind.linkList]
        intro z h_z_in
        have h_z_rank := init_unionFind.linkList.helper_all_rank_zero nodeList nodeList h z h_z_in
        simp [h_z_rank]

      ⟨linkList, h_matching_nodeId, h_matching_ccId, h_matching_length, h_matching_rank, h_nodup, h_rankInvariant⟩
    else
      let linkList : List (unionFindLink nodeList) := []
      ⟨linkList, by simp at h; simp [h], by simp [linkList], by simp at h; simp [h, linkList], by intro y h_y_in; simp [linkList] at h_y_in, by simp [linkList], by simp [linkList]⟩

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

def connected_component_of_unionFind_of_id_helper {nodeList : List node} (uF : unionFind nodeList) (x : unionFindLink nodeList) (h_x_in : x ∈ uF.linkList): Nat :=
  if h_self_connected : x.ccId = x.nodeId
    then
      x.ccId
    else
      let y : unionFindLink nodeList := List.choose (fun y => y.nodeId = x.ccId) uF.linkList (exists_parent_link uF.linkList uF.matching_nodeId uF.matching_ccId x h_x_in)
      have h_y_in : y ∈ uF.linkList := List.choose_mem (fun y => y.nodeId = x.ccId) uF.linkList (exists_parent_link uF.linkList uF.matching_nodeId uF.matching_ccId x h_x_in)

      have h_r : y.rank > x.rank := by
        rcases uF.matching_rank x h_x_in with ⟨h⟩ | ⟨h⟩
        · simp [h] at h_self_connected
        · have h_y_eq : y = List.choose (fun y => y.nodeId = x.ccId) uF.linkList (exists_parent_link uF.linkList uF.matching_nodeId uF.matching_ccId x h_x_in) := by rfl
          rw [← h_y_eq] at h
          exact h

      connected_component_of_unionFind_of_id_helper uF y h_y_in
termination_by nodeList.length - x.rank
  decreasing_by
  have h : ↑(List.choose (fun y => y.nodeId = x.ccId) uF.linkList (exists_parent_link uF.linkList uF.matching_nodeId uF.matching_ccId x h_x_in)).rank = y.rank := by
    simp [y]
  simp [h]
  apply Nat.sub_lt_sub_left
  · exact x.rank.isLt
  · exact h_r

def connected_component_of_unionFind_of_id {nodeList : List node} (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) : Nat :=
  have h' : ∃ x ∈ uF.linkList, x.nodeId = id := by
    rcases h with ⟨x, h_in, h_eq⟩
    have h'' := uF.matching_nodeId x h_in
    rw [h_eq] at h''
    rcases h'' with ⟨y, h_in', h_unique⟩
    refine ⟨y, ?_⟩
    simp [h_in']
  let x := List.choose (fun x => x.nodeId = id) uF.linkList h'
  if x.ccId = x.nodeId
    then
      x.ccId
    else
      have h_x_in : x ∈ uF.linkList := by
        exact List.choose_mem (fun x => x.nodeId = id) uF.linkList h'
      have h'' := uF.matching_ccId x h_x_in
      have h''' : ∃ x_1 ∈ nodeList, x_1.id = x.ccId := by
        rcases h'' with ⟨y, h_in_and_eq, h_rest⟩
        refine ⟨y, ?_⟩
        simp [h_in_and_eq]
      connected_component_of_unionFind_of_id_helper uF x h_x_in

theorem exist_unionFindLink_of_connected_component_of_unionFind_of_id_helper {nodeList : List node} (uF : unionFind nodeList) (x : unionFindLink nodeList) (h_x_in : x ∈ uF.linkList) : ∃ uFL ∈ uF.linkList, uFL.nodeId = connected_component_of_unionFind_of_id_helper uF x h_x_in ∧ uFL.ccId = connected_component_of_unionFind_of_id_helper uF x h_x_in := by
  induction x, h_x_in using connected_component_of_unionFind_of_id_helper.induct with
  | case1 x h_x_in h =>
    unfold connected_component_of_unionFind_of_id_helper
    simp [h]
    refine ⟨x, h_x_in, rfl, h⟩
  | case2 x h_x_in h y h_y_in h_r ih =>
    unfold connected_component_of_unionFind_of_id_helper
    simp [h]
    exact ih

theorem exist_unionFindLink_of_connected_component_of_unionFind_of_id {nodeList : List node} (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) : ∃ uFL ∈ uF.linkList, uFL.nodeId = connected_component_of_unionFind_of_id uF id h ∧ uFL.ccId = connected_component_of_unionFind_of_id uF id h := by
  have h' : ∃ x ∈ uF.linkList, x.nodeId = id := by
    rcases h with ⟨x, h_in, h_eq⟩
    have h'' := uF.matching_nodeId x h_in
    rw [h_eq] at h''
    rcases h'' with ⟨y, h_in', h_unique⟩
    refine ⟨y, ?_⟩
    simp [h_in']
  let x := List.choose (fun x => x.nodeId = id) uF.linkList h'
  have h_x_in : x ∈ uF.linkList := List.choose_mem (fun x => x.nodeId = id) uF.linkList h'

  simp [connected_component_of_unionFind_of_id]
  by_cases h_eq_id : x.ccId = x.nodeId
  · refine ⟨x, ?_⟩
    simp [x, h_eq_id, h_x_in]
  · simp [x, h_eq_id]
    simp [exist_unionFindLink_of_connected_component_of_unionFind_of_id_helper]

theorem update_unionFind_matching_nodeId
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLx_in : uFLx ∈ uF.linkList)
  (h_uFLy_in : uFLy ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLx_prop₂ : uFLx.ccId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length)
  (h_idxOf_uFLy : uF.linkList.idxOf uFLy < uF.linkList.length)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)


  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })
  : ∀ x ∈ nodeList, ∃! y ∈ linkList', x.id = y.nodeId := by
  simp [h_linkList'_eq, ExistsUnique]
  intro z h_z_in
  by_cases h_z_eq_x : z.id = x
  · refine ⟨uFLx', ?_⟩
    constructor
    · constructor
      · apply mem_set_of_ne_index
        · apply List.mem_set
          simp [h_idxOf_uFLx]
        · have h_only_one_x : ∀ (j : ℕ) (h₂ : j < List.idxOf uFLx uF.linkList), uF.linkList[j]'(Nat.lt_trans h₂ h_idxOf_uFLx) ≠ uFLx' := by
            intro j h_lt h_getElem_eq
            have h := uF.matching_nodeId z h_z_in
            simp [ExistsUnique] at h
            rcases h with ⟨w, h_w, h_unique⟩
            have h_uFLx'_eq_w := h_unique (uF.linkList[j]'(Nat.lt_trans h_lt h_idxOf_uFLx))
            simp at h_uFLx'_eq_w
            -- have h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank } := by
            --   simp [uFLx']
            simp [h_getElem_eq, h_uFLx'_eq] at h_uFLx'_eq_w
            simp [← h_uFLx'_eq] at h_uFLx'_eq_w
            simp [h_uFLx_prop₁.symm,h_z_eq_x] at h_uFLx'_eq_w
            have h_uFLx_eq_w := h_unique uFLx h_uFLx_in
            simp [h_z_eq_x, h_uFLx_prop₁] at h_uFLx_eq_w
            simp [h_uFLx'_eq_w, ← h_uFLx_eq_w] at h_getElem_eq
            have h := List.Nodup.idxOf_getElem uF.nodup j (Nat.lt_trans h_lt h_idxOf_uFLx)
            simp [h_getElem_eq] at h
            simp [h] at h_lt
          simp [idxOf_set h_idxOf_uFLx h_only_one_x]
          have h_idxOf_inj : List.idxOf uFLx uF.linkList = List.idxOf uFLy uF.linkList ↔ uFLx = uFLy := List.idxOf_inj h_uFLx_in
          apply (Iff.ne h_idxOf_inj).mpr
          intro h_uFL_eq
          simp [h_uFL_eq, h_uFLy_prop₁] at h_uFLx_prop₁
          simp [h_uFLx_prop₁] at h_eq
      · simp [h_uFLx'_eq, h_z_eq_x, h_uFLx_prop₁]
    · intro w h_w_in h_w_eq
      have h_w_in := mem_or_eq_of_mem_set h_w_in
      rcases h_w_in with ⟨h_w_in⟩ | ⟨h_w_eq_uFLy'⟩
      · have h := uF.matching_nodeId z h_z_in
        simp [ExistsUnique] at h
        have h_w_in := mem_eraseIdx_or_eq_of_mem_set h_w_in
        rcases h_w_in with ⟨h_w_in⟩ | ⟨h_w_eq_uFLx'⟩
        · have h_erase : uF.linkList.eraseIdx (List.idxOf uFLx uF.linkList) = uF.linkList.erase uFLx := by
            rw [eq_comm]
            apply List.erase_eq_eraseIdx_of_idxOf
            rfl
          simp [h_erase] at h_w_in
          have h_uFLx_not_mem_erase := not_mem_erase_of_dodup uF.nodup (a := uFLx)
          have h_unique := uF.matching_nodeId z h_z_in
          simp [ExistsUnique] at h_unique
          rcases h_unique with ⟨v, h_v, h_unique⟩
          simp [← h_z_eq_x] at h_uFLx_prop₁
          have h_v_eq_uFLx := h_unique uFLx h_uFLx_in h_uFLx_prop₁.symm
          have h_v_eq_w := h_unique w (List.mem_of_mem_erase h_w_in) h_w_eq
          simp [h_v_eq_w, ← h_v_eq_uFLx] at h_w_in
          simp [h_uFLx_not_mem_erase] at h_w_in
        · exact h_w_eq_uFLx'
      · cases w
        simp [h_z_eq_x] at h_w_eq
        simp [← h_w_eq, h_uFLy'_eq, h_uFLy_prop₁, h_eq] at h_w_eq_uFLy'
  · by_cases h_z_eq_y : z.id = y
    · refine ⟨uFLy', ?_⟩
      constructor
      · constructor
        · have h : (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length = uF.linkList.length := by
            simp
          rw [← h] at h_idxOf_uFLy
          exact List.mem_set h_idxOf_uFLy uFLy'
        · simp [h_uFLy'_eq, h_uFLy_prop₁, h_z_eq_y]
      · intro w h_w_in h_w_eq
        have h_w_in := mem_eraseIdx_or_eq_of_mem_set h_w_in
        rcases h_w_in with ⟨h_w_in⟩ | ⟨h_w_eq_uFLy'⟩
        · have h_erase : (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').eraseIdx (List.idxOf uFLy uF.linkList) = (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').erase uFLy := by
            rw [eq_comm]
            apply List.erase_eq_eraseIdx_of_idxOf
            have h_ne : uFLy ≠ uFLx' := by
              intro h
              simp [h] at h_uFLy_prop₁
              simp [h_uFLx'_eq, h_uFLx_prop₁] at h_uFLy_prop₁
              simp [h_uFLy_prop₁] at h_eq
            have h_idx : List.idxOf uFLy uF.linkList ≠ List.idxOf uFLx uF.linkList := by
              intro h_idx_eq
              have h : uFLy = uFLx := by
                rw [← (List.getElem_idxOf h_idxOf_uFLx)]
                simp [← h_idx_eq]
              simp [h, h_uFLx_prop₁] at h_uFLy_prop₁
              simp [h_uFLy_prop₁] at h_eq
            simp [idxOf_eq_idxOf_set h_ne h_idx]
          simp [h_erase] at h_w_in

          have h_x' := uF.matching_ccId uFLx h_uFLx_in
          simp [ExistsUnique] at h_x'
          rcases h_x' with ⟨x', h_x', h_unique_x'⟩
          have h_unique_u := uF.matching_nodeId x' h_x'.left
          simp [ExistsUnique] at h_unique_u
          rcases h_unique_u with ⟨u, h_u, h_unique_u⟩
          simp [h_x'.right, h_uFLx_prop₂] at h_unique_u

          have h_nodup : (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').Nodup := by
            have h_not_in : uFLx' ∉ uF.linkList := by
              intro h
              have h_uFLx'_nodeId_eq : uFLx'.nodeId = x := by
                simp [h_uFLx'_eq, h_uFLx_prop₁]
              have h_uFLx'_eq_u := h_unique_u uFLx' h h_uFLx'_nodeId_eq.symm
              have h_uFLx_eq_u := h_unique_u uFLx h_uFLx_in h_uFLx_prop₁.symm
              simp [← h_uFLx'_eq_u] at h_uFLx_eq_u
              have h_ccId_eq : uFLx'.ccId = uFLx.ccId := by
                simp [h_uFLx_eq_u]
              simp [h_uFLx'_eq, h_uFLy_prop₂, h_uFLx_prop₂] at h_ccId_eq
              simp [h_ccId_eq] at h_eq
            simp [nodup_set_of_not_mem uF.nodup h_not_in]
          have h_uFLy_not_mem_erase := List.Nodup.not_mem_erase h_nodup (a := uFLy)
          have h_unique := uF.matching_nodeId z h_z_in
          simp [ExistsUnique] at h_unique
          rcases h_unique with ⟨v, h_v, h_unique⟩
          simp [← h_z_eq_y] at h_uFLy_prop₁
          have h_unique : ∀ y ∈ (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx'), z.id = y.nodeId → y = v := by
            intro t h_t_in
            rcases (mem_or_eq_of_mem_set h_t_in) with ⟨h_t_in⟩ | ⟨h_t_eq⟩
            · exact h_unique t h_t_in
            · simp [h_uFLx'_eq, h_uFLx_prop₁] at h_t_eq
              simp [h_t_eq, h_z_eq_x]
          have h_uFLy_in : uFLy ∈ (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') := by
            apply mem_set_of_ne_index
            · exact h_uFLy_in
            · intro h_idx_eq
              have h_uFL_eq : uFLx = uFLy := by
                rw [← List.getElem_idxOf h_idxOf_uFLy]
                simp [h_idx_eq]
              simp [h_uFL_eq, h_uFLy_prop₁] at h_uFLx_prop₁
              simp [h_uFLx_prop₁] at h_z_eq_x
          have h_v_eq_uFLy := h_unique uFLy h_uFLy_in h_uFLy_prop₁.symm
          have h_v_eq_w := h_unique w (List.mem_of_mem_erase h_w_in) h_w_eq
          simp [h_v_eq_w, ← h_v_eq_uFLy] at h_w_in
          simp [h_uFLy_not_mem_erase] at h_w_in
        · exact h_w_eq_uFLy'
    · have h_w := uF.matching_nodeId z h_z_in
      simp [ExistsUnique] at h_w
      rcases h_w with ⟨w, h_w, h_unique⟩
      refine ⟨w, ?_⟩
      have h_idx_w_ne_idx_uFLx : List.idxOf w uF.linkList ≠ List.idxOf uFLx uF.linkList := by
        intro h_idx_eq
        have h_uFL_eq : w = uFLx := by
          rw [← List.getElem_idxOf h_idxOf_uFLx]
          simp [← h_idx_eq]
        simp [← h_uFL_eq, ← h_w.right] at h_uFLx_prop₁
        simp [h_uFLx_prop₁] at h_z_eq_x
      have h_w_in := mem_set_of_ne_index h_w.left h_idx_w_ne_idx_uFLx (b := uFLx')
      have h_uFLy_ne_uFLx' : uFLy ≠ uFLx' := by
        intro h
        simp [h] at h_uFLy_prop₁
        simp [h_uFLx'_eq] at h_uFLy_prop₁
        simp [h_uFLx_prop₁, h_eq] at h_uFLy_prop₁
      have h_w_ne_uFLx' : w ≠ uFLx' := by
        intro h
        simp [h_uFLx'_eq] at h
        simp [h, h_uFLx_prop₁, h_z_eq_x] at h_w
      have h_idx_uFLy_ne_idx_uFLx : List.idxOf uFLy uF.linkList ≠ List.idxOf uFLx uF.linkList := by
        intro h_idx_eq
        have h_uFL_eq : uFLy = uFLx := by
          rw [← List.getElem_idxOf h_idxOf_uFLx]
          simp [← h_idx_eq]
        simp [← h_uFL_eq, h_uFLy_prop₁] at h_uFLx_prop₁
        simp [h_uFLx_prop₁] at h_eq
      have h_idx_w_ne_idx_uFLy : List.idxOf w (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') ≠ List.idxOf uFLy (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') := by
        intro h_idx_eq
        simp [idxOf_eq_idxOf_set h_w_ne_uFLx' h_idx_w_ne_idx_uFLx, idxOf_eq_idxOf_set h_uFLy_ne_uFLx' h_idx_uFLy_ne_idx_uFLx] at h_idx_eq
        have h_uFL_eq : w = uFLy := by
          rw [← List.getElem_idxOf h_idxOf_uFLy]
          simp [← h_idx_eq]
        simp [← h_uFL_eq, ← h_w.right] at h_uFLy_prop₁
        simp [h_uFLy_prop₁] at h_z_eq_y
      have h_w_in := mem_set_of_ne_index h_w_in h_idx_w_ne_idx_uFLy (b := uFLy')
      simp [idxOf_eq_idxOf_set h_uFLy_ne_uFLx' h_idx_uFLy_ne_idx_uFLx] at h_w_in
      simp [h_w_in, h_w.right]
      intro v h_v_in
      have h_v_in := mem_or_eq_of_mem_set h_v_in
      simp [← h_w.right]
      rcases h_v_in with ⟨h_v_in⟩ | ⟨h_v_eq⟩
      · have h_v_in := mem_or_eq_of_mem_set h_v_in
        rcases h_v_in with ⟨h_v_in⟩ | ⟨h_v_eq⟩
        · exact h_unique v h_v_in
        · simp [h_uFLx'_eq, h_uFLx_prop₁] at h_v_eq
          simp [h_v_eq, h_z_eq_x]
      · simp [h_uFLy'_eq, h_uFLy_prop₁] at h_v_eq
        simp [h_v_eq, h_z_eq_y]

theorem update_unionFind_matching_ccId
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)

  (h_uFLy_in : uFLy ∈ uF.linkList)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })
  : ∀ y ∈ linkList', ∃! x ∈ nodeList, x.id = y.ccId := by
  intro z h_z_in
  simp [h_linkList'_eq] at h_z_in
  have h_z_in := mem_or_eq_of_mem_set h_z_in
  rcases h_z_in with ⟨h_z_in⟩ | ⟨h_z_eq⟩
  · have h_z_in := mem_or_eq_of_mem_set h_z_in
    rcases h_z_in with ⟨h_z_in⟩ | ⟨h_z_eq⟩
    · exact uF.matching_ccId z h_z_in
    · simp [h_z_eq, h_uFLx'_eq]
      exact uF.matching_ccId uFLy h_uFLy_in
  · simp [h_z_eq, h_uFLy'_eq]
    exact uF.matching_ccId uFLy h_uFLy_in

theorem update_unionFind_matching_length
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  : nodeList.length = linkList'.length := by
  simp [h_linkList'_eq]
  exact uF.matching_length

theorem update_unionFind_nodup
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLx_in : uFLx ∈ uF.linkList)
  (h_uFLy_in : uFLy ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLx_prop₂ : uFLx.ccId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })
  : linkList'.Nodup := by
  simp [h_linkList'_eq]
  have h_uFLx'_not_in : uFLx' ∉ uF.linkList := by
    have h_x' := uF.matching_ccId uFLx h_uFLx_in
    simp [ExistsUnique] at h_x'
    rcases h_x' with ⟨x', h_x', h_unique_x'⟩
    have h_unique_u := uF.matching_nodeId x' h_x'.left
    simp [ExistsUnique] at h_unique_u
    rcases h_unique_u with ⟨u, h_u, h_unique_u⟩
    simp [h_x'.right, h_uFLx_prop₂] at h_unique_u
    intro h
    have h_uFLx'_nodeId_eq : uFLx'.nodeId = x := by
      simp [h_uFLx'_eq, h_uFLx_prop₁]
    have h_uFLx'_eq_u := h_unique_u uFLx' h h_uFLx'_nodeId_eq.symm
    have h_uFLx_eq_u := h_unique_u uFLx h_uFLx_in h_uFLx_prop₁.symm
    simp [← h_uFLx'_eq_u] at h_uFLx_eq_u
    have h_ccId_eq : uFLx'.ccId = uFLx.ccId := by
      simp [h_uFLx_eq_u]
    simp [h_uFLx'_eq, h_uFLy_prop₂, h_uFLx_prop₂] at h_ccId_eq
    simp [h_ccId_eq] at h_eq
  have h_nodup := nodup_set_of_not_mem uF.nodup h_uFLx'_not_in (i := List.idxOf uFLx uF.linkList)
  by_cases h_uFLy_eq : uFLy = uFLy'
  · have h := set_eq_self (l := (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx')) (a := uFLy')
    have h' : List.idxOf uFLy' (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') = List.idxOf uFLy' uF.linkList := by
      apply idxOf_eq_idxOf_set
      · simp [h_uFLx'_eq, h_uFLy'_eq, h_uFLx_prop₁, h_uFLy_prop₁, ne_comm.mp h_eq]
      · have h'' : uFLx = uF.linkList[List.idxOf uFLx uF.linkList] := by
          simp
        intro h'''
        simp [← h'''] at h''
        simp [h''] at h_uFLx_prop₁
        simp [h_uFLy'_eq, h_uFLy_prop₁, ne_comm.mp h_eq] at h_uFLx_prop₁
    simp [h'] at h
    simp [h_uFLy_eq, h, h_nodup]
  · have h_uFLy'_not_in : uFLy' ∉ uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx' := by
      have h_y' := uF.matching_ccId uFLy h_uFLy_in
      simp [ExistsUnique] at h_y'
      rcases h_y' with ⟨y', h_y', h_unique_y'⟩
      have h_unique_u := uF.matching_nodeId y' h_y'.left
      simp [ExistsUnique] at h_unique_u
      rcases h_unique_u with ⟨u, h_u, h_unique_u⟩
      simp [h_y'.right, h_uFLy_prop₂] at h_unique_u
      intro h
      have h := mem_or_eq_of_mem_set h
      rcases h with ⟨h⟩ | ⟨h⟩
      · have h_uFLy'_nodeId_eq : uFLy'.nodeId = y := by
          simp [h_uFLy'_eq, h_uFLy_prop₁]
        have h_uFLy'_eq_u := h_unique_u uFLy' h h_uFLy'_nodeId_eq.symm
        have h_uFLy_eq_u := h_unique_u uFLy h_uFLy_in h_uFLy_prop₁.symm
        simp [← h_uFLy'_eq_u] at h_uFLy_eq_u
        simp [h_uFLy_eq_u] at h_uFLy_eq
      · simp [h_uFLx'_eq, h_uFLy'_eq, h_uFLx_prop₁, h_uFLy_prop₁] at h
        simp [h] at h_eq
    exact nodup_set_of_not_mem h_nodup h_uFLy'_not_in (i := List.idxOf uFLy uF.linkList)

theorem update_unionFind_matching_rank
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLx_in : uFLx ∈ uF.linkList)
  (h_uFLy_in : uFLy ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLx_prop₂ : uFLx.ccId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length)
  (h_idxOf_uFLy : uF.linkList.idxOf uFLy < uF.linkList.length)
  (h_rank_le : uFLx.rank ≤ uFLy.rank)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)
  (h_uFLx'_in : uFLx' ∈ linkList')
  (h_uFLy'_in : uFLy' ∈ linkList')

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })

  (matching_nodeId' : ∀ x ∈ nodeList, ∃! y, y ∈ linkList' ∧ x.id = y.nodeId)
  (matching_ccId' : ∀ y ∈ linkList', ∃! x ∈ nodeList, x.id = y.ccId)
  (nodup' : linkList'.Nodup)

  (z : unionFindLink nodeList)
  (h_z_in : z ∈ linkList')
  : z.nodeId = z.ccId ∨ z.rank < (List.choose (fun x => x.nodeId = z.ccId) linkList' (exists_parent_link linkList' matching_nodeId' matching_ccId' z h_z_in)).rank := by
  have h_ex' := exists_parent_link linkList' matching_nodeId' matching_ccId' z h_z_in
  simp [h_linkList'_eq] at h_z_in
  have h_z_in := mem_or_eq_of_mem_set h_z_in
  rcases h_z_in with ⟨h_z_in'⟩ | ⟨h_z_eq⟩
  · have h_z_in' := mem_or_eq_of_mem_set h_z_in'
    rcases h_z_in' with ⟨h_z_in''⟩ | ⟨h_z_eq⟩
    · have h_matching_rank := uF.matching_rank z h_z_in''
      by_cases h_z_eq_id : z.nodeId = z.ccId
      · simp [h_z_eq_id]
      · simp [h_z_eq_id]
        simp [h_z_eq_id] at h_matching_rank
        have h_ex := exists_parent_link uF.linkList uF.matching_nodeId uF.matching_ccId z h_z_in''
        have h_ge_rank : (List.choose (fun x => x.nodeId = z.ccId) linkList' h_ex').rank ≥ (List.choose (fun x => x.nodeId = z.ccId) uF.linkList h_ex).rank := by
          by_cases h_z_eq_x : z.ccId = x
          · have h_choose_eq_uFLx' : List.choose (fun x => x.nodeId = z.ccId) linkList' h_ex' = uFLx' := by
              have h_prop := List.choose_property (fun x => x.nodeId = z.ccId) linkList' h_ex'
              have h := uF.matching_ccId z h_z_in''
              simp [ExistsUnique] at h
              rcases h with ⟨x', h_x', h_x'_unique⟩
              have h := matching_nodeId' x' h_x'.left
              simp [ExistsUnique] at h
              rcases h with ⟨w, h_w, h_w_unique⟩
              have h_choose_eq_w := h_w_unique (List.choose (fun x => x.nodeId = z.ccId) linkList' h_ex') (List.choose_mem (fun x => x.nodeId = z.ccId) linkList' h_ex')
              simp [h_prop, h_x'.right] at h_choose_eq_w
              simp [h_choose_eq_w]
              have h_uFLx_eq_w := h_w_unique uFLx' h_uFLx'_in
              simp [h_uFLx'_eq, h_uFLx_prop₁, h_x'.right, h_z_eq_x] at h_uFLx_eq_w
              simp [h_uFLx'_eq, h_uFLx_prop₁, h_uFLx_eq_w]
            have h : List.choose (fun x => x.nodeId = z.ccId) uF.linkList h_ex = uFLx := by
              have h_prop := List.choose_property (fun x => x.nodeId = z.ccId) uF.linkList h_ex
              have h := uF.matching_ccId z h_z_in''
              simp [ExistsUnique] at h
              rcases h with ⟨x', h_x', h_x'_unique⟩
              have h := uF.matching_nodeId x' h_x'.left
              simp [ExistsUnique] at h
              rcases h with ⟨w, h_w, h_w_unique⟩
              have h_choose_eq_w := h_w_unique (List.choose (fun x => x.nodeId = z.ccId) uF.linkList h_ex) (List.choose_mem (fun x => x.nodeId = z.ccId) uF.linkList h_ex)
              simp [h_prop, h_x'.right] at h_choose_eq_w
              simp [h_choose_eq_w]
              have h_uFLx_eq_w := h_w_unique uFLx h_uFLx_in
              simp [h_uFLx_prop₁, h_x'.right, h_z_eq_x] at h_uFLx_eq_w
              exact h_uFLx_eq_w.symm
            simp [h_choose_eq_uFLx', h, h_uFLx'_eq]
          · have h_uFL_ne : uFLx ≠ uFLy := by
              intro h
              simp_all
            by_cases h_z_eq_y : z.ccId = y
            · have h_not_prop_uFLx' : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLx') := by
                simp [h_uFLx'_eq, h_uFLx_prop₁, ne_comm.mp h_z_eq_x]
              have h_not_prop_uFLx : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLx) := by
                simp [h_uFLx_prop₁, ne_comm.mp h_z_eq_x]
              have h_prop_uFLy' : ((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLy') := by
                simp [h_uFLy'_eq, h_uFLy_prop₁, h_z_eq_y]
              have h_prop_uFLy : ((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLy) := by
                simp [h_uFLy_prop₁, h_z_eq_y]
              simp [h_linkList'_eq]
              simp [choose_findIdx]
              have h : List.findIdx (fun b => decide (b.nodeId = z.ccId)) uF.linkList = List.findIdx (fun b => decide (b.nodeId = z.ccId)) ((uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').set (List.idxOf uFLy uF.linkList) uFLy') := by

                have h' : List.idxOf uFLx uF.linkList ≠ List.idxOf uFLy uF.linkList := by
                  intro h_contra
                  have h_contra' : uFLy = uF.linkList[List.idxOf uFLy uF.linkList] := by
                    simp
                  simp [← h_contra] at h_contra'
                  simp [h_contra'] at h_uFL_ne
                simp [List.set_comm uFLx' uFLy' h' (l := uF.linkList)]
                have h_not_prop_getElem_idxOf_uFLx : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) ((uF.linkList.set (List.idxOf uFLy uF.linkList) uFLy')[List.idxOf uFLx uF.linkList]'(by simp [h_idxOf_uFLx]))) := by
                  simp [List.getElem_set_ne (ne_comm.mp h'), h_not_prop_uFLx]
                have h_idxOf_uFLx_set : List.idxOf uFLx uF.linkList < (uF.linkList.set (List.idxOf uFLy uF.linkList) uFLy').length := by
                  simp [h_idxOf_uFLx]
                have h'' := findIdx_set_of_not_prop h_idxOf_uFLx_set h_not_prop_uFLx' h_not_prop_getElem_idxOf_uFLx (p := (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId)) (l := (uF.linkList.set (List.idxOf uFLy uF.linkList) uFLy'))
                simp [h'']
                have h_prop_getElem_idxOf_uFLy : ((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) (uF.linkList[List.idxOf uFLy uF.linkList]'(by simp [h_idxOf_uFLy]))) := by
                  simp [h_prop_uFLy]
                have h''' := findIdx_set_of_prop h_idxOf_uFLy h_prop_uFLy' h_prop_getElem_idxOf_uFLy (p := (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId))
                simp [h''']
              simp [← h]
              by_cases h' : List.findIdx (fun b => decide (b.nodeId = z.ccId)) uF.linkList = List.idxOf uFLy uF.linkList
              · simp [h', h_uFLy'_eq]
                apply Fin.val_fin_le.mp
                simp
              · have h'' : List.findIdx (fun b => decide (b.nodeId = z.ccId)) uF.linkList < ((uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').set (List.idxOf uFLy uF.linkList) uFLy').length := by
                  simp
                  refine ⟨uFLy, h_uFLy_in, by simp [h_z_eq_y, h_uFLy_prop₁]⟩
                simp [getElem_set_of_ne_index h'' (ne_comm.mp h')]
                by_cases h''' : List.findIdx (fun b => decide (b.nodeId = z.ccId)) uF.linkList = List.idxOf uFLx uF.linkList
                · have h_contra : uFLx = uF.linkList[List.idxOf uFLx uF.linkList] := by
                    simp
                  simp [← h'''] at h_contra
                  have h_contra' : (fun b => decide (b.nodeId = z.ccId)) uFLx := by
                    rw [h_contra]
                    have h_prop := prop_getElem_findIdx (p := (fun (b : unionFindLink nodeList) => decide (b.nodeId = z.ccId))) (l := uF.linkList) (hp := ⟨uFLy, h_uFLy_in, by simp [h_z_eq_y, h_uFLy_prop₁]⟩)
                    simp at h_prop
                    simp [h_prop]
                  simp [h_uFLx_prop₁] at h_contra'
                  simp [h_contra'] at h_z_eq_x
                · have h'''' : List.findIdx (fun b => decide (b.nodeId = z.ccId)) uF.linkList < (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length := by
                    simp
                    refine ⟨uFLy, h_uFLy_in, by simp [h_z_eq_y, h_uFLy_prop₁]⟩
                  simp [getElem_set_of_ne_index h'''' (ne_comm.mp h''')]
            · have h_not_prop_uFLx' : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLx') := by
                simp [h_uFLx'_eq, h_uFLx_prop₁, ne_comm.mp h_z_eq_x]
              have h_not_prop_uFLy' : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLy') := by
                simp [h_uFLy'_eq, h_uFLy_prop₁, ne_comm.mp h_z_eq_y]
              simp [choose_erase_of_not_prop (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) h_ex' h_not_prop_uFLy']
              simp [choose_erase_of_not_prop (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) (prop_erase_of_not_prop (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) h_ex' h_not_prop_uFLy') h_not_prop_uFLx']
              simp [h_linkList'_eq]
              simp [h_linkList'_eq] at nodup'
              have h : List.idxOf uFLy uF.linkList < (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length := by
                simp [h_idxOf_uFLy]
              simp [erase_set_eq_eraseIdx nodup' h]
              have h' := List.eraseIdx_idxOf_eq_erase uFLy (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx')
              have h'' : List.idxOf uFLy uF.linkList ≠ List.idxOf uFLx uF.linkList := by
                intro h_contra
                have h_contra' : uFLy = uF.linkList[List.idxOf uFLy uF.linkList] := by
                  simp
                simp [h_contra] at h_contra'
                simp [h_contra'] at h_uFL_ne
              have h''' : uFLy ≠ uFLx' := by
                intro h_contra
                simp [h_contra] at h_uFLy_prop₁
                simp [h_uFLx'_eq, h_uFLx_prop₁, h_eq] at h_uFLy_prop₁
              simp [- List.eraseIdx_idxOf_eq_erase, idxOf_eq_idxOf_set h''' h''] at h'
              simp [h']
              simp [List.erase_comm uFLy]
              have h_uFLx'_not_in : uFLx' ∉ uF.linkList := by
                have h_x' := uF.matching_ccId uFLx h_uFLx_in
                simp [ExistsUnique] at h_x'
                rcases h_x' with ⟨x', h_x', h_unique_x'⟩
                have h_unique_u := uF.matching_nodeId x' h_x'.left
                simp [ExistsUnique] at h_unique_u
                rcases h_unique_u with ⟨u, h_u, h_unique_u⟩
                simp [h_x'.right, h_uFLx_prop₂] at h_unique_u
                intro h
                have h_uFLx'_nodeId_eq : uFLx'.nodeId = x := by
                  simp [h_uFLx'_eq, h_uFLx_prop₁]
                have h_uFLx'_eq_u := h_unique_u uFLx' h h_uFLx'_nodeId_eq.symm
                have h_uFLx_eq_u := h_unique_u uFLx h_uFLx_in h_uFLx_prop₁.symm
                simp [← h_uFLx'_eq_u] at h_uFLx_eq_u
                have h_ccId_eq : uFLx'.ccId = uFLx.ccId := by
                  simp [h_uFLx_eq_u]
                simp [h_uFLx'_eq, h_uFLy_prop₂, h_uFLx_prop₂] at h_ccId_eq
                simp [h_ccId_eq] at h_eq
              have h_nodup : (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').Nodup := nodup_set_of_not_mem uF.nodup h_uFLx'_not_in (i := List.idxOf uFLx uF.linkList)
              simp [erase_set_eq_eraseIdx h_nodup h_idxOf_uFLx]
              have h_not_prop_uFLx : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLx) := by
                simp [h_uFLx_prop₁, ne_comm.mp h_z_eq_x]
              have h_not_prop_uFLy : ¬((fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) uFLy) := by
                simp [h_uFLy_prop₁, ne_comm.mp h_z_eq_y]
              simp [choose_erase_of_not_prop (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) h_ex h_not_prop_uFLy]
              simp [choose_erase_of_not_prop (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) (prop_erase_of_not_prop (fun (w : unionFindLink nodeList) => w.nodeId = z.ccId) h_ex h_not_prop_uFLy) h_not_prop_uFLx]
              simp [List.erase_comm uFLy]
        apply lt_of_lt_of_le h_matching_rank h_ge_rank
    · right
      have h_choose_eq_uFLy' : List.choose (fun x => x.nodeId = z.ccId) linkList' h_ex' = uFLy' := by
        simp [h_uFLx'_eq, h_uFLy_prop₂, ← h_uFLy_prop₁] at h_z_eq
        have h_prop := List.choose_property (fun x => x.nodeId = z.ccId) linkList' h_ex'
        have h_z_in : z ∈ linkList' := by
          simp [h_linkList'_eq, h_z_in]
        have h := matching_ccId' z h_z_in
        simp [ExistsUnique] at h
        rcases h with ⟨x', h_x', h_x'_unique⟩
        have h := matching_nodeId' x' h_x'.left
        simp [ExistsUnique] at h
        rcases h with ⟨w, h_w, h_w_unique⟩
        have h_choose_eq_w := h_w_unique (List.choose (fun x => x.nodeId = z.ccId) linkList' h_ex') (List.choose_mem (fun x => x.nodeId = z.ccId) linkList' h_ex')
        simp [h_prop, h_x'.right] at h_choose_eq_w
        simp [h_choose_eq_w]
        have h_uFLy_eq_w := h_w_unique uFLy' h_uFLy'_in
        rw [eq_comm]
        apply h_uFLy_eq_w
        simp [h_uFLy'_eq, h_uFLy_prop₁, h_x'.right, h_z_eq]
      simp [h_z_eq, h_uFLx'_eq]
      simp [h_z_eq, h_uFLx'_eq] at h_choose_eq_uFLy'
      simp [h_choose_eq_uFLy', h_uFLy'_eq]
      by_cases h_rank_eq : uFLx.rank = uFLy.rank
      · simp [h_rank_eq]
        apply Fin.val_fin_lt.mp
        simp
      · have h_rank_lt : uFLx.rank < uFLy.rank := lt_of_le_of_ne h_rank_le h_rank_eq
        simp [h_rank_lt]
  · left
    simp [h_z_eq, h_uFLy'_eq, h_uFLy_prop₁, h_uFLy_prop₂]

theorem update_unionFind_rank_succ_isLt -- unused
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLy_in : uFLy ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_rank_lt : uFLx.rank < uFLy.rank)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })
  : (a : unionFindLink nodeList) → (b : unionFindLink nodeList) → a ≠ b → a ∈ linkList' → b ∈ linkList' → a.nodeId = a.ccId → b.nodeId = b.ccId → a.rank = b.rank → a.rank.val.succ < nodeList.length := by
  simp [h_rank_lt] at h_uFLy'_eq
  have h_uFLy'_eq : uFLy' = uFLy := by
    simp [h_uFLy'_eq]
  simp [h_linkList'_eq]
  intro uFL1 uFL2 h_1_ne_2 h_1_in h_2_in h_1_selfcon h_2_selfcon h_eq_rank
  have h_1_in := mem_or_eq_of_mem_set h_1_in
  rcases h_1_in with ⟨h_1_in⟩ | ⟨h_1_eq⟩
  · have h_1_in := mem_or_eq_of_mem_set h_1_in
    rcases h_1_in with ⟨h_1_in⟩ | ⟨h_1_eq⟩
    · have h_2_in := mem_or_eq_of_mem_set h_2_in
      rcases h_2_in with ⟨h_2_in⟩ | ⟨h_2_eq⟩
      · have h_2_in := mem_or_eq_of_mem_set h_2_in
        rcases h_2_in with ⟨h_2_in⟩ | ⟨h_2_eq⟩
        · exact uF.rank_succ_isLt uFL1 uFL2 h_1_ne_2 h_1_in h_2_in h_1_selfcon h_2_selfcon h_eq_rank
        · simp [h_2_eq, h_uFLx'_eq, h_uFLx_prop₁, h_uFLy_prop₂, h_eq] at h_2_selfcon
      · simp [h_eq_rank, h_2_eq, h_uFLy'_eq]
        apply uF.rank_succ_isLt uFLy uFL1 ?_ h_uFLy_in h_1_in ?_ h_1_selfcon ?_
        · have h_2_eq_uFLy : uFL2 = uFLy := by
            simp [h_2_eq, h_uFLy'_eq]
          simp [← h_2_eq_uFLy, ne_comm.mp h_1_ne_2]
        · simp [h_uFLy_prop₁, h_uFLy_prop₂]
        · simp [h_eq_rank, h_2_eq, h_uFLy'_eq]
    · simp [h_1_eq, h_uFLx'_eq, h_uFLx_prop₁, h_uFLy_prop₂, h_eq] at h_1_selfcon
  · have h_2_in := mem_or_eq_of_mem_set h_2_in
    rcases h_2_in with ⟨h_2_in⟩ | ⟨h_2_eq⟩
    · have h_2_in := mem_or_eq_of_mem_set h_2_in
      rcases h_2_in with ⟨h_2_in⟩ | ⟨h_2_eq⟩
      · simp [h_uFLy'_eq] at h_1_eq
        simp [← h_1_eq] at h_uFLy_in
        exact uF.rank_succ_isLt uFL1 uFL2 h_1_ne_2 h_uFLy_in h_2_in h_1_selfcon h_2_selfcon h_eq_rank
      · simp [h_2_eq, h_uFLx'_eq, h_uFLx_prop₁, h_uFLy_prop₂, h_eq] at h_2_selfcon
    · simp [h_eq_rank, h_2_eq, h_uFLy'_eq]
      apply uF.rank_succ_isLt uFLy uFL1 ?_ h_uFLy_in ?_ ?_ h_1_selfcon ?_
      · have h_2_eq_uFLy : uFL2 = uFLy := by
          simp [h_2_eq, h_uFLy'_eq]
        simp [← h_2_eq_uFLy, ne_comm.mp h_1_ne_2]
      · simp [h_uFLy'_eq] at h_1_eq
        simp [h_1_eq, h_uFLy_in]
      · simp [h_uFLy_prop₁, h_uFLy_prop₂]
      · simp [h_eq_rank, h_2_eq, h_uFLy'_eq]

theorem update_unionFind_rankInvariant
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLx_in : uFLx ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLx_prop₂ : uFLx.ccId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length)
  (h_idxOf_uFLy : uF.linkList.idxOf uFLy < uF.linkList.length)
  (h_rank_lt : uFLx.rank < uFLy.rank)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })

  (nodup' : linkList'.Nodup)
  : (z : unionFindLink nodeList) → z ∈ linkList' → (linkList'.filter (fun y => y.rank < z.rank ∧ ¬y.nodeId = y.ccId)).length ≥ z.rank := by
  simp [h_rank_lt] at h_uFLy'_eq
  have h_uFLy'_eq : uFLy' = uFLy := by
    simp [h_uFLy'_eq]
  have h : List.idxOf uFLy uF.linkList = List.idxOf uFLy (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') := by
    have h_uFL_ne : uFLx ≠ uFLy := by
      intro h
      simp_all
    have h' : List.idxOf uFLx uF.linkList ≠ List.idxOf uFLy uF.linkList := by
      intro h_contra
      have h_contra' : uFLy = uF.linkList[List.idxOf uFLy uF.linkList]'h_idxOf_uFLy := by
        simp
      simp [← h_contra] at h_contra'
      simp [h_contra'] at h_uFL_ne
    have h_uFL_ne : uFLx' ≠ uFLy := by
      intro h
      simp_all
    simp [idxOf_eq_idxOf_set h_uFL_ne.symm h'.symm]
  simp [h_uFLy'_eq, h] at h_linkList'_eq
  simp [set_eq_self] at h_linkList'_eq
  simp [h_linkList'_eq]
  simp [h_linkList'_eq] at nodup'
  intro z h_z_in'
  have h_x_rank_eq : uFLx'.rank = uFLx.rank := by
    simp [h_uFLx'_eq]
  by_cases h_z_eq_uFlx' : z = uFLx'
  · simp [h_z_eq_uFlx', h_x_rank_eq]
    have h_rankInvariant := uF.rankInvariant uFLx h_uFLx_in
    apply le_of_le_of_eq h_rankInvariant
    simp
    set p : unionFindLink nodeList → Prop := (fun (w : unionFindLink nodeList) => decide (w.rank < uFLx.rank) && !decide (w.nodeId = w.ccId))
    have h_not_p_uFLx : ¬p uFLx := by
      simp [p]
    have h_not_p_uFLx' : ¬p uFLx' := by
      simp [p, h_x_rank_eq]
    have h_erase_uFLx := filter_erase_eq_self_of_not_prop h_not_p_uFLx (p := p) (l := uF.linkList)
    have h_erase_uFLx' := filter_erase_eq_self_of_not_prop h_not_p_uFLx' (p := p) (l := (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx'))
    simp [p] at h_erase_uFLx
    simp [h_erase_uFLx]
    simp [erase_set_eq_eraseIdx nodup' h_idxOf_uFLx, p] at h_erase_uFLx'
    simp [h_erase_uFLx']
  · have h_z_in : z ∈ uF.linkList := by
      have h' := List.mem_or_eq_of_mem_set h_z_in'
      simp [h_z_eq_uFlx'] at h'
      exact h'
    have h_rankInvariant := uF.rankInvariant z h_z_in
    apply le_trans h_rankInvariant
    simp
    set p : unionFindLink nodeList → Prop := (fun (w : unionFindLink nodeList) => decide (w.rank < z.rank) && !decide (w.nodeId = w.ccId))
    have h_not_p_uFLx : ¬p uFLx := by
      simp [p, h_uFLx_prop₁, h_uFLx_prop₂]
    have h_erase_uFLx := filter_erase_eq_self_of_not_prop h_not_p_uFLx (p := p) (l := uF.linkList)
    simp [p] at h_erase_uFLx
    rw [h_erase_uFLx]
    have h_length_filter_erase_le : (List.filter p ((uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').erase uFLx')).length ≤ (List.filter p (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx')).length := by
      exact length_filter_erase_le_length_filter
    simp [p] at h_length_filter_erase_le
    apply le_trans ?_ h_length_filter_erase_le
    simp [erase_set_eq_eraseIdx nodup' h_idxOf_uFLx]

theorem update_unionFind_rankInvariant_of_rank_eq
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLx_in : uFLx ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLx_prop₂ : uFLx.ccId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length)
  (h_idxOf_uFLy : uF.linkList.idxOf uFLy < uF.linkList.length)
  (h_rank_eq : uFLx.rank = uFLy.rank)
  (h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length)
  (h_uFLx'_in : uFLx' ∈ linkList')

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  (h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ })

  (nodup' : linkList'.Nodup)
  : (z : unionFindLink nodeList) → z ∈ linkList' → (linkList'.filter (fun y => y.rank < z.rank ∧ ¬y.nodeId = y.ccId)).length ≥ z.rank := by
  simp [h_rank_eq] at h_uFLy'_eq
  have h_idxOf_uFLy_eq : List.idxOf uFLy uF.linkList = List.idxOf uFLy (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') := by
    have h_uFL_ne : uFLx ≠ uFLy := by
      intro h
      simp_all
    have h' : List.idxOf uFLx uF.linkList ≠ List.idxOf uFLy uF.linkList := by
      intro h_contra
      have h_contra' : uFLy = uF.linkList[List.idxOf uFLy uF.linkList]'h_idxOf_uFLy := by
        simp
      simp [← h_contra] at h_contra'
      simp [h_contra'] at h_uFL_ne
    have h_uFL_ne : uFLx' ≠ uFLy := by
      intro h
      simp [← h] at h_uFLy_prop₁
      simp [h_uFLx'_eq, h_uFLx_prop₁, h_eq] at h_uFLy_prop₁
    simp [idxOf_eq_idxOf_set h_uFL_ne.symm h'.symm]
  simp [h_idxOf_uFLy_eq] at h_linkList'_eq
  intro z h_z_in
  have h_nodup : (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').Nodup := by
    have h_uFLx'_not_in : uFLx' ∉ uF.linkList := by
      have h_x' := uF.matching_ccId uFLx h_uFLx_in
      simp [ExistsUnique] at h_x'
      rcases h_x' with ⟨x', h_x', h_unique_x'⟩
      have h_unique_u := uF.matching_nodeId x' h_x'.left
      simp [ExistsUnique] at h_unique_u
      rcases h_unique_u with ⟨u, h_u, h_unique_u⟩
      simp [h_x'.right, h_uFLx_prop₂] at h_unique_u
      intro h
      have h_uFLx'_nodeId_eq : uFLx'.nodeId = x := by
        simp [h_uFLx'_eq, h_uFLx_prop₁]
      have h_uFLx'_eq_u := h_unique_u uFLx' h h_uFLx'_nodeId_eq.symm
      have h_uFLx_eq_u := h_unique_u uFLx h_uFLx_in h_uFLx_prop₁.symm
      simp [← h_uFLx'_eq_u] at h_uFLx_eq_u
      have h_ccId_eq : uFLx'.ccId = uFLx.ccId := by
        simp [h_uFLx_eq_u]
      simp [h_uFLx'_eq, h_uFLy_prop₂, h_uFLx_prop₂] at h_ccId_eq
      simp [h_ccId_eq] at h_eq
    exact nodup_set_of_not_mem uF.nodup h_uFLx'_not_in
  by_cases h_z_eq_uFLy' : z = uFLy'
  · simp [h_z_eq_uFLy', h_uFLy'_eq, ← h_rank_eq]
    set p : unionFindLink nodeList → Prop := (fun (y : unionFindLink nodeList) => decide (y.rank < ⟨↑uFLx.rank + 1, h_rank_succ_isLt⟩) && !decide (y.nodeId = y.ccId))
    set p' : unionFindLink nodeList → Prop := (fun (y : unionFindLink nodeList) => decide (y.rank < uFLx.rank) && !decide (y.nodeId = y.ccId))
    have h_not_p'_uFLx' : ¬p' uFLx' := by
      simp [p', h_uFLx'_eq]
    have h_p_uFLx' : p uFLx' := by
      simp [p, h_uFLx'_eq]
      simp [h_uFLx_prop₁, h_uFLy_prop₂, h_eq]
      apply Fin.val_fin_lt.mp
      exact (Nat.lt_succ_self uFLx.rank.val)
    have h_uFLx'_in_filter : uFLx' ∈ List.filter p linkList' := by
      simp [h_uFLx'_in, h_p_uFLx']
    apply lt_of_le_of_lt (uF.rankInvariant uFLx h_uFLx_in)
    apply length_lt_of_subset
    · have h := List.Nodup.filter p' uF.nodup
      simp [p'] at h
      simp [h]
    · have h := List.Nodup.filter p nodup'
      simp [p] at h
      simp [h]
    · simp
      intro w h_w_in h_w_rank_lt h_w_not_selfcon
      refine ⟨?_, ?_, h_w_not_selfcon⟩
      · simp [h_linkList'_eq]
        have h_w_ne_idx : List.idxOf w uF.linkList ≠ List.idxOf uFLx uF.linkList := by
          intro h_w_eq_idx
          rw [h_w_eq_idx.symm] at h_idxOf_uFLx
          rw [← List.getElem_idxOf h_idxOf_uFLx] at h_w_rank_lt
          simp [h_w_eq_idx] at h_w_rank_lt
        have h_w_in' : w ∈ (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') := mem_set_of_ne_index h_w_in h_w_ne_idx
        apply mem_set_of_ne_index h_w_in' ?_
        intro h_w_eq_idx
        have h := List.idxOf_lt_length_of_mem h_w_in'
        rw [← List.getElem_idxOf h] at h_w_not_selfcon
        simp [h_w_eq_idx, h_uFLy_prop₁, h_uFLy_prop₂] at h_w_not_selfcon
      · apply lt_trans h_w_rank_lt
        apply Fin.val_fin_lt.mp
        simp
    · refine ⟨uFLx', ?_, ?_⟩
      · simp [p] at h_p_uFLx'
        simp [h_uFLx'_in, h_p_uFLx']
      · simp [p'] at h_not_p'_uFLx'
        simp
        intro h
        exact h_not_p'_uFLx'
  · by_cases h_z_eq_uFLx' : z = uFLx'
    · simp [h_z_eq_uFLx', h_uFLx'_eq]
      set p : unionFindLink nodeList → Prop := (fun y => decide (y.rank < uFLx.rank) && !decide (y.nodeId = y.ccId))
      have h_rankInvariant := uF.rankInvariant uFLx h_uFLx_in
      apply le_of_le_of_eq h_rankInvariant
      have h_not_p_uFLx : ¬p uFLx := by
        simp [p, h_uFLx_prop₁, h_uFLx_prop₂]
      have h_not_p_uFLy : ¬p uFLy := by
        simp [p, h_uFLy_prop₁, h_uFLy_prop₂]
      have h_not_p_uFLy' : ¬p uFLy' := by
        simp [p, h_uFLy'_eq, h_uFLy_prop₁, h_uFLy_prop₂]
      have h_not_p_uFLx' : ¬p uFLx' := by
        simp [p, h_uFLx'_eq]
      have h_filter_eq : List.filter p uF.linkList = List.filter p ((uF.linkList.erase uFLx).erase uFLy) := by
        have h_erase_uFLx := filter_erase_eq_self_of_not_prop h_not_p_uFLx (p := p) (l := uF.linkList)
        have h_erase_uFLy := filter_erase_eq_self_of_not_prop h_not_p_uFLy (p := p) (l := uF.linkList.erase uFLx)
        simp [h_erase_uFLx, h_erase_uFLy]
      have h_filter_eq' : List.filter p linkList' = List.filter p ((linkList'.erase uFLy').erase uFLx') := by
        have h_erase_uFLy' := filter_erase_eq_self_of_not_prop h_not_p_uFLy' (p := p) (l := linkList')
        have h_erase_uFLx' := filter_erase_eq_self_of_not_prop h_not_p_uFLx' (p := p) (l := linkList'.erase uFLy')
        simp [h_erase_uFLy', h_erase_uFLx']
      simp [p] at h_filter_eq h_filter_eq'
      simp [h_filter_eq, h_filter_eq']
      have h : List.idxOf uFLy (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') < (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length := by
        simp [← h_idxOf_uFLy_eq, h_idxOf_uFLy]
      simp [h_linkList'_eq] at nodup'
      simp [h_linkList'_eq, erase_set_eq_eraseIdx nodup' h]
      nth_rewrite 2 [List.erase_comm]
      simp [erase_set_eq_eraseIdx h_nodup h_idxOf_uFLx]
    · simp [h_linkList'_eq] at h_z_in
      have h_z_in := List.mem_or_eq_of_mem_set h_z_in
      simp [h_z_eq_uFLy'] at h_z_in
      have h_z_in := List.mem_or_eq_of_mem_set h_z_in
      simp [h_z_eq_uFLx'] at h_z_in
      have h_rankInvariant := uF.rankInvariant z h_z_in
      simp
      simp at h_rankInvariant
      set p : unionFindLink nodeList → Prop := (fun (y : unionFindLink nodeList) => decide (y.rank < z.rank) && !decide (y.nodeId = y.ccId))
      have h_not_p_uFLx : ¬p uFLx := by
        simp [p, h_uFLx_prop₁, h_uFLx_prop₂]
      have h_not_p_uFLy : ¬p uFLy := by
        simp [p, h_uFLy_prop₁, h_uFLy_prop₂]
      have h_filter_eq : List.filter p uF.linkList = List.filter p ((uF.linkList.erase uFLx).erase uFLy) := by
        have h_erase_uFLx := filter_erase_eq_self_of_not_prop h_not_p_uFLx (p := p) (l := uF.linkList)
        have h_erase_uFLy := filter_erase_eq_self_of_not_prop h_not_p_uFLy (p := p) (l := uF.linkList.erase uFLx)
        simp [h_erase_uFLx, h_erase_uFLy]
      simp [p] at h_filter_eq
      apply le_trans h_rankInvariant
      simp [h_filter_eq]
      have h_fliter_le : (List.filter p ((linkList'.erase uFLy').erase uFLx')).length ≤ (List.filter p linkList').length := by
        have h_fliter_le : (List.filter p ((linkList'.erase uFLy').erase uFLx')).length ≤ (List.filter p (linkList'.erase uFLy')).length := by
          simp [length_filter_erase_le_length_filter]
        apply le_trans h_fliter_le
        simp [length_filter_erase_le_length_filter]
      simp [p] at h_fliter_le
      apply le_trans ?_ h_fliter_le
      have h : List.idxOf uFLy (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') < (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length := by
        simp [← h_idxOf_uFLy_eq, h_idxOf_uFLy]
      simp [h_linkList'_eq] at nodup'
      simp [h_linkList'_eq, erase_set_eq_eraseIdx nodup' h]
      nth_rewrite 2 [List.erase_comm]
      simp [erase_set_eq_eraseIdx h_nodup h_idxOf_uFLx]

theorem update_unionFind_h_uFLx'_in
  (nodeList : List node)
  (linkList' : List (unionFindLink nodeList))
  (uF : unionFind nodeList)
  (uFLx uFLy uFLx' uFLy' : unionFindLink nodeList)
  (x y : Nat)
  (h_eq : ¬x = y)

  (h_uFLx_in : uFLx ∈ uF.linkList)
  (h_uFLx_prop₁ : uFLx.nodeId = x)
  (h_uFLx_prop₂ : uFLx.ccId = x)
  (h_uFLy_prop₁ : uFLy.nodeId = y)
  (h_uFLy_prop₂ : uFLy.ccId = y)
  (h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length)

  (h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy')
  (h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank })
  : uFLx' ∈ linkList' := by
  simp [h_linkList'_eq]
  apply mem_set_of_ne_index
  · apply List.mem_set
    exact h_idxOf_uFLx
  · have h : List.idxOf uFLx' (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') = List.idxOf uFLx uF.linkList := by
      apply idxOf_set
      · intro j h_j h_getElem_eq
        have h_uFLx'_in := List.mem_of_getElem h_getElem_eq
        have h := uF.matching_ccId uFLx h_uFLx_in
        simp [ExistsUnique] at h
        rcases h with ⟨x', h_x', _⟩
        rw [h_uFLx_prop₂, ← h_uFLx_prop₁] at h_x'
        have h := uF.matching_nodeId x' h_x'.left
        simp [ExistsUnique] at h
        rcases h with ⟨z, h_z, h_unique⟩
        rw [h_x'.right] at h_unique
        have h_uFLx_eq_z : uFLx = z := by
          apply h_unique
          · exact h_uFLx_in
          · rfl
        have h_uFLx'_eq_z : uFLx' = z := by
          apply h_unique
          · exact h_uFLx'_in
          · simp [h_uFLx'_eq]
        simp [← h_uFLx'_eq_z] at h_uFLx_eq_z
        simp [h_uFLx_eq_z] at h_uFLx_prop₂
        simp [h_uFLx'_eq, h_uFLy_prop₂] at h_uFLx_prop₂
        simp [h_uFLx_prop₂] at h_eq
      · exact h_idxOf_uFLx
    simp [h]
    intro h
    have h_contra : uFLx = uF.linkList[List.idxOf uFLx uF.linkList] := by
      simp
    simp [h] at h_contra
    simp [h_contra, h_uFLy_prop₁] at h_uFLx_prop₁
    simp [h_uFLx_prop₁] at h_eq

-- könnte auch union heißen
def update_unionFind {nodeList : List node} (uF : unionFind nodeList) (x y : Nat) (h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x ∧ a.ccId = x) a) (h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y ∧ a.ccId = y) a) : unionFind nodeList :=
  if h_eq : x = y
  then
    uF
  else
    let uFLx : unionFindLink nodeList := List.choose (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList h₁
    let uFLy : unionFindLink nodeList := List.choose (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList h₂
    have h_uFLx_in : uFLx ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList h₁
    have h_uFLy_in : uFLy ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList h₂
    have h_uFLx_prop : uFLx.nodeId = x ∧ uFLx.ccId = x := List.choose_property (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList h₁
    have h_uFLx_prop₁ := h_uFLx_prop.left
    have h_uFLx_prop₂ := h_uFLx_prop.right
    have h_uFLy_prop : uFLy.nodeId = y ∧ uFLy.ccId = y:= List.choose_property (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList h₂
    have h_uFLy_prop₁ := h_uFLy_prop.left
    have h_uFLy_prop₂ := h_uFLy_prop.right
    have h₃ := h₁
    have h₄ := h₂
    have h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x) a := by
      refine ⟨uFLx, h_uFLx_in, h_uFLx_prop₁⟩
    have h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y) a := by
      refine ⟨uFLy, h_uFLy_in, h_uFLy_prop₁⟩
    have h_idxOf_uFLx : uF.linkList.idxOf uFLx < uF.linkList.length := by
      simp [List.idxOf, h_uFLx_in]
      -- refine ⟨uFLx, h_uFLx_in, by simp⟩
    have h_idxOf_uFLy : uF.linkList.idxOf uFLy < uF.linkList.length := by
      simp [List.idxOf, h_uFLy_in]
      -- refine ⟨uFLy, h_uFLy_in, by simp⟩
    if h_rank_lt : uFLx.rank < uFLy.rank
      then




        have h_rank_succ_le : uFLx.rank.val.succ ≤ uFLy.rank.val := by
          simp [h_rank_lt]
        have h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length := by
          simp [Nat.lt_of_le_of_lt h_rank_succ_le]
        let uFLx' : unionFindLink nodeList := ⟨uFLx.nodeId, uFLy.ccId, uFLx.rank⟩
        let uFLy' : unionFindLink nodeList := ⟨uFLy.nodeId, uFLy.ccId, ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩⟩
        let linkList' : List (unionFindLink nodeList) := (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy'
        have h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy' := by
          simp [linkList']
        have h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank } := by
          simp [uFLx']
        have h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ } := by
          simp [uFLy']
        have h_uFLx'_in : uFLx' ∈ linkList' := update_unionFind_h_uFLx'_in nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_linkList'_eq h_uFLx'_eq
        have h_uFLy'_in : uFLy' ∈ linkList' := by
          simp [h_linkList'_eq]
          have h : List.idxOf uFLy uF.linkList < (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length := by
            simp [h_idxOf_uFLy]
          simp [List.mem_set h]

        have matching_nodeId' : ∀ x ∈ nodeList, ∃! y ∈ linkList', x.id = y.nodeId := update_unionFind_matching_nodeId nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLy_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_idxOf_uFLy h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq

        have matching_ccId' : ∀ y ∈ linkList', ∃! x ∈ nodeList, x.id = y.ccId := update_unionFind_matching_ccId nodeList linkList' uF uFLx uFLy uFLx' uFLy' h_uFLy_in h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq

        have matching_length' : nodeList.length = linkList'.length := update_unionFind_matching_length nodeList linkList' uF uFLx uFLy uFLx' uFLy' h_linkList'_eq

        have nodup' : linkList'.Nodup := update_unionFind_nodup nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLy_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq

        have matching_rank' : (z : unionFindLink nodeList) → (h_z_in : z ∈ linkList') → z.nodeId = z.ccId ∨ z.rank < (List.choose (fun x => x.nodeId = z.ccId) linkList' (exists_parent_link linkList' matching_nodeId' matching_ccId' z h_z_in)).rank := update_unionFind_matching_rank nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLy_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_idxOf_uFLy (Fin.le_of_lt h_rank_lt) h_rank_succ_isLt h_uFLx'_in h_uFLy'_in h_linkList'_eq h_uFLx'_eq h_uFLy'_eq matching_nodeId' matching_ccId' nodup'

        have rankInvariant' : (z : unionFindLink nodeList) → z ∈ linkList' → (linkList'.filter (fun y => y.rank < z.rank ∧ ¬y.nodeId = y.ccId)).length ≥ z.rank := update_unionFind_rankInvariant nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_idxOf_uFLy h_rank_lt h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq nodup'

        ⟨linkList', matching_nodeId', matching_ccId', matching_length', matching_rank', nodup', rankInvariant'⟩





      else
        if h_rank_lt' : uFLy.rank < uFLx.rank
          then


            have h_rank_succ_le : uFLy.rank.val.succ ≤ uFLx.rank.val := by
              simp [h_rank_lt']
            have h_rank_succ_isLt : uFLy.rank.val.succ < nodeList.length := by
              simp [Nat.lt_of_le_of_lt h_rank_succ_le]
            let uFLy' : unionFindLink nodeList := ⟨uFLy.nodeId, uFLx.ccId, uFLy.rank⟩
            let uFLx' : unionFindLink nodeList := ⟨uFLx.nodeId, uFLx.ccId, ⟨max uFLx.rank.val uFLy.rank.val.succ, by simp [h_rank_succ_isLt]⟩⟩
            let linkList' : List (unionFindLink nodeList) := (uF.linkList.set (uF.linkList.idxOf uFLy) uFLy').set (uF.linkList.idxOf uFLx) uFLx'
            have h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLy) uFLy').set (uF.linkList.idxOf uFLx) uFLx' := by
              simp [linkList']
            have h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLx.ccId, rank := uFLy.rank } := by
              simp [uFLy']
            have h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLx.ccId, rank := ⟨max uFLx.rank.val uFLy.rank.val.succ, by simp [h_rank_succ_isLt]⟩ } := by
              simp [uFLx']
            have h_uFLy'_in : uFLy' ∈ linkList' := update_unionFind_h_uFLx'_in nodeList linkList' uF uFLy uFLx uFLy' uFLx' y x (ne_comm.mp h_eq) h_uFLy_in h_uFLy_prop₁ h_uFLy_prop₂ h_uFLx_prop₁ h_uFLx_prop₂ h_idxOf_uFLy h_linkList'_eq h_uFLy'_eq
            have h_uFLx'_in : uFLx' ∈ linkList' := by
              simp [h_linkList'_eq]
              have h : List.idxOf uFLx uF.linkList < (uF.linkList.set (List.idxOf uFLy uF.linkList) uFLy').length := by
                simp [h_idxOf_uFLx]
              simp [List.mem_set h]

            have matching_nodeId' : ∀ x ∈ nodeList, ∃! y ∈ linkList', x.id = y.nodeId := update_unionFind_matching_nodeId nodeList linkList' uF uFLy uFLx uFLy' uFLx' y x (ne_comm.mp h_eq) h_uFLy_in h_uFLx_in h_uFLy_prop₁ h_uFLy_prop₂ h_uFLx_prop₁ h_uFLx_prop₂ h_idxOf_uFLy h_idxOf_uFLx h_rank_succ_isLt h_linkList'_eq h_uFLy'_eq h_uFLx'_eq

            have matching_ccId' : ∀ y ∈ linkList', ∃! x ∈ nodeList, x.id = y.ccId := update_unionFind_matching_ccId nodeList linkList' uF uFLy uFLx uFLy' uFLx' h_uFLx_in h_rank_succ_isLt h_linkList'_eq h_uFLy'_eq h_uFLx'_eq

            have matching_length' : nodeList.length = linkList'.length := update_unionFind_matching_length nodeList linkList' uF uFLy uFLx uFLy' uFLx' h_linkList'_eq

            have nodup' : linkList'.Nodup := update_unionFind_nodup nodeList linkList' uF uFLy uFLx uFLy' uFLx' y x (ne_comm.mp h_eq) h_uFLy_in h_uFLx_in h_uFLy_prop₁ h_uFLy_prop₂ h_uFLx_prop₁ h_uFLx_prop₂ h_idxOf_uFLy h_rank_succ_isLt h_linkList'_eq h_uFLy'_eq h_uFLx'_eq

            have matching_rank' : (z : unionFindLink nodeList) → (h_z_in : z ∈ linkList') → z.nodeId = z.ccId ∨ z.rank < (List.choose (fun x => x.nodeId = z.ccId) linkList' (exists_parent_link linkList' matching_nodeId' matching_ccId' z h_z_in)).rank := update_unionFind_matching_rank nodeList linkList' uF uFLy uFLx uFLy' uFLx' y x (ne_comm.mp h_eq) h_uFLy_in h_uFLx_in h_uFLy_prop₁ h_uFLy_prop₂ h_uFLx_prop₁ h_uFLx_prop₂ h_idxOf_uFLy h_idxOf_uFLx (Fin.le_of_lt h_rank_lt') h_rank_succ_isLt h_uFLy'_in h_uFLx'_in h_linkList'_eq h_uFLy'_eq h_uFLx'_eq matching_nodeId' matching_ccId' nodup'

            have rankInvariant' : (z : unionFindLink nodeList) → z ∈ linkList' → (linkList'.filter (fun y => y.rank < z.rank ∧ ¬y.nodeId = y.ccId)).length ≥ z.rank := update_unionFind_rankInvariant nodeList linkList' uF uFLy uFLx uFLy' uFLx' y x (ne_comm.mp h_eq) h_uFLy_in h_uFLy_prop₁ h_uFLy_prop₂ h_uFLx_prop₁ h_uFLx_prop₂ h_idxOf_uFLy h_idxOf_uFLx h_rank_lt' h_rank_succ_isLt h_linkList'_eq h_uFLy'_eq h_uFLx'_eq nodup'

            ⟨linkList', matching_nodeId', matching_ccId', matching_length', matching_rank', nodup', rankInvariant'⟩



          else



            have h_rank_eq : uFLx.rank = uFLy.rank := by
              simp at h_rank_lt h_rank_lt'
              apply eq_of_le_of_ge h_rank_lt' h_rank_lt
            have h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length := by
              apply uF.rank_succ_isLt uFLx uFLy ?_ h_uFLx_in h_uFLy_in ?_ ?_ h_rank_eq
              · intro h_uFL_eq
                simp [h_uFL_eq, h_uFLy_prop₁, ne_comm.mp h_eq] at h_uFLx_prop₁
              · simp [h_uFLx_prop]
              · simp [h_uFLy_prop]
            let uFLx' : unionFindLink nodeList := ⟨uFLx.nodeId, uFLy.ccId, uFLx.rank⟩
            let uFLy' : unionFindLink nodeList := ⟨uFLy.nodeId, uFLy.ccId, ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩⟩
            let linkList' : List (unionFindLink nodeList) := (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy'
            have h_linkList'_eq : linkList' = (uF.linkList.set (uF.linkList.idxOf uFLx) uFLx').set (uF.linkList.idxOf uFLy) uFLy' := by
              simp [linkList']
            have h_uFLx'_eq : uFLx' = { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank } := by
              simp [uFLx']
            have h_uFLy'_eq : uFLy' = { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max uFLy.rank.val uFLx.rank.val.succ, by simp [h_rank_succ_isLt]⟩ } := by
              simp [uFLy']
            have h_uFLx'_in : uFLx' ∈ linkList' := update_unionFind_h_uFLx'_in nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_linkList'_eq h_uFLx'_eq
            have h_uFLy'_in : uFLy' ∈ linkList' := by
              simp [h_linkList'_eq]
              have h : List.idxOf uFLy uF.linkList < (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').length := by
                simp [h_idxOf_uFLy]
              simp [List.mem_set h]

            have matching_nodeId' : ∀ x ∈ nodeList, ∃! y ∈ linkList', x.id = y.nodeId := update_unionFind_matching_nodeId nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLy_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_idxOf_uFLy h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq

            have matching_ccId' : ∀ y ∈ linkList', ∃! x ∈ nodeList, x.id = y.ccId := update_unionFind_matching_ccId nodeList linkList' uF uFLx uFLy uFLx' uFLy' h_uFLy_in h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq

            have matching_length' : nodeList.length = linkList'.length := update_unionFind_matching_length nodeList linkList' uF uFLx uFLy uFLx' uFLy' h_linkList'_eq

            have nodup' : linkList'.Nodup := update_unionFind_nodup nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLy_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_rank_succ_isLt h_linkList'_eq h_uFLx'_eq h_uFLy'_eq

            have matching_rank' : (z : unionFindLink nodeList) → (h_z_in : z ∈ linkList') → z.nodeId = z.ccId ∨ z.rank < (List.choose (fun x => x.nodeId = z.ccId) linkList' (exists_parent_link linkList' matching_nodeId' matching_ccId' z h_z_in)).rank := update_unionFind_matching_rank nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLy_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_idxOf_uFLy (Fin.le_of_eq h_rank_eq) h_rank_succ_isLt h_uFLx'_in h_uFLy'_in h_linkList'_eq h_uFLx'_eq h_uFLy'_eq matching_nodeId' matching_ccId' nodup'

            have rankInvariant' : (z : unionFindLink nodeList) → z ∈ linkList' → (linkList'.filter (fun y => y.rank < z.rank ∧ ¬y.nodeId = y.ccId)).length ≥ z.rank := update_unionFind_rankInvariant_of_rank_eq nodeList linkList' uF uFLx uFLy uFLx' uFLy' x y h_eq h_uFLx_in h_uFLx_prop₁ h_uFLx_prop₂ h_uFLy_prop₁ h_uFLy_prop₂ h_idxOf_uFLx h_idxOf_uFLy h_rank_eq h_rank_succ_isLt h_uFLx'_in h_linkList'_eq h_uFLx'_eq h_uFLy'_eq nodup'

            ⟨linkList', matching_nodeId', matching_ccId', matching_length', matching_rank', nodup', rankInvariant'⟩

def matching_edge  (edgeList : List edge) (nodeList : List node) : Prop := ∀ x ∈ edgeList, (∃ y ∈ nodeList, x.node1 = y.id) ∧ (∃ z ∈ nodeList, x.node2 = z.id)

def update_edgesSoFar (edgesSoFar : List edge) (e : edge) (x y : Nat) : List edge := if x = y then edgesSoFar else e :: edgesSoFar

-- Liste mitgeben mit edgesSoFar für bessere Laufzeit siehe nodeList_of_edgeList_helper
def kruskal_helper (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) : List edge :=
  -- dbg_trace s!"edgeList = {edgeList}" -- debug output
  -- dbg_trace s!"uF.linkList = {uF.linkList}" -- debug output
  match edgeList with
  | [] => edgesSoFar
  | e::es =>
    have h : ∃ x ∈ nodeList, x.id = e.node1 := by
      have h : (∃ x ∈ nodeList, e.node1 = x.id) → (∃ x ∈ nodeList, x.id = e.node1) := by simp [eq_comm]
      simp [h (h_matching_edge e List.mem_cons_self).left]
    let x := (connected_component_of_unionFind_of_id uF e.node1 h)
    have h' : ∃ x ∈ nodeList, x.id = e.node2 := by
      have h' : (∃ x ∈ nodeList, e.node2 = x.id) → (∃ x ∈ nodeList, x.id = e.node2) := by simp [eq_comm]
      simp [h' (h_matching_edge e List.mem_cons_self).right]
    let y := (connected_component_of_unionFind_of_id uF e.node2 h')
    have h_matching_edge' : ∀ x ∈ es, (∃ y ∈ nodeList, x.node1 = y.id) ∧ ∃ z ∈ nodeList, x.node2 = z.id := by
      intro z h_in
      simp [h_matching_edge z (List.mem_cons_of_mem e h_in)]
    -- dbg_trace s!"{x} = {y}" -- debug output
    have h_x := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF e.node1 h
    have h_y := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF e.node2 h'
    let updated_uF := update_unionFind uF x y h_x h_y
    let updated_edgesSoFar := update_edgesSoFar edgesSoFar e x y
    kruskal_helper es nodeList updated_uF updated_edgesSoFar h_matching_edge' h_nodup

def kruskal (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) : List edge :=
    let edgeListSorted : List edge := edgeList.mergeSort
    let uF : unionFind nodeList := init_unionFind nodeList h_nodup
    have h_matching_edge : matching_edge edgeListSorted nodeList := by
      intro e h_e_in
      simp [edgeListSorted] at h_e_in
      simp [matching_edge] at h_matching_edge
      exact h_matching_edge e h_e_in
    kruskal_helper edgeListSorted nodeList uF [] h_matching_edge h_nodup





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
  constructor
  · intro h_x_in
    induction edgeList with
    | nil =>
      simp [nodeList_of_edgeList_helper] at h_x_in
    | cons e edgeList ih =>
      simp [nodeList_of_edgeList_helper] at h_x_in
      by_cases h_eq_or : e.node1 = x.id ∨ e.node2 = x.id
      · refine ⟨e, List.mem_cons_self, h_eq_or⟩
      · simp [h_eq_or]
        by_cases h : e.node1 = e.node2
        · simp [h] at h_eq_or
          simp [h, nodeList_of_edgeList_helper_eq edgeList [{ id := e.node2 }]] at h_x_in
          rcases h_x_in with ⟨h_x_in, h_x_eq⟩ | ⟨h_x_eq⟩
          · rcases ih h_x_in with ⟨y, h_y_in, h_y_eq_or⟩
            refine ⟨y, h_y_in, h_y_eq_or⟩
          · simp [h_x_eq] at h_eq_or
        · simp [h, nodeList_of_edgeList_helper_eq edgeList [{ id := e.node1 }, { id := e.node2 }]] at h_x_in
          rcases h_x_in with ⟨h_x_in, h_x_eq_or⟩ | ⟨h_x_eq_or⟩
          · exact ih h_x_in
          · by_cases h_x_eq : x = { id := e.node1 }
            · simp [h_x_eq] at h_eq_or
            · simp [h_x_eq] at h_x_eq_or
              simp [h_x_eq_or] at h_eq_or

  · intro h_ex_y
    rcases h_ex_y with ⟨y, h_y_in, h_y_eq_or⟩
    induction edgeList with
    | nil =>
      simp at h_y_in
    | cons e edgeList ih =>
      simp at h_y_in
      rcases h_y_in with ⟨h_y_eq⟩ | ⟨h_y_in⟩
      · simp [nodeList_of_edgeList_helper, ← h_y_eq]
        by_cases h_eq : y.node1 = y.node2
        · simp [h_eq] at h_y_eq_or
          simp [h_eq, h_y_eq_or, nodeList_of_edgeList_helper_eq edgeList [{ id := x.id }]]
        · simp [h_eq, nodeList_of_edgeList_helper_eq edgeList [{ id := y.node1 }, { id := y.node2 }]]
          right
          by_cases h_x_eq : y.node1 = x.id
          · simp [h_x_eq]
          · simp [h_x_eq] at h_y_eq_or
            simp [h_y_eq_or]
      · have ih := ih h_y_in
        simp [nodeList_of_edgeList_helper]
        by_cases h_eq : e.node1 = e.node2
        · simp [h_eq, nodeList_of_edgeList_helper_eq edgeList [{ id := e.node2 }], ih]
          by_cases h : x = { id := e.node2 }
          · simp [h]
          · simp [h]
        · simp [h_eq, nodeList_of_edgeList_helper_eq edgeList [{ id := e.node1 }, { id := e.node2 }], ih]
          by_cases h : x = { id := e.node1 }
          · simp [h]
          · simp [h]
            by_cases h' : x = { id := e.node2 }
            · simp [h']
            · simp [h']

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

theorem nodeList_of_edgeList_nodup (edgeList : List edge) : (nodeList_of_edgeList edgeList).Nodup := by
  simp [nodeList_of_edgeList]
  induction edgeList with
  | nil =>
    simp [nodeList_of_edgeList_helper]
  | cons e edgeList ih =>
    simp [nodeList_of_edgeList_helper]
    by_cases h : e.node1 = e.node2
    · simp [h]
      simp [nodeList_of_edgeList_helper_eq edgeList [{ id := e.node2 }]]
      simp [List.nodup_append_comm]
      simp [List.Nodup.filter (fun x => !decide (x = { id := e.node2 })) ih]
    · simp [h]
      simp [nodeList_of_edgeList_helper_eq edgeList [{ id := e.node1 }, { id := e.node2 }]]
      simp [List.nodup_append_comm]
      simp [List.Nodup.filter (fun x => !decide (x = { id := e.node1 }) && !decide (x = { id := e.node2 })) ih, h]

def kruskal_of_edgeList (edgeList : List edge) : List edge :=
  kruskal edgeList (nodeList_of_edgeList edgeList) (matching_edge_for_nodeList_of_edgeList edgeList) (nodeList_of_edgeList_nodup edgeList)

-- #min_imports
