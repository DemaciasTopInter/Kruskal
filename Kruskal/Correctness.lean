import Mathlib
import Kruskal.Basic
import Kruskal.Lists

namespace Kruskal


variable {m n : Nat} {α β : Type}

open SimpleGraph

def SimpleGraph.IsSpanningTree (G : SimpleGraph α) (H : SimpleGraph α) : Prop := H ≤ G ∧ H.IsAcyclic ∧ (∀ (x y : α), G.Reachable x y ↔ H.Reachable x y)

theorem spanninTree_connected_iff_connected (G : SimpleGraph α) (H : SimpleGraph α) (h : SimpleGraph.IsSpanningTree G H) : G.Connected ↔ H.Connected := by
  simp [SimpleGraph.connected_iff_exists_forall_reachable]
  simp [SimpleGraph.IsSpanningTree] at h
  rcases h with ⟨_, _, h⟩
  simp [h]

theorem nodeList_of_edgeList_helper_nonempty {nodeList : List node} (edgeList : List edge) : nodeList ≠ [] → nodeList_of_edgeList_helper edgeList nodeList ≠ [] := by
  intro h'
  induction edgeList generalizing nodeList with
  | nil =>
    simp [nodeList_of_edgeList_helper, h']
  | cons e edgeList ih =>
    by_cases h_eq : e.node1 = e.node2
    · simp [nodeList_of_edgeList_helper, h_eq]
      by_cases h_in : { id := e.node2 } ∈ nodeList
      · simp [h_in]
        apply ih h'
      · simp [h_in]
        apply ih
        · simp
    · simp [nodeList_of_edgeList_helper, h_eq]
      by_cases h_in₁ : { id := e.node1 } ∈ nodeList
      · by_cases h_in₂ : { id := e.node2 } ∈ nodeList
        · simp [h_in₁, h_in₂]
          apply ih h'
        · simp [h_in₁, h_in₂]
          apply ih
          · simp
      · by_cases h_in₂ : { id := e.node2 } ∈ nodeList
        · simp [h_in₁, h_in₂]
          apply ih
          · simp
        · simp [h_in₁, h_in₂]
          apply ih
          · simp

theorem nodeList_of_edgeList_nonempty (edgeList : List edge) (h : edgeList ≠ []) : nodeList_of_edgeList edgeList ≠ [] := by
  cases edgeList with
  | nil =>
    simp at h
  | cons e edgeList =>
    simp [nodeList_of_edgeList, nodeList_of_edgeList_helper]
    by_cases h_eq : e.node1 = e.node2
    · simp [h_eq, nodeList_of_edgeList_helper_nonempty]
    · simp [h_eq, nodeList_of_edgeList_helper_nonempty]

def nodeList_of_edgeList_max (edgeList : List edge) (h : edgeList ≠ []) : node := (nodeList_of_edgeList edgeList).max (nodeList_of_edgeList_nonempty edgeList h)

def fin_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : Type := Fin (nodeList_of_edgeList_max edgeList h).id.succ

-- def SimpleGraph_of_edgeSet (edgeSet : Set edge) : SimpleGraph (Fin n) where
--   Adj (a b) := ∃ e ∈ edgeSet, (e.node1 = a.val ∧ e.node2 = b.val) ∨ (e.node1 = b.val ∧ e.node2 = a.val)
--   symm := by
--     simp [Symmetric]
--     intro a b e h_e_in h_adj
--     refine ⟨e, h_e_in, h_adj.symm⟩
--   loopless := by
--     simp [irrefl_def]
--     intro a e h_e h_eq₁ h_eq₂
--     have h_lt := e.nodesLt
--     simp [h_eq₁, h_eq₂] at h_lt

def SimpleGraph_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph (fin_of_edgeList edgeList h) where -- := SimpleGraph_of_edgeSet {e | e ∈ edgeList}
  Adj (a b) := ∃ e ∈ edgeList, (e.node1 = a.val ∧ e.node2 = b.val) ∨ (e.node1 = b.val ∧ e.node2 = a.val)
  symm := by
    simp [Symmetric]
    intro a b e h_e_in h_adj
    refine ⟨e, h_e_in, h_adj.symm⟩
  loopless := by
    simp [irrefl_def]
    intro a e h_e h_eq₁ h_eq₂
    have h_lt := e.nodesLt
    simp [h_eq₁, h_eq₂] at h_lt

-- def SimpleGraph_of_n_of_edgeList (n : Nat) (edgeList : List edge) (h : edgeList ≠ []) (h_eq : n = (nodeList_of_edgeList_max edgeList h).id.succ) : SimpleGraph (Fin n) :=
--   let G := SimpleGraph_of_edgeList edgeList h
--   have test : SimpleGraph (fin_of_edgeList edgeList h) = SimpleGraph (Fin n) := by
--     simp [fin_of_edgeList, h_eq]
--   have hx : 1=1 := by
--     simp [test] at G
--   G

theorem connected_component_of_init_unionFind_of_id_eq_id {nodeList : List node} {h_nodup : nodeList.Nodup} {id : Nat} {h : ∃ x ∈ nodeList, x.id = id} : connected_component_of_unionFind_of_id (init_unionFind nodeList h_nodup) id h = id := by
  simp [init_unionFind]
  by_cases h_nonempty : nodeList ≠ []
  · simp [h_nonempty]
    simp [connected_component_of_unionFind_of_id]
    have h_ex : ∃ y ∈ (init_unionFind_helper nodeList (by simp [h_nonempty])), (fun x => x.nodeId = id) y := by
      let uF := init_unionFind nodeList h_nodup
      have h_linkList_eq : uF.linkList = (init_unionFind_helper nodeList (by simp [h_nonempty])) := by
        simp [uF, init_unionFind, h_nonempty]
      simp [← h_linkList_eq]
      rcases h with ⟨z, h_z_in, h_z_id_eq⟩
      have h_matching_nodeId := uF.matching_nodeId z h_z_in
      simp [ExistsUnique, h_z_id_eq] at h_matching_nodeId
      rcases h_matching_nodeId with ⟨y, h_y, h_unique⟩
      refine ⟨y, ?_⟩
      simp [h_y]
    set x := List.choose (fun x => x.nodeId = id) (init_unionFind_helper nodeList (by simp [h_nonempty])) h_ex with h_x
    simp [← h_x]
    have h_x_in := List.choose_mem (fun x => x.nodeId = id) (init_unionFind_helper nodeList (by simp [h_nonempty])) h_ex
    simp [← h_x] at h_x_in
    simp [init_unionFind_helper] at h_x_in
    have h_x_prop := List.choose_property (fun x => x.nodeId = id) (init_unionFind_helper nodeList (by simp [h_nonempty])) h_ex
    simp [← h_x] at h_x_prop
    have h_x_selfcon := init_unionFind_helper.helper_all_self_connected nodeList nodeList (by simp [h_nonempty]) x h_x_in
    simp [h_x_selfcon.symm, h_x_prop]
  · simp at h_nonempty
    simp [h_nonempty] at h

theorem kruskal_helper_nonempty
  {edgeList : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  {h_matching_edge : matching_edge edgeList nodeList}
  {h_nodup : nodeList.Nodup}
  : edgesSoFar ≠ [] → kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup ≠ [] := by
  intro h_nonempty
  induction edgeList generalizing uF edgesSoFar with
  | nil =>
    simp [kruskal_helper, h_nonempty]
  | cons e edgeList ih =>
    simp [kruskal_helper]
    split_ifs
    · apply ih
      simp [h_nonempty]
    · apply ih
      simp

theorem kruskal_nonempty (edgeList : List edge) (h : edgeList ≠ []) : kruskal_of_edgeList edgeList ≠ [] := by
  simp [kruskal_of_edgeList]
  unfold kruskal
  -- simp [kruskal]
  -- set edgeListSorted := edgeList.mergeSort with h_edgeListSorted
  cases edgeList with
  | nil =>
    simp at h
  | cons e edgeList =>
    simp
    -- simp [] at h_edgeListSorted
    have h_split := List.mergeSort_cons (α := edge) (le := fun a b => decide (a ≤ b)) (by simp; exact edge_Preorder.le_trans) (by simp; exact edge_LinearOrder.le_total) e edgeList
    rcases h_split with ⟨l₁, l₂, h_split⟩
    simp [h_split]
    cases l₁ with
    | nil =>
      simp [kruskal_helper]
      simp [connected_component_of_init_unionFind_of_id_eq_id]
      by_cases h_eq : e.node1 = e.node2
      · have h_contra := e.nodesLt
        simp [h_eq] at h_contra
      · simp [h_eq]
        exact kruskal_helper_nonempty (by simp)
    | cons f l₁ =>
      simp [kruskal_helper]
      simp [connected_component_of_init_unionFind_of_id_eq_id]
      by_cases h_eq : f.node1 = f.node2
      · have h_contra := f.nodesLt
        simp [h_eq] at h_contra
      · simp [h_eq]
        exact kruskal_helper_nonempty (by simp)

def SimpleGraph_of_kruskal (edgeList : List edge) (h : edgeList ≠ []) := SimpleGraph_of_edgeList (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h)

theorem kruskal_helper_sublist {edgeList : List edge} {nodeList : List node} {uF : unionFind nodeList} {edgesSoFar : List edge} {h_matching_edge : matching_edge edgeList nodeList} {h_nodup : nodeList.Nodup} : ∀ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e ∈ edgeList ∨ e ∈ edgesSoFar := by
  induction edgeList, uF, edgesSoFar, h_matching_edge using kruskal_helper.induct with
  | case1 uF edgesSoFar h_matching_edge =>
    simp [kruskal_helper]
  | case2 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_eq ih₁ =>
    simp [kruskal_helper]
    simp [x, y] at h_eq
    simp [h_eq]
    intro f h_f_in
    rcases (ih₁ f h_f_in) with ⟨h_f_in⟩ | ⟨h_f_in⟩
    · simp [h_f_in]
    · simp [h_f_in]
  | case3 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_ne h_x h_y ih₁ ih₂ =>
    simp [kruskal_helper]
    simp [x, y] at h_ne
    simp [h_ne]
    intro f h_f_in
    rcases (ih₂ f h_f_in) with ⟨h_f_in⟩ | ⟨h_f_in⟩
    · simp [h_f_in]
    · simp at h_f_in
      rcases h_f_in with ⟨h_f_eq⟩ | ⟨h_f_in⟩
      · simp [h_f_eq]
      · simp [h_f_in]

theorem kruskal_sublist {edgeList : List edge} {nodeList : List node} {h_matching_edge : matching_edge edgeList nodeList} {h_nodup : nodeList.Nodup} : ∀ e ∈ kruskal edgeList nodeList h_matching_edge h_nodup, e ∈ edgeList := by
  simp [kruskal]
  intro e h_e_in
  have h := kruskal_helper_sublist e h_e_in
  simp at h
  exact h

theorem ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node
  {edgeList : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar₁ edgesSoFar₂ : List edge}
  {h_matching_edge : matching_edge edgeList nodeList}
  {h_nodup : nodeList.Nodup}
  : kruskal_helper edgeList nodeList uF (edgesSoFar₁ ++ edgesSoFar₂) h_matching_edge h_nodup = kruskal_helper edgeList nodeList uF edgesSoFar₁ h_matching_edge h_nodup ++ edgesSoFar₂ := by
  set edgesSoFar := edgesSoFar₁ ++ edgesSoFar₂ with h_edgesSoFar
  revert h_edgesSoFar
  induction edgeList, uF, edgesSoFar, h_matching_edge using kruskal_helper.induct nodeList generalizing edgesSoFar₁ with
  | case1 uF edgesSoFar h_matching_edge =>
    simp [kruskal_helper]
  | case2 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_eq ih =>
    simp [kruskal_helper]
    simp [x, y] at h_eq
    simp [h_eq]
    exact ih
  | case3 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_ne h_x h_y uF' ih =>
    simp [kruskal_helper]
    simp [x, y] at h_ne
    simp [h_ne]
    have h_uF' : uF' = update_unionFind uF x y h_x h_y := by
      simp [uF']
    simp [x, y] at h_uF'
    simp [← h_uF']
    have ih := ih (edgesSoFar₁ := e :: edgesSoFar₁)
    simp at ih
    exact ih

theorem kruskal_helper_append {edgeList₁ edgeList₂ : List edge} {nodeList : List node} {uF : unionFind nodeList} {edgesSoFar : List edge} {h_matching_edge : matching_edge (edgeList₁ ++ edgeList₂) nodeList} {h_matching_edge₁ : matching_edge edgeList₁ nodeList} {h_matching_edge₂ : matching_edge edgeList₂ nodeList} {h_nodup : nodeList.Nodup} : kruskal_helper (edgeList₁ ++ edgeList₂) nodeList uF edgesSoFar h_matching_edge h_nodup = kruskal_helper edgeList₂ nodeList uF ((kruskal_helper edgeList₁ nodeList uF [] h_matching_edge₁ h_nodup) ++ edgesSoFar) h_matching_edge₂ h_nodup := by
  induction edgeList₁ generalizing uF edgesSoFar with
  | nil =>
    simp
    have h_empty : kruskal_helper [] nodeList uF [] h_matching_edge₁ h_nodup = [] := by
      simp [kruskal_helper]
    simp [h_empty]
  | cons e edgeList₁ ih =>
    simp [kruskal_helper]
    simp [matching_edge] at h_matching_edge₁
    by_cases h_eq : connected_component_of_unionFind_of_id uF e.node1 (by grind) = connected_component_of_unionFind_of_id uF e.node2 (by grind)
    · simp [h_eq]
      exact ih
    · simp [h_eq]
      set uF' := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 sorry) (connected_component_of_unionFind_of_id uF e.node2 sorry) sorry sorry
      simp [matching_edge] at h_matching_edge
      have ih := ih (uF := uF') (edgesSoFar := e :: edgesSoFar) (h_matching_edge₁ := h_matching_edge₁.right) (h_matching_edge := by simp [matching_edge]; exact h_matching_edge.right)
      simp [ih]
      have h_nil_append : [e] = [] ++ [e] := by
        simp
      rw [h_nil_append]
      simp only [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node]
      simp [kruskal_helper]
      sorry -- Denkfehler

theorem nodeList_of_kruskal_perm (edgeList : List edge) : List.Perm (nodeList_of_edgeList (kruskal_of_edgeList edgeList)) (nodeList_of_edgeList edgeList) := by
  have h_nodup1 := nodeList_of_edgeList_nodup (kruskal_of_edgeList edgeList)
  have h_nodup2 := nodeList_of_edgeList_nodup edgeList
  apply (List.perm_ext_iff_of_nodup h_nodup1 h_nodup2).mpr
  intro x
  constructor
  · intro h_x_in_nodeList_of_kruskal
    simp [nodeList_of_edgeList] at h_x_in_nodeList_of_kruskal
    have h_ex_e := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList (kruskal_of_edgeList edgeList) x).mp h_x_in_nodeList_of_kruskal
    rcases h_ex_e with ⟨e, h_e_in_kruskal, h_e_con_x⟩
    have h_e_in_edgeList := kruskal_sublist e h_e_in_kruskal
    simp [nodeList_of_edgeList]
    apply (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList x).mpr
    refine ⟨e, h_e_in_edgeList, h_e_con_x⟩
  · intro h_x_in_nodeList_of_edgeList
    simp [nodeList_of_edgeList] at h_x_in_nodeList_of_edgeList
    have h_ex_e := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList x).mp h_x_in_nodeList_of_edgeList
    rcases h_ex_e with ⟨e, h_e_in_kruskal, h_e_con_x⟩
    simp [nodeList_of_edgeList]
    simp [kruskal_of_edgeList, kruskal]
    set edgeListSorted : List edge := edgeList.mergeSort with h_edgeListSorted
    simp [← h_edgeListSorted]
    have h_e_in_edgeListSorted : e ∈ edgeListSorted := by
      simp [h_edgeListSorted, h_e_in_kruskal]
    have h_ex : ∃ e_1 ∈ edgeListSorted, e_1.node1 = x.id ∨ e_1.node2 = x.id := by
      refine ⟨e, h_e_in_edgeListSorted, h_e_con_x⟩
    have h_split := prop_split (fun (e_1 : edge) => e_1.node1 = x.id ∨ e_1.node2 = x.id) h_ex
    rcases h_split with ⟨l₁, l₂, f, h_split, h_f_con_x, h_l₁_not_con_x⟩
    simp [h_split]
    sorry

theorem SimpleGraph_of_kruskal_IsSubgraph (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h) ≤ (SimpleGraph_of_edgeList edgeList h) := by sorry

theorem SimpleGraph_of_kruskal_IsAcyclic (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h).IsAcyclic := by sorry

theorem SimpleGraph_of_kruskal_IsEqReachable (edgeList : List edge) (h : edgeList ≠ []) : ∀ (x y), (SimpleGraph_of_edgeList edgeList h).Reachable x y ↔ (SimpleGraph_of_kruskal edgeList h).Reachable x y := by sorry

theorem SimpleGraph_of_kruskal_IsSpanningTree (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph.IsSpanningTree (SimpleGraph_of_kruskal edgeList h) (SimpleGraph_of_edgeList edgeList h) := by sorry

def cost_of_edgeList : List edge → Nat
  | [] => 0
  | e :: edgeList => e.cost + cost_of_edgeList edgeList

def minimalSpanninTree_of_edgeList (edgeList : List edge) (h₁ : edgeList ≠ []) (G := SimpleGraph_of_edgeList edgeList h₁) (minEdgeList : List edge) (h₂ : minEdgeList ≠ []) (h₃ : SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList minEdgeList h₂)) (h₄ : ∀ x ∈ minEdgeList, x ∈ edgeList) : Prop := ∀ (el : List edge), (h₅ : el ≠ []) → (h₆ : ∀ x ∈ el, x ∈ edgeList) → SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList el h₅) → (cost_of_edgeList el) ≥ (cost_of_edgeList minEdgeList)

theorem kruskal_minimalSpanninTree_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : minimalSpanninTree_of_edgeList edgeList h (SimpleGraph_of_edgeList edgeList h₁) (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) := by sorry
