import Mathlib
import Kruskal.Basic
import Kruskal.Lists

-- set_option pp.all true

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

def SimpleGraph_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph (fin_of_edgeList edgeList h) where
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

def SimpleGraph_of_n_of_edgeList (n : Nat) (edgeList : List edge) (h : edgeList ≠ []) (h_eq : n = (nodeList_of_edgeList_max edgeList h).id.succ) : SimpleGraph (Fin n) :=
  let G := SimpleGraph_of_edgeList edgeList h
  let Adj := fun (a b : Fin n) => G.Adj ⟨a, by rw [← h_eq]; exact a.isLt⟩ ⟨b, by rw [← h_eq]; exact b.isLt⟩
  have symm : Symmetric Adj := by
    simp [Symmetric, Adj]
    intro a b
    have h_symm := G.symm
    simp only [Symmetric] at h_symm
    exact h_symm (x := ⟨a, by rw [← h_eq]; exact a.isLt⟩) (y := ⟨b, by rw [← h_eq]; exact b.isLt⟩)
  have loopless : Std.Irrefl Adj := by
    simp [irrefl_def, Adj]
  ⟨Adj, symm, loopless⟩
-- def SimpleGraph_of_n_of_edgeList (n : Nat) (edgeList : List edge) (h : edgeList ≠ []) (h_eq : n = (nodeList_of_edgeList_max edgeList h).id.succ) : SimpleGraph (Fin n) := by
--   let G := SimpleGraph_of_edgeList edgeList h
--   have h_eq : SimpleGraph (fin_of_edgeList edgeList h) = SimpleGraph (Fin n) := by
--     simp [fin_of_edgeList, h_eq]
--   rw [← h_eq]
--   exact G

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
    simp [kruskal_helper, update_unionFind]
    apply ih
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
      exact kruskal_helper_nonempty (by simp)
    | cons f l₁ =>
      simp [kruskal_helper]
      simp [connected_component_of_init_unionFind_of_id_eq_id]
      exact kruskal_helper_nonempty (by simp)

def SimpleGraph_of_kruskal (edgeList : List edge) (h : edgeList ≠ []) := SimpleGraph_of_n_of_edgeList (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) _).id.succ (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) (rfl)

theorem kruskal_helper_sublist {edgeList : List edge} {nodeList : List node} {uF : unionFind nodeList} {edgesSoFar : List edge} {h_matching_edge : matching_edge edgeList nodeList} {h_nodup : nodeList.Nodup} : ∀ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e ∈ edgeList ∨ e ∈ edgesSoFar := by
  induction edgeList, uF, edgesSoFar, h_matching_edge using kruskal_helper.induct with
  | case1 uF edgesSoFar h_matching_edge =>
    simp [kruskal_helper]
  | case2 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_eq ih₁ updateUF ih₂ =>
    simp [kruskal_helper]
    -- simp [x, y] at h_eq
    simp [updateUF, x, y] at ih₂
    grind

theorem kruskal_sublist {edgeList : List edge} {nodeList : List node} {h_matching_edge : matching_edge edgeList nodeList} {h_nodup : nodeList.Nodup} : ∀ e ∈ kruskal edgeList nodeList h_matching_edge h_nodup, e ∈ edgeList := by
  simp [kruskal]
  intro e h_e_in
  have h := kruskal_helper_sublist e h_e_in
  simp at h
  exact h

theorem ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node -- besserer Name: kruskal_helper.edgesSoFar_append
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
  | case2 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_eq ih₁ updateUF =>
    rename_i ih₂ -- strange aber funktioniert so
    simp [kruskal_helper]
    grind

theorem kruskal_helper.edgeList_append {edgeList₁ edgeList₂ : List edge} {nodeList : List node} {uF : unionFind nodeList} {edgesSoFar : List edge} {h_matching_edge : matching_edge (edgeList₁ ++ edgeList₂) nodeList} {h_matching_edge₁ : matching_edge edgeList₁ nodeList} {h_matching_edge₂ : matching_edge edgeList₂ nodeList} {h_nodup : nodeList.Nodup} : ∃ (uF' : unionFind nodeList), kruskal_helper (edgeList₁ ++ edgeList₂) nodeList uF edgesSoFar h_matching_edge h_nodup = kruskal_helper edgeList₂ nodeList uF' ((kruskal_helper edgeList₁ nodeList uF [] h_matching_edge₁ h_nodup) ++ edgesSoFar) h_matching_edge₂ h_nodup := by
  induction edgeList₁ generalizing uF edgesSoFar with
  | nil =>
    simp
    have h_empty : kruskal_helper [] nodeList uF [] h_matching_edge₁ h_nodup = [] := by
      simp [kruskal_helper]
    simp [h_empty]
    refine ⟨uF, rfl⟩
  | cons e edgeList₁ ih =>
    simp [kruskal_helper]
    simp [matching_edge] at h_matching_edge₁
    by_cases h_eq : connected_component_of_unionFind_of_id uF e.node1 (by grind) = connected_component_of_unionFind_of_id uF e.node2 (by grind)
    · simp [update_unionFind, h_eq]
      have h : [e] = [] ++ [e] := by
        simp
      rw [h]
      simp only [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node]
      simp only [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node] at ih
      simp
      exact ih
    · set uF' := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (by grind)) (connected_component_of_unionFind_of_id uF e.node2 (by grind)) _ _
      simp [matching_edge] at h_matching_edge
      have ih := ih (uF := uF') (edgesSoFar := e :: edgesSoFar) (h_matching_edge₁ := h_matching_edge₁.right) (h_matching_edge := by simp [matching_edge]; exact h_matching_edge.right)
      rcases ih with ⟨uF'', ih⟩
      simp [ih]
      have h_nil_append : [e] = [] ++ [e] := by
        simp
      rw [h_nil_append]
      simp only [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node]
      simp
      refine ⟨uF'', rfl⟩

theorem kruskal_helper_not_con_invariant
  {edgeList : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  {h_matching_edge : matching_edge edgeList nodeList}
  {h_nodup : nodeList.Nodup}
  {z : node}
  (h_edgeList_not_con : ∀ e ∈ edgeList, ¬(e.node1 = z.id ∨ e.node2 = z.id))
  (h_uF_not_con : ∀ uFL ∈ uF.linkList, uFL.ccId = z.id ↔ uFL.nodeId = z.id)
  : ∃ (uF' : unionFind nodeList), kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup = kruskal_helper [] nodeList uF' ((kruskal_helper edgeList nodeList uF [] h_matching_edge h_nodup) ++ edgesSoFar) (by simp [matching_edge]) h_nodup ∧ ∀ uFL ∈ uF'.linkList, uFL.ccId = z.id ↔ uFL.nodeId = z.id := by
  induction edgeList with
  | nil =>
    simp [kruskal_helper]
    refine ⟨uF, h_uF_not_con⟩
  | cons e edgeList ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h_edgeList_not_con
    set eSF := kruskal_helper (e :: edgeList) nodeList uF [] h_matching_edge h_nodup ++ edgesSoFar
    set k := kruskal_helper (e :: edgeList) nodeList uF edgesSoFar h_matching_edge h_nodup
    simp [kruskal_helper]
    simp [eSF, k]
    constructor
    · have h : edgesSoFar = [] ++ edgesSoFar := by
        simp
      rw [h]
      exact ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node
    · refine ⟨uF, h_uF_not_con⟩

theorem connected_component_of_unionFind_of_id_not_con
  {nodeList : List node}
  {uF : unionFind nodeList}
  {z : node}
  (h_z_in : z ∈ nodeList)
  (h_uF_not_con : ∀ uFL ∈ uF.linkList, uFL.ccId = z.id ↔ uFL.nodeId = z.id)
  : ∀ (x : node), (h_x_in : x ∈ nodeList) → connected_component_of_unionFind_of_id uF x.id ⟨x, h_x_in, rfl⟩ = z.id ↔ x = z := by
  intro x h_x_in
  constructor
  · simp [connected_component_of_unionFind_of_id]
    have h_ex_uFLx : ∃ a ∈ uF.linkList, (fun y => y.nodeId = x.id) a := by
      have h := uF.matching_nodeId x h_x_in
      simp [ExistsUnique] at h
      rcases h with ⟨a, h_a, _⟩
      grind
    set uFLx := List.choose (fun y => y.nodeId = x.id) uF.linkList h_ex_uFLx with h_uFLx
    have h_uFLx_prop := List.choose_property (fun y => y.nodeId = x.id) uF.linkList h_ex_uFLx
    have h_uFLx_in := List.choose_mem (fun y => y.nodeId = x.id) uF.linkList h_ex_uFLx
    simp_all [← h_uFLx]
    by_cases h_uFLx_self_con : uFLx.ccId = uFLx.nodeId
    · simp [← h_uFLx_self_con, ← h_uFLx_prop]
      intro h_eq
      have h := (h_uF_not_con uFLx h_uFLx_in).mp h_eq
      cases x
      cases z
      simp [h] at h_uFLx_prop
      simp [h_uFLx_prop.symm]
    · simp [h_uFLx_self_con, ← h_uFLx_prop]
      have h_goal : ∀ (uFL : unionFindLink nodeList) (h_in : uFL ∈ uF.linkList), connected_component_of_unionFind_of_id_helper uF uFL h_in = z.id → uFL.nodeId = z.id := by
        intro uFL h_uFL_in
        induction uFL, h_uFL_in using connected_component_of_unionFind_of_id_helper.induct with
        | case1 uFL h_uFL_in h_uFL_self_con =>
          rw [connected_component_of_unionFind_of_id_helper]
          simp [h_uFL_self_con]
        | case2 uFL h_uFL_in h_uFL_not_self_con uFLy h_uFLy_in h_rank_lt ih =>
          rw [connected_component_of_unionFind_of_id_helper]
          simp [h_uFL_not_self_con]
          intro h_id
          have h_uFLx_prop := List.choose_property (fun y => y.nodeId = uFL.ccId) uF.linkList (by grind)
          simp [h_id, uFLy, h_uFLx_prop] at ih
          exact (h_uF_not_con uFL h_uFL_in).mp ih
      intro h_eq
      have h := h_goal uFLx h_uFLx_in h_eq
      simp [h_uFLx_prop] at h
      cases x
      cases z
      simp at h
      simp [h]
  · intro h_eq
    simp [h_eq, connected_component_of_unionFind_of_id]
    have h_ex_uFLz : ∃ a ∈ uF.linkList, (fun x => x.nodeId = z.id) a := by
      have h := uF.matching_nodeId z h_z_in
      simp [ExistsUnique] at h
      rcases h with ⟨a, h_a, _⟩
      grind
    set uFLz := List.choose (fun x => x.nodeId = z.id) uF.linkList h_ex_uFLz with h_uFLz
    have h_uFLz_prop := List.choose_property (fun x => x.nodeId = z.id) uF.linkList h_ex_uFLz
    have h_uFLz_in := List.choose_mem (fun x => x.nodeId = z.id) uF.linkList h_ex_uFLz
    simp [← h_uFLz] at *
    simp [h_uFLz_prop, (h_uF_not_con uFLz h_uFLz_in)]

theorem kruskal_helper_not_con_invariant_append
  {edgeList₁ edgeList₂ : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  {h_matching_edge : matching_edge (edgeList₁ ++ edgeList₂) nodeList}
  {h_nodup : nodeList.Nodup}
  {z : node}
  (h_z_in : z ∈ nodeList)
  (h_edgeList_not_con : ∀ e ∈ edgeList₁, ¬(e.node1 = z.id ∨ e.node2 = z.id))
  (h_uF_not_con : ∀ uFL ∈ uF.linkList, uFL.ccId = z.id ↔ uFL.nodeId = z.id)
  : ∃ (uF' : unionFind nodeList), kruskal_helper (edgeList₁ ++ edgeList₂) nodeList uF edgesSoFar h_matching_edge h_nodup = kruskal_helper edgeList₂ nodeList uF' ((kruskal_helper edgeList₁ nodeList uF [] (by simp [matching_edge] at h_matching_edge; simp [matching_edge]; grind) h_nodup) ++ edgesSoFar) (by simp [matching_edge] at h_matching_edge; simp [matching_edge]; grind) h_nodup ∧ ∀ uFL ∈ uF'.linkList, uFL.ccId = z.id ↔ uFL.nodeId = z.id := by
  induction edgeList₁ generalizing uF edgesSoFar with
  | nil =>
    simp [kruskal_helper]
    refine ⟨uF, rfl, h_uF_not_con⟩
  | cons e edgeList₁ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h_edgeList_not_con
    simp [kruskal_helper]
    set x := connected_component_of_unionFind_of_id uF e.node1 _ with h_x
    set y := connected_component_of_unionFind_of_id uF e.node2 _ with h_y
    simp [← h_x, ← h_y]
    have h : [e] = [] ++ [e] := by
      simp
    rw [h]
    simp only [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node]
    simp
    simp only [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node] at ih
    apply ih
    · exact h_edgeList_not_con.right
    · by_cases h_eq : x = y
      · simp [update_unionFind, h_eq]
        exact h_uF_not_con
      · simp [update_unionFind, h_eq]
        have h_x_ne_z : x ≠ z.id := by
          simp at h_edgeList_not_con
          simp [matching_edge] at h_matching_edge
          rcases h_matching_edge.left.left with ⟨nx, h_nx_in, h_nx⟩
          have h := (connected_component_of_unionFind_of_id_not_con h_z_in h_uF_not_con nx h_nx_in).mp
          intro h_contra
          simp [← h_contra, ← h_nx, h_x] at h
          cases z
          cases nx
          simp at h
          simp [h] at h_nx
          simp [h_nx] at h_edgeList_not_con
        have h_y_ne_z : y ≠ z.id := by
          simp at h_edgeList_not_con
          simp [matching_edge] at h_matching_edge
          rcases h_matching_edge.left.right with ⟨ny, h_ny_in, h_ny⟩
          have h := (connected_component_of_unionFind_of_id_not_con h_z_in h_uF_not_con ny h_ny_in).mp
          intro h_contra
          simp [← h_contra, ← h_ny, h_y] at h
          cases z
          cases ny
          simp at h
          simp [h] at h_ny
          simp [h_ny] at h_edgeList_not_con
        set uFLx := List.choose (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList _ with h_uFLx
        set uFLy := List.choose (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList _ with h_uFLy
        have h_uFLx_prop : uFLx.nodeId = x ∧ uFLx.ccId = x := List.choose_property (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList _
        have h_uFLy_prop : uFLy.nodeId = y ∧ uFLy.ccId = y := List.choose_property (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList _
        simp [← h_uFLx, ← h_uFLy]
        by_cases h_rank_lt : uFLx.rank < uFLy.rank
        · simp [h_rank_lt]
          intro uFL h_uFL_in
          rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
          · rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
            · exact h_uF_not_con uFL h_uFL_in
            · simp [h_uFL_eq, h_uFLx_prop, h_uFLy_prop, h_x_ne_z, h_y_ne_z]
          · simp [h_uFL_eq, h_uFLy_prop, h_y_ne_z]
        · by_cases h_rank_lt' : uFLy.rank < uFLx.rank
          · simp [h_rank_lt, h_rank_lt']
            intro uFL h_uFL_in
            rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
            · rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
              · exact h_uF_not_con uFL h_uFL_in
              · simp [h_uFL_eq, h_uFLx_prop, h_uFLy_prop, h_x_ne_z, h_y_ne_z]
            · simp [h_uFL_eq, h_uFLx_prop, h_x_ne_z]
          · simp [h_rank_lt, h_rank_lt']
            intro uFL h_uFL_in
            rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
            · rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
              · exact h_uF_not_con uFL h_uFL_in
              · simp [h_uFL_eq, h_uFLx_prop, h_uFLy_prop, h_x_ne_z, h_y_ne_z]
            · simp [h_uFL_eq, h_uFLy_prop, h_y_ne_z]

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
    simp [h_split, nodeList_of_edgeList]
    simp [nodeList_of_edgeList] at h_nodup2
    set uF := init_unionFind (nodeList_of_edgeList_helper edgeList []) _
    have h_edgeList_not_con : ∀ e ∈ l₁, ¬(e.node1 = x.id ∨ e.node2 = x.id) := by
      exact h_l₁_not_con_x
    have h_uF_not_con : ∀ uFL ∈ uF.linkList, uFL.ccId = x.id ↔ uFL.nodeId = x.id := by
      have h_nonempty : nodeList_of_edgeList_helper edgeList [] ≠ [] := by
        intro h_contra
        simp [h_contra] at h_x_in_nodeList_of_edgeList
      simp [uF, init_unionFind, h_nonempty, init_unionFind_helper]
      have h := init_unionFind_helper.helper_all_self_connected (nodeList_of_edgeList_helper edgeList []) (nodeList_of_edgeList_helper edgeList []) (by simp [h_nonempty])
      intro uFL h_uFL_in
      simp [h uFL h_uFL_in]
    have h_matching_edge : matching_edge (l₁ ++ f :: l₂) (nodeList_of_edgeList_helper edgeList []) := by
      simp [← h_split, edgeListSorted, matching_edge]
      intro g h_g_in
      constructor
      · have h := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList { id := g.node1 }).mpr
        simp at h
        have h := h g h_g_in
        simp at h
        refine ⟨{ id := g.node1 }, h, by simp⟩
      · have h := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList { id := g.node2 }).mpr
        simp at h
        have h := h g h_g_in
        simp at h
        refine ⟨{ id := g.node2 }, h, by simp⟩
    have h := kruskal_helper_not_con_invariant_append h_x_in_nodeList_of_edgeList h_edgeList_not_con h_uF_not_con (h_nodup := h_nodup2) (h_matching_edge := h_matching_edge) (edgesSoFar := []) (uF := uF) (edgeList₂ := f :: l₂)
    rcases h with ⟨uF', h_eq, h_uF'_not_con⟩
    simp [h_eq]
    set k_l₁ := kruskal_helper l₁ (nodeList_of_edgeList_helper edgeList []) uF [] _ h_nodup2
    simp [kruskal_helper]
    have h_f_in : f ∈ edgeListSorted := by
      simp [h_split]
    simp [edgeListSorted] at h_f_in
    have h_ex_f_node1 : ∃ x ∈ nodeList_of_edgeList_helper edgeList [], x.id = f.node1 := by
      have h := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList { id := f.node1 }).mpr
      simp at h
      refine ⟨{ id := f.node1 }, ?_, by simp⟩
      apply h f
      · exact h_f_in
      · simp
    have h_ex_f_node2 : ∃ x ∈ nodeList_of_edgeList_helper edgeList [], x.id = f.node2 := by
      have h := (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList edgeList { id := f.node2 }).mpr
      simp at h
      refine ⟨{ id := f.node2 }, ?_, by simp⟩
      apply h f
      · exact h_f_in
      · simp
    have h_ne : connected_component_of_unionFind_of_id uF' f.node1 h_ex_f_node1 ≠ connected_component_of_unionFind_of_id uF' f.node2 h_ex_f_node2 := by
      intro h_find_eq
      have h := connected_component_of_unionFind_of_id_not_con h_x_in_nodeList_of_edgeList h_uF'_not_con
      rcases h_f_con_x with h_f_con_x | h_f_con_x
      · rcases h_ex_f_node2 with ⟨y, h_y_in, h_y⟩
        have h_find_y := (h y h_y_in).mp
        have h_find_x := (h x h_x_in_nodeList_of_edgeList).mpr
        simp [← h_f_con_x] at h_find_x
        simp [h_y, ← h_f_con_x, ← h_find_eq] at h_find_y
        simp [h_find_x] at h_find_y
        simp [h_find_y, ← h_f_con_x] at h_y
        have h_contra := f.nodesLt
        simp [h_y] at h_contra
      · rcases h_ex_f_node1 with ⟨y, h_y_in, h_y⟩
        have h_find_y := (h y h_y_in).mp
        have h_find_x := (h x h_x_in_nodeList_of_edgeList).mpr
        simp [← h_f_con_x] at h_find_x
        simp [h_y, ← h_f_con_x, h_find_eq] at h_find_y
        simp [h_find_x] at h_find_y
        simp [h_find_y, ← h_f_con_x] at h_y
        have h_contra := f.nodesLt
        simp [h_y] at h_contra
    simp [h_ne]
    have h : f :: k_l₁ = [] ++ (f :: k_l₁) := by
      simp
    rw [h]
    set uF'' := update_unionFind uF' (connected_component_of_unionFind_of_id uF' f.node1 _) (connected_component_of_unionFind_of_id uF' f.node2 _) _ _
    rw [ex_mem_kruskal_helper_con_node_of_ex_mem_edgeList_con_node (edgeList := l₂) (nodeList := nodeList_of_edgeList_helper edgeList []) (uF := uF'')]
    apply (mem_nodeList_of_edgeList_helper_iff_node_in_edgeList (kruskal_helper l₂ (nodeList_of_edgeList_helper edgeList []) uF'' [] _ h_nodup2 ++ f :: k_l₁) x).mpr
    refine ⟨f, ?_⟩
    simp [h_f_con_x]

theorem nodeList_of_edgeList_max_eq (edgeList : List edge) (h : edgeList ≠ []) : (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h)).id.succ = (nodeList_of_edgeList_max edgeList h).id.succ := by
  simp [nodeList_of_edgeList_max]
  have h_edgeList_max := max_eq_maximum (nodeList_of_edgeList_nonempty edgeList h)
  have h_kruskal_max := max_eq_maximum (nodeList_of_edgeList_nonempty (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h))
  have h_maximum_eq := List.Perm.maximum_eq (nodeList_of_kruskal_perm edgeList)
  simp [h_maximum_eq, ← h_edgeList_max] at h_kruskal_max
  simp [h_kruskal_max]

theorem SimpleGraph_of_kruskal_IsSubgraph (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h) ≤ (SimpleGraph_of_n_of_edgeList (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) _).id.succ edgeList h (nodeList_of_edgeList_max_eq edgeList h)) := by
  simp [LE.le]
  simp [SimpleGraph_of_kruskal, SimpleGraph_of_n_of_edgeList, SimpleGraph_of_edgeList]
  intro u v e h_e_in h_adj
  refine ⟨e, kruskal_sublist e h_e_in, h_adj⟩

theorem kruskal_helper_Reachable_iff_con
  {edgeList : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  {h_matching_edge : matching_edge edgeList nodeList}
  {h_nodup : nodeList.Nodup}
  (h_nonempty : nodeList ≠ [])
  {h_symm : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  {h_loopless : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  (h_invariant : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => ∀ (a b : Fin _), (h_ex_x : ∃ x ∈ nodeList, x.id = ↑a) → (h_ex_y : ∃ x ∈ nodeList, x.id = ↑b) → (G.Reachable a b ↔ connected_component_of_unionFind_of_id uF a.val h_ex_x = connected_component_of_unionFind_of_id uF b.val h_ex_y)) { Adj := fun a b => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := sorry, loopless := sorry})
  : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => ∀ (a b : Fin _), (h_ex_x : ∃ x ∈ nodeList, x.id = ↑a) → (h_ex_y : ∃ x ∈ nodeList, x.id = ↑b) → (G.Reachable a b ↔ connected_component_of_unionFind_of_id uF a.val h_ex_x = connected_component_of_unionFind_of_id uF b.val h_ex_y)) { Adj := fun a b => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm, loopless := h_loopless } := by
  simp
  intro a b x h_x_in h_x y h_y_in h_y
  set ccx := connected_component_of_unionFind_of_id uF a.val ⟨x, h_x_in, h_x⟩
  set ccy := connected_component_of_unionFind_of_id uF b.val ⟨y, h_y_in, h_y⟩
  induction
    edgeList,
    uF,
    edgesSoFar,
    h_matching_edge
  using kruskal_helper.induct with
  | case1 uF edgesSoFar h_matching_edge =>
    simp [kruskal_helper]
    constructor
    · intro h_reachable
      have h := (h_invariant a b ⟨x, h_x_in, h_x⟩ ⟨y, h_y_in, h_y⟩).mp h_reachable
      simp [ccx, ccy, h]
    · intro h_eq
      have h := (h_invariant a b ⟨x, h_x_in, h_x⟩ ⟨y, h_y_in, h_y⟩).mpr h_eq
      simp [h]
  | case2 uF edgesSoFar e es h_matching_edge' h_ex_1 cce1 h_ex_2 cce2 h_matching_edge =>
    rename_i h_eq ih
    simp [kruskal_helper]
    simp at ih h_invariant
    have h_symm' : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper es nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by
      simp [Symmetric]
      intro u v f h_f_in h_adj
      rw [or_comm] at h_adj
      refine ⟨f, h_f_in, h_adj⟩
    have h_loopless' : Std.Irrefl fun (a : Fin ((nodeList.max h_nonempty).id + 1)) b => ∃ e ∈ kruskal_helper es nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by
      simp [irrefl_def]
      intro a e h_e h_eq₁ h_eq₂
      have h_lt := e.nodesLt
      simp [h_eq₁, h_eq₂] at h_lt
    have h := ih h_invariant (h_symm := h_symm') (h_loopless := h_loopless')
    by_cases h_cc_eq : ccx = ccy
    · simp [cce1, cce2] at h_eq
      simp [h_cc_eq, h_eq]
      simp [ccx, ccy] at h_cc_eq
      simp [h_cc_eq] at h
      exact h
    · simp [cce1, cce2] at h_eq
      simp [h_cc_eq, h_eq]
      simp [ccx, ccy] at h_cc_eq
      simp [h_cc_eq] at h
      exact h

theorem kruskal_helper_IsAcyclic
  {edgeList : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  {h_matching_edge : matching_edge edgeList nodeList}
  {h_nodup : nodeList.Nodup}
  -- (h_nodeList : nodeList = nodeList_of_edgeList edgeList)
  (h_nonempty : nodeList ≠ [])
  -- {G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)}
  {h_symm : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  {h_loopless : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  -- {h_G : G = { Adj := fun a b => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm, loopless := h_loopless }}
  -- (h_invariant : (h : edgesSoFar ≠ []) → ∀ (a : fin_of_edgeList edgesSoFar h), ∀ (p : (SimpleGraph_of_edgeList edgesSoFar h).Walk a a), ¬p.IsCycle)
  (h_invariant : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => G.IsAcyclic) { Adj := fun a b => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := sorry, loopless := sorry})
  -- (h_invariant₂ : (fun (H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => ∀ a b, H.Reachable a b ↔ connected_component_of_unionFind_of_id uF a.val sorry = connected_component_of_unionFind_of_id uF b.val sorry) { Adj := fun a b => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := sorry, loopless := sorry})
  : (fun (H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => H.IsAcyclic) { Adj := fun a b => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm, loopless := h_loopless } := by
  simp
  -- revert h_nodeList
  induction
    edgeList,
    uF,
    edgesSoFar,
    h_matching_edge
  using kruskal_helper.induct with -- generalizing h_nodeList
  | case1 uF edgesSoFar h_matching_edge =>
    -- intro h_nodeList
    -- simp [nodeList_of_edgeList, nodeList_of_edgeList_helper, h_nonempty] at h_nodeList
    simp [kruskal_helper]
    exact h_invariant
    -- cases edgesSoFar with
    -- | nil =>
    --   simp
    --   simp [SimpleGraph.IsAcyclic]
    --   intro v p
    --   simp [SimpleGraph.Walk.isCycle_def]
    --   intro h_trail h_not_nil
    --   cases p with
    --   | nil =>
    --     simp at h_not_nil
    --   | cons h_adj h_walk =>
    --     rename_i u
    --     simp at h_adj
    -- | cons e edgesSoFar =>
    --   simp [SimpleGraph_of_edgeList] at h_invariant
    --   simp [SimpleGraph.IsAcyclic]
    --   intro v p
    --   have h_isLt := v.isLt
    --   simp [] at h_isLt
    --   sorry
  | case2 uF edgesSoFar e es h_matching_edge' h_ex_1 x h_ex_2 y h_matching_edge =>
    rename_i h_eq ih
    simp [kruskal_helper]
    set x := connected_component_of_unionFind_of_id uF e.node1 _ with h_x
    set y := connected_component_of_unionFind_of_id uF e.node2 _ with h_y
    by_cases h_eq : x = y
    · simp [← h_x, ← h_y, h_eq]
      apply ih
      exact h_invariant
    · simp [← h_x, ← h_y, h_eq]
    cases edgesSoFar with
    | nil =>
      simp
      simp [SimpleGraph.IsAcyclic]
      intro v p
      simp [SimpleGraph.Walk.isCycle_def]
      intro h_trail h_not_nil
      cases p with
      | nil =>
        simp at h_not_nil
      | cons h_adj h_walk =>
        rename_i u
        simp at h_adj
    | cons e edgesSoFar =>
      simp [SimpleGraph_of_edgeList] at h_invariant
      simp [SimpleGraph.IsAcyclic]
      intro v p
      have h_isLt := v.isLt
      simp [] at h_isLt
    sorry
  | case3 uF edgesSoFar e es h_matching_edge h_ex_1 x h_ex_2 y h_matching_edge' h_ne h_ex_uFLx =>
    rename_i h_ex_uFLy update_uF ih
    sorry

theorem SimpleGraph_of_kruskal_IsAcyclic (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h).IsAcyclic := by
  simp [SimpleGraph_of_kruskal, SimpleGraph_of_n_of_edgeList, SimpleGraph_of_edgeList, kruskal_of_edgeList, kruskal]--, SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  set edgeListSorted := edgeList.mergeSort fun a b => decide (a ≤ b) with h_edgeListSorted
  set nodeList := nodeList_of_edgeList edgeList with h_nodeList
  set uF := init_unionFind (nodeList_of_edgeList edgeList) (nodeList_of_edgeList_nodup edgeList) with h_uF
  set edgesSoFar : List edge := [] with h_edgesSoFar
  simp [h_edgesSoFar] at h
  have h_matching_edge : matching_edge _ _ := kruskal._proof_1 edgeList (nodeList_of_edgeList edgeList) (matching_edge_for_nodeList_of_edgeList edgeList)
  have h_nodup := nodeList_of_edgeList_nodup edgeList
  simp [← h_edgeListSorted, ← h_uF, ← h_edgesSoFar]
  -- have h_invariant : (h : edgesSoFar ≠ []) → ∀ (a b : fin_of_edgeList edgesSoFar h), (SimpleGraph_of_edgeList edgesSoFar h).Reachable a b := by
  --   simp [edgesSoFar]
  -- have h_loopless : Std.Irrefl fun (a b : Fin _) => ∃ e ∈ kruskal_helper edgeListSorted nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by sorry
  exact kruskal_helper_IsAcyclic sorry sorry sorry (h_G := rfl) (h_loopless := sorry) (h_symm := sorry) (G := { Adj := fun a b => ∃ e ∈ kruskal_helper edgeListSorted nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := sorry, loopless := sorry })

theorem SimpleGraph_of_kruskal_IsEqReachable (edgeList : List edge) (h : edgeList ≠ []) : ∀ (x y), (SimpleGraph_of_edgeList edgeList h).Reachable x y ↔ (SimpleGraph_of_kruskal edgeList h).Reachable x y := by sorry

theorem SimpleGraph_of_kruskal_IsSpanningTree (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph.IsSpanningTree (SimpleGraph_of_kruskal edgeList h) (SimpleGraph_of_edgeList edgeList h) := by sorry

def cost_of_edgeList : List edge → Nat
  | [] => 0
  | e :: edgeList => e.cost + cost_of_edgeList edgeList

def minimalSpanninTree_of_edgeList (edgeList : List edge) (h₁ : edgeList ≠ []) (G := SimpleGraph_of_edgeList edgeList h₁) (minEdgeList : List edge) (h₂ : minEdgeList ≠ []) (h₃ : SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList minEdgeList h₂)) (h₄ : ∀ x ∈ minEdgeList, x ∈ edgeList) : Prop := ∀ (el : List edge), (h₅ : el ≠ []) → (h₆ : ∀ x ∈ el, x ∈ edgeList) → SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList el h₅) → (cost_of_edgeList el) ≥ (cost_of_edgeList minEdgeList)

theorem kruskal_minimalSpanninTree_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : minimalSpanninTree_of_edgeList edgeList h (SimpleGraph_of_edgeList edgeList h₁) (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) := by sorry
