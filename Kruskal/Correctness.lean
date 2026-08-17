-- import Mathlib
import Kruskal.Basic
-- import Kruskal.Lists
import Kruskal.Tantow
import Kruskal.SimpleGraph

set_option maxHeartbeats 100000000

-- set_option pp.all true

namespace Kruskal


variable {m n : Nat} {α β : Type}

open SimpleGraph

def SimpleGraph.IsSpanningTree (G H : SimpleGraph α) : Prop := H ≤ G ∧ H.IsAcyclic ∧ (∀ (x y : α), G.Reachable x y ↔ H.Reachable x y)

theorem spanninTree_connected_iff_connected (G H : SimpleGraph α) (h : SimpleGraph.IsSpanningTree G H) : G.Connected ↔ H.Connected := by
  simp [SimpleGraph.connected_iff_exists_forall_reachable]
  simp [SimpleGraph.IsSpanningTree] at h
  rcases h with ⟨_, _, h⟩
  simp [h]







def cost_of_edgeList : List edge → Nat
  | [] => 0
  | e :: edgeList => e.cost + cost_of_edgeList edgeList

theorem nodeList_of_edgeList_helper_nonempty {nodeList : List node} (edgeList : List edge) : nodeList ≠ [] → nodeList_of_edgeList_helper edgeList nodeList ≠ [] := by
  intro h'
  induction edgeList generalizing nodeList with
  | nil =>
    simp [nodeList_of_edgeList_helper, h']
  | cons e edgeList ih =>
    simp [nodeList_of_edgeList_helper]
    grind

theorem nodeList_of_edgeList_nonempty (edgeList : List edge) (h : edgeList ≠ []) : nodeList_of_edgeList edgeList ≠ [] := by
  cases edgeList with
  | nil =>
    simp at h
  | cons e edgeList =>
    simp [nodeList_of_edgeList, nodeList_of_edgeList_helper]
    by_cases h_eq : e.node1 = e.node2
    · simp [h_eq, nodeList_of_edgeList_helper_nonempty]
    · simp [nodeList_of_edgeList_helper_nonempty]

def nodeList_of_edgeList_max (edgeList : List edge) (h : edgeList ≠ []) : node := (nodeList_of_edgeList edgeList).max (nodeList_of_edgeList_nonempty edgeList h)

def fin_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : Type := Fin (nodeList_of_edgeList_max edgeList h).id.succ

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

theorem connected_component_of_init_unionFind_of_id_eq_id {nodeList : List node} {h_nodup : nodeList.Nodup} {id : Nat} {h : ∃ x ∈ nodeList, x.id = id} : connected_component_of_unionFind_of_id (init_unionFind nodeList h_nodup) id h = id := by
  simp [init_unionFind]
  by_cases h_nonempty : nodeList ≠ []
  · simp [h_nonempty]
    simp [connected_component_of_unionFind_of_id]
    have h_ex : ∃ y ∈ (init_unionFind.linkList nodeList (by simp [h_nonempty])), (fun x => x.nodeId = id) y := by
      let uF := init_unionFind nodeList h_nodup
      have h_linkList_eq : uF.linkList = (init_unionFind.linkList nodeList (by simp [h_nonempty])) := by
        simp [uF, init_unionFind, h_nonempty]
      simp [← h_linkList_eq]
      rcases h with ⟨z, h_z_in, h_z_id_eq⟩
      have h_matching_nodeId := uF.matching_nodeId z h_z_in
      simp [ExistsUnique, h_z_id_eq] at h_matching_nodeId
      rcases h_matching_nodeId with ⟨y, h_y, h_unique⟩
      refine ⟨y, ?_⟩
      simp [h_y]
    set x := List.choose (fun x => x.nodeId = id) (init_unionFind.linkList nodeList (by simp [h_nonempty])) h_ex with h_x
    simp [← h_x]
    have h_x_in := List.choose_mem (fun x => x.nodeId = id) (init_unionFind.linkList nodeList (by simp [h_nonempty])) h_ex
    simp [← h_x] at h_x_in
    simp [init_unionFind.linkList] at h_x_in
    have h_x_prop := List.choose_property (fun x => x.nodeId = id) (init_unionFind.linkList nodeList (by simp [h_nonempty])) h_ex
    simp [← h_x] at h_x_prop
    have h_x_selfcon := init_unionFind.linkList.helper_all_self_connected nodeList nodeList (by simp [h_nonempty]) x h_x_in
    rw [connected_component_of_unionFind_of_unionFindLink]
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
    simp [update_edgesSoFar]
    split_ifs
    · exact h_nonempty
    · simp

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
      exact kruskal_helper_nonempty (by simp [update_edgesSoFar, ne_of_lt e.nodesLt])
    | cons f l₁ =>
      simp [kruskal_helper]
      simp [connected_component_of_init_unionFind_of_id_eq_id]
      exact kruskal_helper_nonempty (by simp [update_edgesSoFar, ne_of_lt f.nodesLt])

def SimpleGraph_of_kruskal (edgeList : List edge) (h : edgeList ≠ []) := SimpleGraph_of_n_of_edgeList (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) _).id.succ (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) (rfl)








def minimalSpanninTree_of_edgeList {minEdgeList : List edge} {edgeList : List edge} {n : Nat} (h_nonempty₁ : minEdgeList ≠ []) (h_nonempty₂ : edgeList ≠ []) (h_eq₁ : n = (nodeList_of_edgeList_max minEdgeList h_nonempty₁).id.succ) (h_eq₂ : n = (nodeList_of_edgeList_max edgeList h_nonempty₂).id.succ) : Prop := SimpleGraph.IsSpanningTree (SimpleGraph_of_n_of_edgeList n minEdgeList h_nonempty₁ h_eq₁) (SimpleGraph_of_n_of_edgeList n edgeList h_nonempty₂ h_eq₂) → ∀ (otherEdgeList : List edge), (h_nonempty₃ : otherEdgeList ≠ []) → (h_eq₃ : n = (nodeList_of_edgeList_max otherEdgeList h_nonempty₃).id.succ) → SimpleGraph.IsSpanningTree (SimpleGraph_of_n_of_edgeList n otherEdgeList h_nonempty₃ h_eq₃) (SimpleGraph_of_n_of_edgeList n edgeList h_nonempty₂ h_eq₂) → (cost_of_edgeList minEdgeList) ≤ (cost_of_edgeList otherEdgeList)








theorem kruskal_helper_sublist {edgeList : List edge} {nodeList : List node} {uF : unionFind nodeList} {edgesSoFar : List edge} {h_matching_edge : matching_edge edgeList nodeList} {h_nodup : nodeList.Nodup} : ∀ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e ∈ edgeList ∨ e ∈ edgesSoFar := by
  fun_induction kruskal_helper with
  | case1 uF edgesSoFar h_matching_edge =>
    simp
  | case2 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_self_con1 h_self_con2 updated_uF updated_edgesSoFar ih =>
    simp [or_assoc]
    intro f h_f_in
    have ih := ih f h_f_in
    simp only [updated_edgesSoFar, update_edgesSoFar] at ih
    by_cases h_eq : x = y
    · simp [h_eq] at ih
      right
      exact ih
    · simp [h_eq] at ih
      grind

theorem kruskal_sublist {edgeList : List edge} {nodeList : List node} {h_matching_edge : matching_edge edgeList nodeList} {h_nodup : nodeList.Nodup} : ∀ e ∈ kruskal edgeList nodeList h_matching_edge h_nodup, e ∈ edgeList := by
  simp [kruskal]
  intro e h_e_in
  have h := kruskal_helper_sublist e h_e_in
  simp at h
  exact h

theorem kruskal_helper.edgesSoFar_append
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
  | case2 uF edgesSoFar e es h_matching_edge h_ex1 x h_ex2 y h_matching_edge' h_self_con1 h_self_con2 updated_uF updated_edgesSoFar =>
    rename_i edgesSoFar' ih -- strange aber funktioniert so
    intro h_edgesSoFar'
    simp [updated_edgesSoFar, h_edgesSoFar'] at ih
    simp [kruskal_helper]
    have ih := ih (edgesSoFar₁ := update_edgesSoFar edgesSoFar₁ e x y )
    by_cases h_eq : x = y
    · simp [x, y] at h_eq
      simp [update_edgesSoFar, h_eq]
      simp [update_edgesSoFar] at ih
      grind
    · simp [x, y] at h_eq
      simp [update_edgesSoFar, h_eq]
      simp [update_edgesSoFar] at ih
      grind

-- unused
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
      simp [update_edgesSoFar]
      exact ih
    · set uF' := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (by grind)) (connected_component_of_unionFind_of_id uF e.node2 (by grind)) _ _
      simp [matching_edge] at h_matching_edge
      have ih := ih (uF := uF') (edgesSoFar := e :: edgesSoFar) (h_matching_edge₁ := h_matching_edge₁.right) (h_matching_edge := by simp [matching_edge]; exact h_matching_edge.right)
      rcases ih with ⟨uF'', ih⟩
      simp [update_edgesSoFar, h_eq, ih]
      have h_nil_append : [e] = [] ++ [e] := by
        simp
      rw [h_nil_append]
      simp only [kruskal_helper.edgesSoFar_append]
      simp
      refine ⟨uF'', rfl⟩

-- unused
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
      exact kruskal_helper.edgesSoFar_append
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
    have h_goal : ∀ (uFL : unionFindLink nodeList) (h_in : uFL ∈ uF.linkList), connected_component_of_unionFind_of_unionFindLink uF uFL h_in = z.id → uFL.nodeId = z.id := by
      intro uFL h_uFL_in
      induction uFL, h_uFL_in using connected_component_of_unionFind_of_unionFindLink.induct with
      | case1 uFL h_uFL_in h_uFL_self_con =>
        rw [connected_component_of_unionFind_of_unionFindLink]
        simp [h_uFL_self_con]
      | case2 uFL h_uFL_in h_uFL_not_self_con uFLy h_uFLy_in h_rank_lt ih =>
        rw [connected_component_of_unionFind_of_unionFindLink]
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
    rw [connected_component_of_unionFind_of_unionFindLink]
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
    by_cases h_eq : x = y
    · simp [update_edgesSoFar, h_eq]
      apply ih
      · exact h_edgeList_not_con.right
      · simp [update_unionFind]
        exact h_uF_not_con
    · simp [update_edgesSoFar, h_eq]
      rw [h]
      simp only [kruskal_helper.edgesSoFar_append]
      simp
      simp only [kruskal_helper.edgesSoFar_append] at ih
      apply ih
      · exact h_edgeList_not_con.right
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
        by_cases h_rank_lt' : uFLy.rank < uFLx.rank
        · simp [h_rank_lt']
          intro uFL h_uFL_in
          rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
          · rcases List.mem_or_eq_of_mem_set h_uFL_in with ⟨h_uFL_in⟩ | ⟨h_uFL_eq⟩
            · exact h_uF_not_con uFL h_uFL_in
            · simp [h_uFL_eq, h_uFLx_prop, h_uFLy_prop, h_x_ne_z, h_y_ne_z]
          · simp [h_uFL_eq, h_uFLx_prop, h_x_ne_z]
        · simp [h_rank_lt']
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
    set uF := init_unionFind (nodeList_of_edgeList_helper edgeList []) h_nodup2
    have h_edgeList_not_con : ∀ e ∈ l₁, ¬(e.node1 = x.id ∨ e.node2 = x.id) := by
      exact h_l₁_not_con_x
    have h_uF_not_con : ∀ uFL ∈ uF.linkList, uFL.ccId = x.id ↔ uFL.nodeId = x.id := by
      have h_nonempty : nodeList_of_edgeList_helper edgeList [] ≠ [] := by
        intro h_contra
        simp [h_contra] at h_x_in_nodeList_of_edgeList
      simp [uF, init_unionFind, h_nonempty, init_unionFind.linkList]
      have h := init_unionFind.linkList.helper_all_self_connected (nodeList_of_edgeList_helper edgeList []) (nodeList_of_edgeList_helper edgeList []) (by simp [h_nonempty])
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
    simp [update_edgesSoFar, h_ne]
    have h : f :: k_l₁ = [] ++ (f :: k_l₁) := by
      simp
    rw [h]
    set uF'' := update_unionFind uF' (connected_component_of_unionFind_of_id uF' f.node1 _) (connected_component_of_unionFind_of_id uF' f.node2 _) _ _
    rw [kruskal_helper.edgesSoFar_append (edgeList := l₂) (nodeList := nodeList_of_edgeList_helper edgeList []) (uF := uF'')]
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

theorem SimpleGraph_of_kruskal.IsSubgraph (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h) ≤ (SimpleGraph_of_n_of_edgeList (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) _).id.succ edgeList h (nodeList_of_edgeList_max_eq edgeList h)) := by
  simp [LE.le]
  simp [SimpleGraph_of_kruskal, SimpleGraph_of_n_of_edgeList, SimpleGraph_of_edgeList]
  intro u v e h_e_in h_adj
  refine ⟨e, kruskal_sublist e h_e_in, h_adj⟩









-- unused 2
theorem connected_component_of_unionFind_of_id_of_self
  {nodeList : List node}
  {uF : unionFind nodeList}
  {id : Nat}
  {h : ∃ x ∈ nodeList, x.id = id}
  {h' : ∃ x ∈ nodeList, x.id = connected_component_of_unionFind_of_id uF id h}
  : connected_component_of_unionFind_of_id uF (connected_component_of_unionFind_of_id uF id h) h' = connected_component_of_unionFind_of_id uF id h := by
  set cc := connected_component_of_unionFind_of_id uF id h with ← h_cc
  simp [h_cc]
  have h_ex := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF id h
  simp [h_cc] at h_ex
  rcases h_ex with ⟨uFLcc, h_uFLcc_self_con⟩
  set uFLcc' := List.choose (fun x => x.nodeId = cc) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF cc (h_cc ▸ h') : ∃ x ∈ uF.linkList, x.nodeId = cc) with h_uFLcc'
  have h_uFLcc'_prop := List.choose_property (fun x => x.nodeId = cc) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF cc (h_cc ▸ h') : ∃ x ∈ uF.linkList, x.nodeId = cc)
  have h_uFLcc'_mem := List.choose_mem (fun x => x.nodeId = cc) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF cc (h_cc ▸ h') : ∃ x ∈ uF.linkList, x.nodeId = cc)
  simp [connected_component_of_unionFind_of_id]
  cases h' with
  | intro x h_x =>
  cases x
  simp at h_x
  simp [h_x.right] at h_x
  have h_matching_nodeId := uF.matching_nodeId ⟨cc⟩ h_x
  simp [ExistsUnique] at h_matching_nodeId
  rcases h_matching_nodeId with ⟨uFLcc'', h_prop, h_unique⟩
  simp [← h_uFLcc', h_unique uFLcc' h_uFLcc'_mem h_uFLcc'_prop.symm]
  simp [← h_unique uFLcc h_uFLcc_self_con.left h_uFLcc_self_con.right.left.symm]
  rw [connected_component_of_unionFind_of_unionFindLink]
  simp [h_uFLcc_self_con]

theorem node_of_uFL
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  : ∃ x ∈ nodeList, x.id = uFL.nodeId := by
  by_cases h_goal : ∃ x ∈ nodeList, x.id = uFL.nodeId
  · exact h_goal
  · simp at h_goal
    have h_len := uF.matching_length
    rcases mem_split h_in with ⟨l₁, l₂, h_split⟩
    have h_matching_nodeId := uF.matching_nodeId
    simp [h_split] at h_matching_nodeId
    have h_matching_nodeId : ∀ x ∈ nodeList, ∃! y, (y ∈ l₁ ∨ y ∈ l₂) ∧ x.id = y.nodeId := by
      intro x h_x_in
      have h_matching_nodeId := h_matching_nodeId x h_x_in
      have h_goal := h_goal x h_x_in
      simp [ExistsUnique]
      simp [ExistsUnique] at h_matching_nodeId
      rcases h_matching_nodeId with ⟨y, h⟩
      have h_y_ne_uFL : y ≠ uFL := by
        intro h_eq
        simp [← h_eq] at h_goal
        simp [h_goal] at h
      simp [h_y_ne_uFL] at h
      refine ⟨y, ?_⟩
      constructor
      · simp [h]
      · intro z h_z_in
        have h' := h.right z
        rcases h_z_in with h_z_in | h_z_in
        · simp [h_z_in] at h'
          exact h'
        · simp [h_z_in] at h'
          exact h'
    have h_len' : uF.linkList.length = (l₁ ++ l₂).length + 1 := by
      simp [h_split.left]
      omega
    simp [h_len'] at h_len
    let f : node → unionFindLink nodeList := fun x_1 =>
      if h_x_1_in : x_1 ∈ nodeList
        then
          have h_ex := h_matching_nodeId x_1 h_x_1_in
          let uFL_1 : unionFindLink nodeList := by
            simp [ExistsUnique] at h_ex
            -- rcases h_ex with ⟨uFL_1, h⟩
            exact Classical.choose h_ex
          uFL_1
        else
          uFL
    have h_f_id : ∀ a ∈ nodeList, (f a).nodeId = a.id := by
      grind
    have h_injectiv : ∀ a ∈ nodeList, ∀ b ∈ nodeList, f a = f b → a = b := by
      intro a h_a_in b h_b_in h_f_eq
      have h_id_eq : a.id = b.id := by
        simp [← h_f_id a h_a_in, h_f_eq, h_f_id b h_b_in]
      cases a
      simp at h_id_eq
      simp [h_id_eq]
    have h_image : ∀ a ∈ nodeList, f a ∈ l₁ ++ l₂ := by
      grind
    have h := lenght_ge_of_injectiv h_nodup h_injectiv h_image
    simp [h_len] at h

-- unused
theorem connected_component_of_unionFind_of_unionFindLink_of_self
  {nodeList : List node}
  {uF : unionFind nodeList}
  {a b : unionFindLink nodeList}
  {h_a_in : a ∈ uF.linkList}
  {h_b_in : b ∈ uF.linkList}
  (h_nodup : nodeList.Nodup)
  : connected_component_of_unionFind_of_unionFindLink uF a h_a_in = connected_component_of_unionFind_of_unionFindLink uF b h_b_in →
    connected_component_of_unionFind_of_id uF a.nodeId (node_of_uFL h_a_in h_nodup) =
    connected_component_of_unionFind_of_id uF b.nodeId (node_of_uFL h_b_in h_nodup) := by
  have h_unique_nodeId : ∀ uFL_1 ∈ uF.linkList, ∀ uFL_2 ∈ uF.linkList, uFL_1.nodeId = uFL_2.nodeId → uFL_1 = uFL_2 := by
    intro uFL_1 h_uFL_1_in uFL_2 h_uFL_2_in h_nodeId_eq
    have h_ex_node := node_of_uFL h_uFL_1_in h_nodup
    rcases h_ex_node with ⟨x, h_x_in, h_x_id⟩
    have h := uF.matching_nodeId x h_x_in
    simp [ExistsUnique] at h
    rcases h with ⟨uFL, h_uFL, h_unique⟩
    have h_eq_1 := h_unique uFL_1 h_uFL_1_in h_x_id
    have h_eq_2 := h_unique uFL_2 h_uFL_2_in (by simp [h_x_id, h_nodeId_eq])
    simp [h_eq_1, h_eq_2]
  rw [connected_component_of_unionFind_of_unionFindLink]
  rw [connected_component_of_unionFind_of_unionFindLink]
  simp [connected_component_of_unionFind_of_id]
  have h_a'_prop := List.choose_property (fun x => x.nodeId = a.nodeId) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF a.nodeId (node_of_uFL h_a_in h_nodup) : ∃ x ∈ uF.linkList, x.nodeId = a.nodeId)
  have h_a'_in := List.choose_mem (fun x => x.nodeId = a.nodeId) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF a.nodeId (node_of_uFL h_a_in h_nodup) : ∃ x ∈ uF.linkList, x.nodeId = a.nodeId)
  set a' := List.choose (fun x => x.nodeId = a.nodeId) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF a.nodeId (node_of_uFL h_a_in h_nodup) : ∃ x ∈ uF.linkList, x.nodeId = a.nodeId) with ← h_a'
  have h_b'_prop := List.choose_property (fun x => x.nodeId = b.nodeId) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF b.nodeId (node_of_uFL h_b_in h_nodup) : ∃ x ∈ uF.linkList, x.nodeId = b.nodeId)
  have h_b'_in := List.choose_mem (fun x => x.nodeId = b.nodeId) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF b.nodeId (node_of_uFL h_b_in h_nodup) : ∃ x ∈ uF.linkList, x.nodeId = b.nodeId)
  set b' := List.choose (fun x => x.nodeId = b.nodeId) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF b.nodeId (node_of_uFL h_b_in h_nodup) : ∃ x ∈ uF.linkList, x.nodeId = b.nodeId) with ← h_b'
  simp [h_a', h_b', h_unique_nodeId a' h_a'_in a h_a_in (by simp [h_a'_prop]), h_unique_nodeId b' h_b'_in b h_b_in (by simp [h_b'_prop])]
  split_ifs with h_a_self_con h_b_self_con
  · intro h
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [← h_a_self_con, h_b_self_con, h]
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [h_b_self_con]
  · intro h
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [← h_a_self_con]
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [h_b_self_con, h]
  · intro h
    rw [connected_component_of_unionFind_of_unionFindLink]
    rw [connected_component_of_unionFind_of_unionFindLink]
    rename_i h_b_self_con
    simp [h_a_self_con, h_b_self_con, h]
  · intro h
    rw [connected_component_of_unionFind_of_unionFindLink]
    rw [connected_component_of_unionFind_of_unionFindLink]
    rename_i h_b_self_con
    simp [h_a_self_con, h_b_self_con, h]

theorem uFL_choose_self
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  : List.choose (fun x => x.nodeId = uFL.nodeId) uF.linkList (by grind) = uFL := by
  rcases (node_of_uFL h_in h_nodup) with ⟨x, h_x_in, h_x⟩
  rcases (uF.matching_nodeId x h_x_in) with ⟨uFL', h_uFL'_in, h_unique⟩
  have h_eq1 := h_unique uFL (by grind)
  have h_eq2:= h_unique (List.choose (fun x => x.nodeId = uFL.nodeId) uF.linkList (by grind)) ?_
  · simp [h_eq2, ← h_eq1]
  · simp [List.choose_mem, h_uFL'_in.right, ← h_eq1]
    have h_prop := List.choose_property (fun x => x.nodeId = uFL.nodeId) uF.linkList (by grind)
    simp [h_prop]

theorem nodeId_lt_max
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  (h_nonempty : nodeList ≠ [])
  : uFL.nodeId < (nodeList.max h_nonempty).id.succ := by
  rcases (node_of_uFL h_in h_nodup) with ⟨x, h_x_in, h_x⟩
  simp [← h_x]
  exact List.le_max_of_mem h_x_in

theorem connected_component_of_unionFind_of_id_lt_max
  {nodeList : List node}
  {uF : unionFind nodeList}
  {x : node}
  (h_x_in : x ∈ nodeList)
  (h_nodup : nodeList.Nodup)
  (h_nonempty : nodeList ≠ [])
  : connected_component_of_unionFind_of_id uF x.id ⟨x, h_x_in, rfl⟩ < (nodeList.max h_nonempty).id.succ := by
  have h := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF x.id ⟨x, h_x_in, rfl⟩
  rcases h with ⟨uFL, h_uFL_in, h_uFL⟩
  have h := nodeId_lt_max h_uFL_in h_nodup h_nonempty
  simp [h_uFL] at h
  simp [h]

def parent
  {nodeList : List node}
  {uF : unionFind nodeList}
  (uFL : unionFindLink nodeList)
  (h_in : uFL ∈ uF.linkList)
  : unionFindLink nodeList
  := List.choose (fun a => a.nodeId = uFL.ccId) uF.linkList (by rcases (uF.matching_ccId uFL h_in) with ⟨x, h, _⟩; rcases (uF.matching_nodeId x h.left) with ⟨uFL', h', _⟩; simp [← h.right]; refine ⟨uFL', by simp [h']⟩)

theorem parent_in
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : parent uFL h_in ∈ uF.linkList := by
  simp [parent, List.choose_mem]

theorem con_parent
  {nodeList : List node}
  {uF : unionFind nodeList}
  (uFL : unionFindLink nodeList)
  (h_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  : connected_component_of_unionFind_of_unionFindLink uF uFL h_in = connected_component_of_unionFind_of_unionFindLink uF (parent uFL h_in) (parent_in h_in) := by
  by_cases h_self_con : uFL.ccId = uFL.nodeId
  · have h := uFL_choose_self h_in h_nodup
    simp [h_self_con, parent, h]
  · nth_rewrite 1 [connected_component_of_unionFind_of_unionFindLink]
    simp [h_self_con, parent]

theorem parent_nodeId
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : (parent uFL h_in).nodeId = uFL.ccId := by
  have h := List.choose_property (fun a => a.nodeId = uFL.ccId) uF.linkList (by rcases (uF.matching_ccId uFL h_in) with ⟨x, h, _⟩; rcases (uF.matching_nodeId x h.left) with ⟨uFL', h', _⟩; simp [← h.right]; refine ⟨uFL', by simp [h']⟩)
  simp [parent, h]

-- unused 2
def parent_path
  {nodeList : List node}
  (uF : unionFind nodeList)
  (p : List (unionFindLink nodeList))
  (h_in : ∀ a ∈ p, a ∈ uF.linkList)
  : Prop :=
  match p with
  | [] => true
  | a :: [] => true
  | a :: b :: p' => b = parent (uF := uF) a (by grind) ∧ parent_path uF (b :: p') (by grind)

-- unused
theorem eq_cc
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uF' : unionFind nodeList}
  {a b : unionFindLink nodeList}
  {h_a_in : a ∈ uF.linkList}
  {h_b_in : b ∈ uF'.linkList}
  (h_eq : a = b)
  (p : List (unionFindLink nodeList))
  (h_path_in : ∀ a ∈ p, a ∈ uF.linkList)
  (h_path_in' : ∀ a ∈ p, a ∈ uF'.linkList)
  (h_path : parent_path uF p h_path_in)
  (h_path' : parent_path uF' p h_path_in')
  (h_path_start : ∃ p', p = a :: p')
  (h_path_end : ∃ c ∈ p, c.nodeId = c.ccId)
  : connected_component_of_unionFind_of_unionFindLink uF a h_a_in = connected_component_of_unionFind_of_unionFindLink uF' b h_b_in := by
  induction a, h_a_in using connected_component_of_unionFind_of_unionFindLink.induct generalizing b p with
  | case1 x h_x_in h_x_self_con =>
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [h_x_self_con, ← h_eq]
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [h_x_self_con]
  | case2 x h_x_in h_x_not_self_con y h_y_in h_rank_lt =>
    rename_i ih
    simp [← h_eq]
    rw [connected_component_of_unionFind_of_unionFindLink]
    rw [connected_component_of_unionFind_of_unionFindLink]
    simp [h_x_not_self_con]
    have h_y_eq_parent : y = parent x h_x_in := by
      simp [y, parent]
    rcases h_path_start with ⟨p', h_path_start⟩
    cases p' with
    | nil =>
      simp [h_path_start] at h_path_end
      simp [h_path_end] at h_x_not_self_con
    | cons z p' =>
      have h_z_eq_y : z = y := by
        simp [h_path_start, parent_path] at h_path
        simp [h_path, h_y_eq_parent]
      simp [h_z_eq_y] at h_path_start
      have h_y_eq_parent' : y = parent b h_b_in := by
        simp [h_path_start, parent_path, h_eq] at h_path'
        simp [← h_path'.left]
      have h_y : List.choose (fun y => y.nodeId = x.ccId) uF.linkList (connected_component_of_unionFind_of_unionFindLink._unary._proof_1 uF x h_x_in : ∃ y ∈ uF.linkList, y.nodeId = x.ccId) = y := by
        simp [y]
      simp [parent, ← h_eq] at h_y_eq_parent'
      simp [h_y, ← h_y_eq_parent']
      apply ih (by rfl) (y :: p')
      · simp [h_path_start, parent_path] at h_path
        simp [h_path.right]
      · simp [h_path_start, parent_path] at h_path'
        simp [h_path'.right]
      · refine ⟨p', rfl⟩
      · simp [h_path_start, ne_comm.mp h_x_not_self_con] at h_path_end
        simp [h_path_end]
      · simp [h_path_start] at h_path_in
        simp
        exact h_path_in.right
      · simp [h_path_start] at h_path_in'
        simp
        exact h_path_in'.right

def get_parent_path
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : List (unionFindLink nodeList) :=
  if h_self_con : uFL.nodeId = uFL.ccId
    then
      (uFL :: [])
    else
      (uFL :: (get_parent_path (uFL := parent uFL h_in) (by simp [parent, List.choose_mem]) (uF := uF)))
termination_by nodeList.length - uFL.rank
  decreasing_by
  have h_lt := uFL.rank.isLt
  have h_increase : uFL.rank.val < (parent uFL h_in).rank.val := by
    have h := uF.matching_rank uFL h_in
    simp [h_self_con] at h
    simp [parent, h]
  exact Nat.sub_lt_sub_left h_lt h_increase

theorem get_parent_path_in
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : ∀ a ∈ (get_parent_path h_in), a ∈ uF.linkList := by
  fun_induction get_parent_path with
  | case1 uFL h_in _ =>
    simp [h_in]
  | case2 uFL h_in _ ih =>
    simp [h_in]
    exact ih

-- unused 2
theorem get_parent_path_is_parent_path
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : parent_path uF (get_parent_path h_in) (get_parent_path_in h_in) := by
  fun_induction get_parent_path with
  | case1 uFL h_in h_self_con =>
    unfold get_parent_path
    simp [h_self_con, parent_path]
  | case2 uFL h_in h_not_self_con ih =>
    unfold get_parent_path
    simp [h_not_self_con]
    unfold get_parent_path
    unfold get_parent_path at ih
    split_ifs with h_self_con
    · simp [parent_path]
    · simp [parent_path]
      simp [h_self_con] at ih
      exact ih

-- unused 2
theorem get_parent_path_start
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : ∃ p', (get_parent_path h_in) = uFL :: p' := by
  unfold get_parent_path
  split_ifs
  · simp
  · simp

theorem get_parent_path_end
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : ∃ a ∈ (get_parent_path h_in), a.nodeId = a.ccId := by
  fun_induction get_parent_path with
  | case1 uFL h_in h_self_con =>
    simp [h_self_con]
  | case2 uFL h_in h_not_self_con ih =>
    simp [h_not_self_con]
    exact ih

-- unused
def walk_of_subgraph [DecidableEq α] (G H : SimpleGraph α) (h_sub : G ≤ H) (a b : α) (p : G.Walk a b) : H.Walk a b :=
  match h_p : p with
  | .nil =>
    SimpleGraph.Walk.nil
  | .cons h_adj p' =>
    let c := p'.start
    have h_adj' : H.Adj a c := by
      simp [LE.le] at h_sub
      apply h_sub
      exact h_adj
    SimpleGraph.Walk.cons h_adj' (walk_of_subgraph G H h_sub c b p')
termination_by p.length
  decreasing_by
  simp

-- unused 2
theorem not_reachable_of_neighbor_not_reachable (G : SimpleGraph α) (a b c : α) (h_adj : G.Adj a b) (h_not_reachable : ¬G.Reachable a c) : ¬G.Reachable b c := by
  intro h_reachable
  simp [SimpleGraph.Reachable] at h_reachable h_not_reachable
  cases h_reachable with
  | intro p =>
  let q : G.Walk a c := SimpleGraph.Walk.cons h_adj p
  cases h_not_reachable with
  | mk h_not_reachable =>
  have h_contra := h_not_reachable q
  contradiction

-- unused
def walk_of_keine_ahnung
  (G H : SimpleGraph (Fin n))
  (a b : (Fin n))
  (p : G.Walk a b)
  (edgesSoFar : List edge)
  (e : edge)
  (h_G : G.Adj = fun (a b : Fin n) => (e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a) ∨ ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a)
  (h_H : H.Adj = fun (a b : Fin n) => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a)
  {h_lt₁ : e.node1 < n}
  {h_lt₂ : e.node2 < n}
  (h_not_reachable1 : ¬H.Reachable a ⟨e.node1, h_lt₁⟩)
  (h_not_reachable2 : ¬H.Reachable a ⟨e.node2, h_lt₂⟩)
  : H.Walk a b :=
  match h_p : p with
  | .nil =>
    SimpleGraph.Walk.nil
  | .cons h_adj p' =>
    let c := p'.start
    have h_adj' : H.Adj a c := by
      have h_e1_ne_a : e.node1 ≠ a.val := by
        intro h_eq
        simp [h_eq] at h_not_reachable1
      have h_e2_ne_a : e.node2 ≠ a.val := by
        intro h_eq
        simp [h_eq] at h_not_reachable2
      simp [h_G, h_e1_ne_a, h_e2_ne_a] at h_adj
      simp [h_H, h_adj, c]
    have h_not_reachable_c_e1 := not_reachable_of_neighbor_not_reachable H a c ⟨e.node1, h_lt₁⟩ h_adj' h_not_reachable1
    have h_not_reachable_c_e2 := not_reachable_of_neighbor_not_reachable H a c ⟨e.node2, h_lt₂⟩ h_adj' h_not_reachable2
    SimpleGraph.Walk.cons h_adj' (walk_of_keine_ahnung G H c b p' edgesSoFar e h_G h_H h_not_reachable_c_e1 h_not_reachable_c_e2)
termination_by p.length
  decreasing_by
  simp

-- unused
theorem con_parent'
  {nodeList : List node}
  {uF : unionFind nodeList}
  (uFL : unionFindLink nodeList)
  (h_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  : connected_component_of_unionFind_of_id uF uFL.nodeId (node_of_uFL h_in h_nodup) = connected_component_of_unionFind_of_id uF (parent uFL h_in).nodeId (node_of_uFL (parent_in h_in) h_nodup) := by
  have h_eq := uFL_choose_self h_in h_nodup
  simp [connected_component_of_unionFind_of_id, h_eq]
  nth_rewrite 1 [connected_component_of_unionFind_of_unionFindLink]
  split_ifs with h_self_con
  · simp [h_self_con, h_eq, connected_component_of_unionFind_of_unionFindLink, parent]
  · have h_eq := uFL_choose_self (parent_in h_in) h_nodup
    simp [h_eq]
    simp [parent]

theorem connected_component_of_unionFind_of_unionFindLink_of_get_parent_path
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFLa : unionFindLink nodeList}
  (h_uFLa_in : uFLa ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  : ∀ uFLb, (h_uFLb_in : uFLb ∈ get_parent_path h_uFLa_in) → connected_component_of_unionFind_of_unionFindLink uF uFLa h_uFLa_in = connected_component_of_unionFind_of_unionFindLink uF uFLb (get_parent_path_in h_uFLa_in uFLb h_uFLb_in) := by
  intro uFLb h_uFLb_in
  fun_induction get_parent_path with
  | case1 uFLa h_uFLa_in h =>
    simp [get_parent_path, h] at h_uFLb_in
    simp [h_uFLb_in]
  | case2 uFLa h_uFLa_in h ih =>
    rw [get_parent_path] at h_uFLb_in
    simp [h] at h_uFLb_in
    rcases h_uFLb_in with h_eq | h_uFLb_in
    · simp [h_eq]
    · have h := con_parent uFLa h_uFLa_in h_nodup
      simp [h]
      exact ih h_uFLb_in

theorem get_parent_path_nonempty
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : get_parent_path h_in ≠ [] := by
  rw [get_parent_path]
  split_ifs
  · simp
  · simp

theorem get_parent_path_end_eq_last
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  : ∀ a ∈ (get_parent_path h_in), a.nodeId = a.ccId → a = (get_parent_path h_in).getLast (get_parent_path_nonempty h_in) := by
  intro a h_a_in h_self_con
  fun_induction get_parent_path with
  | case1 uFL h_in h =>
    simp [get_parent_path, h] at h_a_in ⊢
    exact h_a_in
  | case2 uFL h_in h ih =>
    rw [get_parent_path] at h_a_in
    simp [h] at h_a_in
    rcases h_a_in with h_eq | h_a_in
    · simp [← h_eq, h_self_con] at h
    · unfold get_parent_path
      simp [h, get_parent_path_nonempty, ih h_a_in]

theorem get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_uFL_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  : ((get_parent_path h_uFL_in).getLast (get_parent_path_nonempty h_uFL_in)).nodeId = connected_component_of_unionFind_of_unionFindLink uF uFL h_uFL_in := by
  rcases (get_parent_path_end h_uFL_in) with ⟨uFLe, h_uFLe_in, h_uFLe⟩
  have h := get_parent_path_end_eq_last h_uFL_in uFLe h_uFLe_in h_uFLe
  have h' := connected_component_of_unionFind_of_unionFindLink_of_get_parent_path h_uFL_in h_nodup uFLe h_uFLe_in
  simp [← h, h', connected_component_of_unionFind_of_unionFindLink, h_uFLe]

-- unused
theorem init_unionFind_reachable_parent
  {nodeList : List node}
  {edgesSoFar : List edge}
  {uF : unionFind nodeList}
  (h_nodup : nodeList.Nodup)
  (h_uF : uF = init_unionFind nodeList h_nodup)
  (uFL : unionFindLink nodeList)
  (h_in : uFL ∈ uF.linkList)
  (h_nonempty : nodeList ≠ [])
  : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => G.Reachable ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨(parent _ h_in).nodeId, nodeId_lt_max (parent_in h_in) h_nodup h_nonempty⟩) { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } := by
  have h_eq := uFL_choose_self h_in h_nodup
  simp [h_uF, init_unionFind, h_nonempty, init_unionFind.linkList] at h_in
  have h_self_con := init_unionFind.linkList.helper_all_self_connected nodeList nodeList (by simp [h_nonempty]) uFL h_in
  simp [parent, ← h_self_con, h_eq]

theorem parent_walk
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL : unionFindLink nodeList}
  (h_uFL_in : uFL ∈ uF.linkList)
  (h_nodup : nodeList.Nodup)
  (h_nonempty : nodeList ≠ [])
  {G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)}
  (h_reachable_parent : ∀ uFL, (h_in : uFL ∈ uF.linkList) → G.Reachable ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨(parent _ h_in).nodeId, nodeId_lt_max (parent_in h_in) h_nodup h_nonempty⟩)
  : Nonempty (G.Walk ⟨uFL.nodeId, nodeId_lt_max h_uFL_in h_nodup h_nonempty⟩ ⟨((get_parent_path h_uFL_in).getLast (get_parent_path_nonempty h_uFL_in)).nodeId, nodeId_lt_max (get_parent_path_in h_uFL_in ((get_parent_path h_uFL_in).getLast (get_parent_path_nonempty h_uFL_in)) (by simp [List.getLast_mem])) h_nodup h_nonempty⟩) := by
  fun_induction get_parent_path with
  | case1 uFL h_in h =>
    simp [get_parent_path, h]
    exact ⟨.nil⟩
  | case2 uFL h_in h ih =>
    simp
    rcases ih with ⟨w⟩
    set p := get_parent_path h_in with ← h_p
    rw [get_parent_path] at h_p
    simp [h] at h_p
    set uFLl := p.getLast (by simp [← h_p]) with ← h_uFLl
    have h_uFLl_in : uFLl ∈ uF.linkList := get_parent_path_in h_in uFLl (by simp [← h_uFLl, p])
    simp [← h_p, get_parent_path_nonempty] at h_uFLl
    simp [h_uFLl] at w
    have h_v := h_reachable_parent uFL h_in
    simp [SimpleGraph.Reachable] at h_v
    rcases h_v with ⟨v⟩
    let u : G.Walk ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨uFLl.nodeId, nodeId_lt_max h_uFLl_in h_nodup h_nonempty⟩ := SimpleGraph.Walk.append v w
    exact ⟨u⟩

theorem update_unionFind_reachable_parent
  {nodeList : List node}
  {e : edge}
  {edgesSoFar : List edge}
  {uF : unionFind nodeList}
  (h_nodup : nodeList.Nodup)
  (h_nonempty : nodeList ≠ [])
  (h_ex1 : ∃ x ∈ nodeList, x.id = e.node1)
  (h_ex2 : ∃ x ∈ nodeList, x.id = e.node2)
  (h_e1_self_con : ∃ uFL ∈ uF.linkList, uFL.nodeId = connected_component_of_unionFind_of_id uF e.node1 h_ex1 ∧ uFL.ccId = connected_component_of_unionFind_of_id uF e.node1 h_ex1)
  (h_e2_self_con : ∃ uFL ∈ uF.linkList, uFL.nodeId = connected_component_of_unionFind_of_id uF e.node2 h_ex2 ∧ uFL.ccId = connected_component_of_unionFind_of_id uF e.node2 h_ex2)
  (h_invariant : ∀ uFL, (h_in : uFL ∈ uF.linkList) → (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => G.Reachable ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨(parent _ h_in).nodeId, nodeId_lt_max (parent_in h_in) h_nodup h_nonempty⟩) { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) })
  : ∀ uFL, (h_in : uFL ∈ (update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2) h_e1_self_con h_e2_self_con).linkList) → (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => G.Reachable ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨(parent _ h_in).nodeId, nodeId_lt_max (parent_in h_in) h_nodup h_nonempty⟩) { Adj := fun a b => ∃ f ∈ update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2), f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } := by
  simp
  set cce1 := connected_component_of_unionFind_of_id uF e.node1 h_ex1 with ← h_cce1
  set cce2 := connected_component_of_unionFind_of_id uF e.node2 h_ex2 with ← h_cce2
  simp [h_cce1, h_cce2]
  by_cases h_cc_eq : cce1 = cce2
  · simp [h_cc_eq, update_edgesSoFar, update_unionFind]
    exact h_invariant
  · simp [h_cc_eq, update_edgesSoFar, update_unionFind]
    split_ifs with h_rank_lt
    · intro uFL h_uFL_in
      set uFLx : unionFindLink nodeList := List.choose (fun a => a.nodeId = cce2 ∧ a.ccId = cce2) uF.linkList h_e2_self_con with ← h_uFLx
      set uFLy : unionFindLink nodeList := List.choose (fun a => a.nodeId = cce1 ∧ a.ccId = cce1) uF.linkList h_e1_self_con with ← h_uFLy
      have h_uFLx_in : uFLx ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = cce2 ∧ a.ccId = cce2) uF.linkList h_e2_self_con
      have h_uFLy_in : uFLy ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = cce1 ∧ a.ccId = cce1) uF.linkList h_e1_self_con
      have h_uFLx_prop : uFLx.nodeId = cce2 ∧ uFLx.ccId = cce2 := List.choose_property (fun a => a.nodeId = cce2 ∧ a.ccId = cce2) uF.linkList h_e2_self_con
      have h_uFLy_prop : uFLy.nodeId = cce1 ∧ uFLy.ccId = cce1 := List.choose_property (fun a => a.nodeId = cce1 ∧ a.ccId = cce1) uF.linkList h_e1_self_con
      have h_idx_uFLx_lt : List.idxOf uFLx uF.linkList < uF.linkList.length := by
        exact List.idxOf_lt_length_of_mem h_uFLx_in
      have h_idx_uFLy_lt : List.idxOf uFLy uF.linkList < uF.linkList.length := by
        exact List.idxOf_lt_length_of_mem h_uFLy_in
      simp [h_uFLx, h_uFLy, h_rank_lt] at h_uFL_in
      set uFLx' : unionFindLink nodeList := { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank } with ← h_uFLx'
      have h_ne : uFLy ≠ uFLx' := by
        grind
      have h_ne_idx : List.idxOf uFLy uF.linkList ≠ List.idxOf uFLx uF.linkList := by
        have : uFLx = uF.linkList[List.idxOf uFLx uF.linkList]'h_idx_uFLx_lt := by
          simp
        grind
      have h_eq_idx := idxOf_eq_idxOf_set h_ne h_ne_idx
      simp [← h_eq_idx, set_eq_self] at h_uFL_in
      rcases (mem_or_eq_of_mem_set h_uFL_in) with h_uFL_in | h_uFL_eq
      · have h_invariant := h_invariant uFL h_uFL_in
        set G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) }
        set H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2), f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } with ← h_H
        simp [update_edgesSoFar, h_cce1, h_cce2, h_cc_eq] at h_H
        simp [h_H]
        have h_subgraph : G ≤ H := by
          simp [LE.le, G, ← h_H]
          intro u v e h_e_in h_e_con
          right
          refine ⟨e, h_e_in, h_e_con⟩
        simp [parent_nodeId]
        simp [parent_nodeId] at h_invariant
        exact SimpleGraph.Reachable.mono h_subgraph h_invariant
      · simp [parent_nodeId, h_uFL_eq, ← h_uFLx', SimpleGraph.Reachable]
        set G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) }
        set H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2), f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } with ← h_H
        simp [update_edgesSoFar, h_cce1, h_cce2, h_cc_eq] at h_H
        simp [h_H]
        have h_subgraph : G ≤ H := by
          simp [LE.le, G, ← h_H]
          intro u v e h_e_in h_e_con
          right
          refine ⟨e, h_e_in, h_e_con⟩
        rcases h_ex1 with ⟨e1, h_e1_in, h_e1⟩
        rcases h_ex2 with ⟨e2, h_e2_in, h_e2⟩
        rcases uF.matching_nodeId e1 h_e1_in with ⟨uFLe1, h_uFLe1_in, h_uFLe1⟩
        rcases uF.matching_nodeId e2 h_e2_in with ⟨uFLe2, h_uFLe2_in, h_uFLe2⟩
        have h_eq_cce1 : connected_component_of_unionFind_of_unionFindLink uF uFLe1 h_uFLe1_in.left = cce1 := by
          simp [cce1, connected_component_of_unionFind_of_id]
          have h : uFLe1 = (List.choose (fun x => x.nodeId = e.node1) uF.linkList ⟨uFLe1, h_uFLe1_in.left, by simp [← h_uFLe1_in.right, h_e1]⟩) := by
            have h_uFLe1 := h_uFLe1 (List.choose (fun x => x.nodeId = e.node1) uF.linkList ⟨uFLe1, h_uFLe1_in.left, by simp [← h_uFLe1_in.right, h_e1]⟩)
            have h := List.choose_property (fun x => x.nodeId = e.node1) uF.linkList ⟨uFLe1, h_uFLe1_in.left, by simp [← h_uFLe1_in.right, h_e1]⟩
            simp [List.choose_mem, h, h_e1] at h_uFLe1
            simp [h_uFLe1]
          simp [h]
        have h_eq_cce2 : connected_component_of_unionFind_of_unionFindLink uF uFLe2 h_uFLe2_in.left = cce2 := by
          simp [cce2, connected_component_of_unionFind_of_id]
          have h : uFLe2 = (List.choose (fun x => x.nodeId = e.node2) uF.linkList ⟨uFLe2, h_uFLe2_in.left, by simp [← h_uFLe2_in.right, h_e2]⟩) := by
            have h_uFLe2 := h_uFLe2 (List.choose (fun x => x.nodeId = e.node2) uF.linkList ⟨uFLe2, h_uFLe2_in.left, by simp [← h_uFLe2_in.right, h_e2]⟩)
            have h := List.choose_property (fun x => x.nodeId = e.node2) uF.linkList ⟨uFLe2, h_uFLe2_in.left, by simp [← h_uFLe2_in.right, h_e2]⟩
            simp [List.choose_mem, h, h_e2] at h_uFLe2
            simp [h_uFLe2]
          simp [h]
        have h_w1 := parent_walk h_uFLe1_in.left h_nodup h_nonempty h_invariant
        have h_w2 := parent_walk h_uFLe2_in.left h_nodup h_nonempty h_invariant
        simp [get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink h_uFLe1_in.left h_nodup, h_eq_cce1, ← h_uFLe1_in.right, h_e1] at h_w1
        simp [get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink h_uFLe2_in.left h_nodup, h_eq_cce2, ← h_uFLe2_in.right, h_e2] at h_w2
        have h_w1 := SimpleGraph.Reachable.mono h_subgraph (by unfold SimpleGraph.Reachable; exact h_w1)
        have h_w2 := SimpleGraph.Reachable.mono h_subgraph (by unfold SimpleGraph.Reachable; exact h_w2)
        rcases h_w1 with ⟨w1⟩
        rcases h_w2 with ⟨w2⟩
        let w2 := SimpleGraph.Walk.reverse w2
        simp [h_uFLx_prop, h_uFLy_prop]
        refine ⟨SimpleGraph.Walk.append w2 (.cons ?_ w1)⟩
        simp [H, update_edgesSoFar, h_cc_eq, h_cce1, h_cce2]

    · intro uFL h_uFL_in
      set uFLx : unionFindLink nodeList := List.choose (fun a => a.nodeId = cce1 ∧ a.ccId = cce1) uF.linkList h_e1_self_con with ← h_uFLx
      set uFLy : unionFindLink nodeList := List.choose (fun a => a.nodeId = cce2 ∧ a.ccId = cce2) uF.linkList h_e2_self_con with ← h_uFLy
      have h_uFLx_in : uFLx ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = cce1 ∧ a.ccId = cce1) uF.linkList h_e1_self_con
      have h_uFLy_in : uFLy ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = cce2 ∧ a.ccId = cce2) uF.linkList h_e2_self_con
      have h_uFLx_prop : uFLx.nodeId = cce1 ∧ uFLx.ccId = cce1 := List.choose_property (fun a => a.nodeId = cce1 ∧ a.ccId = cce1) uF.linkList h_e1_self_con
      have h_uFLy_prop : uFLy.nodeId = cce2 ∧ uFLy.ccId = cce2 := List.choose_property (fun a => a.nodeId = cce2 ∧ a.ccId = cce2) uF.linkList h_e2_self_con
      have h_idx_uFLx_lt : List.idxOf uFLx uF.linkList < uF.linkList.length := by
        exact List.idxOf_lt_length_of_mem h_uFLx_in
      have h_idx_uFLy_lt : List.idxOf uFLy uF.linkList < uF.linkList.length := by
        exact List.idxOf_lt_length_of_mem h_uFLy_in
      simp [h_uFLx, h_uFLy, ] at h_uFL_in
      set uFLx' : unionFindLink nodeList := { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank } with ← h_uFLx'
      have h_ne : uFLy ≠ uFLx' := by
        grind
      have h_ne_idx : List.idxOf uFLy uF.linkList ≠ List.idxOf uFLx uF.linkList := by
        have : uFLx = uF.linkList[List.idxOf uFLx uF.linkList]'h_idx_uFLx_lt := by
          simp
        grind
      have h_eq_idx := idxOf_eq_idxOf_set h_ne h_ne_idx
      rcases (mem_or_eq_of_mem_set h_uFL_in) with h_uFL_in | h_uFL_eq
      · rcases (mem_or_eq_of_mem_set h_uFL_in) with h_uFL_in | h_uFL_eq
        · have h_invariant := h_invariant uFL h_uFL_in
          set G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) }
          set H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2), f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } with ← h_H
          simp [update_edgesSoFar, h_cce1, h_cce2, h_cc_eq] at h_H
          simp [h_H]
          have h_subgraph : G ≤ H := by
            simp [LE.le, G, ← h_H]
            intro u v e h_e_in h_e_con
            right
            refine ⟨e, h_e_in, h_e_con⟩
          simp [parent_nodeId]
          simp [parent_nodeId] at h_invariant
          exact SimpleGraph.Reachable.mono h_subgraph h_invariant
        · simp [parent_nodeId, h_uFL_eq, ← h_uFLx', SimpleGraph.Reachable]
          set G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) }
          set H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2), f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } with ← h_H
          simp [update_edgesSoFar, h_cce1, h_cce2, h_cc_eq] at h_H
          simp [h_H]
          have h_subgraph : G ≤ H := by
            simp [LE.le, G, ← h_H]
            intro u v e h_e_in h_e_con
            right
            refine ⟨e, h_e_in, h_e_con⟩
          rcases h_ex1 with ⟨e1, h_e1_in, h_e1⟩
          rcases h_ex2 with ⟨e2, h_e2_in, h_e2⟩
          rcases uF.matching_nodeId e1 h_e1_in with ⟨uFLe1, h_uFLe1_in, h_uFLe1⟩
          rcases uF.matching_nodeId e2 h_e2_in with ⟨uFLe2, h_uFLe2_in, h_uFLe2⟩
          have h_eq_cce1 : connected_component_of_unionFind_of_unionFindLink uF uFLe1 h_uFLe1_in.left = cce1 := by
            simp [cce1, connected_component_of_unionFind_of_id]
            have h : uFLe1 = (List.choose (fun x => x.nodeId = e.node1) uF.linkList ⟨uFLe1, h_uFLe1_in.left, by simp [← h_uFLe1_in.right, h_e1]⟩) := by
              have h_uFLe1 := h_uFLe1 (List.choose (fun x => x.nodeId = e.node1) uF.linkList ⟨uFLe1, h_uFLe1_in.left, by simp [← h_uFLe1_in.right, h_e1]⟩)
              have h := List.choose_property (fun x => x.nodeId = e.node1) uF.linkList ⟨uFLe1, h_uFLe1_in.left, by simp [← h_uFLe1_in.right, h_e1]⟩
              simp [List.choose_mem, h, h_e1] at h_uFLe1
              simp [h_uFLe1]
            simp [h]
          have h_eq_cce2 : connected_component_of_unionFind_of_unionFindLink uF uFLe2 h_uFLe2_in.left = cce2 := by
            simp [cce2, connected_component_of_unionFind_of_id]
            have h : uFLe2 = (List.choose (fun x => x.nodeId = e.node2) uF.linkList ⟨uFLe2, h_uFLe2_in.left, by simp [← h_uFLe2_in.right, h_e2]⟩) := by
              have h_uFLe2 := h_uFLe2 (List.choose (fun x => x.nodeId = e.node2) uF.linkList ⟨uFLe2, h_uFLe2_in.left, by simp [← h_uFLe2_in.right, h_e2]⟩)
              have h := List.choose_property (fun x => x.nodeId = e.node2) uF.linkList ⟨uFLe2, h_uFLe2_in.left, by simp [← h_uFLe2_in.right, h_e2]⟩
              simp [List.choose_mem, h, h_e2] at h_uFLe2
              simp [h_uFLe2]
            simp [h]
          have h_w1 := parent_walk h_uFLe1_in.left h_nodup h_nonempty h_invariant
          have h_w2 := parent_walk h_uFLe2_in.left h_nodup h_nonempty h_invariant
          simp [get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink h_uFLe1_in.left h_nodup, h_eq_cce1, ← h_uFLe1_in.right, h_e1] at h_w1
          simp [get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink h_uFLe2_in.left h_nodup, h_eq_cce2, ← h_uFLe2_in.right, h_e2] at h_w2
          have h_w1 := SimpleGraph.Reachable.mono h_subgraph (by unfold SimpleGraph.Reachable; exact h_w1)
          have h_w2 := SimpleGraph.Reachable.mono h_subgraph (by unfold SimpleGraph.Reachable; exact h_w2)
          rcases h_w1 with ⟨w1⟩
          rcases h_w2 with ⟨w2⟩
          let w1 := SimpleGraph.Walk.reverse w1
          simp [h_uFLx_prop, h_uFLy_prop]
          refine ⟨SimpleGraph.Walk.append w1 (.cons ?_ w2)⟩
          simp [H, update_edgesSoFar, h_cc_eq, h_cce1, h_cce2]
      · simp [parent_nodeId, h_uFL_eq, SimpleGraph.Reachable]
        simp [h_uFLy_prop]
        exact ⟨.nil⟩

theorem update_con_of_con
  {a b c d : Nat}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {h_a : ∃ x ∈ nodeList, x.id = a}
  {h_b : ∃ x ∈ nodeList, x.id = b}
  {h_c : ∃ uFL ∈ uF.linkList, (fun uFL' => uFL'.nodeId = c ∧ uFL'.ccId = c) uFL}
  {h_d : ∃ uFL ∈ uF.linkList, (fun uFL' => uFL'.nodeId = d ∧ uFL'.ccId = d) uFL}
  (h_con : connected_component_of_unionFind_of_id uF a h_a = connected_component_of_unionFind_of_id uF b h_b)
  : connected_component_of_unionFind_of_id (update_unionFind uF c d h_c h_d) a h_a = connected_component_of_unionFind_of_id (update_unionFind uF c d h_c h_d) b h_b := by

  sorry

theorem new_edge_con
  {nodeList : List node}
  {uF : unionFind nodeList}
  -- {h_nodup : nodeList.Nodup}
  -- (h_nonempty : nodeList ≠ [])
  {x y : Nat}
  (h_ex_x : ∃ a ∈ nodeList, a.id = x)
  (h_ex_y : ∃ a ∈ nodeList, a.id = y)
  (h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x ∧ a.ccId = x) a)
  (h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y ∧ a.ccId = y) a)
  : connected_component_of_unionFind_of_id (update_unionFind uF x y h₁ h₂) x h_ex_x = connected_component_of_unionFind_of_id (update_unionFind uF x y h₁ h₂) y h_ex_y := by
  sorry

theorem kruskal_helper_Reachable_iff_con
  {e : edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  {h_nodup : nodeList.Nodup}
  (h_nonempty : nodeList ≠ [])
  (h_ex1 : ∃ x ∈ nodeList, x.id = e.node1)
  (h_ex2 : ∃ x ∈ nodeList, x.id = e.node2)
  (h_e1_self_con : ∃ uFL ∈ uF.linkList, uFL.nodeId = connected_component_of_unionFind_of_id uF e.node1 h_ex1 ∧ uFL.ccId = connected_component_of_unionFind_of_id uF e.node1 h_ex1)
  (h_e2_self_con : ∃ uFL ∈ uF.linkList, uFL.nodeId = connected_component_of_unionFind_of_id uF e.node2 h_ex2 ∧ uFL.ccId = connected_component_of_unionFind_of_id uF e.node2 h_ex2)
  (h_invariant : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => ∀ (a b : Fin _), (h_ex_x : ∃ x ∈ nodeList, x.id = ↑a) → (h_ex_y : ∃ x ∈ nodeList, x.id = ↑b) → (G.Reachable a b ↔ connected_component_of_unionFind_of_id uF a.val h_ex_x = connected_component_of_unionFind_of_id uF b.val h_ex_y)) { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) })
  : (fun
      (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => ∀ (a b : Fin _), (h_ex_x : ∃ x ∈ nodeList, x.id = ↑a) →
      (h_ex_y : ∃ x ∈ nodeList, x.id = ↑b) →
      (G.Reachable a b ↔
        connected_component_of_unionFind_of_id (update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2) h_e1_self_con h_e2_self_con) a.val h_ex_x =
        connected_component_of_unionFind_of_id (update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2) h_e1_self_con h_e2_self_con) b.val h_ex_y))
    { Adj := fun a b => ∃ f ∈ update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 h_ex1) (connected_component_of_unionFind_of_id uF e.node2 h_ex2), f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) } := by
  simp
  intro a b x h_x_in h_x y h_y_in h_y
  set cce1 := connected_component_of_unionFind_of_id uF e.node1 h_ex1 with ← h_cce1
  set cce2 := connected_component_of_unionFind_of_id uF e.node2 h_ex2 with ← h_cce2
  set cca := connected_component_of_unionFind_of_id uF ↑a ⟨x, h_x_in, h_x⟩ with h_cca
  set ccb := connected_component_of_unionFind_of_id uF ↑b ⟨y, h_y_in, h_y⟩ with h_ccb
  simp [h_cce1, h_cce2]
  by_cases h_cc_eq : cce1 = cce2
  · simp [update_edgesSoFar, update_unionFind, h_cc_eq]
    simp at h_invariant
    exact h_invariant a b x h_x_in h_x y h_y_in h_y
  · simp [update_edgesSoFar, h_cc_eq] -- , update_unionFind
    set G :  SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless := (by simp [irrefl_def]; intro a e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) }
    set H :  SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => (e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a) ∨ ∃ f ∈ edgesSoFar, f.node1 = ↑a ∧ f.node2 = ↑b ∨ f.node1 = ↑b ∧ f.node2 = ↑a, symm := (by simp [Symmetric]; intro a b e; grind), loopless :=  (by simp [irrefl_def]; intro a; constructor; grind; intro e _ h_eq₁ h_eq₂; have h_lt := e.nodesLt; simp [h_eq₁, h_eq₂] at h_lt) }
    have h_subgraph : G ≤ H := by
      simp [LE.le, G, H]
      intro u v e h_e_in h_e_con
      right
      refine ⟨e, h_e_in, h_e_con⟩

    by_cases h_a_eq_b : a = b
    · simp [h_a_eq_b]
    · constructor
      · intro h_reachable_H
        by_cases h_reachable_G : G.Reachable a b
        · have h_invariant := (h_invariant a b ⟨x, h_x_in, h_x⟩ ⟨y, h_y_in, h_y⟩).mp h_reachable_G
          exact update_con_of_con h_invariant
        · set e1 : Fin (nodeList.max h_nonempty).id.succ := ⟨e.node1, by grind⟩
          set e2 : Fin (nodeList.max h_nonempty).id.succ := ⟨e.node2, by grind⟩
          have h_con_e1 : connected_component_of_unionFind_of_id uF e.node1 h_ex1 = connected_component_of_unionFind_of_id uF cce1 (by rcases h_e1_self_con with ⟨_, h_in, h, _⟩; rw [← h]; exact node_of_uFL h_in h_nodup) := by
            simp [h_cce1]
            rcases h_e1_self_con with ⟨uFL, h_uFL_in, h_uFL⟩
            simp [connected_component_of_unionFind_of_id, ← h_uFL.left, uFL_choose_self h_uFL_in h_nodup]
            rw [connected_component_of_unionFind_of_unionFindLink]
            simp [h_uFL]
          have h_con_e2 : connected_component_of_unionFind_of_id uF e.node2 h_ex2 = connected_component_of_unionFind_of_id uF cce2 (by rcases h_e2_self_con with ⟨_, h_in, h, _⟩; rw [← h]; exact node_of_uFL h_in h_nodup) := by
            simp [h_cce2]
            rcases h_e2_self_con with ⟨uFL, h_uFL_in, h_uFL⟩
            simp [connected_component_of_unionFind_of_id, ← h_uFL.left, uFL_choose_self h_uFL_in h_nodup]
            rw [connected_component_of_unionFind_of_unionFindLink]
            simp [h_uFL]
          have h_con_e1 := update_con_of_con (h_con_e1) (h_c := h_e1_self_con) (h_d := h_e2_self_con)
          have h_con_e2 := update_con_of_con (h_con_e2) (h_c := h_e1_self_con) (h_d := h_e2_self_con)
          by_cases h_a12b : G.Reachable a e1 ∧ G.Reachable b e2
          · have h_con_a := update_con_of_con ((h_invariant a e1 ⟨x, h_x_in, h_x⟩ h_ex1).mp h_a12b.left) (h_c := h_e1_self_con) (h_d := h_e2_self_con)
            have h_con_b := update_con_of_con ((h_invariant b e2 ⟨y, h_y_in, h_y⟩ h_ex2).mp h_a12b.right) (h_c := h_e1_self_con) (h_d := h_e2_self_con)
            simp [h_con_a, h_con_b, e1, e2, h_con_e1, h_con_e2]
            apply new_edge_con
          · by_cases h_a21b : G.Reachable a e2 ∧ G.Reachable b e1
            · have h_con_a := update_con_of_con ((h_invariant a e2 ⟨x, h_x_in, h_x⟩ h_ex2).mp h_a21b.left) (h_c := h_e1_self_con) (h_d := h_e2_self_con)
              have h_con_b := update_con_of_con ((h_invariant b e1 ⟨y, h_y_in, h_y⟩ h_ex1).mp h_a21b.right) (h_c := h_e1_self_con) (h_d := h_e2_self_con)
              simp [h_con_a, h_con_b, e1, e2, h_con_e1, h_con_e2]
              rw [eq_comm]
              apply new_edge_con
            · have h_e_not_reachable : ¬G.Reachable e1 e2 := by
                intro h
                have h := (h_invariant e1 e2 h_ex1 h_ex2).mp h
                simp [e1, e2, h_cce1, h_cce2, h_cc_eq] at h
              have h_e_not_adj : ¬G.Adj e1 e2 := by
                intro h
                let w : G.Walk e1 e2 := .cons h .nil
                simp [SimpleGraph.Reachable] at h_e_not_reachable
                have h := h_e_not_reachable.false w
                simp at h
              have h : G = H.deleteEdges {.mk e1 e2} := by
                refine adj_inj.mp ?_
                ext c d
                simp [G, H]
                clear * - h_e_not_adj
                simp [G] at h_e_not_adj
                constructor
                · intro h
                  rcases h with ⟨g, h_g_in, h_g⟩
                  constructor
                  · right
                    exact ⟨g, h_g_in, h_g⟩
                  · have h := h_e_not_adj g h_g_in
                    simp [Fin.ext_iff]
                    grind
                · intro h
                  rcases h with ⟨⟨h | h⟩ | h, h_not_in⟩
                  · simp [e1, e2, h] at h_not_in
                  · simp [e1, e2, h] at h_not_in
                  · exact h
              have h_f_in := edge_in_walk h h_reachable_G
              simp [SimpleGraph.Reachable] at h_reachable_H
              rcases h_reachable_H with ⟨p⟩
              have h_f_in := h_f_in p
              have h_f_in' : s(e1, e2) ∈ p.reverse.edges := by
                simp [h_f_in]
              have h_contra := vertex_of_edge_in_walk_reachable_without_edge h_f_in
              have h_contra' := vertex_of_edge_in_walk_reachable_without_edge h_f_in'
              simp [← h] at h_contra h_contra'
              rcases h_contra with h_contra | h_contra
              · rcases h_contra' with h_contra' | h_contra'
                · rcases h_contra with ⟨p⟩
                  rcases h_contra' with ⟨p'⟩
                  simp [SimpleGraph.Reachable, Nonempty.intro (SimpleGraph.Walk.append p p'.reverse)] at h_reachable_G
                · simp [h_contra, h_contra'] at h_a12b
              · rcases h_contra' with h_contra' | h_contra'
                · simp [h_contra, h_contra'] at h_a21b
                · rcases h_contra with ⟨p⟩
                  rcases h_contra' with ⟨p'⟩
                  simp [SimpleGraph.Reachable, Nonempty.intro (SimpleGraph.Walk.append p p'.reverse)] at h_reachable_G

      · intro h_con
        simp [SimpleGraph.Reachable]
        have h_reachable_parent_G : ∀ uFL, (h_in : uFL ∈ uF.linkList) → G.Reachable ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨(parent _ h_in).nodeId, nodeId_lt_max (parent_in h_in) h_nodup h_nonempty⟩ := by
          intro uFL h_uFL_in
          have h_ex_x : ∃ x ∈ nodeList, x.id = (⟨uFL.nodeId, nodeId_lt_max h_uFL_in h_nodup h_nonempty⟩ : Fin _).val := by
            simp [node_of_uFL h_uFL_in h_nodup]
          have h_ex_y : ∃ x ∈ nodeList, x.id = (⟨(parent uFL h_uFL_in).nodeId, nodeId_lt_max (parent_in h_uFL_in) h_nodup h_nonempty⟩ : Fin _).val := by
            simp [node_of_uFL (parent_in h_uFL_in) h_nodup]
          have h_invariant := h_invariant ⟨uFL.nodeId, nodeId_lt_max h_uFL_in h_nodup h_nonempty⟩ ⟨(parent uFL h_uFL_in).nodeId, nodeId_lt_max (parent_in h_uFL_in) h_nodup h_nonempty⟩ h_ex_x h_ex_y
          simp [h_invariant, connected_component_of_unionFind_of_id, uFL_choose_self h_uFL_in h_nodup, uFL_choose_self (parent_in h_uFL_in) h_nodup]
          nth_rewrite 1 [connected_component_of_unionFind_of_unionFindLink]
          split_ifs with h
          · simp [parent, h, uFL_choose_self h_uFL_in h_nodup, connected_component_of_unionFind_of_unionFindLink]
          · simp [parent]
        have h_reachable_parent_H : ∀ uFL, (h_in : uFL ∈ (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList) → H.Reachable ⟨uFL.nodeId, nodeId_lt_max h_in h_nodup h_nonempty⟩ ⟨(parent _ h_in).nodeId, nodeId_lt_max (parent_in h_in) h_nodup h_nonempty⟩ := by
          have h := update_unionFind_reachable_parent h_nodup h_nonempty h_ex1 h_ex2 h_e1_self_con h_e2_self_con h_reachable_parent_G
          intro uFL h_uFL_in
          have h := h uFL h_uFL_in
          simp [update_edgesSoFar, h_cc_eq, h_cce1, h_cce2] at h
          exact h
        rcases ((update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).matching_nodeId x h_x_in) with ⟨uFLa, h_uFLa, h_unique_a⟩
        rcases ((update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).matching_nodeId y h_y_in) with ⟨uFLb, h_uFLb, h_unique_b⟩
        have h_wa := parent_walk h_uFLa.left h_nodup h_nonempty h_reachable_parent_H
        have h_wb := parent_walk h_uFLb.left h_nodup h_nonempty h_reachable_parent_H
        simp [← h_uFLa.right, h_x, get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink h_uFLa.left h_nodup] at h_wa
        simp [← h_uFLb.right, h_y, get_parent_path_last_eq_connected_component_of_unionFind_of_unionFindLink h_uFLb.left h_nodup] at h_wb
        have h_eq_a : connected_component_of_unionFind_of_id (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con) ↑a ⟨x, h_x_in, h_x⟩ = connected_component_of_unionFind_of_unionFindLink (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con) uFLa h_uFLa.left := by
          simp [connected_component_of_unionFind_of_id]
          have h : List.choose (fun x => x.nodeId = ↑a) (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList ⟨uFLa, h_uFLa.left, by simp [h_uFLa.right.symm, h_x]⟩ = uFLa := by
            have h_unique_a := h_unique_a (List.choose (fun x => x.nodeId = ↑a) (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList ⟨uFLa, h_uFLa.left, by simp [h_uFLa.right.symm, h_x]⟩)
            have h := List.choose_property (fun x => x.nodeId = ↑a) (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList ⟨uFLa, h_uFLa.left, by simp [h_uFLa.right.symm, h_x]⟩
            simp [List.choose_mem, h, h_x] at h_unique_a
            exact h_unique_a
          simp [h]
        have h_eq_b : connected_component_of_unionFind_of_id (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con) ↑b ⟨y, h_y_in, h_y⟩ = connected_component_of_unionFind_of_unionFindLink (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con) uFLb h_uFLb.left := by
          simp [connected_component_of_unionFind_of_id]
          have h : List.choose (fun x => x.nodeId = ↑b) (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList ⟨uFLb, h_uFLb.left, by simp [h_uFLb.right.symm, h_y]⟩ = uFLb := by
            have h_unique_b := h_unique_b (List.choose (fun x => x.nodeId = ↑b) (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList ⟨uFLb, h_uFLb.left, by simp [h_uFLb.right.symm, h_y]⟩)
            have h := List.choose_property (fun x => x.nodeId = ↑b) (update_unionFind uF cce1 cce2 h_e1_self_con h_e2_self_con).linkList ⟨uFLb, h_uFLb.left, by simp [h_uFLb.right.symm, h_y]⟩
            simp [List.choose_mem, h, h_y] at h_unique_b
            exact h_unique_b
          simp [h]
        simp [h_eq_a, h_eq_b] at h_con
        simp [h_con] at h_wa
        rcases h_wa with ⟨wa⟩
        rcases h_wb with ⟨wb⟩
        let wb := SimpleGraph.Walk.reverse wb
        exact ⟨SimpleGraph.Walk.append wa wb⟩

theorem kruskal_helper_IsAcyclic
  {edgeList : List edge}
  {nodeList : List node}
  {uF : unionFind nodeList}
  {edgesSoFar : List edge}
  (h_matching_edge : matching_edge edgeList nodeList)
  {h_nodup : nodeList.Nodup}
  (h_nonempty : nodeList ≠ [])
  {h_symm : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  {h_loopless : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  {h_symm' : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  {h_loopless' : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a}
  (h_invariant₁ : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => G.IsAcyclic) { Adj := fun a b => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm', loopless := h_loopless'})
  (h_invariant₂ : (fun (G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => ∀ (a b : Fin _), (h_ex_x : ∃ x ∈ nodeList, x.id = ↑a) → (h_ex_y : ∃ x ∈ nodeList, x.id = ↑b) → G.Reachable a b ↔ connected_component_of_unionFind_of_id uF a.val h_ex_x = connected_component_of_unionFind_of_id uF b.val h_ex_y) { Adj := fun a b => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm', loopless := h_loopless'})
  : (fun (H : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ)) => H.IsAcyclic) { Adj := fun a b => ∃ e ∈ kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm, loopless := h_loopless } := by
  simp
  induction
    edgeList,
    uF,
    edgesSoFar,
    h_matching_edge
  using kruskal_helper.induct with
  | case1 uF edgesSoFar h_matching_edge =>
    simp [kruskal_helper]
    exact h_invariant₁
  | case2 uF edgesSoFar e es h_matching_edge' h_ex_1 x h_ex_2 y h_matching_edge h_uFLx =>
    rename_i h_uFLy updated_uF updated_edgesSoFar ih
    simp [kruskal_helper]
    have h_x : connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e es h_matching_edge') = x := by
      simp [x]
    have h_y : connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e es h_matching_edge') = y := by
      simp [y]
    simp [h_x, h_y]
    apply ih
    · simp [updated_edgesSoFar, update_edgesSoFar]
      by_cases h_eq : x = y
      · simp [h_eq]
        exact h_invariant₁
      · simp [h_eq]
        simp [matching_edge] at h_matching_edge'
        have h_match1 := h_matching_edge'.left.left
        have h_match2 := h_matching_edge'.left.right
        simp [eq_comm] at h_match1
        simp [eq_comm] at h_match2
        have h_e1_lt : e.node1 < (nodeList.max h_nonempty).id.succ := by
          rcases h_match1 with ⟨z, h_z⟩
          simp [← h_z.right]
          have h_goal : z ≤ nodeList.max h_nonempty := by
            grind
          exact h_goal
        have h_e2_lt : e.node2 < (nodeList.max h_nonempty).id.succ := by
          rcases h_match2 with ⟨z, h_z⟩
          simp [← h_z.right]
          have h_goal : z ≤ nodeList.max h_nonempty := by
            grind
          exact h_goal
        set G : SimpleGraph (Fin (nodeList.max h_nonempty).id.succ) := { Adj := fun a b => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm', loopless := h_loopless' } with ← h_G
        have h_not_reachable : ¬G.Reachable ⟨e.node1, h_e1_lt⟩ ⟨e.node2, h_e2_lt⟩ := by
          intro h
          have h' := (h_invariant₂ ⟨e.node1, h_e1_lt⟩ ⟨e.node2, h_e2_lt⟩ h_match1 h_match2).mp h
          simp [h_x, h_y, h_eq] at h'
        have h := (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable _ _ h_not_reachable).mpr h_invariant₁
        have h_symm'' : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => (e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a) ∨ ∃ a_1 ∈ edgesSoFar, a_1.node1 = ↑a ∧ a_1.node2 = ↑b ∨ a_1.node1 = ↑b ∧ a_1.node2 = ↑a := by
          simp [Symmetric]
          intro a b e
          grind
        have h_loopless'' : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => (e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a) ∨ ∃ a_1 ∈ edgesSoFar, a_1.node1 = ↑a ∧ a_1.node2 = ↑b ∨ a_1.node1 = ↑b ∧ a_1.node2 = ↑a := by
          simp [irrefl_def]
          intro a
          constructor
          · grind
          · intro e _ h_eq₁ h_eq₂
            have h_lt := e.nodesLt
            simp [h_eq₁, h_eq₂] at h_lt
        have h_add_edge_eq : G ⊔ SimpleGraph.edge ⟨e.node1, h_e1_lt⟩ ⟨e.node2, h_e2_lt⟩ = { Adj := fun a b => (e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a) ∨ ∃ a_1 ∈ edgesSoFar, a_1.node1 = ↑a ∧ a_1.node2 = ↑b ∨ a_1.node1 = ↑b ∧ a_1.node2 = ↑a, symm := h_symm'', loopless := h_loopless'' } := by
          simp [G]
          ext a b
          simp [SimpleGraph.edge]
          grind
        simp [h_add_edge_eq] at h
        exact h
    · simp [updated_edgesSoFar, update_edgesSoFar, updated_uF]
      by_cases h_eq : x = y
      · simp [h_eq, update_unionFind]
        simp at h_invariant₂
        exact h_invariant₂
      · intro a b xa h_xa_in h_xa xb h_xb_in h_xb
        simp [h_eq]
        simp at h_invariant₂
        have h := kruskal_helper_Reachable_iff_con h_nonempty h_ex_1 h_ex_2 h_uFLx h_uFLy (by simp; exact h_invariant₂) a b ⟨xa, h_xa_in, h_xa⟩ ⟨xb, h_xb_in, h_xb⟩ (h_nodup := h_nodup) (edgesSoFar := edgesSoFar) (uF := uF) (e := e)
        simp [update_edgesSoFar, h_x, h_y, h_eq] at h
        exact h
    · simp [Symmetric]
      intro a b e
      grind
    · simp [irrefl_def]
      intro a e _ h_eq₁ h_eq₂
      have h_lt := e.nodesLt
      simp [h_eq₁, h_eq₂] at h_lt

-- nicht von mir gelöst sondern von Zulip-Nutzer Aaron Liu https://leanprover.zulipchat.com/#user/816344
theorem cast_Fin_fun {n m : Nat} {a b : Fin m} (f : (Fin n) → (Fin n) → Prop) (h : Fin n = Fin m) : (h ▸ f) a b = f (h ▸ a) (h ▸ b) := by
  cases fin_injective h
  rfl

theorem SimpleGraph_of_kruskal.IsAcyclic (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h).IsAcyclic := by
  set G := SimpleGraph_of_kruskal edgeList h with h_G
  simp [SimpleGraph_of_kruskal, SimpleGraph_of_n_of_edgeList, SimpleGraph_of_edgeList, kruskal_of_edgeList, kruskal] at h_G --, SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  set edgeListSorted := edgeList.mergeSort fun a b => decide (a ≤ b) with h_edgeListSorted
  set nodeList := nodeList_of_edgeList edgeList with h_nodeList
  set uF := init_unionFind (nodeList_of_edgeList edgeList) (nodeList_of_edgeList_nodup edgeList) with h_uF
  set edgesSoFar : List edge := [] with h_edgesSoFar
  simp [h_edgesSoFar] at h
  have h_matching_edge : matching_edge _ _ := kruskal._proof_1 edgeList (nodeList_of_edgeList edgeList) (matching_edge_for_nodeList_of_edgeList edgeList)
  have h_nodup := nodeList_of_edgeList_nodup edgeList
  simp [← h_edgeListSorted, ← h_uF, ← h_edgesSoFar] at h_G
  have h_eq := nodeList_of_edgeList_max_eq edgeList h
  simp only [kruskal_of_edgeList, kruskal, Nat.succ_eq_add_one] at h_eq
  nth_rewrite 2 [nodeList_of_edgeList_max] at h_eq
  have h_nonempty : nodeList ≠ [] := nodeList_of_edgeList_nonempty edgeList h
  have h_symm : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeListSorted nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by
    simp [Symmetric]
    intro a b e
    grind
  have h_loopless : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ kruskal_helper edgeListSorted nodeList uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by
    simp [irrefl_def]
    intro a e _ h_eq₁ h_eq₂
    have h_lt := e.nodesLt
    simp [h_eq₁, h_eq₂] at h_lt
  have h_symm' : Symmetric fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by
    simp [Symmetric]
    intro a b e
    grind
  have h_loopless' : Std.Irrefl fun (a b : Fin (nodeList.max h_nonempty).id.succ) => ∃ e ∈ edgesSoFar, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a := by
    simp [irrefl_def]
    intro a e _ h_eq₁ h_eq₂
    have h_lt := e.nodesLt
    simp [h_eq₁, h_eq₂] at h_lt
  have h_acyclic_of_invariants := kruskal_helper_IsAcyclic h_matching_edge h_nonempty (edgeList := edgeListSorted) (nodeList := nodeList_of_edgeList edgeList) (uF := uF) (edgesSoFar := edgesSoFar) (h_nodup := h_nodup) (h_loopless := h_loopless) (h_loopless' := h_loopless') (h_symm := h_symm) (h_symm' := h_symm')
  simp at h_acyclic_of_invariants
  have h_acyclic := h_acyclic_of_invariants ?_ ?_
  · have h_SimpleGraph_eq : SimpleGraph (Fin ((nodeList_of_edgeList edgeList).max (nodeList_of_edgeList_nonempty edgeList h)).id.succ) = SimpleGraph (Fin (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) (kruskal_nonempty _ h)).id.succ) := by
      simp [← h_eq, nodeList_of_edgeList_max, kruskal_of_edgeList, kruskal]
    have h_Fin_eq : Fin ((nodeList_of_edgeList edgeList).max (nodeList_of_edgeList_nonempty edgeList h)).id.succ = Fin (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) (kruskal_nonempty _ h)).id.succ := by
      simp [← h_eq, nodeList_of_edgeList_max, kruskal_of_edgeList, kruskal]
    set H : SimpleGraph (Fin (((nodeList_of_edgeList edgeList).max (nodeList_of_edgeList_nonempty edgeList h)).id + 1)) := { Adj := fun a b => ∃ e ∈ kruskal_helper edgeListSorted (nodeList_of_edgeList edgeList) uF edgesSoFar h_matching_edge h_nodup, e.node1 = ↑a ∧ e.node2 = ↑b ∨ e.node1 = ↑b ∧ e.node2 = ↑a, symm := h_symm, loopless := h_loopless } with h_H
    set G' := h_Fin_eq ▸ H with ← h_G'
    have : G'.IsAcyclic := by
      grind
    have : G = G' := by
      simp [h_G, G']
      ext a b
      have h_cast_1 : (h_Fin_eq ▸ H).Adj = h_Fin_eq ▸ H.Adj := by
        grind
      have h_cast_2 : (h_Fin_eq ▸ H.Adj) a b = H.Adj (h_Fin_eq ▸ a) (h_Fin_eq ▸ b) := by
        apply cast_Fin_fun
      simp [h_cast_1, h_cast_2]
      simp [H]
      have h_cast_3 : (h_Fin_eq ▸ a).val = a.val := by
        grind
      have h_cast_4 : (h_Fin_eq ▸ b).val = b.val := by
        grind
      simp [h_cast_3, h_cast_4]
    grind
  · simp [edgesSoFar, SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  · simp [edgesSoFar]
    intro a b x h_x_in h_x y h_y_in h_y
    constructor
    · simp [SimpleGraph.Reachable]
      intro p
      cases p with
      | nil =>
        simp
      | cons h_adj p' =>
        simp at h_adj
    · simp [nodeList] at h_nonempty
      simp [connected_component_of_unionFind_of_id]
      set uFLa := List.choose (fun x => x.nodeId = ↑a) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF (↑a) (Exists.intro x ⟨h_x_in, h_x⟩)) with ← h_uFLa
      set uFLb := List.choose (fun x => x.nodeId = ↑b) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF (↑b) (Exists.intro y ⟨h_y_in, h_y⟩)) with ← h_uFLb
      simp [h_uFLa, h_uFLb]
      have h_uFLa_mem := List.choose_mem (fun x => x.nodeId = ↑a) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF (↑a) (Exists.intro x ⟨h_x_in, h_x⟩))
      have h_uFLb_mem := List.choose_mem (fun x => x.nodeId = ↑b) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF (↑b) (Exists.intro y ⟨h_y_in, h_y⟩))
      have h_uFLa_prop := List.choose_property (fun x => x.nodeId = ↑a) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF (↑a) (Exists.intro x ⟨h_x_in, h_x⟩))
      have h_uFLb_prop := List.choose_property (fun x => x.nodeId = ↑b) uF.linkList (connected_component_of_unionFind_of_id._proof_1 uF (↑b) (Exists.intro y ⟨h_y_in, h_y⟩))
      simp [h_uFLa, h_uFLb] at h_uFLa_mem h_uFLb_mem h_uFLa_prop h_uFLb_prop
      simp [uF, init_unionFind, h_nonempty, init_unionFind.linkList] at h_uFLa_mem h_uFLb_mem
      have h_all_self_con := init_unionFind.linkList.helper_all_self_connected (nodeList_of_edgeList edgeList) (nodeList_of_edgeList edgeList) (by simp [h_nonempty])
      rw [connected_component_of_unionFind_of_unionFindLink]
      rw [connected_component_of_unionFind_of_unionFindLink]
      simp [← h_all_self_con uFLa h_uFLa_mem, ← h_all_self_con uFLb h_uFLb_mem, h_uFLa_prop, h_uFLb_prop]
      intro h_a_eq_b
      have h_a_eq_b : a = b := by
        cases a
        cases b
        simp at h_a_eq_b
        simp [h_a_eq_b]
      simp [h_a_eq_b]










theorem SimpleGraph_of_kruskal.IsEqReachable (edgeList : List edge) (h : edgeList ≠ []) : ∀ (x y), (SimpleGraph_of_n_of_edgeList _ edgeList h (nodeList_of_edgeList_max_eq edgeList h)).Reachable x y ↔ (SimpleGraph_of_kruskal edgeList h).Reachable x y := by sorry

theorem SimpleGraph_of_kruskal.IsSpanningTree (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph.IsSpanningTree (SimpleGraph_of_n_of_edgeList _ edgeList h (nodeList_of_edgeList_max_eq edgeList h)) (SimpleGraph_of_kruskal edgeList h) := ⟨SimpleGraph_of_kruskal.IsSubgraph edgeList h, SimpleGraph_of_kruskal.IsAcyclic edgeList h, SimpleGraph_of_kruskal.IsEqReachable edgeList h⟩

theorem SimpleGraph_of_kruskal.connected_iff_connected (edgeList : List edge) (h : edgeList ≠ []) (h_con : (SimpleGraph_of_n_of_edgeList _ edgeList h (nodeList_of_edgeList_max_eq edgeList h)).Connected) : (SimpleGraph_of_kruskal edgeList h).Connected := by
  simp [SimpleGraph.connected_iff] at h_con ⊢
  constructor
  · simp [SimpleGraph.Preconnected] at h_con ⊢
    intro u v
    exact (SimpleGraph_of_kruskal.IsEqReachable edgeList h u v).mp (h_con.left u v)
  · apply Fin.pos_iff_nonempty.mp
    simp










theorem kruskal_minimalSpanninTree_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : minimalSpanninTree_of_edgeList h (kruskal_nonempty edgeList h) rfl (nodeList_of_edgeList_max_eq edgeList h).symm := by sorry









-- Ab hier für Algolean


instance fin_of_edgeList_Finite {edgeList : List edge} {h : edgeList ≠ []} : Finite (fin_of_edgeList edgeList h) := by
  simp [fin_of_edgeList]
  exact Finite.of_fintype (Fin ((nodeList_of_edgeList_max edgeList h).id + 1))

noncomputable instance SimpleGraph_of_edgeList.edgeSet_Fintype {edgeList : List edge} {h : edgeList ≠ []} : Fintype ↑(SimpleGraph_of_edgeList edgeList h).edgeSet :=
  Fintype.ofFinite ↑(SimpleGraph_of_edgeList edgeList h).edgeSet

theorem SimpleGraph_of_edgeList.ex_edge_of_edge (edgeList : List edge) (h : edgeList ≠ []) : ∀ (a b : fin_of_edgeList edgeList h), s(a, b) ∈ (SimpleGraph_of_edgeList edgeList h).edgeFinset → ∃ e ∈ edgeList, e.node1 = a.val ∧ e.node2 = b.val ∨ e.node1 = b.val ∧ e.node2 = a.val := by
  intro a b h_s_in
  simp [SimpleGraph_of_edgeList] at h_s_in
  exact h_s_in

noncomputable def SimpleGraph_of_edgeList.edge_of_edge (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_edgeList edgeList h).edgeFinset → edgeList.toFinset := by
  intro s -- a b h_s_in
  rcases s with ⟨s, h_s_in⟩
  simp [Sym2] at s
  -- have h_ex_s' := s.exists_rep
  have h_ex_a_b: ∃ a b, s = s(a, b) := by
    rcases s with ⟨a, b⟩
    refine ⟨a, b, rfl⟩
    -- rcases h_ex_s' with ⟨s', h⟩
    -- simp at h_s_in
  set a := Classical.choose h_ex_a_b with ← h_a
  have h_a_spec := Classical.choose_spec h_ex_a_b
  set b := Classical.choose h_a_spec with ← h_b
  have h_b_spec := Classical.choose_spec h_a_spec
  simp [h_a, h_b] at h_b_spec
  simp only [h_b_spec] at h_s_in
  have h_ex_edge_of_edge := SimpleGraph_of_edgeList.ex_edge_of_edge edgeList h a b h_s_in
  let e := List.choose (fun (e : edge) => e.node1 = a.val ∧ e.node2 = b.val ∨ e.node1 = b.val ∧ e.node2 = a.val) edgeList h_ex_edge_of_edge
  have h_e_in := List.choose_mem (fun (e : edge) => e.node1 = a.val ∧ e.node2 = b.val ∨ e.node1 = b.val ∧ e.node2 = a.val) edgeList h_ex_edge_of_edge
  have h_e_in' : e ∈ edgeList.toFinset := by
    exact List.mem_toFinset.mpr h_e_in
  exact ⟨e, h_e_in'⟩

theorem SimpleGraph_of_edgeList.edge_of_edge_injective (edgeList : List edge) (h : edgeList ≠ []) : Function.Injective (SimpleGraph_of_edgeList.edge_of_edge edgeList h) := by
  intro s1 s2 h_eq
  simp [SimpleGraph_of_edgeList.edge_of_edge] at h_eq
  set a := Classical.choose (SimpleGraph_of_edgeList.edge_of_edge._proof_1 edgeList h (↑s1) s1.property) with ← h_a
  set b := Classical.choose (SimpleGraph_of_edgeList.edge_of_edge._proof_3 edgeList h (↑s1) (edge_of_edge._proof_1 edgeList h (↑s1) s1.property)) with ← h_b
  set c := Classical.choose (SimpleGraph_of_edgeList.edge_of_edge._proof_1 edgeList h (↑s2) s2.property) with ← h_c
  set d := Classical.choose (SimpleGraph_of_edgeList.edge_of_edge._proof_3 edgeList h (↑s2) (edge_of_edge._proof_1 edgeList h (↑s2) s2.property)) with ← h_d
  have h_a_prop := Classical.choose_spec (SimpleGraph_of_edgeList.edge_of_edge._proof_1 edgeList h (↑s1) s1.property)
  have h_b_prop := Classical.choose_spec (SimpleGraph_of_edgeList.edge_of_edge._proof_3 edgeList h (↑s1) (edge_of_edge._proof_1 edgeList h (↑s1) s1.property))
  have h_c_prop := Classical.choose_spec (SimpleGraph_of_edgeList.edge_of_edge._proof_1 edgeList h (↑s2) s2.property)
  have h_d_prop := Classical.choose_spec (SimpleGraph_of_edgeList.edge_of_edge._proof_3 edgeList h (↑s2) (edge_of_edge._proof_1 edgeList h (↑s2) s2.property))
  simp [h_a, h_b, h_c, h_d] at h_eq h_a_prop h_b_prop h_c_prop h_d_prop
  have h_ex_e1 : ∃ e ∈ edgeList, e.node1 = a.val ∧ e.node2 = b.val ∨ e.node1 = b.val ∧ e.node2 = a.val := by
    have h_ex_a_b : ∃ (a b : fin_of_edgeList edgeList h), s1 = s(a, b) := by refine ⟨a, b, h_b_prop⟩
    have h := (SimpleGraph_of_edgeList.edge_of_edge._proof_6 edgeList h (↑s1) s1.property) h_ex_a_b rfl h_a_prop rfl h_b_prop
    exact h
  have h_ex_e2 : ∃ e ∈ edgeList, e.node1 = c.val ∧ e.node2 = d.val ∨ e.node1 = d.val ∧ e.node2 = c.val := by
    have h_ex_a_b : ∃ (c d : fin_of_edgeList edgeList h), s2 = s(c, d) := by refine ⟨c, d, h_d_prop⟩
    have h := (SimpleGraph_of_edgeList.edge_of_edge._proof_6 edgeList h (↑s2) s2.property) h_ex_a_b rfl h_c_prop rfl h_d_prop
    exact h
  set e1 := List.choose (fun e => e.node1 = a.val ∧ e.node2 = b.val ∨ e.node1 = b.val ∧ e.node2 = a.val) edgeList h_ex_e1 with ← h_e1
  set e2 := List.choose (fun e => e.node1 = c.val ∧ e.node2 = d.val ∨ e.node1 = d.val ∧ e.node2 = c.val) edgeList h_ex_e2 with ← h_e2
  have h_e1_prop := List.choose_property (fun e => e.node1 = a.val ∧ e.node2 = b.val ∨ e.node1 = b.val ∧ e.node2 = a.val) edgeList h_ex_e1
  have h_e2_prop := List.choose_property (fun e => e.node1 = c.val ∧ e.node2 = d.val ∨ e.node1 = d.val ∧ e.node2 = c.val) edgeList h_ex_e2
  simp [h_e1, h_e2, h_eq] at h_e1_prop h_e2_prop
  have h_goal : s(a, b) = s(c, d) := by
    rcases h_e1_prop with h_e1_prop | h_e1_prop
    · rcases h_e2_prop with h_e2_prop | h_e2_prop
      · simp [h_e1_prop] at h_e2_prop
        simp
        grind
      · simp [h_e1_prop] at h_e2_prop
        simp
        grind
    · rcases h_e2_prop with h_e2_prop | h_e2_prop
      · simp [h_e1_prop] at h_e2_prop
        simp
        grind
      · simp [h_e1_prop] at h_e2_prop
        simp
        grind
  simp [h_goal, ← h_d_prop] at h_b_prop
  exact h_b_prop

def SimpleGraph_of_edgeList.edge_of_edge_reverse (edgeList : List edge) (h : edgeList ≠ []) : edgeList.toFinset → (SimpleGraph_of_edgeList edgeList h).edgeFinset := by
  intro e -- h_e_in
  rcases e with ⟨e, h_e_in⟩
  have h_e_in : e ∈ edgeList := List.mem_dedup.mp h_e_in
  have h_lt1 : e.node1 < (nodeList_of_edgeList_max edgeList h).id.succ := by
    have h_goal : ⟨e.node1⟩ ≤ nodeList_of_edgeList_max edgeList h := by
      simp [nodeList_of_edgeList_max]
      have h_matching_edge := matching_edge_for_nodeList_of_edgeList edgeList
      simp [matching_edge] at h_matching_edge
      have h_matching_edge := (h_matching_edge e h_e_in).left
      rcases h_matching_edge with ⟨x, h_x_in, h_x⟩
      cases x
      simp at h_x
      simp [← h_x] at h_x_in
      simp [List.le_max_of_mem h_x_in]
    simp
    exact h_goal
  have h_lt2 : e.node2 < (nodeList_of_edgeList_max edgeList h).id.succ := by
    have h_goal : ⟨e.node2⟩ ≤ nodeList_of_edgeList_max edgeList h := by
      simp [nodeList_of_edgeList_max]
      have h_matching_edge := matching_edge_for_nodeList_of_edgeList edgeList
      simp [matching_edge] at h_matching_edge
      have h_matching_edge := (h_matching_edge e h_e_in).right
      rcases h_matching_edge with ⟨x, h_x_in, h_x⟩
      cases x
      simp at h_x
      simp [← h_x] at h_x_in
      simp [List.le_max_of_mem h_x_in]
    simp
    exact h_goal
  let a : fin_of_edgeList edgeList h := ⟨e.node1, h_lt1⟩
  let b : fin_of_edgeList edgeList h := ⟨e.node2, h_lt2⟩
  have h_edge : s(a, b) ∈ (SimpleGraph_of_edgeList edgeList h).edgeFinset := by
    simp [SimpleGraph_of_edgeList]
    simp [a, b]
    refine ⟨e, h_e_in, by simp⟩
  set s := s(a, b)
  exact ⟨s, h_edge⟩

theorem SimpleGraph_of_edgeList.edge_of_edge_reverse_injective
  (edgeList : List edge) (h : edgeList ≠ []) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2)
  : Function.Injective (SimpleGraph_of_edgeList.edge_of_edge_reverse edgeList h) := by
  intro e₁ e₂ h_eq
  rcases e₁ with ⟨e₁, h_e₁_in⟩
  rcases e₂ with ⟨e₂, h_e₂_in⟩
  have h_e₁_in : e₁ ∈ edgeList := List.mem_dedup.mp h_e₁_in
  have h_e₂_in : e₂ ∈ edgeList := List.mem_dedup.mp h_e₂_in
  simp [SimpleGraph_of_edgeList.edge_of_edge_reverse] at h_eq
  have h_eq : e₁.node1 = e₂.node1 ∧ e₁.node2 = e₂.node2 ∨ e₁.node1 = e₂.node2 ∧ e₁.node2 = e₂.node1 := by
    grind
  exact Subtype.ext <| h_nodup_con e₁ h_e₁_in e₂ h_e₂_in h_eq

theorem SimpleGraph_of_edgeList.card_edgeSet_eq_edgeList_length (edgeList : List edge) (h : edgeList ≠ []) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2) (h_nodup : edgeList.Nodup) : (SimpleGraph_of_edgeList edgeList h).edgeFinset.card = edgeList.length := by
  have h_card_sub : edgeList.toFinset.card = edgeList.length := by
    exact List.toFinset_card_of_nodup h_nodup
  have h_le : (SimpleGraph_of_edgeList edgeList h).edgeFinset.card ≤ edgeList.length := by
    have h' := Fintype.card_le_of_injective (SimpleGraph_of_edgeList.edge_of_edge edgeList h) (SimpleGraph_of_edgeList.edge_of_edge_injective edgeList h)
    simp only [Fintype.card_coe, h_card_sub] at h'
    exact h'
  have h_ge : (SimpleGraph_of_edgeList edgeList h).edgeFinset.card ≥ edgeList.length := by
    have h' := Fintype.card_le_of_injective (SimpleGraph_of_edgeList.edge_of_edge_reverse edgeList h) (SimpleGraph_of_edgeList.edge_of_edge_reverse_injective edgeList h h_nodup_con)
    simp only [Fintype.card_coe, h_card_sub] at h'
    exact h'
  exact eq_of_le_of_ge h_le h_ge

instance (edgeList : List edge) (h : edgeList ≠ []) : Fintype (fin_of_edgeList edgeList h) := by
  simp [fin_of_edgeList]
  exact Fin.fintype ((nodeList_of_edgeList_max edgeList h).id + 1)

instance (edgeList : List edge) (h : edgeList ≠ []) : Nonempty (fin_of_edgeList edgeList h) := by
  simp [fin_of_edgeList]
  exact instNonemptyOfInhabited

theorem SimpleGraph_of_edgeList.card_edgeSet (edgeList : List edge) (h : edgeList ≠ []) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2) (h_nodup : edgeList.Nodup) (h_acyclic : (SimpleGraph_of_edgeList edgeList h).IsAcyclic) : edgeList.length < (nodeList_of_edgeList_max edgeList h).id.succ := by
  have h_eq : (nodeList_of_edgeList_max edgeList h).id.succ = Fintype.card (fin_of_edgeList edgeList h) := by
    simp [fin_of_edgeList]
    exact Eq.symm (Fintype.card_fin ((nodeList_of_edgeList_max edgeList h).id + 1))
  simp only [h_eq]
  have h_tantow := h_acyclic.card_edgeFinset_le
  simp at h_tantow
  apply lt_of_eq_of_lt ?_ h_tantow
  exact (SimpleGraph_of_edgeList.card_edgeSet_eq_edgeList_length edgeList h h_nodup_con h_nodup).symm

-- geht auch ohne edgeList.Nodup, ist aber aufwändiger
theorem kruskal_helper.Nodup (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_invariant : (edgeList ++ edgesSoFar).Nodup) : (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).Nodup := by
  fun_induction kruskal_helper with
  | case1 uF edgesSoFar h_matching_edge =>
    exact h_invariant
  | case2 uF edgesSoFar e es h_matching_edge h x h' y h_matching_edge' h_x h_y updated_uF updated_edgesSoFar ih =>
    apply ih
    simp [updated_edgesSoFar, update_edgesSoFar]
    split_ifs
    · grind
    · grind

-- geht auch ohne edgeList.Nodup, abhängig von kruskal_helper.Nodup
theorem kruskal_of_edgeList.Nodup (edgeList : List edge) (h_nodup : edgeList.Nodup) : (kruskal_of_edgeList edgeList).Nodup := by
  simp [kruskal_of_edgeList, kruskal]
  apply kruskal_helper.Nodup
  simp [h_nodup]

-- geht auch ohne edgeList.nodup_con, ist aber aufwändiger
theorem kruskal_helper.nodup_con (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_invariant : ∀ e1 ∈ edgeList ++ edgesSoFar, ∀ e2 ∈ edgeList ++ edgesSoFar, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2) : ∀ e1 ∈ (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup), ∀ e2 ∈ (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup), e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2 := by
  fun_induction kruskal_helper with
  | case1 uF edgesSoFar h_matching_edge =>
    exact h_invariant
  | case2 uF edgesSoFar e es h_matching_edge h x h' y h_matching_edge' h_x h_y updated_uF updated_edgesSoFar ih =>
    apply ih
    simp [updated_edgesSoFar, update_edgesSoFar]
    split_ifs
    · grind
    · grind

-- geht auch ohne edgeList.nodup_con, abhängig von kruskal_helper.nodup_con
theorem kruskal_of_edgeList.nodup_con (edgeList : List edge) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2) : ∀ e1 ∈ kruskal_of_edgeList edgeList, ∀ e2 ∈ kruskal_of_edgeList edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2 := by
  simp [kruskal_of_edgeList, kruskal]
  apply kruskal_helper.nodup_con
  simp
  exact h_nodup_con

-- geht auch ohne edgeList.Nodup, abhängig von kruskal_helper.Nodup
-- geht auch ohne edgeList.nodup_con, abhängig von kruskal_helper.nodup_con
theorem kruskal_of_edgeList.card_edgeSet (edgeList : List edge) (h : edgeList ≠ []) (h_nodup : edgeList.Nodup) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2) : (kruskal_of_edgeList edgeList).length < (nodeList_of_edgeList_max (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h)).id.succ := SimpleGraph_of_edgeList.card_edgeSet (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) (kruskal_of_edgeList.nodup_con edgeList h_nodup_con) (kruskal_of_edgeList.Nodup edgeList h_nodup) (by exact SimpleGraph_of_kruskal.IsAcyclic edgeList h)

theorem rank_le_rank_of_mem_get_parent_path
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL uFL' : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  (h_in' : uFL' ∈ get_parent_path h_in)
  (h_ne : uFL ≠ uFL')
  : uFL.rank < uFL'.rank := by
  fun_induction get_parent_path with
  | case1 uFL h_in h_self_con =>
    simp at h_in'
    simp [h_in'] at h_ne
  | case2 uFL h_in h_self_con ih =>
    rw [get_parent_path] at h_in'
    set p := parent uFL h_in with ← h_p
    simp [h_p, ne_comm.mp h_ne] at h_in'
    revert h_in'
    split_ifs with h_p_self_con
    · simp
      intro h_in'
      simp [h_in', p, parent]
      have h := uF.matching_rank uFL h_in
      simp [h_self_con] at h
      exact h
    · simp
      intro h_in'
      have h_lt_parent : uFL.rank < p.rank := by
        simp [p, parent]
        have h := uF.matching_rank uFL h_in
        simp [h_self_con] at h
        exact h
      by_cases h_eq : uFL' = p
      · simp [h_eq]
        exact h_lt_parent
      · simp [h_p] at ih
        simp [h_eq] at h_in'
        -- have ih := ih h_in'
        apply lt_trans h_lt_parent
        apply ih
        · rw [get_parent_path]
          simp [h_p_self_con, h_eq, h_in']
        · exact ne_comm.mp h_eq

theorem not_self_con_of_mem_get_parent_path
  {nodeList : List node}
  {uF : unionFind nodeList}
  {uFL uFL' : unionFindLink nodeList}
  (h_in : uFL ∈ uF.linkList)
  (h_in' : uFL' ∈ get_parent_path h_in)
  (h_ne : uFL ≠ uFL')
  : uFL.nodeId ≠ uFL.ccId := by
  intro h_self_con
  rw [get_parent_path] at h_in'
  simp [h_self_con, ne_comm.mp h_ne] at h_in'

theorem le_two_pow_minus_one (n : Nat) : n ≤ 2^n-1 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    apply Nat.lt_of_succ_le
    apply Nat.le_of_lt_succ
    have h : (2 ^ (n + 1) - 1).succ = 2 ^ (n + 1) := by
      grind
    rw [h]
    exact Nat.lt_two_pow_self

def unionFind.rankInvariant_strict {nodeList : List node} (uF : unionFind nodeList) := ∀ uFL ∈ uF.linkList, (uF.linkList.filter (fun x => if h_x_in : x ∈ uF.linkList then uFL ∈ get_parent_path h_x_in else False)).length ≥ 2^(uFL.rank.val)

theorem unionFind.rankInvariant_of_rankInvariant_strict {nodeList : List node} {uF : unionFind nodeList} (h_rankInvariant : uF.rankInvariant_strict) : ∀ uFL ∈ uF.linkList, (uF.linkList.filter (fun x => x.rank < uFL.rank ∧ ¬x.nodeId = x.ccId)).length ≥ uFL.rank := by
  intro uFL h_in
  set rank := uFL.rank.val with ← h_rank
  revert h_rank
  induction rank generalizing uFL with
  | zero =>
    simp
  | succ rank' ih =>
    intro h_rank'
    have h : rank' + 1 ≤ 2^rank'-1+1 := by
      simp [le_two_pow_minus_one rank']
    apply le_trans h
    have h : (2 ^ rank' - 1) + 1 = 2 ^ rank' := by
      grind
    simp only [h]
    have h_length_lt : (List.filter (fun x => if h_x_in : x ∈ uF.linkList then decide (uFL ∈ get_parent_path h_x_in) else decide False) uF.linkList).length ≤ (uFL :: List.filter (fun x => decide (x.rank < uFL.rank) && !decide (x.nodeId = x.ccId)) uF.linkList).length := by
      apply nodup_length_le_length_all_mem (by simp [List.Nodup.filter, uF.nodup])
      intro x h_x_in_filter
      by_cases h_eq : x = uFL
      · simp [h_eq]
      · have h_x_in := List.mem_of_mem_filter h_x_in_filter
        have h_x_prop := (List.mem_filter.mp h_x_in_filter).right
        simp at h_x_prop
        rcases h_x_prop with ⟨_, h_x_prop⟩
        simp [h_eq, h_x_in]
        constructor
        · exact rank_le_rank_of_mem_get_parent_path h_x_in h_x_prop h_eq
        · exact not_self_con_of_mem_get_parent_path h_x_in h_x_prop h_eq
    simp at h_length_lt
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_succ_le
    simp only [Nat.succ_eq_add_one, Bool.decide_and, decide_not]
    apply le_trans ?_ h_length_lt
    apply le_trans ?_ (h_rankInvariant uFL h_in)
    simp [h_rank']
    simp [pow_add]

theorem init_unionFind.rankInvariant_strict {nodeList : List node} (h_nodup : nodeList.Nodup) : (init_unionFind nodeList h_nodup).rankInvariant_strict := by
  simp [unionFind.rankInvariant_strict, init_unionFind, init_unionFind.linkList]
  by_cases h_empty : nodeList = []
  · simp [h_empty]
  · simp [h_empty]
    intro uFL h_in
    have h_rank := init_unionFind.linkList.helper_all_rank_zero nodeList nodeList (by simp [h_empty]) uFL h_in
    simp [h_rank]
    have h_in_filter : uFL ∈ (List.filter (fun x => if h : x ∈ (init_unionFind nodeList h_nodup).linkList then decide (uFL ∈ get_parent_path (Eq.mpr_prop (Eq.refl (x ∈ (init_unionFind nodeList h_nodup).linkList)) h)) else false) (init_unionFind nodeList h_nodup).linkList) := by
      simp [init_unionFind, init_unionFind.linkList, h_empty, h_in]
      rw [get_parent_path]
      split_ifs
      · simp
      · simp
    have h_length : 1 ≤ (List.filter (fun x => if h : x ∈ (init_unionFind nodeList h_nodup).linkList then decide (uFL ∈ get_parent_path (Eq.mpr_prop (Eq.refl (x ∈ (init_unionFind nodeList h_nodup).linkList)) h)) else false) (init_unionFind nodeList h_nodup).linkList).length := by
      grind
    simp [init_unionFind, init_unionFind.linkList, h_empty] at h_length
    exact h_length

theorem update_unionFind.rankInvariant_strict {nodeList : List node} (uF : unionFind nodeList) (x y : ℕ) (h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x ∧ a.ccId = x) a) (h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y ∧ a.ccId = y) a) (h_rankInvariant : uF.rankInvariant_strict) : (update_unionFind uF x y h₁ h₂).rankInvariant_strict := by
  simp [unionFind.rankInvariant_strict, update_unionFind]
  set linklist' := (update_unionFind uF x y h₁ h₂).linkList with ← h_linklist'
  set uFLx := List.choose (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList h₁ with ← h_uFLx
  set uFLy := List.choose (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList h₂ with ← h_uFLy
  have h_uFLx_in : uFLx ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList h₁
  have h_uFLy_in : uFLy ∈ uF.linkList := List.choose_mem (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList h₂
  have h_uFLx_prop : uFLx.nodeId = x ∧ uFLx.ccId = x := List.choose_property (fun a => a.nodeId = x ∧ a.ccId = x) uF.linkList h₁
  have h_uFLy_prop : uFLy.nodeId = y ∧ uFLy.ccId = y := List.choose_property (fun a => a.nodeId = y ∧ a.ccId = y) uF.linkList h₂

  simp [h_uFLx, h_uFLy]--, h_uFLy', h_linklist']
  split_ifs with h_eq h_rank_lt
  · exact h_rankInvariant
  -- wegen h_rank_lt kürzung
  -- · set uFLx' : unionFindLink nodeList := { nodeId := uFLx.nodeId, ccId := uFLy.ccId, rank := uFLx.rank } with ← h_uFLx'
  --   have h_rank_succ_le : uFLx.rank.val.succ ≤ uFLy.rank.val := by
  --     simp [h_rank_lt]
  --   have h_rank_succ_isLt : uFLx.rank.val.succ < nodeList.length := by
  --     simp [Nat.lt_of_le_of_lt h_rank_succ_le]
  --   set uFLy' : unionFindLink nodeList := { nodeId := uFLy.nodeId, ccId := uFLy.ccId, rank := ⟨max (uFLy.rank.val) (uFLx.rank.val + 1), by simp [h_rank_succ_isLt]⟩ } with ← h_uFLy'
  --   simp [h_uFLy', h_uFLx']
  --   simp [update_unionFind, h_uFLx, h_uFLy, h_uFLx', h_uFLy'] at h_linklist'
  --   simp [h_eq, h_rank_lt] at h_linklist'
  --   have h_uFLx'_in : uFLx' ∈ linklist' := by
  --     simp [← h_linklist']
  --     apply mem_set_of_ne_index
  --     · apply List.mem_set
  --       simp [List.idxOf_lt_length_iff, h_uFLx_in]
  --     · have h : List.idxOf uFLx' (uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx') = List.idxOf uFLx uF.linkList := by
  --         apply idxOf_set
  --         · intro j h_j
  --           have h_not_in : ¬uFLx' ∈ uF.linkList := by
  --             intro h_contra
  --             have h := uF.matching_ccId uFLx h_uFLx_in
  --             rcases h with ⟨z, h_z, _⟩
  --             have h' := uF.matching_nodeId z h_z.left
  --             rcases h' with ⟨w, h_w, h_unique⟩
  --             simp [h_z.right] at h_unique
  --             have h_eq1 := h_unique uFLx h_uFLx_in (by simp [h_uFLx_prop])
  --             have h_eq2 := h_unique uFLx' h_contra (by simp [h_uFLx_prop, uFLx'])
  --             grind
  --           grind
  --         · simp [List.idxOf_lt_length_iff, h_uFLx_in]
  --       simp [h]
  --       intro h_contra
  --       have h : uFLx = uF.linkList[List.idxOf uFLx uF.linkList]'(by simp [List.idxOf_lt_length_iff, h_uFLx_in]) := by
  --         simp
  --       simp [h_contra] at h
  --       simp [h, h_uFLy_prop] at h_uFLx_prop
  --       simp [h_uFLx_prop] at h_eq
  --   intro uFL h_uFL_in
  --   simp [unionFind.rankInvariant_strict] at h_rankInvariant
  --   by_cases h_uFL_eq : uFL = uFLx'
  --   · have h := h_rankInvariant uFLx h_uFLx_in
  --     set l1 := List.filter (fun x => if h : x ∈ uF.linkList then decide (uFLx ∈ get_parent_path h) else false) uF.linkList with ← h_l1
  --     set l2 := List.filter (fun x_1 => if h : x_1 ∈ linklist' then decide (uFL ∈ get_parent_path h) else false) ((uF.linkList.set (List.idxOf uFLx uF.linkList) uFLx').set (List.idxOf uFLy uF.linkList) uFLy') with ← h_l2
  --     simp [update_unionFind, linklist', h_eq, h_uFLx, h_uFLy, h_uFLx', h_uFLy'] at h_l2
  --     simp [h_rank_lt] at h_l2
  --     simp [h_l2]
  --     simp [h_uFL_eq]
  --     have h_rank_eq : 2 ^ uFLx'.rank.val = 2 ^ uFLx.rank.val := by
  --       simp [uFLx']
  --     apply le_of_eq_of_le h_rank_eq
  --     apply le_trans h
  --     let f : l1.toFinset → l2.toFinset := fun uFL1 =>
  --       if h_uFL1_eq : uFL1 = uFLx
  --         then
  --           have h_uFLx'_in_finset : uFLx' ∈ l2.toFinset := by
  --             simp [l2, h_uFLx'_in]
  --             constructor
  --             · simp [← h_linklist'] at h_uFLx'_in
  --               exact h_uFLx'_in
  --             · rw [get_parent_path]
  --               grind
  --           ⟨uFLx', h_uFLx'_in_finset⟩
  --         else
  --           have h_uFL1_in_finset : ↑uFL1 ∈ l2.toFinset := by
  --             have h_uFL1_in := uFL1.mem
  --             simp [l1] at h_uFL1_in
  --             rcases h_uFL1_in with ⟨h_uFL1_in, h_uFL1_prop⟩
  --             simp [l2]
  --             constructor
  --             · sorry
  --             · sorry
  --           ⟨uFL1, h_uFL1_in_finset⟩
  --     apply nodup_length_le_length_of_injectiv_fun f
  --     · exact List.Nodup.filter _ uF.nodup
  --     · sorry
  --   · sorry
  · simp [h_rank_lt]
    set uFLx' : unionFindLink nodeList := { nodeId := uFLy.nodeId, ccId := uFLx.ccId, rank := uFLy.rank } with ← h_uFLx'
    -- set uFLy' : unionFindLink nodeList := { nodeId := uFLx.nodeId, ccId := uFLx.ccId, rank := uFLx.rank } with ← h_uFLy'
    intro uFL h_uFL_in
    have h_idx_uFLx_lt : List.idxOf uFLx uF.linkList < uF.linkList.length := by
      exact List.idxOf_lt_length_of_mem h_uFLx_in
    have h_idx_uFLy_lt : List.idxOf uFLy uF.linkList < uF.linkList.length := by
      exact List.idxOf_lt_length_of_mem h_uFLy_in
    have h_ne : uFLx ≠ uFLx' := by
      grind
    have h_ne_idx : List.idxOf uFLx uF.linkList ≠ List.idxOf uFLy uF.linkList := by
      have : uFLx = uF.linkList[List.idxOf uFLx uF.linkList]'h_idx_uFLx_lt := by
        simp
      grind
    have h_eq_idx := idxOf_eq_idxOf_set h_ne h_ne_idx
    simp [← h_eq_idx, h_uFLx', set_eq_self] at h_uFL_in ⊢
    sorry
  · sorry

theorem max_rank {nodeList : List node} {uF : unionFind nodeList} (h_rankInvariant : uF.rankInvariant_strict) : ∀ uFL ∈ uF.linkList, uFL.rank.val ≤ Nat.log 2 nodeList.length := by
  intro uFL h_uFL_in
  by_cases h_contra : uFL.rank.val > Nat.log 2 nodeList.length
  · simp [unionFind.rankInvariant_strict] at h_rankInvariant
    have h := h_rankInvariant uFL h_uFL_in
    have h : 2 ^ uFL.rank.val ≤ uF.linkList.length := by
      apply le_trans h
      simp [List.length_filter_le]
    have h' : 2 ^ (Nat.log 2 nodeList.length + 1) ≤ 2 ^ uFL.rank.val := by
      simp [Nat.pow_le_pow_iff_right]
      exact h_contra
    have h := le_trans h' h
    simp [uF.matching_length.symm] at h
    have h' := Nat.lt_pow_succ_log_self (b := 2) (by simp) nodeList.length
    simp at h'
    have h := lt_of_le_of_lt h h'
    simp at h
  · simp at h_contra
    exact h_contra

-- #min_imports
