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

def SimpleGraph_of_edgeSet (edgeSet : Set edge) : SimpleGraph (Fin n) where
  Adj (a b) := ∃ e ∈ edgeSet, (e.node1 = a.val ∧ e.node2 = b.val) ∨ (e.node1 = b.val ∧ e.node2 = a.val)
  symm := by
    simp [Symmetric]
    intro a b e h_e_in h_adj
    refine ⟨e, h_e_in, h_adj.symm⟩
  loopless := by
    simp [irrefl_def]
    intro a e h_e h_eq₁ h_eq₂
    have h_lt := e.nodesLt
    simp [h_eq₁, h_eq₂] at h_lt

def SimpleGraph_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph (fin_of_edgeList edgeList h) := SimpleGraph_of_edgeSet {e | e ∈ edgeList}

theorem kruskal_nonempty (edgeList : List edge) (h : edgeList ≠ []) : kruskal_of_edgeList edgeList ≠ [] := by sorry

def SimpleGraph_of_kruskal (edgeList : List edge) (h : edgeList ≠ []) := SimpleGraph_of_edgeList (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h)

theorem nodeList_of_kruskal_perm (edgeList : List edge) : List.Perm (nodeList_of_edgeList (kruskal_of_edgeList edgeList)) (nodeList_of_edgeList edgeList) := by sorry

theorem SimpleGraph_of_kruskal_IsSubgraph (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h) ≤ (SimpleGraph_of_edgeList edgeList h) := by sorry

theorem SimpleGraph_of_kruskal_IsAcyclic (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h).IsAcyclic := by sorry

theorem SimpleGraph_of_kruskal_IsEqReachable (edgeList : List edge) (h : edgeList ≠ []) : ∀ (x y), (SimpleGraph_of_edgeList edgeList h).Reachable x y ↔ (SimpleGraph_of_kruskal edgeList h).Reachable x y := by sorry

theorem SimpleGraph_of_kruskal_IsSpanningTree (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph.IsSpanningTree (SimpleGraph_of_kruskal edgeList h) (SimpleGraph_of_edgeList edgeList h) := by sorry

def cost_of_edgeList : List edge → Nat
  | [] => 0
  | e :: edgeList => e.cost + cost_of_edgeList edgeList

def minimalSpanninTree_of_edgeList (edgeList : List edge) (h₁ : edgeList ≠ []) (G := SimpleGraph_of_edgeList edgeList h₁) (minEdgeList : List edge) (h₂ : minEdgeList ≠ []) (h₃ : SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList minEdgeList h₂)) (h₄ : ∀ x ∈ minEdgeList, x ∈ edgeList) : Prop := ∀ (el : List edge), (h₅ : el ≠ []) → (h₆ : ∀ x ∈ el, x ∈ edgeList) → SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList el h₅) → (cost_of_edgeList el) ≥ (cost_of_edgeList minEdgeList)

theorem kruskal_minimalSpanninTree_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : minimalSpanninTree_of_edgeList edgeList h (SimpleGraph_of_edgeList edgeList h₁) (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) := by sorry
