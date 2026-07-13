-- Folgendes ist von Johannes Tantow

import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

noncomputable instance edgeSet_Fintype [Fintype V] {G : SimpleGraph V} : Fintype (G.edgeSet) :=
  Fintype.ofFinite ↑G.edgeSet

lemma IsAcyclic.card_edgeFinset_le [Fintype V] [Nonempty V] (hG : G.IsAcyclic) : Finset.card G.edgeFinset + 1 ≤ Fintype.card V := by
  obtain ⟨T, h₁, h₂, hT⟩ := Connected.exists_isTree_le_of_le_of_isAcyclic connected_top (OrderTop.le_top G) hG
  rw [← IsTree.card_edgeFinset hT]
  refine Nat.add_le_add_right (Finset.card_le_card (edgeFinset_mono h₁)) 1
