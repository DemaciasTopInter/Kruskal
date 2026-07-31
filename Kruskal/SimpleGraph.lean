import Mathlib

universe u

variable {α : Type u} {a b : α}

theorem reachable_of_le_reachble (G H : SimpleGraph α) (h_le : G ≤ H) : G.Reachable a b → H.Reachable a b := by
  exact fun a_1 => SimpleGraph.Reachable.mono h_le a_1

theorem Walk.symm (G : SimpleGraph α) : Nonempty (G.Walk a b) → Nonempty (G.Walk b a) := by
  exact fun a_1 =>
    (fun {α β} f g => (Nonempty.congr f g).mpr) (fun a_2 => id a_2.reverse)
      (fun a_2 => id a_2.reverse) a_1

theorem Reachable.symm (G : SimpleGraph α) : G.Reachable a b → G.Reachable b a := by
  exact SimpleGraph.Reachable.symm
