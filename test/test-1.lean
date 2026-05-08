import Kruskal

open Kruskal

def edgeList : List edge := [
    ⟨0, 0, 5, 14, by simp⟩,
    ⟨1, 0, 2, 9, by simp⟩,
    ⟨2, 0, 1, 1, by simp⟩,
    ⟨3, 4, 5, 9, by simp⟩,
    ⟨4, 3, 5, 2, by simp⟩,
    ⟨5, 1, 2, 10, by simp⟩,
    ⟨6, 3, 4, 6, by simp⟩,
    ⟨7, 2, 3, 11, by simp⟩,
    ⟨8, 1, 3, 15, by simp⟩
  ]

#eval kruskal_of_edgeList edgeList
#eval nodeList_of_edgeList edgeList
