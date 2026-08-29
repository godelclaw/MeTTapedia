import Mettapedia.Combinatorics.Matching.Loopless

/-!
# Support neighbourhoods of coloured matching weights

The support graph forgets colours and remembers whether some coloured entry over
an unordered vertex pair is nonzero. Loop erasure preserves this graph.
-/

namespace MatchingSupport

open MatchingLoopless

variable {V C R : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The vertices joined to `u` by at least one nonzero coloured weight. -/
noncomputable def liveNeighbours [Zero R]
    (W : Sym2 (V × C) → R) (u : V) : Finset V :=
  (Finset.univ.erase u).filter
    (fun y => ∃ a b : C, W s((u, a), (y, b)) ≠ 0)

lemma mem_liveNeighbours [Zero R] {W : Sym2 (V × C) → R} {u y : V} :
    y ∈ liveNeighbours W u ↔
      y ≠ u ∧ ∃ a b : C, W s((u, a), (y, b)) ≠ 0 := by
  classical
  simp [liveNeighbours, Finset.mem_filter, Finset.mem_erase]

/-- Removing loop weights preserves every support neighbourhood. -/
lemma liveNeighbours_deloop [CommSemiring R]
    (W : Sym2 (V × C) → R) (u : V) :
    liveNeighbours (deloop W) u = liveNeighbours W u := by
  ext y
  simp only [mem_liveNeighbours]
  constructor
  · rintro ⟨hy, a, b, hab⟩
    exact ⟨hy, a, b, by rwa [deloop_off hy.symm a b] at hab⟩
  · rintro ⟨hy, a, b, hab⟩
    exact ⟨hy, a, b, by rwa [deloop_off hy.symm a b]⟩

end MatchingSupport
