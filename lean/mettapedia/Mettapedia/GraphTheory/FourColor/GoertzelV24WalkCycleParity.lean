import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleSpace

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WalkCycleParity

open GoertzelV24PrimalCycleSpace
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The mod-two traversal count of each graph edge in a walk. -/
def walkEdgeParity {start finish : V} (walk : G.Walk start finish) :
    G.edgeSet → F2 :=
  fun edge => (walk.edges.count edge.1 : F2)

/-- Adding the first step of a walk adds the corresponding edge basis vector
to its mod-two edge-parity vector. -/
theorem walkEdgeParity_cons {start next finish : V}
    (hadj : G.Adj start next) (tail : G.Walk next finish) :
    walkEdgeParity (Walk.cons hadj tail) =
      Pi.single
        (⟨s(start, next), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet) 1 +
        walkEdgeParity tail := by
  funext edge
  by_cases hedge : edge.1 = s(start, next)
  · have hedgeSubtype :
        edge =
          (⟨s(start, next), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet) :=
      Subtype.ext hedge
    subst edge
    simp [walkEdgeParity, Walk.edges_cons, add_comm]
  · have hedgeSubtype :
        edge ≠
          (⟨s(start, next), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet) := by
      intro heq
      exact hedge (congrArg Subtype.val heq)
    have hhead : s(start, next) ≠ edge.1 := Ne.symm hedge
    simp [walkEdgeParity, Walk.edges_cons, hhead, hedgeSubtype]

/-- The incidence boundary of one edge basis vector is the sum of its two
endpoint basis vectors. -/
theorem f2IncidenceMatrix_mulVec_single_edge {left right : V}
    (hadj : G.Adj left right) :
    (f2IncidenceMatrix G).mulVecLin
        (Pi.single
          (⟨s(left, right), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet) 1) =
      Pi.single left 1 + Pi.single right 1 := by
  funext vertex
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  by_cases hleft : vertex = left
  · by_cases hright : vertex = right
    · exact (hadj.ne (hleft.symm.trans hright)).elim
    · simp [f2IncidenceMatrix, Pi.single_apply, Sym2.mem_iff,
        hleft, hright, hadj.ne]
  · by_cases hright : vertex = right <;>
      simp [f2IncidenceMatrix, Pi.single_apply, Sym2.mem_iff,
        hleft, hright, hadj.ne, hadj.ne.symm]

/-- The incidence boundary of a walk's edge-parity vector consists exactly
of its two endpoints. -/
theorem f2IncidenceMatrix_mulVec_walkEdgeParity {start finish : V}
    (walk : G.Walk start finish) :
    (f2IncidenceMatrix G).mulVecLin (walkEdgeParity walk) =
      Pi.single start 1 + Pi.single finish 1 := by
  induction walk with
  | nil =>
      funext vertex
      simp [walkEdgeParity, Matrix.mulVecLin_apply, Matrix.mulVec,
        dotProduct, zmod2_add_self]
  | @cons start next finish hadj tail ih =>
      rw [walkEdgeParity_cons hadj tail, LinearMap.map_add,
        f2IncidenceMatrix_mulVec_single_edge hadj, ih]
      funext vertex
      simp only [Pi.add_apply]
      let leftValue : F2 :=
        (Pi.single start (1 : F2) : V → F2) vertex
      let middleValue : F2 :=
        (Pi.single next (1 : F2) : V → F2) vertex
      let rightValue : F2 :=
        (Pi.single finish (1 : F2) : V → F2) vertex
      change (leftValue + middleValue) + (middleValue + rightValue) =
        leftValue + rightValue
      calc
        (leftValue + middleValue) + (middleValue + rightValue) =
            leftValue + (middleValue + middleValue) + rightValue := by abel
        _ = leftValue + rightValue := by
          rw [zmod2_add_self]
          simp

/-- The mod-two edge-parity vector of a closed walk is a genuine graph cycle. -/
theorem walkEdgeParity_mem_f2CycleSpace_of_closed {vertex : V}
    (walk : G.Walk vertex vertex) :
    walkEdgeParity walk ∈ f2CycleSpace G := by
  rw [f2CycleSpace, LinearMap.mem_ker,
    f2IncidenceMatrix_mulVec_walkEdgeParity]
  funext other
  simp [zmod2_add_self]

/-- An edge absent from a walk has zero coordinate in its mod-two parity
vector. -/
theorem walkEdgeParity_apply_eq_zero_of_not_mem_edges
    {start finish : V} (walk : G.Walk start finish) (edge : G.edgeSet)
    (hnot : edge.1 ∉ walk.edges) :
    walkEdgeParity walk edge = 0 := by
  simp [walkEdgeParity, List.count_eq_zero.2 hnot]

end

end GoertzelV24WalkCycleParity

end Mettapedia.GraphTheory.FourColor
