import MettapediaFourColor.ThreeBlockDiskBoundary
import MettapediaFourColor.CyclicCoreStars

/-! # Complete core rows exclude extra ambient edges

The source row is closed under the actual vertex rotation. Vertexwise
cyclicity therefore forces every ambient neighbour of a core vertex to
occur in that row. No degree equality or complete-star assumption is used.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem core_nonempty : ∀ i : Fin 18, 11 ≤ i.val → ∃ j, upper.graph.Adj i j := by
  decide +kernel

theorem core_predecessor : ∀ i j : Fin 18, 11 ≤ i.val → upper.graph.Adj i j →
    ∃ k, upper.graph.Adj i k ∧ Turn i k j := by decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data)

omit [DecidableEq V] in
/-- An exact cyclic core reading already determines its complete ambient star. -/
theorem core_stars (cyclic : data.IsVertexwiseCyclic)
    (i : Fin 18) (hi : 11 ≤ i.val) (v : V) (hv : G.Adj (r.hom i) v) :
    ∃ j, r.hom j = v ∧ upper.graph.Adj i j := by
  apply CyclicCoreStars.covers data cyclic r.hom i (core_nonempty i hi) ?_ v hv
  intro j hj
  obtain ⟨k, hk, turn⟩ := core_predecessor i j hi hj
  exact ⟨k, hk, r.turn i k j turn⟩

end FourColor.ThreeBlockDiskBoundary
