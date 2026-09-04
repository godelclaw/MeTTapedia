import Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffConnected
import Mettapedia.GraphTheory.FourColor.RootedCutSaturation

/-!
# Nesting cycle push-off shores at one exterior root

Rooted saturation should preserve the planar nesting carried by a family of
cycle separators.  The essential graph-theoretic observation is this: if a
connected outer complement avoids an inner separator cycle, then every walk
from the common exterior root through that complement stays on the exterior
side of the inner exact face cut.  Hence the rooted closure of the inner side
is contained in the outer side.

The theorem below isolates that observation from residual-return geometry.
Its only geometric premise is the literal containment of the inner cycle's
support in the outer side.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut

open GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.Embedding
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If a connected outer complement avoids an inner cycle, then saturating
the inner filled side at their common exterior root remains inside the outer
side. -/
theorem closureSide_filledCycleSide_subset_of_cycle_support_subset
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (outerSide : V → Prop)
    (houterComplementConnected :
      (G.induce (fun vertex => ¬ outerSide vertex)).Connected)
    (outsideRoot : V)
    (hrootInner : ¬ cut.filledCycleSide data cycle selected outsideRoot)
    (hrootOuter : ¬ outerSide outsideRoot)
    (hcycleInside : ∀ vertex, vertex ∈ cycle.support → outerSide vertex) :
    ∀ vertex,
      closureSide (G := G) (cut.filledCycleSide data cycle selected)
          outsideRoot hrootInner vertex →
        outerSide vertex := by
  intro vertex hclosure
  by_contra hvertexOuter
  have hreachableOuter :
      (G.induce (fun point => ¬ outerSide point)).Reachable
        ⟨outsideRoot, hrootOuter⟩ ⟨vertex, hvertexOuter⟩ :=
    houterComplementConnected.preconnected _ _
  rcases hreachableOuter with ⟨outerWalk⟩
  let ambientWalk : G.Walk outsideRoot vertex :=
    (outerWalk.map
      (SimpleGraph.Embedding.induce
        (fun point => ¬ outerSide point)).toHom).copy
      rfl rfl
  have hambientAvoids : ∀ point ∈ ambientWalk.support,
      point ∉ cycle.support := by
    intro point hpoint hcycle
    have hmapped : point ∈
        (outerWalk.map
          (SimpleGraph.Embedding.induce
            (fun vertex => ¬ outerSide vertex)).toHom).support := by
      simpa only [ambientWalk, SimpleGraph.Walk.support_copy] using hpoint
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hmapped
    rcases hmapped with ⟨source, _hsource, hsource⟩
    have hnotOuter : ¬ outerSide source.1 := source.2
    have hsourceValue : source.1 = point := by
      simpa using hsource
    exact hnotOuter (hsourceValue ▸ hcycleInside point hcycle)
  have hambientOutside : ∀ point ∈ ambientWalk.support,
      ¬ cut.filledCycleSide data cycle selected point := by
    intro point hpoint hpointSide
    have hprefAvoid : ∀ current ∈
        (ambientWalk.takeUntil point hpoint).support,
        current ∉ cycle.support := by
      intro current hcurrent
      exact hambientAvoids current
        (ambientWalk.support_takeUntil_subset_support hpoint hcurrent)
    exact hrootInner
      ((filledCycleSide_iff_of_walk_avoids_support data hrotation cycle cut
        selected (ambientWalk.takeUntil point hpoint) hprefAvoid).2 hpointSide)
  have hvertexInner :
      ¬ cut.filledCycleSide data cycle selected vertex :=
    hambientOutside vertex ambientWalk.end_mem_support
  apply hclosure
  refine ⟨hvertexInner, ?_⟩
  refine ⟨(ambientWalk.induce
      (fun point => ¬ cut.filledCycleSide data cycle selected point)
      hambientOutside).copy ?_ ?_⟩
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

end

end Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut
