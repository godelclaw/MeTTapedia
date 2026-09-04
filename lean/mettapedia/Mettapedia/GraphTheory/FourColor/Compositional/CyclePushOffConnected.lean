import Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicThreeCutConnectedSides

/-!
# Connected filled sides of cycle push-off cuts

The filled side of an exact face cut around a simple primal cycle is
connected whenever the ambient graph is connected.  The point is elementary
but useful: all vertices of the cycle lie in one induced component, while an
edge leaving any other filled-side component would have to cross the filled
side.  Every such crossing edge is incident to the cycle, forcing the two
components to meet.

This is the connectivity half of the geometric separator interface.  The
open complementary side can still have several components and is handled by
rooted saturation.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut

open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.Embedding
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The cycle-filled side of a push-off separator is an induced connected
subgraph. -/
theorem induce_filledCycleSide_connected
    (data : Data G)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (_hcycle : cycle.IsCycle)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) :
    (G.induce (cut.filledCycleSide data cycle selected)).Connected := by
  let side : V → Prop := cut.filledCycleSide data cycle selected
  have hbase : side base :=
    cut.mem_filledCycleSide_of_mem_support data cycle selected (by simp)
  let component := inducedReachableSide G side base hbase
  have hcycleComponent : ∀ vertex, vertex ∈ cycle.support → component vertex := by
    intro vertex hvertex
    let hvertexSide : side vertex :=
      cut.mem_filledCycleSide_of_mem_support data cycle selected hvertex
    refine ⟨hvertexSide, ?_⟩
    let path := cycle.takeUntil vertex hvertex
    have hpathSupport : ∀ point ∈ path.support, side point := by
      intro point hpoint
      exact cut.mem_filledCycleSide_of_mem_support data cycle selected
        (cycle.support_takeUntil_subset_support hvertex hpoint)
    let insidePath := path.induce side hpathSupport
    exact ⟨by simpa [insidePath, path] using insidePath⟩
  have hall : ∀ vertex, side vertex → component vertex := by
    intro vertex hvertex
    by_contra hnotComponent
    let otherComponent := inducedReachableSide G side vertex hvertex
    have hotherVertex : otherComponent vertex :=
      inducedReachableSide_root side vertex hvertex
    have hnotOtherBase : ¬ otherComponent base := by
      intro hotherBase
      apply hnotComponent
      rcases hotherBase with ⟨_hbase, hvertexBase⟩
      exact ⟨hvertex, by simpa [component, otherComponent] using hvertexBase.symm⟩
    rcases hconnected vertex base with ⟨ambientWalk⟩
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
        otherComponent ambientWalk hotherVertex hnotOtherBase with
      ⟨edge, _hedgeWalk, hcrossOther⟩
    have hcrossSide : EdgeCrossesVertexSide G side edge :=
      edgeCrossesVertexSide_of_inducedReachableSide
        side vertex hvertex edge hcrossOther
    rcases exists_cycle_endpoint_of_edgeCrosses_filledCycleSide
        data hrotation cycle cut selected edge hcrossSide with
      ⟨cycleVertex, hcycleVertexEdge, hcycleVertex⟩
    rcases hcrossOther with
      ⟨inner, outer, hinnerEdge, houterEdge, hinnerOther, houterOther⟩
    have hverticesNe : inner ≠ outer := by
      intro heq
      exact houterOther (heq ▸ hinnerOther)
    have hedgePair : (edge : Sym2 V) = s(inner, outer) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hinnerEdge houterEdge hverticesNe
    have houterNotSide : ¬ side outer := by
      intro houterSide
      have hadj : (G.induce side).Adj
          ⟨inner, inducedReachableSide_mem hinnerOther⟩
          ⟨outer, houterSide⟩ :=
        (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgePair] using edge.2)
      exact houterOther
        ⟨houterSide, hinnerOther.choose_spec.trans hadj.reachable⟩
    have hcycleVertexSide : side cycleVertex :=
      cut.mem_filledCycleSide_of_mem_support data cycle selected hcycleVertex
    have hcycleVertexEq : cycleVertex = inner := by
      have hm : cycleVertex = inner ∨ cycleVertex = outer := by
        simpa [hedgePair] using hcycleVertexEdge
      rcases hm with hin | hout
      · exact hin
      · exact (houterNotSide (hout ▸ hcycleVertexSide)).elim
    have hinnerMain : component inner := by
      simpa [hcycleVertexEq] using hcycleComponent cycleVertex hcycleVertex
    apply hnotComponent
    rcases hinnerMain with ⟨_hinnerSide, hbaseInner⟩
    rcases hinnerOther with ⟨_hinnerSide', hvertexInner⟩
    exact ⟨hvertex, by
      simpa [component, otherComponent] using hbaseInner.trans hvertexInner.symm⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨base, hbase⟩, ?_⟩
  intro vertex
  rcases hall vertex.1 vertex.2 with ⟨_hvertex, hreachable⟩
  simpa [component] using hreachable

end

end Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut
