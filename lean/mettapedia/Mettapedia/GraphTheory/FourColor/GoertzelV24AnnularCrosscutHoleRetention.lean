import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut

/-!
# Retaining container boundaries across a source crosscut

The source splice keeps both annular holes outside the pumped strip.  At the
graph level, the needed fact is simple but indispensable: a closed container
walk which avoids the primal cut cannot change deletion component.  Thus one
retained anchor keeps its entire boundary on the retained side.

This is generic finite-deletion theory, not a configuration or covering
argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the finite edge carrier aligned with the source crosscut API. -/
local instance sourceCrosscutHoleRetentionGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Every vertex of an ambient walk that avoids a source crosscut's primal
support lies on the same retained side as its root.  This is the component
form of the source requirement that a container boundary remains outside the
pumped region. -/
theorem SourceCrosscutBoundaryData.walk_support_subset_componentSide_of_avoids_primalCut
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    {root : V} (walk : G.Walk root root)
    (hroot : root ∈ boundary.component.supp)
    (havoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges →
      edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data))
    {vertex : V} (hvertex : vertex ∈ walk.support) :
    vertex ∈ pair.componentSide boundary.component := by
  let walkPrefix := walk.takeUntil vertex hvertex
  have hprefixAvoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walkPrefix.edges →
      edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges data) := by
    intro edge hedge
    exact havoid edge
      (walk.edges_takeUntil_subset_edges hvertex hedge)
  have hside := component_side_iff_of_walk_avoiding_removed
    (pair.primalCutEdges data) boundary.component walkPrefix hprefixAvoid
  exact (pair.mem_componentSide_iff boundary.component vertex).2 (hside.mp hroot)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
