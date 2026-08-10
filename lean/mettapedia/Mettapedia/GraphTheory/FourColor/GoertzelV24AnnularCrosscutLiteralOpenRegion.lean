import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionTaitInheritance

/-!
# Literal open tangles from paired source crosscuts

The paired simple crosscuts already determine an exact deletion component and
its exposed primal edges.  This file turns that component into the literal
open rotation system used by the compositional proof's `Count` semantics.
It is deliberately sourced from `SourceCrosscutBoundaryData`: no chord wall
is substituted for a transversal and no boundary state is supplied by fiat.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

local instance sourceOpenRegionRetainedVertexFintype (side : Finset V) :
    Fintype (GoertzelV24OpenRegionRotation.RetainedVertex
      (fun vertex : V => vertex ∈ side)) :=
  GoertzelV24OpenRegionRotation.retainedVertexFintype _

local instance sourceOpenRegionRetainedVertexDecidableEq (side : Finset V) :
    DecidableEq (GoertzelV24OpenRegionRotation.RetainedVertex
      (fun vertex : V => vertex ∈ side)) :=
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq _

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The distinguished ambient outer dart lies in the selected outer deletion
component, so it supplies a concrete root for that literal open tangle. -/
noncomputable def sourceCrosscutOpenRoot
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
    (boundary : SourceCrosscutBoundaryData data pair) :
    Dart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) :=
  Sum.inl ⟨data.toRotationSystem.outer, boundary.outer_kept⟩

/-- The actual open rotation system bounded by the two source transversals.
Its old vertices are precisely the selected deletion component and its fresh
degree-one vertices are precisely the component's exposed boundary darts. -/
noncomputable def sourceCrosscutOpenRegion
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
    (boundary : SourceCrosscutBoundaryData data pair) :
    RotationSystem
      (Vertex data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component))
      (rewiredDartSystem data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.sourceCrosscutOpenRoot data boundary)).Edge :=
  rotationSystem data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary)

/-- Restrict an ambient proper edge coloring to the literal source open
tangle. -/
noncomputable def sourceCrosscutInheritedOpenColoring
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
    (coloring : data.toRotationSystem.EdgeColoring Color) :
    (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color :=
  inheritedColoring data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary) coloring

/-- The restriction of an ambient Tait coloring is an actual Tait coloring
of the source component's literal open tangle. -/
theorem sourceCrosscutInheritedOpenColoring_isTait
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
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      (pair.sourceCrosscutInheritedOpenColoring data boundary coloring) := by
  exact inheritedColoring_isTait data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary) coloring hcoloring

/-- At every exposed component-side dart, the literal open tangle's boundary
stub reads exactly the ambient color of the primal edge it opens. -/
theorem sourceCrosscutInheritedOpenColoring_stubColor
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
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (exposed : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component)) :
    pair.sourceCrosscutInheritedOpenColoring data boundary coloring
        ((pair.sourceCrosscutOpenRegion data boundary).edgeOf (Sum.inr exposed)) =
      coloring (data.toRotationSystem.edgeOf exposed.1.1) := by
  change inheritedColoring data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component)
      (pair.sourceCrosscutOpenRoot data boundary) coloring
      ((rotationSystem data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.sourceCrosscutOpenRoot data boundary)).edgeOf (Sum.inr exposed)) = _
  exact inheritedColoring_edgeOf data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary) coloring (Sum.inr exposed)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
