import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenRegionalProfile
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
open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

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
    (boundary : SourceCrosscutBoundaryData data pair) := by
  exact rotationSystem data.toRotationSystem
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
    (coloring : data.toRotationSystem.EdgeColoring Color) := by
  exact inheritedColoring data.toRotationSystem
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

/-- The source boundary profile's raw regional edges are genuinely carried by
the selected deletion component.  This is the structural bridge that permits
its five finite coordinates to be read from the literal open tangle. -/
theorem sourceCrosscutBoundaryProfileData_regionEdges_subset
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
    (pair.sourceCrosscutBoundaryProfileData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) := by
  intro edge hedge
  simpa [sourceCrosscutBoundaryProfileData,
    vertexSetBoundaryGraphCutDataWithIndexing] using hedge

/-- Read a regional ambient edge from an arbitrary coloring of the literal
open source component.  A region edge is represented by its endpoint-side
dart; values outside the component are zero and cannot enter a profile port. -/
noncomputable def sourceCrosscutLiteralColorOnVertexSide
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) :
    G.edgeSet → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) then
      dartColor data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.sourceCrosscutOpenRoot data boundary) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem
          (pair.componentSide boundary.component) edge hedge,
          vertexSideDart_mem_inside data.toRotationSystem
            (pair.componentSide boundary.component) edge hedge⟩)
    else 0

/-- A regional edge receives a nonzero color from every literal open Tait
coloring. -/
theorem sourceCrosscutLiteralColorOnVertexSide_ne_zero
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)) :
    pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring edge ≠ 0 := by
  rw [sourceCrosscutLiteralColorOnVertexSide]
  simp only [dif_pos hedge]
  exact dartColor_ne_zero data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary) coloring hcoloring _

/-- The source's full finite five-coordinate profile, now read from a literal
open coloring of the component bounded by the paired transversals. -/
noncomputable def sourceCrosscutLiteralOpenProfile
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring) :=
  let hregion := pair.sourceCrosscutBoundaryProfileData_regionEdges_subset
    data boundary
  let hports := pair.sourceCrosscutBoundaryProfileData_portsInRegion
    data boundary
  (pair.sourceCrosscutBoundaryProfileData data boundary).regionalProfile
    (pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutLiteralColorOnVertexSide_ne_zero data boundary
        coloring hcoloring (hregion (hports (.inl crossing))))

/-- The color coordinate of the literal open profile is exactly the color of
the selected component-side edge in its open tangle. -/
@[simp]
theorem sourceCrosscutLiteralOpenProfile_edgeColor_toColor
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring)
    (crossing : Fin (Fintype.card (VertexSetCrossingEdge
      data.toRotationSystem (pair.componentSide boundary.component)))) :
    ((pair.sourceCrosscutLiteralOpenProfile data boundary coloring hcoloring).edgeColor
      crossing).toColor =
      pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
        ((pair.sourceCrosscutBoundaryProfileData data boundary).crossingEdge crossing) := by
  unfold sourceCrosscutLiteralOpenProfile
  exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ crossing

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
