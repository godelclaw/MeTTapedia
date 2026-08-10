import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutBoundaryWordGluing

/-!
# Literal profile boundary words for source crosscuts

The compositional counting semantics reads its boundary-color coordinate from
the same literal open tangle that is used by the source crosscut gluing
theorem.  This file identifies those two readings at an exposed boundary dart.
It deliberately establishes only the boundary-color coordinate; connectivity
and capped face-progress remain the separate finite-profile coordinates of
`Count`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionColorGluing
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- On a literal source component, the profile reader chooses the same color
as the actual open-boundary reader at every exposed dart.  The only possible
other dart over the same edge is its opposite, which lies outside the chosen
component and is excluded by the boundary-dart witness. -/
theorem sourceCrosscutLiteralColorOnVertexSide_eq_boundaryDartColor
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
    (exposed : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component)) :
    pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
      (data.toRotationSystem.edgeOf exposed.1.1) =
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.sourceCrosscutOpenRoot data boundary) coloring
        exposed.1.1 exposed.1.2 := by
  let inside := pair.componentSide boundary.component
  let edge := data.toRotationSystem.edgeOf exposed.1.1
  have hcrossing : edge ∈ vertexSetCrossingEdges data.toRotationSystem inside := by
    dsimp [edge, inside]
    exact boundaryDart_edge_mem_vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component) exposed
  have hregion : edge ∈ vertexSetRegionEdges data.toRotationSystem inside :=
    vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem inside hcrossing
  rw [sourceCrosscutLiteralColorOnVertexSide, dif_pos hregion]
  change dartColor data.toRotationSystem
      (fun vertex => vertex ∈ inside)
      (pair.sourceCrosscutOpenRoot data boundary) coloring
      (Sum.inl ⟨vertexSideDart data.toRotationSystem inside edge hregion,
        vertexSideDart_mem_inside data.toRotationSystem inside edge hregion⟩) =
    openOldDartColor data.toRotationSystem
      (fun vertex => vertex ∈ inside)
      (pair.sourceCrosscutOpenRoot data boundary) coloring
      exposed.1.1 exposed.1.2
  have hsideEdge :
      data.toRotationSystem.edgeOf
        (vertexSideDart data.toRotationSystem inside edge hregion) = edge :=
    vertexSideDart_edgeOf data.toRotationSystem inside edge hregion
  rcases data.toRotationSystem.edge_fiber_two_cases
      (d := vertexSideDart data.toRotationSystem inside edge hregion)
      (y := exposed.1.1) hsideEdge (by simp [edge]) with hsame | hopposite
  · unfold dartColor openOldDartColor
    congr 3
    apply Subtype.ext
    exact hsame.symm
  · exfalso
    have houtside :
        data.toRotationSystem.vertOf
          (data.toRotationSystem.alpha exposed.1.1) ∉ inside := exposed.2
    apply houtside
    rw [hopposite, data.toRotationSystem.alpha_involutive]
    exact vertexSideDart_mem_inside data.toRotationSystem inside edge hregion

/-- The first block of the literal finite profile is the actual boundary word
on the left source transversal. -/
theorem sourceCrosscutLiteralOpenProfile_left_edgeColor_eq_insideBoundaryWord
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
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutLiteralOpenProfile data boundary coloring hcoloring).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.castAdd pair.right.walk.length step))).toColor =
      pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inl step) := by
  calc
    ((pair.sourceCrosscutLiteralOpenProfile data boundary coloring hcoloring).edgeColor
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.castAdd pair.right.walk.length step))).toColor =
        pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          ((pair.sourceCrosscutBoundaryProfileData data boundary).crossingEdge
            (Fin.cast
              (pair.componentSide_crossingCard_eq_interfaceWidths data
                boundary.component boundary.component_boundary).symm
              (Fin.castAdd pair.right.walk.length step))) :=
      pair.sourceCrosscutLiteralOpenProfile_edgeColor_toColor data boundary coloring
        hcoloring _
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (pair.left.crossingEdge hunique step) := by
      congr 1
      change vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
          (pair.componentSide boundary.component)
          (pair.sourceCrosscutBoundaryIndexing data boundary)
          (Fin.cast
            (pair.componentSide_crossingCard_eq_interfaceWidths data
              boundary.component boundary.component_boundary).symm
            (Fin.castAdd pair.right.walk.length step)) = _
      exact pair.sourceCrosscutBoundaryIndexing_left data boundary step
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step)).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary (.inl step)]
      congr 1
    _ = pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inl step) :=
      pair.sourceCrosscutLiteralColorOnVertexSide_eq_boundaryDartColor
        data boundary coloring
        (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step))

/-- The second block of the literal finite profile is the actual boundary word
on the aligned right source transversal. -/
theorem sourceCrosscutLiteralOpenProfile_right_edgeColor_eq_insideBoundaryWord
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
    (step : Fin pair.right.walk.length) :
    ((pair.sourceCrosscutLiteralOpenProfile data boundary coloring hcoloring).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.natAdd pair.left.walk.length step))).toColor =
      pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inr step) := by
  calc
    ((pair.sourceCrosscutLiteralOpenProfile data boundary coloring hcoloring).edgeColor
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.natAdd pair.left.walk.length step))).toColor =
        pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          ((pair.sourceCrosscutBoundaryProfileData data boundary).crossingEdge
            (Fin.cast
              (pair.componentSide_crossingCard_eq_interfaceWidths data
                boundary.component boundary.component_boundary).symm
              (Fin.natAdd pair.left.walk.length step))) :=
      pair.sourceCrosscutLiteralOpenProfile_edgeColor_toColor data boundary coloring
        hcoloring _
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (pair.right.crossingEdge hunique step) := by
      congr 1
      change vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
          (pair.componentSide boundary.component)
          (pair.sourceCrosscutBoundaryIndexing data boundary)
          (Fin.cast
            (pair.componentSide_crossingCard_eq_interfaceWidths data
              boundary.component boundary.component_boundary).symm
            (Fin.natAdd pair.left.walk.length step)) = _
      exact pair.sourceCrosscutBoundaryIndexing_right data boundary step
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary (.inr step)).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary (.inr step)]
      congr 1
    _ = pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inr step) :=
      pair.sourceCrosscutLiteralColorOnVertexSide_eq_boundaryDartColor
        data boundary coloring
        (pair.sourceCrosscutBoundaryDartAt data boundary (.inr step))

/-- The finite profile of a coloring of the shortened source splice reads the
sewn left seam word in its first source-order block. -/
theorem sourceCrosscutSpliceOutputLiteralOpenProfile_left_edgeColor_eq_seamColorWord
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
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (output :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (houtput : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutLiteralOpenProfile data boundary
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
      (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
        output houtput)).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.castAdd pair.right.walk.length step))).toColor =
      seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
        output step := by
  calc
    ((pair.sourceCrosscutLiteralOpenProfile data boundary
        (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
        (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
          output houtput)).edgeColor
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.castAdd pair.right.walk.length step))).toColor =
        pair.sourceCrosscutInsideBoundaryWord data boundary
          (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
          (.inl step) :=
      pair.sourceCrosscutLiteralOpenProfile_left_edgeColor_eq_insideBoundaryWord
        data boundary
        (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
        (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
          output houtput) step
    _ = seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
          output step :=
      pair.sourceCrosscutOutputInsideBoundaryWord_left_eq_seamColorWord
        data boundary seamEndpoints output step

/-- The aligned right block of the shortened splice's finite profile reads the
same sewn seam word.  The cast is the source crosscut alignment, not an
identification of the two transversals. -/
theorem sourceCrosscutSpliceOutputLiteralOpenProfile_right_edgeColor_eq_seamColorWord
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
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (output :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (houtput : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutLiteralOpenProfile data boundary
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
      (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
        output houtput)).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.natAdd pair.left.walk.length (Fin.cast pair.length_eq step)))).toColor =
      seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
        output step := by
  calc
    ((pair.sourceCrosscutLiteralOpenProfile data boundary
        (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
        (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
          output houtput)).edgeColor
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.natAdd pair.left.walk.length (Fin.cast pair.length_eq step)))).toColor =
        pair.sourceCrosscutInsideBoundaryWord data boundary
          (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
          (.inr (Fin.cast pair.length_eq step)) :=
      pair.sourceCrosscutLiteralOpenProfile_right_edgeColor_eq_insideBoundaryWord
        data boundary
        (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
        (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
          output houtput) (Fin.cast pair.length_eq step)
    _ = seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
          output step :=
      pair.sourceCrosscutOutputInsideBoundaryWord_right_eq_seamColorWord
        data boundary seamEndpoints output step

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
