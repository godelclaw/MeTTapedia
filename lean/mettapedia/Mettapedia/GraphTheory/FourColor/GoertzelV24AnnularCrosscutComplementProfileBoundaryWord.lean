import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile

/-!
# Boundary-color coordinates of complementary crosscut profiles

The source's `Count` profile is computed separately on both open sides of a
crosscut.  This file identifies the boundary-color coordinate of the removed
side's full profile with the literal source-ordered boundary word used by the
open-region gluing theorem.  Thus the complementary profile matrix has the
same concrete boundary semantics as the retained-side matrix; its remaining
connectivity and face-progress coordinates remain genuine refinements.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
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

/-- On the complementary literal source tangle, the profile reader chooses
the color of the opposite source boundary dart.  The other dart over that
edge belongs to the retained component, so the vertex-side choice cannot
select it. -/
theorem sourceCrosscutComplementLiteralColorOnVertexSide_eq_outsideBoundaryDartColor
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (index : pair.SourceCrosscutBoundaryIndex) :
    pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic
      coloring
      (data.toRotationSystem.edgeOf
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1) =
      pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring index := by
  let inside := pair.componentSide boundary.component
  let outside := insideᶜ
  let exposed := pair.sourceCrosscutBoundaryDartAt data boundary index
  let edge := data.toRotationSystem.edgeOf exposed.1.1
  have hcrossing : edge ∈ vertexSetCrossingEdges data.toRotationSystem outside := by
    rw [mem_vertexSetCrossingEdges_iff]
    apply (edgeCrossesVertexSet_compl data.toRotationSystem inside edge).2
    rw [← mem_vertexSetCrossingEdges_iff]
    dsimp [edge, exposed, inside]
    exact boundaryDart_edge_mem_vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component)
      (pair.sourceCrosscutBoundaryDartAt data boundary index)
  have hregion : edge ∈ vertexSetRegionEdges data.toRotationSystem outside :=
    vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem outside hcrossing
  rw [sourceCrosscutComplementLiteralColorOnVertexSide, dif_pos hregion]
  change dartColor data.toRotationSystem
        (fun vertex => vertex ∉ inside)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem outside edge hregion, by
          simpa [outside] using
            vertexSideDart_mem_inside data.toRotationSystem outside edge hregion⟩) =
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ inside)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (data.toRotationSystem.alpha exposed.1.1) exposed.2
  have hsideEdge :
      data.toRotationSystem.edgeOf
        (vertexSideDart data.toRotationSystem outside edge hregion) = edge :=
    vertexSideDart_edgeOf data.toRotationSystem outside edge hregion
  rcases data.toRotationSystem.edge_fiber_two_cases
      (d := vertexSideDart data.toRotationSystem outside edge hregion)
      (y := data.toRotationSystem.alpha exposed.1.1) hsideEdge (by
        simp [edge]) with hsame | hopposite
  · unfold dartColor openOldDartColor
    congr 3
    apply Subtype.ext
    exact hsame.symm
  · exfalso
    have hins : data.toRotationSystem.vertOf exposed.1.1 ∈ inside := by
      change data.toRotationSystem.vertOf
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1 ∈
        pair.componentSide boundary.component
      exact (pair.sourceCrosscutBoundaryDartAt data boundary index).1.2
    have hnotOutside : data.toRotationSystem.vertOf exposed.1.1 ∉ outside := by
      simpa [outside] using hins
    apply hnotOutside
    have hsame : exposed.1.1 =
        vertexSideDart data.toRotationSystem outside edge hregion := by
      have halpha := congrArg data.toRotationSystem.alpha hopposite
      simpa only [data.toRotationSystem.alpha_involutive] using halpha
    rw [hsame]
    exact vertexSideDart_mem_inside data.toRotationSystem outside edge hregion

/-- The left removed-side profile reads the literal left source boundary
word at every port. -/
theorem sourceCrosscutComplementLiteralOpenLeftProfile_edgeColor_eq_boundaryWord
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
      coloring hcoloring).edgeColor step).toColor =
      pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring step := by
  change ((pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
      coloring hcoloring).edgeColor step).toColor =
    pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring (.inl step)
  calc
    ((pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        coloring hcoloring).edgeColor step).toColor =
        pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring
          ((pair.sourceCrosscutComplementLeftCutData data boundary).crossingEdge step) := by
      unfold sourceCrosscutComplementLiteralOpenLeftProfile
      exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ step
    _ = pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring
          (pair.left.crossingEdge hunique step) := by
      rfl
    _ = pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step)).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary (.inl step)]
      rfl
    _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring (.inl step) :=
      pair.sourceCrosscutComplementLiteralColorOnVertexSide_eq_outsideBoundaryDartColor
        data boundary hcubic coloring (.inl step)

/-- The aligned right removed-side profile reads the literal right source
boundary word in the same rung coordinate as the left profile. -/
theorem sourceCrosscutComplementLiteralOpenRightProfile_edgeColor_eq_boundaryWord
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
      coloring hcoloring).edgeColor step).toColor =
      pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring
        (Fin.cast pair.length_eq step) := by
  change ((pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
      coloring hcoloring).edgeColor step).toColor =
    pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring
      (.inr (Fin.cast pair.length_eq step))
  calc
    ((pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        coloring hcoloring).edgeColor step).toColor =
        pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring
          ((pair.sourceCrosscutComplementRightCutData data boundary).crossingEdge step) := by
      unfold sourceCrosscutComplementLiteralOpenRightProfile
      exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ step
    _ = pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring
          (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) := by
      rfl
    _ = pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary
              (.inr (Fin.cast pair.length_eq step))).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary
        (.inr (Fin.cast pair.length_eq step))]
      rfl
    _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring
        (.inr (Fin.cast pair.length_eq step)) :=
      pair.sourceCrosscutComplementLiteralColorOnVertexSide_eq_outsideBoundaryDartColor
        data boundary hcubic coloring (.inr (Fin.cast pair.length_eq step))

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
