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

/-- Project the color coordinate of a removed-side left interface profile to
its literal source boundary word. -/
noncomputable def sourceCrosscutComplementInterfaceProfileLeftColorWord
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
    (profile : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    Fin pair.left.walk.length → Color :=
  fun step => (profile.edgeColor step).toColor

/-- Project the color coordinate of an aligned removed-side right interface
profile back to the literal right source-boundary order. -/
noncomputable def sourceCrosscutComplementInterfaceProfileRightColorWord
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
    (profile : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    Fin pair.right.walk.length → Color :=
  fun step => (profile.edgeColor (Fin.cast pair.length_eq.symm step)).toColor

/-- The color projection of a literal complementary left profile is its
literal left source boundary word. -/
theorem sourceCrosscutComplementLiteralOpenLeftProfile_colorWord_eq_boundaryWord
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
      coloring) :
    pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
      (pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        coloring hcoloring) =
      pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring := by
  funext step
  exact pair.sourceCrosscutComplementLiteralOpenLeftProfile_edgeColor_eq_boundaryWord
    data boundary hcubic coloring hcoloring step

/-- The color projection of a literal complementary aligned right profile is
its literal right source boundary word. -/
theorem sourceCrosscutComplementLiteralOpenRightProfile_colorWord_eq_boundaryWord
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
      coloring) :
    pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
      (pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        coloring hcoloring) =
      pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring := by
  funext step
  change ((pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
    coloring hcoloring).edgeColor (Fin.cast pair.length_eq.symm step)).toColor = _
  simpa using
    (pair.sourceCrosscutComplementLiteralOpenRightProfile_edgeColor_eq_boundaryWord
      data boundary hcubic coloring hcoloring (Fin.cast pair.length_eq.symm step))

/-- The ordinary two-boundary `Count` support on the removed tangle is the
projection of its literal full-profile matrix support.  Every realized pair
of words therefore has a computed connectivity/face refinement, and every
positive full-profile entry realizes its displayed two boundary words. -/
theorem sourceCrosscutComplementBoundaryColorCount_pos_iff_exists_profilePair
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
    (leftWord : Fin pair.left.walk.length → Color)
    (rightWord : Fin pair.right.walk.length → Color) :
    0 < pair.sourceCrosscutComplementBoundaryColorCount data boundary hcubic
      leftWord rightWord ↔
      ∃ leftProfile rightProfile :
          pair.SourceCrosscutComplementInterfaceProfile data boundary,
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
            leftProfile = leftWord ∧
          pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
            rightProfile = rightWord ∧
          0 < pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary
            hcubic leftProfile rightProfile := by
  constructor
  · rw [pair.sourceCrosscutComplementBoundaryColorCount_apply]
    intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    rcases (pair.mem_sourceCrosscutComplementTaitColoringFiber_iff data boundary
      hcubic leftWord rightWord coloring).1 hmember with ⟨hcoloring, hleft, hright⟩
    refine ⟨pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        coloring hcoloring,
      pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        coloring hcoloring, ?_, ?_, ?_⟩
    · calc
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
            (pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
              coloring hcoloring) =
            pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring :=
          pair.sourceCrosscutComplementLiteralOpenLeftProfile_colorWord_eq_boundaryWord
            data boundary hcubic coloring hcoloring
        _ = leftWord := hleft
    · calc
        pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
            (pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
              coloring hcoloring) =
            pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring :=
          pair.sourceCrosscutComplementLiteralOpenRightProfile_colorWord_eq_boundaryWord
            data boundary hcubic coloring hcoloring
        _ = rightWord := hright
    · exact pair.sourceCrosscutComplementLiteralOpenProfileCount_pos_of_coloring
        data boundary hcubic ⟨coloring, hcoloring⟩
  · rintro ⟨leftProfile, rightProfile, hleftWord, hrightWord, hpositive⟩
    rw [pair.sourceCrosscutComplementBoundaryColorCount_apply]
    rcases (pair.sourceCrosscutComplementLiteralOpenProfileCount_pos_iff
      data boundary hcubic leftProfile rightProfile).1 hpositive with
      ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring.1, ?_⟩
    apply (pair.mem_sourceCrosscutComplementTaitColoringFiber_iff data boundary hcubic
      leftWord rightWord coloring.1).2
    refine ⟨coloring.2, ?_, ?_⟩
    · calc
        pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring.1 =
            pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
              (pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
                coloring.1 coloring.2) :=
          (pair.sourceCrosscutComplementLiteralOpenLeftProfile_colorWord_eq_boundaryWord
            data boundary hcubic coloring.1 coloring.2).symm
        _ = pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
            leftProfile := by
          rw [hleft]
        _ = leftWord := hleftWord
    · calc
        pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring.1 =
            pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
              (pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
                coloring.1 coloring.2) :=
          (pair.sourceCrosscutComplementLiteralOpenRightProfile_colorWord_eq_boundaryWord
            data boundary hcubic coloring.1 coloring.2).symm
        _ = pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
            rightProfile := by
          rw [hright]
        _ = rightWord := hrightWord

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
