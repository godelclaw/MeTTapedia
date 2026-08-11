import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileRestriction

/-!
# Restricting the combined profile of a removed source region

The removed tangle between two source crosscuts already has one source-ordered
combined boundary profile, `sourceCrosscutComplementBoundaryProfileData`.
Its existing `Count` matrix exposes two width-preserving profiles, one at
either block, but both profiles use the same removed-region face-fragment
carrier.

The main results are restriction laws on that established combined object.
Selecting its left or right crossing block gives exactly the corresponding
raw profile used by `Count`.  No second presentation of the region is
introduced, and no claim is made that a general removed source region is the
complete boundary of a corridor hexagon.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] {RS : RotationSystem V E}
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The left source block inside the established combined crossing carrier. -/
noncomputable def sourceCrosscutComplementLeftCombinedIndex
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
    Fin pair.left.walk.length →
      Fin (Fintype.card (VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)) :=
  fun step =>
    (pair.sourceCrosscutComplementBoundaryIndexing data boundary).symm
      (pair.sourceCrosscutComplementPort data boundary (Sum.inl step))

/-- The aligned right source block inside the same combined carrier. -/
noncomputable def sourceCrosscutComplementRightCombinedIndex
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
    Fin pair.left.walk.length →
      Fin (Fintype.card (VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)) :=
  fun step =>
    (pair.sourceCrosscutComplementBoundaryIndexing data boundary).symm
      (pair.sourceCrosscutComplementPort data boundary
        (Sum.inr (Fin.cast pair.length_eq step)))

@[simp]
theorem sourceCrosscutComplementBoundaryProfileData_crossingEdge_left
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
    (step : Fin pair.left.walk.length) :
    (pair.sourceCrosscutComplementBoundaryProfileData data boundary).crossingEdge
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary step) =
      pair.left.crossingEdge hunique step := by
  simp [sourceCrosscutComplementBoundaryProfileData,
    sourceCrosscutComplementLeftCombinedIndex,
    vertexSetBoundaryGraphCutDataWithIndexing,
    vertexSetCrossingEdgeAtWithIndexing]

@[simp]
theorem sourceCrosscutComplementBoundaryProfileData_crossingEdge_right
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
    (step : Fin pair.left.walk.length) :
    (pair.sourceCrosscutComplementBoundaryProfileData data boundary).crossingEdge
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary step) =
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) := by
  simp [sourceCrosscutComplementBoundaryProfileData,
    sourceCrosscutComplementRightCombinedIndex,
    vertexSetBoundaryGraphCutDataWithIndexing,
    vertexSetCrossingEdgeAtWithIndexing]

/-- Selecting the left block of the combined raw data recovers the existing
left matrix-index data exactly. -/
theorem sourceCrosscutComplementBoundaryProfileData_restrict_left
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
    GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings
        (pair.sourceCrosscutComplementBoundaryProfileData data boundary)
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) =
      pair.sourceCrosscutComplementLeftCutData data boundary := by
  apply graphCorridorCutData_eq_of_fields <;>
    simp [sourceCrosscutComplementBoundaryProfileData,
      sourceCrosscutComplementLeftCombinedIndex,
      sourceCrosscutComplementLeftCutData,
      sourceCrosscutComplementCutData,
      GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings,
      vertexSetBoundaryGraphCutDataWithIndexing,
      vertexSetCrossingEdgeAtWithIndexing]

/-- Selecting the aligned right block recovers the existing right
matrix-index data exactly. -/
theorem sourceCrosscutComplementBoundaryProfileData_restrict_right
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
    GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings
        (pair.sourceCrosscutComplementBoundaryProfileData data boundary)
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary) =
      pair.sourceCrosscutComplementRightCutData data boundary := by
  apply graphCorridorCutData_eq_of_fields <;>
    simp [sourceCrosscutComplementBoundaryProfileData,
      sourceCrosscutComplementRightCombinedIndex,
      sourceCrosscutComplementRightCutData,
      sourceCrosscutComplementCutData,
      GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings,
      vertexSetBoundaryGraphCutDataWithIndexing,
      vertexSetCrossingEdgeAtWithIndexing]

/-- Restriction of any combined graph-derived profile is the left full
profile used as a `Count` matrix index. -/
theorem sourceCrosscutComplementCombinedProfile_restrict_left
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
    (color : G.edgeSet → Color)
    (hcombined : ∀ crossing,
      color ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).crossingEdge crossing) ≠ 0)
    (hleft : ∀ crossing,
      color ((pair.sourceCrosscutComplementLeftCutData data boundary
        ).crossingEdge crossing) ≠ 0) :
    GoertzelV24CorridorProfileRestriction.CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementBoundaryProfileData data boundary
          |>.regionalProfile color hcombined)
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) =
      (pair.sourceCrosscutComplementLeftCutData data boundary
        |>.regionalProfile color hleft) := by
  calc
    _ = (GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings
            (pair.sourceCrosscutComplementBoundaryProfileData data boundary)
            (pair.sourceCrosscutComplementLeftCombinedIndex data boundary)
        ).regionalProfile color
          (fun crossing => hcombined
            (pair.sourceCrosscutComplementLeftCombinedIndex data boundary
              crossing)) :=
      GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings_regionalProfile
          (pair.sourceCrosscutComplementBoundaryProfileData data boundary)
          (pair.sourceCrosscutComplementLeftCombinedIndex data boundary)
          color hcombined
    _ = _ := by
      exact GoertzelV24CorridorProfileRestriction.graphCorridorCutData_regionalProfile_eq_of_eq
          (pair.sourceCrosscutComplementBoundaryProfileData_restrict_left
            data boundary)
          color
          (fun crossing => hcombined
            (pair.sourceCrosscutComplementLeftCombinedIndex data boundary
              crossing))
          hleft

/-- Restriction of the same combined profile is the aligned right full
profile used by `Count`. -/
theorem sourceCrosscutComplementCombinedProfile_restrict_right
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
    (color : G.edgeSet → Color)
    (hcombined : ∀ crossing,
      color ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).crossingEdge crossing) ≠ 0)
    (hright : ∀ crossing,
      color ((pair.sourceCrosscutComplementRightCutData data boundary
        ).crossingEdge crossing) ≠ 0) :
    GoertzelV24CorridorProfileRestriction.CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementBoundaryProfileData data boundary
          |>.regionalProfile color hcombined)
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary) =
      (pair.sourceCrosscutComplementRightCutData data boundary
        |>.regionalProfile color hright) := by
  calc
    _ = (GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings
            (pair.sourceCrosscutComplementBoundaryProfileData data boundary)
            (pair.sourceCrosscutComplementRightCombinedIndex data boundary)
        ).regionalProfile color
          (fun crossing => hcombined
            (pair.sourceCrosscutComplementRightCombinedIndex data boundary
              crossing)) :=
      GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings_regionalProfile
          (pair.sourceCrosscutComplementBoundaryProfileData data boundary)
          (pair.sourceCrosscutComplementRightCombinedIndex data boundary)
          color hcombined
    _ = _ := by
      exact GoertzelV24CorridorProfileRestriction.graphCorridorCutData_regionalProfile_eq_of_eq
          (pair.sourceCrosscutComplementBoundaryProfileData_restrict_right
            data boundary)
          color
          (fun crossing => hcombined
            (pair.sourceCrosscutComplementRightCombinedIndex data boundary
              crossing))
          hright

/-- The literal removed-side profile restricts to its established left
`Count` index.  This is the concrete open-tangle specialization of the
combined-profile restriction law. -/
theorem sourceCrosscutComplementLiteralOpenProfile_restrict_left
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
    GoertzelV24CorridorProfileRestriction.CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
          coloring hcoloring)
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) =
      pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        coloring hcoloring := by
  unfold sourceCrosscutComplementLiteralOpenProfile
  unfold sourceCrosscutComplementLiteralOpenLeftProfile
  apply pair.sourceCrosscutComplementCombinedProfile_restrict_left

/-- The same literal removed-side profile restricts to its aligned right
`Count` index. -/
theorem sourceCrosscutComplementLiteralOpenProfile_restrict_right
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
    GoertzelV24CorridorProfileRestriction.CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
          coloring hcoloring)
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary) =
      pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        coloring hcoloring := by
  unfold sourceCrosscutComplementLiteralOpenProfile
  unfold sourceCrosscutComplementLiteralOpenRightProfile
  apply pair.sourceCrosscutComplementCombinedProfile_restrict_right

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
