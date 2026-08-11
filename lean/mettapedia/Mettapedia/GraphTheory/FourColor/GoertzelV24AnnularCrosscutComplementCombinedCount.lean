import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementCombinedProfile

/-!
# The removed-side Count through one combined profile

The literal removed region has one profile on all source-ordered boundary
crossings.  Its existing `Count` matrix uses the restrictions to the left and
right crossing blocks as indices.  This file records the exact factorization:
a positive matrix entry is equivalent to one realizable combined profile
whose two restrictions are the named indices.

No region is identified with a corridor hexagon boundary here.  The combined
profile is computed from the literal removed open tangle, and the restriction
maps are the already-proved source crossing coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The complete four-block profile carrier of the literal removed region,
before selecting either matrix-index boundary. -/
abbrev SourceCrosscutComplementCombinedProfile
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
    (boundary : SourceCrosscutBoundaryData data pair) :=
  CorridorCutProfile
    (Fintype.card (VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ)) 0
    (pair.sourceCrosscutComplementFaceFragmentCount data boundary)

/-- A combined profile is realizable when it is computed from one literal
Tait coloring of the removed open tangle. -/
def SourceCrosscutComplementCombinedProfileRealizable
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
    (profile : pair.SourceCrosscutComplementCombinedProfile data boundary) :
    Prop :=
  ∃ coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring data
      boundary hcubic,
    pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
      coloring.1 coloring.2 = profile

/-- A positive removed-side `Count` entry factors through one literal
combined profile.  In particular, the two matrix indices are not unrelated
profile witnesses: they are restrictions of the same computed five-field
state. -/
theorem sourceCrosscutComplementLiteralOpenProfileCount_pos_iff_exists_combined
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    0 < pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary
        hcubic left right ↔
      ∃ combined : pair.SourceCrosscutComplementCombinedProfile data boundary,
        pair.SourceCrosscutComplementCombinedProfileRealizable data boundary
            hcubic combined ∧
          CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) =
            left ∧
          CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementRightCombinedIndex data boundary) =
            right := by
  rw [pair.sourceCrosscutComplementLiteralOpenProfileCount_pos_iff]
  constructor
  · rintro ⟨coloring, hleft, hright⟩
    let combined := pair.sourceCrosscutComplementLiteralOpenProfile data
      boundary hcubic coloring.1 coloring.2
    refine ⟨combined, ⟨coloring, rfl⟩, ?_, ?_⟩
    · exact (pair.sourceCrosscutComplementLiteralOpenProfile_restrict_left
        data boundary hcubic coloring.1 coloring.2).trans hleft
    · exact (pair.sourceCrosscutComplementLiteralOpenProfile_restrict_right
        data boundary hcubic coloring.1 coloring.2).trans hright
  · rintro ⟨combined, ⟨coloring, hcombined⟩, hleft, hright⟩
    refine ⟨coloring, ?_, ?_⟩
    · calc
        pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary
            hcubic coloring.1 coloring.2 =
            CorridorCutProfile.restrictCrossings
              (pair.sourceCrosscutComplementLiteralOpenProfile data boundary
                hcubic coloring.1 coloring.2)
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) :=
          (pair.sourceCrosscutComplementLiteralOpenProfile_restrict_left
            data boundary hcubic coloring.1 coloring.2).symm
        _ = CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) :=
          congrArg
            (fun profile => CorridorCutProfile.restrictCrossings profile
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary))
            hcombined
        _ = left := hleft
    · calc
        pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary
            hcubic coloring.1 coloring.2 =
            CorridorCutProfile.restrictCrossings
              (pair.sourceCrosscutComplementLiteralOpenProfile data boundary
                hcubic coloring.1 coloring.2)
              (pair.sourceCrosscutComplementRightCombinedIndex data boundary) :=
          (pair.sourceCrosscutComplementLiteralOpenProfile_restrict_right
            data boundary hcubic coloring.1 coloring.2).symm
        _ = CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementRightCombinedIndex data boundary) :=
          congrArg
            (fun profile => CorridorCutProfile.restrictCrossings profile
              (pair.sourceCrosscutComplementRightCombinedIndex data boundary))
            hcombined
        _ = right := hright

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
