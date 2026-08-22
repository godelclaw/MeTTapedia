import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementCombinedCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileOfBoundary

/-!
# Boundary-rooted combined profile for the removed-side Count

The actual source annulus is not globally cubic: its named boundary stubs have
degree one.  The boundary-rooted `Count` therefore cannot use the older
cubicity-parameterized combined-profile wrapper even though its generic
restriction laws are valid.

This file proves the corresponding non-vacuous factorization.  A positive
boundary-rooted `Count` entry is witnessed by one literal Tait coloring and
one complete combined four-port profile; the left and right matrix indices
are the two restrictions of that same five-coordinate state.
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

/-- The boundary-rooted literal combined profile restricts to its left
matrix-index profile. -/
theorem sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_left
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring) :
    CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
          data boundary coloring hcoloring)
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) =
      pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
        data boundary coloring hcoloring := by
  unfold sourceCrosscutComplementLiteralOpenProfileOfBoundary
  unfold sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
  apply pair.sourceCrosscutComplementCombinedProfile_restrict_left

/-- The same boundary-rooted combined profile restricts to its aligned right
matrix-index profile. -/
theorem sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_right
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring) :
    CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
          data boundary coloring hcoloring)
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary) =
      pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
        data boundary coloring hcoloring := by
  unfold sourceCrosscutComplementLiteralOpenProfileOfBoundary
  unfold sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
  apply pair.sourceCrosscutComplementCombinedProfile_restrict_right

/-- A combined profile is boundary-rooted realizable when one literal Tait
coloring of the removed open tangle computes it. -/
def SourceCrosscutComplementCombinedProfileRealizableOfBoundary
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
    (profile : pair.SourceCrosscutComplementCombinedProfile data boundary) :
    Prop :=
  ∃ coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
      data boundary,
    pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
      coloring.1 coloring.2 = profile

/-- A positive boundary-rooted removed-side `Count` entry factors through one
literal combined profile.  In particular, its two matrix indices are
restrictions of the same computed five-coordinate state. -/
theorem sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff_exists_combined
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        data boundary left right ↔
      ∃ combined : pair.SourceCrosscutComplementCombinedProfile data boundary,
        pair.SourceCrosscutComplementCombinedProfileRealizableOfBoundary
            data boundary combined ∧
          CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) =
            left ∧
          CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementRightCombinedIndex data boundary) =
            right := by
  rw [pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff]
  constructor
  · rintro ⟨coloring, hleft, hright⟩
    let combined := pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
      data boundary coloring.1 coloring.2
    refine ⟨combined, ⟨coloring, rfl⟩, ?_, ?_⟩
    · exact
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_left
          data boundary coloring.1 coloring.2).trans hleft
    · exact
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_right
          data boundary coloring.1 coloring.2).trans hright
  · rintro ⟨combined, ⟨coloring, hcombined⟩, hleft, hright⟩
    refine ⟨coloring, ?_, ?_⟩
    · calc
        pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
            data boundary coloring.1 coloring.2 =
            CorridorCutProfile.restrictCrossings
              (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
                data boundary coloring.1 coloring.2)
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) :=
          (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_left
            data boundary coloring.1 coloring.2).symm
        _ = CorridorCutProfile.restrictCrossings combined
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) :=
          congrArg
            (fun profile => CorridorCutProfile.restrictCrossings profile
              (pair.sourceCrosscutComplementLeftCombinedIndex data boundary))
            hcombined
        _ = left := hleft
    · calc
        pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
            data boundary coloring.1 coloring.2 =
            CorridorCutProfile.restrictCrossings
              (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
                data boundary coloring.1 coloring.2)
              (pair.sourceCrosscutComplementRightCombinedIndex data boundary) :=
          (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_right
            data boundary coloring.1 coloring.2).symm
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
