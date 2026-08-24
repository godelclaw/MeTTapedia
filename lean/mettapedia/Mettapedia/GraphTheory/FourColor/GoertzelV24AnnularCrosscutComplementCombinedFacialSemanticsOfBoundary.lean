import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementCombinedConnectivityOfBoundary

/-!
# Boundary-rooted facial semantics of a combined removed-side profile

The source's one-Cell `Count` state retains one facial coordinate in three
Lean fields: ambient-face continuation, fragment/port incidence, and face
progress capped at five.  This file exposes those three observations for the
same boundary-rooted combined profile used by the tracked-connectivity
calibration.

Every statement is read from one literal open-Cell coloring.  No global
cubicity, ambient-prefix coloring, deterministic update, or quotient by the
three geometric orientation labels is used.  The result completes the local
five-field semantics of an arbitrary positive `Count` entry; composing that
local state with an arbitrary cumulative prefix remains separate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileRestriction
open GoertzelV24CorridorProfileSerialConnectivity
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Exact occurrence-sensitive facial observations of one boundary-rooted
combined profile.  The three fields jointly implement the source's capped
face-progress coordinate. -/
structure SourceCrosscutComplementCombinedFacialSemanticsOfBoundary
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
    (profile : pair.SourceCrosscutComplementCombinedProfile data boundary) : Prop where
  faceContinues : ∀ left right,
    (profile.faceContinues left right = true) ↔
      (pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).fragmentFace left =
      (pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).fragmentFace right
  fragmentContainsPort : ∀ fragment port,
    (profile.fragmentContainsPort fragment port = true) ↔
      (pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).portEdge port ∈
      (pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).regionalFragmentEdges fragment
  faceLengthCap : ∀ fragment,
    (profile.faceLengthCap fragment).val =
      min ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
        ).regionalFragmentEdges fragment).card 5

/-- The literal boundary-rooted combined profile has all three exact facial
observations. -/
theorem sourceCrosscutComplementLiteralOpenProfileOfBoundary_facialSemantics
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
    pair.SourceCrosscutComplementCombinedFacialSemanticsOfBoundary data boundary
      (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
        coloring hcoloring) := by
  let cutData := pair.sourceCrosscutComplementBoundaryProfileData data boundary
  let color := pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
    data boundary coloring
  let hregion := pair.sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
    data boundary
  let hports := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    data boundary
  let hcrossing : ∀ crossing, color (cutData.crossingEdge crossing) ≠ 0 :=
    fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
        data boundary coloring hcoloring (hregion (hports (.inl crossing)))
  change SourceCrosscutComplementCombinedFacialSemanticsOfBoundary data pair
    boundary (cutData.regionalProfile color hcrossing)
  refine {
    faceContinues := ?_
    fragmentContainsPort := ?_
    faceLengthCap := ?_ }
  · intro left right
    exact cutData.regionalProfile_faceContinues_eq_true_iff color hcrossing
      left right
  · intro fragment port
    exact cutData.regionalProfile_fragmentContainsPort_eq_true_iff color
      hcrossing fragment port
  · intro fragment
    exact cutData.regionalProfile_faceLengthCap_val color hcrossing fragment

/-- Realizability of an abstract combined state supplies one literal coloring
and the exact facial semantics of that same state. -/
theorem SourceCrosscutComplementCombinedProfileRealizableOfBoundary.exists_facial_semantics
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
    (profile : pair.SourceCrosscutComplementCombinedProfile data boundary)
    (hrealizable : pair.SourceCrosscutComplementCombinedProfileRealizableOfBoundary
      data boundary profile) :
    ∃ coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
        data boundary,
      pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
          coloring.1 coloring.2 = profile ∧
        pair.SourceCrosscutComplementCombinedFacialSemanticsOfBoundary
          data boundary profile := by
  rcases hrealizable with ⟨coloring, hprofile⟩
  refine ⟨coloring, hprofile, ?_⟩
  rw [← hprofile]
  exact pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_facialSemantics
    data boundary coloring.1 coloring.2

/-- Positive boundary-rooted `Count` support is exactly one realizable
combined state carrying both the tracked serial law and the complete local
facial semantics.  This is the full five-coordinate local semantic package;
the cumulative prefix factorization is the next theorem. -/
theorem sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff_exists_combined_fullSemantics
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
            right ∧
          SerialProfileConnectivity left combined right
            (pair.sourceCrosscutComplementLeftCombinedIndex data boundary)
            (pair.sourceCrosscutComplementRightCombinedIndex data boundary) ∧
          pair.SourceCrosscutComplementCombinedFacialSemanticsOfBoundary
            data boundary combined := by
  constructor
  · intro hpositive
    rcases
        (pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff_exists_combined_serial
          data boundary left right).1 hpositive with
      ⟨combined, hrealizable, hleft, hright, hserial⟩
    have hfacial :=
      (hrealizable.exists_facial_semantics data pair boundary combined).choose_spec.2
    exact ⟨combined, hrealizable, hleft, hright, hserial, hfacial⟩
  · rintro ⟨combined, hrealizable, hleft, hright, _hserial, _hfacial⟩
    exact
      (pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff_exists_combined
        data boundary left right).2
        ⟨combined, hrealizable, hleft, hright⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
