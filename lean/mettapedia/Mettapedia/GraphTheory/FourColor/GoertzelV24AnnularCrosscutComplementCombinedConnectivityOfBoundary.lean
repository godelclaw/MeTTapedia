import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementCombinedCountOfBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileSerialConnectivity

/-!
# Boundary-rooted connectivity of a combined removed-side profile

The opened source annulus has degree-one boundary stubs, so its rotation
system is not globally cubic.  Nevertheless, one literal complementary Cell
has the same combined four-port connectivity semantics as in the closed-map
development: its two exposed profiles are restrictions of one realizable
combined profile, and that combined profile satisfies the exact finite serial
connectivity law.

This file proves the boundary-rooted version directly from the literal open
Cell coloring.  No global cubicity, ambient-prefix coloring, deterministic
update, or orientation quotient is used.  In particular, a positive entry of
the source's five-coordinate `Count` now supplies the complete local tracked
morphism needed by the later cumulative recurrence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileRestriction
open GoertzelV24CorridorProfileSerialConnectivity
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- A boundary-rooted combined crossing stores the literal color of its
ambient cut edge. -/
theorem sourceCrosscutComplementLiteralOpenProfileOfBoundary_edgeColor_toColor
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
      data boundary).IsTaitEdgeColoring coloring)
    (crossing : Fin (Fintype.card (VertexSetCrossingEdge
      data.toRotationSystem (pair.componentSide boundary.component)ᶜ))) :
    ((pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
        coloring hcoloring).edgeColor crossing).toColor =
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
        data boundary coloring
        ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
          ).crossingEdge crossing) := by
  unfold sourceCrosscutComplementLiteralOpenProfileOfBoundary
  exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ crossing

/-- A combined-profile connectivity bit is exactly tracked-color
reachability in the literal boundary-rooted complementary Cell. -/
theorem sourceCrosscutComplementLiteralOpenProfileOfBoundary_strandConnected_eq_true_iff
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
      data boundary).IsTaitEdgeColoring coloring)
    (trackedPair : TrackedColorPair)
    (first second : Fin (Fintype.card (VertexSetCrossingEdge
      data.toRotationSystem (pair.componentSide boundary.component)ᶜ))) :
    (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
        coloring hcoloring).strandConnected trackedPair
          (.inl first) (.inl second) = true ↔
      IsTrackedColor (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2
          (pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
            data boundary coloring
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge first)) ∧
        IsTrackedColor (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2
          (pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
            data boundary coloring
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge second)) ∧
        (regionalTrackedEdgeGraph data.toRotationSystem
          (pair.sourceCrosscutComplementBoundaryProfileData data boundary
            ).regionEdges
          (pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
            data boundary coloring)
          (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2).Reachable
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge first)
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge second) := by
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
  change (cutData.regionalProfile color hcrossing).strandConnected trackedPair
      (.inl first) (.inl second) = true ↔ _
  rw [cutData.regionalProfile_strandConnected_eq_true_iff]
  have hfirst : cutData.portEdge (.inl first) ∈ cutData.regionEdges :=
    hports (.inl first)
  have hsecond : cutData.portEdge (.inl second) ∈ cutData.regionEdges :=
    hports (.inl second)
  simp only [hfirst, hsecond, true_and]
  rfl

/-- The boundary-rooted literal combined profile satisfies the finite serial
connectivity law between its left and right restrictions. -/
theorem sourceCrosscutComplementLiteralOpenProfileOfBoundary_serialConnectivity
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
    SerialProfileConnectivity
      (CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
          coloring hcoloring)
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary))
      (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
        coloring hcoloring)
      (CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary data boundary
          coloring hcoloring)
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary))
      (pair.sourceCrosscutComplementLeftCombinedIndex data boundary)
      (pair.sourceCrosscutComplementRightCombinedIndex data boundary) := by
  let combined := pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
    data boundary coloring hcoloring
  let leftIndex := pair.sourceCrosscutComplementLeftCombinedIndex data boundary
  let rightIndex := pair.sourceCrosscutComplementRightCombinedIndex data boundary
  let cutData := pair.sourceCrosscutComplementBoundaryProfileData data boundary
  let color := pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
    data boundary coloring
  refine {
    leftColors := ?_
    rightColors := ?_
    strandConnected := ?_ }
  · intro index
    rfl
  · intro index
    rfl
  · intro trackedPair first second
    change combined.strandConnected trackedPair
        (.inl (rightIndex first)) (.inl (rightIndex second)) = true ↔
      IsTrackedColor (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2
          (combined.edgeColor (rightIndex first)).toColor ∧
        IsTrackedColor (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2
          (combined.edgeColor (rightIndex second)).toColor ∧
        Relation.ReflTransGen
          (serialProfileConnectivityStep
            (CorridorCutProfile.restrictCrossings combined leftIndex)
            combined leftIndex trackedPair)
          (rightIndex first) (rightIndex second)
    constructor
    · intro hconnected
      have hsemantic :=
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_strandConnected_eq_true_iff
          data boundary coloring hcoloring trackedPair
          (rightIndex first) (rightIndex second)).1 hconnected
      refine ⟨?_, ?_,
        serialProfileConnectivityClosure_of_cell
          (CorridorCutProfile.restrictCrossings combined leftIndex)
          combined leftIndex trackedPair (rightIndex first)
          (rightIndex second) hconnected⟩
      · rw [pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_edgeColor_toColor
          data boundary coloring hcoloring (rightIndex first)]
        exact hsemantic.1
      · rw [pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_edgeColor_toColor
          data boundary coloring hcoloring (rightIndex second)]
        exact hsemantic.2.1
    · rintro ⟨hfirstColor, hsecondColor, hclosure⟩
      have hstepReachable : ∀ {firstPort secondPort},
          serialProfileConnectivityStep
              (CorridorCutProfile.restrictCrossings combined leftIndex)
              combined leftIndex trackedPair firstPort secondPort →
            (regionalTrackedEdgeGraph data.toRotationSystem cutData.regionEdges
              color (trackedColorPairColors trackedPair).1
              (trackedColorPairColors trackedPair).2).Reachable
                (cutData.crossingEdge firstPort)
                (cutData.crossingEdge secondPort) := by
        intro firstPort secondPort hstep
        rcases hstep with hinput | hcell
        · rcases hinput with ⟨left, right, hfirst, hsecond, hinput⟩
          subst firstPort
          subst secondPort
          change combined.strandConnected trackedPair
              (.inl (leftIndex left)) (.inl (leftIndex right)) = true at hinput
          exact
            (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_strandConnected_eq_true_iff
              data boundary coloring hcoloring trackedPair
              (leftIndex left) (leftIndex right)).1 hinput |>.2.2
        · exact
            (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_strandConnected_eq_true_iff
              data boundary coloring hcoloring trackedPair
              firstPort secondPort).1 hcell |>.2.2
      have hreachable :
          (regionalTrackedEdgeGraph data.toRotationSystem cutData.regionEdges
            color (trackedColorPairColors trackedPair).1
            (trackedColorPairColors trackedPair).2).Reachable
              (cutData.crossingEdge (rightIndex first))
              (cutData.crossingEdge (rightIndex second)) :=
        Relation.ReflTransGen.trans_induction_on
          (motive := fun {firstPort secondPort} _ =>
            (regionalTrackedEdgeGraph data.toRotationSystem cutData.regionEdges
              color (trackedColorPairColors trackedPair).1
              (trackedColorPairColors trackedPair).2).Reachable
                (cutData.crossingEdge firstPort)
                (cutData.crossingEdge secondPort))
          hclosure
          (fun _ => SimpleGraph.Reachable.rfl)
          (fun hstep => hstepReachable hstep)
          (fun _ _ hleft hright => hleft.trans hright)
      apply
        (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_strandConnected_eq_true_iff
          data boundary coloring hcoloring trackedPair
          (rightIndex first) (rightIndex second)).2
      refine ⟨?_, ?_, hreachable⟩
      · rw [← pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_edgeColor_toColor
          data boundary coloring hcoloring (rightIndex first)]
        exact hfirstColor
      · rw [← pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_edgeColor_toColor
          data boundary coloring hcoloring (rightIndex second)]
        exact hsecondColor

/-- A positive boundary-rooted five-coordinate `Count` entry supplies one
realizable combined state with its exact finite serial-connectivity law. -/
theorem sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff_exists_combined_serial
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
            (pair.sourceCrosscutComplementRightCombinedIndex data boundary) := by
  constructor
  · intro hpositive
    rcases (pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff
        data boundary left right).1 hpositive with
      ⟨coloring, hleft, hright⟩
    let combined := pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary
      data boundary coloring.1 coloring.2
    have hrestrictLeft : CorridorCutProfile.restrictCrossings combined
          (pair.sourceCrosscutComplementLeftCombinedIndex data boundary) = left :=
      (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_left
        data boundary coloring.1 coloring.2).trans hleft
    have hrestrictRight : CorridorCutProfile.restrictCrossings combined
          (pair.sourceCrosscutComplementRightCombinedIndex data boundary) = right :=
      (pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_restrict_right
        data boundary coloring.1 coloring.2).trans hright
    refine ⟨combined, ⟨coloring, rfl⟩, hrestrictLeft, hrestrictRight, ?_⟩
    rw [← hrestrictLeft, ← hrestrictRight]
    exact pair.sourceCrosscutComplementLiteralOpenProfileOfBoundary_serialConnectivity
      data boundary coloring.1 coloring.2
  · rintro ⟨combined, hrealizable, hleft, hright, _hserial⟩
    exact
      (pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff_exists_combined
        data boundary left right).2
        ⟨combined, hrealizable, hleft, hright⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
