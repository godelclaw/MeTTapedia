import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementCombinedCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileSerialConnectivity

/-!
# Connectivity semantics of a combined removed-side profile

The removed source Cell has one profile on all crossings of both boundary
blocks.  This file exposes the exact graph meaning of its connectivity
coordinate before that profile is composed with a cumulative prefix state.

No equality with the complete boundary of the next hexagonal face is used.
The graph below is the literal complementary open region selected by the
paired source crosscuts, and realizability is witnessed by one Tait coloring
of that region.
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

/-- The color stored at a combined crossing is the literal color of its
ambient cut edge. -/
theorem sourceCrosscutComplementLiteralOpenProfile_edgeColor_toColor
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic
      ).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic
      ).IsTaitEdgeColoring coloring)
    (crossing : Fin (Fintype.card (VertexSetCrossingEdge
      data.toRotationSystem (pair.componentSide boundary.component)ᶜ))) :
    ((pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
        coloring hcoloring).edgeColor crossing).toColor =
      pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary
        hcubic coloring
        ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
          ).crossingEdge crossing) := by
  unfold sourceCrosscutComplementLiteralOpenProfile
  exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ crossing

/-- A connectivity bit of the combined profile is exactly tracked-color
reachability inside the literal removed open region.  Port membership is
discharged from the graph-derived boundary data, leaving only the two color
guards and the actual regional path. -/
theorem sourceCrosscutComplementLiteralOpenProfile_strandConnected_eq_true_iff
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic
      ).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic
      ).IsTaitEdgeColoring coloring)
    (trackedPair : TrackedColorPair)
    (first second : Fin (Fintype.card (VertexSetCrossingEdge
      data.toRotationSystem (pair.componentSide boundary.component)ᶜ))) :
    (pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
        coloring hcoloring).strandConnected trackedPair
          (.inl first) (.inl second) = true ↔
      IsTrackedColor (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2
          (pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary
            hcubic coloring
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge first)) ∧
        IsTrackedColor (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2
          (pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary
            hcubic coloring
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge second)) ∧
        (regionalTrackedEdgeGraph data.toRotationSystem
          (pair.sourceCrosscutComplementBoundaryProfileData data boundary
            ).regionEdges
          (pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary
            hcubic coloring)
          (trackedColorPairColors trackedPair).1
          (trackedColorPairColors trackedPair).2).Reachable
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge first)
            ((pair.sourceCrosscutComplementBoundaryProfileData data boundary
              ).crossingEdge second) := by
  let cutData := pair.sourceCrosscutComplementBoundaryProfileData data boundary
  let color := pair.sourceCrosscutComplementLiteralColorOnVertexSide data
    boundary hcubic coloring
  let hregion := pair.sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
    data boundary
  let hports := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    data boundary
  let hcrossing : ∀ crossing, color (cutData.crossingEdge crossing) ≠ 0 :=
    fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSide_ne_zero data
        boundary hcubic coloring hcoloring (hregion (hports (.inl crossing)))
  change (cutData.regionalProfile color hcrossing).strandConnected trackedPair
      (.inl first) (.inl second) = true ↔ _
  rw [cutData.regionalProfile_strandConnected_eq_true_iff]
  have hfirst : cutData.portEdge (.inl first) ∈ cutData.regionEdges :=
    hports (.inl first)
  have hsecond : cutData.portEdge (.inl second) ∈ cutData.regionEdges :=
    hports (.inl second)
  simp only [hfirst, hsecond, true_and]
  rfl

/-- Realizability of an abstract combined state supplies one literal coloring
and the exact connectivity semantics of every bit of that state. -/
theorem SourceCrosscutComplementCombinedProfileRealizable.exists_connectivity_semantics
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
    (profile : pair.SourceCrosscutComplementCombinedProfile data boundary)
    (hrealizable : pair.SourceCrosscutComplementCombinedProfileRealizable data
      boundary hcubic profile) :
    ∃ coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring data
        boundary hcubic,
      pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
          coloring.1 coloring.2 = profile ∧
        ∀ (trackedPair : TrackedColorPair)
          (first second : Fin (Fintype.card (VertexSetCrossingEdge
            data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ))),
          profile.strandConnected trackedPair (.inl first) (.inl second) = true ↔
            IsTrackedColor (trackedColorPairColors trackedPair).1
                (trackedColorPairColors trackedPair).2
                (pair.sourceCrosscutComplementLiteralColorOnVertexSide data
                  boundary hcubic coloring.1
                  ((pair.sourceCrosscutComplementBoundaryProfileData data
                    boundary).crossingEdge first)) ∧
              IsTrackedColor (trackedColorPairColors trackedPair).1
                (trackedColorPairColors trackedPair).2
                (pair.sourceCrosscutComplementLiteralColorOnVertexSide data
                  boundary hcubic coloring.1
                  ((pair.sourceCrosscutComplementBoundaryProfileData data
                    boundary).crossingEdge second)) ∧
              (regionalTrackedEdgeGraph data.toRotationSystem
                (pair.sourceCrosscutComplementBoundaryProfileData data boundary
                  ).regionEdges
                (pair.sourceCrosscutComplementLiteralColorOnVertexSide data
                  boundary hcubic coloring.1)
                (trackedColorPairColors trackedPair).1
                (trackedColorPairColors trackedPair).2).Reachable
                  ((pair.sourceCrosscutComplementBoundaryProfileData data
                    boundary).crossingEdge first)
                  ((pair.sourceCrosscutComplementBoundaryProfileData data
                    boundary).crossingEdge second) := by
  rcases hrealizable with ⟨coloring, hprofile⟩
  refine ⟨coloring, hprofile, ?_⟩
  intro trackedPair first second
  rw [← hprofile]
  exact pair.sourceCrosscutComplementLiteralOpenProfile_strandConnected_eq_true_iff
    data boundary hcubic coloring.1 coloring.2 trackedPair first second

/-- A literal removed Cell satisfies the finite serial-connectivity law when
its left and right boundary restrictions are used as the two exposed states.
The reverse implication is the substantive direction: a chain of input or
Cell profile moves is interpreted as a chain of paths in the one literal
regional graph, then composed there.

This theorem calibrates the finite relation against `Count`; it does not yet
identify either restricted state with a cumulative corridor-prefix state. -/
theorem sourceCrosscutComplementLiteralOpenProfile_serialConnectivity
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic
      ).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic
      ).IsTaitEdgeColoring coloring) :
    SerialProfileConnectivity
      (CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
          coloring hcoloring)
        (pair.sourceCrosscutComplementLeftCombinedIndex data boundary))
      (pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
        coloring hcoloring)
      (CorridorCutProfile.restrictCrossings
        (pair.sourceCrosscutComplementLiteralOpenProfile data boundary hcubic
          coloring hcoloring)
        (pair.sourceCrosscutComplementRightCombinedIndex data boundary))
      (pair.sourceCrosscutComplementLeftCombinedIndex data boundary)
      (pair.sourceCrosscutComplementRightCombinedIndex data boundary) := by
  let combined := pair.sourceCrosscutComplementLiteralOpenProfile data
    boundary hcubic coloring hcoloring
  let leftIndex := pair.sourceCrosscutComplementLeftCombinedIndex data boundary
  let rightIndex := pair.sourceCrosscutComplementRightCombinedIndex data boundary
  let cutData := pair.sourceCrosscutComplementBoundaryProfileData data boundary
  let color := pair.sourceCrosscutComplementLiteralColorOnVertexSide data
    boundary hcubic coloring
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
        (pair.sourceCrosscutComplementLiteralOpenProfile_strandConnected_eq_true_iff
          data boundary hcubic coloring hcoloring trackedPair
          (rightIndex first) (rightIndex second)).1 hconnected
      refine ⟨?_, ?_,
        serialProfileConnectivityClosure_of_cell
          (CorridorCutProfile.restrictCrossings combined leftIndex)
          combined leftIndex trackedPair (rightIndex first)
          (rightIndex second) hconnected⟩
      · rw [pair.sourceCrosscutComplementLiteralOpenProfile_edgeColor_toColor
          data boundary hcubic coloring hcoloring (rightIndex first)]
        exact hsemantic.1
      · rw [pair.sourceCrosscutComplementLiteralOpenProfile_edgeColor_toColor
          data boundary hcubic coloring hcoloring (rightIndex second)]
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
            (pair.sourceCrosscutComplementLiteralOpenProfile_strandConnected_eq_true_iff
              data boundary hcubic coloring hcoloring trackedPair
              (leftIndex left) (leftIndex right)).1 hinput |>.2.2
        · exact
            (pair.sourceCrosscutComplementLiteralOpenProfile_strandConnected_eq_true_iff
              data boundary hcubic coloring hcoloring trackedPair
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
        (pair.sourceCrosscutComplementLiteralOpenProfile_strandConnected_eq_true_iff
          data boundary hcubic coloring hcoloring trackedPair
          (rightIndex first) (rightIndex second)).2
      refine ⟨?_, ?_, hreachable⟩
      · rw [← pair.sourceCrosscutComplementLiteralOpenProfile_edgeColor_toColor
          data boundary hcubic coloring hcoloring (rightIndex first)]
        exact hfirstColor
      · rw [← pair.sourceCrosscutComplementLiteralOpenProfile_edgeColor_toColor
          data boundary hcubic coloring hcoloring (rightIndex second)]
        exact hsecondColor

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
