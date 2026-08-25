import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt

/-!
# A colouring-parametric five-field boundary-rebase output

The tracked two-factor collar now accepts an arbitrary colour function.  This
file threads the same parameter through the successor tracked receipt and the
complete terminal-aware output profile.  The occurrence-sensitive facial
receipt is reused unchanged: its equivalence classes, port incidences, and
capped lengths depend on the region and rotation system, not on edge colours.

The resulting native Boolean output packet decodes exactly to the successor
five-field regional profile at the supplied colouring.  At the ambient web
colouring both the packet and the profile specialize to the earlier source
objects.  No positive-`Count` composition or reachable closure is claimed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorSkeleton
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryRebaseOutputColorParametricEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The next terminal-aware source profile evaluated at an arbitrary colour
function.  Only the two displayed crossing edges require nonzero witnesses;
the terminal colour remains observable through tracked connectivity. -/
noncomputable def terminalInputBoundedProfileForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet -> Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    BoundedCorridorCutProfile 2 1 4 where
  faceFragmentCount :=
    ⟨Fintype.card (BoundaryRegionalFragment web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerLeftCrossingAt corridor hunique offset))
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)),
      Nat.lt_succ_of_le
        (regionalBoundaryGraphCutData_fragmentCount_le_two_mul web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          (sourceLocalLayerLeftCrossingAt corridor hunique offset))⟩
  profile :=
    (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
      ).regionalProfile color hcrossing

@[simp]
theorem terminalInputBoundedProfileForColorAt_ambient
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    terminalInputBoundedProfileForColorAt corridor hunique offset coloring
        (fun _ => web.tait _) =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        offset := by
  rfl

/-- Exact successor tracked data at an arbitrary colour function. -/
noncomputable def successorTrackedStateForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) : SourceLocalLayerBoundaryRebaseTrackedState where
  roleColor := fun role => strandColorOfNonzero
    (color (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
      role)) (hrole role)
  roleInRegion := fun role => decide
    (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))
  trackedResidual := fun pair =>
    exactSupportedPortResidualCode
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
      Empty.elim

@[simp]
theorem successorTrackedStateForColorAt_ambient
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    successorTrackedStateForColorAt corridor hunique offset hnext coloring
        (fun _ => web.tait _) =
      sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt corridor hunique
        offset hnext := by
  simp only [successorTrackedStateForColorAt,
    sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt,
    successorTrackedGraphForColorAt]

theorem successorTrackedStateForColorAt_connected_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (successorTrackedStateForColorAt corridor hunique offset hnext color hrole
      ).connected pair left right ↔
      regionalTrackedConnectivity web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)) color pair
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) = true := by
  let graph := successorTrackedGraphForColorAt corridor hunique offset hnext
    color pair
  let edgeAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
  have hreachable :
      graph.Reachable (edgeAt left) (edgeAt right) ↔
        SupportedPortResidualFactoredReachability
          (exactSupportedPortResidualCode graph edgeAt Empty.elim)
          (fun _ _ : Empty => False) left right := by
    apply reachable_iff_exactSupportedPortResidualFactoredReachability
    · intro port
      exact port.elim
    · intro port
      exact port.elim
  rw [regionalTrackedConnectivity_eq_true_iff]
  simp only [SourceLocalLayerBoundaryRebaseTrackedState.connected,
    successorTrackedStateForColorAt, strandColorOfNonzero_toColor]
  change (_ ∧ _ ∧ _ ∧ _ ∧
      SupportedPortResidualFactoredReachability
        (exactSupportedPortResidualCode graph edgeAt Empty.elim)
        (fun _ _ : Empty => False) left right) ↔
    _ ∧ _ ∧ _ ∧ _ ∧ graph.Reachable (edgeAt left) (edgeAt right)
  rw [hreachable]
  simp

/-- The complete native Boolean successor packet at an arbitrary colouring.
The facial half is the same literal geometric receipt. -/
noncomputable def finiteBoolOutputLetterCodeForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) : SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode where
  outputCount :=
    (sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt corridor hunique
      offset hnext).outputCount
  tracked := successorTrackedStateForColorAt corridor hunique offset hnext color
    hrole
  facial :=
    (sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt corridor hunique
      offset hnext).facial

@[simp]
theorem finiteBoolOutputLetterCodeForColorAt_ambient
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    finiteBoolOutputLetterCodeForColorAt corridor hunique offset hnext coloring
        (fun _ => web.tait _) =
      sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt corridor hunique
        offset hnext := by
  rw [SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.mk.injEq]
  refine ⟨rfl, ?_, rfl⟩
  exact successorTrackedStateForColorAt_ambient corridor hunique offset hnext

/-- Nonzero colors on the named rebase roles include the two successor
crossings.  Keeping this as a named theorem makes the proof argument of the
color-parametric successor profile stable for later support letters. -/
theorem successorCrossingNonzeroForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) :
    ∀ step, color
      ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).crossingEdge step) ≠ 0 := by
  intro step
  have h := hrole
    (sourceLocalLayerBoundaryRebaseSuccessorPortRole (.inl step))
  rw [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole] at h
  simpa [sourceLocalLayerBoundaryRebaseSuccessorCutDataAt,
    GraphCorridorCutData.portEdge] using h

/-- The color-parametric native packet decodes all five fields of the literal
successor profile.  Thus changing the local Cell coloring changes exactly the
two color-sensitive fields while retaining the proved facial receipt. -/
theorem finiteBoolOutputLetterCodeForColorAt_outputProfile_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) :
    (finiteBoolOutputLetterCodeForColorAt corridor hunique offset hnext color
      hrole).outputProfile =
      terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole) := by
  classical
  let output := terminalInputBoundedProfileForColorAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext) color
      (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
        hrole)
  let code := finiteBoolOutputLetterCodeForColorAt corridor hunique offset hnext
    color hrole
  simp only [finiteBoolOutputLetterCodeForColorAt,
    SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputProfile,
    terminalInputBoundedProfileForColorAt,
    sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt,
    ofFiniteOutputLetterCode,
    sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt,
    sourceLocalLayerSerialTerminalInputBoundedProfileAt]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext crossing
    apply StrandColor.toColor_injective
    simp only [successorTrackedStateForColorAt, strandColorOfNonzero_toColor]
    rw [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole]
    exact (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique
      offset hnext).regionalProfile_edgeColor_toColor color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole) crossing |>.symm
  · funext pair left right
    apply Bool.eq_iff_iff.mpr
    simp only [trackedConnectedBool_eq_true_iff]
    rw [successorTrackedStateForColorAt_connected_iff]
    change _ ↔
      ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
        hnext).regionalProfile color
          (successorCrossingNonzeroForColorAt corridor hunique offset hnext
            color hrole)).strandConnected pair left right = true
    rw [(sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalProfile_strandConnected_eq_true_iff]
    simp only [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole,
      sourceLocalLayerBoundaryRebaseSuccessorCutDataAt,
      sourceLocalLayerSerialTerminalInputCutDataAt_regionEdges]
    rw [regionalTrackedConnectivity_eq_true_iff]
  · funext left right
    change
      (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
        offset hnext).facial.faceContinues
          (code.outputFaceSlot left) (code.outputFaceSlot right) =
        output.profile.faceContinues left right
    have hslot (fragment : Fin output.faceFragmentCount.val) :
        code.outputFaceSlot fragment =
          sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
            hunique offset hnext
            (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
              hunique offset hnext fragment) := by
      rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
      apply Fin.ext
      rfl
    rw [hslot left, hslot right]
    exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceContinues
      corridor hunique offset hnext left right
  · funext fragment port
    change
      (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
        offset hnext).facial.fragmentContainsPort
          (code.outputFaceSlot fragment) port =
        output.profile.fragmentContainsPort fragment port
    have hslot : code.outputFaceSlot fragment =
        sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment) := by
      rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
      apply Fin.ext
      rfl
    rw [hslot]
    exact
      sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_fragmentContainsPort
        corridor hunique offset hnext fragment port
  · funext fragment
    change
      (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
        offset hnext).facial.faceLengthCap (code.outputFaceSlot fragment) =
        output.profile.faceLengthCap fragment
    have hslot : code.outputFaceSlot fragment =
        sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment) := by
      rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
      apply Fin.ext
      rfl
    rw [hslot]
    exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceLengthCap
      corridor hunique offset hnext fragment

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric

end Mettapedia.GraphTheory.FourColor
