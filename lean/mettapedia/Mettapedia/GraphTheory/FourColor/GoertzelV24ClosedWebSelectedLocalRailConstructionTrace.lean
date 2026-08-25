import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailExactTerminalWindow

/-!
# L1: proof-relevant construction trace for the terminal rail window

The complete adjacent append exposes only the final endpoint order.  That is
the right consumer API, but it forgets which finite local repair produced the
pair.  A mutable-window induction needs that distinction: the remote prefix
may be frozen while the bounded terminal repair remains inspectable.

The existing length-resolved outcome already is the correct proof-relevant
trace.  Its six residual constructors retain the cross collision, the local
same-track or centre witness, and the finite length equations which force the
repair.  This module packages that value before it is erased, proves that it
is the canonical classifier result, and projects it back to the established
complete outcome and exact terminal-window certificate.

This does not construct the rolling transition, an arbitrary-length rail
pair, either end cap, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

/-- Apply the already-proved finite repair selected by a length-resolved
branch, retaining only its final endpoint order. -/
noncomputable def SelectedLocalRailAppendLengthResolvedOutcome.toComplete
    (resolved : SelectedLocalRailAppendLengthResolvedOutcome successor left) :
    SelectedLocalRailAppendCompleteOutcome successor left :=
  match resolved with
  | .straight assembly => .straight assembly
  | .swapped assembly => .swapped assembly
  | .firstSecondSameFirst cross same lengths =>
      match appendFirstSecondSameFirst cross same lengths with
      | .inl assembly => .straight assembly
      | .inr assembly => .swapped assembly
  | .firstSecondSameSecond cross same lengths =>
      match appendFirstSecondSameSecond cross same lengths with
      | .inl assembly => .straight assembly
      | .inr assembly => .swapped assembly
  | .firstSecondCenter cross center lengths =>
      match appendFirstSecondCenter cross center lengths with
      | .inl assembly => .straight assembly
      | .inr assembly => .swapped assembly
  | .secondFirstSameFirst cross same lengths =>
      match appendSecondFirstSameFirst cross same lengths with
      | .inl assembly => .straight assembly
      | .inr assembly => .swapped assembly
  | .secondFirstSameSecond cross same lengths =>
      match appendSecondFirstSameSecond cross same lengths with
      | .inl assembly => .straight assembly
      | .inr assembly => .swapped assembly
  | .secondFirstCenter cross center lengths =>
      match appendSecondFirstCenter cross center lengths with
      | .inl assembly => .straight assembly
      | .inr assembly => .swapped assembly

/-- Erasing the canonical length-resolved value gives the public complete
adjacent append definitionally. -/
@[simp] theorem classifyLocalSuccessorAppendLengthResolved_toComplete :
    (classifyLocalSuccessorAppendLengthResolved successor left).toComplete =
      appendLocalSuccessorComplete successor left := rfl

/-- A canonical adjacent terminal repair before its finite construction
branch is erased.

The `resolved` field can be pattern matched by the rolling-window transition;
the exact provenance field keeps every resulting support in the five literal
source pieces of this terminal window. -/
structure ExactSelectedLocalRailConstructionTrace
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) where
  resolved : SelectedLocalRailAppendLengthResolvedOutcome successor left
  resolved_eq : resolved = classifyLocalSuccessorAppendLengthResolved successor left
  hasExactWindowProvenance : resolved.HasExactWindowProvenance

/-- The proof-relevant trace produced by the actual adjacent classifier. -/
noncomputable def ExactSelectedLocalRailConstructionTrace.ofClassifier :
    ExactSelectedLocalRailConstructionTrace successor left :=
  ⟨classifyLocalSuccessorAppendLengthResolved successor left, rfl,
    classifyLocalSuccessorAppendLengthResolved_hasExactWindowProvenance⟩

/-- Forget the finite branch and run its already-proved repair. -/
noncomputable def ExactSelectedLocalRailConstructionTrace.toOutcome
    (trace : ExactSelectedLocalRailConstructionTrace successor left) :
    SelectedLocalRailAppendCompleteOutcome successor left :=
  trace.resolved.toComplete

/-- Every canonical trace erases to the established complete append. -/
theorem ExactSelectedLocalRailConstructionTrace.toOutcome_eq_complete
    (trace : ExactSelectedLocalRailConstructionTrace successor left) :
    trace.toOutcome = appendLocalSuccessorComplete successor left := by
  rw [ExactSelectedLocalRailConstructionTrace.toOutcome, trace.resolved_eq]
  exact classifyLocalSuccessorAppendLengthResolved_toComplete

/-- Project a proof-relevant trace to the exact five-piece terminal-window
certificate used by existing remote-separation consumers. -/
noncomputable def ExactSelectedLocalRailConstructionTrace.toExactTerminalWindow
    (trace : ExactSelectedLocalRailConstructionTrace successor left) :
    ExactCertifiedSelectedLocalRailTerminalWindow successor left := by
  refine ⟨trace.toOutcome, ?_⟩
  rw [trace.toOutcome_eq_complete]
  exact appendLocalSuccessorComplete_hasExactWindowProvenance

/-- The canonical construction trace has the same public outcome as the
canonical exact terminal window. -/
@[simp] theorem ExactSelectedLocalRailConstructionTrace.ofClassifier_outcome :
    (ExactSelectedLocalRailConstructionTrace.ofClassifier
      (successor := successor) (left := left)).toOutcome =
      ExactCertifiedSelectedLocalRailTerminalWindow.ofComplete.outcome := rfl

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
