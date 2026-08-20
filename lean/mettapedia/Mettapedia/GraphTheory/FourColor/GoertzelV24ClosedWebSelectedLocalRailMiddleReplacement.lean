import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleCollisionClearance
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairRetainedSupport

/-!
# L1: replace the overlapping middle window by its canonical repair

The canonical four-cell collision packet contains three adjacent two-cell
windows.  When its middle band is selected, the middle construction trace
already supplies a literal separated repair.  This file splices that repair
between the untouched first-cell rails and the untouched fourth-cell
continuations.

Both joins are tested after loop erasure.  A successful branch therefore
returns a concrete four-cell `SelectedSourceLocalRailAssembly`; a failing
branch retains the exact first or second join, endpoint parity, and surviving
collision witness.  No disjointness premise is added.

The result is a fail-closed middle replacement, not yet a proof that either
join must succeed, an arbitrary-length rolling transition, either end cap, a
pair of simple dual crosscuts, or closure of Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {firstPlacement : SelectedInternalHexRungPlacement corridor rungs firstInterior}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev BridgeLeft :=
  firstSuccessor.rightRailsAsNextLeft bridge

private abbrev StraightMiddleAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)

private abbrev SwappedMiddleAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)

/-- The literal fourth-cell continuation pair, packaged with its already
proved path and separation certificates. -/
noncomputable def continuationAssembly
    (successor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement) :
    SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace thirdPlacement successor.frame.leftBefore)
      (selectedPlacementSideFace thirdPlacement successor.frame.leftAfter)
      (selectedPlacementSideFace fourthPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace fourthPlacement successor.rightOutgoingAfter) where
  firstRail := successor.firstContinuation
  secondRail := successor.secondContinuation
  firstRail_isPath := successor.firstContinuation_isPath
  secondRail_isPath := successor.secondContinuation_isPath
  firstRail_support_disjoint_secondRail :=
    successor.firstContinuation_support_disjoint_secondContinuation

private noncomputable def rebaseMiddleStraight
    (assembly : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :=
  rebaseAssemblyStart assembly
    firstSuccessor.frame.leftBeforeFace_eq_rightAfterFace.symm
    firstSuccessor.frame.leftAfterFace_eq_rightBeforeFace.symm

private noncomputable def rebaseMiddleSwapped
    (assembly : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :=
  rebaseAssemblyStart assembly
    firstSuccessor.frame.leftBeforeFace_eq_rightAfterFace.symm
    firstSuccessor.frame.leftAfterFace_eq_rightBeforeFace.symm

private noncomputable def rebaseLastContinuation :=
  rebaseAssemblyStart (continuationAssembly lastSuccessor)
    (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingBefore_eq_nextLeftBefore lastSuccessor)).symm
    (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingAfter_eq_nextLeftAfter lastSuccessor)).symm

/-- Exact surviving collision data from one of the two joins of a canonical
middle replacement.  The constructors retain the middle branch and the
classifier equation, so this cannot be inhabited by merely postulating a
failure face. -/
inductive ExactSelectedLocalRailMiddleReplacementCollision
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (face : SelectedFace (web := web)) : Prop
  | straightLeft
      (middle : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle)
      (witness : RetainedBypassCrossCollision firstLeft.toAssembly
        (rebaseMiddleStraight middle))
      (hclassified : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleStraight middle) = .collision witness)
      (hface : witness.face = face)
  | swappedLeft
      (middle : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle)
      (witness : RetainedBypassCrossCollision firstLeft.toAssembly
        (rebaseMiddleSwapped middle))
      (hclassified : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleSwapped middle) = .collision witness)
      (hface : witness.face = face)
  | straightRight
      (middle : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle)
      (prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter))
      (hleft : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleStraight middle) = .assembled prefixMiddle)
      (witness : RetainedBypassCrossCollision prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)))
      (hright : classifyRetainedBypassAppend prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)) =
        .collision witness)
      (hface : witness.face = face)
  | swappedRight
      (middle : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle)
      (prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore))
      (hleft : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleSwapped middle) = .assembled prefixMiddle)
      (witness : CrossedRetainedBypassCrossCollision prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)))
      (hright : classifyCrossedRetainedBypassAppend prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)) =
        .collision witness)
      (hface : witness.face = face)

/-- Result of replacing the overlapping middle window and testing both of
its literal joins after loop erasure. -/
inductive ExactSelectedLocalRailMiddleReplacementOutcome
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) : Type (u + 1)
  | straight
      (middle : StraightMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle)
      (prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter))
      (hleft : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleStraight middle) = .assembled prefixMiddle)
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingAfter))
      (hright : classifyRetainedBypassAppend prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)) = .assembled assembly)
  | swapped
      (middle : SwappedMiddleAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle)
      (prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore))
      (hleft : classifyRetainedBypassAppend firstLeft.toAssembly
        (rebaseMiddleSwapped middle) = .assembled prefixMiddle)
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fourthPlacement lastSuccessor.rightOutgoingBefore))
      (hright : classifyCrossedRetainedBypassAppend prefixMiddle
        (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)) = .assembled assembly)
  | collision
      (face : SelectedFace (web := web))
      (data : ExactSelectedLocalRailMiddleReplacementCollision
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)

/-- Classify the literal replacement selected by the canonical middle trace.
The returned collision-avoiding rail is retained separately by
`collisionAvoidingMiddleRail`; this classifier tests whether the whole pair
can be joined to both untouched outer cells. -/
noncomputable def classifyExactSelectedLocalRailMiddleReplacement
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace := by
  classical
  cases hresult : trace.toOutcome with
  | straight middle =>
      cases hleft : classifyRetainedBypassAppend firstLeft.toAssembly
          (rebaseMiddleStraight middle) with
      | collision witness =>
          exact .collision witness.face
            (.straightLeft middle hresult witness hleft rfl)
      | assembled prefixMiddle =>
          cases hright : classifyRetainedBypassAppend prefixMiddle
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)) with
          | assembled assembly =>
              exact .straight middle hresult prefixMiddle hleft assembly hright
          | collision witness =>
              exact .collision witness.face
                (.straightRight middle hresult prefixMiddle hleft witness hright rfl)
  | swapped middle =>
      cases hleft : classifyRetainedBypassAppend firstLeft.toAssembly
          (rebaseMiddleSwapped middle) with
      | collision witness =>
          exact .collision witness.face
            (.swappedLeft middle hresult witness hleft rfl)
      | assembled prefixMiddle =>
          cases hright : classifyCrossedRetainedBypassAppend prefixMiddle
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)) with
          | assembled assembly =>
              exact .swapped middle hresult prefixMiddle hleft assembly hright
          | collision witness =>
              exact .collision witness.face
                (.swappedRight middle hresult prefixMiddle hleft witness hright rfl)

/-- A face lies on one of the three literal assembly packets used by a middle
replacement: the untouched first cell, the rebased canonical middle repair,
or the untouched fourth-cell continuation. -/
def FaceInMiddleReplacementSplicePieces
    {middleFirstFinish middleSecondFinish : SelectedFace (web := web)}
    (middle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
      middleFirstFinish middleSecondFinish)
    (face : SelectedFace (web := web)) : Prop :=
  face ∈ firstLeft.toAssembly.firstRail.support ∨
    face ∈ firstLeft.toAssembly.secondRail.support ∨
    face ∈ middle.firstRail.support ∨
    face ∈ middle.secondRail.support ∨
    face ∈ (rebaseLastContinuation (bridge := bridge)
      (lastSuccessor := lastSuccessor)).firstRail.support ∨
    face ∈ (rebaseLastContinuation (bridge := bridge)
      (lastSuccessor := lastSuccessor)).secondRail.support

private theorem faceInMiddleReplacementSplicePieces_of_prefixMiddle
    {middleFirstFinish middleSecondFinish : SelectedFace (web := web)}
    {middle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
      middleFirstFinish middleSecondFinish}
    {prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)
      middleFirstFinish middleSecondFinish}
    (hprovenance : AssemblySupportContainedInAssemblyPair
      firstLeft.toAssembly middle prefixMiddle)
    {face : SelectedFace (web := web)}
    (hface : face ∈ prefixMiddle.firstRail.support ∨
      face ∈ prefixMiddle.secondRail.support) :
    FaceInMiddleReplacementSplicePieces
      (bridge := bridge) (lastSuccessor := lastSuccessor)
      (firstLeft := firstLeft) middle face := by
  rcases hface with hfirst | hsecond
  · rcases hprovenance.1 face hfirst with
      holdFirst | holdSecond | hmiddleFirst | hmiddleSecond
    · exact .inl holdFirst
    · exact .inr (.inl holdSecond)
    · exact .inr (.inr (.inl hmiddleFirst))
    · exact .inr (.inr (.inr (.inl hmiddleSecond)))
  · rcases hprovenance.2 face hsecond with
      holdFirst | holdSecond | hmiddleFirst | hmiddleSecond
    · exact .inl holdFirst
    · exact .inr (.inl holdSecond)
    · exact .inr (.inr (.inl hmiddleFirst))
    · exact .inr (.inr (.inr (.inl hmiddleSecond)))

private theorem faceInMiddleReplacementSplicePieces_of_final
    {middleFirstFinish middleSecondFinish finalFirst finalSecond :
      SelectedFace (web := web)}
    {middle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
      middleFirstFinish middleSecondFinish}
    {prefixMiddle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)
      middleFirstFinish middleSecondFinish}
    {finalAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)
      finalFirst finalSecond}
    (hleft : AssemblySupportContainedInAssemblyPair
      firstLeft.toAssembly middle prefixMiddle)
    (hright : AssemblySupportContainedInAssemblyPair prefixMiddle
      (rebaseLastContinuation (bridge := bridge)
        (lastSuccessor := lastSuccessor)) finalAssembly)
    {face : SelectedFace (web := web)}
    (hface : face ∈ finalAssembly.firstRail.support ∨
      face ∈ finalAssembly.secondRail.support) :
    FaceInMiddleReplacementSplicePieces
      (bridge := bridge) (lastSuccessor := lastSuccessor)
      (firstLeft := firstLeft) middle face := by
  have hsource := hface.elim (hright.1 face) (hright.2 face)
  rcases hsource with hprefixFirst | hprefixSecond | hlastFirst | hlastSecond
  · exact faceInMiddleReplacementSplicePieces_of_prefixMiddle hleft
      (.inl hprefixFirst)
  · exact faceInMiddleReplacementSplicePieces_of_prefixMiddle hleft
      (.inr hprefixSecond)
  · exact .inr (.inr (.inr (.inr (.inl hlastFirst))))
  · exact .inr (.inr (.inr (.inr (.inr hlastSecond))))

/-- Source-piece membership expressed only through the canonical trace, not
through the proof term witnessing which classifier branch was taken. -/
def FaceInCanonicalMiddleReplacementSplicePieces
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (face : SelectedFace (web := web)) : Prop :=
  match trace.toOutcome with
  | .straight middle =>
      FaceInMiddleReplacementSplicePieces
        (bridge := bridge) (lastSuccessor := lastSuccessor)
        (firstLeft := firstLeft) (rebaseMiddleStraight middle) face
  | .swapped middle =>
      FaceInMiddleReplacementSplicePieces
        (bridge := bridge) (lastSuccessor := lastSuccessor)
        (firstLeft := firstLeft) (rebaseMiddleSwapped middle) face

/-- Both first-join and second-join collision constructors carry a literal
source-piece membership witness. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.hasSourcePieceMembership
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    FaceInCanonicalMiddleReplacementSplicePieces
      (bridge := bridge) (lastSuccessor := lastSuccessor)
      (firstLeft := firstLeft) trace face := by
  cases data with
  | straightLeft middle hresult witness hclassified hface =>
      subst face
      simp only [FaceInCanonicalMiddleReplacementSplicePieces, hresult]
      cases witness.origin with
      | firstSecond hold hnew => exact .inl hold
      | secondFirst hold hnew => exact .inr (.inl hold)
  | swappedLeft middle hresult witness hclassified hface =>
      subst face
      simp only [FaceInCanonicalMiddleReplacementSplicePieces, hresult]
      cases witness.origin with
      | firstSecond hold hnew => exact .inl hold
      | secondFirst hold hnew => exact .inr (.inl hold)
  | straightRight middle hresult prefixMiddle hleft witness hright hface =>
      subst face
      simp only [FaceInCanonicalMiddleReplacementSplicePieces, hresult]
      cases witness.origin with
      | firstSecond hold hnew =>
          exact .inr (.inr (.inr (.inr (.inr (List.mem_of_mem_tail hnew)))))
      | secondFirst hold hnew =>
          exact .inr (.inr (.inr (.inr (.inl (List.mem_of_mem_tail hnew)))))
  | swappedRight middle hresult prefixMiddle hleft witness hright hface =>
      subst face
      simp only [FaceInCanonicalMiddleReplacementSplicePieces, hresult]
      cases witness.origin with
      | firstFirst hold hnew =>
          exact .inr (.inr (.inr (.inr (.inl (List.mem_of_mem_tail hnew)))))
      | secondSecond hold hnew =>
          exact .inr (.inr (.inr (.inr (.inr (List.mem_of_mem_tail hnew)))))

/-- Exact source-support receipt on every success and collision branch of the
two-stage replacement. -/
def ExactSelectedLocalRailMiddleReplacementOutcome.HasSourceSupportProvenance
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    (outcome : ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace) : Prop :=
  match outcome with
  | .straight middle _ _ _ assembly _ =>
      (∀ face ∈ assembly.firstRail.support,
          FaceInMiddleReplacementSplicePieces
            (bridge := bridge) (lastSuccessor := lastSuccessor)
            (firstLeft := firstLeft)
            (rebaseMiddleStraight middle) face) ∧
        ∀ face ∈ assembly.secondRail.support,
          FaceInMiddleReplacementSplicePieces
            (bridge := bridge) (lastSuccessor := lastSuccessor)
            (firstLeft := firstLeft)
            (rebaseMiddleStraight middle) face
  | .swapped middle _ _ _ assembly _ =>
      (∀ face ∈ assembly.firstRail.support,
          FaceInMiddleReplacementSplicePieces
            (bridge := bridge) (lastSuccessor := lastSuccessor)
            (firstLeft := firstLeft)
            (rebaseMiddleSwapped middle) face) ∧
        ∀ face ∈ assembly.secondRail.support,
          FaceInMiddleReplacementSplicePieces
            (bridge := bridge) (lastSuccessor := lastSuccessor)
            (firstLeft := firstLeft)
            (rebaseMiddleSwapped middle) face
  | .collision face _ =>
      FaceInCanonicalMiddleReplacementSplicePieces
        (bridge := bridge) (lastSuccessor := lastSuccessor)
        (firstLeft := firstLeft) trace face

/-- The canonical middle-replacement classifier introduces no face outside
the three literal packets which it splices. -/
theorem ExactSelectedLocalRailMiddleReplacementOutcome.hasSourceSupportProvenance
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    (outcome : ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace) :
    outcome.HasSourceSupportProvenance := by
  classical
  cases outcome with
  | straight middle hresult prefixMiddle hclassified assembly hfinal =>
      have hleft := classifyRetainedBypassAppend_hasSupportProvenance
        firstLeft.toAssembly (rebaseMiddleStraight middle)
      rw [hclassified] at hleft
      have hright := classifyRetainedBypassAppend_hasSupportProvenance
        prefixMiddle (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor))
      rw [hfinal] at hright
      exact ⟨
        fun face hface => faceInMiddleReplacementSplicePieces_of_final
          hleft hright (.inl hface),
        fun face hface => faceInMiddleReplacementSplicePieces_of_final
          hleft hright (.inr hface)⟩
  | swapped middle hresult prefixMiddle hclassified assembly hfinal =>
      have hleft := classifyRetainedBypassAppend_hasSupportProvenance
        firstLeft.toAssembly (rebaseMiddleSwapped middle)
      rw [hclassified] at hleft
      have hright := classifyCrossedRetainedBypassAppend_hasSupportProvenance
        prefixMiddle (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor))
      rw [hfinal] at hright
      exact ⟨
        fun face hface => faceInMiddleReplacementSplicePieces_of_final
          hleft hright (.inl hface),
        fun face hface => faceInMiddleReplacementSplicePieces_of_final
          hleft hright (.inr hface)⟩
  | collision face data => exact data.hasSourcePieceMembership

/-- Membership in the canonical repaired middle packet, with its endpoint
parity read from the construction trace rather than supplied independently. -/
def FaceInCanonicalMiddleRepair
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (face : SelectedFace (web := web)) : Prop :=
  match trace.toOutcome with
  | .straight middle =>
      face ∈ (rebaseMiddleStraight middle).firstRail.support ∨
        face ∈ (rebaseMiddleStraight middle).secondRail.support
  | .swapped middle =>
      face ∈ (rebaseMiddleSwapped middle).firstRail.support ∨
        face ∈ (rebaseMiddleSwapped middle).secondRail.support

/-- After the first-to-fourth remote term is removed, a surviving collision
of the canonical middle replacement lies in one of the two literal adjacent
join bands. -/
inductive ExactSelectedLocalRailMiddleReplacementLocalBand
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (face : SelectedFace (web := web)) : Prop
  | firstMiddle
      (first : face ∈ firstLeft.toAssembly.firstRail.support ∨
        face ∈ firstLeft.toAssembly.secondRail.support)
      (middle : FaceInCanonicalMiddleRepair
        (firstSuccessor := firstSuccessor) (bridge := bridge) trace face)
  | middleLast
      (middle : FaceInCanonicalMiddleRepair
        (firstSuccessor := firstSuccessor) (bridge := bridge) trace face)
      (last : face ∈ (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)).firstRail.support ∨
        face ∈ (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)).secondRail.support)

private theorem firstPiece_disjoint_lastPiece
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {face : SelectedFace (web := web)}
    (hfirst : face ∈ firstLeft.toAssembly.firstRail.support ∨
      face ∈ firstLeft.toAssembly.secondRail.support)
    (hlast : face ∈ (rebaseLastContinuation (bridge := bridge)
        (lastSuccessor := lastSuccessor)).firstRail.support ∨
      face ∈ (rebaseLastContinuation (bridge := bridge)
        (lastSuccessor := lastSuccessor)).secondRail.support) : False := by
  have hgap : firstInterior.center.val + 2 <
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val := by
    change firstInterior.center.val + 2 < firstInterior.center.val + 3
    omega
  rcases hfirst with hfirst | hsecond <;>
    rcases hlast with hlast | hlast
  · exact (List.disjoint_left.mp
      (SelectedSourceLocalRailPaths.firstRail_support_disjoint_firstRail_of_add_two_lt
        hsource firstLeft.paths lastSuccessor.rightRails.paths hgap) (by
          simpa using hfirst)) (by
          simpa [rebaseLastContinuation, continuationAssembly] using hlast)
  · exact (List.disjoint_left.mp
      (SelectedSourceLocalRailPaths.firstRail_support_disjoint_secondRail_of_add_two_lt
        hsource firstLeft.paths lastSuccessor.rightRails.paths hgap) (by
          simpa using hfirst)) (by
          simpa [rebaseLastContinuation, continuationAssembly] using hlast)
  · exact (List.disjoint_left.mp
      (SelectedSourceLocalRailPaths.secondRail_support_disjoint_firstRail_of_add_two_lt
        hsource firstLeft.paths lastSuccessor.rightRails.paths hgap) (by
          simpa using hsecond)) (by
          simpa [rebaseLastContinuation, continuationAssembly] using hlast)
  · exact (List.disjoint_left.mp
      (SelectedSourceLocalRailPaths.secondRail_support_disjoint_secondRail_of_add_two_lt
        hsource firstLeft.paths lastSuccessor.rightRails.paths hgap) (by
          simpa using hsecond)) (by
          simpa [rebaseLastContinuation, continuationAssembly] using hlast)

/-- **L1 bounded collision localization.** Source boundary-cleanliness rules
out the sole nonlocal first-to-fourth term in the two-stage replacement.
Every surviving bad branch is therefore an exact contact across the left or
right adjacent join of the repaired middle packet. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.hasLocalBand
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    ExactSelectedLocalRailMiddleReplacementLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face := by
  classical
  cases data with
  | straightLeft middle hresult witness hclassified hface =>
      subst face
      have hmiddle : FaceInCanonicalMiddleRepair
          (firstSuccessor := firstSuccessor) (bridge := bridge)
          trace witness.face := by
        simp only [FaceInCanonicalMiddleRepair, hresult]
        cases witness.origin with
        | firstSecond hold hnew =>
            exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew =>
            exact .inl (List.mem_of_mem_tail hnew)
      cases witness.origin with
      | firstSecond hold hnew => exact .firstMiddle (.inl hold) hmiddle
      | secondFirst hold hnew => exact .firstMiddle (.inr hold) hmiddle
  | swappedLeft middle hresult witness hclassified hface =>
      subst face
      have hmiddle : FaceInCanonicalMiddleRepair
          (firstSuccessor := firstSuccessor) (bridge := bridge)
          trace witness.face := by
        simp only [FaceInCanonicalMiddleRepair, hresult]
        cases witness.origin with
        | firstSecond hold hnew =>
            exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew =>
            exact .inl (List.mem_of_mem_tail hnew)
      cases witness.origin with
      | firstSecond hold hnew => exact .firstMiddle (.inl hold) hmiddle
      | secondFirst hold hnew => exact .firstMiddle (.inr hold) hmiddle
  | straightRight middle hresult prefixMiddle hleft witness hright hface =>
      subst face
      have hprovenance := classifyRetainedBypassAppend_hasSupportProvenance
        firstLeft.toAssembly (rebaseMiddleStraight middle)
      rw [hleft] at hprovenance
      cases witness.origin with
      | firstSecond hold hnew =>
          have hlast : witness.face ∈
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)).secondRail.support :=
            List.mem_of_mem_tail hnew
          rcases hprovenance.1 witness.face hold with
            hfirst | hsecond | hmiddleFirst | hmiddleSecond
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inl hfirst) (.inr hlast))
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inr hsecond) (.inr hlast))
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inl hmiddleFirst) (.inr hlast)
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inr hmiddleSecond) (.inr hlast)

      | secondFirst hold hnew =>
          have hlast : witness.face ∈
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)).firstRail.support :=
            List.mem_of_mem_tail hnew
          rcases hprovenance.2 witness.face hold with
            hfirst | hsecond | hmiddleFirst | hmiddleSecond
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inl hfirst) (.inl hlast))
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inr hsecond) (.inl hlast))
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inl hmiddleFirst) (.inl hlast)
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inr hmiddleSecond) (.inl hlast)
  | swappedRight middle hresult prefixMiddle hleft witness hright hface =>
      subst face
      have hprovenance := classifyRetainedBypassAppend_hasSupportProvenance
        firstLeft.toAssembly (rebaseMiddleSwapped middle)
      rw [hleft] at hprovenance
      cases witness.origin with
      | firstFirst hold hnew =>
          have hlast : witness.face ∈
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)).firstRail.support :=
            List.mem_of_mem_tail hnew
          rcases hprovenance.1 witness.face hold with
            hfirst | hsecond | hmiddleFirst | hmiddleSecond
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inl hfirst) (.inl hlast))
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inr hsecond) (.inl hlast))
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inl hmiddleFirst) (.inl hlast)
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inr hmiddleSecond) (.inl hlast)
      | secondSecond hold hnew =>
          have hlast : witness.face ∈
              (rebaseLastContinuation (bridge := bridge)
                (lastSuccessor := lastSuccessor)).secondRail.support :=
            List.mem_of_mem_tail hnew
          rcases hprovenance.2 witness.face hold with
            hfirst | hsecond | hmiddleFirst | hmiddleSecond
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inl hfirst) (.inr hlast))
          · exact False.elim (firstPiece_disjoint_lastPiece hsource
              (.inr hsecond) (.inr hlast))
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inl hmiddleFirst) (.inr hlast)
          · exact .middleLast (by
              simp only [FaceInCanonicalMiddleRepair, hresult]
              exact .inr hmiddleSecond) (.inr hlast)

/-- A surviving middle-replacement collision is never either literal flank
face at the first/second-cell interface.  A left-join collision is excluded
from the two starts of the retained suffix.  A right-join collision would
otherwise meet both the first and fourth source packets, contradicting their
proved remote separation. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.face_ne_firstFlanks
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    face ≠ selectedPlacementSideFace firstPlacement
        firstSuccessor.frame.leftBefore ∧
      face ≠ selectedPlacementSideFace firstPlacement
        firstSuccessor.frame.leftAfter := by
  constructor
  · intro hfaceEq
    cases data with
    | straightLeft middle hresult witness hclassified hface =>
        exact witness.face_ne_newFirstStart (hface.trans hfaceEq)
    | swappedLeft middle hresult witness hclassified hface =>
        exact witness.face_ne_newFirstStart (hface.trans hfaceEq)
    | straightRight middle hresult prefixMiddle hleft witness hright hface =>
        have hfirst : face ∈ firstLeft.toAssembly.firstRail.support := by
          rw [hfaceEq]
          simp
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).firstRail.support ∨
          face ∈ (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).secondRail.support := by
          cases witness.origin with
          | firstSecond hold hnew => exact .inr (by
              simpa [hface] using List.mem_of_mem_tail hnew)
          | secondFirst hold hnew => exact .inl (by
              simpa [hface] using List.mem_of_mem_tail hnew)
        exact firstPiece_disjoint_lastPiece hsource (.inl hfirst) hlast
    | swappedRight middle hresult prefixMiddle hleft witness hright hface =>
        have hfirst : face ∈ firstLeft.toAssembly.firstRail.support := by
          rw [hfaceEq]
          simp
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).firstRail.support ∨
          face ∈ (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).secondRail.support := by
          cases witness.origin with
          | firstFirst hold hnew => exact .inl (by
              simpa [hface] using List.mem_of_mem_tail hnew)
          | secondSecond hold hnew => exact .inr (by
              simpa [hface] using List.mem_of_mem_tail hnew)
        exact firstPiece_disjoint_lastPiece hsource (.inl hfirst) hlast
  · intro hfaceEq
    cases data with
    | straightLeft middle hresult witness hclassified hface =>
        exact witness.face_ne_newSecondStart (hface.trans hfaceEq)
    | swappedLeft middle hresult witness hclassified hface =>
        exact witness.face_ne_newSecondStart (hface.trans hfaceEq)
    | straightRight middle hresult prefixMiddle hleft witness hright hface =>
        have hfirst : face ∈ firstLeft.toAssembly.secondRail.support := by
          rw [hfaceEq]
          simp
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).firstRail.support ∨
          face ∈ (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).secondRail.support := by
          cases witness.origin with
          | firstSecond hold hnew => exact .inr (by
              simpa [hface] using List.mem_of_mem_tail hnew)
          | secondFirst hold hnew => exact .inl (by
              simpa [hface] using List.mem_of_mem_tail hnew)
        exact firstPiece_disjoint_lastPiece hsource (.inr hfirst) hlast
    | swappedRight middle hresult prefixMiddle hleft witness hright hface =>
        have hfirst : face ∈ firstLeft.toAssembly.secondRail.support := by
          rw [hfaceEq]
          simp
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).firstRail.support ∨
          face ∈ (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).secondRail.support := by
          cases witness.origin with
          | firstFirst hold hnew => exact .inl (by
              simpa [hface] using List.mem_of_mem_tail hnew)
          | secondSecond hold hnew => exact .inr (by
              simpa [hface] using List.mem_of_mem_tail hnew)
        exact firstPiece_disjoint_lastPiece hsource (.inr hfirst) hlast

/-- Symmetrically, a surviving middle-replacement collision is never either
literal flank face at the third/fourth-cell interface. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.face_ne_lastFlanks
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    face ≠ selectedPlacementSideFace thirdPlacement
        lastSuccessor.frame.leftBefore ∧
      face ≠ selectedPlacementSideFace thirdPlacement
        lastSuccessor.frame.leftAfter := by
  constructor
  · intro hfaceEq
    cases data with
    | straightLeft middle hresult witness hclassified hface =>
        have hfirst : face ∈ firstLeft.toAssembly.firstRail.support ∨
            face ∈ firstLeft.toAssembly.secondRail.support := by
          cases witness.origin with
          | firstSecond hold hnew => exact .inl (by simpa [hface] using hold)
          | secondFirst hold hnew => exact .inr (by simpa [hface] using hold)
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).firstRail.support := by
          rw [hfaceEq]
          simpa only [rebaseLastContinuation,
            rebaseAssemblyStart_firstRail_support, continuationAssembly] using
            lastSuccessor.firstContinuation.start_mem_support
        exact firstPiece_disjoint_lastPiece hsource hfirst (.inl hlast)
    | swappedLeft middle hresult witness hclassified hface =>
        have hfirst : face ∈ firstLeft.toAssembly.firstRail.support ∨
            face ∈ firstLeft.toAssembly.secondRail.support := by
          cases witness.origin with
          | firstSecond hold hnew => exact .inl (by simpa [hface] using hold)
          | secondFirst hold hnew => exact .inr (by simpa [hface] using hold)
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).firstRail.support := by
          rw [hfaceEq]
          simpa only [rebaseLastContinuation,
            rebaseAssemblyStart_firstRail_support, continuationAssembly] using
            lastSuccessor.firstContinuation.start_mem_support
        exact firstPiece_disjoint_lastPiece hsource hfirst (.inl hlast)
    | straightRight middle hresult prefixMiddle hleft witness hright hface =>
        apply witness.face_ne_newFirstStart
        exact (hface.trans hfaceEq).trans (congrArg
          (selectedPlacementSideFace thirdPlacement)
          (bridge.rightOutgoingBefore_eq_nextLeftBefore lastSuccessor)).symm
    | swappedRight middle hresult prefixMiddle hleft witness hright hface =>
        apply witness.face_ne_newFirstStart
        exact (hface.trans hfaceEq).trans (congrArg
          (selectedPlacementSideFace thirdPlacement)
          (bridge.rightOutgoingBefore_eq_nextLeftBefore lastSuccessor)).symm
  · intro hfaceEq
    cases data with
    | straightLeft middle hresult witness hclassified hface =>
        have hfirst : face ∈ firstLeft.toAssembly.firstRail.support ∨
            face ∈ firstLeft.toAssembly.secondRail.support := by
          cases witness.origin with
          | firstSecond hold hnew => exact .inl (by simpa [hface] using hold)
          | secondFirst hold hnew => exact .inr (by simpa [hface] using hold)
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).secondRail.support := by
          rw [hfaceEq]
          simpa only [rebaseLastContinuation,
            rebaseAssemblyStart_secondRail_support, continuationAssembly] using
            lastSuccessor.secondContinuation.start_mem_support
        exact firstPiece_disjoint_lastPiece hsource hfirst (.inr hlast)
    | swappedLeft middle hresult witness hclassified hface =>
        have hfirst : face ∈ firstLeft.toAssembly.firstRail.support ∨
            face ∈ firstLeft.toAssembly.secondRail.support := by
          cases witness.origin with
          | firstSecond hold hnew => exact .inl (by simpa [hface] using hold)
          | secondFirst hold hnew => exact .inr (by simpa [hface] using hold)
        have hlast : face ∈
            (rebaseLastContinuation (bridge := bridge)
              (lastSuccessor := lastSuccessor)).secondRail.support := by
          rw [hfaceEq]
          simpa only [rebaseLastContinuation,
            rebaseAssemblyStart_secondRail_support, continuationAssembly] using
            lastSuccessor.secondContinuation.start_mem_support
        exact firstPiece_disjoint_lastPiece hsource hfirst (.inr hlast)
    | straightRight middle hresult prefixMiddle hleft witness hright hface =>
        apply witness.face_ne_newSecondStart
        exact (hface.trans hfaceEq).trans (congrArg
          (selectedPlacementSideFace thirdPlacement)
          (bridge.rightOutgoingAfter_eq_nextLeftAfter lastSuccessor)).symm
    | swappedRight middle hresult prefixMiddle hleft witness hright hface =>
        apply witness.face_ne_newSecondStart
        exact (hface.trans hfaceEq).trans (congrArg
          (selectedPlacementSideFace thirdPlacement)
          (bridge.rightOutgoingAfter_eq_nextLeftAfter lastSuccessor)).symm

/-- The seven literal source atoms from which the canonical middle repair may
draw a face: two old tracks, two successor tracks, the Cell-3 centre, and the
two seam flanks. -/
def FaceInCanonicalMiddleSourcePieces
    (face : SelectedFace (web := web)) : Prop :=
  face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
      (bridge := bridge)).paths.firstRail.support ∨
    face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
      (bridge := bridge)).paths.secondRail.support ∨
    face ∈ bridge.firstContinuation.support ∨
    face ∈ bridge.secondContinuation.support ∨
    face = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center ∨
    face = selectedPlacementSideFace secondPlacement bridge.frame.leftBefore ∨
    face = selectedPlacementSideFace secondPlacement bridge.frame.leftAfter

private theorem faceInCanonicalMiddleSourcePieces_of_expected
    {oldSupport newSupport : List (SelectedFace (web := web))}
    {face : SelectedFace (web := web)}
    (hold : face ∈ oldSupport → FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face)
    (hnew : face ∈ newSupport → FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face)
    (hface : FaceInExpectedSelectedRailTrack (corridor := corridor)
      (leftInterior := nextCorridorInterior firstInterior hfirstNext)
      (leftPlacement := secondPlacement) (successor := bridge)
      oldSupport newSupport face) :
    FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face := by
  simp only [FaceInExpectedSelectedRailTrack] at hface
  rcases hface with holdFace | newFace | hcenter | hbefore | hafter
  · exact hold holdFace
  · exact hnew newFace
  · exact .inr (.inr (.inr (.inr (.inl hcenter))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl hbefore)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr hafter)))))

/-- Track provenance unfolds every face of the canonical middle repair into
one of its seven literal source atoms. -/
theorem faceInCanonicalMiddleSourcePieces_of_middleRepair
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    {face : SelectedFace (web := web)}
    (hface : FaceInCanonicalMiddleRepair
      (firstSuccessor := firstSuccessor) (bridge := bridge) trace face) :
    FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face := by
  have htrack := trace.hasTrackProvenance
  cases hresult : trace.toOutcome with
  | straight middle =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance,
        hresult, SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance]
        at htrack
      simp only [FaceInCanonicalMiddleRepair, hresult] at hface
      rcases hface with hfirst | hsecond
      · exact faceInCanonicalMiddleSourcePieces_of_expected
          (fun hold => .inl hold)
          (fun hnew => .inr (.inr (.inl hnew)))
          (htrack.1 face (by simpa [rebaseMiddleStraight] using hfirst))
      · exact faceInCanonicalMiddleSourcePieces_of_expected
          (fun hold => .inr (.inl hold))
          (fun hnew => .inr (.inr (.inr (.inl hnew))))
          (htrack.2 face (by simpa [rebaseMiddleStraight] using hsecond))
  | swapped middle =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance,
        hresult, SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance]
        at htrack
      simp only [FaceInCanonicalMiddleRepair, hresult] at hface
      rcases hface with hfirst | hsecond
      · exact faceInCanonicalMiddleSourcePieces_of_expected
          (fun hold => .inl hold)
          (fun hnew => .inr (.inr (.inr (.inl hnew))))
          (htrack.1 face (by simpa [rebaseMiddleSwapped] using hfirst))
      · exact faceInCanonicalMiddleSourcePieces_of_expected
          (fun hold => .inr (.inl hold))
          (fun hnew => .inr (.inr (.inl hnew)))
          (htrack.2 face (by simpa [rebaseMiddleSwapped] using hsecond))

/-- A coordinate on a walk of length at most two.  The alternatives are
deliberately allowed to coincide when the walk has length zero or one; the
point is finite exhaustion, not a false distinctness assertion. -/
inductive FaceInShortRailCoordinates {F : Type*} {H : SimpleGraph F}
    {start finish : F} (walk : H.Walk start finish) (face : F) : Prop
  | start (face_eq : face = start)
  | middle (face_eq : face = walk.getVert 1)
  | finish (face_eq : face = finish)

private theorem faceInShortRailCoordinates_of_mem_support
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hlength : walk.length ≤ 2)
    (hface : face ∈ walk.support) :
    FaceInShortRailCoordinates walk face := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hface with
    ⟨index, hindex, hindexLe⟩
  have hindexTwo : index ≤ 2 := hindexLe.trans hlength
  interval_cases index
  · exact .start (by simpa using hindex.symm)
  · exact .middle (by simpa using hindex.symm)
  · have hlengthTwo : walk.length = 2 := by omega
    exact .finish (by
      calc
        face = walk.getVert 2 := hindex.symm
        _ = walk.getVert walk.length := by rw [hlengthTwo]
        _ = finish := walk.getVert_length)

/-- Fully finite coordinates for the canonical middle repair's source
support.  The four short rail packets have been expanded to start, optional
middle, or finish; the three displayed connector faces remain literal
singletons. -/
inductive FaceInCanonicalMiddleCoordinates
    (face : SelectedFace (web := web)) : Prop
  | bridgeOldFirst
      (coordinate : FaceInShortRailCoordinates
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.firstRail face)
  | bridgeOldSecond
      (coordinate : FaceInShortRailCoordinates
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.secondRail face)
  | bridgeNewFirst
      (coordinate : FaceInShortRailCoordinates bridge.firstContinuation face)
  | bridgeNewSecond
      (coordinate : FaceInShortRailCoordinates bridge.secondContinuation face)
  | center
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
  | beforeSeam
      (face_eq : face = selectedPlacementSideFace secondPlacement
        bridge.frame.leftBefore)
  | afterSeam
      (face_eq : face = selectedPlacementSideFace secondPlacement
        bridge.frame.leftAfter)

/-- Every source-piece membership of the canonical middle repair is one of
fifteen explicit walk coordinates: three on each of four length-at-most-two
rails, plus the centre and two seam faces. -/
theorem faceInCanonicalMiddleCoordinates_of_sourcePieces
    {face : SelectedFace (web := web)}
    (hface : FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face) :
    FaceInCanonicalMiddleCoordinates
      (firstSuccessor := firstSuccessor) (bridge := bridge) face := by
  rcases hface with hface | hface | hface | hface | hface | hface | hface
  · exact .bridgeOldFirst
      (faceInShortRailCoordinates_of_mem_support _
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.firstRail_length_le_two hface)
  · exact .bridgeOldSecond
      (faceInShortRailCoordinates_of_mem_support _
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.secondRail_length_le_two hface)
  · exact .bridgeNewFirst
      (faceInShortRailCoordinates_of_mem_support _ (by
        simpa [SeparatedSelectedSourceLocalRailSuccessor.firstContinuation] using
          bridge.rightRails.paths.firstRail_length_le_two) hface)
  · exact .bridgeNewSecond
      (faceInShortRailCoordinates_of_mem_support _ (by
        simpa [SeparatedSelectedSourceLocalRailSuccessor.secondContinuation] using
          bridge.rightRails.paths.secondRail_length_le_two) hface)
  · exact .center hface
  · exact .beforeSeam hface
  · exact .afterSeam hface

/-- Track provenance plus the length-two bound turns every repaired-middle
face into a finite literal coordinate. -/
theorem faceInCanonicalMiddleCoordinates_of_middleRepair
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    {face : SelectedFace (web := web)}
    (hface : FaceInCanonicalMiddleRepair
      (firstSuccessor := firstSuccessor) (bridge := bridge) trace face) :
    FaceInCanonicalMiddleCoordinates
      (firstSuccessor := firstSuccessor) (bridge := bridge) face :=
  faceInCanonicalMiddleCoordinates_of_sourcePieces
    (faceInCanonicalMiddleSourcePieces_of_middleRepair trace hface)

/-- Source-level form of the two residual adjacent bands.  The repaired
middle is no longer opaque: its contact face is one of seven displayed atoms
of the literal second/third-cell bridge window. -/
inductive ExactSelectedLocalRailMiddleReplacementSourceLocalBand
    (face : SelectedFace (web := web)) : Prop
  | firstMiddle
      (first : face ∈ firstLeft.toAssembly.firstRail.support ∨
        face ∈ firstLeft.toAssembly.secondRail.support)
      (middle : FaceInCanonicalMiddleSourcePieces
        (firstSuccessor := firstSuccessor) (bridge := bridge) face)
  | middleLast
      (middle : FaceInCanonicalMiddleSourcePieces
        (firstSuccessor := firstSuccessor) (bridge := bridge) face)
      (last : face ∈ (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)).firstRail.support ∨
        face ∈ (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)).secondRail.support)

/-- The bounded localization can be read entirely in literal source pieces,
ready for the finite neighboring-window classification required by the
source. -/
theorem ExactSelectedLocalRailMiddleReplacementLocalBand.toSourceLocalBand
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (band : ExactSelectedLocalRailMiddleReplacementLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    ExactSelectedLocalRailMiddleReplacementSourceLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face := by
  cases band with
  | firstMiddle first middle =>
      exact .firstMiddle first
        (faceInCanonicalMiddleSourcePieces_of_middleRepair trace middle)
  | middleLast middle last =>
      exact .middleLast
        (faceInCanonicalMiddleSourcePieces_of_middleRepair trace middle) last

/-- Coordinate-level form of the residual local table.  The outer packet is
still retained as the side of the collision, while the repaired-middle side
is now one of finitely many explicit positions on four walks of length at
most two, or one of three displayed faces. -/
inductive ExactSelectedLocalRailMiddleReplacementCoordinateLocalBand
    (face : SelectedFace (web := web)) : Prop
  | firstMiddle
      (first : face ∈ firstLeft.toAssembly.firstRail.support ∨
        face ∈ firstLeft.toAssembly.secondRail.support)
      (middle : FaceInCanonicalMiddleCoordinates
        (firstSuccessor := firstSuccessor) (bridge := bridge) face)
  | middleLast
      (middle : FaceInCanonicalMiddleCoordinates
        (firstSuccessor := firstSuccessor) (bridge := bridge) face)
      (last : face ∈ (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)).firstRail.support ∨
        face ∈ (rebaseLastContinuation (bridge := bridge)
          (lastSuccessor := lastSuccessor)).secondRail.support)

/-- Replace the repaired-middle support packet in either adjacent band by
its finite coordinate classification. -/
theorem ExactSelectedLocalRailMiddleReplacementSourceLocalBand.toCoordinateLocalBand
    {face : SelectedFace (web := web)}
    (band : ExactSelectedLocalRailMiddleReplacementSourceLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face) :
    ExactSelectedLocalRailMiddleReplacementCoordinateLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face := by
  cases band with
  | firstMiddle first middle =>
      exact .firstMiddle first
        (faceInCanonicalMiddleCoordinates_of_sourcePieces middle)
  | middleLast middle last =>
      exact .middleLast
        (faceInCanonicalMiddleCoordinates_of_sourcePieces middle) last

/-- Both sides of a residual join expressed in finite coordinates.  Each
outer rail is again a literal Cell-3 rail of length at most two, so no opaque
support-membership packet remains in this local table. -/
inductive ExactSelectedLocalRailMiddleReplacementFullyCoordinateLocalBand
    (face : SelectedFace (web := web)) : Prop
  | firstMiddle
      (first : FaceInShortRailCoordinates firstLeft.toAssembly.firstRail face ∨
        FaceInShortRailCoordinates firstLeft.toAssembly.secondRail face)
      (middle : FaceInCanonicalMiddleCoordinates
        (firstSuccessor := firstSuccessor) (bridge := bridge) face)
  | middleLast
      (middle : FaceInCanonicalMiddleCoordinates
        (firstSuccessor := firstSuccessor) (bridge := bridge) face)
      (last : FaceInShortRailCoordinates
          (rebaseLastContinuation (bridge := bridge)
            (lastSuccessor := lastSuccessor)).firstRail face ∨
        FaceInShortRailCoordinates
          (rebaseLastContinuation (bridge := bridge)
            (lastSuccessor := lastSuccessor)).secondRail face)

/-- Expand the remaining first/fourth support packet by the same length-two
coordinate argument used for the repaired middle. -/
theorem ExactSelectedLocalRailMiddleReplacementCoordinateLocalBand.toFullyCoordinateLocalBand
    {face : SelectedFace (web := web)}
    (band : ExactSelectedLocalRailMiddleReplacementCoordinateLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face) :
    ExactSelectedLocalRailMiddleReplacementFullyCoordinateLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face := by
  cases band with
  | firstMiddle first middle =>
      refine .firstMiddle ?_ middle
      rcases first with first | second
      · exact .inl (faceInShortRailCoordinates_of_mem_support _ (by
          simpa using firstLeft.paths.firstRail_length_le_two) first)
      · exact .inr (faceInShortRailCoordinates_of_mem_support _ (by
          simpa using firstLeft.paths.secondRail_length_le_two) second)
  | middleLast middle last =>
      refine .middleLast middle ?_
      rcases last with first | second
      · exact .inl (faceInShortRailCoordinates_of_mem_support _ (by
          simpa [rebaseLastContinuation, continuationAssembly,
            rebaseAssemblyStart,
            SeparatedSelectedSourceLocalRailSuccessor.firstContinuation] using
              lastSuccessor.rightRails.paths.firstRail_length_le_two) first)
      · exact .inr (faceInShortRailCoordinates_of_mem_support _ (by
          simpa [rebaseLastContinuation, continuationAssembly,
            rebaseAssemblyStart,
            SeparatedSelectedSourceLocalRailSuccessor.secondContinuation] using
              lastSuccessor.rightRails.paths.secondRail_length_le_two) second)

/-- The second-cell centre cannot occur on either literal fourth-cell
continuation.  The former is the corridor centre two positions behind the
latter, so such membership would contradict skeleton nonadjacency. -/
theorem face_ne_middleCenter_of_mem_lastPiece
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {face : SelectedFace (web := web)}
    (hlast : face ∈ (rebaseLastContinuation (bridge := bridge)
        (lastSuccessor := lastSuccessor)).firstRail.support ∨
      face ∈ (rebaseLastContinuation (bridge := bridge)
        (lastSuccessor := lastSuccessor)).secondRail.support) :
    face ≠ corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hnotadj : ¬ (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
      (skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center)
      (skeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) :=
    skeleton.separated_not_adjacent
      (nextCorridorInterior firstInterior hfirstNext).center
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center (by
          change firstInterior.center.val + 1 + 1 < firstInterior.center.val + 3
          omega)
  intro hface
  rcases hlast with hlast | hlast
  · have hadj := lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
      face (by
        simpa [rebaseLastContinuation, continuationAssembly] using hlast)
    exact hnotadj (by simpa [skeleton, hface] using hadj.symm)
  · have hadj := lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
      face (by
        simpa [rebaseLastContinuation, continuationAssembly] using hlast)
    exact hnotadj (by simpa [skeleton, hface] using hadj.symm)

/-- A residual collision at the displayed second-cell centre is necessarily
in the left adjacent band; the right band has just been ruled out. -/
theorem ExactSelectedLocalRailMiddleReplacementSourceLocalBand.firstMiddle_of_eq_middleCenter
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {face : SelectedFace (web := web)}
    (band : ExactSelectedLocalRailMiddleReplacementSourceLocalBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face)
    (hface : face =
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    (face ∈ firstLeft.toAssembly.firstRail.support ∨
        face ∈ firstLeft.toAssembly.secondRail.support) ∧
      FaceInCanonicalMiddleSourcePieces
        (firstSuccessor := firstSuccessor) (bridge := bridge) face := by
  cases band with
  | firstMiddle first middle => exact ⟨first, middle⟩
  | middleLast middle last =>
      exact False.elim ((face_ne_middleCenter_of_mem_lastPiece hsource last) hface)

/-- The three possible centre relations of a face in the canonical middle
repair.  Old bridge rails and seam faces lie next to the second centre; new
bridge continuations lie next to the third centre; the displayed centre is
retained as an equality case. -/
inductive FaceNearCanonicalMiddleCenters
    (face : SelectedFace (web := web)) : Prop
  | secondCenter
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
  | secondAdjacent
      (adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center) face)
  | thirdAdjacent
      (adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
          face)

/-- Collapse the finite middle-source coordinates to the centre relation
which matters for the next planar collision argument. -/
theorem faceNearCanonicalMiddleCenters_of_sourcePieces
    {face : SelectedFace (web := web)}
    (hface : FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face) :
    FaceNearCanonicalMiddleCenters (corridor := corridor)
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) face := by
  rcases hface with hface | hface | hface | hface | hface | hface | hface
  · exact .secondAdjacent
      ((BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
        |>.firstRail_support_adjacent_center face hface)
  · exact .secondAdjacent
      ((BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
        |>.secondRail_support_adjacent_center face hface)
  · have hface' : face ∈ bridge.rightRails.paths.firstRail.support := by
      rw [← bridge.firstContinuation_support]
      exact hface
    exact .thirdAdjacent
      (bridge.rightRails.paths.firstRail_support_adjacent_center face hface')
  · have hface' : face ∈ bridge.rightRails.paths.secondRail.support := by
      rw [← bridge.secondContinuation_support]
      exact hface
    exact .thirdAdjacent
      (bridge.rightRails.paths.secondRail_support_adjacent_center face hface')
  · exact .secondCenter hface
  · subst face
    exact .secondAdjacent
      (selectedPlacementSideFace_adjacent_center
        (corridor := corridor) secondPlacement bridge.frame.leftBefore)
  · subst face
    exact .secondAdjacent
      (selectedPlacementSideFace_adjacent_center
        (corridor := corridor) secondPlacement bridge.frame.leftAfter)

/-- The five literal centre geometries of a surviving canonical middle
replacement collision.  Adjacent-centre cases are dual triangles; the two
distance-two cases are the bounded alternative routes which the finite local
classification must still consume. -/
inductive ExactSelectedLocalRailMiddleReplacementCollisionGeometry
    (face : SelectedFace (web := web)) : Prop
  | secondCenter
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
  | firstSecondCommon
      (first_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center) face)
      (second_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center) face)
  | firstThirdCommon
      (first_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center) face)
      (third_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
          face)
  | secondFourthCommon
      (second_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center) face)
      (fourth_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
              hlastNext).center) face)
  | thirdFourthCommon
      (third_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
          face)
      (fourth_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
              hlastNext).center) face)

/-- **Bounded middle-replacement geometry.** Every surviving bad branch has
one of five exact centre relations.  This is a classification theorem, not a
claim that any of the five cases is empty. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.hasGeometry
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    ExactSelectedLocalRailMiddleReplacementCollisionGeometry
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) face := by
  have band := (data.hasLocalBand hsource).toSourceLocalBand
  cases band with
  | firstMiddle first middle =>
      have hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center) face := by
        rcases first with first | second
        · exact firstLeft.paths.firstRail_support_adjacent_center face first
        · exact firstLeft.paths.secondRail_support_adjacent_center face second
      cases faceNearCanonicalMiddleCenters_of_sourcePieces middle with
      | secondCenter face_eq => exact .secondCenter face_eq
      | secondAdjacent adjacent => exact .firstSecondCommon hfirst adjacent
      | thirdAdjacent adjacent => exact .firstThirdCommon hfirst adjacent
  | middleLast middle last =>
      have hfourth : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
              hlastNext).center) face := by
        rcases last with first | second
        · exact lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
            face (by
              simpa [rebaseLastContinuation, continuationAssembly] using first)
        · exact lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
            face (by
              simpa [rebaseLastContinuation, continuationAssembly] using second)
      cases faceNearCanonicalMiddleCenters_of_sourcePieces middle with
      | secondCenter face_eq =>
          exact False.elim ((face_ne_middleCenter_of_mem_lastPiece hsource last)
            face_eq)
      | secondAdjacent adjacent => exact .secondFourthCommon adjacent hfourth
      | thirdAdjacent adjacent => exact .thirdFourthCommon adjacent hfourth

/-- The six source-ladder shapes obtained after splitting a distance-two
common neighbour according to whether it is the intervening corridor centre.
The adjacent common-neighbour cases are triangles.  A genuinely new common
neighbour across two corridor steps is a square together with the two literal
corridor edges.  This is still positive geometry, not a reduction of any
case. -/
inductive ExactSelectedLocalRailMiddleReplacementLadderGeometry
    (face : SelectedFace (web := web)) : Prop
  | secondCenter
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
  | thirdCenter
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
  | firstSecondTriangle
      (first_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center) face)
      (second_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center) face)
  | firstThirdSquare
      (first_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center) face)
      (third_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
          face)
      (face_ne_second : face ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
  | secondFourthSquare
      (second_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center) face)
      (fourth_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
              hlastNext).center) face)
      (face_ne_third : face ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
  | thirdFourthTriangle
      (third_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
          face)
      (fourth_adjacent : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
              hlastNext).center) face)

/-- Normalize the five overlapping centre relations into the source's
triangle/centre/square ladder shapes.  The split is exhaustive and assumes no
case away. -/
theorem ExactSelectedLocalRailMiddleReplacementCollisionGeometry.toLadderGeometry
    {face : SelectedFace (web := web)}
    (geometry : ExactSelectedLocalRailMiddleReplacementCollisionGeometry
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) face) :
    ExactSelectedLocalRailMiddleReplacementLadderGeometry
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) face := by
  cases geometry with
  | secondCenter face_eq => exact .secondCenter face_eq
  | firstSecondCommon first_adjacent second_adjacent =>
      exact .firstSecondTriangle first_adjacent second_adjacent
  | firstThirdCommon first_adjacent third_adjacent =>
      by_cases hface : face =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center
      · exact .secondCenter hface
      · exact .firstThirdSquare first_adjacent third_adjacent hface
  | secondFourthCommon second_adjacent fourth_adjacent =>
      by_cases hface : face =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      · exact .thirdCenter hface
      · exact .secondFourthSquare second_adjacent fourth_adjacent hface
  | thirdFourthCommon third_adjacent fourth_adjacent =>
      exact .thirdFourthTriangle third_adjacent fourth_adjacent

/-- Every surviving replacement collision is therefore a literal centre,
triangle, or square case from the source reduction ladder.  This theorem only
classifies the branch; it does not yet apply the rotor or square reduction. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.hasLadderGeometry
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    ExactSelectedLocalRailMiddleReplacementLadderGeometry
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) face :=
  (data.hasGeometry hsource).toLadderGeometry

/-- The replacement classifier retains the independently proved concrete rail
which avoids the original middle-band collision face. -/
structure ExactSelectedLocalRailMiddleReplacement
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      bridge (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) where
  clearMiddleRail : CollisionAvoidingMiddleRail trace collision
  outcome : ExactSelectedLocalRailMiddleReplacementOutcome
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace

/-- Construct the proof-relevant middle replacement from the actual canonical
trace and an independently selected middle collision. -/
noncomputable def ExactSelectedLocalRailMiddleReplacement.ofClassifier
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (collision : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      bridge (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    ExactSelectedLocalRailMiddleReplacement
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace collision where
  clearMiddleRail := trace.collisionAvoidingMiddleRail collision
  outcome := classifyExactSelectedLocalRailMiddleReplacement
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
