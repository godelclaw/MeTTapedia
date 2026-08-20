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
