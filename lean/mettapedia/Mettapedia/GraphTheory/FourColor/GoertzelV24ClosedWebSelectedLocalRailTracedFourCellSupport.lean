import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairRetainedSupport

/-!
# L1: support provenance for the canonical traced four-cell transition

The retained four-cell classifier returns simple rails after loop erasure.
This module proves that every face on a successful returned rail was already
present in one of its two exact terminal windows.  Collision branches retain
their existing exact witness and require no substitute support claim.

This closes a proof-relevance gap in the rolling interface: a successful
four-cell result is now tied to the literal source windows which constructed
it.  It does not eliminate the collision branches, perform the rolling
induction, attach either end cap, or close Fable flag L1.
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

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- A support uses only faces in the two exact terminal windows of a
four-cell transition. -/
def SupportContainedInExactTerminalWindowPair
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (support : List (SelectedFace (web := web))) : Prop :=
  ∀ face ∈ support,
    face ∈ firstWindow.toCertified.firstSupport ∨
    face ∈ firstWindow.toCertified.secondSupport ∨
    face ∈ lastWindow.toCertified.firstSupport ∨
    face ∈ lastWindow.toCertified.secondSupport

/-- Provenance predicate on the strongest four-cell outcome. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasWindowSupportProvenance
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      SupportContainedInExactTerminalWindowPair firstWindow lastWindow
          assembly.firstRail.support ∧
        SupportContainedInExactTerminalWindowPair firstWindow lastWindow
          assembly.secondRail.support
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

/-- A face occurs on one of the two rails of a successful four-cell outcome.
Collision outcomes have no successful rail and therefore make this predicate
false rather than silently forgetting their witness. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.SuccessfulRailContains
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow)
    (face : SelectedFace (web := web)) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      face ∈ assembly.firstRail.support ∨ face ∈ assembly.secondRail.support
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => False

/-- The two literal terminal windows give the complete center provenance of a
successful four-cell rail face. -/
def FaceNearExactTerminalCenterPairs
    (face : SelectedFace (web := web)) : Prop :=
  FaceNearSelectedCenterPair (corridor := corridor)
      firstInterior.center (nextCorridorInterior firstInterior hfirstNext).center face ∨
    FaceNearSelectedCenterPair (corridor := corridor)
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center face

/-- Exact support provenance locates every successful returned face in the
closed neighbourhood of one of the two terminal center pairs. -/
theorem ExactSelectedLocalRailFourCellRetainedOutcome.faceNearTerminalCenterPairs_of_contains
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow)
    (hprovenance : outcome.HasWindowSupportProvenance)
    {face : SelectedFace (web := web)}
    (hcontains : outcome.SuccessfulRailContains face) :
    FaceNearExactTerminalCenterPairs
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) face := by
  cases outcome with
  | straight assembly | swapped assembly =>
      rcases hcontains with hfirst | hsecond
      · have hwindow := hprovenance.1 face hfirst
        rcases hwindow with hfirstFirst | hfirstSecond | hlastFirst | hlastSecond
        · exact .inl (firstWindow.toCertified.firstSupport_near face hfirstFirst)
        · exact .inl (firstWindow.toCertified.secondSupport_near face hfirstSecond)
        · exact .inr (lastWindow.toCertified.firstSupport_near face hlastFirst)
        · exact .inr (lastWindow.toCertified.secondSupport_near face hlastSecond)
      · have hwindow := hprovenance.2 face hsecond
        rcases hwindow with hfirstFirst | hfirstSecond | hlastFirst | hlastSecond
        · exact .inl (firstWindow.toCertified.firstSupport_near face hfirstFirst)
        · exact .inl (firstWindow.toCertified.secondSupport_near face hfirstSecond)
        · exact .inr (lastWindow.toCertified.firstSupport_near face hlastFirst)
        · exact .inr (lastWindow.toCertified.secondSupport_near face hlastSecond)
  | straightStraightCollision | straightSwappedCollision |
      swappedStraightCollision | swappedSwappedCollision =>
      exact hcontains.elim

private theorem supportContainedInWindows_of_assemblies
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    {firstFirstStart firstSecondStart firstFirstFinish firstSecondFinish :
      SelectedFace (web := web)}
    {firstAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstFirstStart firstSecondStart firstFirstFinish firstSecondFinish}
    {lastFirstStart lastSecondStart lastFirstFinish lastSecondFinish :
      SelectedFace (web := web)}
    {lastAssembly : SelectedSourceLocalRailAssembly (web := web)
      lastFirstStart lastSecondStart lastFirstFinish lastSecondFinish}
    {support : List (SelectedFace (web := web))}
    (hfirstFirst : firstAssembly.firstRail.support =
      firstWindow.toCertified.firstSupport)
    (hfirstSecond : firstAssembly.secondRail.support =
      firstWindow.toCertified.secondSupport)
    (hlastFirst : lastAssembly.firstRail.support =
      lastWindow.toCertified.firstSupport)
    (hlastSecond : lastAssembly.secondRail.support =
      lastWindow.toCertified.secondSupport)
    (hcontained : SupportContainedInAssemblyPair firstAssembly lastAssembly support) :
    SupportContainedInExactTerminalWindowPair firstWindow lastWindow support := by
  intro face hface
  rcases hcontained face hface with holdFirst | holdSecond | hlastFirstMem | hlastSecondMem
  · exact .inl (by simpa [hfirstFirst] using holdFirst)
  · exact .inr (.inl (by simpa [hfirstSecond] using holdSecond))
  · exact .inr (.inr (.inl (by simpa [hlastFirst] using hlastFirstMem)))
  · exact .inr (.inr (.inr (by simpa [hlastSecond] using hlastSecondMem)))

/-- The strongest canonical four-cell classifier preserves the literal
support envelope of its two exact terminal windows. -/
theorem classifyExactSelectedLocalRailFourCellRetained_hasWindowSupportProvenance
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) :
    (classifyExactSelectedLocalRailFourCellRetained firstWindow lastWindow
      |>.HasWindowSupportProvenance) := by
  classical
  rcases firstWindow with ⟨firstOutcome, firstExact⟩
  rcases lastWindow with ⟨lastOutcome, lastExact⟩
  cases firstOutcome with
  | straight firstAssembly =>
      let firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
          firstSuccessor firstLeft := ⟨.straight firstAssembly, firstExact⟩
      cases lastOutcome with
      | straight lastAssembly =>
          let lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
              (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)) :=
            ⟨.straight lastAssembly, lastExact⟩
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          simp only [classifyExactSelectedLocalRailFourCellRetained,
            ExactSelectedLocalRailFourCellRetainedOutcome.HasWindowSupportProvenance]
          have hgeneric := classifyRetainedBypassAppend_hasSupportProvenance
            firstAssembly rebased
          cases hretained : classifyRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              change AssemblySupportContainedInAssemblyPair
                firstAssembly rebased assembly at hgeneric
              have hfirstFirst : firstAssembly.firstRail.support =
                  firstWindow.toCertified.firstSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              have hfirstSecond : firstAssembly.secondRail.support =
                  firstWindow.toCertified.secondSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              have hlastFirst : rebased.firstRail.support =
                  lastWindow.toCertified.firstSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              have hlastSecond : rebased.secondRail.support =
                  lastWindow.toCertified.secondSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              have hprovenance :
                  SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.firstRail.support ∧
                    SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.secondRail.support := ⟨
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.1,
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.2⟩
              simpa using hprovenance
          | collision collision =>
              simp

      | swapped lastAssembly =>
          let lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
              (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)) :=
            ⟨.swapped lastAssembly, lastExact⟩
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          simp only [classifyExactSelectedLocalRailFourCellRetained,
            ExactSelectedLocalRailFourCellRetainedOutcome.HasWindowSupportProvenance]
          have hgeneric := classifyRetainedBypassAppend_hasSupportProvenance
            firstAssembly rebased
          cases hretained : classifyRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              change AssemblySupportContainedInAssemblyPair
                firstAssembly rebased assembly at hgeneric
              have hfirstFirst : firstAssembly.firstRail.support =
                  firstWindow.toCertified.firstSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              have hfirstSecond : firstAssembly.secondRail.support =
                  firstWindow.toCertified.secondSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              have hlastFirst : rebased.firstRail.support =
                  lastWindow.toCertified.firstSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              have hlastSecond : rebased.secondRail.support =
                  lastWindow.toCertified.secondSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              have hprovenance :
                  SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.firstRail.support ∧
                    SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.secondRail.support := ⟨
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.1,
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.2⟩
              simpa using hprovenance
          | collision collision =>
              simp

  | swapped firstAssembly =>
      let firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
          firstSuccessor firstLeft := ⟨.swapped firstAssembly, firstExact⟩
      cases lastOutcome with
      | straight lastAssembly =>
          let lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
              (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)) :=
            ⟨.straight lastAssembly, lastExact⟩
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          simp only [classifyExactSelectedLocalRailFourCellRetained,
            ExactSelectedLocalRailFourCellRetainedOutcome.HasWindowSupportProvenance]
          have hgeneric := classifyCrossedRetainedBypassAppend_hasSupportProvenance
            firstAssembly rebased
          cases hretained : classifyCrossedRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              change AssemblySupportContainedInAssemblyPair
                firstAssembly rebased assembly at hgeneric
              have hfirstFirst : firstAssembly.firstRail.support =
                  firstWindow.toCertified.firstSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              have hfirstSecond : firstAssembly.secondRail.support =
                  firstWindow.toCertified.secondSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              have hlastFirst : rebased.firstRail.support =
                  lastWindow.toCertified.firstSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              have hlastSecond : rebased.secondRail.support =
                  lastWindow.toCertified.secondSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              have hprovenance :
                  SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.firstRail.support ∧
                    SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.secondRail.support := ⟨
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.1,
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.2⟩
              simpa using hprovenance
          | collision collision =>
              simp
      | swapped lastAssembly =>
          let lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
              (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)) :=
            ⟨.swapped lastAssembly, lastExact⟩
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          simp only [classifyExactSelectedLocalRailFourCellRetained,
            ExactSelectedLocalRailFourCellRetainedOutcome.HasWindowSupportProvenance]
          have hgeneric := classifyCrossedRetainedBypassAppend_hasSupportProvenance
            firstAssembly rebased
          cases hretained : classifyCrossedRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              change AssemblySupportContainedInAssemblyPair
                firstAssembly rebased assembly at hgeneric
              have hfirstFirst : firstAssembly.firstRail.support =
                  firstWindow.toCertified.firstSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              have hfirstSecond : firstAssembly.secondRail.support =
                  firstWindow.toCertified.secondSupport := by
                simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              have hlastFirst : rebased.firstRail.support =
                  lastWindow.toCertified.firstSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              have hlastSecond : rebased.secondRail.support =
                  lastWindow.toCertified.secondSupport := by
                simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              have hprovenance :
                  SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.firstRail.support ∧
                    SupportContainedInExactTerminalWindowPair firstWindow lastWindow
                      assembly.secondRail.support := ⟨
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.1,
                supportContainedInWindows_of_assemblies firstWindow lastWindow
                  hfirstFirst hfirstSecond hlastFirst hlastSecond hgeneric.2⟩
              simpa using hprovenance
          | collision collision =>
              simp

/-- A traced four-cell transition whose successful outcome is certified to
use only the two literal terminal-window supports.  This wrapper deliberately
strengthens the older packet instead of pretending that every arbitrary
inhabitant of that packet was produced by the canonical classifier. -/
structure SupportCertifiedExactSelectedLocalRailTracedFourCellTransition where
  transition : ExactSelectedLocalRailTracedFourCellTransition
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
  hasWindowSupportProvenance : transition.outcome.HasWindowSupportProvenance

/-- Construct the support-certified traced transition from the actual three
adjacent classifiers. -/
noncomputable def
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor) :
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) := by
  let transition := ExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) hsource
  refine ⟨transition, ?_⟩
  exact classifyExactSelectedLocalRailFourCellRetained_hasWindowSupportProvenance
    transition.firstTrace.toExactTerminalWindow
    transition.lastTrace.toExactTerminalWindow

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
