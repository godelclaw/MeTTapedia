import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellSupport

/-!
# L1: track-sensitive support provenance for the traced four-cell transition

The earlier terminal-window receipt remembers only that a successful returned
rail lies in the union of four supports.  This module retains the stronger
pairing supplied by the actual retained-bypass classifier: the first and
second outputs each use one named track from the first window and its ordered
or crossed continuation from the last window.

This is proof-relevant support provenance for the constructed four-cell
transition.  It does not identify a retained collision with a rail endpoint,
repair a collision, prove companion separation after a repair, iterate the
transition, attach end caps, construct separated crosscuts, or close Fable
flag L1.
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

/-- Ordered terminal-window provenance: output one stays on the two first
tracks and output two stays on the two second tracks. -/
def SupportsContainedInOrderedExactTerminalTracks
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (firstSupport secondSupport : List (SelectedFace (web := web))) : Prop :=
  SupportContainedInTrackPair firstWindow.toCertified.firstSupport
      lastWindow.toCertified.firstSupport firstSupport ∧
    SupportContainedInTrackPair firstWindow.toCertified.secondSupport
      lastWindow.toCertified.secondSupport secondSupport

/-- Crossed terminal-window provenance: the first output follows the first
track then the second continuation, and conversely for the second output. -/
def SupportsContainedInCrossedExactTerminalTracks
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (firstSupport secondSupport : List (SelectedFace (web := web))) : Prop :=
  SupportContainedInTrackPair firstWindow.toCertified.firstSupport
      lastWindow.toCertified.secondSupport firstSupport ∧
    SupportContainedInTrackPair firstWindow.toCertified.secondSupport
      lastWindow.toCertified.firstSupport secondSupport

/-- Successful four-cell outcomes retain either the ordered or the crossed
pairing of their two literal terminal-window tracks. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasSuccessfulTrackSupportProvenance
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      SupportsContainedInOrderedExactTerminalTracks firstWindow lastWindow
          assembly.firstRail.support assembly.secondRail.support ∨
        SupportsContainedInCrossedExactTerminalTracks firstWindow lastWindow
          assembly.firstRail.support assembly.secondRail.support
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

private theorem orderedTrackSupport_of_assemblies
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    {firstFirstStart firstSecondStart firstFirstFinish firstSecondFinish :
      SelectedFace (web := web)}
    {firstAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstFirstStart firstSecondStart firstFirstFinish firstSecondFinish}
    {lastFirstFinish lastSecondFinish : SelectedFace (web := web)}
    {lastAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstFirstFinish firstSecondFinish lastFirstFinish lastSecondFinish}
    {firstSupport secondSupport : List (SelectedFace (web := web))}
    (hfirstFirst : firstAssembly.firstRail.support =
      firstWindow.toCertified.firstSupport)
    (hfirstSecond : firstAssembly.secondRail.support =
      firstWindow.toCertified.secondSupport)
    (hlastFirst : lastAssembly.firstRail.support =
      lastWindow.toCertified.firstSupport)
    (hlastSecond : lastAssembly.secondRail.support =
      lastWindow.toCertified.secondSupport)
    (hcontained : AssemblySupportContainedInOrderedTrackPairs
      firstAssembly lastAssembly firstSupport secondSupport) :
    SupportsContainedInOrderedExactTerminalTracks firstWindow lastWindow
      firstSupport secondSupport := by
  constructor
  · intro face hface
    rcases hcontained.1 face hface with hold | hlast
    · exact .inl (by simpa [hfirstFirst] using hold)
    · exact .inr (by simpa [hlastFirst] using hlast)
  · intro face hface
    rcases hcontained.2 face hface with hold | hlast
    · exact .inl (by simpa [hfirstSecond] using hold)
    · exact .inr (by simpa [hlastSecond] using hlast)

private theorem crossedTrackSupport_of_assemblies
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    {firstFirstStart firstSecondStart firstFirstFinish firstSecondFinish :
      SelectedFace (web := web)}
    {firstAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstFirstStart firstSecondStart firstFirstFinish firstSecondFinish}
    {lastFirstFinish lastSecondFinish : SelectedFace (web := web)}
    {lastAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstSecondFinish firstFirstFinish lastFirstFinish lastSecondFinish}
    {firstSupport secondSupport : List (SelectedFace (web := web))}
    (hfirstFirst : firstAssembly.firstRail.support =
      firstWindow.toCertified.firstSupport)
    (hfirstSecond : firstAssembly.secondRail.support =
      firstWindow.toCertified.secondSupport)
    (hlastFirst : lastAssembly.firstRail.support =
      lastWindow.toCertified.firstSupport)
    (hlastSecond : lastAssembly.secondRail.support =
      lastWindow.toCertified.secondSupport)
    (hcontained : AssemblySupportContainedInCrossedTrackPairs
      firstAssembly lastAssembly firstSupport secondSupport) :
    SupportsContainedInCrossedExactTerminalTracks firstWindow lastWindow
      firstSupport secondSupport := by
  constructor
  · intro face hface
    rcases hcontained.1 face hface with hold | hlast
    · exact .inl (by simpa [hfirstFirst] using hold)
    · exact .inr (by simpa [hlastSecond] using hlast)
  · intro face hface
    rcases hcontained.2 face hface with hold | hlast
    · exact .inl (by simpa [hfirstSecond] using hold)
    · exact .inr (by simpa [hlastFirst] using hlast)

/-- The canonical retained four-cell classifier preserves the exact pairing
of the two terminal-window tracks. -/
theorem classifyExactSelectedLocalRailFourCellRetained_hasSuccessfulTrackSupportProvenance
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) :
    (classifyExactSelectedLocalRailFourCellRetained firstWindow lastWindow
      |>.HasSuccessfulTrackSupportProvenance) := by
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
            ExactSelectedLocalRailFourCellRetainedOutcome.HasSuccessfulTrackSupportProvenance]
          have hgeneric := classifyRetainedBypassAppend_hasTrackProvenance
            firstAssembly rebased
          cases hretained : classifyRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              left
              apply orderedTrackSupport_of_assemblies firstWindow lastWindow
                (firstAssembly := firstAssembly) (lastAssembly := rebased)
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              · exact hgeneric
          | collision collision => simp
      | swapped lastAssembly =>
          let lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
              (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)) :=
            ⟨.swapped lastAssembly, lastExact⟩
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          simp only [classifyExactSelectedLocalRailFourCellRetained,
            ExactSelectedLocalRailFourCellRetainedOutcome.HasSuccessfulTrackSupportProvenance]
          have hgeneric := classifyRetainedBypassAppend_hasTrackProvenance
            firstAssembly rebased
          cases hretained : classifyRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              left
              apply orderedTrackSupport_of_assemblies firstWindow lastWindow
                (firstAssembly := firstAssembly) (lastAssembly := rebased)
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              · exact hgeneric
          | collision collision => simp
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
            ExactSelectedLocalRailFourCellRetainedOutcome.HasSuccessfulTrackSupportProvenance]
          have hgeneric := classifyCrossedRetainedBypassAppend_hasTrackProvenance
            firstAssembly rebased
          cases hretained : classifyCrossedRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              right
              apply crossedTrackSupport_of_assemblies firstWindow lastWindow
                (firstAssembly := firstAssembly) (lastAssembly := rebased)
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              · exact hgeneric
          | collision collision => simp
      | swapped lastAssembly =>
          let lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
              (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)) :=
            ⟨.swapped lastAssembly, lastExact⟩
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          simp only [classifyExactSelectedLocalRailFourCellRetained,
            ExactSelectedLocalRailFourCellRetainedOutcome.HasSuccessfulTrackSupportProvenance]
          have hgeneric := classifyCrossedRetainedBypassAppend_hasTrackProvenance
            firstAssembly rebased
          cases hretained : classifyCrossedRetainedBypassAppend firstAssembly rebased with
          | assembled assembly =>
              rw [hretained] at hgeneric
              right
              apply crossedTrackSupport_of_assemblies firstWindow lastWindow
                (firstAssembly := firstAssembly) (lastAssembly := rebased)
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, firstWindow]
              · simp [ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, firstWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.firstSupport, lastWindow]
              · simp [rebased, ExactCertifiedSelectedLocalRailTerminalWindow.toCertified,
                  CertifiedSelectedLocalRailTerminalWindow.secondSupport, lastWindow]
              · exact hgeneric
          | collision collision => simp

/-- A traced four-cell transition whose successful branch retains the exact
ordered-or-crossed terminal-track pairing. -/
structure TrackSupportCertifiedExactSelectedLocalRailTracedFourCellTransition where
  transition : ExactSelectedLocalRailTracedFourCellTransition
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
  hasSuccessfulTrackSupportProvenance :
    transition.outcome.HasSuccessfulTrackSupportProvenance

/-- Construct the track-certified transition from the actual adjacent
classifiers. -/
noncomputable def
    TrackSupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor) :
    TrackSupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) := by
  let transition := ExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) hsource
  refine ⟨transition, ?_⟩
  exact
    classifyExactSelectedLocalRailFourCellRetained_hasSuccessfulTrackSupportProvenance
      transition.firstTrace.toExactTerminalWindow
      transition.lastTrace.toExactTerminalWindow

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
