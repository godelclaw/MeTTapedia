import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendComplete

/-!
# L1: remote separation for provenance-tracked selected rail windows

The unconditional adjacent append may reroute through either of its two
Cell-3 centre faces.  Consequently the older invariant saying that every rail
face is adjacent to one generating centre is too narrow for iteration.  The
right finite-window invariant is the closed neighbourhood of the two centres:
each retained face is either one of those centres or adjacent to one of them.

This module proves the remote half of that invariant.  Two arbitrary supports
carried by such adjacent two-centre windows are disjoint once their left
centres differ by more than three corridor positions.  Equal-centre and
centre-neighbour collisions are excluded by the corridor skeleton; a face
adjacent to both windows is excluded by source boundary-cleanliness.

This is a separation theorem for an explicitly supplied support provenance.
The ordinary straight append, the double-cross swapped append, both immediate
centre-bridge exits, and all six finite residue repairs are proved to carry
it.  The certificate is packaged on the complete-outcome wrapper.  This module
does not yet construct the mutable-terminal-window induction, attach either
annular end cap, or close Fable flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A face belongs to the closed dual neighbourhood of one of two corridor
centres.  Equality is retained separately because dual adjacency is
irreflexive. -/
def FaceNearSelectedCenterPair
    (left right : Fin blockLength) (face : SelectedFace (web := web)) : Prop :=
  face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt left) ∨
    face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt right) ∨
    SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt left) face ∨
    SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt right) face

/-- A finite facial support is carried by the closed neighbourhood of a
two-centre selected Cell-3 window. -/
def SupportNearSelectedCenterPair
    (left right : Fin blockLength) (support : List (SelectedFace (web := web))) :
    Prop :=
  ∀ face ∈ support,
    FaceNearSelectedCenterPair (corridor := corridor) left right face

/-- Both rails of an assembly retain the closed-neighbourhood provenance of
one adjacent Cell-3 window. -/
def SupportedBySelectedCenterPair
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish)
    (left right : Fin blockLength) : Prop :=
  SupportNearSelectedCenterPair (corridor := corridor) left right
      assembly.firstRail.support ∧
    SupportNearSelectedCenterPair (corridor := corridor) left right
      assembly.secondRail.support

variable
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

/-- Membership in the finite adjacent repair carrier implies the closed
two-centre provenance consumed by remote separation. -/
theorem faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
    {face : SelectedFace (web := web)}
    (hface : FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face) :
    FaceNearSelectedCenterPair (corridor := corridor) leftInterior.center
      (nextCorridorInterior leftInterior hnext).center face := by
  rcases hface with hcenter | hleftFirst | hleftSecond | hrightFirst |
    hrightSecond
  · exact Or.inl hcenter
  · exact Or.inr (Or.inr (Or.inl
      (left.paths.firstRail_support_adjacent_center face hleftFirst)))
  · exact Or.inr (Or.inr (Or.inl
      (left.paths.secondRail_support_adjacent_center face hleftSecond)))
  · have hrightFirst' : face ∈ successor.rightRails.paths.firstRail.support := by
      rw [← successor.firstContinuation_support]
      exact hrightFirst
    exact Or.inr (Or.inr (Or.inr
      (successor.rightRails.paths.firstRail_support_adjacent_center
        face hrightFirst')))
  · have hrightSecond' : face ∈ successor.rightRails.paths.secondRail.support := by
      rw [← successor.secondContinuation_support]
      exact hrightSecond
    exact Or.inr (Or.inr (Or.inr
      (successor.rightRails.paths.secondRail_support_adjacent_center
        face hrightSecond')))

/-- To certify a repaired adjacent assembly it suffices to show that both of
its supports stay inside the five explicitly listed source pieces. -/
theorem supportedBySelectedCenterPair_of_support_subset_adjacentPieces
    {firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      firstFinish secondFinish)
    (hfirst : ∀ face ∈ assembly.firstRail.support,
      FaceInAdjacentSelectedRailPieces (successor := successor)
        (left := left) face)
    (hsecond : ∀ face ∈ assembly.secondRail.support,
      FaceInAdjacentSelectedRailPieces (successor := successor)
        (left := left) face) :
    SupportedBySelectedCenterPair (corridor := corridor) assembly
      leftInterior.center (nextCorridorInterior leftInterior hnext).center := by
  constructor
  · intro face hface
    exact faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
      (hfirst face hface)
  · intro face hface
    exact faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
      (hsecond face hface)

/-- The ordinary loop-erased straight append carries the new window
provenance.  Loop erasure can remove support but cannot introduce a face
outside the old and successor local rails. -/
theorem appendSuccessorBypass_supportedBySelectedCenterPair
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter)
    (hfirstSecond : left.paths.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : left.paths.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    SupportedBySelectedCenterPair (corridor := corridor)
      (appendSuccessorBypass successor left.toAssembly
        hfirstSecond hsecondFirst)
      leftInterior.center (nextCorridorInterior leftInterior hnext).center := by
  apply supportedBySelectedCenterPair_of_support_subset_adjacentPieces
    (successor := successor) (left := left)
  · intro face hface
    have hraw :=
      (left.paths.firstRail.append successor.firstContinuation
        |>.support_bypass_subset_support) hface
    rw [SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hold | hnew
    · exact Or.inr (Or.inl hold)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_tail hnew))))
  · intro face hface
    have hraw :=
      (left.paths.secondRail.append successor.secondContinuation
        |>.support_bypass_subset_support) hface
    rw [SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hold | hnew
    · exact Or.inr (Or.inr (Or.inl hold))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_of_mem_tail hnew))))

/-- The double-cross endpoint swap also stays in the same two-cell source
window.  Each rerouted support is already proved to lie in one old rail and
the opposite successor tail. -/
theorem appendSuccessorSwapBothCrossCollisions_supportedBySelectedCenterPair
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter)
    (firstSecondFace secondFirstFace : SelectedFace (web := web))
    (hfirstSecondOld : firstSecondFace ∈ left.paths.firstRail.support)
    (hfirstSecondNew :
      firstSecondFace ∈ successor.secondContinuation.support.tail)
    (hsecondFirstOld : secondFirstFace ∈ left.paths.secondRail.support)
    (hsecondFirstNew :
      secondFirstFace ∈ successor.firstContinuation.support.tail)
    (hfirstFirst : left.paths.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondSecond : left.paths.secondRail.support.Disjoint
      successor.secondContinuation.support.tail) :
    SupportedBySelectedCenterPair (corridor := corridor)
      (appendSuccessorSwapBothCrossCollisions successor left
        firstSecondFace secondFirstFace hfirstSecondOld hfirstSecondNew
        hsecondFirstOld hsecondFirstNew hfirstFirst hsecondSecond)
      leftInterior.center (nextCorridorInterior leftInterior hnext).center := by
  apply supportedBySelectedCenterPair_of_support_subset_adjacentPieces
    (successor := successor) (left := left)
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) firstSecondFace
          hfirstSecondOld hfirstSecondNew
    have hparts : face ∈ left.paths.firstRail.support ∨
        face ∈ successor.secondContinuation.support.tail := by
      exact reroute.route_support_subset face hface
    rcases hparts with hold | hnew
    · exact Or.inr (Or.inl hold)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_of_mem_tail hnew))))
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) secondFirstFace
          hsecondFirstOld hsecondFirstNew
    have hparts : face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support.tail := by
      exact reroute.route_support_subset face hface
    rcases hparts with hold | hnew
    · exact Or.inr (Or.inr (Or.inl hold))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_of_mem_tail hnew))))

/-- The immediate first-to-second centre-bridge repair carries the same
two-centre provenance as the principal adjacent constructors. -/
theorem appendSingleFirstSecondViaLeftCenter_supportedBySelectedCenterPair
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (holdSecond :
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          left.paths.secondRail.support)
    (hnewFirst :
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          successor.firstContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∉
        (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
          (successor := successor) (left := left) collision.face
          collision.mem_old collision.mem_new).route.support) :
    SupportedBySelectedCenterPair (corridor := corridor)
      (appendSingleFirstSecondViaLeftCenter collision holdSecond hnewFirst hcenter)
      leftInterior.center (nextCorridorInterior leftInterior hnext).center := by
  apply supportedBySelectedCenterPair_of_support_subset_adjacentPieces
    (successor := successor) (left := left)
  · exact (appendSingleFirstSecondViaLeftCenter_supportContained
      collision holdSecond hnewFirst hcenter).1
  · exact (appendSingleFirstSecondViaLeftCenter_supportContained
      collision holdSecond hnewFirst hcenter).2

/-- Symmetric two-centre provenance for the immediate second-to-first
centre-bridge repair. -/
theorem appendSingleSecondFirstViaLeftCenter_supportedBySelectedCenterPair
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (holdFirst :
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          left.paths.firstRail.support)
    (hnewSecond :
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support.Disjoint
          successor.secondContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∉
        (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
          (successor := successor) (left := left) collision.face
          collision.mem_old collision.mem_new).route.support) :
    SupportedBySelectedCenterPair (corridor := corridor)
      (appendSingleSecondFirstViaLeftCenter collision holdFirst hnewSecond hcenter)
      leftInterior.center (nextCorridorInterior leftInterior hnext).center := by
  apply supportedBySelectedCenterPair_of_support_subset_adjacentPieces
    (successor := successor) (left := left)
  · exact (appendSingleSecondFirstViaLeftCenter_supportContained
      collision holdFirst hnewSecond hcenter).1
  · exact (appendSingleSecondFirstViaLeftCenter_supportContained
      collision holdFirst hnewSecond hcenter).2

/-- Provenance predicate on the first exhaustive adjacent classifier.  Only
its constructive branches contain assemblies; collision branches retain data
for the later finite repairs. -/
def SelectedLocalRailAppendOutcome.HasWindowProvenance
    (result : SelectedLocalRailAppendOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .swapped assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .singleFirstSecond _ _ => True
  | .singleSecondFirst _ _ => True
  | .doubleCrossSameTrack _ _ _ => True

/-- Every assembly returned directly by the first exhaustive classifier
carries the literal adjacent-window provenance. -/
theorem classifyLocalSuccessorAppend_supportedBySelectedCenterPair :
    (classifyLocalSuccessorAppend successor left).HasWindowProvenance
      (corridor := corridor) := by
  classical
  unfold classifyLocalSuccessorAppend
  split
  · rename_i hfirstSecond
    split
    · rename_i hsecondFirst
      exact appendSuccessorBypass_supportedBySelectedCenterPair
        successor left hfirstSecond hsecondFirst
    · trivial
  · rename_i hfirstSecond
    dsimp only
    split
    · trivial
    · rename_i hsecondFirst
      split
      · rename_i hfirstFirst
        split
        · rename_i hsecondSecond
          exact
            appendSuccessorSwapBothCrossCollisions_supportedBySelectedCenterPair
              successor left
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).face
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).face
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_old
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_new
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_old
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_new
              hfirstFirst hsecondSecond
        · trivial
      · trivial

/-- Provenance predicate for the first-to-second centre-bridge classifier. -/
def SingleFirstSecondCenterBridgeOutcome.HasWindowProvenance
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail}
    (result : SingleFirstSecondCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      SupportedBySelectedCenterPair (corridor := corridor) value
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .meetsOldSecond _ => True
  | .meetsNewFirst _ => True
  | .containsLeftCenter _ => True

/-- The first-to-second centre-bridge classifier certifies every assembly it
returns immediately. -/
theorem classifySingleFirstSecondCenterBridge_hasWindowProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail) :
    (classifySingleFirstSecondCenterBridge collision).HasWindowProvenance
      (corridor := corridor) := by
  classical
  unfold classifySingleFirstSecondCenterBridge
  dsimp only
  split
  · rename_i holdSecond
    split
    · rename_i hnewFirst
      split
      · trivial
      · rename_i hcenter
        exact appendSingleFirstSecondViaLeftCenter_supportedBySelectedCenterPair
          collision holdSecond hnewFirst hcenter
    · trivial
  · trivial

/-- Provenance predicate for the symmetric centre-bridge classifier. -/
def SingleSecondFirstCenterBridgeOutcome.HasWindowProvenance
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail}
    (result : SingleSecondFirstCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      SupportedBySelectedCenterPair (corridor := corridor) value
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .meetsOldFirst _ => True
  | .meetsNewSecond _ => True
  | .containsLeftCenter _ => True

/-- The second-to-first centre-bridge classifier likewise certifies each
immediate assembly. -/
theorem classifySingleSecondFirstCenterBridge_hasWindowProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail) :
    (classifySingleSecondFirstCenterBridge collision).HasWindowProvenance
      (corridor := corridor) := by
  classical
  unfold classifySingleSecondFirstCenterBridge
  dsimp only
  split
  · rename_i holdFirst
    split
    · rename_i hnewSecond
      split
      · trivial
      · rename_i hcenter
        exact appendSingleSecondFirstViaLeftCenter_supportedBySelectedCenterPair
          collision holdFirst hnewSecond hcenter
    · trivial
  · trivial

/-- Provenance predicate for a finite adjacent repair which may preserve or
exchange the two outgoing labels. -/
def AdjacentAssemblySumSupportedBySelectedCenterPair
    (result :
      Sum (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter))
        (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore))) : Prop :=
  match result with
  | .inl assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .inr assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center

/-- Finite-piece provenance from the constructor layer implies the closed
two-centre provenance used by remote-window separation. -/
theorem assemblySum_supportedBySelectedCenterPair_of_supportContained
    (result :
      Sum (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter))
        (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore)))
    (hresult : AssemblySumSupportedByAdjacentSelectedRailPieces
      (successor := successor) (left := left) result) :
    AdjacentAssemblySumSupportedBySelectedCenterPair
      (corridor := corridor) result := by
  cases result with
  | inl assembly =>
      exact supportedBySelectedCenterPair_of_support_subset_adjacentPieces
        (successor := successor) (left := left) assembly hresult.1 hresult.2
  | inr assembly =>
      exact supportedBySelectedCenterPair_of_support_subset_adjacentPieces
        (successor := successor) (left := left) assembly hresult.1 hresult.2

theorem appendFirstSecondSameFirst_supportedBySelectedCenterPair
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AdjacentAssemblySumSupportedBySelectedCenterPair (corridor := corridor)
      (appendFirstSecondSameFirst cross same lengths) :=
  assemblySum_supportedBySelectedCenterPair_of_supportContained
    (appendFirstSecondSameFirst cross same lengths)
    (appendFirstSecondSameFirst_supportContained cross same lengths)

theorem appendSecondFirstSameSecond_supportedBySelectedCenterPair
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AdjacentAssemblySumSupportedBySelectedCenterPair (corridor := corridor)
      (appendSecondFirstSameSecond cross same lengths) :=
  assemblySum_supportedBySelectedCenterPair_of_supportContained
    (appendSecondFirstSameSecond cross same lengths)
    (appendSecondFirstSameSecond_supportContained cross same lengths)

theorem appendFirstSecondSameSecond_supportedBySelectedCenterPair
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AdjacentAssemblySumSupportedBySelectedCenterPair (corridor := corridor)
      (appendFirstSecondSameSecond cross same lengths) :=
  assemblySum_supportedBySelectedCenterPair_of_supportContained
    (appendFirstSecondSameSecond cross same lengths)
    (appendFirstSecondSameSecond_supportContained cross same lengths)

theorem appendSecondFirstSameFirst_supportedBySelectedCenterPair
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AdjacentAssemblySumSupportedBySelectedCenterPair (corridor := corridor)
      (appendSecondFirstSameFirst cross same lengths) :=
  assemblySum_supportedBySelectedCenterPair_of_supportContained
    (appendSecondFirstSameFirst cross same lengths)
    (appendSecondFirstSameFirst_supportContained cross same lengths)

theorem appendFirstSecondCenter_supportedBySelectedCenterPair
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.secondContinuation.support.tail)
    (lengths : 0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AdjacentAssemblySumSupportedBySelectedCenterPair (corridor := corridor)
      (appendFirstSecondCenter cross center lengths) :=
  assemblySum_supportedBySelectedCenterPair_of_supportContained
    (appendFirstSecondCenter cross center lengths)
    (appendFirstSecondCenter_supportContained cross center lengths)

theorem appendSecondFirstCenter_supportedBySelectedCenterPair
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.firstContinuation.support.tail)
    (lengths : 0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AdjacentAssemblySumSupportedBySelectedCenterPair (corridor := corridor)
      (appendSecondFirstCenter cross center lengths) :=
  assemblySum_supportedBySelectedCenterPair_of_supportContained
    (appendSecondFirstCenter cross center lengths)
    (appendSecondFirstCenter_supportContained cross center lengths)

/-- Provenance predicate on the classifier after the impossible mixed
double-cross branch has been removed. -/
def SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance
    (result : SelectedLocalRailAppendResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .swapped assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .singleFirstSecond _ _ => True
  | .singleSecondFirst _ _ => True

/-- The refined classifier preserves the provenance certification on every
constructive branch. -/
theorem classifyLocalSuccessorAppendResolved_hasWindowProvenance :
    (classifyLocalSuccessorAppendResolved successor left).HasWindowProvenance
      (corridor := corridor) := by
  classical
  have hbase := classifyLocalSuccessorAppend_supportedBySelectedCenterPair
    (corridor := corridor) (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppend successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasWindowProvenance,
        SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance] using hbase
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasWindowProvenance,
        SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance] using hbase
  | singleFirstSecond _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance]
  | singleSecondFirst _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance]
  | doubleCrossSameTrack firstSecond secondFirst sameTrack =>
      exact False.elim
        (not_doubleCrossSameTrack firstSecond secondFirst sameTrack)

/-- Provenance predicate on the final finite length classifier.  Residual
branches carry collision data and are certified after their repair is run. -/
def SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance
    (result : SelectedLocalRailAppendLengthResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .swapped assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .firstSecondSameFirst _ _ _ => True
  | .firstSecondSameSecond _ _ _ => True
  | .firstSecondCenter _ _ _ => True
  | .secondFirstSameFirst _ _ _ => True
  | .secondFirstSameSecond _ _ _ => True
  | .secondFirstCenter _ _ _ => True

/-- Every assembly returned before the six finite residue repairs already
carries adjacent-window provenance. -/
theorem classifyLocalSuccessorAppendLengthResolved_hasWindowProvenance :
    (classifyLocalSuccessorAppendLengthResolved successor left).HasWindowProvenance
      (corridor := corridor) := by
  classical
  have hresolved := classifyLocalSuccessorAppendResolved_hasWindowProvenance
    (corridor := corridor) (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendResolved successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance,
        SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
        using hresolved
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasWindowProvenance,
        SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
        using hresolved
  | singleFirstSecond cross _ =>
      have hs := classifySingleFirstSecondCenterBridge_hasWindowProvenance
        (corridor := corridor) cross
      cases hcenter : classifySingleFirstSecondCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleFirstSecondCenterBridgeOutcome.HasWindowProvenance,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
            using hs
      | meetsOldSecond _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
      | meetsNewFirst _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
      | containsLeftCenter _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
  | singleSecondFirst cross _ =>
      have hs := classifySingleSecondFirstCenterBridge_hasWindowProvenance
        (corridor := corridor) cross
      cases hcenter : classifySingleSecondFirstCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleSecondFirstCenterBridgeOutcome.HasWindowProvenance,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
            using hs
      | meetsOldFirst _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
      | meetsNewSecond _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]
      | containsLeftCenter _ =>
          simp [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance]

/-- Public provenance predicate on the complete adjacent append outcome. -/
def SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance
    (result : SelectedLocalRailAppendCompleteOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center
  | .swapped assembly =>
      SupportedBySelectedCenterPair (corridor := corridor) assembly
        leftInterior.center (nextCorridorInterior leftInterior hnext).center

/-- **L1 complete adjacent append provenance.** The unconditional local append
returns two simple support-disjoint rails, and whichever endpoint order it
chooses, both rails remain in the closed dual neighbourhood of the two literal
Cell-3 centres. -/
theorem appendLocalSuccessorComplete_hasWindowProvenance :
    (appendLocalSuccessorComplete successor left).HasWindowProvenance
      (corridor := corridor) := by
  classical
  have hlength :=
    classifyLocalSuccessorAppendLengthResolved_hasWindowProvenance
      (corridor := corridor) (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendLengthResolved successor left with
  | straight assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance,
        SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hlength
  | swapped assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasWindowProvenance,
        SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hlength
  | firstSecondSameFirst cross same lengths =>
      have hs := appendFirstSecondSameFirst_supportedBySelectedCenterPair
        (corridor := corridor) cross same lengths
      cases hrepair : appendFirstSecondSameFirst cross same lengths with
      | inl assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
      | inr assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
  | firstSecondSameSecond cross same lengths =>
      have hs := appendFirstSecondSameSecond_supportedBySelectedCenterPair
        (corridor := corridor) cross same lengths
      cases hrepair : appendFirstSecondSameSecond cross same lengths with
      | inl assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
      | inr assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
  | firstSecondCenter cross center lengths =>
      have hs := appendFirstSecondCenter_supportedBySelectedCenterPair
        (corridor := corridor) cross center lengths
      cases hrepair : appendFirstSecondCenter cross center lengths with
      | inl assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
      | inr assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
  | secondFirstSameFirst cross same lengths =>
      have hs := appendSecondFirstSameFirst_supportedBySelectedCenterPair
        (corridor := corridor) cross same lengths
      cases hrepair : appendSecondFirstSameFirst cross same lengths with
      | inl assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
      | inr assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
  | secondFirstSameSecond cross same lengths =>
      have hs := appendSecondFirstSameSecond_supportedBySelectedCenterPair
        (corridor := corridor) cross same lengths
      cases hrepair : appendSecondFirstSameSecond cross same lengths with
      | inl assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
      | inr assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
  | secondFirstCenter cross center lengths =>
      have hs := appendSecondFirstCenter_supportedBySelectedCenterPair
        (corridor := corridor) cross center lengths
      cases hrepair : appendSecondFirstCenter cross center lengths with
      | inl assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
      | inr assembly =>
          simpa [appendLocalSuccessorComplete, hresult, hrepair,
            AdjacentAssemblySumSupportedBySelectedCenterPair,
            SelectedLocalRailAppendCompleteOutcome.HasWindowProvenance] using hs
/-- **L1 remote two-window separation.** Closed-neighbourhood provenance is
exactly strong enough to separate arbitrary selected rail supports belonging
to sufficiently remote adjacent Cell-3 windows. -/
theorem supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
    {leftInterior : CorridorInterior blockLength}
    {hleftNext : leftInterior.center.val + 2 < blockLength}
    {rightInterior : CorridorInterior blockLength}
    {hrightNext : rightInterior.center.val + 2 < blockLength}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (leftSupport rightSupport : List (SelectedFace (web := web)))
    (hleft : SupportNearSelectedCenterPair (corridor := corridor)
      leftInterior.center (nextCorridorInterior leftInterior hleftNext).center
      leftSupport)
    (hright : SupportNearSelectedCenterPair (corridor := corridor)
      rightInterior.center (nextCorridorInterior rightInterior hrightNext).center
      rightSupport)
    (hseparated : leftInterior.center.val + 3 < rightInterior.center.val) :
    leftSupport.Disjoint rightSupport := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have h00ne : skeleton.faceAt leftInterior.center ≠
      skeleton.faceAt rightInterior.center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      omega)
  have h01ne : skeleton.faceAt leftInterior.center ≠
      skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      change leftInterior.center.val = rightInterior.center.val + 1 at hvalues
      omega)
  have h10ne : skeleton.faceAt
        (nextCorridorInterior leftInterior hleftNext).center ≠
      skeleton.faceAt rightInterior.center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      change leftInterior.center.val + 1 = rightInterior.center.val at hvalues
      omega)
  have h11ne : skeleton.faceAt
        (nextCorridorInterior leftInterior hleftNext).center ≠
      skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      change leftInterior.center.val + 1 = rightInterior.center.val + 1 at hvalues
      omega)
  have h00notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt leftInterior.center)
      (skeleton.faceAt rightInterior.center) :=
    skeleton.separated_not_adjacent leftInterior.center rightInterior.center
      (by omega)
  have h01notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt leftInterior.center)
      (skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center) :=
    skeleton.separated_not_adjacent leftInterior.center
      (nextCorridorInterior rightInterior hrightNext).center (by
        change leftInterior.center.val + 1 < rightInterior.center.val + 1
        omega)
  have h10notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior leftInterior hleftNext).center)
      (skeleton.faceAt rightInterior.center) :=
    skeleton.separated_not_adjacent
      (nextCorridorInterior leftInterior hleftNext).center rightInterior.center
      (by
        change leftInterior.center.val + 1 + 1 < rightInterior.center.val
        omega)
  have h11notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior leftInterior hleftNext).center)
      (skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center) :=
    skeleton.separated_not_adjacent
      (nextCorridorInterior leftInterior hleftNext).center
      (nextCorridorInterior rightInterior hrightNext).center (by
        change leftInterior.center.val + 1 + 1 < rightInterior.center.val + 1
        omega)
  rw [List.disjoint_left]
  intro face hfaceLeft hfaceRight
  rcases hleft face hfaceLeft with hleft0 | hleft1 | hleft0adj | hleft1adj
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · exact h00ne (hleft0.symm.trans hright0)
    · exact h01ne (hleft0.symm.trans hright1)
    · subst face
      exact h00notadj hright0adj.symm
    · subst face
      exact h01notadj hright1adj.symm
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · exact h10ne (hleft1.symm.trans hright0)
    · exact h11ne (hleft1.symm.trans hright1)
    · subst face
      exact h10notadj hright0adj.symm
    · subst face
      exact h11notadj hright1adj.symm
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · subst face
      exact h00notadj hleft0adj
    · subst face
      exact h01notadj hleft0adj
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        leftInterior.center rightInterior.center (by omega)
        ⟨face, hleft0adj, hright0adj⟩
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        leftInterior.center
        (nextCorridorInterior rightInterior hrightNext).center (by
          change leftInterior.center.val + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleft0adj, hright1adj⟩
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · subst face
      exact h10notadj hleft1adj
    · subst face
      exact h11notadj hleft1adj
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        (nextCorridorInterior leftInterior hleftNext).center
        rightInterior.center (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val
          omega)
        ⟨face, hleft1adj, hright0adj⟩
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        (nextCorridorInterior leftInterior hleftNext).center
        (nextCorridorInterior rightInterior hrightNext).center (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleft1adj, hright1adj⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
