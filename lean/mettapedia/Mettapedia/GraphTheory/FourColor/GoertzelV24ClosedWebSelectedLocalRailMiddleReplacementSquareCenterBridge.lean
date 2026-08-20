import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementCycles
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathInteriorCrossSplice

/-!
# L1: splice a replacement-square collision through corridor centres

The distance-two square branches expose a collision face adjacent to the two
outer corridor centres of a three-centre chain.  A local rail piece on either
side is itself supported on faces adjacent to its own centre.  Consequently
the predecessor and successor at an internal collision can be joined by the
literal four-edge walk

`predecessor -> first centre -> middle centre -> last centre -> successor`.

This module constructs that path and proves that loop-erased splicing removes
the collision.  It also specializes all four choices of first-cell rail and
third-cell continuation in the first--third square branch to literal source
endpoints.  It does not yet extract the two local walk pieces from every
constructor of the middle-replacement collision packet, handle the remaining
middle-cell source atoms or the second--fourth mirror, prove separation from
the companion rail, iterate the repair, or attach annular end caps.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathInteriorCrossSplice
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
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

private theorem penultimate_mem_original_support
    {start finish current : SelectedFace (web := web)}
    (walk : SelectedDualGraph (web := web).Walk start finish)
    (hcurrent : current ∈ walk.support) (hstart : start ≠ current) :
    (walk.takeUntil current hcurrent).penultimate ∈ walk.support := by
  have hnotNil : ¬(walk.takeUntil current hcurrent).Nil := by
    simpa only [SimpleGraph.Walk.nil_takeUntil] using hstart
  apply walk.support_takeUntil_subset_support hcurrent
  exact List.dropLast_subset _
    ((walk.takeUntil current hcurrent).penultimate_mem_dropLast_support hnotNil)

private theorem snd_mem_original_support
    {start finish current : SelectedFace (web := web)}
    (walk : SelectedDualGraph (web := web).Walk start finish)
    (hcurrent : current ∈ walk.support) (hend : current ≠ finish) :
    (walk.dropUntil current hcurrent).snd ∈ walk.support := by
  have hnotNil : ¬(walk.dropUntil current hcurrent).Nil := by
    intro hnil
    exact hend hnil.eq
  apply walk.support_dropUntil_subset_support hcurrent
  exact List.mem_of_mem_tail
    ((walk.dropUntil current hcurrent).snd_mem_tail_support hnotNil)

/-- **L1 first--third square repair.**  The literal three-centre corridor
chain constructs a simple old-to-new path avoiding the internal collision. -/
theorem exists_firstThirdSquare_crossSplice
    {face oldStart oldFinish newStart newFinish : SelectedFace (web := web)}
    (oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish)
    (newWalk : SelectedDualGraph (web := web).Walk newStart newFinish)
    (holdPath : oldWalk.IsPath) (hnewPath : newWalk.IsPath)
    (hold : face ∈ oldWalk.support) (hnew : face ∈ newWalk.support)
    (holdStart : oldStart ≠ face) (hnewEnd : face ≠ newFinish)
    (holdAdjacent : ∀ current ∈ oldWalk.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt firstInterior.center) current)
    (hnewAdjacent : ∀ current ∈ newWalk.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        current)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ∃ route : SelectedDualGraph (web := web).Walk oldStart newFinish,
      route.IsPath ∧ face ∉ route.support ∧
        ∀ current ∈ route.support,
          current ∈ oldWalk.support ∨
          current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center ∨
          current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior firstInterior hfirstNext).center ∨
          current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
          current ∈ newWalk.support := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let secondInterior := nextCorridorInterior firstInterior hfirstNext
  let thirdInterior := nextCorridorInterior secondInterior hbridgeNext
  let oldPrefix := oldWalk.takeUntil face hold
  let newSuffix := newWalk.dropUntil face hnew
  have hprefixNotNil : ¬oldPrefix.Nil := by
    simpa only [oldPrefix, SimpleGraph.Walk.nil_takeUntil] using holdStart
  have hsuffixNotNil : ¬newSuffix.Nil := by
    intro hnil
    exact hnewEnd hnil.eq
  have hleft : SelectedDualGraph (web := web).Adj
      oldPrefix.penultimate (skeleton.faceAt firstInterior.center) :=
    (holdAdjacent oldPrefix.penultimate
      (penultimate_mem_original_support oldWalk hold holdStart)).symm
  have hfirstSecond : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center)
      (skeleton.faceAt secondInterior.center) :=
    skeleton.consecutive_adjacent firstInterior.center secondInterior.center rfl
  have hsecondThird : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt secondInterior.center)
      (skeleton.faceAt thirdInterior.center) :=
    skeleton.consecutive_adjacent secondInterior.center thirdInterior.center rfl
  have hright : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt thirdInterior.center) newSuffix.snd :=
    hnewAdjacent newSuffix.snd
      (snd_mem_original_support newWalk hnew hnewEnd)
  let centerBridge := threeCenterBridge hleft hfirstSecond hsecondThird hright
  have hbridgeAvoids : face ∉ centerBridge.support := by
    apply current_not_mem_threeCenterBridge_support
    · exact oldPrefix.adj_penultimate hprefixNotNil |>.ne.symm
    · exact hfirst.ne.symm
    · exact hfaceSecond
    · exact hthird.ne.symm
    · exact newSuffix.adj_snd hsuffixNotNil |>.ne
  let route := crossSpliceAroundWithBridge oldWalk newWalk hold hnew centerBridge
  refine ⟨route, crossSpliceAroundWithBridge_isPath _ _ _ _ _, ?_, ?_⟩
  · exact current_not_mem_crossSpliceAroundWithBridge_support
      oldWalk newWalk holdPath hnewPath hold hnew holdStart hnewEnd
        centerBridge hbridgeAvoids
  · intro current hcurrent
    rcases crossSpliceAroundWithBridge_support_subset oldWalk newWalk hold hnew
        holdStart hnewEnd centerBridge current hcurrent with
      holdCurrent | hcenter | hnewCurrent
    · exact .inl holdCurrent
    · simp only [centerBridge, threeCenterBridge_support, List.mem_cons,
        List.not_mem_nil, or_false] at hcenter
      rcases hcenter with hleft | hfirst | hsecond | hthird | hright
      · exact .inl
          (hleft ▸ penultimate_mem_original_support oldWalk hold holdStart)
      · exact .inr (.inl hfirst)
      · exact .inr (.inr (.inl hsecond))
      · exact .inr (.inr (.inr (.inl hthird)))
      · exact .inr (.inr (.inr (.inr
          (hright ▸ snd_mem_original_support newWalk hnew hnewEnd))))
    · exact .inr (.inr (.inr (.inr hnewCurrent)))

/-- **L1 second--fourth square repair.**  The shifted three-centre chain gives
the symmetric collision-removing splice. -/
theorem exists_secondFourthSquare_crossSplice
    {face oldStart oldFinish newStart newFinish : SelectedFace (web := web)}
    (oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish)
    (newWalk : SelectedDualGraph (web := web).Walk newStart newFinish)
    (holdPath : oldWalk.IsPath) (hnewPath : newWalk.IsPath)
    (hold : face ∈ oldWalk.support) (hnew : face ∈ newWalk.support)
    (holdStart : oldStart ≠ face) (hnewEnd : face ≠ newFinish)
    (holdAdjacent : ∀ current ∈ oldWalk.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior firstInterior hfirstNext).center) current)
    (hnewAdjacent : ∀ current ∈ newWalk.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) current)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hfaceThird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center) :
    ∃ route : SelectedDualGraph (web := web).Walk oldStart newFinish,
      route.IsPath ∧ face ∉ route.support ∧
        ∀ current ∈ route.support,
          current ∈ oldWalk.support ∨
          current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior firstInterior hfirstNext).center ∨
          current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior
                (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
          current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior
                (nextCorridorInterior
                  (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
                hlastNext).center ∨
          current ∈ newWalk.support := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let secondInterior := nextCorridorInterior firstInterior hfirstNext
  let thirdInterior := nextCorridorInterior secondInterior hbridgeNext
  let fourthInterior := nextCorridorInterior thirdInterior hlastNext
  let oldPrefix := oldWalk.takeUntil face hold
  let newSuffix := newWalk.dropUntil face hnew
  have hprefixNotNil : ¬oldPrefix.Nil := by
    simpa only [oldPrefix, SimpleGraph.Walk.nil_takeUntil] using holdStart
  have hsuffixNotNil : ¬newSuffix.Nil := by
    intro hnil
    exact hnewEnd hnil.eq
  have hleft : SelectedDualGraph (web := web).Adj
      oldPrefix.penultimate (skeleton.faceAt secondInterior.center) :=
    (holdAdjacent oldPrefix.penultimate
      (penultimate_mem_original_support oldWalk hold holdStart)).symm
  have hsecondThird : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt secondInterior.center)
      (skeleton.faceAt thirdInterior.center) :=
    skeleton.consecutive_adjacent secondInterior.center thirdInterior.center rfl
  have hthirdFourth : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt thirdInterior.center)
      (skeleton.faceAt fourthInterior.center) :=
    skeleton.consecutive_adjacent thirdInterior.center fourthInterior.center rfl
  have hright : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt fourthInterior.center) newSuffix.snd :=
    hnewAdjacent newSuffix.snd
      (snd_mem_original_support newWalk hnew hnewEnd)
  let centerBridge := threeCenterBridge hleft hsecondThird hthirdFourth hright
  have hbridgeAvoids : face ∉ centerBridge.support := by
    apply current_not_mem_threeCenterBridge_support
    · exact oldPrefix.adj_penultimate hprefixNotNil |>.ne.symm
    · exact hsecond.ne.symm
    · exact hfaceThird
    · exact hfourth.ne.symm
    · exact newSuffix.adj_snd hsuffixNotNil |>.ne
  let route := crossSpliceAroundWithBridge oldWalk newWalk hold hnew centerBridge
  refine ⟨route, crossSpliceAroundWithBridge_isPath _ _ _ _ _, ?_, ?_⟩
  · exact current_not_mem_crossSpliceAroundWithBridge_support
      oldWalk newWalk holdPath hnewPath hold hnew holdStart hnewEnd
        centerBridge hbridgeAvoids
  · intro current hcurrent
    rcases crossSpliceAroundWithBridge_support_subset oldWalk newWalk hold hnew
        holdStart hnewEnd centerBridge current hcurrent with
      holdCurrent | hcenter | hnewCurrent
    · exact .inl holdCurrent
    · simp only [centerBridge, threeCenterBridge_support, List.mem_cons,
        List.not_mem_nil, or_false] at hcenter
      rcases hcenter with hleft | hsecond | hthird | hfourth | hright
      · exact .inl
          (hleft ▸ penultimate_mem_original_support oldWalk hold holdStart)
      · exact .inr (.inl hsecond)
      · exact .inr (.inr (.inl hthird))
      · exact .inr (.inr (.inr (.inl hfourth)))
      · exact .inr (.inr (.inr (.inr
          (hright ▸ snd_mem_original_support newWalk hnew hnewEnd))))
    · exact .inr (.inr (.inr (.inr hnewCurrent)))

section SourceTrackSpecialization

variable
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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

/-- Exact source ingredients from which a first--third square splice may draw
its support.  This is the finite separation interface for the companion rail. -/
def FaceInFirstThirdSquareSourceSpliceSupport
    (oldSupport newSupport : List (SelectedFace (web := web)))
    (current : SelectedFace (web := web)) : Prop :=
  current ∈ oldSupport ∨
    current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      firstInterior.center ∨
    current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center ∨
    current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
    current ∈ newSupport

/-- A support receipt for the literal source splice reduces companion
separation to the two source pieces and the three displayed centres. -/
theorem support_disjoint_of_faceInFirstThirdSquareSourceSpliceSupport
    {oldSupport newSupport routeSupport companionSupport :
      List (SelectedFace (web := web))}
    (hroute : ∀ current ∈ routeSupport,
      FaceInFirstThirdSquareSourceSpliceSupport
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        oldSupport newSupport current)
    (hold : oldSupport.Disjoint companionSupport)
    (hfirstCenter :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center ∉ companionSupport)
    (hsecondCenter :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center ∉ companionSupport)
    (hthirdCenter :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∉
        companionSupport)
    (hnew : newSupport.Disjoint companionSupport) :
    routeSupport.Disjoint companionSupport := by
  rw [List.disjoint_left]
  intro current hcurrent hcompanion
  rcases hroute current hcurrent with holdCurrent | hfirst | hsecond | hthird | hnewCurrent
  · exact (List.disjoint_left.mp hold holdCurrent) hcompanion
  · exact hfirstCenter (hfirst ▸ hcompanion)
  · exact hsecondCenter (hsecond ▸ hcompanion)
  · exact hthirdCenter (hthird ▸ hcompanion)
  · exact (List.disjoint_left.mp hnew hnewCurrent) hcompanion

/-- The first/first literal source-track instance of the first--third square
repair.  Reversing the old rail starts at the proved collision-free seam flank;
the following successor ends at the proved collision-free opposite seam. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.exists_firstThirdSquare_firstFirstSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hfirst : face ∈ firstLeft.paths.firstRail.support)
    (hnew : face ∈ bridge.firstContinuation.support)
    (hfirstAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt firstInterior.center) face)
    (hthirdAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ∃ route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore),
      route.IsPath ∧ face ∉ route.support ∧
        ∀ current ∈ route.support,
          FaceInFirstThirdSquareSourceSpliceSupport
            (corridor := corridor) (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            firstLeft.paths.firstRail.support bridge.firstContinuation.support
            current := by
  have hold : face ∈ firstLeft.paths.firstRail.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hfirst
  have holdStart :
      selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore ≠
        face :=
    (data.face_ne_firstFlanks hsource).1.symm
  have hnewEnd : face ≠
      selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore := by
    intro hface
    apply (data.face_ne_lastFlanks hsource).1
    exact hface.trans (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingBefore_eq_nextLeftBefore lastSuccessor))
  have holdAdjacent : ∀ current ∈ firstLeft.paths.firstRail.reverse.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt firstInterior.center) current := by
    intro current hcurrent
    apply firstLeft.paths.firstRail_support_adjacent_center
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hcurrent
  have hnewAdjacent : ∀ current ∈ bridge.firstContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        current := by
    intro current hcurrent
    apply bridge.rightRails.paths.firstRail_support_adjacent_center
    simpa only [bridge.firstContinuation_support] using hcurrent
  rcases exists_firstThirdSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext)
      firstLeft.paths.firstRail.reverse bridge.firstContinuation
      firstLeft.paths.firstRail_isPath.reverse bridge.firstContinuation_isPath
      hold hnew holdStart hnewEnd holdAdjacent hnewAdjacent hfirstAdjacent
      hthirdAdjacent hfaceSecond with ⟨route, hpath, havoids, hsupport⟩
  refine ⟨route, hpath, havoids, ?_⟩
  intro current hcurrent
  simpa only [FaceInFirstThirdSquareSourceSpliceSupport,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hsupport current hcurrent

/-- The first/second literal source-track instance of the first--third square
repair. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.exists_firstThirdSquare_firstSecondSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hfirst : face ∈ firstLeft.paths.firstRail.support)
    (hnew : face ∈ bridge.secondContinuation.support)
    (hfirstAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt firstInterior.center) face)
    (hthirdAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ∃ route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter),
      route.IsPath ∧ face ∉ route.support ∧
        ∀ current ∈ route.support,
          FaceInFirstThirdSquareSourceSpliceSupport
            (corridor := corridor) (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            firstLeft.paths.firstRail.support bridge.secondContinuation.support
            current := by
  have hold : face ∈ firstLeft.paths.firstRail.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hfirst
  have holdStart :
      selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore ≠
        face :=
    (data.face_ne_firstFlanks hsource).1.symm
  have hnewEnd : face ≠
      selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter := by
    intro hface
    apply (data.face_ne_lastFlanks hsource).2
    exact hface.trans (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingAfter_eq_nextLeftAfter lastSuccessor))
  have holdAdjacent : ∀ current ∈ firstLeft.paths.firstRail.reverse.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt firstInterior.center) current := by
    intro current hcurrent
    apply firstLeft.paths.firstRail_support_adjacent_center
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hcurrent
  have hnewAdjacent : ∀ current ∈ bridge.secondContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        current := by
    intro current hcurrent
    apply bridge.rightRails.paths.secondRail_support_adjacent_center
    simpa only [bridge.secondContinuation_support] using hcurrent
  rcases exists_firstThirdSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext)
      firstLeft.paths.firstRail.reverse bridge.secondContinuation
      firstLeft.paths.firstRail_isPath.reverse bridge.secondContinuation_isPath
      hold hnew holdStart hnewEnd holdAdjacent hnewAdjacent hfirstAdjacent
      hthirdAdjacent hfaceSecond with ⟨route, hpath, havoids, hsupport⟩
  refine ⟨route, hpath, havoids, ?_⟩
  intro current hcurrent
  simpa only [FaceInFirstThirdSquareSourceSpliceSupport,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hsupport current hcurrent

/-- The second/first literal source-track instance of the first--third square
repair. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.exists_firstThirdSquare_secondFirstSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hfirst : face ∈ firstLeft.paths.secondRail.support)
    (hnew : face ∈ bridge.firstContinuation.support)
    (hfirstAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt firstInterior.center) face)
    (hthirdAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ∃ route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore),
      route.IsPath ∧ face ∉ route.support ∧
        ∀ current ∈ route.support,
          FaceInFirstThirdSquareSourceSpliceSupport
            (corridor := corridor) (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            firstLeft.paths.secondRail.support bridge.firstContinuation.support
            current := by
  have hold : face ∈ firstLeft.paths.secondRail.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hfirst
  have holdStart :
      selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter ≠
        face :=
    (data.face_ne_firstFlanks hsource).2.symm
  have hnewEnd : face ≠
      selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore := by
    intro hface
    apply (data.face_ne_lastFlanks hsource).1
    exact hface.trans (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingBefore_eq_nextLeftBefore lastSuccessor))
  have holdAdjacent : ∀ current ∈ firstLeft.paths.secondRail.reverse.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt firstInterior.center) current := by
    intro current hcurrent
    apply firstLeft.paths.secondRail_support_adjacent_center
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hcurrent
  have hnewAdjacent : ∀ current ∈ bridge.firstContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        current := by
    intro current hcurrent
    apply bridge.rightRails.paths.firstRail_support_adjacent_center
    simpa only [bridge.firstContinuation_support] using hcurrent
  rcases exists_firstThirdSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext)
      firstLeft.paths.secondRail.reverse bridge.firstContinuation
      firstLeft.paths.secondRail_isPath.reverse bridge.firstContinuation_isPath
      hold hnew holdStart hnewEnd holdAdjacent hnewAdjacent hfirstAdjacent
      hthirdAdjacent hfaceSecond with ⟨route, hpath, havoids, hsupport⟩
  refine ⟨route, hpath, havoids, ?_⟩
  intro current hcurrent
  simpa only [FaceInFirstThirdSquareSourceSpliceSupport,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hsupport current hcurrent

/-- The second/second literal source-track instance of the first--third square
repair. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.exists_firstThirdSquare_secondSecondSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {face : SelectedFace (web := web)}
    (data : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hfirst : face ∈ firstLeft.paths.secondRail.support)
    (hnew : face ∈ bridge.secondContinuation.support)
    (hfirstAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt firstInterior.center) face)
    (hthirdAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ∃ route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter),
      route.IsPath ∧ face ∉ route.support ∧
        ∀ current ∈ route.support,
          FaceInFirstThirdSquareSourceSpliceSupport
            (corridor := corridor) (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            firstLeft.paths.secondRail.support bridge.secondContinuation.support
            current := by
  have hold : face ∈ firstLeft.paths.secondRail.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hfirst
  have holdStart :
      selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter ≠
        face :=
    (data.face_ne_firstFlanks hsource).2.symm
  have hnewEnd : face ≠
      selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter := by
    intro hface
    apply (data.face_ne_lastFlanks hsource).2
    exact hface.trans (congrArg (selectedPlacementSideFace thirdPlacement)
      (bridge.rightOutgoingAfter_eq_nextLeftAfter lastSuccessor))
  have holdAdjacent : ∀ current ∈ firstLeft.paths.secondRail.reverse.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt firstInterior.center) current := by
    intro current hcurrent
    apply firstLeft.paths.secondRail_support_adjacent_center
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hcurrent
  have hnewAdjacent : ∀ current ∈ bridge.secondContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        current := by
    intro current hcurrent
    apply bridge.rightRails.paths.secondRail_support_adjacent_center
    simpa only [bridge.secondContinuation_support] using hcurrent
  rcases exists_firstThirdSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext)
      firstLeft.paths.secondRail.reverse bridge.secondContinuation
      firstLeft.paths.secondRail_isPath.reverse bridge.secondContinuation_isPath
      hold hnew holdStart hnewEnd holdAdjacent hnewAdjacent hfirstAdjacent
      hthirdAdjacent hfaceSecond with ⟨route, hpath, havoids, hsupport⟩
  refine ⟨route, hpath, havoids, ?_⟩
  intro current hcurrent
  simpa only [FaceInFirstThirdSquareSourceSpliceSupport,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hsupport current hcurrent

end SourceTrackSpecialization

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
