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
the collision.  It does not yet extract the two local walk pieces from every
constructor of the middle-replacement collision packet, prove separation from
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
      route.IsPath ∧ face ∉ route.support := by
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
  refine ⟨route, crossSpliceAroundWithBridge_isPath _ _ _ _ _, ?_⟩
  exact current_not_mem_crossSpliceAroundWithBridge_support
    oldWalk newWalk holdPath hnewPath hold hnew holdStart hnewEnd
      centerBridge hbridgeAvoids

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
      route.IsPath ∧ face ∉ route.support := by
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
  refine ⟨route, crossSpliceAroundWithBridge_isPath _ _ _ _ _, ?_⟩
  exact current_not_mem_crossSpliceAroundWithBridge_support
    oldWalk newWalk holdPath hnewPath hold hnew holdStart hnewEnd
      centerBridge hbridgeAvoids

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
