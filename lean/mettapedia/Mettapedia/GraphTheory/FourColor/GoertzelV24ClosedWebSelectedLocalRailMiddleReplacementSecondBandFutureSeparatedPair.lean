import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandFutureCompanionResolution

/-!
# L1: rebuild the separated pair from an advanced companion route

A parity-compatible advanced source splice and companion route already have
the correct four endpoints and are individually simple.  The primary splice's
sharp support receipt reduces their mutual separation to the retained old
prefix, the six literal corridor centres, and the retained future suffix.  In
particular, collisions in the discarded old suffix or future prefix are not
premises.  The companion route's receipt further reduces the two retained-piece
obligations to its literal middle rail and future companion piece.

This module packages that fact in the standard two-rail assembly type.  It
also reduces the six-centre premise for the loop-erased companion route to
the literal middle rail and future companion piece from which that route was
built.

The centre premise is not discharged here.  Consequently this is an
explicitly conditional assembly interface, not a construction of the
arbitrary-length rails, the separated crosscuts, or Fable flag L1.
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
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev FourthInterior :=
  nextCorridorInterior
    (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
    hlastNext

variable
    {hfourthNext :
      (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)).center.val + 2 <
          blockLength}
    {hfifthNext :
      (nextCorridorInterior
        (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
          (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
        hfourthNext).center.val + 2 < blockLength}
    {hsixthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
            (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
          hfourthNext)
        hfifthNext).center.val + 2 < blockLength}

/-- The six displayed centres used by the advanced primary splice. -/
def secondBandFutureSpliceCenters : List (SelectedFace (web := web)) :=
  [corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center,
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center,
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)).center,
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
          (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
        hfourthNext).center,
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior
          (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
            (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
          hfourthNext)
        hfifthNext).center,
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            hfourthNext)
          hfifthNext)
        hsixthNext).center]

/-- A walk avoids every literal centre used by the advanced primary splice. -/
def WalkAvoidsSecondBandFutureSpliceCenters
    {start finish : SelectedFace (web := web)}
    (walk : SelectedDualGraph (web := web).Walk start finish) : Prop :=
  ∀ center ∈ secondBandFutureSpliceCenters
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext),
    center ∉ walk.support

/-- The loop-erased companion route avoids all six splice centres whenever
its two literal ingredients do. -/
theorem SecondBandFutureSourceSpliceCompanionRoute.avoidsSpliceCenters_of_parts
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish : SelectedFace (web := web)}
    {oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish}
    {newWalk : SelectedDualGraph (web := web).Walk newStart newFinish}
    {oldCompanion : SelectedDualGraph (web := web).Walk
      oldCompanionStart oldCompanionFinish}
    {newCompanion : SelectedDualGraph (web := web).Walk
      newCompanionStart newCompanionFinish}
    {pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face) oldWalk newWalk oldCompanion newCompanion}
    (route : SecondBandFutureSourceSpliceCompanionRoute pieces)
    (hmiddle : WalkAvoidsSecondBandFutureSpliceCenters
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext) route.middle)
    (hfuture : WalkAvoidsSecondBandFutureSpliceCenters
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext) newCompanion) :
    WalkAvoidsSecondBandFutureSpliceCenters
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext) route.route := by
  intro center hcenter hroute
  rcases route.support_receipt center hroute with hmiddleCurrent | hfutureCurrent
  · exact hmiddle center hcenter hmiddleCurrent
  · exact hfuture center hcenter hfutureCurrent

/-- Disjointness from the loop-erased companion route reduces to disjointness
from its literal middle rail and future companion piece. -/
theorem SecondBandFutureSourceSpliceCompanionRoute.support_disjoint_of_parts
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish sourceStart sourceFinish :
        SelectedFace (web := web)}
    {oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish}
    {newWalk : SelectedDualGraph (web := web).Walk newStart newFinish}
    {oldCompanion : SelectedDualGraph (web := web).Walk
      oldCompanionStart oldCompanionFinish}
    {newCompanion : SelectedDualGraph (web := web).Walk
      newCompanionStart newCompanionFinish}
    {pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face) oldWalk newWalk oldCompanion newCompanion}
    (route : SecondBandFutureSourceSpliceCompanionRoute pieces)
    (source : SelectedDualGraph (web := web).Walk sourceStart sourceFinish)
    (hmiddle : source.support.Disjoint route.middle.support)
    (hfuture : source.support.Disjoint newCompanion.support) :
    source.support.Disjoint route.route.support := by
  rw [List.disjoint_left]
  intro current hsource hroute
  rcases route.support_receipt current hroute with hmiddleCurrent | hfutureCurrent
  · exact (List.disjoint_left.mp hmiddle hsource) hmiddleCurrent
  · exact (List.disjoint_left.mp hfuture hsource) hfutureCurrent

/-- A centre-clear companion route and its primary splice form a literal
two-rail assembly with the source endpoints and machine-checked mutual
separation.  Only the retained old prefix and future suffix occur in the
cross-piece premises; the future suffix versus future companion fact is
inherited from the already-separated future source pair.  The centre-clear
premise remains an explicit debt. -/
noncomputable def SecondBandFutureSourceSpliceCompanionRoute.toSeparatedAssembly
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish : SelectedFace (web := web)}
    {oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish}
    {newWalk : SelectedDualGraph (web := web).Walk newStart newFinish}
    {oldCompanion : SelectedDualGraph (web := web).Walk
      oldCompanionStart oldCompanionFinish}
    {newCompanion : SelectedDualGraph (web := web).Walk
      newCompanionStart newCompanionFinish}
    {pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face) oldWalk newWalk oldCompanion newCompanion}
    (route : SecondBandFutureSourceSpliceCompanionRoute pieces)
    (holdMiddle :
      (oldWalk.takeUntil face pieces.splice.oldOccurrence).dropLast.support.Disjoint
        route.middle.support)
    (holdFuture :
      (oldWalk.takeUntil face pieces.splice.oldOccurrence).dropLast.support.Disjoint
        newCompanion.support)
    (hnewMiddle :
      (newWalk.dropUntil face pieces.splice.newOccurrence).tail.support.Disjoint
        route.middle.support)
    (hcenters : WalkAvoidsSecondBandFutureSpliceCenters
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext) route.route) :
    SelectedSourceLocalRailAssembly (web := web)
      oldStart oldCompanionStart newFinish newCompanionFinish :=
  {
    firstRail := pieces.splice.route
    secondRail := route.route
    firstRail_isPath := pieces.splice.isPath
    secondRail_isPath := route.route_isPath
    firstRail_support_disjoint_secondRail := by
      have hnewFuture :
          (newWalk.dropUntil face pieces.splice.newOccurrence).tail.support.Disjoint
            newCompanion.support := by
        rw [List.disjoint_left]
        intro current hcurrent hcompanion
        apply (List.disjoint_left.mp pieces.new_disjoint ?_) hcompanion
        apply newWalk.support_dropUntil_subset_support pieces.splice.newOccurrence
        let suffix := newWalk.dropUntil face pieces.splice.newOccurrence
        have hsuffixNotNil : ¬suffix.Nil := by
          intro hnil
          exact pieces.splice.newFinish_ne hnil.eq
        rw [suffix.support_tail_of_not_nil hsuffixNotNil] at hcurrent
        exact List.mem_of_mem_tail hcurrent
      apply pieces.splice.support_disjoint_sharp route.route
      · exact route.support_disjoint_of_parts
          (oldWalk.takeUntil face pieces.splice.oldOccurrence).dropLast
          holdMiddle holdFuture
      · simpa [WalkAvoidsSecondBandFutureSpliceCenters,
          secondBandFutureSpliceCenters] using hcenters
      · exact route.support_disjoint_of_parts
          (newWalk.dropUntil face pieces.splice.newOccurrence).tail
          hnewMiddle hnewFuture
  }

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
