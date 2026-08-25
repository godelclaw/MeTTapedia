import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendDoubleCross
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailCenterEdgeReceipt

/-!
# L1: bridge the unmatched rail through a literal Cell-3 centre

Exactly one cross-track collision already supplies one crossed reroute.  The
other two seam flanks can be joined through the displayed Cell-3 centre.  This
file proves that construction when the crossed reroute avoids the unmatched
old rail, the unmatched continuation tail, and the centre itself.  If one of
those finite support tests fails, the classifier retains the actual offending
face.

This is a constructive refinement of the lone-cross residue.  It does not
assert that the three remaining support tests always pass, iterate an
arbitrary corridor, attach either annular end cap, or close Fable flag L1.
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

namespace Instance.SelectedLocalLayerFormation

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

private theorem start_not_mem_support_tail_of_isPath
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath) :
    start ∉ walk.support.tail := by
  have hnodup := hpath.support_nodup
  rw [← walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

private theorem support_dropUntil_subset_tail_of_mem_tail_of_isPath
    {F : Type*} [DecidableEq F] {H : SimpleGraph F}
    {start finish face : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath)
    (hface : face ∈ walk.support.tail) :
    (walk.dropUntil face (List.mem_of_mem_tail hface)).support ⊆
      walk.support.tail := by
  cases walk with
  | nil => simp at hface
  | @cons next _ _ hadj tail =>
      have hne : start ≠ face := by
        intro heq
        subst face
        have hnodup := hpath.support_nodup
        simp only [SimpleGraph.Walk.support_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1 hface
      simpa [SimpleGraph.Walk.dropUntil, hne] using
        tail.support_dropUntil_subset_support hface

namespace SelectedSourceLocalRailAssembly

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

/-- The literal two-edge walk from the after-flank to the before-flank through
the left Cell-3 centre. -/
private def leftCenterBridge : SelectedDualGraph (web := web).Walk
    (selectedPlacementSideFace leftPlacement successor.frame.leftAfter)
    (selectedPlacementSideFace leftPlacement successor.frame.leftBefore) :=
  by
    let _ := left
    exact selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
      successor.frame.leftBefore

/-- The first-to-second reroute constructed at a collision cannot return to
the old first rail's seam endpoint. -/
private theorem firstToSecondReroute_before_not_mem
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail) :
    selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∉
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support := by
  intro hface
  let raw :=
    (left.paths.firstRail.takeUntil collision.face collision.mem_old).append
      (successor.secondContinuation.dropUntil collision.face
        (List.mem_of_mem_tail collision.mem_new))
  have hraw : selectedPlacementSideFace leftPlacement
      successor.frame.leftBefore ∈ raw.support := by
    exact raw.support_bypass_subset_support (by
      simpa [SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute,
        raw] using hface)
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hold | hnew
  · let actual :
        SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
          successor left := {
      face := collision.face
      collision := Or.inl ⟨collision.mem_old, collision.mem_new⟩
    }
    exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      left.paths.firstRail_isPath
      collision.mem_old actual.toAdjacentDualTriangle.third_ne_before.symm hold
  · have hnewTail : selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore ∈ successor.secondContinuation.support.tail :=
      support_dropUntil_subset_tail_of_mem_tail_of_isPath
        successor.secondContinuation successor.secondContinuation_isPath
        collision.mem_new (List.mem_of_mem_tail hnew)
    have hfirstStart : selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore ∈ successor.firstContinuation.support := by
      rw [successor.firstContinuation_support,
        successor.frame.leftBeforeFace_eq_rightAfterFace]
      exact successor.rightRails.paths.firstRail.start_mem_support
    exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        hfirstStart) (List.mem_of_mem_tail hnewTail)

/-- The same reroute cannot return to the other seam flank. -/
private theorem firstToSecondReroute_after_not_mem
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail) :
    selectedPlacementSideFace leftPlacement successor.frame.leftAfter ∉
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support := by
  intro hface
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset _ hface with hold | hnew
  · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hold) left.paths.secondRail.end_mem_support
  · exact start_not_mem_support_tail_of_isPath successor.secondContinuation
      successor.secondContinuation_isPath (by
        simpa using hnew)

/-- A lone first-to-second collision is repaired by sending the unmatched
second-to-first rail through the left Cell-3 centre, provided the crossed
reroute avoids the three displayed pieces of that bridge. -/
noncomputable def appendSingleFirstSecondViaLeftCenter
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
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
    SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore) := by
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  let bridge := leftCenterBridge (successor := successor) (left := left)
  let rawSecond :=
    (left.paths.secondRail.append bridge).append successor.firstContinuation
  refine {
    firstRail := reroute.route
    secondRail := rawSecond.bypass
    firstRail_isPath := reroute.route_isPath
    secondRail_isPath := rawSecond.bypass_isPath
    firstRail_support_disjoint_secondRail := ?_
  }
  rw [List.disjoint_left]
  intro face hfirst hsecond
  have hsecondRaw := rawSecond.support_bypass_subset_support hsecond
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append] at hsecondRaw
  rcases List.mem_append.mp hsecondRaw with hleftBridge | hright
  · rcases List.mem_append.mp hleftBridge with hold | hbridge
    · exact (List.disjoint_left.mp holdSecond hfirst) hold
    · simp [bridge, leftCenterBridge, selectedPlacementCenterBridge] at hbridge
      rcases hbridge with hcenterFace | hbefore
      · exact hcenter (hcenterFace ▸ hfirst)
      · exact firstToSecondReroute_before_not_mem collision (hbefore ▸ hfirst)
  · exact (List.disjoint_left.mp hnewFirst hfirst) hright

/-- Both supports of the immediate first-to-second centre-bridge repair stay
inside the previous centre, the two old local rails, and the two successor
local rails.  This is the constructor-level provenance needed by the later
two-centre-window invariant. -/
theorem appendSingleFirstSecondViaLeftCenter_supportContained
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
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
    let assembly := appendSingleFirstSecondViaLeftCenter collision
      holdSecond hnewFirst hcenter
    (∀ face ∈ assembly.firstRail.support,
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face ∈ left.paths.firstRail.support ∨
        face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support ∨
        face ∈ successor.secondContinuation.support) ∧
      (∀ face ∈ assembly.secondRail.support,
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face ∈ left.paths.firstRail.support ∨
        face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support ∨
        face ∈ successor.secondContinuation.support) := by
  dsimp only
  constructor
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new
    have hparts := reroute.route_support_subset face hface
    rcases hparts with hold | hnew
    · exact Or.inr (Or.inl hold)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_of_mem_tail hnew))))
  · intro face hface
    let bridge := leftCenterBridge (successor := successor) (left := left)
    let rawSecond :=
      (left.paths.secondRail.append bridge).append successor.firstContinuation
    have hraw : face ∈ rawSecond.support := by
      exact rawSecond.support_bypass_subset_support (by
        simpa [appendSingleFirstSecondViaLeftCenter, rawSecond, bridge] using hface)
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hleftBridge | hright
    · rcases List.mem_append.mp hleftBridge with hold | hbridge
      · exact Or.inr (Or.inr (Or.inl hold))
      · simp [bridge, leftCenterBridge, selectedPlacementCenterBridge] at hbridge
        rcases hbridge with hcenterFace | hbefore
        · exact Or.inl hcenterFace
        · exact Or.inr (Or.inl (hbefore ▸ left.paths.firstRail.end_mem_support))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_of_mem_tail hright))))

/-- Track-sensitive form of the immediate first-to-second centre bridge.
The crossed output uses old first/new second; the unmatched output uses old
second/new first.  Only the two seam flanks and the displayed centre may be
introduced by the connector. -/
theorem appendSingleFirstSecondViaLeftCenter_trackProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
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
    let assembly := appendSingleFirstSecondViaLeftCenter collision
      holdSecond hnewFirst hcenter
    (∀ face ∈ assembly.firstRail.support,
        face ∈ left.paths.firstRail.support ∨
        face ∈ successor.secondContinuation.support ∨
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftAfter) ∧
      ∀ face ∈ assembly.secondRail.support,
        face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support ∨
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftAfter := by
  dsimp only
  constructor
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new
    rcases reroute.route_support_subset face hface with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))
  · intro face hface
    let bridge := leftCenterBridge (successor := successor) (left := left)
    let rawSecond :=
      (left.paths.secondRail.append bridge).append successor.firstContinuation
    have hraw : face ∈ rawSecond.support := by
      exact rawSecond.support_bypass_subset_support (by
        simpa [appendSingleFirstSecondViaLeftCenter, rawSecond, bridge] using hface)
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hleftBridge | hright
    · rcases List.mem_append.mp hleftBridge with hold | hbridge
      · exact Or.inl hold
      · have hbridge' : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          face = selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore := by
          simpa only [bridge, leftCenterBridge, selectedPlacementCenterBridge,
            SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] using hbridge
        rcases hbridge' with hcenterFace | hbefore
        · exact Or.inr (Or.inr (Or.inl hcenterFace))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hbefore)))
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hright))

/-- The second-to-first reroute cannot return to the old first seam flank. -/
private theorem secondToFirstReroute_before_not_mem
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail) :
    selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∉
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support := by
  intro hface
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset _ hface with hold | hnew
  · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      left.paths.firstRail.end_mem_support) hold
  · exact start_not_mem_support_tail_of_isPath successor.firstContinuation
      successor.firstContinuation_isPath (by simpa using hnew)

/-- The second-to-first reroute cannot return to the old second seam flank. -/
private theorem secondToFirstReroute_after_not_mem
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail) :
    selectedPlacementSideFace leftPlacement successor.frame.leftAfter ∉
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support := by
  intro hface
  let raw :=
    (left.paths.secondRail.takeUntil collision.face collision.mem_old).append
      (successor.firstContinuation.dropUntil collision.face
        (List.mem_of_mem_tail collision.mem_new))
  have hraw : selectedPlacementSideFace leftPlacement
      successor.frame.leftAfter ∈ raw.support := by
    exact raw.support_bypass_subset_support (by
      simpa [SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute,
        raw] using hface)
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hold | hnew
  · let actual :
        SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
          successor left := {
      face := collision.face
      collision := Or.inr ⟨collision.mem_old, collision.mem_new⟩
    }
    exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      left.paths.secondRail_isPath collision.mem_old
      actual.toAdjacentDualTriangle.third_ne_after.symm hold
  · have hnewTail : selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter ∈ successor.firstContinuation.support.tail :=
      support_dropUntil_subset_tail_of_mem_tail_of_isPath
        successor.firstContinuation successor.firstContinuation_isPath
        collision.mem_new (List.mem_of_mem_tail hnew)
    have hsecondStart : selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter ∈ successor.secondContinuation.support := by
      rw [successor.secondContinuation_support,
        successor.frame.leftAfterFace_eq_rightBeforeFace]
      exact successor.rightRails.paths.secondRail.start_mem_support
    exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation.symm
        hsecondStart) (List.mem_of_mem_tail hnewTail)

/-- Symmetric centre-bridge repair for one second-to-first collision. -/
noncomputable def appendSingleSecondFirstViaLeftCenter
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
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
    SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore) := by
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  let bridge := (leftCenterBridge (successor := successor) (left := left)).reverse
  let rawFirst :=
    (left.paths.firstRail.append bridge).append successor.secondContinuation
  refine {
    firstRail := rawFirst.bypass
    secondRail := reroute.route
    firstRail_isPath := rawFirst.bypass_isPath
    secondRail_isPath := reroute.route_isPath
    firstRail_support_disjoint_secondRail := ?_
  }
  rw [List.disjoint_left]
  intro face hfirst hsecond
  have hfirstRaw := rawFirst.support_bypass_subset_support hfirst
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append] at hfirstRaw
  rcases List.mem_append.mp hfirstRaw with hleftBridge | hright
  · rcases List.mem_append.mp hleftBridge with hold | hbridge
    · exact (List.disjoint_left.mp holdFirst hsecond) hold
    · simp [bridge, leftCenterBridge, selectedPlacementCenterBridge] at hbridge
      rcases hbridge with hcenterFace | hafter
      · exact hcenter (hcenterFace ▸ hsecond)
      · exact secondToFirstReroute_after_not_mem collision (hafter ▸ hsecond)
  · exact (List.disjoint_left.mp hnewSecond hsecond) hright

/-- Symmetric constructor-level provenance for the immediate
second-to-first centre-bridge repair. -/
theorem appendSingleSecondFirstViaLeftCenter_supportContained
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
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
    let assembly := appendSingleSecondFirstViaLeftCenter collision
      holdFirst hnewSecond hcenter
    (∀ face ∈ assembly.firstRail.support,
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face ∈ left.paths.firstRail.support ∨
        face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support ∨
        face ∈ successor.secondContinuation.support) ∧
      (∀ face ∈ assembly.secondRail.support,
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face ∈ left.paths.firstRail.support ∨
        face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support ∨
        face ∈ successor.secondContinuation.support) := by
  dsimp only
  constructor
  · intro face hface
    let bridge := (leftCenterBridge (successor := successor) (left := left)).reverse
    let rawFirst :=
      (left.paths.firstRail.append bridge).append successor.secondContinuation
    have hraw : face ∈ rawFirst.support := by
      exact rawFirst.support_bypass_subset_support (by
        simpa [appendSingleSecondFirstViaLeftCenter, rawFirst, bridge] using hface)
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hleftBridge | hright
    · rcases List.mem_append.mp hleftBridge with hold | hbridge
      · exact Or.inr (Or.inl hold)
      · simp [bridge, leftCenterBridge, selectedPlacementCenterBridge] at hbridge
        rcases hbridge with hcenterFace | hafter
        · exact Or.inl hcenterFace
        · exact Or.inr (Or.inr (Or.inl
            (hafter ▸ left.paths.secondRail.end_mem_support)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_of_mem_tail hright))))
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new
    have hparts := reroute.route_support_subset face hface
    rcases hparts with hold | hnew
    · exact Or.inr (Or.inr (Or.inl hold))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_of_mem_tail hnew))))

/-- Symmetric track-sensitive form of the immediate centre bridge. -/
theorem appendSingleSecondFirstViaLeftCenter_trackProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
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
    let assembly := appendSingleSecondFirstViaLeftCenter collision
      holdFirst hnewSecond hcenter
    (∀ face ∈ assembly.firstRail.support,
        face ∈ left.paths.firstRail.support ∨
        face ∈ successor.secondContinuation.support ∨
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftAfter) ∧
      ∀ face ∈ assembly.secondRail.support,
        face ∈ left.paths.secondRail.support ∨
        face ∈ successor.firstContinuation.support ∨
        face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∨
        face = selectedPlacementSideFace leftPlacement successor.frame.leftAfter := by
  dsimp only
  constructor
  · intro face hface
    let bridge := (leftCenterBridge (successor := successor) (left := left)).reverse
    let rawFirst :=
      (left.paths.firstRail.append bridge).append successor.secondContinuation
    have hraw : face ∈ rawFirst.support := by
      exact rawFirst.support_bypass_subset_support (by
        simpa [appendSingleSecondFirstViaLeftCenter, rawFirst, bridge] using hface)
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hleftBridge | hright
    · rcases List.mem_append.mp hleftBridge with hold | hbridge
      · exact Or.inl hold
      · simp [bridge, leftCenterBridge, selectedPlacementCenterBridge] at hbridge
        rcases hbridge with hcenterFace | hafter
        · exact Or.inr (Or.inr (Or.inl hcenterFace))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hafter)))
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hright))
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new
    rcases reroute.route_support_subset face hface with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))

private def firstRerouteMeetsOldSecond_to_sameSecondCollision
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (witness : SelectedRailSupportCollision (web := web)
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support
      left.paths.secondRail.support) :
    SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.secondContinuation.support.tail := by
  classical
  apply Classical.choice
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset witness.face witness.mem_old with
    hold | hnew
  · exact False.elim ((List.disjoint_left.mp
      left.firstRail_support_disjoint_secondRail hold) witness.mem_new)
  · exact ⟨⟨witness.face, witness.mem_new, hnew⟩⟩

private def firstRerouteMeetsNewFirst_to_sameFirstCollision
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (witness : SelectedRailSupportCollision (web := web)
      (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support
      successor.firstContinuation.support.tail) :
    SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.firstContinuation.support.tail := by
  classical
  apply Classical.choice
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset witness.face witness.mem_old with
    hold | hnew
  · exact ⟨⟨witness.face, hold, witness.mem_new⟩⟩
  · exact False.elim ((List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        (List.mem_of_mem_tail witness.mem_new)) (List.mem_of_mem_tail hnew))

private theorem firstReroute_center_mem_implies_newSecond
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        (SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
          (successor := successor) (left := left) collision.face
          collision.mem_old collision.mem_new).route.support) :
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt leftInterior.center) ∈
      successor.secondContinuation.support.tail := by
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset _ hcenter with hold | hnew
  · exact False.elim ((left.paths.firstRail_support_adjacent_center _ hold).ne rfl)
  · exact hnew

private def secondRerouteMeetsOldFirst_to_sameFirstCollision
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (witness : SelectedRailSupportCollision (web := web)
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support
      left.paths.firstRail.support) :
    SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.firstContinuation.support.tail := by
  classical
  apply Classical.choice
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset witness.face witness.mem_old with
    hold | hnew
  · exact False.elim ((List.disjoint_left.mp
      left.firstRail_support_disjoint_secondRail witness.mem_new) hold)
  · exact ⟨⟨witness.face, witness.mem_new, hnew⟩⟩

private def secondRerouteMeetsNewSecond_to_sameSecondCollision
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (witness : SelectedRailSupportCollision (web := web)
      (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) collision.face
        collision.mem_old collision.mem_new).route.support
      successor.secondContinuation.support.tail) :
    SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.secondContinuation.support.tail := by
  classical
  apply Classical.choice
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset witness.face witness.mem_old with
    hold | hnew
  · exact ⟨⟨witness.face, hold, witness.mem_new⟩⟩
  · exact False.elim ((List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        (List.mem_of_mem_tail hnew)) (List.mem_of_mem_tail witness.mem_new))

private theorem secondReroute_center_mem_implies_newFirst
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        (SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
          (successor := successor) (left := left) collision.face
          collision.mem_old collision.mem_new).route.support) :
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt leftInterior.center) ∈
      successor.firstContinuation.support.tail := by
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  rcases reroute.route_support_subset _ hcenter with hold | hnew
  · exact False.elim ((left.paths.secondRail_support_adjacent_center _ hold).ne rfl)
  · exact hnew

/-- Exact residual data when a first-to-second collision cannot yet be closed
by the left-centre bridge. -/
inductive SingleFirstSecondCenterBridgeOutcome
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail) : Type (u + 1)
  | assembly
      (value : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
  | meetsOldSecond
      (witness : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support
        successor.secondContinuation.support.tail)
  | meetsNewFirst
      (witness : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support
        successor.firstContinuation.support.tail)
  | containsLeftCenter
      (witness :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∈
          successor.secondContinuation.support.tail)

/-- Test the three remaining finite conditions for the first-to-second centre
bridge and retain the first exact failure. -/
noncomputable def classifySingleFirstSecondCenterBridge
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail) :
    SingleFirstSecondCenterBridgeOutcome collision := by
  classical
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  by_cases holdSecond : reroute.route.support.Disjoint
      left.paths.secondRail.support
  · by_cases hnewFirst : reroute.route.support.Disjoint
        successor.firstContinuation.support.tail
    · by_cases hcenter :
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center) ∈ reroute.route.support
      · exact .containsLeftCenter
          (firstReroute_center_mem_implies_newSecond collision hcenter)
      · exact .assembly (appendSingleFirstSecondViaLeftCenter collision
          holdSecond hnewFirst hcenter)
    · exact .meetsNewFirst
        (firstRerouteMeetsNewFirst_to_sameFirstCollision collision
          (SelectedRailSupportCollision.of_not_disjoint hnewFirst))
  · exact .meetsOldSecond
      (firstRerouteMeetsOldSecond_to_sameSecondCollision collision
        (SelectedRailSupportCollision.of_not_disjoint holdSecond))

/-- Symmetric exact outcome for the second-to-first centre bridge. -/
inductive SingleSecondFirstCenterBridgeOutcome
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail) : Type (u + 1)
  | assembly
      (value : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
  | meetsOldFirst
      (witness : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support
        successor.firstContinuation.support.tail)
  | meetsNewSecond
      (witness : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support
        successor.secondContinuation.support.tail)
  | containsLeftCenter
      (witness :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∈
          successor.firstContinuation.support.tail)

/-- Test the symmetric three centre-bridge conditions. -/
noncomputable def classifySingleSecondFirstCenterBridge
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail) :
    SingleSecondFirstCenterBridgeOutcome collision := by
  classical
  let reroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) collision.face
      collision.mem_old collision.mem_new
  by_cases holdFirst : reroute.route.support.Disjoint
      left.paths.firstRail.support
  · by_cases hnewSecond : reroute.route.support.Disjoint
        successor.secondContinuation.support.tail
    · by_cases hcenter :
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center) ∈ reroute.route.support
      · exact .containsLeftCenter
          (secondReroute_center_mem_implies_newFirst collision hcenter)
      · exact .assembly (appendSingleSecondFirstViaLeftCenter collision
          holdFirst hnewSecond hcenter)
    · exact .meetsNewSecond
        (secondRerouteMeetsNewSecond_to_sameSecondCollision collision
          (SelectedRailSupportCollision.of_not_disjoint hnewSecond))
  · exact .meetsOldFirst
      (secondRerouteMeetsOldFirst_to_sameFirstCollision collision
        (SelectedRailSupportCollision.of_not_disjoint holdFirst))

/-- The adjacent append after both crossed-collision repairs and the literal
centre bridge have been applied.  Every remaining case is now either a
same-track old/new revisit or the previous Cell-3 centre occurring in one
next-cell continuation. -/
inductive SelectedLocalRailAppendCenterResolvedOutcome
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
  | sameFirstCollision
      (collision : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support
        successor.firstContinuation.support.tail)
  | sameSecondCollision
      (collision : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support
        successor.secondContinuation.support.tail)
  | firstContinuationContainsLeftCenter
      (witness :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∈
          successor.firstContinuation.support.tail)
  | secondContinuationContainsLeftCenter
      (witness :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∈
          successor.secondContinuation.support.tail)

/-- **L1 centre-resolved adjacent classifier.** Every literal neighbouring
Cell-3 pair either constructs a straight/swapped separated assembly or returns
one of four exact lower-level residues.  Cross-track collisions themselves no
longer remain in the result. -/
noncomputable def classifyLocalSuccessorAppendCenterResolved
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    SelectedLocalRailAppendCenterResolvedOutcome successor left := by
  cases classifyLocalSuccessorAppendResolved successor left with
  | straight assembly => exact .straight assembly
  | swapped assembly => exact .swapped assembly
  | singleFirstSecond collision _ =>
      cases classifySingleFirstSecondCenterBridge collision with
      | assembly value => exact .swapped value
      | meetsOldSecond witness => exact .sameSecondCollision witness
      | meetsNewFirst witness => exact .sameFirstCollision witness
      | containsLeftCenter witness =>
          exact .secondContinuationContainsLeftCenter witness
  | singleSecondFirst collision _ =>
      cases classifySingleSecondFirstCenterBridge collision with
      | assembly value => exact .swapped value
      | meetsOldFirst witness => exact .sameFirstCollision witness
      | meetsNewSecond witness => exact .sameSecondCollision witness
      | containsLeftCenter witness =>
          exact .firstContinuationContainsLeftCenter witness

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
