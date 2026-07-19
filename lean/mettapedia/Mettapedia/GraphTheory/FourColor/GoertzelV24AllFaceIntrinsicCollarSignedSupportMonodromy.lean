import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarSupportCycleMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileSignedMonodromy

/-! Oriented crossing states for a collar discrepancy support cycle and its
remote facial-dual separator. -/

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- Distinct edge positions of a simple closed walk have distinct initial
vertices. -/
theorem IsCycle.dartAtEdgePosition_fst_injective
    {left : Vertex} {walk : Graph.Walk left left}
    (hcycle : walk.IsCycle) :
    Function.Injective
      (fun position : Fin walk.edges.length =>
        (walk.dartAtEdgePosition position).fst) := by
  intro first second heq
  have hnodup : walk.support.dropLast.Nodup :=
    hcycle.nodup_dropLast_support
  apply Fin.ext
  apply hnodup.getElem_inj_iff.mp
  rw [List.getElem_dropLast (by simpa using first.isLt),
    List.getElem_dropLast (by simpa using second.isLt)]
  simpa [SimpleGraph.Walk.dartAtEdgePosition,
    List.get_eq_getElem] using heq

/-- Distinct edge positions of a simple closed walk have distinct terminal
vertices. -/
theorem IsCycle.dartAtEdgePosition_snd_injective
    {left : Vertex} {walk : Graph.Walk left left}
    (hcycle : walk.IsCycle) :
    Function.Injective
      (fun position : Fin walk.edges.length =>
        (walk.dartAtEdgePosition position).snd) := by
  intro first second heq
  have hnodup : walk.support.tail.Nodup :=
    hcycle.support_nodup
  apply Fin.ext
  apply hnodup.getElem_inj_iff.mp
  rw [List.getElem_tail (by simpa using first.isLt),
    List.getElem_tail (by simpa using second.isLt)]
  simpa [SimpleGraph.Walk.dartAtEdgePosition,
    List.get_eq_getElem] using heq

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualCycleBond
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem prop_eq_of_ne_of_ne
    (P Q R : Prop) (hPQ : P ≠ Q) (hQR : Q ≠ R) : P = R := by
  apply propext
  tauto

namespace GoertzelV24ComplementaryRegionBoundaryOrder

/-- If a facial orbit has exactly two side-transition darts, then those
transitions have opposite current-side orientations. -/
theorem side_ne_of_two_transition_darts
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (side : V → Prop) (face : OrbitFace RS)
    (first second : RS.D)
    (hfirst : first ∈ orbitFaceSideTransitionDarts RS side face)
    (hsecond : second ∈ orbitFaceSideTransitionDarts RS side face)
    (hne : first ≠ second)
    (hcard : (orbitFaceSideTransitionDarts RS side face).card ≤ 2) :
    side (RS.vertOf first) ≠ side (RS.vertOf second) := by
  have hfirstData :=
    (mem_orbitFaceSideTransitionDarts_iff RS side face first).1 hfirst
  have hsecondData :=
    (mem_orbitFaceSideTransitionDarts_iff RS side face second).1 hsecond
  have hpairSubset : ({first, second} : Finset RS.D) ⊆
      orbitFaceSideTransitionDarts RS side face := by
    intro dart hdart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
    rcases hdart with rfl | rfl
    · exact hfirst
    · exact hsecond
  have hpairCard : ({first, second} : Finset RS.D).card = 2 :=
    Finset.card_pair hne
  have htransitionCard :
      (orbitFaceSideTransitionDarts RS side face).card = 2 := by
    have hlower := Finset.card_le_card hpairSubset
    rw [hpairCard] at hlower
    omega
  have hfaceTransitionCard :
      (faceSideTransitionDarts RS side first).card = 2 := by
    rw [← orbitFaceSideTransitionDarts_dartOrbitFace]
    rw [hfirstData.1]
    exact htransitionCard
  have hexitCard : (faceSideExitDarts RS side first).card = 1 := by
    have htwice :=
      card_faceSideTransitionDarts_eq_twice_exitDarts RS side first
    rw [hfaceTransitionCard] at htwice
    omega
  have hentryCard : (faceSideEntryDarts RS side first).card = 1 := by
    rw [← card_faceSideExitDarts_eq_card_faceSideEntryDarts]
    exact hexitCard
  have hfirstOrbit : first ∈ RS.faceOrbit first := by
    rw [RS.mem_faceOrbit]
  have hsecondOrbit : second ∈ RS.faceOrbit first := by
    rw [RS.mem_faceOrbit]
    have hquotient : dartOrbitFace RS first = dartOrbitFace RS second :=
      hfirstData.1.trans hsecondData.1.symm
    change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) first =
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) second at hquotient
    rw [Quotient.eq] at hquotient
    exact hquotient
  intro hsides
  by_cases hfirstSide : side (RS.vertOf first)
  · have hsecondSide : side (RS.vertOf second) := by
      rw [← hsides]
      exact hfirstSide
    have hfirstNext : ¬ side (RS.vertOf (RS.phi first)) := by
      intro hnext
      apply hfirstData.2
      exact propext ⟨fun _ => hnext, fun _ => hfirstSide⟩
    have hsecondNext : ¬ side (RS.vertOf (RS.phi second)) := by
      intro hnext
      apply hsecondData.2
      exact propext ⟨fun _ => hnext, fun _ => hsecondSide⟩
    have hfirstExit : first ∈ faceSideExitDarts RS side first := by
      rw [faceSideExitDarts, Finset.mem_sdiff]
      refine ⟨(mem_faceSideCurrentDarts_iff RS side first first).2
        ⟨hfirstOrbit, hfirstSide⟩, ?_⟩
      intro hnext
      exact hfirstNext
        ((mem_faceSideNextDarts_iff RS side first first).1 hnext).2
    have hsecondExit : second ∈ faceSideExitDarts RS side first := by
      rw [faceSideExitDarts, Finset.mem_sdiff]
      refine ⟨(mem_faceSideCurrentDarts_iff RS side first second).2
        ⟨hsecondOrbit, hsecondSide⟩, ?_⟩
      intro hnext
      exact hsecondNext
        ((mem_faceSideNextDarts_iff RS side first second).1 hnext).2
    have hlower : 2 ≤ (faceSideExitDarts RS side first).card := by
      have hsubset : ({first, second} : Finset RS.D) ⊆
          faceSideExitDarts RS side first := by
        intro dart hdart
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
        rcases hdart with rfl | rfl
        · exact hfirstExit
        · exact hsecondExit
      rw [← hpairCard]
      exact Finset.card_le_card hsubset
    omega
  · have hsecondSide : ¬ side (RS.vertOf second) := by
      intro hsecond
      apply hfirstSide
      rw [hsides]
      exact hsecond
    have hfirstNext : side (RS.vertOf (RS.phi first)) := by
      by_contra hnext
      apply hfirstData.2
      exact propext ⟨fun h => (hfirstSide h).elim,
        fun h => (hnext h).elim⟩
    have hsecondNext : side (RS.vertOf (RS.phi second)) := by
      by_contra hnext
      apply hsecondData.2
      exact propext ⟨fun h => (hsecondSide h).elim,
        fun h => (hnext h).elim⟩
    have hfirstEntry : first ∈ faceSideEntryDarts RS side first := by
      rw [faceSideEntryDarts, Finset.mem_sdiff]
      refine ⟨(mem_faceSideNextDarts_iff RS side first first).2
        ⟨hfirstOrbit, hfirstNext⟩, ?_⟩
      intro hcurrent
      exact hfirstSide
        ((mem_faceSideCurrentDarts_iff RS side first first).1 hcurrent).2
    have hsecondEntry : second ∈ faceSideEntryDarts RS side first := by
      rw [faceSideEntryDarts, Finset.mem_sdiff]
      refine ⟨(mem_faceSideNextDarts_iff RS side first second).2
        ⟨hsecondOrbit, hsecondNext⟩, ?_⟩
      intro hcurrent
      exact hsecondSide
        ((mem_faceSideCurrentDarts_iff RS side first second).1 hcurrent).2
    have hlower : 2 ≤ (faceSideEntryDarts RS side first).card := by
      have hsubset : ({first, second} : Finset RS.D) ⊆
          faceSideEntryDarts RS side first := by
        intro dart hdart
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
        rcases hdart with rfl | rfl
        · exact hfirstEntry
        · exact hsecondEntry
      rw [← hpairCard]
      exact Finset.card_le_card hsubset
    omega

end GoertzelV24ComplementaryRegionBoundaryOrder

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open RotationOrderedFusionEscapeColorState

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The primal edge crossed at a remote-cycle step lies on that step's
left quotient face. -/
theorem crossingAt_mem_leftFace
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    cycle.crossingAt step ∈ orbitFaceBoundary
      graphData.toRotationSystem (cycle.walk.getVert step).1 := by
  simpa [crossingAt] using
    (dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step)

/-- Each indexed crossing has an oriented graph dart on the left face of
the remote traversal. -/
theorem exists_leftFaceDartAt
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    ∃ dart : G.Dart,
      dart ∈ orbitFaceDarts graphData.toRotationSystem
          (cycle.walk.getVert step).1 ∧
        graphData.toRotationSystem.edgeOf dart = cycle.crossingAt step :=
  (mem_orbitFaceBoundary_iff graphData.toRotationSystem
    (cycle.walk.getVert step).1 (cycle.crossingAt step)).1
      (cycle.crossingAt_mem_leftFace step)

/-- The canonical left-face orientation of an indexed remote crossing. -/
def leftFaceDartAt
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) : G.Dart :=
  Classical.choose (cycle.exists_leftFaceDartAt step)

theorem leftFaceDartAt_mem_face
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    cycle.leftFaceDartAt step ∈
      orbitFaceDarts graphData.toRotationSystem
        (cycle.walk.getVert step).1 :=
  (Classical.choose_spec (cycle.exists_leftFaceDartAt step)).1

@[simp] theorem leftFaceDartAt_edgeOf
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    graphData.toRotationSystem.edgeOf (cycle.leftFaceDartAt step) =
      cycle.crossingAt step :=
  (Classical.choose_spec (cycle.exists_leftFaceDartAt step)).2

/-- Along an exact primal boundary, consecutive left-face crossing darts
of the remote dual cycle have the same current-side orientation. -/
theorem leftFaceDartAt_side_coherent_of_boundary_eq
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (side : V → Prop)
    (hboundary : crossingEdgeFinset G side = cycle.crossingEdges)
    (step : Fin cycle.walk.length) :
    side (cycle.leftFaceDartAt step).fst ↔
      side (cycle.leftFaceDartAt
        (finRotate cycle.walk.length step)).fst := by
  let RS := graphData.toRotationSystem
  let next := finRotate cycle.walk.length step
  let first := cycle.leftFaceDartAt step
  let second := cycle.leftFaceDartAt next
  let sharedFace := (cycle.walk.getVert (step.val + 1)).1
  have hfirstFace : dartOrbitFace RS first =
      (cycle.walk.getVert step).1 :=
    (mem_orbitFaceDarts_iff RS (cycle.walk.getVert step).1 first).1
      (cycle.leftFaceDartAt_mem_face step)
  have hsecondFace : dartOrbitFace RS second =
      (cycle.walk.getVert next).1 :=
    (mem_orbitFaceDarts_iff RS (cycle.walk.getVert next).1 second).1
      (cycle.leftFaceDartAt_mem_face next)
  have hcurrentRightNe : (cycle.walk.getVert step).1 ≠ sharedFace := by
    have hadj := cycle.walk.adj_getVert_succ step.isLt
    intro heq
    exact hadj.ne (Subtype.ext heq)
  have hfirstEdgeRight : RS.edgeOf first ∈
      orbitFaceBoundary RS sharedFace := by
    rw [cycle.leftFaceDartAt_edgeOf]
    exact dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step
  have halphaFirstFace : dartOrbitFace RS (RS.alpha first) =
      sharedFace := by
    apply dartOrbitFace_alpha_eq_of_mem_other_face RS
      minimal.facesTwoSided first sharedFace hfirstEdgeRight
    exact hfirstFace.trans_ne hcurrentRightNe
  have hnextFace : (cycle.walk.getVert next).1 = sharedFace := by
    exact congrArg Subtype.val
      (getVert_succ_eq_getVert_finRotate cycle.walk cycle.isCycle step).symm
  have hsecondSharedFace : dartOrbitFace RS second = sharedFace :=
    hsecondFace.trans hnextFace
  have hcrossingMem (position : Fin cycle.walk.length) :
      cycle.crossingAt position ∈ cycle.crossingEdges := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk (cycle.crossingAt position)).2 ⟨position, rfl⟩
  have hfirstBoundary : RS.edgeOf (RS.alpha first) ∈
      crossingEdgeFinset G side := by
    rw [RS.edge_alpha, cycle.leftFaceDartAt_edgeOf, hboundary]
    exact hcrossingMem step
  have hsecondBoundary : RS.edgeOf second ∈
      crossingEdgeFinset G side := by
    rw [cycle.leftFaceDartAt_edgeOf, hboundary]
    exact hcrossingMem next
  have halphaFirstTransition : RS.alpha first ∈
      orbitFaceSideTransitionDarts RS side sharedFace := by
    apply (mem_orbitFaceSideTransitionDarts_iff RS side sharedFace
      (RS.alpha first)).2
    refine ⟨halphaFirstFace, ?_⟩
    apply (edgeCrosses_toRotationSystem_edgeOf_iff_transition
      graphData side (RS.alpha first)).1
    exact (mem_crossingEdgeFinset_iff side _).1 hfirstBoundary
  have hsecondTransition : second ∈
      orbitFaceSideTransitionDarts RS side sharedFace := by
    apply (mem_orbitFaceSideTransitionDarts_iff RS side sharedFace
      second).2
    refine ⟨hsecondSharedFace, ?_⟩
    apply (edgeCrosses_toRotationSystem_edgeOf_iff_transition
      graphData side second).1
    exact (mem_crossingEdgeFinset_iff side _).1 hsecondBoundary
  have hnextNe : next ≠ step := by
    intro heq
    apply cycle.sourcePosition_finRotate_ne step
    exact congrArg cycle.sourcePosition heq
  have hcrossingNe : cycle.crossingAt step ≠ cycle.crossingAt next := by
    intro hedges
    apply hnextNe
    apply dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS)
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk cycle.isCycle
    simpa [crossingAt] using hedges.symm
  have hdartsNe : RS.alpha first ≠ second := by
    intro hdarts
    apply hcrossingNe
    have hedges := congrArg RS.edgeOf hdarts
    calc
      cycle.crossingAt step = RS.edgeOf first :=
        (cycle.leftFaceDartAt_edgeOf step).symm
      _ = RS.edgeOf (RS.alpha first) := (RS.edge_alpha first).symm
      _ = RS.edgeOf second := hedges
      _ = cycle.crossingAt next := cycle.leftFaceDartAt_edgeOf next
  have htransitionCardLe :
      (orbitFaceSideTransitionDarts RS side sharedFace).card ≤ 2 := by
    have hinjective : Set.InjOn RS.edgeOf
        (orbitFaceSideTransitionDarts RS side sharedFace) := by
      intro left hleft right hright hedges
      apply edgeOf_injOn_orbitFaceDarts_of_twoSided
        RS minimal.facesTwoSided sharedFace
      · exact (mem_orbitFaceDarts_iff RS sharedFace left).2
          ((mem_orbitFaceSideTransitionDarts_iff RS side sharedFace
            left).1 hleft).1
      · exact (mem_orbitFaceDarts_iff RS sharedFace right).2
          ((mem_orbitFaceSideTransitionDarts_iff RS side sharedFace
            right).1 hright).1
      · exact hedges
    calc
      (orbitFaceSideTransitionDarts RS side sharedFace).card =
          ((orbitFaceSideTransitionDarts RS side sharedFace).image
            RS.edgeOf).card :=
        (Finset.card_image_iff.mpr hinjective).symm
      _ = (crossingEdgeFinset G side ∩
          orbitFaceBoundary RS sharedFace).card := by
        rw [image_edgeOf_orbitFaceSideTransitionDarts_eq_crossing_inter_boundary]
      _ = (cycle.crossingEdges ∩
          orbitFaceBoundary RS sharedFace).card := by rw [hboundary]
      _ ≤ 2 :=
        card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
          graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
          cycle.walk cycle.isCycle sharedFace
  have hoppositeSides :
      side (RS.vertOf (RS.alpha first)) ≠ side (RS.vertOf second) :=
    side_ne_of_two_transition_darts RS side sharedFace
      (RS.alpha first) second halphaFirstTransition hsecondTransition
      hdartsNe htransitionCardLe
  have hfirstBoundaryOriginal : RS.edgeOf first ∈
      crossingEdgeFinset G side := by
    simpa [RS.edge_alpha] using hfirstBoundary
  have hfirstOpposite :
      side (RS.vertOf first) ≠ side (RS.vertOf (RS.alpha first)) := by
    have htransition :=
      (edgeCrosses_toRotationSystem_edgeOf_iff_transition
        graphData side first).1
        ((mem_crossingEdgeFinset_iff side _).1 hfirstBoundaryOriginal)
    rw [RS.vert_phi_eq_vert_alpha] at htransition
    exact htransition
  exact Iff.of_eq
    (prop_eq_of_ne_of_ne
      (side (RS.vertOf first))
      (side (RS.vertOf (RS.alpha first)))
      (side (RS.vertOf second)) hfirstOpposite hoppositeSides)

/-- Exact primal-boundary orientation is coherent at every pair of remote
cycle steps. -/
theorem leftFaceDartAt_side_coherent_all_of_boundary_eq
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (side : V → Prop)
    (hboundary : crossingEdgeFinset G side = cycle.crossingEdges)
    (first second : Fin cycle.walk.length) :
    side (cycle.leftFaceDartAt first).fst ↔
      side (cycle.leftFaceDartAt second).fst := by
  have htwoLength : 2 ≤ cycle.walk.length :=
    le_trans (by omega) cycle.isCycle.three_le_length
  have hrotateNe (step : Fin cycle.walk.length) :
      finRotate cycle.walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hsameCycle :
      (finRotate cycle.walk.length).SameCycle first second :=
    (isCycle_finRotate_of_le htwoLength).sameCycle
      (hrotateNe first) (hrotateNe second)
  rcases hsameCycle.exists_nat_pow_eq with ⟨power, hpower⟩
  have hiterate : ∀ exponent : Nat,
      side (cycle.leftFaceDartAt first).fst ↔
        side (cycle.leftFaceDartAt
          (((finRotate cycle.walk.length) ^ exponent) first)).fst := by
    intro exponent
    induction exponent with
    | zero => simp
    | succ previous ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans
          (cycle.leftFaceDartAt_side_coherent_of_boundary_eq side hboundary _)
  have hiteratePower := hiterate power
  rw [hpower] at hiteratePower
  exact hiteratePower

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
  CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
    rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

namespace ScalarSupportCrossingState

variable (state : ScalarSupportCrossingState collar sourceEscape)

/-- The physical crossing value at a target-rooted support-order
position. -/
def targetRootedCrossingValue
    (position : Fin state.targetRootedSupportOrder.length) : Sym2 V :=
  state.targetRootedSupportOrder.get position

theorem targetRootedCrossingValue_mem_supportOrder
    (position : Fin state.targetRootedSupportOrder.length) :
    state.targetRootedCrossingValue position ∈
      state.targetRootedSupportOrder :=
  List.get_mem _ position

theorem targetRootedCrossingValue_mem_supportCycle
    (position : Fin state.targetRootedSupportOrder.length) :
    state.targetRootedCrossingValue position ∈ state.supportCycle.edges := by
  have hrooted := state.targetRootedCrossingValue_mem_supportOrder position
  have horiginal : state.targetRootedCrossingValue position ∈
      cycle.supportCrossingOrder state.supportCycle := by
    simpa [targetRootedSupportOrder] using hrooted
  exact (cycle.mem_supportCrossingOrder_iff state.supportCycle
    (state.targetRootedCrossingValue position)).1 horiginal |>.1

theorem targetRootedCrossingValue_mem_remote
    (position : Fin state.targetRootedSupportOrder.length) :
    state.targetRootedCrossingValue position ∈ cycle.crossingSym2Finset := by
  have hrooted := state.targetRootedCrossingValue_mem_supportOrder position
  have horiginal : state.targetRootedCrossingValue position ∈
      cycle.supportCrossingOrder state.supportCycle := by
    simpa [targetRootedSupportOrder] using hrooted
  exact (cycle.mem_supportCrossingOrder_iff state.supportCycle
    (state.targetRootedCrossingValue position)).1 horiginal |>.2

/-- The rooted crossing value regarded as an actual ambient graph edge. -/
def targetRootedCrossingEdge
    (position : Fin state.targetRootedSupportOrder.length) : G.edgeSet :=
  ⟨state.targetRootedCrossingValue position,
    state.supportCycle.edges_subset_edgeSet
      (state.targetRootedCrossingValue_mem_supportCycle position)⟩

@[simp] theorem targetRootedCrossingEdge_val
    (position : Fin state.targetRootedSupportOrder.length) :
    (state.targetRootedCrossingEdge position : Sym2 V) =
      state.targetRootedCrossingValue position :=
  rfl

theorem targetRootedCrossingEdge_mem_remote
    (position : Fin state.targetRootedSupportOrder.length) :
    state.targetRootedCrossingEdge position ∈ cycle.crossingEdges := by
  rcases Finset.mem_image.1
      (state.targetRootedCrossingValue_mem_remote position) with
    ⟨edge, hedge, heq⟩
  have hedges : state.targetRootedCrossingEdge position = edge := by
    apply Subtype.ext
    exact heq.symm
  simpa [hedges] using hedge

/-- The unique occurrence of a rooted crossing in the simple support
cycle's full edge list. -/
def supportEdgePosition
    (position : Fin state.targetRootedSupportOrder.length) :
    Fin state.supportCycle.edges.length :=
  (List.Nodup.getEquiv state.supportCycle.edges
    state.supportCycle_isCycle.edges_nodup).symm
      ⟨state.targetRootedCrossingValue position,
        state.targetRootedCrossingValue_mem_supportCycle position⟩

/-- Rooted crossing positions remain distinct when embedded into the full
support cycle. -/
theorem supportEdgePosition_injective :
    Function.Injective state.supportEdgePosition := by
  intro first second hpositions
  apply state.targetRootedSupportOrder_nodup.get_inj_iff.mp
  let equivalence := List.Nodup.getEquiv state.supportCycle.edges
    state.supportCycle_isCycle.edges_nodup
  have hsubtypes :
      (⟨state.targetRootedCrossingValue first,
          state.targetRootedCrossingValue_mem_supportCycle first⟩ :
        {edge // edge ∈ state.supportCycle.edges}) =
      ⟨state.targetRootedCrossingValue second,
          state.targetRootedCrossingValue_mem_supportCycle second⟩ := by
    apply equivalence.symm.injective
    exact hpositions
  exact congrArg Subtype.val hsubtypes

/-- The orientation in which the scalar support cycle traverses a rooted
crossing. -/
def supportDartAt
    (position : Fin state.targetRootedSupportOrder.length) : G.Dart :=
  state.supportCycle.dartAtEdgePosition
    (state.supportEdgePosition position)

@[simp] theorem supportDartAt_edge
    (position : Fin state.targetRootedSupportOrder.length) :
    (state.supportDartAt position).edge =
      (state.targetRootedCrossingEdge position : Sym2 V) := by
  rw [supportDartAt, SimpleGraph.Walk.dartAtEdgePosition_edge]
  let equivalence := List.Nodup.getEquiv state.supportCycle.edges
    state.supportCycle_isCycle.edges_nodup
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨state.targetRootedCrossingValue position,
        state.targetRootedCrossingValue_mem_supportCycle position⟩)

/-- Every support dart selected at a singleton separator crossing changes
from the singleton side to its complement, or conversely. -/
theorem supportDartAt_crosses_singletonSide
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    let side := fun vertex => vertex ∈ profile.component.supp
    side (state.supportDartAt position).fst ≠
      side (state.supportDartAt position).snd := by
  let side := fun vertex => vertex ∈ profile.component.supp
  have hcross : EdgeCrossesVertexSide G side
      (state.targetRootedCrossingEdge position) := by
    apply (mem_crossingEdgeFinset_iff side _).1
    rw [profile.component_boundary_eq]
    exact state.targetRootedCrossingEdge_mem_remote position
  have htransition :=
    (edgeCrosses_toRotationSystem_edgeOf_iff_transition
      graphData side (state.supportDartAt position)).1
      (show EdgeCrossesVertexSide G side
        (graphData.toRotationSystem.edgeOf
          (state.supportDartAt position)) by
        have hedge : graphData.toRotationSystem.edgeOf
            (state.supportDartAt position) =
            state.targetRootedCrossingEdge position := by
          apply Subtype.ext
          simpa [Data.toRotationSystem_edgeOf] using
            state.supportDartAt_edge position
        rw [hedge]
        exact hcross)
  rw [graphData.toRotationSystem.vert_phi_eq_vert_alpha] at htransition
  simpa [side, Data.toRotationSystem_vertOf,
    Data.toRotationSystem_alpha] using htransition

/-- Two distinct support crossings through a singleton component have
opposite traversal orientations relative to that component. -/
theorem supportDartAt_fst_side_ne_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile)
    {first second : Fin state.targetRootedSupportOrder.length}
    (hne : first ≠ second) :
    (state.supportDartAt first).fst ∈ profile.component.supp ↔
      (state.supportDartAt second).fst ∉ profile.component.supp := by
  let side := fun vertex => vertex ∈ profile.component.supp
  have hfirstCross := state.supportDartAt_crosses_singletonSide
    profile first
  have hsecondCross := state.supportDartAt_crosses_singletonSide
    profile second
  have hpositionNe : state.supportEdgePosition first ≠
      state.supportEdgePosition second := by
    intro heq
    exact hne (state.supportEdgePosition_injective heq)
  by_cases hfirstSide : side (state.supportDartAt first).fst
  · have hsecondNotSide : ¬ side (state.supportDartAt second).fst := by
      intro hsecondSide
      have hvertices : (state.supportDartAt first).fst =
          (state.supportDartAt second).fst :=
        profile.vertex_eq_of_mem_component hfirstSide hsecondSide
      exact hpositionNe
        (state.supportCycle_isCycle.dartAtEdgePosition_fst_injective
          hvertices)
    exact ⟨fun _ => hsecondNotSide, fun _ => hfirstSide⟩
  · have hfirstSnd : side (state.supportDartAt first).snd := by
      by_contra hnot
      apply hfirstCross
      exact propext ⟨fun h => (hfirstSide h).elim,
        fun h => (hnot h).elim⟩
    have hsecondSide : side (state.supportDartAt second).fst := by
      by_contra hsecondNotSide
      have hsecondSnd : side (state.supportDartAt second).snd := by
        by_contra hnot
        apply hsecondCross
        exact propext ⟨fun h => (hsecondNotSide h).elim,
          fun h => (hnot h).elim⟩
      have hvertices : (state.supportDartAt first).snd =
          (state.supportDartAt second).snd :=
        profile.vertex_eq_of_mem_component hfirstSnd hsecondSnd
      exact hpositionNe
        (state.supportCycle_isCycle.dartAtEdgePosition_snd_injective
          hvertices)
    exact ⟨fun h => (hfirstSide h).elim,
      fun hsecondNot => (hsecondNot hsecondSide).elim⟩

/-- The unique indexed remote-cycle step crossing a rooted physical
crossing edge. -/
def remoteStepAt
    (position : Fin state.targetRootedSupportOrder.length) :
    Fin cycle.walk.length :=
  Classical.choose
    ((mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk (state.targetRootedCrossingEdge position)).1
        (state.targetRootedCrossingEdge_mem_remote position))

@[simp] theorem crossingAt_remoteStepAt
    (position : Fin state.targetRootedSupportOrder.length) :
    cycle.crossingAt (state.remoteStepAt position) =
      state.targetRootedCrossingEdge position := by
  simpa [crossingAt, remoteStepAt] using
    (Classical.choose_spec
      ((mem_dualWalkCrossingEdges_iff
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk (state.targetRootedCrossingEdge position)).1
          (state.targetRootedCrossingEdge_mem_remote position)))

/-- The canonical left-face orientation in which the remote dual cycle
crosses a rooted physical crossing edge. -/
def remoteDartAt
    (position : Fin state.targetRootedSupportOrder.length) : G.Dart :=
  cycle.leftFaceDartAt (state.remoteStepAt position)

theorem remoteDartAt_mem_leftFace
    (position : Fin state.targetRootedSupportOrder.length) :
    state.remoteDartAt position ∈
      orbitFaceDarts graphData.toRotationSystem
        (cycle.walk.getVert (state.remoteStepAt position)).1 :=
  cycle.leftFaceDartAt_mem_face (state.remoteStepAt position)

@[simp] theorem remoteDartAt_edge
    (position : Fin state.targetRootedSupportOrder.length) :
    (state.remoteDartAt position).edge =
      (state.targetRootedCrossingEdge position : Sym2 V) := by
  have hedge := congrArg Subtype.val
    (cycle.leftFaceDartAt_edgeOf (state.remoteStepAt position))
  simpa [remoteDartAt, Data.toRotationSystem_edgeOf] using hedge

/-- At each shared physical edge, the remote and support orientations are
equal or exact reversals. -/
theorem remoteDartAt_eq_or_eq_support_symm
    (position : Fin state.targetRootedSupportOrder.length) :
    state.remoteDartAt position = state.supportDartAt position ∨
      state.remoteDartAt position = (state.supportDartAt position).symm := by
  apply (SimpleGraph.dart_edge_eq_iff _ _).1
  rw [state.remoteDartAt_edge, state.supportDartAt_edge]

/-- Local crossing chirality is positive precisely when the support-cycle
and remote-cycle orientations agree on that physical edge. -/
def targetRootedCrossingChirality
    (position : Fin state.targetRootedSupportOrder.length) : Bool :=
  if state.remoteDartAt position = state.supportDartAt position then
    true
  else false

@[simp] theorem targetRootedCrossingChirality_eq_true_iff
    (position : Fin state.targetRootedSupportOrder.length) :
    state.targetRootedCrossingChirality position = true ↔
      state.remoteDartAt position = state.supportDartAt position := by
  simp [targetRootedCrossingChirality]

@[simp] theorem targetRootedCrossingChirality_eq_false_iff
    (position : Fin state.targetRootedSupportOrder.length) :
    state.targetRootedCrossingChirality position = false ↔
      state.remoteDartAt position =
        (state.supportDartAt position).symm := by
  constructor
  · intro hnegative
    have hne : state.remoteDartAt position ≠
        state.supportDartAt position := by
      intro heq
      have hpositive :=
        (state.targetRootedCrossingChirality_eq_true_iff position).2 heq
      rw [hnegative] at hpositive
      contradiction
    rcases state.remoteDartAt_eq_or_eq_support_symm position with
      hsame | hreverse
    · exact False.elim (hne hsame)
    · exact hreverse
  · intro hreverse
    have hne : state.remoteDartAt position ≠
        state.supportDartAt position := by
      intro heq
      exact SimpleGraph.Dart.symm_ne _ (hreverse.symm.trans heq)
    unfold targetRootedCrossingChirality
    rw [if_neg hne]

/-- The signed rooted monodromy transports both the crossing rank and one
of the two orientations of its physical edge. -/
def targetRootedSignedMonodromy :
    Equiv.Perm
      (Fin state.targetRootedSupportOrder.length × Bool) :=
  signedIndexPermutation state.targetRootedOrderTransport.monodromy
    state.targetRootedCrossingChirality

@[simp] theorem targetRootedSignedMonodromy_apply_fst
    (signedPosition : Fin state.targetRootedSupportOrder.length × Bool) :
    (state.targetRootedSignedMonodromy signedPosition).1 =
      state.targetRootedOrderTransport.monodromy signedPosition.1 :=
  rfl

@[simp] theorem targetRootedSignedMonodromy_apply_snd
    (signedPosition : Fin state.targetRootedSupportOrder.length × Bool) :
    (state.targetRootedSignedMonodromy signedPosition).2 =
      fusionEndpointTransport
        (state.targetRootedCrossingChirality signedPosition.1)
        signedPosition.2 :=
  rfl

/-- Signed rooted monodromy is trivial exactly when bare crossing order is
trivial and every remote/support orientation agrees. -/
theorem targetRootedSignedMonodromy_eq_refl_iff :
    state.targetRootedSignedMonodromy =
        Equiv.refl
          (Fin state.targetRootedSupportOrder.length × Bool) ↔
      state.targetRootedOrderTransport.monodromy =
          Equiv.refl (Fin state.targetRootedSupportOrder.length) ∧
        ∀ position, state.targetRootedCrossingChirality position = true :=
  signedIndexPermutation_eq_refl_iff _ _

/-- One oppositely oriented crossing makes the signed rooted monodromy
nonidentity, even when bare crossing order is fixed. -/
theorem targetRootedSignedMonodromy_ne_refl_of_remoteDart_eq_support_symm
    (position : Fin state.targetRootedSupportOrder.length)
    (hreverse : state.remoteDartAt position =
      (state.supportDartAt position).symm) :
    state.targetRootedSignedMonodromy ≠
      Equiv.refl
        (Fin state.targetRootedSupportOrder.length × Bool) := by
  intro hidentity
  have hpositive :=
    (state.targetRootedSignedMonodromy_eq_refl_iff.1 hidentity).2
      position
  have hnegative :=
    (state.targetRootedCrossingChirality_eq_false_iff position).2
      hreverse
  rw [hnegative] at hpositive
  contradiction

/-- The simple support cycle meets an exact singleton remote triangle in
exactly two physical crossing edges. -/
theorem targetRootedSupportOrder_length_eq_two_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    state.targetRootedSupportOrder.length = 2 := by
  have htwo := state.two_le_targetRootedSupportOrder_length
  have hwidth : state.targetRootedSupportOrder.length ≤
      cycle.walk.length := by
    simpa [targetRootedSupportOrder] using
      cycle.supportCrossingOrder_length_le_walk_length
        state.supportCycle_isCycle
  rw [profile.length_eq_three] at hwidth
  rcases state.targetRootedSupportOrder_length_even with ⟨half, hhalf⟩
  omega

/-- In the singleton three-cut branch, the unsigned position component is
fixed pointwise; the remaining signed action is exactly the local crossing
orientation transport. -/
theorem targetRootedSignedMonodromy_apply_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile)
    (signedPosition : Fin state.targetRootedSupportOrder.length × Bool) :
    state.targetRootedSignedMonodromy signedPosition =
      (signedPosition.1,
        fusionEndpointTransport
          (state.targetRootedCrossingChirality signedPosition.1)
          signedPosition.2) := by
  apply Prod.ext
  · change state.targetRootedOrderTransport.monodromy signedPosition.1 =
      signedPosition.1
    rw [state.targetRootedMonodromy_eq_refl_of_singletonPrimalCutProfile
      profile]
    rfl
  · rfl

/-- For a singleton primal cut, signed identity is equivalent to positive
orientation at every physical crossing. -/
theorem targetRootedSignedMonodromy_eq_refl_iff_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    state.targetRootedSignedMonodromy =
        Equiv.refl
          (Fin state.targetRootedSupportOrder.length × Bool) ↔
      ∀ position, state.targetRootedCrossingChirality position = true := by
  rw [state.targetRootedSignedMonodromy_eq_refl_iff,
    state.targetRootedMonodromy_eq_refl_of_singletonPrimalCutProfile profile]
  simp

/-- The singleton branch has nontrivial signed monodromy exactly when one
of its concrete remote crossing darts reverses the support-cycle dart. -/
theorem targetRootedSignedMonodromy_ne_refl_iff_exists_reversed_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    state.targetRootedSignedMonodromy ≠
        Equiv.refl
          (Fin state.targetRootedSupportOrder.length × Bool) ↔
      ∃ position : Fin state.targetRootedSupportOrder.length,
        state.remoteDartAt position =
          (state.supportDartAt position).symm := by
  constructor
  · intro hnontrivial
    by_contra hnoReverse
    push Not at hnoReverse
    apply hnontrivial
    apply
      (state.targetRootedSignedMonodromy_eq_refl_iff_of_singletonPrimalCutProfile
        profile).2
    intro position
    cases hchirality : state.targetRootedCrossingChirality position with
    | false =>
        exfalso
        exact hnoReverse position
          ((state.targetRootedCrossingChirality_eq_false_iff position).1
            hchirality)
    | true => rfl
  · rintro ⟨position, hreverse⟩
    exact state.targetRootedSignedMonodromy_ne_refl_of_remoteDart_eq_support_symm
      position hreverse

/-- Singleton collar geometry forces nontrivial signed monodromy: the
remote boundary orientation is coherent, whereas a simple primal support
cycle enters and leaves the singleton component in opposite orientations. -/
theorem targetRootedSignedMonodromy_ne_refl_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    state.targetRootedSignedMonodromy ≠
      Equiv.refl
        (Fin state.targetRootedSupportOrder.length × Bool) := by
  intro hidentity
  let side := fun vertex => vertex ∈ profile.component.supp
  let first := state.targetRootedSupportEntryPosition
  let second := finRotate state.targetRootedSupportOrder.length first
  have htwo : 2 ≤ state.targetRootedSupportOrder.length :=
    state.two_le_targetRootedSupportOrder_length
  have hrotateNe : second ≠ first := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwo]
    exact Finset.mem_univ _
  have hpositionsNe : first ≠ second := hrotateNe.symm
  have hsupportOpposite :
      side (state.supportDartAt first).fst ↔
        ¬ side (state.supportDartAt second).fst := by
    exact state.supportDartAt_fst_side_ne_of_singletonPrimalCutProfile
      profile hpositionsNe
  have hremoteCoherent :
      side (state.remoteDartAt first).fst ↔
        side (state.remoteDartAt second).fst := by
    simpa [side, remoteDartAt] using
      cycle.leftFaceDartAt_side_coherent_all_of_boundary_eq
        side profile.component_boundary_eq
        (state.remoteStepAt first) (state.remoteStepAt second)
  have hpositive :=
    (state.targetRootedSignedMonodromy_eq_refl_iff_of_singletonPrimalCutProfile
      profile).1 hidentity
  have hfirstSame : state.remoteDartAt first =
      state.supportDartAt first :=
    (state.targetRootedCrossingChirality_eq_true_iff first).1
      (hpositive first)
  have hsecondSame : state.remoteDartAt second =
      state.supportDartAt second :=
    (state.targetRootedCrossingChirality_eq_true_iff second).1
      (hpositive second)
  have hsupportCoherent :
      side (state.supportDartAt first).fst ↔
        side (state.supportDartAt second).fst := by
    rw [← hfirstSame, ← hsecondSame]
    exact hremoteCoherent
  tauto

end ScalarSupportCrossingState

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
