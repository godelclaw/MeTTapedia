import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutAttachment
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [decidableAdjacency : DecidableRel G.Adj]

noncomputable section

local instance bondFiniteGraphLocallyFinite (G : SimpleGraph V)
    [decidableAdjacency' : DecidableRel G.Adj] :
    G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (decidableAdjacency' vertex) inferInstance

namespace GoertzelV24DualCycleBond

attribute [local instance]
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

/-- For a graph-backed rotation system, a dart changes vertex sides along
its facial step exactly when its underlying graph edge crosses the side. -/
theorem edgeCrosses_toRotationSystem_edgeOf_iff_transition
    (data : Data G) (side : V → Prop) (dart : G.Dart) :
    EdgeCrossesVertexSide G side (data.toRotationSystem.edgeOf dart) ↔
      side (data.toRotationSystem.vertOf dart) ≠
        side (data.toRotationSystem.vertOf
          (data.toRotationSystem.phi dart)) := by
  rw [data.toRotationSystem.vert_phi_eq_vert_alpha]
  simp only [Data.toRotationSystem_edgeOf, Data.toRotationSystem_vertOf,
    Data.toRotationSystem_alpha]
  change EdgeCrossesVertexSide G side
      (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet) ↔
    side dart.fst ≠ side dart.snd
  constructor
  · intro hcross hsides
    have hnotIff :=
      not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
        (G := G) (side := side)
        (a := dart.fst) (b := dart.snd)
        (e := (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet)) rfl hcross
    apply hnotIff
    exact Iff.of_eq hsides
  · intro hsides
    by_cases hfirst : side dart.fst
    · have hsecond : ¬ side dart.snd := by
        intro hsecond
        apply hsides
        exact propext ⟨fun _ => hsecond, fun _ => hfirst⟩
      exact ⟨dart.fst, dart.snd, by
        change dart.fst ∈ s(dart.fst, dart.snd)
        simp, by
        change dart.snd ∈ s(dart.fst, dart.snd)
        simp, hfirst, hsecond⟩
    · have hsecond : side dart.snd := by
        by_contra hsecond
        apply hsides
        exact propext ⟨fun h => (hfirst h).elim,
          fun h => (hsecond h).elim⟩
      exact ⟨dart.snd, dart.fst, by
        change dart.snd ∈ s(dart.fst, dart.snd)
        simp, by
        change dart.fst ∈ s(dart.fst, dart.snd)
        simp, hsecond, hfirst⟩

/-- Under facial two-sidedness, the edge map is injective on the darts of
each quotient face. -/
theorem edgeOf_injOn_orbitFaceDarts_of_twoSided
    (RS : RotationSystem V G.edgeSet) (htwoSided : OrbitFacesTwoSided RS)
    (face : OrbitFace RS) :
    Set.InjOn RS.edgeOf (orbitFaceDarts RS face) := by
  intro left hleft right hright hedge
  rcases RS.edge_fiber_two_cases rfl hedge.symm with heq | heq
  · exact heq.symm
  · exfalso
    apply htwoSided left
    have hleftFace : dartOrbitFace RS left = face :=
      (mem_orbitFaceDarts_iff RS face left).1 hleft
    have hrightFace : dartOrbitFace RS right = face :=
      (mem_orbitFaceDarts_iff RS face right).1 hright
    rw [← heq, hleftFace, hrightFace]

/-- The edge image of the side-transition darts on a quotient face is the
intersection of that face boundary with the exact side-crossing edge set. -/
theorem image_edgeOf_orbitFaceSideTransitionDarts_eq_crossing_inter_boundary
    (data : Data G) (side : V → Prop)
    (face : OrbitFace data.toRotationSystem) :
    (orbitFaceSideTransitionDarts data.toRotationSystem side face).image
        data.toRotationSystem.edgeOf =
      crossingEdgeFinset G side ∩
        orbitFaceBoundary data.toRotationSystem face := by
  classical
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_image.1 hedge with ⟨dart, hdart, rfl⟩
    have hdartData :=
      (mem_orbitFaceSideTransitionDarts_iff
        data.toRotationSystem side face dart).1 hdart
    exact Finset.mem_inter.2
      ⟨(mem_crossingEdgeFinset_iff side _).2
          ((edgeCrosses_toRotationSystem_edgeOf_iff_transition
            data side dart).2 hdartData.2),
        (mem_orbitFaceBoundary_iff data.toRotationSystem face _).2
          ⟨dart,
            (mem_orbitFaceDarts_iff data.toRotationSystem face dart).2
              hdartData.1,
            rfl⟩⟩
  · intro hedge
    rcases Finset.mem_inter.1 hedge with ⟨hcrossing, hface⟩
    rcases (mem_orbitFaceBoundary_iff data.toRotationSystem face edge).1 hface
      with ⟨dart, hdartFace, hdartEdge⟩
    refine Finset.mem_image.2 ⟨dart, ?_, hdartEdge⟩
    apply (mem_orbitFaceSideTransitionDarts_iff
      data.toRotationSystem side face dart).2
    refine ⟨(mem_orbitFaceDarts_iff
      data.toRotationSystem face dart).1 hdartFace, ?_⟩
    apply (edgeCrosses_toRotationSystem_edgeOf_iff_transition
      data side dart).1
    rw [hdartEdge]
    exact (mem_crossingEdgeFinset_iff side edge).1 hcrossing

/-- Every quotient face meets an exact vertex-side edge boundary an even
number of times. -/
theorem even_card_crossingEdgeFinset_inter_orbitFaceBoundary
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (side : V → Prop) (face : OrbitFace data.toRotationSystem) :
    Even ((crossingEdgeFinset G side ∩
      orbitFaceBoundary data.toRotationSystem face).card) := by
  have himage :=
    image_edgeOf_orbitFaceSideTransitionDarts_eq_crossing_inter_boundary
      data side face
  rw [← himage]
  have hinjective : Set.InjOn data.toRotationSystem.edgeOf
      (orbitFaceSideTransitionDarts data.toRotationSystem side face) := by
    intro left hleft right hright hedge
    apply edgeOf_injOn_orbitFaceDarts_of_twoSided
      data.toRotationSystem htwoSided face
    · exact (mem_orbitFaceDarts_iff data.toRotationSystem face left).2
        ((mem_orbitFaceSideTransitionDarts_iff
          data.toRotationSystem side face left).1 hleft).1
    · exact (mem_orbitFaceDarts_iff data.toRotationSystem face right).2
        ((mem_orbitFaceSideTransitionDarts_iff
          data.toRotationSystem side face right).1 hright).1
    · exact hedge
  rw [Finset.card_image_iff.mpr hinjective]
  exact even_card_orbitFaceSideTransitionDarts
    data.toRotationSystem side face

/-- Cyclic successor reads the next walk vertex, including across the
closing step of a simple cycle. -/
theorem getVert_succ_eq_getVert_finRotate
    {F E : Type*} [Fintype F] [DecidableEq F]
    [Fintype E] [DecidableEq E]
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start start)
    (hcycle : walk.IsCycle) (step : Fin walk.length) :
    walk.getVert (step.val + 1) =
      walk.getVert (finRotate walk.length step).val := by
  have hpositive : 0 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  have hone : 1 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  letI : NeZero walk.length := ⟨Nat.ne_of_gt hpositive⟩
  by_cases hnext : step.val + 1 < walk.length
  · have hrotate : (finRotate walk.length step).val = step.val + 1 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hnext]
    rw [hrotate]
  · have hlast : step.val + 1 = walk.length := by omega
    have hrotate : (finRotate walk.length step).val = 0 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, hlast, Nat.mod_self]
    rw [hlast, hrotate, walk.getVert_length, walk.getVert_zero]

/-- At most two crossings of a simple facial-dual cycle are incident to any
one quotient face. -/
theorem card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (face : OrbitFace data.toRotationSystem) :
    (dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk ∩
        orbitFaceBoundary data.toRotationSystem face).card ≤ 2 := by
  classical
  let crossing := dualWalkCrossingEdge
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let incidentSteps : Finset (Fin walk.length) :=
    Finset.univ.filter fun step =>
      crossing step ∈ orbitFaceBoundary data.toRotationSystem face
  let leftSteps : Finset (Fin walk.length) :=
    Finset.univ.filter fun step => (walk.getVert step.val).1 = face
  let rightSteps : Finset (Fin walk.length) :=
    Finset.univ.filter fun step => (walk.getVert (step.val + 1)).1 = face
  have hincidentSubset : incidentSteps ⊆ leftSteps ∪ rightSteps := by
    intro step hstep
    have hboundary : crossing step ∈
        orbitFaceBoundary data.toRotationSystem face :=
      (Finset.mem_filter.1 hstep).2
    let left := walk.getVert step.val
    let right := walk.getVert (step.val + 1)
    have hadj := walk.adj_getVert_succ step.isLt
    have hfaces : left.1 ≠ right.1 := by
      intro heq
      exact hadj.ne (Subtype.ext heq)
    have hleft : crossing step ∈
        orbitFaceBoundary data.toRotationSystem left.1 :=
      dualWalkCrossingEdge_mem_leftFace
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk step
    have hright : crossing step ∈
        orbitFaceBoundary data.toRotationSystem right.1 :=
      dualWalkCrossingEdge_mem_rightFace
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk step
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem)
        left.2 right.2 (Finset.mem_univ face) hfaces hleft hright hboundary
    rcases hcases with hfaceLeft | hfaceRight
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfaceLeft.symm⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfaceRight.symm⟩)
  have hleftCard : leftSteps.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    have hfirstFace := (Finset.mem_filter.1 hfirst).2
    have hsecondFace := (Finset.mem_filter.1 hsecond).2
    apply Fin.ext
    exact hcycle.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext (hfirstFace.trans hsecondFace.symm))
  have hrightCard : rightSteps.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    have hfirstFace := (Finset.mem_filter.1 hfirst).2
    have hsecondFace := (Finset.mem_filter.1 hsecond).2
    apply Fin.ext
    have hvalues := hcycle.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext (hfirstFace.trans hsecondFace.symm))
    omega
  have hincidentCard : incidentSteps.card ≤ 2 := by
    calc
      incidentSteps.card ≤ (leftSteps ∪ rightSteps).card :=
        Finset.card_le_card hincidentSubset
      _ ≤ leftSteps.card + rightSteps.card :=
        Finset.card_union_le leftSteps rightSteps
      _ ≤ 2 := by omega
  have himage : incidentSteps.image crossing =
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk ∩
          orbitFaceBoundary data.toRotationSystem face := by
    ext edge
    constructor
    · intro hedge
      rcases Finset.mem_image.1 hedge with ⟨step, hstep, hstepEdge⟩
      have hboundary := (Finset.mem_filter.1 hstep).2
      apply Finset.mem_inter.2
      exact ⟨(mem_dualWalkCrossingEdges_iff
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk edge).2 ⟨step, hstepEdge⟩,
          hstepEdge ▸ hboundary⟩
    · intro hedge
      rcases Finset.mem_inter.1 hedge with ⟨hcrossing, hboundary⟩
      rcases (mem_dualWalkCrossingEdges_iff
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk edge).1 hcrossing with ⟨step, hstepEdge⟩
      apply Finset.mem_image.2
      refine ⟨step, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
        hstepEdge⟩
      change dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk step ∈ orbitFaceBoundary data.toRotationSystem face
      rw [hstepEdge]
      exact hboundary
  rw [← himage,
    Finset.card_image_of_injective _
      (dualWalkCrossingEdge_injective_of_isCycle
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem)
        hunique walk hcycle)]
  exact hincidentCard

/-- A nonempty exact vertex-side boundary contained in the crossings of a
simple facial-dual cycle is the whole crossing set. Even facial incidence
propagates membership once around the cycle. -/
theorem crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (side : V → Prop)
    (hsubset : crossingEdgeFinset G side ⊆
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (hnonempty : (crossingEdgeFinset G side).Nonempty) :
    crossingEdgeFinset G side =
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk := by
  classical
  let crossing := dualWalkCrossingEdge
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let boundary := crossingEdgeFinset G side
  have hcrossingInjective : Function.Injective crossing :=
    dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem)
      hunique walk hcycle
  have htwoLength : 2 ≤ walk.length :=
    le_trans (by omega) hcycle.three_le_length
  have hrotateNe (step : Fin walk.length) :
      finRotate walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hsuccessor (step : Fin walk.length)
      (hstepBoundary : crossing step ∈ boundary) :
      crossing (finRotate walk.length step) ∈ boundary := by
    let face := (walk.getVert (step.val + 1)).1
    let boundaryAtFace := boundary ∩
      orbitFaceBoundary data.toRotationSystem face
    let removedAtFace := removed ∩
      orbitFaceBoundary data.toRotationSystem face
    have hstepRemoved : crossing step ∈ removed := by
      exact (mem_dualWalkCrossingEdges_iff
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk (crossing step)).2 ⟨step, rfl⟩
    have hnextRemoved : crossing (finRotate walk.length step) ∈ removed := by
      exact (mem_dualWalkCrossingEdges_iff
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk (crossing (finRotate walk.length step))).2
          ⟨finRotate walk.length step, rfl⟩
    have hstepFace : crossing step ∈
        orbitFaceBoundary data.toRotationSystem face :=
      dualWalkCrossingEdge_mem_rightFace
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk step
    have hnextFace : crossing (finRotate walk.length step) ∈
        orbitFaceBoundary data.toRotationSystem face := by
      have hmem := dualWalkCrossingEdge_mem_leftFace
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        hunique walk (finRotate walk.length step)
      rw [← getVert_succ_eq_getVert_finRotate walk hcycle step] at hmem
      exact hmem
    have hedgesNe : crossing step ≠
        crossing (finRotate walk.length step) := by
      intro hedges
      exact hrotateNe step (hcrossingInjective hedges.symm)
    have hboundaryAtFaceSubset : boundaryAtFace ⊆ removedAtFace := by
      intro edge hedge
      rcases Finset.mem_inter.1 hedge with ⟨hboundary, hface⟩
      exact Finset.mem_inter.2 ⟨hsubset hboundary, hface⟩
    have hboundaryAtFaceEven : Even boundaryAtFace.card := by
      exact even_card_crossingEdgeFinset_inter_orbitFaceBoundary
        data htwoSided side face
    have hboundaryAtFacePositive : 0 < boundaryAtFace.card := by
      apply Finset.card_pos.2
      exact ⟨crossing step,
        Finset.mem_inter.2 ⟨hstepBoundary, hstepFace⟩⟩
    have hremovedAtFaceCardLe : removedAtFace.card ≤ 2 :=
      card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
        data hunique walk hcycle face
    have hboundaryAtFaceCardLe : boundaryAtFace.card ≤ 2 :=
      le_trans (Finset.card_le_card hboundaryAtFaceSubset)
        hremovedAtFaceCardLe
    have hboundaryAtFaceCard : boundaryAtFace.card = 2 := by
      rcases hboundaryAtFaceEven with ⟨half, hhalf⟩
      omega
    have hpairSubset :
        {crossing step, crossing (finRotate walk.length step)} ⊆
          removedAtFace := by
      intro edge hedge
      rw [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl
      · exact Finset.mem_inter.2 ⟨hstepRemoved, hstepFace⟩
      · exact Finset.mem_inter.2 ⟨hnextRemoved, hnextFace⟩
    have hpairCard :
        ({crossing step, crossing (finRotate walk.length step)} :
          Finset G.edgeSet).card = 2 := by
      exact Finset.card_pair hedgesNe
    have hremovedAtFaceCard : removedAtFace.card = 2 := by
      have hlower : 2 ≤ removedAtFace.card := by
        rw [← hpairCard]
        exact Finset.card_le_card hpairSubset
      omega
    have hfacesEqual : boundaryAtFace = removedAtFace := by
      apply Finset.eq_of_subset_of_card_le hboundaryAtFaceSubset
      omega
    have hnextBoundaryAtFace :
        crossing (finRotate walk.length step) ∈ boundaryAtFace := by
      rw [hfacesEqual]
      exact Finset.mem_inter.2 ⟨hnextRemoved, hnextFace⟩
    exact (Finset.mem_inter.1 hnextBoundaryAtFace).1
  rcases hnonempty with ⟨seedEdge, hseedBoundary⟩
  have hseedRemoved := hsubset hseedBoundary
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      hunique walk seedEdge).1 hseedRemoved with
    ⟨seed, hseedEdge⟩
  have hseed : crossing seed ∈ boundary := by
    change dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      hunique walk seed ∈ crossingEdgeFinset G side
    rw [hseedEdge]
    exact hseedBoundary
  have hallSteps (target : Fin walk.length) : crossing target ∈ boundary := by
    have hsameCycle :
        (finRotate walk.length).SameCycle seed target :=
      (isCycle_finRotate_of_le htwoLength).sameCycle
        (hrotateNe seed) (hrotateNe target)
    rcases hsameCycle.exists_nat_pow_eq with ⟨power, hpower⟩
    have hiterate : ∀ exponent : Nat,
        crossing (((finRotate walk.length) ^ exponent) seed) ∈ boundary := by
      intro exponent
      induction exponent with
      | zero => simpa using hseed
      | succ previous ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact hsuccessor _ ih
    have hiteratePower := hiterate power
    rw [hpower] at hiteratePower
    exact hiteratePower
  apply Finset.Subset.antisymm hsubset
  intro edge hedge
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      hunique walk edge).1 hedge with ⟨step, hstepEdge⟩
  rw [← hstepEdge]
  exact hallSteps step

end GoertzelV24DualCycleBond

namespace GoertzelV24DualCycleSeparator

attribute [local instance] graphEdgeSetDecidableEq

/-- A separating facial-dual four-cycle in a cubic cyclically
five-edge-connected graph cuts off exactly two vertices, and all four
cycle crossings are incident to that component. -/
theorem exists_primalCut_component_card_eq_two_and_boundary_eq_of_isCycle_of_length_eq_four
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length = 4)
    (hdelete :
      ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges (dualWalkPrimalCut data hunique walk)).ConnectedComponent,
      Nat.card {vertex : V // vertex ∈ component.supp} = 2 ∧
        crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) =
          removed := by
  dsimp only
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  have hremovedCard : removed.card = 4 := by
    rw [GoertzelV24DualPathTransversal.card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hunique walk hcycle,
      hlength]
  have hcutEq :=
    dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      data hunique walk
  rw [hcutEq] at hdelete ⊢
  rcases
      GoertzelV24FiniteEdgeDeletion.exists_component_card_le_two_of_cyclicallyFive_of_not_connected
        hregular hconnected hcyclic removed (by omega) hdelete with
    ⟨component, hcomponentCardLe⟩
  let side : V → Prop := fun vertex => vertex ∈ component.supp
  have hcomponentCardPositive :
      0 < Nat.card {vertex : V // side vertex} := by
    letI : Nonempty {vertex : V // side vertex} :=
      ⟨⟨component.nonempty_supp.choose,
        component.nonempty_supp.choose_spec⟩⟩
    exact Nat.card_pos
  have hcomponentBoundaryCard :=
    GoertzelV24FiniteEdgeDeletion.card_componentCrossingEdges_eq_card_add_two_of_cubic_of_card_le_two
      hregular removed component hcomponentCardLe
  have hboundaryNonempty : (crossingEdgeFinset G side).Nonempty := by
    apply Finset.card_pos.1
    rw [← GoertzelV24FiniteEdgeDeletion.componentCrossingEdges_eq_crossingEdgeFinset
      removed component, hcomponentBoundaryCard]
    omega
  have hboundarySubset : crossingEdgeFinset G side ⊆ removed := by
    rw [← GoertzelV24FiniteEdgeDeletion.componentCrossingEdges_eq_crossingEdgeFinset
      removed component]
    exact
      GoertzelV24FiniteEdgeDeletion.componentCrossingEdges_subset_removed
        removed component
  have hboundaryEq : crossingEdgeFinset G side = removed :=
    GoertzelV24DualCycleBond.crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
      data htwoSided hunique walk hcycle side hboundarySubset
        hboundaryNonempty
  have hcomponentCard :
      Nat.card {vertex : V // side vertex} = 2 := by
    rw [GoertzelV24FiniteEdgeDeletion.componentCrossingEdges_eq_crossingEdgeFinset,
      hboundaryEq, hremovedCard] at hcomponentBoundaryCard
    change Nat.card {vertex : V // vertex ∈ component.supp} = 2
    omega
  exact ⟨component, hcomponentCard, hboundaryEq⟩

end GoertzelV24DualCycleSeparator

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- In the short saturated regime, recovery produces a remote separating
facial-dual four-cycle with an exact two-vertex primal collar. Every one of
the four cycle crossings is incident to that collar. -/
theorem exists_remote_primal_separator_with_exact_two_vertex_collar_of_arcLength_le_four
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (hshort : rebaseCircuit.arcLength ≤ 4) :
    rebaseCircuit.arcLength = 4 ∧
      ∃ walk :
          (interiorDualGraph
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace graphData.toRotationSystem))).Walk
            rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
        walk.IsCycle ∧
          ¬ (G.deleteEdges
            (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
              (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk)).Connected ∧
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal) walk).ncard = 4 ∧
          (let removed := dualWalkCrossingEdges
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))
              (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
            ∃ component :
                (G.deleteEdges
                  (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
                    (pairwiseUniqueSharedInteriorEdges graphData minimal)
                    walk)).ConnectedComponent,
              Nat.card {vertex : V // vertex ∈ component.supp} = 2 ∧
                crossingEdgeFinset G
                    (fun vertex => vertex ∈ component.supp) =
                  removed) ∧
          (∀ face ∈ walk.support,
            centralEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) ∧
          (∀ face ∈ walk.support, ∀ port : Fin 4,
            boundaryEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) := by
  rcases
      circuit.exists_remote_primal_separator_with_attachmentProfile_of_arcLength_le_four
        hcyclic hminimal hlength hshort with
    ⟨hrebaseLength, walk, hcycle, hdelete, hcutCard,
      _hattachment, hcentral, hboundary⟩
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hwalkLength : walk.length = 4 := by
    calc
      walk.length =
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk).ncard :=
        (GoertzelV24DualCycleSeparator.ncard_dualWalkPrimalCut_eq_length_of_isCycle
          graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
            walk hcycle).symm
      _ = 4 := hcutCard
  have hexact :=
    GoertzelV24DualCycleSeparator.exists_primalCut_component_card_eq_two_and_boundary_eq_of_isCycle_of_length_eq_four
      graphData hregular hconnected hcyclic minimal.facesTwoSided
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
          hwalkLength hdelete
  exact ⟨hrebaseLength, walk, hcycle, hdelete, hcutCard,
    hexact, hcentral, hboundary⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
