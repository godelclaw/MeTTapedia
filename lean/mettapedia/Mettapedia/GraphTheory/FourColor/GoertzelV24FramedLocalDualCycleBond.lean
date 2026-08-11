import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleCrossingInjective

/-!
# Local facial two-sidedness for exact dual-cycle cuts

The Cell-3 carrier is an open annular tangle: its two named hole faces contain
degree-one stubs and are therefore not globally two-sided.  A source corridor
layer, however, runs entirely through ordinary annular-interior faces, each of
which has a simple two-sided boundary.  This file factors the standard
dual-cycle bond argument through exactly that local hypothesis.  It thereby
constructs the graph-side cut of a Cell-3 layer without misrepresenting the
open tangle as a closed cubic map.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedLocalDualCycleBondEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace GoertzelV24FramedLocalDualCycleBond

/-- The finite set of graph edges crossing a vertex side, kept local so the
open-tangle bond construction does not import the closed-cubic collar stack. -/
noncomputable def localCrossingEdgeFinset (G : SimpleGraph V) (side : V → Prop) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter (EdgeCrossesVertexSide G side)

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_localCrossingEdgeFinset_iff (side : V → Prop) (edge : G.edgeSet) :
    edge ∈ localCrossingEdgeFinset G side ↔
      EdgeCrossesVertexSide G side edge := by
  simp [localCrossingEdgeFinset]

/-- For a graph-backed rotation system, a dart changes vertex sides along
its facial step exactly when its underlying graph edge crosses the side. -/
private theorem edgeCrosses_toRotationSystem_edgeOf_iff_transition
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

/-- The edge image of the side-transition darts on a quotient face is the
intersection of that face boundary with the exact side-crossing edge set. -/
private theorem image_edgeOf_orbitFaceSideTransitionDarts_eq_crossing_inter_boundary
    (data : Data G) (side : V → Prop)
    (face : OrbitFace data.toRotationSystem) :
    (orbitFaceSideTransitionDarts data.toRotationSystem side face).image
        data.toRotationSystem.edgeOf =
      localCrossingEdgeFinset G side ∩
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
      ⟨(mem_localCrossingEdgeFinset_iff side _).2
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
    exact (mem_localCrossingEdgeFinset_iff side edge).1 hcrossing

/-- The edge map is injective on one facial orbit when that individual face,
rather than the whole rotation system, is two-sided. -/
theorem edgeOf_injOn_orbitFaceDarts_of_faceTwoSided
    (RS : RotationSystem V G.edgeSet) (face : OrbitFace RS)
    (hfaceTwoSided : ∀ dart, dartOrbitFace RS dart = face →
      dartOrbitFace RS dart ≠ dartOrbitFace RS (RS.alpha dart)) :
    Set.InjOn RS.edgeOf (orbitFaceDarts RS face) := by
  intro left hleft right hright hedge
  rcases RS.edge_fiber_two_cases rfl hedge.symm with heq | heq
  · exact heq.symm
  · exfalso
    have hleftFace : dartOrbitFace RS left = face :=
      (mem_orbitFaceDarts_iff RS face left).1 hleft
    have hrightFace : dartOrbitFace RS right = face :=
      (mem_orbitFaceDarts_iff RS face right).1 hright
    apply hfaceTwoSided left hleftFace
    rw [← heq, hleftFace, hrightFace]

/-- Every locally two-sided face meets an exact vertex-side boundary an even
number of times.  No statement is made about unrelated one-sided hole faces. -/
theorem even_card_crossingEdgeFinset_inter_orbitFaceBoundary_of_faceTwoSided
    (data : Data G) (side : V → Prop) (face : OrbitFace data.toRotationSystem)
    (hfaceTwoSided : ∀ dart, dartOrbitFace data.toRotationSystem dart = face →
      dartOrbitFace data.toRotationSystem dart ≠
        dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart)) :
    Even ((localCrossingEdgeFinset G side ∩
      orbitFaceBoundary data.toRotationSystem face).card) := by
  have himage :=
    image_edgeOf_orbitFaceSideTransitionDarts_eq_crossing_inter_boundary
      data side face
  rw [← himage]
  have hinjective : Set.InjOn data.toRotationSystem.edgeOf
      (orbitFaceSideTransitionDarts data.toRotationSystem side face) := by
    intro left hleft right hright hedge
    apply edgeOf_injOn_orbitFaceDarts_of_faceTwoSided
      data.toRotationSystem face hfaceTwoSided
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

/-- Cyclic successor reads the next walk vertex, including across the closing
step of a simple cycle. -/
private theorem getVert_succ_eq_getVert_finRotate
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
one quotient face.  This is a combinatorial property of the cycle itself and
does not assume that every face in the ambient open tangle is two-sided. -/
private theorem card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
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
      (dualWalkCrossingEdge_injective_of_isCycle_core
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem)
        hunique walk hcycle)]
  exact hincidentCard

/-- A nonempty exact vertex-side boundary contained in a simple facial-dual
cycle is the whole crossing set when every face actually visited by that cycle
is two-sided.  This is the bridge-safe, open-tangle version of the ordinary
dual-cycle bond theorem. -/
theorem crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset_of_supportTwoSided
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (side : V → Prop)
    (hsubset : localCrossingEdgeFinset G side ⊆
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (hnonempty : (localCrossingEdgeFinset G side).Nonempty)
    (hsupportTwoSided : ∀ face, face ∈ walk.support → ∀ dart,
      dartOrbitFace data.toRotationSystem dart = face.1 →
        dartOrbitFace data.toRotationSystem dart ≠
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart)) :
    localCrossingEdgeFinset G side =
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
  let boundary := localCrossingEdgeFinset G side
  have hcrossingInjective : Function.Injective crossing :=
    dualWalkCrossingEdge_injective_of_isCycle_core
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
      apply even_card_crossingEdgeFinset_inter_orbitFaceBoundary_of_faceTwoSided
        data side face
      intro dart hdart
      exact hsupportTwoSided (walk.getVert (step.val + 1))
        (walk.getVert_mem_support (step.val + 1)) dart hdart
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
      hunique walk seed ∈ localCrossingEdgeFinset G side
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
      hunique walk edge).1 hedge with
    ⟨step, hstepEdge⟩
  rw [← hstepEdge]
  exact hallSteps step

end GoertzelV24FramedLocalDualCycleBond

end

end Mettapedia.GraphTheory.FourColor
