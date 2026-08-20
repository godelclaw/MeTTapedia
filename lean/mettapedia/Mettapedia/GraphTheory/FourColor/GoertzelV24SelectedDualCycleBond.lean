import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedLocalDualCycleBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleSeparator

/-!
# Exact bonds for literally selected dual-cycle crossings

The open annular carrier is not globally face-two-sided.  A selected dual
cycle supported on ordinary interior faces nevertheless has enough local
two-sidedness for the usual bond propagation: if a nonempty exact vertex-side
boundary is contained in its literally selected crossings, it contains every
selected crossing.

This is the selected-edge counterpart of
`crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset_of_supportTwoSided`.
It does not assume unique shared edges between all ambient face pairs; the
cycle carries the actual crossed edge at every step.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24SelectedDualCycleSeparator
open GoertzelV24SelectedDualCycleSeparator.SelectedDualCycle
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24SelectedDualCycleBond

local instance selectedDualCycleBondEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Orienting a side-crossing edge from the chosen side to its complement is
an equivalence between outgoing side darts and the exact finite boundary. -/
noncomputable def crossingSideDartEquivLocalCrossingEdge (side : V → Prop) :
    GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side ≃
      {edge : G.edgeSet // edge ∈ localCrossingEdgeFinset G side} := by
  classical
  let toCrossing :
      GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side →
        {edge : G.edgeSet // edge ∈ localCrossingEdgeFinset G side} :=
    fun dart =>
      ⟨⟨dart.1.edge, dart.1.edge_mem⟩,
        (mem_localCrossingEdgeFinset_iff side _).2
          ⟨dart.1.fst, dart.1.snd,
            (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
            (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
            dart.2.1, dart.2.2⟩⟩
  have hinjective : Function.Injective toCrossing := by
    intro left right heq
    apply GoertzelV24CubicSmallBoundaryCycle.crossingSideDart_edge_injective side
    exact congrArg (fun edge => edge.1) heq
  refine Equiv.ofBijective toCrossing ⟨hinjective, ?_⟩
  rintro ⟨edge, hedge⟩
  rcases (mem_localCrossingEdgeFinset_iff side edge).1 hedge with
    ⟨left, right, hleftEdge, hrightEdge, hleftSide, hrightSide⟩
  have hne : left ≠ right := by
    intro heq
    exact hrightSide (heq ▸ hleftSide)
  have hedgeValue : edge.1 = s(left, right) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hleftEdge hrightEdge hne
  have hadj : G.Adj left right :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  let dart : GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side :=
    ⟨⟨(left, right), hadj⟩, hleftSide, hrightSide⟩
  refine ⟨dart, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hedgeValue.symm

/-- The finite exact boundary and its uniquely outward-oriented darts have
the same cardinality. -/
theorem card_localCrossingEdgeFinset_eq_crossingSideDart (side : V → Prop) :
    (localCrossingEdgeFinset G side).card =
      Fintype.card
        (GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side) := by
  calc
    (localCrossingEdgeFinset G side).card =
        Fintype.card {edge : G.edgeSet //
          edge ∈ localCrossingEdgeFinset G side} := (Fintype.card_coe _).symm
    _ = Fintype.card
        (GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side) :=
      Fintype.card_congr
        (crossingSideDartEquivLocalCrossingEdge side).symm

/-- Cyclic successor reads the next walk vertex, including at the closing
step. -/
private theorem getVert_succ_eq_getVert_finRotate
    (data : Data G)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start)
    (step : Fin cycle.walk.length) :
    cycle.walk.getVert (step.val + 1) =
      cycle.walk.getVert (finRotate cycle.walk.length step).val := by
  have hpositive : 0 < cycle.walk.length :=
    lt_of_lt_of_le (by omega) cycle.isCycle.three_le_length
  have hone : 1 < cycle.walk.length :=
    lt_of_lt_of_le (by omega) cycle.isCycle.three_le_length
  letI : NeZero cycle.walk.length := ⟨Nat.ne_of_gt hpositive⟩
  by_cases hnext : step.val + 1 < cycle.walk.length
  · have hrotate : (finRotate cycle.walk.length step).val = step.val + 1 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hnext]
    rw [hrotate]
  · have hlast : step.val + 1 = cycle.walk.length := by omega
    have hrotate : (finRotate cycle.walk.length step).val = 0 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, hlast, Nat.mod_self]
    rw [hlast, hrotate, cycle.walk.getVert_length, cycle.walk.getVert_zero]

/-- At most two literally selected crossings of a simple dual cycle occur
on any one ambient face. -/
private theorem card_crossingEdges_inter_faceBoundary_le_two
    (data : Data G)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start)
    (face : OrbitFace data.toRotationSystem) :
    (cycle.crossingEdges ∩
      orbitFaceBoundary data.toRotationSystem face).card ≤ 2 := by
  classical
  let incidentSteps : Finset (Fin cycle.walk.length) :=
    Finset.univ.filter fun step =>
      cycle.crossingEdge step ∈ orbitFaceBoundary data.toRotationSystem face
  let leftSteps : Finset (Fin cycle.walk.length) :=
    Finset.univ.filter fun step =>
      (cycle.walk.getVert step.val).1 = face
  let rightSteps : Finset (Fin cycle.walk.length) :=
    Finset.univ.filter fun step =>
      (cycle.walk.getVert (step.val + 1)).1 = face
  have hincidentSubset : incidentSteps ⊆ leftSteps ∪ rightSteps := by
    intro step hstep
    have hboundary : cycle.crossingEdge step ∈
        orbitFaceBoundary data.toRotationSystem face :=
      (Finset.mem_filter.1 hstep).2
    let left := cycle.walk.getVert step.val
    let right := cycle.walk.getVert (step.val + 1)
    have hadj := cycle.walk.adj_getVert_succ step.isLt
    have hfaces : left.1 ≠ right.1 := by
      intro heq
      exact hadj.ne (Subtype.ext heq)
    have hleft : cycle.crossingEdge step ∈
        orbitFaceBoundary data.toRotationSystem left.1 :=
      cycle.crossingEdge_mem_leftFace step
    have hright : cycle.crossingEdge step ∈
        orbitFaceBoundary data.toRotationSystem right.1 :=
      cycle.crossingEdge_mem_rightFace step
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
    exact cycle.isCycle.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext (hfirstFace.trans hsecondFace.symm))
  have hrightCard : rightSteps.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    have hfirstFace := (Finset.mem_filter.1 hfirst).2
    have hsecondFace := (Finset.mem_filter.1 hsecond).2
    apply Fin.ext
    have hvalues := cycle.isCycle.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext (hfirstFace.trans hsecondFace.symm))
    omega
  have hincidentCard : incidentSteps.card ≤ 2 := by
    calc
      incidentSteps.card ≤ (leftSteps ∪ rightSteps).card :=
        Finset.card_le_card hincidentSubset
      _ ≤ leftSteps.card + rightSteps.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have himage : incidentSteps.image cycle.crossingEdge =
      cycle.crossingEdges ∩ orbitFaceBoundary data.toRotationSystem face := by
    ext edge
    constructor
    · intro hedge
      rcases Finset.mem_image.1 hedge with ⟨step, hstep, hstepEdge⟩
      exact Finset.mem_inter.2 ⟨
        (cycle.mem_crossingEdges_iff edge).2 ⟨step, hstepEdge⟩,
        hstepEdge ▸ (Finset.mem_filter.1 hstep).2⟩
    · intro hedge
      rcases Finset.mem_inter.1 hedge with ⟨hcrossing, hboundary⟩
      rcases (cycle.mem_crossingEdges_iff edge).1 hcrossing with
        ⟨step, hstepEdge⟩
      exact Finset.mem_image.2 ⟨step,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hstepEdge ▸ hboundary⟩,
        hstepEdge⟩
  rw [← himage,
    Finset.card_image_of_injective _
      (cycle.crossingEdge_injective
        (orbitFace_incidence_le_two data.toRotationSystem))]
  exact hincidentCard

/-- A nonempty exact side boundary contained in the literal crossings of a
simple selected dual cycle is the whole selected crossing set, provided only
the faces visited by the cycle are two-sided. -/
theorem crossingEdgeFinset_eq_crossingEdges_of_isCycle_of_subset_of_supportTwoSided
    (data : Data G)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start)
    (side : V → Prop)
    (hsubset : localCrossingEdgeFinset G side ⊆ cycle.crossingEdges)
    (hnonempty : (localCrossingEdgeFinset G side).Nonempty)
    (hsupportTwoSided : ∀ face, face ∈ cycle.walk.support → ∀ dart,
      dartOrbitFace data.toRotationSystem dart = face.1 →
        dartOrbitFace data.toRotationSystem dart ≠
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart)) :
    localCrossingEdgeFinset G side = cycle.crossingEdges := by
  classical
  let crossing := cycle.crossingEdge
  let removed := cycle.crossingEdges
  let boundary := localCrossingEdgeFinset G side
  have hcrossingInjective : Function.Injective crossing :=
    cycle.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem)
  have htwoLength : 2 ≤ cycle.walk.length :=
    le_trans (by omega) cycle.isCycle.three_le_length
  have hrotateNe (step : Fin cycle.walk.length) :
      finRotate cycle.walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support, support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hsuccessor (step : Fin cycle.walk.length)
      (hstepBoundary : crossing step ∈ boundary) :
      crossing (finRotate cycle.walk.length step) ∈ boundary := by
    let face := (cycle.walk.getVert (step.val + 1)).1
    let boundaryAtFace := boundary ∩
      orbitFaceBoundary data.toRotationSystem face
    let removedAtFace := removed ∩
      orbitFaceBoundary data.toRotationSystem face
    have hstepRemoved : crossing step ∈ removed :=
      (cycle.mem_crossingEdges_iff _).2 ⟨step, rfl⟩
    have hnextRemoved : crossing (finRotate cycle.walk.length step) ∈ removed :=
      (cycle.mem_crossingEdges_iff _).2
        ⟨finRotate cycle.walk.length step, rfl⟩
    have hstepFace : crossing step ∈
        orbitFaceBoundary data.toRotationSystem face :=
      cycle.crossingEdge_mem_rightFace step
    have hnextFace : crossing (finRotate cycle.walk.length step) ∈
        orbitFaceBoundary data.toRotationSystem face := by
      have hmem := cycle.crossingEdge_mem_leftFace
        (finRotate cycle.walk.length step)
      rw [← getVert_succ_eq_getVert_finRotate data cycle step] at hmem
      exact hmem
    have hedgesNe : crossing step ≠
        crossing (finRotate cycle.walk.length step) := by
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
      exact hsupportTwoSided (cycle.walk.getVert (step.val + 1))
        (cycle.walk.getVert_mem_support (step.val + 1)) dart hdart
    have hboundaryAtFacePositive : 0 < boundaryAtFace.card := by
      apply Finset.card_pos.2
      exact ⟨crossing step,
        Finset.mem_inter.2 ⟨hstepBoundary, hstepFace⟩⟩
    have hremovedAtFaceCardLe : removedAtFace.card ≤ 2 :=
      card_crossingEdges_inter_faceBoundary_le_two data cycle face
    have hboundaryAtFaceCardLe : boundaryAtFace.card ≤ 2 :=
      le_trans (Finset.card_le_card hboundaryAtFaceSubset)
        hremovedAtFaceCardLe
    have hboundaryAtFaceCard : boundaryAtFace.card = 2 := by
      rcases hboundaryAtFaceEven with ⟨half, hhalf⟩
      omega
    have hpairSubset :
        {crossing step, crossing (finRotate cycle.walk.length step)} ⊆
          removedAtFace := by
      intro edge hedge
      rw [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl
      · exact Finset.mem_inter.2 ⟨hstepRemoved, hstepFace⟩
      · exact Finset.mem_inter.2 ⟨hnextRemoved, hnextFace⟩
    have hpairCard :
        ({crossing step, crossing (finRotate cycle.walk.length step)} :
          Finset G.edgeSet).card = 2 := Finset.card_pair hedgesNe
    have hremovedAtFaceCard : removedAtFace.card = 2 := by
      have hlower : 2 ≤ removedAtFace.card := by
        rw [← hpairCard]
        exact Finset.card_le_card hpairSubset
      omega
    have hfacesEqual : boundaryAtFace = removedAtFace := by
      apply Finset.eq_of_subset_of_card_le hboundaryAtFaceSubset
      omega
    have hnextBoundaryAtFace :
        crossing (finRotate cycle.walk.length step) ∈ boundaryAtFace := by
      rw [hfacesEqual]
      exact Finset.mem_inter.2 ⟨hnextRemoved, hnextFace⟩
    exact (Finset.mem_inter.1 hnextBoundaryAtFace).1
  rcases hnonempty with ⟨seedEdge, hseedBoundary⟩
  have hseedRemoved := hsubset hseedBoundary
  rcases (cycle.mem_crossingEdges_iff seedEdge).1 hseedRemoved with
    ⟨seed, hseedEdge⟩
  have hseed : crossing seed ∈ boundary := by
    change cycle.crossingEdge seed ∈ localCrossingEdgeFinset G side
    rw [hseedEdge]
    exact hseedBoundary
  have hallSteps (target : Fin cycle.walk.length) :
      crossing target ∈ boundary := by
    have hsameCycle :
        (finRotate cycle.walk.length).SameCycle seed target :=
      (isCycle_finRotate_of_le htwoLength).sameCycle
        (hrotateNe seed) (hrotateNe target)
    rcases hsameCycle.exists_nat_pow_eq with ⟨power, hpower⟩
    have hiterate : ∀ exponent : Nat,
        crossing (((finRotate cycle.walk.length) ^ exponent) seed) ∈
          boundary := by
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
  rcases (cycle.mem_crossingEdges_iff edge).1 hedge with ⟨step, hstepEdge⟩
  rw [← hstepEdge]
  exact hallSteps step

end GoertzelV24SelectedDualCycleBond

end

end Mettapedia.GraphTheory.FourColor
