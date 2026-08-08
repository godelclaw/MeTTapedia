import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport

/-!
# Exact-cut transport through one locally cubic cycle turn

The framed annular graph is not globally cubic because its interface stubs
have degree one.  Every internal chord-cycle vertex is nevertheless cubic.
This module localizes the existing cubic rotation arguments to one
three-dart fiber, then proves that the face-side label of an exact cut is
preserved when an oriented cut cycle turns through that vertex and every
other incident edge avoids the cut.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Three pairwise distinct darts exhaust one locally cubic vertex fiber. -/
theorem rho_eq_second_or_third_of_card_dartsAt_eq_three
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {first second third : RS.D}
    (hcard : (RS.dartsAt (RS.vertOf first)).card = 3)
    (hsecondBase : RS.vertOf second = RS.vertOf first)
    (hthirdBase : RS.vertOf third = RS.vertOf first)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    RS.rho first = second ∨ RS.rho first = third := by
  let vertex := RS.vertOf first
  have hfirstMem : first ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex]
  have hsecondMem : second ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex, hsecondBase]
  have hthirdMem : third ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex, hthirdBase]
  have htripleSubset : ({first, second, third} : Finset RS.D) ⊆
      RS.dartsAt vertex := by
    intro dart hdart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
    rcases hdart with rfl | rfl | rfl
    · exact hfirstMem
    · exact hsecondMem
    · exact hthirdMem
  have htripleCard : ({first, second, third} : Finset RS.D).card = 3 := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  have htripleEq : ({first, second, third} : Finset RS.D) =
      RS.dartsAt vertex := by
    apply Finset.eq_of_subset_of_card_le htripleSubset
    rw [show (RS.dartsAt vertex).card = 3 by simpa [vertex] using hcard,
      htripleCard]
  have hrhoMem : RS.rho first ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex, RS.vert_rho]
  rw [← htripleEq] at hrhoMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrhoMem
  rcases hrhoMem with hfixed | hsecond | hthird
  · have hnontrivialFinset : (RS.dartsAt vertex).Nontrivial := by
      apply Finset.one_lt_card_iff_nontrivial.mp
      rw [show (RS.dartsAt vertex).card = 3 by simpa [vertex] using hcard]
      omega
    have hnontrivial : (RS.dartsAt vertex : Set RS.D).Nontrivial := by
      simpa only [Finset.coe_sort_coe] using hnontrivialFinset
    exact False.elim
      ((rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
        hnontrivial hfirstMem hfixed)
  · exact Or.inl hsecond
  · exact Or.inr hthird

/-- In a locally cubic cyclic dart fiber, either of two distinct darts is
the immediate successor of the other. -/
theorem rho_eq_or_rho_eq_of_card_dartsAt_eq_three
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {first second : RS.D}
    (hcard : (RS.dartsAt (RS.vertOf first)).card = 3)
    (hbase : RS.vertOf second = RS.vertOf first)
    (hne : first ≠ second) :
    RS.rho first = second ∨ RS.rho second = first := by
  by_cases hforward : RS.rho first = second
  · exact Or.inl hforward
  · let third := RS.rho first
    have hthirdBase : RS.vertOf third = RS.vertOf first :=
      RS.vert_rho first
    have hfirstThird : first ≠ third := by
      have hfirstMem : first ∈ RS.dartsAt (RS.vertOf first) := by
        simp [RotationSystem.dartsAt]
      have hnontrivialFinset :
          (RS.dartsAt (RS.vertOf first)).Nontrivial := by
        apply Finset.one_lt_card_iff_nontrivial.mp
        rw [hcard]
        omega
      have hnontrivial :
          (RS.dartsAt (RS.vertOf first) : Set RS.D).Nontrivial := by
        simpa only [Finset.coe_sort_coe] using hnontrivialFinset
      exact ((rho_isCycleOn_dartsAt RS hrotation
        (RS.vertOf first)).apply_ne hnontrivial hfirstMem).symm
    rcases rho_eq_second_or_third_of_card_dartsAt_eq_three
        RS hrotation (first := second) (second := first) (third := third)
        (by simpa [hbase] using hcard)
        hbase.symm (hthirdBase.trans hbase.symm)
        hne.symm (fun heq => hforward heq.symm)
        hfirstThird with hback | hthird
    · exact Or.inr hback
    · exfalso
      apply hne
      apply RS.rho.injective
      rw [hthird]

/-- Once the first step in one locally cubic rotation fiber is fixed, the
remaining two steps are forced. -/
theorem rho_three_cycle_of_eq_second_of_card_dartsAt_eq_three
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {first second third : RS.D}
    (hcard : (RS.dartsAt (RS.vertOf first)).card = 3)
    (hsecondBase : RS.vertOf second = RS.vertOf first)
    (hthirdBase : RS.vertOf third = RS.vertOf first)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirst : RS.rho first = second) :
    RS.rho second = third ∧ RS.rho third = first := by
  have hnext := rho_eq_second_or_third_of_card_dartsAt_eq_three
    RS hrotation (first := second) (second := third) (third := first)
    (by simpa [hsecondBase] using hcard)
    (hthirdBase.trans hsecondBase.symm) hsecondBase.symm
    hsecondThird hfirstSecond.symm hfirstThird.symm
  have hfirstMem : first ∈ RS.dartsAt (RS.vertOf first) := by
    simp [RotationSystem.dartsAt]
  have hcubeRaw :=
    (rho_isCycleOn_dartsAt RS hrotation
      (RS.vertOf first)).pow_card_apply hfirstMem
  have hcube : RS.rho (RS.rho (RS.rho first)) = first := by
    rw [hcard] at hcubeRaw
    simpa [pow_succ] using hcubeRaw
  rcases hnext with hsecond | hback
  · rw [hfirst, hsecond] at hcube
    exact ⟨hsecond, hcube⟩
  · rw [hfirst, hback, hfirst] at hcube
    exact False.elim (hfirstSecond hcube.symm)

/-- The exact-cut label on one oriented side of a cycle is preserved through
one locally cubic turn.  Only the unused dart between the two cycle darts
must avoid the cut. -/
theorem labels_eq_of_cutCycle_turn_at_card_dartsAt_eq_three
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (previous outgoing : RS.D)
    (hcard : (RS.dartsAt (RS.vertOf outgoing)).card = 3)
    (hbase : RS.vertOf outgoing = RS.vertOf (RS.alpha previous))
    (hnonback : RS.alpha previous ≠ outgoing)
    (hother : ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf outgoing →
      dart ≠ RS.alpha previous → dart ≠ outgoing →
      ¬cut (RS.edgeOf dart)) :
    labels (dartOrbitFace RS previous) =
      labels (dartOrbitFace RS outgoing) := by
  let arrived := RS.alpha previous
  have harrivedBase : RS.vertOf arrived = RS.vertOf outgoing :=
    hbase.symm
  have hcardArrived : (RS.dartsAt (RS.vertOf arrived)).card = 3 := by
    simpa [harrivedBase] using hcard
  by_cases hforward : RS.rho arrived = outgoing
  · calc
      labels (dartOrbitFace RS previous) =
          labels (dartOrbitFace RS (RS.phi previous)) :=
        congrArg labels (dartOrbitFace_phi_eq RS previous).symm
      _ = labels (dartOrbitFace RS outgoing) := by
        rw [RotationSystem.phi_apply, hforward]
  · have hreverse : RS.rho outgoing = arrived := by
      rcases rho_eq_or_rho_eq_of_card_dartsAt_eq_three
          RS hrotation hcardArrived harrivedBase.symm hnonback with
        hforward' | hreverse
      · exact False.elim (hforward hforward')
      · exact hreverse
    let third := RS.rho arrived
    have hthirdBase : RS.vertOf third = RS.vertOf outgoing :=
      (RS.vert_rho arrived).trans harrivedBase
    have hthirdNeArrived : third ≠ arrived := by
      have harrivedMem : arrived ∈ RS.dartsAt (RS.vertOf arrived) := by
        simp [RotationSystem.dartsAt]
      have hnontrivialFinset :
          (RS.dartsAt (RS.vertOf arrived)).Nontrivial := by
        apply Finset.one_lt_card_iff_nontrivial.mp
        rw [hcardArrived]
        omega
      have hnontrivial :
          (RS.dartsAt (RS.vertOf arrived) : Set RS.D).Nontrivial := by
        simpa only [Finset.coe_sort_coe] using hnontrivialFinset
      exact (rho_isCycleOn_dartsAt RS hrotation
        (RS.vertOf arrived)).apply_ne hnontrivial harrivedMem
    have hthirdNeOutgoing : third ≠ outgoing := hforward
    have hthirdNotCut : ¬cut (RS.edgeOf third) :=
      hother third hthirdBase hthirdNeArrived hthirdNeOutgoing
    have hthirdRho : RS.rho third = outgoing :=
      (rho_three_cycle_of_eq_second_of_card_dartsAt_eq_three
        RS hrotation (first := outgoing) (second := arrived)
        (third := third) hcard harrivedBase hthirdBase
        hnonback.symm hthirdNeOutgoing.symm hthirdNeArrived.symm hreverse).2
    have htransport := labels_eq_rho_of_not_cut
      RS labels cut hexact third hthirdNotCut
    calc
      labels (dartOrbitFace RS previous) =
          labels (dartOrbitFace RS (RS.phi previous)) :=
        congrArg labels (dartOrbitFace_phi_eq RS previous).symm
      _ = labels (dartOrbitFace RS third) := by
        rfl
      _ = labels (dartOrbitFace RS outgoing) := by
        rw [hthirdRho] at htransport
        exact htransport

end RotationSystem

end Mettapedia.GraphTheory.FourColor
