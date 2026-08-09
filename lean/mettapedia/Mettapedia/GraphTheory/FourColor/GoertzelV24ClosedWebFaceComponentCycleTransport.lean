import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFaceTracing
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleTurn
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleWalkTransport

/-!
# Wall-avoiding face transport at a cubic cycle turn

The chord wall is a primal simple cycle, whereas the generic dual-cycle
separator theorem applies to a facial-dual cycle.  The correct local bridge is
smaller: at a cubic cycle turn, the unused dart is outside the wall, so the
two faces on the chosen side of the turn are connected in the facial dual
with the wall removed.  Iterating this fact transports one selected face
component around the whole primal cycle.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebFaceComponentCycleTransport

open GoertzelV24ClosedWebFaceTracing
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- One locally cubic nonbacktracking cycle turn stays connected in the
facial dual after the wall edges are removed.  The proof follows the two
possible orientations of the three-dart rotation fiber. -/
theorem faceAdjacencyAvoiding_reachable_of_faceCutCycleTurn
    (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS)
    (hrotation : VertexRotationCyclic RS)
    (wall : Finset E)
    {previous outgoing : RS.D}
    (hbase : RS.vertOf outgoing = RS.vertOf (RS.alpha previous))
    (hnonback : RS.alpha previous ≠ outgoing)
    (hcard : (RS.dartsAt (RS.vertOf outgoing)).card = 3)
    (hother : ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf outgoing →
      dart ≠ RS.alpha previous → dart ≠ outgoing →
      RS.edgeOf dart ∉ wall) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
      (orbitFaceVertex RS previous) (orbitFaceVertex RS outgoing) := by
  let arrived := RS.alpha previous
  have harrivedBase : RS.vertOf arrived = RS.vertOf outgoing :=
    hbase.symm
  have hcardArrived : (RS.dartsAt (RS.vertOf arrived)).card = 3 := by
    simpa [arrived, harrivedBase] using hcard
  by_cases hforward : RS.rho arrived = outgoing
  · have hface : dartOrbitFace RS previous =
        dartOrbitFace RS outgoing := by
      calc
        dartOrbitFace RS previous = dartOrbitFace RS (RS.phi previous) :=
          (dartOrbitFace_phi_eq RS previous).symm
        _ = dartOrbitFace RS (RS.rho arrived) := by
          simp [RotationSystem.phi_apply, arrived]
        _ = dartOrbitFace RS outgoing := by rw [hforward]
    exact (by simpa [orbitFaceVertex, hface])
  · have hreverse : RS.rho outgoing = arrived := by
      rcases RotationSystem.rho_eq_or_rho_eq_of_card_dartsAt_eq_three
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
    have hthirdAway : RS.edgeOf third ∉ wall :=
      hother third hthirdBase hthirdNeArrived hthirdNeOutgoing
    have hthirdRho : RS.rho third = outgoing :=
      (RotationSystem.rho_three_cycle_of_eq_second_of_card_dartsAt_eq_three
        RS hrotation (first := outgoing) (second := arrived)
        (third := third) hcard harrivedBase hthirdBase
        hnonback.symm hthirdNeOutgoing.symm hthirdNeArrived.symm hreverse).2
    have hstep := faceAdjacencyAvoiding_reachable_of_rho
      RS htwoSided wall third hthirdAway
    have hfirst : orbitFaceVertex RS previous =
        orbitFaceVertex RS third := by
      apply Subtype.ext
      calc
        dartOrbitFace RS previous = dartOrbitFace RS (RS.phi previous) :=
          (dartOrbitFace_phi_eq RS previous).symm
        _ = dartOrbitFace RS third := by
          simp [RotationSystem.phi_apply, third, arrived]
    have hlast : orbitFaceVertex RS (RS.rho third) =
        orbitFaceVertex RS outgoing := by rw [hthirdRho]
    exact hfirst ▸ hstep.trans (by simpa [hlast])

/-! Hole-free face regions also have a direct primal consequence.  At a
wall-free vertex, all incident face choices are connected by rotation; hence
a vertex incident with a forbidden hole face cannot belong to the selected
face-component side. -/

theorem not_faceComponentSide_of_holeFree_incident_dart
    (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS)
    (hrotation : VertexRotationCyclic RS)
    (wall : Finset E)
    (seed hole : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (dart : RS.D)
    (hface : orbitFaceVertex RS dart = hole)
    (havoid : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf dart → RS.edgeOf incident ∉ wall)
    (hfree : ¬ (faceAdjacencyAvoiding
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).Reachable seed hole) :
    ¬ faceComponentSide RS wall seed (RS.vertOf dart) := by
  intro hside
  rcases hside with ⟨incident, hincident, hreach⟩
  have hsame : RS.rho.SameCycle incident dart :=
    hrotation incident dart (hincident.trans rfl)
  have hconnect :=
    faceAdjacencyAvoiding_reachable_of_rho_sameCycle_of_vertex_avoids
      RS htwoSided wall hsame (by
        intro other hother
        exact havoid other (hother.trans hincident))
  apply hfree
  have htoHole :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        (orbitFaceVertex RS dart) hole := by
    rw [hface]
  exact hreach.trans (hconnect.trans htoHole)

/-! The one-step result iterates over a simple graph cycle. -/

namespace SimpleGraphDartRotation.Data

local instance faceComponentCycleGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

theorem faceComponentSide_of_mem_cycle_darts
    (graphData : SimpleGraphDartRotation.Data G)
    {root : V} (cycle : G.Walk root root)
    (hcycle : cycle.IsCycle)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hlocalCubic : ∀ dart ∈ cycle.darts,
      (graphData.toRotationSystem.dartsAt
        (graphData.toRotationSystem.vertOf dart)).card = 3)
    (wall : Finset G.edgeSet)
    (hwall : ∀ edge : G.edgeSet,
      edge ∈ wall ↔ edge.1 ∈ cycle.edges)
    (seed : AmbientFace (Finset.univ : Finset
      (OrbitFace graphData.toRotationSystem)))
    (hseed :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)) wall).Reachable
        seed
        (orbitFaceVertex graphData.toRotationSystem
          (cycle.firstDart hcycle.not_nil)))
    {target : G.Dart} (htarget : target ∈ cycle.darts) :
    faceComponentSide graphData.toRotationSystem wall seed target.fst := by
  let RS := graphData.toRotationSystem
  have hdartsNe : cycle.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hcycle.not_nil
  have hchain :=
    SimpleGraphDartRotation.Data.isChain_faceCutCycleTurnStep_darts_of_local_cubic
      graphData
    cycle hcycle hlocalCubic
  have hchainWall : cycle.darts.IsChain
      (RS.FaceCutCycleTurnStep (fun edge => edge ∈ wall)) := by
    simpa [hwall] using hchain
  have hlist : cycle.darts.head hdartsNe :: cycle.darts.tail = cycle.darts := by
    apply List.cons_head?_tail
    rw [List.head?_eq_some_head hdartsNe]
    simp
  have htargetList : target ∈
      (cycle.darts.head hdartsNe :: cycle.darts.tail : List RS.D) := by
    change target ∈ cycle.darts.head hdartsNe :: cycle.darts.tail
    rw [hlist]
    exact htarget
  have hchainHead :
      (cycle.darts.head hdartsNe :: cycle.darts.tail : List RS.D).IsChain
        (RS.FaceCutCycleTurnStep (fun edge => edge ∈ wall)) := by
    change (cycle.darts.head hdartsNe :: cycle.darts.tail).IsChain
      (graphData.toRotationSystem.FaceCutCycleTurnStep
        (fun edge => edge ∈ wall))
    rw [hlist]
    exact hchainWall
  have hhead : cycle.darts.head hdartsNe =
      cycle.firstDart hcycle.not_nil := by
    exact cycle.firstDart_eq_head_darts hcycle.not_nil |>.symm
  have hreachable_head :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        seed (orbitFaceVertex RS (cycle.darts.head hdartsNe)) := by
    rw [hhead]
    exact hseed
  have hreachable_mem : ∀ (first : RS.D) (rest : List RS.D),
      (first :: rest).IsChain (RS.FaceCutCycleTurnStep
        (fun edge => edge ∈ wall)) →
      target ∈ first :: rest →
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        (orbitFaceVertex RS first) (orbitFaceVertex RS target) := by
    intro first rest
    induction rest generalizing first with
    | nil =>
        intro _ hmem
        rcases List.mem_singleton.mp hmem with rfl
        exact SimpleGraph.Reachable.refl _
    | cons second rest ih =>
        intro hturnChain hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact SimpleGraph.Reachable.refl _
        · have hstep : RS.FaceCutCycleTurnStep
              (fun edge => edge ∈ wall) first second :=
            hturnChain.rel
          have hsecond :
              (faceAdjacencyAvoiding
                (orbitFaceBoundary RS)
                (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
                (orbitFaceVertex RS first) (orbitFaceVertex RS second) :=
            faceAdjacencyAvoiding_reachable_of_faceCutCycleTurn
              RS htwoSided hrotation wall hstep.1 hstep.2.1
              hstep.2.2.1 hstep.2.2.2
          exact hsecond.trans (ih second hturnChain.of_cons htail)
  have hreachable :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        seed (orbitFaceVertex RS target) := by
    exact hreachable_head.trans
      (hreachable_mem (cycle.darts.head hdartsNe)
        (cycle.darts.tail) hchainHead htargetList)
  exact ⟨target, rfl, hreachable⟩

/-! A selected face component therefore contains the primal cycle itself on
its vertex side.  This is the first of the two cycle witnesses needed by the
cyclic-cut constructor; no planar picture is used. -/

theorem hasCycleOnSide_of_faceComponentSide_cycle
    (graphData : SimpleGraphDartRotation.Data G)
    {root : V} (cycle : G.Walk root root)
    (hcycle : cycle.IsCycle)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hlocalCubic : ∀ dart ∈ cycle.darts,
      (graphData.toRotationSystem.dartsAt
        (graphData.toRotationSystem.vertOf dart)).card = 3)
    (wall : Finset G.edgeSet)
    (hwall : ∀ edge : G.edgeSet,
      edge ∈ wall ↔ edge.1 ∈ cycle.edges)
    (seed : AmbientFace (Finset.univ : Finset
      (OrbitFace graphData.toRotationSystem)))
    (hseed :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)) wall).Reachable
        seed
        (orbitFaceVertex graphData.toRotationSystem
          (cycle.firstDart hcycle.not_nil))) :
    HasCycleOnSide G
      (faceComponentSide graphData.toRotationSystem wall seed) := by
  let RS := graphData.toRotationSystem
  have hfirst : cycle.firstDart hcycle.not_nil ∈ cycle.darts :=
    cycle.firstDart_mem_darts hcycle.not_nil
  have hfirstSide : faceComponentSide RS wall seed root := by
    have hside := faceComponentSide_of_mem_cycle_darts
      graphData cycle hcycle hrotation htwoSided hlocalCubic wall hwall
      seed hseed hfirst
    simpa [RS] using hside
  refine ⟨root, hfirstSide, cycle, hcycle, ?_⟩
  intro vertex hvertex
  by_cases hroot : vertex = root
  · simpa [hroot] using hfirstSide
  · have hneLast : vertex ≠ cycle.support.getLast (by simp) := by
      rw [cycle.getLast_support]
      exact hroot
    have hdrop : vertex ∈ cycle.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hvertex hneLast
    rw [← cycle.map_fst_darts] at hdrop
    rcases List.mem_map.mp hdrop with ⟨dart, hdart, hfst⟩
    have hside := faceComponentSide_of_mem_cycle_darts
      graphData cycle hcycle hrotation htwoSided hlocalCubic wall hwall
      seed hseed hdart
    simpa [RS, hfst] using hside

end SimpleGraphDartRotation.Data

namespace SimpleGraphDartRotation.Data

local instance faceComponentCycleGraphEdgeSetDecidableEqOpposite :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! The opposite facial side is transported by reversing the local turn.  At
the common vertex of consecutive cycle darts `first, second`, the flipped
pair `alpha second, alpha first` has exactly the same unused third dart. -/

theorem hasCycleOnSide_of_faceComponentSide_cycle_opposite
    (graphData : SimpleGraphDartRotation.Data G)
    {root : V} (cycle : G.Walk root root)
    (hcycle : cycle.IsCycle)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hlocalCubic : ∀ dart ∈ cycle.darts,
      (graphData.toRotationSystem.dartsAt
        (graphData.toRotationSystem.vertOf dart)).card = 3)
    (wall : Finset G.edgeSet)
    (hwall : ∀ edge : G.edgeSet,
      edge ∈ wall ↔ edge.1 ∈ cycle.edges)
    (seed : AmbientFace (Finset.univ : Finset
      (OrbitFace graphData.toRotationSystem)))
    (hseed :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)) wall).Reachable
        seed
        (orbitFaceVertex graphData.toRotationSystem
          (graphData.toRotationSystem.rho
            (cycle.firstDart hcycle.not_nil)))) :
    HasCycleOnSide G
      (faceComponentSide graphData.toRotationSystem wall seed) := by
  let RS := graphData.toRotationSystem
  have hdartsNe : cycle.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hcycle.not_nil
  have hchain :=
    SimpleGraphDartRotation.Data.isChain_faceCutCycleTurnStep_darts_of_local_cubic
      graphData cycle hcycle hlocalCubic
  have hchainWall : cycle.darts.IsChain
      (RS.FaceCutCycleTurnStep (fun edge => edge ∈ wall)) := by
    simpa [hwall] using hchain
  have hlist : cycle.darts.head hdartsNe :: cycle.darts.tail = cycle.darts := by
    apply List.cons_head?_tail
    rw [List.head?_eq_some_head hdartsNe]
    simp
  have hchainHead :
      (cycle.darts.head hdartsNe :: cycle.darts.tail : List RS.D).IsChain
        (RS.FaceCutCycleTurnStep (fun edge => edge ∈ wall)) := by
    change (cycle.darts.head hdartsNe :: cycle.darts.tail).IsChain
      (graphData.toRotationSystem.FaceCutCycleTurnStep
        (fun edge => edge ∈ wall))
    rw [hlist]
    exact hchainWall
  have hhead : cycle.darts.head hdartsNe =
      cycle.firstDart hcycle.not_nil := by
    exact cycle.firstDart_eq_head_darts hcycle.not_nil |>.symm
  have hreachable_mem : ∀ (first : RS.D) (rest : List RS.D)
      (target : RS.D),
      (first :: rest).IsChain (RS.FaceCutCycleTurnStep
        (fun edge => edge ∈ wall)) →
      target ∈ first :: rest →
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        (orbitFaceVertex RS (RS.rho first))
        (orbitFaceVertex RS (RS.rho target)) := by
    intro first rest target
    induction rest generalizing first with
    | nil =>
        intro _ hmem
        rcases List.mem_singleton.mp hmem with rfl
        exact SimpleGraph.Reachable.refl _
    | cons second rest ih =>
        intro hturnChain hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact SimpleGraph.Reachable.refl _
        · have hstep : RS.FaceCutCycleTurnStep
              (fun edge => edge ∈ wall) first second :=
            hturnChain.rel
          have hsecond :
              (faceAdjacencyAvoiding
                (orbitFaceBoundary RS)
                (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
                (orbitFaceVertex RS (RS.rho first))
                (orbitFaceVertex RS (RS.rho second)) := by
            have hbaseOpp : RS.vertOf (RS.alpha first) =
                RS.vertOf (RS.alpha (RS.alpha second)) := by
              simpa [RS.alpha_involutive] using hstep.1.symm
            have hnonbackOpp : RS.alpha (RS.alpha second) ≠
                RS.alpha first := by
              simpa only [RS.alpha_involutive] using hstep.2.1.symm
            have hotherOpp : ∀ dart : RS.D,
                RS.vertOf dart = RS.vertOf (RS.alpha first) →
                dart ≠ RS.alpha (RS.alpha second) →
                dart ≠ RS.alpha first →
                RS.edgeOf dart ∉ wall := by
              intro dart hdart hneSecond hneFirst
              apply hstep.2.2.2 dart
              · calc
                  RS.vertOf dart = RS.vertOf (RS.alpha first) := hdart
                  _ = RS.vertOf second := by
                    simpa only [RS.alpha_involutive] using hstep.1.symm
              · exact hneFirst
              · simpa only [RS.alpha_involutive] using hneSecond
            have hcardOpp :
                (RS.dartsAt (RS.vertOf (RS.alpha first))).card = 3 := by
              simpa only [hstep.1] using hstep.2.2.1
            have hturnOpp :=
              faceAdjacencyAvoiding_reachable_of_faceCutCycleTurn
                RS htwoSided hrotation wall
                (previous := RS.alpha second)
                (outgoing := RS.alpha first)
                hbaseOpp hnonbackOpp hcardOpp hotherOpp
            have hturnOpp' :
                (faceAdjacencyAvoiding
                  (orbitFaceBoundary RS)
                  (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
                  (orbitFaceVertex RS (RS.rho second))
                  (orbitFaceVertex RS (RS.rho first)) := by
              simpa only [orbitFaceVertex_alpha_eq_orbitFaceVertex_rho] using
                hturnOpp
            exact hturnOpp'.symm
          exact hsecond.trans
            (ih second hturnChain.of_cons htail)
  have hreachable_to : ∀ (target : RS.D), target ∈ cycle.darts →
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        seed (orbitFaceVertex RS (RS.rho target)) := by
    intro target htarget
    have htargetList : target ∈
        (cycle.darts.head hdartsNe :: cycle.darts.tail : List RS.D) := by
      change target ∈ cycle.darts.head hdartsNe :: cycle.darts.tail
      rw [hlist]
      exact htarget
    have htransport := hreachable_mem (cycle.darts.head hdartsNe)
      (cycle.darts.tail) target hchainHead htargetList
    rw [hhead] at htransport
    exact hseed.trans htransport
  have hfirstSide : faceComponentSide RS wall seed root := by
    refine ⟨RS.rho (cycle.firstDart hcycle.not_nil), ?_, ?_⟩
    · simpa [RS, hhead] using RS.vert_rho
        (cycle.firstDart hcycle.not_nil)
    · exact hreachable_to (cycle.firstDart hcycle.not_nil)
        (cycle.firstDart_mem_darts hcycle.not_nil)
  refine ⟨root, hfirstSide, cycle, hcycle, ?_⟩
  intro vertex hvertex
  by_cases hroot : vertex = root
  · simpa [hroot] using hfirstSide
  · have hneLast : vertex ≠ cycle.support.getLast (by simp) := by
      rw [cycle.getLast_support]
      exact hroot
    have hdrop : vertex ∈ cycle.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hvertex hneLast
    rw [← cycle.map_fst_darts] at hdrop
    rcases List.mem_map.mp hdrop with ⟨dart, hdart, hfst⟩
    refine ⟨RS.rho dart, ?_, ?_⟩
    · simpa [RS, hfst] using RS.vert_rho dart
    · exact hreachable_to dart hdart

end SimpleGraphDartRotation.Data

end

end GoertzelV24ClosedWebFaceComponentCycleTransport

end Mettapedia.GraphTheory.FourColor
