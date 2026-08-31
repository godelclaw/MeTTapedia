import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnShore
import Mettapedia.GraphTheory.Embedding.FaceCutCycle
import Mathlib.Data.List.NodupEquivFin

/-!
# Cyclic coordinates for a residual return pairing

A proper alternating site already carries a simple closed walk whose support
is exactly the exchange carrier.  The tail support of that walk lists every
carrier vertex exactly once.  It therefore gives a canonical cyclic
coordinate for the physical return pairing constructed from the common
residual graph.

This module transports the return pairing, its physical reachability, and its
same-face-shore theorem into that coordinate.  It does not infer noncrossing
from the shore equality: excluding two interleaving return components remains
a separate planar-separation theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualReturnCycleOrder

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24KauffmanFacePotential
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open GoertzelV24RotationMultigraphAdapter
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The literal cyclic coordinate -/

/-- Positions in the cyclic list obtained by deleting the repeated initial
vertex from the front of a simple closed walk.  The tail support starts at the
second cycle vertex and ends at the initial vertex, so positive rotation still
follows the displayed cycle, merely with a rotated origin. -/
abbrev CyclePosition
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :=
  Fin site.cycle.tail.support.length

/-- The tail support of a proper alternating cycle contains exactly its
exchange carrier. -/
theorem mem_cycle_tail_support_iff
    (sigma : Pairing V) {first second vertex : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    vertex ∈ site.cycle.tail.support ↔ vertex ∈ site.carrier := by
  rw [← site.cycle_support_eq]
  simp only [List.mem_toFinset]
  constructor
  · intro hmem
    have hsupport : first :: site.cycle.tail.support =
        site.cycle.support :=
      site.cycle.cons_support_tail site.cycle_isCycle.not_nil
    rw [← hsupport]
    exact List.mem_cons_of_mem _ hmem
  · intro hmem
    have hsupport : first :: site.cycle.tail.support =
        site.cycle.support :=
      site.cycle.cons_support_tail site.cycle_isCycle.not_nil
    rw [← hsupport] at hmem
    rcases List.mem_cons.mp hmem with hfirst | htail
    · subst vertex
      rw [site.cycle.support_tail_of_not_nil site.cycle_isCycle.not_nil]
      exact site.cycle.end_mem_tail_support site.cycle_isCycle.not_nil
    · exact htail

/-- A simple alternating cycle has one cyclic position per exchange-carrier
vertex. -/
def cycleVertexOrder
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    CyclePosition sigma site ≃ BoundaryVertex site.carrier :=
  (site.cycle_isCycle.isPath_tail.support_nodup.getEquiv
      site.cycle.tail.support).trans
    { toFun := fun vertex =>
        ⟨vertex.1,
          (mem_cycle_tail_support_iff sigma site).1 vertex.2⟩
      invFun := fun vertex =>
        ⟨vertex.1,
          (mem_cycle_tail_support_iff sigma site).2 vertex.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp]
theorem cycleVertexOrder_apply_val
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (cycleVertexOrder sigma site position).1 =
      site.cycle.tail.support.get position :=
  rfl

/-- The number of cyclic coordinates is the length of the simple alternating
cycle. -/
theorem cyclePosition_card_eq_cycle_length
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Fintype.card (CyclePosition sigma site) = site.cycle.length := by
  rw [Fintype.card_fin, SimpleGraph.Walk.length_support]
  exact site.cycle.length_tail_add_one site.cycle_isCycle.not_nil

/-- Positive rotation of the cyclic coordinate follows one actual edge of
the displayed alternating cycle.  This is the semantic link between the
finite order and the embedded graph, rather than merely a cardinality
identification. -/
theorem cycleVertexOrder_adj_finRotate
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    G.Adj (cycleVertexOrder sigma site position).1
      (cycleVertexOrder sigma site
        (finRotate site.cycle.tail.support.length position)).1 := by
  change G.Adj (site.cycle.tail.support.get position)
    (site.cycle.tail.support.get
      (finRotate site.cycle.tail.support.length position))
  haveI : NeZero site.cycle.tail.support.length := position.neZero
  have hlength : site.cycle.tail.support.length =
      site.cycle.tail.length + 1 := site.cycle.tail.length_support
  have htwo : 2 ≤ site.cycle.tail.support.length := by
    have hcycleLength := site.cycle_isCycle.three_le_length
    have htailLength :=
      site.cycle.length_tail_add_one site.cycle_isCycle.not_nil
    omega
  have hone : ((1 : Fin site.cycle.tail.support.length).val) = 1 := by
    change 1 % site.cycle.tail.support.length = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hrotate :
      (finRotate site.cycle.tail.support.length position).val =
        (position.val + 1) % site.cycle.tail.support.length := by
    rw [finRotate_apply, Fin.val_add, hone]
  have supportGet_eq_getVert
      (index : Fin site.cycle.tail.support.length) :
      site.cycle.tail.support.get index =
        site.cycle.tail.getVert index.val := by
    simpa only [List.get_eq_getElem] using
      site.cycle.tail.support_getElem_eq_getVert index.isLt
  by_cases hbefore : position.val < site.cycle.tail.length
  · have hsum : position.val + 1 <
        site.cycle.tail.support.length := by omega
    have hrotateSucc :
        (finRotate site.cycle.tail.support.length position).val =
          position.val + 1 := by
      rw [hrotate, Nat.mod_eq_of_lt hsum]
    rw [supportGet_eq_getVert, supportGet_eq_getVert]
    simpa only [hrotateSucc] using
      site.cycle.tail.adj_getVert_succ hbefore
  · have hlast : position.val = site.cycle.tail.length := by
      omega
    have hrotateZero :
        (finRotate site.cycle.tail.support.length position).val = 0 := by
      rw [hrotate, hlast, hlength]
      exact Nat.mod_self _
    rw [supportGet_eq_getVert, supportGet_eq_getVert]
    simpa only [hlast, hrotateZero, SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero] using
      site.cycle.adj_snd site.cycle_isCycle.not_nil

/-- The oriented cycle dart leaving one cyclic coordinate.  Except at the
last coordinate this is the corresponding dart of `cycle.tail`; at the last
coordinate it is the first dart of the closed walk. -/
def cycleForwardDart
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) : G.Dart :=
  if hposition : position.val < site.cycle.tail.length then
    site.cycle.tail.darts[position.val]'(by simpa using hposition)
  else
    site.cycle.firstDart site.cycle_isCycle.not_nil

/-- Before the final cyclic coordinate, positive rotation increments the
underlying linear index without wraparound. -/
theorem finRotate_cyclePosition_val_eq_add_one_of_lt_tail_length
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site)
    (hposition : position.val < site.cycle.tail.length) :
    (finRotate site.cycle.tail.support.length position).val =
      position.val + 1 := by
  haveI : NeZero site.cycle.tail.support.length := position.neZero
  have hlength : site.cycle.tail.support.length =
      site.cycle.tail.length + 1 := site.cycle.tail.length_support
  have hone : ((1 : Fin site.cycle.tail.support.length).val) = 1 := by
    change 1 % site.cycle.tail.support.length = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [finRotate_apply, Fin.val_add, hone, Nat.mod_eq_of_lt]
  omega

/-- Before the final cyclic coordinate, the positive rotation is literally
the `Fin` value at the successor natural-number coordinate. -/
theorem finRotate_cyclePosition_eq_mk_add_one_of_lt_tail_length
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site)
    (hposition : position.val < site.cycle.tail.length) :
    finRotate site.cycle.tail.support.length position =
      ⟨position.val + 1, by
        have hlength : site.cycle.tail.support.length =
            site.cycle.tail.length + 1 := site.cycle.tail.length_support
        omega⟩ := by
  apply Fin.ext
  exact finRotate_cyclePosition_val_eq_add_one_of_lt_tail_length
    sigma site position hposition

/-- The forward cycle dart is based at the vertex named by its coordinate. -/
@[simp] theorem cycleForwardDart_fst
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (cycleForwardDart sigma site position).fst =
      (cycleVertexOrder sigma site position).1 := by
  have hsupportLength : site.cycle.tail.support.length =
      site.cycle.tail.length + 1 := site.cycle.tail.length_support
  have hget := congrFun site.cycle.tail.getVert_comp_val_eq_get_support position
  simp only [Function.comp_apply] at hget
  by_cases hposition : position.val < site.cycle.tail.length
  · rw [cycleForwardDart, dif_pos hposition,
      site.cycle.tail.darts_getElem_eq_getVert]
    exact hget
  · have hlast : position.val = site.cycle.tail.length := by
      have := position.isLt
      omega
    rw [cycleForwardDart, dif_neg hposition,
      SimpleGraph.Walk.firstDart_toProd]
    change first = (cycleVertexOrder sigma site position).1
    rw [cycleVertexOrder_apply_val, ← hget, hlast,
      SimpleGraph.Walk.getVert_length]

/-- The target of the forward cycle dart is the vertex at the next cyclic
coordinate. -/
@[simp] theorem cycleForwardDart_snd
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (cycleForwardDart sigma site position).snd =
      (cycleVertexOrder sigma site
        (finRotate site.cycle.tail.support.length position)).1 := by
  have hsupportLength : site.cycle.tail.support.length =
      site.cycle.tail.length + 1 := site.cycle.tail.length_support
  by_cases hposition : position.val < site.cycle.tail.length
  · have hrotate :=
      finRotate_cyclePosition_val_eq_add_one_of_lt_tail_length
        sigma site position hposition
    rw [cycleForwardDart, dif_pos hposition,
      site.cycle.tail.darts_getElem_eq_getVert]
    change site.cycle.tail.getVert (position.val + 1) = _
    rw [cycleVertexOrder_apply_val]
    have hget := congrFun site.cycle.tail.getVert_comp_val_eq_get_support
      (finRotate site.cycle.tail.support.length position)
    simp only [Function.comp_apply] at hget
    rw [← hget]
    exact congrArg site.cycle.tail.getVert hrotate.symm
  · have hlast : position.val = site.cycle.tail.length := by
      have := position.isLt
      omega
    haveI : NeZero site.cycle.tail.support.length := position.neZero
    have hrotateZero :
        (finRotate site.cycle.tail.support.length position).val = 0 := by
      have hone : ((1 : Fin site.cycle.tail.support.length).val) = 1 := by
        change 1 % site.cycle.tail.support.length = 1
        apply Nat.mod_eq_of_lt
        have hthree := site.cycle_isCycle.three_le_length
        have hcycleLength :=
          site.cycle.length_tail_add_one site.cycle_isCycle.not_nil
        omega
      rw [finRotate_apply, Fin.val_add, hone, hlast, hsupportLength,
        Nat.mod_self]
    rw [cycleForwardDart, dif_neg hposition,
      SimpleGraph.Walk.firstDart_toProd]
    change site.cycle.snd =
      (cycleVertexOrder sigma site
        (finRotate site.cycle.tail.support.length position)).1
    rw [cycleVertexOrder_apply_val]
    have hget := congrFun site.cycle.tail.getVert_comp_val_eq_get_support
      (finRotate site.cycle.tail.support.length position)
    simp only [Function.comp_apply] at hget
    rw [← hget, hrotateZero, SimpleGraph.Walk.getVert_zero]

/-- The forward dart is a literal dart of the displayed simple cycle. -/
theorem cycleForwardDart_mem_darts
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    cycleForwardDart sigma site position ∈ site.cycle.darts := by
  by_cases hposition : position.val < site.cycle.tail.length
  · rw [cycleForwardDart, dif_pos hposition]
    apply site.cycle.isSubwalk_rfl.tail.darts_subset
    exact List.getElem_mem (by simpa using hposition)
  · rw [cycleForwardDart, dif_neg hposition]
    exact site.cycle.firstDart_mem_darts site.cycle_isCycle.not_nil

/-- Consequently the forward dart's edge belongs to the displayed cycle. -/
theorem cycleForwardDart_edge_mem
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (cycleForwardDart sigma site position).edge ∈ site.cycle.edges := by
  exact List.mem_map_of_mem
    (cycleForwardDart_mem_darts sigma site position)

/-- The canonical residual third dart leaves the cycle rather than following
one of its two cycle edges. -/
theorem siteThirdDart_edge_not_cycle
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (siteThirdDart hG sigma hSigma site
      (cycleVertexOrder sigma site position)).edge ∉ site.cycle.edges := by
  exact commonResidualGraph_adj_not_cycle sigma site
    (commonResidualGraph_adj_siteThirdNeighbor hG sigma hSigma site
      (cycleVertexOrder sigma site position))

/-- At a cycle coordinate, the residual third dart and the forward cycle
dart are distinct. -/
theorem siteThirdDart_ne_cycleForwardDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site position) ≠
      cycleForwardDart sigma site position := by
  intro hdart
  apply siteThirdDart_edge_not_cycle hG sigma hSigma site position
  simpa [hdart] using cycleForwardDart_edge_mem sigma site position

/-- Consecutive forward darts of the displayed simple cycle never
immediately backtrack. -/
theorem alpha_cycleForwardDart_ne_next
    (rotation : Data G)
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    rotation.toRotationSystem.alpha
        (cycleForwardDart sigma site position) ≠
      cycleForwardDart sigma site
        (finRotate site.cycle.tail.support.length position) := by
  let previous := cycleForwardDart sigma site position
  let outgoing := cycleForwardDart sigma site
    (finRotate site.cycle.tail.support.length position)
  intro hback
  have hpreviousMem : previous ∈ site.cycle.darts :=
    cycleForwardDart_mem_darts sigma site position
  have houtgoingMem : outgoing ∈ site.cycle.darts :=
    cycleForwardDart_mem_darts sigma site
      (finRotate site.cycle.tail.support.length position)
  have hedge : previous.edge = outgoing.edge := by
    calc
      previous.edge =
          (rotation.toRotationSystem.alpha previous).edge := by
        simpa using
          (rotation.toRotationSystem.edge_alpha previous).symm
      _ = outgoing.edge := congrArg SimpleGraph.Dart.edge hback
  have hdart :=
    site.cycle_isCycle.isTrail.dart_eq_of_mem_darts_and_edge_eq
      hpreviousMem houtgoingMem hedge
  exact rotation.toRotationSystem.alpha_fixfree previous
    (hback.trans hdart.symm)

/-- At the next coordinate of the simple cycle, the residual dart is the
unique third dart besides the arriving and outgoing cycle darts. -/
theorem eq_siteThirdDart_of_next_base_of_ne_cycleDarts
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site)
    (dart : rotation.toRotationSystem.D)
    (hbase : rotation.toRotationSystem.vertOf dart =
      rotation.toRotationSystem.vertOf
        (cycleForwardDart sigma site
          (finRotate site.cycle.tail.support.length position)))
    (hneArrived : dart ≠ rotation.toRotationSystem.alpha
      (cycleForwardDart sigma site position))
    (hneOutgoing : dart ≠ cycleForwardDart sigma site
      (finRotate site.cycle.tail.support.length position)) :
    dart = siteThirdDart hG sigma hSigma site
      (cycleVertexOrder sigma site
        (finRotate site.cycle.tail.support.length position)) := by
  let arrived : G.Dart := rotation.toRotationSystem.alpha
    (cycleForwardDart sigma site position)
  let outgoing : G.Dart := cycleForwardDart sigma site
    (finRotate site.cycle.tail.support.length position)
  let third : G.Dart := siteThirdDart hG sigma hSigma site
    (cycleVertexOrder sigma site
      (finRotate site.cycle.tail.support.length position))
  have harrivedBase : rotation.toRotationSystem.vertOf arrived =
      rotation.toRotationSystem.vertOf outgoing := by
    change (cycleForwardDart sigma site position).snd = outgoing.fst
    simp [outgoing]
  have hthirdBase : rotation.toRotationSystem.vertOf third =
      rotation.toRotationSystem.vertOf outgoing := by
    calc
      rotation.toRotationSystem.vertOf third =
          (cycleVertexOrder sigma site
            (finRotate site.cycle.tail.support.length position)).1 := by
        rfl
      _ = rotation.toRotationSystem.vertOf outgoing := by
        exact (cycleForwardDart_fst sigma site
          (finRotate site.cycle.tail.support.length position)).symm
  have harrivedNeOutgoing : arrived ≠ outgoing :=
    alpha_cycleForwardDart_ne_next rotation sigma site position
  have hthirdNeOutgoing : third ≠ outgoing := by
    exact siteThirdDart_ne_cycleForwardDart hG sigma hSigma site
      (finRotate site.cycle.tail.support.length position)
  have hthirdNeArrived : third ≠ arrived := by
    intro heq
    apply siteThirdDart_edge_not_cycle hG sigma hSigma site
      (finRotate site.cycle.tail.support.length position)
    have hedge : third.edge =
        (cycleForwardDart sigma site position).edge := by
      calc
        third.edge = arrived.edge := congrArg SimpleGraph.Dart.edge heq
        _ = (cycleForwardDart sigma site position).edge := by
          simp [arrived]
    rw [hedge]
    exact cycleForwardDart_edge_mem sigma site position
  have htripleSubset : ({arrived, outgoing, third} : Finset G.Dart) ⊆
      rotation.toRotationSystem.dartsAt
        (rotation.toRotationSystem.vertOf outgoing) := by
    intro candidate hcandidate
    rcases Finset.mem_insert.mp hcandidate with harrived | hcandidate
    · rw [harrived]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, harrivedBase⟩
    rcases Finset.mem_insert.mp hcandidate with houtgoing | hthird
    · rw [houtgoing]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · have hcandThird := Finset.mem_singleton.mp hthird
      rw [hcandThird]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hthirdBase⟩
  have htripleCard :
      ({arrived, outgoing, third} : Finset G.Dart).card = 3 := by
    have harrivedNotMem : arrived ∉
        ({outgoing, third} : Finset G.Dart) := by
      simp [harrivedNeOutgoing, hthirdNeArrived.symm]
    have houtgoingNotMem : outgoing ∉ ({third} : Finset G.Dart) := by
      simp [hthirdNeOutgoing.symm]
    calc
      ({arrived, outgoing, third} : Finset G.Dart).card =
          ({outgoing, third} : Finset G.Dart).card + 1 :=
        Finset.card_insert_of_notMem harrivedNotMem
      _ = ({third} : Finset G.Dart).card + 1 + 1 := by
        rw [Finset.card_insert_of_notMem houtgoingNotMem]
      _ = 3 := by simp
  have htripleEq : ({arrived, outgoing, third} : Finset G.Dart) =
      rotation.toRotationSystem.dartsAt
        (rotation.toRotationSystem.vertOf outgoing) := by
    apply Finset.eq_of_subset_of_card_le htripleSubset
    calc
      (rotation.toRotationSystem.dartsAt
          (rotation.toRotationSystem.vertOf outgoing)).card = 3 := by
        simpa [outgoing] using hcubic
          (rotation.toRotationSystem.vertOf
            (cycleForwardDart sigma site
              (finRotate site.cycle.tail.support.length position)))
      _ = ({arrived, outgoing, third} : Finset G.Dart).card :=
        htripleCard.symm
      _ ≤ ({arrived, outgoing, third} : Finset G.Dart).card := le_rfl
  have hdartMem : dart ∈ rotation.toRotationSystem.dartsAt
      (rotation.toRotationSystem.vertOf outgoing) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbase⟩
  rw [← htripleEq] at hdartMem
  rcases Finset.mem_insert.mp hdartMem with harrived | hdartMem
  · exact False.elim (hneArrived harrived)
  rcases Finset.mem_insert.mp hdartMem with houtgoing | hthird
  · exact False.elim (hneOutgoing houtgoing)
  · exact Finset.mem_singleton.mp hthird

/-- If the residual third edge at the next coordinate avoids an exact cut,
both oriented face-side labels of the displayed cycle propagate through that
turn. -/
theorem ExactFaceCut.labels_eq_cycleForward_next_of_siteThird_not_selected
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {selected : G.edgeSet → Prop} {A : Type*}
    (cut : ExactFaceCut rotation.toRotationSystem selected A)
    (position : CyclePosition sigma site)
    (hthird : ¬selected (rotation.toRotationSystem.edgeOf
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site
          (finRotate site.cycle.tail.support.length position))))) :
    (cut.label (dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma site position)) =
        cut.label (dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma site
            (finRotate site.cycle.tail.support.length position)))) ∧
      (cut.label (dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha
            (cycleForwardDart sigma site position))) =
        cut.label (dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha
            (cycleForwardDart sigma site
              (finRotate site.cycle.tail.support.length position))))) := by
  let previous := cycleForwardDart sigma site position
  let outgoing := cycleForwardDart sigma site
    (finRotate site.cycle.tail.support.length position)
  have hbase : rotation.toRotationSystem.vertOf outgoing =
      rotation.toRotationSystem.vertOf
        (rotation.toRotationSystem.alpha previous) := by
    change outgoing.fst = previous.snd
    simp [previous, outgoing]
  have hnonback : rotation.toRotationSystem.alpha previous ≠ outgoing :=
    alpha_cycleForwardDart_ne_next rotation sigma site position
  have hother : ∀ dart : rotation.toRotationSystem.D,
      rotation.toRotationSystem.vertOf dart =
          rotation.toRotationSystem.vertOf outgoing →
      dart ≠ rotation.toRotationSystem.alpha previous →
      dart ≠ outgoing →
      ¬selected (rotation.toRotationSystem.edgeOf dart) := by
    intro dart hdart hneArrived hneOutgoing
    have hdartThird :=
      eq_siteThirdDart_of_next_base_of_ne_cycleDarts
        rotation hcubic hG sigma hSigma site position dart
          hdart hneArrived hneOutgoing
    rw [hdartThird]
    exact hthird
  constructor
  · exact cut.label_eq_across_locallyCubicCycleTurn hrotation
      previous outgoing (hcubic _) hbase hnonback hother
  · exact cut.label_eq_opposite_across_locallyCubicCycleTurn hrotation
      previous outgoing (hcubic _) hbase hnonback hother |>.symm

/-- In the sector where the residual dart precedes the outgoing cycle dart,
the oriented-side label flips at the next coordinate exactly when that
residual edge is selected. -/
theorem ExactFaceCut.label_add_cycleForward_next_eq_one_iff_selected_of_sector
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {selected : G.edgeSet → Prop}
    (cut : ExactFaceCut rotation.toRotationSystem selected F2)
    (position : CyclePosition sigma site)
    (hsector : rotation.toRotationSystem.rho
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site
          (finRotate site.cycle.tail.support.length position))) =
      cycleForwardDart sigma site
        (finRotate site.cycle.tail.support.length position)) :
    cut.label (dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma site position)) +
        cut.label (dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma site
            (finRotate site.cycle.tail.support.length position))) = 1 ↔
      selected (rotation.toRotationSystem.edgeOf
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site
            (finRotate site.cycle.tail.support.length position)))) := by
  let RS := rotation.toRotationSystem
  let previous := cycleForwardDart sigma site position
  let outgoing := cycleForwardDart sigma site
    (finRotate site.cycle.tail.support.length position)
  let arrived := RS.alpha previous
  let third := siteThirdDart hG sigma hSigma site
    (cycleVertexOrder sigma site
      (finRotate site.cycle.tail.support.length position))
  have harrivedBase : RS.vertOf arrived = RS.vertOf outgoing := by
    change previous.snd = outgoing.fst
    simp [previous, outgoing]
  have hthirdBase : RS.vertOf third = RS.vertOf outgoing := by
    calc
      RS.vertOf third =
          (cycleVertexOrder sigma site
            (finRotate site.cycle.tail.support.length position)).1 := by rfl
      _ = RS.vertOf outgoing := by
        exact (cycleForwardDart_fst sigma site
          (finRotate site.cycle.tail.support.length position)).symm
  have harrivedNeOutgoing : arrived ≠ outgoing :=
    alpha_cycleForwardDart_ne_next rotation sigma site position
  have hthirdNeOutgoing : third ≠ outgoing :=
    siteThirdDart_ne_cycleForwardDart hG sigma hSigma site
      (finRotate site.cycle.tail.support.length position)
  have hthirdNeArrived : third ≠ arrived := by
    intro heq
    apply siteThirdDart_edge_not_cycle hG sigma hSigma site
      (finRotate site.cycle.tail.support.length position)
    have hedge : third.edge = previous.edge := by
      calc
        third.edge = arrived.edge := congrArg SimpleGraph.Dart.edge heq
        _ = previous.edge := by simp [arrived, RS]
    rw [hedge]
    exact cycleForwardDart_edge_mem sigma site position
  have hturn := RotationSystem.rho_three_cycle_of_eq_second RS
    hcubic hrotation (first := third) (second := outgoing) (third := arrived)
      hthirdBase.symm (harrivedBase.trans hthirdBase.symm)
      hthirdNeOutgoing hthirdNeArrived harrivedNeOutgoing.symm hsector
  exact cut.label_add_across_cycleTurn_eq_one_iff_selected_middle
    previous third outgoing hturn.2 hsector

/-- In the opposite sector, the opposite-side label has the corresponding
binary flip recurrence. -/
theorem ExactFaceCut.label_add_opposite_cycleForward_next_eq_one_iff_selected_of_sector
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {selected : G.edgeSet → Prop}
    (cut : ExactFaceCut rotation.toRotationSystem selected F2)
    (position : CyclePosition sigma site)
    (hsector : rotation.toRotationSystem.rho
      (cycleForwardDart sigma site
        (finRotate site.cycle.tail.support.length position)) =
      siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site
          (finRotate site.cycle.tail.support.length position))) :
    cut.label (dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha
            (cycleForwardDart sigma site position))) +
        cut.label (dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha
            (cycleForwardDart sigma site
              (finRotate site.cycle.tail.support.length position)))) = 1 ↔
      selected (rotation.toRotationSystem.edgeOf
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site
            (finRotate site.cycle.tail.support.length position)))) := by
  let RS := rotation.toRotationSystem
  let previous := cycleForwardDart sigma site position
  let outgoing := cycleForwardDart sigma site
    (finRotate site.cycle.tail.support.length position)
  let arrived := RS.alpha previous
  let third := siteThirdDart hG sigma hSigma site
    (cycleVertexOrder sigma site
      (finRotate site.cycle.tail.support.length position))
  have harrivedBase : RS.vertOf arrived = RS.vertOf outgoing := by
    change previous.snd = outgoing.fst
    simp [previous, outgoing]
  have hthirdBase : RS.vertOf third = RS.vertOf outgoing := by
    calc
      RS.vertOf third =
          (cycleVertexOrder sigma site
            (finRotate site.cycle.tail.support.length position)).1 := by rfl
      _ = RS.vertOf outgoing := by
        exact (cycleForwardDart_fst sigma site
          (finRotate site.cycle.tail.support.length position)).symm
  have harrivedNeOutgoing : arrived ≠ outgoing :=
    alpha_cycleForwardDart_ne_next rotation sigma site position
  have hthirdNeOutgoing : third ≠ outgoing :=
    siteThirdDart_ne_cycleForwardDart hG sigma hSigma site
      (finRotate site.cycle.tail.support.length position)
  have hthirdNeArrived : third ≠ arrived := by
    intro heq
    apply siteThirdDart_edge_not_cycle hG sigma hSigma site
      (finRotate site.cycle.tail.support.length position)
    have hedge : third.edge = previous.edge := by
      calc
        third.edge = arrived.edge := congrArg SimpleGraph.Dart.edge heq
        _ = previous.edge := by simp [arrived, RS]
    rw [hedge]
    exact cycleForwardDart_edge_mem sigma site position
  have hturn := RotationSystem.rho_three_cycle_of_eq_second RS
    hcubic hrotation (first := outgoing) (second := third) (third := arrived)
      hthirdBase (harrivedBase)
      hthirdNeOutgoing.symm harrivedNeOutgoing.symm hthirdNeArrived hsector
  exact cut.label_add_opposite_across_cycleTurn_eq_one_iff_selected_middle
    previous third outgoing hsector hturn.1

/-- The cyclic rotation places the residual third dart on exactly one of the
two sides of the oriented cycle dart. -/
theorem rho_siteThirdDart_eq_cycleForwardDart_or_reverse
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    rotation.toRotationSystem.rho
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site position)) =
          cycleForwardDart sigma site position ∨
      rotation.toRotationSystem.rho
          (cycleForwardDart sigma site position) =
        siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site position) := by
  apply rotation.toRotationSystem.rho_eq_or_rho_eq_of_cubic
    hcubic hrotation
  · change (cycleForwardDart sigma site position).fst =
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site position)).fst
    simp [siteThirdDart]
  · exact (siteThirdDart_ne_cycleForwardDart
      hG sigma hSigma site position)

/-- In the forward local sector, an unselected residual edge sees the same
exact-cut label as the oriented cycle side at that coordinate. -/
theorem ExactFaceCut.label_thirdDart_eq_cycleForward_of_not_selected_of_sector
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {selected : G.edgeSet → Prop} {A : Type*}
    (cut : ExactFaceCut rotation.toRotationSystem selected A)
    (position : CyclePosition sigma site)
    (hnotSelected : ¬selected (rotation.toRotationSystem.edgeOf
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site position))))
    (hsector : rotation.toRotationSystem.rho
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site position)) =
      cycleForwardDart sigma site position) :
    cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site position))) =
      cut.label (dartOrbitFace rotation.toRotationSystem
        (cycleForwardDart sigma site position)) := by
  let third := siteThirdDart hG sigma hSigma site
    (cycleVertexOrder sigma site position)
  have hsame :
      cut.label (dartOrbitFace rotation.toRotationSystem third) =
        cut.label (dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha third)) := by
    apply not_ne_iff.mp
    intro hne
    exact hnotSelected ((cut.separates third).mp hne)
  have hface :
      dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha third) =
        dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma site position) := by
    calc
      dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha third) =
          dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.rho third) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho
          rotation.toRotationSystem third
      _ = dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma site position) := by rw [hsector]
  exact hsame.trans (congrArg cut.label hface)

/-- In the reverse local sector, the residual dart lies directly on the
opposite oriented cycle face side. -/
theorem ExactFaceCut.label_thirdDart_eq_opposite_cycleForward_of_sector
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {selected : G.edgeSet → Prop} {A : Type*}
    (cut : ExactFaceCut rotation.toRotationSystem selected A)
    (position : CyclePosition sigma site)
    (hsector : rotation.toRotationSystem.rho
      (cycleForwardDart sigma site position) =
      siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site position)) :
    cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site position))) =
      cut.label (dartOrbitFace rotation.toRotationSystem
        (rotation.toRotationSystem.alpha
          (cycleForwardDart sigma site position))) := by
  apply congrArg cut.label
  symm
  calc
    dartOrbitFace rotation.toRotationSystem
        (rotation.toRotationSystem.alpha
          (cycleForwardDart sigma site position)) =
        dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.rho
            (cycleForwardDart sigma site position)) :=
      dartOrbitFace_alpha_eq_dartOrbitFace_rho
        rotation.toRotationSystem (cycleForwardDart sigma site position)
    _ = dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site position)) := by rw [hsector]

/-- If exactly one residual edge is selected while traversing a linear
interval of the displayed cycle, and the endpoint residual darts use the
same local sector as that selected edge, then their exact-cut labels differ.
This is the algebraic disk-crossing lemma used by residual-return
noncrossing. -/
theorem ExactFaceCut.label_ne_thirdDarts_of_single_selected_cyclePosition
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {selected : G.edgeSet → Prop}
    (cut : ExactFaceCut rotation.toRotationSystem selected F2)
    (start pivot finish : CyclePosition sigma site)
    (hstartPivot : start.val < pivot.val)
    (hpivotFinish : pivot.val < finish.val)
    (hselected : ∀ position : CyclePosition sigma site,
      start.val ≤ position.val → position.val ≤ finish.val →
      (selected (rotation.toRotationSystem.edgeOf
          (siteThirdDart hG sigma hSigma site
            (cycleVertexOrder sigma site position))) ↔
        position = pivot))
    (hstartSector :
      (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma site
            (cycleVertexOrder sigma site start)) =
        cycleForwardDart sigma site start) ↔
      (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma site
            (cycleVertexOrder sigma site pivot)) =
        cycleForwardDart sigma site pivot))
    (hfinishSector :
      (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma site
            (cycleVertexOrder sigma site finish)) =
        cycleForwardDart sigma site finish) ↔
      (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma site
            (cycleVertexOrder sigma site pivot)) =
        cycleForwardDart sigma site pivot)) :
    cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site start))) ≠
      cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site finish))) := by
  let cycleLength := site.cycle.tail.support.length
  let forwardLabel : Nat → F2 := fun index =>
    if hindex : index < cycleLength then
      cut.label (dartOrbitFace rotation.toRotationSystem
        (cycleForwardDart sigma site ⟨index, hindex⟩))
    else 0
  let oppositeLabel : Nat → F2 := fun index =>
    if hindex : index < cycleLength then
      cut.label (dartOrbitFace rotation.toRotationSystem
        (rotation.toRotationSystem.alpha
          (cycleForwardDart sigma site ⟨index, hindex⟩)))
    else 0
  have hstepForward : ∀ index, start.val ≤ index →
      index < finish.val → index + 1 ≠ pivot.val →
      forwardLabel index = forwardLabel (index + 1) := by
    intro index hstartIndex hindexFinish hnextNePivot
    have hindexBound : index < cycleLength := by
      have := finish.isLt
      simpa [cycleLength] using (show index < site.cycle.tail.support.length by
        omega)
    have hnextBound : index + 1 < cycleLength := by
      have := finish.isLt
      simpa [cycleLength] using
        (show index + 1 < site.cycle.tail.support.length by omega)
    let position : CyclePosition sigma site := ⟨index, by
      simpa [cycleLength] using hindexBound⟩
    let next : CyclePosition sigma site := ⟨index + 1, by
      simpa [cycleLength] using hnextBound⟩
    have hpositionTail : position.val < site.cycle.tail.length := by
      have hlength : site.cycle.tail.support.length =
          site.cycle.tail.length + 1 := site.cycle.tail.length_support
      dsimp [position]
      omega
    have hrotate :
        finRotate site.cycle.tail.support.length position = next := by
      simpa [position, next] using
        finRotate_cyclePosition_eq_mk_add_one_of_lt_tail_length
          sigma site position hpositionTail
    have hnextNe : next ≠ pivot := by
      intro heq
      apply hnextNePivot
      exact congrArg Fin.val heq
    have hnextNotSelected : ¬selected (rotation.toRotationSystem.edgeOf
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site next))) := by
      intro hsel
      apply hnextNe
      apply (hselected next (by dsimp [next]; omega)
        (by dsimp [next]; omega)).mp hsel
    have hlabels :=
      GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.labels_eq_cycleForward_next_of_siteThird_not_selected
        rotation hcubic hrotation hG sigma hSigma site cut position (by
          simpa only [hrotate] using hnextNotSelected)
    simpa only [forwardLabel, cycleLength, dif_pos hindexBound,
      dif_pos hnextBound, hrotate] using hlabels.1
  have hstepOpposite : ∀ index, start.val ≤ index →
      index < finish.val → index + 1 ≠ pivot.val →
      oppositeLabel index = oppositeLabel (index + 1) := by
    intro index hstartIndex hindexFinish hnextNePivot
    have hindexBound : index < cycleLength := by
      have := finish.isLt
      simpa [cycleLength] using (show index < site.cycle.tail.support.length by
        omega)
    have hnextBound : index + 1 < cycleLength := by
      have := finish.isLt
      simpa [cycleLength] using
        (show index + 1 < site.cycle.tail.support.length by omega)
    let position : CyclePosition sigma site := ⟨index, by
      simpa [cycleLength] using hindexBound⟩
    let next : CyclePosition sigma site := ⟨index + 1, by
      simpa [cycleLength] using hnextBound⟩
    have hpositionTail : position.val < site.cycle.tail.length := by
      have hlength : site.cycle.tail.support.length =
          site.cycle.tail.length + 1 := site.cycle.tail.length_support
      dsimp [position]
      omega
    have hrotate :
        finRotate site.cycle.tail.support.length position = next := by
      simpa [position, next] using
        finRotate_cyclePosition_eq_mk_add_one_of_lt_tail_length
          sigma site position hpositionTail
    have hnextNe : next ≠ pivot := by
      intro heq
      apply hnextNePivot
      exact congrArg Fin.val heq
    have hnextNotSelected : ¬selected (rotation.toRotationSystem.edgeOf
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site next))) := by
      intro hsel
      apply hnextNe
      apply (hselected next (by dsimp [next]; omega)
        (by dsimp [next]; omega)).mp hsel
    have hlabels :=
      GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.labels_eq_cycleForward_next_of_siteThird_not_selected
        rotation hcubic hrotation hG sigma hSigma site cut position (by
          simpa only [hrotate] using hnextNotSelected)
    simpa only [oppositeLabel, cycleLength, dif_pos hindexBound,
      dif_pos hnextBound, hrotate] using hlabels.2
  let predecessor : CyclePosition sigma site := ⟨pivot.val - 1, by
    have := pivot.isLt
    omega⟩
  have hpredecessorTail : predecessor.val < site.cycle.tail.length := by
    have hlength : site.cycle.tail.support.length =
        site.cycle.tail.length + 1 := site.cycle.tail.length_support
    dsimp [predecessor]
    omega
  have hrotatePredecessor :
      finRotate site.cycle.tail.support.length predecessor = pivot := by
    rw [finRotate_cyclePosition_eq_mk_add_one_of_lt_tail_length
      sigma site predecessor hpredecessorTail]
    apply Fin.ext
    dsimp [predecessor]
    omega
  have hpivotSelected : selected (rotation.toRotationSystem.edgeOf
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site pivot))) :=
    (hselected pivot hstartPivot.le hpivotFinish.le).2 rfl
  have hstartNotSelected : ¬selected (rotation.toRotationSystem.edgeOf
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site start))) := by
    intro hsel
    have := (hselected start le_rfl (by omega)).1 hsel
    exact (Fin.ne_of_lt hstartPivot) this
  have hfinishNotSelected : ¬selected (rotation.toRotationSystem.edgeOf
      (siteThirdDart hG sigma hSigma site
        (cycleVertexOrder sigma site finish))) := by
    intro hsel
    have := (hselected finish (by omega) le_rfl).1 hsel
    exact (Fin.ne_of_gt hpivotFinish) this
  rcases rho_siteThirdDart_eq_cycleForwardDart_or_reverse
      rotation hcubic hrotation hG sigma hSigma site pivot with
    hpivotForward | hpivotReverse
  · have hstartForward := hstartSector.mpr hpivotForward
    have hfinishForward := hfinishSector.mpr hpivotForward
    have hflip : forwardLabel (pivot.val - 1) +
        forwardLabel pivot.val = 1 := by
      have hrecurrence :=
        (GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_add_cycleForward_next_eq_one_iff_selected_of_sector
          rotation hcubic hrotation hG sigma hSigma site cut predecessor (by
            simpa only [hrotatePredecessor] using hpivotForward)).2 (by
              simpa only [hrotatePredecessor] using hpivotSelected)
      have hpredBound : pivot.val - 1 < cycleLength := by
        have := pivot.isLt
        simpa [cycleLength] using
          (show pivot.val - 1 < site.cycle.tail.support.length by omega)
      have hpivotBound : pivot.val < cycleLength := by
        simpa [cycleLength] using pivot.isLt
      simpa only [forwardLabel, cycleLength, dif_pos hpredBound,
        dif_pos hpivotBound, hrotatePredecessor] using hrecurrence
    have hsideNe : forwardLabel start.val ≠ forwardLabel finish.val :=
      ne_of_single_f2_flip_on_interval forwardLabel hstartPivot hpivotFinish
        (by
          intro index hstartIndex hnextPivot
          apply hstepForward index hstartIndex (by omega)
          omega)
        hflip
        (by
          intro index hpivotIndex hindexFinish
          apply hstepForward index (by omega) hindexFinish
          omega)
    have hstartSide :=
      GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_thirdDart_eq_cycleForward_of_not_selected_of_sector
        rotation hG sigma hSigma site cut start hstartNotSelected hstartForward
    have hfinishSide :=
      GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_thirdDart_eq_cycleForward_of_not_selected_of_sector
        rotation hG sigma hSigma site cut finish hfinishNotSelected hfinishForward
    intro heq
    apply hsideNe
    have hstartBound : start.val < cycleLength := by
      simpa [cycleLength] using start.isLt
    have hfinishBound : finish.val < cycleLength := by
      simpa [cycleLength] using finish.isLt
    simpa only [forwardLabel, cycleLength, dif_pos hstartBound,
      dif_pos hfinishBound, ← hstartSide, ← hfinishSide] using heq
  · have hpivotNotForward : ¬rotation.toRotationSystem.rho
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site pivot)) =
          cycleForwardDart sigma site pivot := by
      intro hforward
      exact (siteThirdDart_ne_cycleForwardDart
        hG sigma hSigma site pivot) (by
          have hcube := rho_cube_apply_of_isCubic rotation.toRotationSystem
            hcubic hrotation
              (siteThirdDart hG sigma hSigma site
                (cycleVertexOrder sigma site pivot))
          rw [hforward, hpivotReverse, hforward] at hcube
          exact hcube.symm)
    have hstartNotForward : ¬rotation.toRotationSystem.rho
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site start)) =
          cycleForwardDart sigma site start :=
      fun h => hpivotNotForward (hstartSector.mp h)
    have hfinishNotForward : ¬rotation.toRotationSystem.rho
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site finish)) =
          cycleForwardDart sigma site finish :=
      fun h => hpivotNotForward (hfinishSector.mp h)
    have hstartReverse := (rho_siteThirdDart_eq_cycleForwardDart_or_reverse
      rotation hcubic hrotation hG sigma hSigma site start).resolve_left
        hstartNotForward
    have hfinishReverse := (rho_siteThirdDart_eq_cycleForwardDart_or_reverse
      rotation hcubic hrotation hG sigma hSigma site finish).resolve_left
        hfinishNotForward
    have hflip : oppositeLabel (pivot.val - 1) +
        oppositeLabel pivot.val = 1 := by
      have hrecurrence :=
        (GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_add_opposite_cycleForward_next_eq_one_iff_selected_of_sector
          rotation hcubic hrotation hG sigma hSigma site cut predecessor (by
            simpa only [hrotatePredecessor] using hpivotReverse)).2 (by
              simpa only [hrotatePredecessor] using hpivotSelected)
      have hpredBound : pivot.val - 1 < cycleLength := by
        have := pivot.isLt
        simpa [cycleLength] using
          (show pivot.val - 1 < site.cycle.tail.support.length by omega)
      have hpivotBound : pivot.val < cycleLength := by
        simpa [cycleLength] using pivot.isLt
      simpa only [oppositeLabel, cycleLength, dif_pos hpredBound,
        dif_pos hpivotBound, hrotatePredecessor] using hrecurrence
    have hsideNe : oppositeLabel start.val ≠ oppositeLabel finish.val :=
      ne_of_single_f2_flip_on_interval oppositeLabel hstartPivot hpivotFinish
        (by
          intro index hstartIndex hnextPivot
          apply hstepOpposite index hstartIndex (by omega)
          omega)
        hflip
        (by
          intro index hpivotIndex hindexFinish
          apply hstepOpposite index (by omega) hindexFinish
          omega)
    have hstartSide :=
      GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_thirdDart_eq_opposite_cycleForward_of_sector
        rotation hG sigma hSigma site cut start hstartReverse
    have hfinishSide :=
      GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_thirdDart_eq_opposite_cycleForward_of_sector
        rotation hG sigma hSigma site cut finish hfinishReverse
    intro heq
    apply hsideNe
    have hstartBound : start.val < cycleLength := by
      simpa [cycleLength] using start.isLt
    have hfinishBound : finish.val < cycleLength := by
      simpa [cycleLength] using finish.isLt
    simpa only [oppositeLabel, cycleLength, dif_pos hstartBound,
      dif_pos hfinishBound, ← hstartSide, ← hfinishSide] using heq

/-- A third dart lies on the oriented face shore of the forward cycle dart
exactly in the corresponding local rotation sector. -/
theorem thirdDart_same_cycleForward_faceShore_iff
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) :
    ((dartOrbitFace rotation.toRotationSystem
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site position)) ∈ bond.faces) ↔
        (dartOrbitFace rotation.toRotationSystem
          (cycleForwardDart sigma bond.site position) ∈ bond.faces)) ↔
      rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site position)) =
        cycleForwardDart sigma bond.site position := by
  let RS := rotation.toRotationSystem
  let third := siteThirdDart hG sigma hSigma bond.site
    (cycleVertexOrder sigma bond.site position)
  let forward := cycleForwardDart sigma bond.site position
  have hthirdNot : third.edge ∉ bond.site.cycle.edges :=
    siteThirdDart_edge_not_cycle hG sigma hSigma bond.site position
  have hforwardMem : forward.edge ∈ bond.site.cycle.edges :=
    cycleForwardDart_edge_mem sigma bond.site position
  have hthirdSame :
      (dartOrbitFace RS third ∈ bond.faces ↔
        dartOrbitFace RS (RS.alpha third) ∈ bond.faces) := by
    have hnoxor : ¬((dartOrbitFace RS third ∈ bond.faces ∧
          dartOrbitFace RS (RS.alpha third) ∉ bond.faces) ∨
        (dartOrbitFace RS third ∉ bond.faces ∧
          dartOrbitFace RS (RS.alpha third) ∈ bond.faces)) := by
      intro hxor
      exact hthirdNot ((bond.cycle_separates_faces third).2 hxor)
    tauto
  have hforwardOpposite :
      (dartOrbitFace RS forward ∈ bond.faces ∧
          dartOrbitFace RS (RS.alpha forward) ∉ bond.faces) ∨
        (dartOrbitFace RS forward ∉ bond.faces ∧
          dartOrbitFace RS (RS.alpha forward) ∈ bond.faces) :=
    (bond.cycle_separates_faces forward).1 hforwardMem
  rcases rho_siteThirdDart_eq_cycleForwardDart_or_reverse
      rotation hcubic hrotation hG sigma hSigma bond.site position with
    hthirdForward | hforwardThird
  · refine ⟨fun _ => hthirdForward, fun _ => ?_⟩
    have hface : dartOrbitFace RS (RS.alpha third) =
        dartOrbitFace RS forward := by
      calc
        dartOrbitFace RS (RS.alpha third) =
            dartOrbitFace RS (RS.rho third) :=
          dartOrbitFace_alpha_eq_dartOrbitFace_rho RS third
        _ = dartOrbitFace RS forward := by rw [hthirdForward]
    rw [hface] at hthirdSame
    exact hthirdSame
  · refine ⟨?_, fun heq => False.elim
      (siteThirdDart_ne_cycleForwardDart hG sigma hSigma bond.site position
        (by
          have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation third
          rw [heq, hforwardThird, heq] at hcube
          exact hcube.symm))⟩
    intro hsame
    have hface : dartOrbitFace RS (RS.alpha forward) =
        dartOrbitFace RS third := by
      calc
        dartOrbitFace RS (RS.alpha forward) =
            dartOrbitFace RS (RS.rho forward) :=
          dartOrbitFace_alpha_eq_dartOrbitFace_rho RS forward
        _ = dartOrbitFace RS third := by rw [hforwardThird]
    rw [hface] at hforwardOpposite
    tauto

/-- Every forward dart of the oriented simple cycle belongs to the same one
of the cycle's two facial shores. -/
theorem cycleForwardDarts_same_face_shore
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (sigma : Pairing V)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (left right : CyclePosition sigma bond.site) :
    (dartOrbitFace rotation.toRotationSystem
        (cycleForwardDart sigma bond.site left) ∈ bond.faces) ↔
      (dartOrbitFace rotation.toRotationSystem
        (cycleForwardDart sigma bond.site right) ∈ bond.faces) := by
  let cut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ bond.site.cycle.edges) F2 :=
    { label := faceSetIndicator rotation bond.faces
      separates := by
        intro dart
        rw [bond.cycle_separates_faces]
        by_cases hleft : dartOrbitFace rotation.toRotationSystem dart ∈
            bond.faces <;>
          by_cases hright : dartOrbitFace rotation.toRotationSystem
              (rotation.toRotationSystem.alpha dart) ∈ bond.faces <;>
          simp [faceSetIndicator, hleft, hright] }
  have hlocalCubic : ∀ dart ∈ bond.site.cycle.darts,
      (rotation.toRotationSystem.dartsAt
        (rotation.toRotationSystem.vertOf dart)).card = 3 := by
    intro dart _
    exact hcubic (rotation.toRotationSystem.vertOf dart)
  have hleftLabel := cut.label_eq_on_orientedCycle rotation hrotation
    bond.site.cycle bond.site.cycle_isCycle hlocalCubic
      (cycleForwardDart sigma bond.site left)
      (cycleForwardDart_mem_darts sigma bond.site left)
  have hrightLabel := cut.label_eq_on_orientedCycle rotation hrotation
    bond.site.cycle bond.site.cycle_isCycle hlocalCubic
      (cycleForwardDart sigma bond.site right)
      (cycleForwardDart_mem_darts sigma bond.site right)
  have heq := hleftLabel.symm.trans hrightLabel
  change faceSetIndicator rotation bond.faces
      (dartOrbitFace rotation.toRotationSystem
        (cycleForwardDart sigma bond.site left)) =
    faceSetIndicator rotation bond.faces
      (dartOrbitFace rotation.toRotationSystem
        (cycleForwardDart sigma bond.site right)) at heq
  by_cases hleft : dartOrbitFace rotation.toRotationSystem
      (cycleForwardDart sigma bond.site left) ∈ bond.faces <;>
    by_cases hright : dartOrbitFace rotation.toRotationSystem
      (cycleForwardDart sigma bond.site right) ∈ bond.faces <;>
    simp [faceSetIndicator, hleft, hright] at heq ⊢

/-- Equal facial shores of two residual third darts are equivalent to equal
local rotation sectors at their cycle coordinates. -/
theorem cycleRotationSector_iff_of_thirdDarts_same_face_shore
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (left right : CyclePosition sigma bond.site)
    (hshore :
      (dartOrbitFace rotation.toRotationSystem
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site left)) ∈ bond.faces) ↔
        (dartOrbitFace rotation.toRotationSystem
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site right)) ∈ bond.faces)) :
    (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site left)) =
        cycleForwardDart sigma bond.site left) ↔
      (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site right)) =
        cycleForwardDart sigma bond.site right) := by
  have hleftLocal := thirdDart_same_cycleForward_faceShore_iff
    rotation hcubic hrotation hG sigma hSigma bond left
  have hrightLocal := thirdDart_same_cycleForward_faceShore_iff
    rotation hcubic hrotation hG sigma hSigma bond right
  have hforward := cycleForwardDarts_same_face_shore
    rotation hcubic hrotation sigma bond left right
  constructor
  · intro hleftSector
    apply hrightLocal.mp
    have hleftSame := hleftLocal.mpr hleftSector
    constructor
    · intro hrightThird
      exact hforward.mp (hleftSame.mp (hshore.mpr hrightThird))
    · intro hrightForward
      exact hshore.mp (hleftSame.mpr (hforward.mpr hrightForward))
  · intro hrightSector
    apply hleftLocal.mp
    have hrightSame := hrightLocal.mpr hrightSector
    constructor
    · intro hleftThird
      exact hforward.mpr (hrightSame.mp (hshore.mp hleftThird))
    · intro hleftForward
      exact hshore.mpr (hrightSame.mpr (hforward.mp hleftForward))

/-! ## Transporting a pairing through coordinates -/

/-- Relabel a fixed-point-free involution through an equivalence. -/
def pairingCongr {A B : Type*} (coordinate : A ≃ B)
    (pairing : Pairing B) : Pairing A where
  partner point := coordinate.symm (pairing.partner (coordinate point))
  partner_partner := by
    intro point
    apply coordinate.injective
    simp only [Equiv.apply_symm_apply, pairing.partner_partner]
  partner_ne := by
    intro point hfixed
    apply pairing.partner_ne (coordinate point)
    have := congrArg coordinate hfixed
    simpa only [Equiv.apply_symm_apply] using this

@[simp]
theorem pairingCongr_partner {A B : Type*} (coordinate : A ≃ B)
    (pairing : Pairing B) (point : A) :
    (pairingCongr coordinate pairing).partner point =
      coordinate.symm (pairing.partner (coordinate point)) :=
  rfl

/-- The physical residual return pairing, written in the actual cyclic order
of the operated alternating cycle. -/
def orderedSiteReturnPairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Pairing (CyclePosition sigma site) :=
  pairingCongr (cycleVertexOrder sigma site)
    (siteReturnPairing hG sigma hSigma site)

/-- Conjugating into cyclic coordinates changes no physical endpoint: the
ordered partner maps back to the original return partner. -/
theorem cycleVertexOrder_orderedSiteReturnPairing_partner
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner position) =
      (siteReturnPairing hG sigma hSigma site).partner
        (cycleVertexOrder sigma site position) := by
  simp [orderedSiteReturnPairing, pairingCongr]

/-- Every ordered return chord is still witnessed by a literal path in the
common residual graph. -/
theorem orderedSiteReturnPairing_reachable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (commonResidualGraph G sigma site).Reachable
        (cycleVertexOrder sigma site position).1
        (cycleVertexOrder sigma site
          ((orderedSiteReturnPairing hG sigma hSigma site).partner
            position)).1 := by
  rw [cycleVertexOrder_orderedSiteReturnPairing_partner]
  exact siteReturnPairing_reachable hG sigma hSigma site
    (cycleVertexOrder sigma site position)

/-- The same-shore theorem in exact cyclic coordinates.  This is the input a
future noncrossing proof must combine with planar separation; it is not itself
that proof. -/
theorem orderedSiteReturnPairing_thirdDarts_same_face_shore
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) :
    (dartOrbitFace rotation.toRotationSystem
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site position)) ∈ bond.faces) ↔
      (dartOrbitFace rotation.toRotationSystem
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site
              ((orderedSiteReturnPairing hG sigma hSigma bond.site).partner
                position))) ∈ bond.faces) := by
  rw [cycleVertexOrder_orderedSiteReturnPairing_partner]
  exact siteReturnPairing_thirdDarts_same_face_shore rotation
    hcubic hrotation hG sigma hSigma bond
      (cycleVertexOrder sigma bond.site position)

/-- The finite two-sector label of a residual return endpoint: `true` means
that the face immediately on the oriented third-dart side belongs to the
selected shore of the cycle's exact facial bond. -/
def orderedReturnShore
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) : Bool :=
  decide (dartOrbitFace rotation.toRotationSystem
      (siteThirdDart hG sigma hSigma bond.site
        (cycleVertexOrder sigma bond.site position)) ∈ bond.faces)

/-- Equality of the Boolean return-shore coordinates gives equality of the
intrinsic local rotation sectors. -/
theorem cycleRotationSector_iff_of_orderedReturnShore_eq
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (left right : CyclePosition sigma bond.site)
    (hshore : orderedReturnShore rotation hG sigma hSigma bond left =
      orderedReturnShore rotation hG sigma hSigma bond right) :
    (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site left)) =
        cycleForwardDart sigma bond.site left) ↔
      (rotation.toRotationSystem.rho
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site right)) =
        cycleForwardDart sigma bond.site right) := by
  apply cycleRotationSector_iff_of_thirdDarts_same_face_shore
    rotation hcubic hrotation hG sigma hSigma bond left right
  unfold orderedReturnShore at hshore
  by_cases hleft : dartOrbitFace rotation.toRotationSystem
      (siteThirdDart hG sigma hSigma bond.site
        (cycleVertexOrder sigma bond.site left)) ∈ bond.faces <;>
    by_cases hright : dartOrbitFace rotation.toRotationSystem
      (siteThirdDart hG sigma hSigma bond.site
        (cycleVertexOrder sigma bond.site right)) ∈ bond.faces <;>
    simp [hleft, hright] at hshore ⊢

/-- A physical return chord has one well-defined shore: its two cyclic
endpoints receive the same Boolean sector label. -/
theorem orderedReturnShore_partner
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) :
    orderedReturnShore rotation hG sigma hSigma bond position =
      orderedReturnShore rotation hG sigma hSigma bond
        ((orderedSiteReturnPairing hG sigma hSigma bond.site).partner
          position) := by
  unfold orderedReturnShore
  have hshore :=
    orderedSiteReturnPairing_thirdDarts_same_face_shore rotation
      hcubic hrotation hG sigma hSigma bond position
  by_cases hleft :
      dartOrbitFace rotation.toRotationSystem
          (siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site position)) ∈ bond.faces
  · have hright := hshore.mp hleft
    simp [hleft, hright]
  · have hright : ¬ dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          (cycleVertexOrder sigma bond.site
            ((orderedSiteReturnPairing hG sigma hSigma bond.site).partner
              position))) ∈ bond.faces := by
      exact fun h => hleft (hshore.mpr h)
    simp [hleft, hright]

/-! ## Canonical finite chords -/

/-- One edge of a pairing on a linearly displayed cyclic carrier, written
with its smaller endpoint first.  The cyclic geometry will be imposed by the
actual cycle coordinate above; this structure only removes the arbitrary
choice of one of a chord's two endpoints. -/
structure OrderedReturnChord {n : Nat} (pairing : Pairing (Fin n)) where
  left : Fin n
  right : Fin n
  left_lt_right : left < right
  partner_left : pairing.partner left = right

@[ext]
theorem OrderedReturnChord.ext {n : Nat} {pairing : Pairing (Fin n)}
    {first second : OrderedReturnChord pairing}
    (hleft : first.left = second.left)
    (hright : first.right = second.right) : first = second := by
  cases first
  cases second
  simp_all

/-- The canonical ordered chord represented by one endpoint. -/
def orderedReturnChord {n : Nat} (pairing : Pairing (Fin n))
    (position : Fin n) : OrderedReturnChord pairing where
  left := min position (pairing.partner position)
  right := max position (pairing.partner position)
  left_lt_right := (min_lt_max).2 (pairing.partner_ne position).symm
  partner_left := by
    by_cases hle : position ≤ pairing.partner position
    · rw [min_eq_left hle, max_eq_right hle]
    · have hreverse : pairing.partner position ≤ position :=
        le_of_not_ge hle
      rw [min_eq_right hreverse, max_eq_left hreverse,
        pairing.partner_partner]

/-- Choosing the other endpoint names the same canonical chord. -/
theorem orderedReturnChord_partner {n : Nat}
    (pairing : Pairing (Fin n)) (position : Fin n) :
    orderedReturnChord pairing (pairing.partner position) =
      orderedReturnChord pairing position := by
  apply OrderedReturnChord.ext
  · change min (pairing.partner position)
        (pairing.partner (pairing.partner position)) =
        min position (pairing.partner position)
    rw [pairing.partner_partner]
    exact min_comm _ _
  · change max (pairing.partner position)
        (pairing.partner (pairing.partner position)) =
        max position (pairing.partner position)
    rw [pairing.partner_partner]
    exact max_comm _ _

/-- Two canonically ordered chords cross when their four endpoints strictly
interleave in the displayed linear cut of the cyclic order.  The usual two
interleaving orders are exactly the cyclic alternation relation, independently
of where the linear display was cut. -/
def OrderedReturnChord.Crosses {n : Nat} {pairing : Pairing (Fin n)}
    (first second : OrderedReturnChord pairing) : Prop :=
  (first.left < second.left ∧ second.left < first.right ∧
      first.right < second.right) ∨
    (second.left < first.left ∧ first.left < second.right ∧
      second.right < first.right)

instance {n : Nat} {pairing : Pairing (Fin n)}
    (first second : OrderedReturnChord pairing) :
    Decidable (first.Crosses second) := by
  unfold OrderedReturnChord.Crosses
  infer_instance

/-- Boundary vertices in the same common-residual component name the same
canonical return chord. -/
theorem orderedReturnChord_eq_of_reachable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (firstPosition secondPosition : CyclePosition sigma site)
    (hreach : (commonResidualGraph G sigma site).Reachable
      (cycleVertexOrder sigma site firstPosition).1
      (cycleVertexOrder sigma site secondPosition).1) :
    orderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma site) firstPosition =
      orderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma site) secondPosition := by
  by_cases hsame : cycleVertexOrder sigma site secondPosition =
      cycleVertexOrder sigma site firstPosition
  · have hpositions : secondPosition = firstPosition :=
      (cycleVertexOrder sigma site).injective hsame
    subst secondPosition
    rfl
  · have hphysical := siteReturnPairing_eq_of_reachable
      hG sigma hSigma site
        (cycleVertexOrder sigma site firstPosition)
        (cycleVertexOrder sigma site secondPosition) hsame hreach
    have hordered :
        (orderedSiteReturnPairing hG sigma hSigma site).partner
            firstPosition = secondPosition := by
      apply (cycleVertexOrder sigma site).injective
      rw [cycleVertexOrder_orderedSiteReturnPairing_partner]
      exact hphysical
    rw [← hordered, orderedReturnChord_partner]

/-- Witnessing paths of two different return chords are edge-disjoint.  This
is the physical component statement needed before planar noncrossing can be
invoked: it follows from uniqueness of the two boundary endpoints in every
degree-`1/2` common-residual component, not from a picture of chords. -/
theorem orderedSiteReturnPairing_walk_edges_disjoint_of_chord_ne
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (firstPosition secondPosition : CyclePosition sigma site)
    (firstPath : (commonResidualGraph G sigma site).Walk
      (cycleVertexOrder sigma site firstPosition).1
      (cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner
          firstPosition)).1)
    (secondPath : (commonResidualGraph G sigma site).Walk
      (cycleVertexOrder sigma site secondPosition).1
      (cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner
          secondPosition)).1)
    (hchordNe :
      orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) firstPosition ≠
        orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) secondPosition) :
    firstPath.edges.Disjoint secondPath.edges := by
  rw [List.disjoint_left]
  intro edge hfirstEdge hsecondEdge
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleftFirst : left ∈ firstPath.support :=
        firstPath.fst_mem_support_of_mem_edges hfirstEdge
      have hleftSecond : left ∈ secondPath.support :=
        secondPath.fst_mem_support_of_mem_edges hsecondEdge
      have hfirstReach : (commonResidualGraph G sigma site).Reachable
          (cycleVertexOrder sigma site firstPosition).1 left :=
        (firstPath.takeUntil left hleftFirst).reachable
      have hsecondReach : (commonResidualGraph G sigma site).Reachable
          (cycleVertexOrder sigma site secondPosition).1 left :=
        (secondPath.takeUntil left hleftSecond).reachable
      have hstarts : (commonResidualGraph G sigma site).Reachable
          (cycleVertexOrder sigma site firstPosition).1
          (cycleVertexOrder sigma site secondPosition).1 :=
        hfirstReach.trans hsecondReach.symm
      exact hchordNe (orderedReturnChord_eq_of_reachable
        hG sigma hSigma site firstPosition secondPosition hstarts)

/-- Different physical return chords have vertex-disjoint witnessing paths,
including their cycle endpoints. -/
theorem orderedSiteReturnPairing_walk_support_disjoint_of_chord_ne
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (firstPosition secondPosition : CyclePosition sigma site)
    (firstPath : (commonResidualGraph G sigma site).Walk
      (cycleVertexOrder sigma site firstPosition).1
      (cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner
          firstPosition)).1)
    (secondPath : (commonResidualGraph G sigma site).Walk
      (cycleVertexOrder sigma site secondPosition).1
      (cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner
          secondPosition)).1)
    (hchordNe :
      orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) firstPosition ≠
        orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) secondPosition) :
    firstPath.support.Disjoint secondPath.support := by
  rw [List.disjoint_left]
  intro vertex hfirstVertex hsecondVertex
  have hfirstReach : (commonResidualGraph G sigma site).Reachable
      (cycleVertexOrder sigma site firstPosition).1 vertex :=
    (firstPath.takeUntil vertex hfirstVertex).reachable
  have hsecondReach : (commonResidualGraph G sigma site).Reachable
      (cycleVertexOrder sigma site secondPosition).1 vertex :=
    (secondPath.takeUntil vertex hsecondVertex).reachable
  have hstarts : (commonResidualGraph G sigma site).Reachable
      (cycleVertexOrder sigma site firstPosition).1
      (cycleVertexOrder sigma site secondPosition).1 :=
    hfirstReach.trans hsecondReach.symm
  exact hchordNe (orderedReturnChord_eq_of_reachable
    hG sigma hSigma site firstPosition secondPosition hstarts)

/-- The shore carried by a canonical return chord.  Its value is independent
of which endpoint was used to name the chord. -/
def orderedReturnChordShore
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) : Bool :=
  orderedReturnShore rotation hG sigma hSigma bond
    (orderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site) position).left

/-- Reversing the representative endpoint changes neither the chord nor its
shore. -/
theorem orderedReturnChordShore_partner
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) :
    orderedReturnChordShore rotation hG sigma hSigma bond
        ((orderedSiteReturnPairing hG sigma hSigma bond.site).partner position) =
      orderedReturnChordShore rotation hG sigma hSigma bond position := by
  unfold orderedReturnChordShore
  rw [orderedReturnChord_partner]

end

end GoertzelV24ResidualReturnCycleOrder

end Mettapedia.GraphTheory.FourColor
