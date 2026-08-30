import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnShore
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
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open GoertzelV24RotationMultigraphAdapter
open MatchingParity
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
