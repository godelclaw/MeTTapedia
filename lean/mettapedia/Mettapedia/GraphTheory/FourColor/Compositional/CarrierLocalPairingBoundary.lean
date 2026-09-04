import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingCarrierUnion
import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationBoundaryDecomposition

/-!
# Constant local boundary of an alternating carrier prefix

A linear prefix of a cyclic carrier has only two geometric ends.  If a
pairing joins cyclic neighbours, at most two of its selected endpoints can
have their partners outside the prefix.

At a proper alternating site the restricted `sigma` and `tau` pairings do
join cyclic neighbours.  This is derived from the displayed physical cycle:
its forward and backward edges belong to the union of the two pairing roles,
and pointwise disagreement makes those two roles distinct.  Consequently the
two local frontier terms in the saturated-carrier boundary estimate contribute
at most four in total.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierLocalPairingBoundary

open AlternatingCarrierUnion
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open MatchingParity
open Mettapedia.GraphTheory
open ResidualCircuitParity
open ResidualReturnComponentSaturation
open SimpleGraph

noncomputable section

universe u

/-- A pairing of cyclic neighbours exposes at most two endpoints across a
linear prefix of the cyclic coordinate. -/
theorem card_pairingBoundaryOpenEndpoint_le_two_of_cyclic_neighbors
    {n : Nat} (hfour : 4 ≤ n) (pairing : Pairing (Fin n))
    (hlocal : ∀ position,
      pairing.partner position = finRotate n position ∨
        pairing.partner position = (finRotate n).symm position)
    (cut : Fin n) :
    Nat.card
        (PairingBoundaryOpenEndpoint pairing (fun position => position < cut)) ≤
      2 := by
  letI : NeZero n := ⟨by omega⟩
  let code :
      PairingBoundaryOpenEndpoint pairing (fun position => position < cut) →
        Fin 2 :=
    fun endpoint => if endpoint.1 = 0 then 0 else 1
  have nonzero_succ_eq_cut
      (endpoint : PairingBoundaryOpenEndpoint pairing
        (fun position => position < cut))
      (hnonzero : endpoint.1 ≠ 0) :
      endpoint.1.val + 1 = cut.val := by
    rcases hlocal endpoint.1 with hsucc | hpred
    · have hsum : endpoint.1.val + 1 < n := by
        have hselected := endpoint.2.1
        have hcut := cut.isLt
        exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hselected) hcut
      have hrotateVal :
          (finRotate n endpoint.1).val = endpoint.1.val + 1 := by
        rw [finRotate_apply, Fin.val_add]
        have hone : ((1 : Fin n).val) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [hone, Nat.mod_eq_of_lt hsum]
      have hnot := endpoint.2.2
      rw [hsucc] at hnot
      change ¬(finRotate n endpoint.1).val < cut.val at hnot
      rw [hrotateVal] at hnot
      have hselected := endpoint.2.1
      omega
    · have hpredVal :
          ((finRotate n).symm endpoint.1).val = endpoint.1.val - 1 :=
        coe_finRotate_symm_of_ne_zero hnonzero
      have hnot := endpoint.2.2
      rw [hpred] at hnot
      apply False.elim
      apply hnot
      change ((finRotate n).symm endpoint.1).val < cut.val
      rw [hpredVal]
      have hselected := endpoint.2.1
      have hpositive : 0 < endpoint.1.val :=
        Fin.pos_iff_ne_zero.mpr hnonzero
      omega
  simpa using Nat.card_le_card_of_injective code (by
    intro left right heq
    apply Subtype.ext
    apply Fin.ext
    by_cases hleft : left.1 = 0
    · have hright : right.1 = 0 := by
        by_contra hright
        have := congrArg Fin.val heq
        simp [code, hleft, hright] at this
      simp [hleft, hright]
    · have hright : right.1 ≠ 0 := by
        intro hright
        have := congrArg Fin.val heq
        simp [code, hleft, hright] at this
      have hleftCut := nonzero_succ_eq_cut left hleft
      have hrightCut := nonzero_succ_eq_cut right hright
      omega)

/-- On a cyclic coordinate with at least four positions, successor and
predecessor are distinct. -/
theorem finRotate_ne_symm_of_four_le
    {n : Nat} (hfour : 4 ≤ n) (position : Fin n) :
    finRotate n position ≠ (finRotate n).symm position := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := by
    exact ⟨n - 3, by omega⟩
  have hneighbors : position - 1 ≠ position + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc position, left_eq_add]
    exact ne_of_beq_false rfl
  simpa only [finRotate_apply, finRotate_symm_apply] using hneighbors.symm

/-- A proper alternating carrier has at least four cyclic positions. -/
theorem four_le_cyclePosition
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    4 ≤ site.cycle.tail.support.length := by
  have hcard := Fintype.card_congr (cycleVertexOrder sigma site)
  have hboundaryCard :
      Fintype.card (BoundaryVertex site.carrier) = site.carrier.card :=
    Fintype.card_coe site.carrier
  rw [Fintype.card_fin, hboundaryCard] at hcard
  rw [hcard]
  exact site.four_le

/-- Both matching roles at a proper alternating site join predecessor or
successor positions of the displayed carrier cycle. -/
theorem orderedSitePairings_are_cyclicNeighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    ((orderedSiteSigmaPairing sigma site).partner position =
        finRotate site.cycle.tail.support.length position ∨
      (orderedSiteSigmaPairing sigma site).partner position =
        (finRotate site.cycle.tail.support.length).symm position) ∧
    ((orderedSiteTauPairing sigma site).partner position =
        finRotate site.cycle.tail.support.length position ∨
      (orderedSiteTauPairing sigma site).partner position =
        (finRotate site.cycle.tail.support.length).symm position) := by
  let rotate := finRotate site.cycle.tail.support.length
  let forward := rotate position
  let previous := rotate.symm position
  let vertex := (cycleVertexOrder sigma site position).1
  let forwardVertex := (cycleVertexOrder sigma site forward).1
  let previousVertex := (cycleVertexOrder sigma site previous).1
  have hfour : 4 ≤ site.cycle.tail.support.length :=
    four_le_cyclePosition sigma site
  have hforwardNePrevious : forward ≠ previous :=
    finRotate_ne_symm_of_four_le hfour position
  have hforwardUnion :
      (pairingCarrierGraph sigma site.carrier ⊔
        pairingCarrierGraph site.tau site.carrier).Adj vertex forwardVertex := by
    have hedge :=
      AlternatingCarrierUnion.ProperAlternatingComponentWitness.cycle_edges_pairingUnion
        site (cycleForwardDart sigma site position).edge
        (cycleForwardDart_edge_mem sigma site position)
    have hadj :
        (pairingCarrierGraph sigma site.carrier ⊔
          pairingCarrierGraph site.tau site.carrier).Adj
          (cycleForwardDart sigma site position).fst
          (cycleForwardDart sigma site position).snd := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [SimpleGraph.Dart.edge] using hedge
    simpa only [vertex, forwardVertex, forward, rotate,
      cycleForwardDart_fst, cycleForwardDart_snd] using hadj
  have hpreviousUnion :
      (pairingCarrierGraph sigma site.carrier ⊔
        pairingCarrierGraph site.tau site.carrier).Adj vertex previousVertex := by
    have hedge :=
      AlternatingCarrierUnion.ProperAlternatingComponentWitness.cycle_edges_pairingUnion
        site (cycleForwardDart sigma site previous).edge
        (cycleForwardDart_edge_mem sigma site previous)
    have hedgeAdj :
        (pairingCarrierGraph sigma site.carrier ⊔
          pairingCarrierGraph site.tau site.carrier).Adj
          (cycleForwardDart sigma site previous).fst
          (cycleForwardDart sigma site previous).snd := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [SimpleGraph.Dart.edge] using hedge
    have hadj :
        (pairingCarrierGraph sigma site.carrier ⊔
          pairingCarrierGraph site.tau site.carrier).Adj
          previousVertex vertex := by
      have hrotate : rotate previous = position :=
        rotate.apply_symm_apply position
      simpa only [previousVertex, vertex, previous, rotate,
        cycleForwardDart_fst, cycleForwardDart_snd, hrotate] using hedgeAdj
    exact hadj.symm
  have hforward : sigma.partner vertex = forwardVertex ∨
      site.tau.partner vertex = forwardVertex := by
    rw [SimpleGraph.sup_adj] at hforwardUnion
    rcases hforwardUnion with hsigma | htau
    · exact Or.inl
        ((pairingCarrierGraph_adj sigma site.carrier).mp hsigma).2.2
    · exact Or.inr
        ((pairingCarrierGraph_adj site.tau site.carrier).mp htau).2.2
  have hprevious : sigma.partner vertex = previousVertex ∨
      site.tau.partner vertex = previousVertex := by
    rw [SimpleGraph.sup_adj] at hpreviousUnion
    rcases hpreviousUnion with hsigma | htau
    · exact Or.inl
        ((pairingCarrierGraph_adj sigma site.carrier).mp hsigma).2.2
    · exact Or.inr
        ((pairingCarrierGraph_adj site.tau site.carrier).mp htau).2.2
  have hvertexMem : vertex ∈ site.carrier :=
    (cycleVertexOrder sigma site position).2
  have hforwardVertexNePreviousVertex : forwardVertex ≠ previousVertex := by
    intro heq
    apply hforwardNePrevious
    apply (cycleVertexOrder sigma site).injective
    exact Subtype.ext heq
  have hsigma : sigma.partner vertex = forwardVertex ∨
      sigma.partner vertex = previousVertex := by
    rcases hforward with hs | ht
    · exact Or.inl hs
    · rcases hprevious with hs | ht'
      · exact Or.inr hs
      · exact False.elim
          (hforwardVertexNePreviousVertex (ht.symm.trans ht'))
  have htau : site.tau.partner vertex = forwardVertex ∨
      site.tau.partner vertex = previousVertex := by
    rcases hforward with hs | ht
    · rcases hprevious with hs' | ht'
      · exact False.elim
          (hforwardVertexNePreviousVertex (hs.symm.trans hs'))
      · exact Or.inr ht'
    · exact Or.inl ht
  constructor
  · have hcoordinate :=
      cycleVertexOrder_orderedSiteSigmaPairing_partner sigma site position
    have hcoordinateVal := congrArg Subtype.val hcoordinate
    have hcoordinateVal' :
        (cycleVertexOrder sigma site
          ((orderedSiteSigmaPairing sigma site).partner position)).1 =
          sigma.partner vertex := by
      simpa only [siteSigmaPairing, Pairing.subtype_partner_val, vertex]
        using hcoordinateVal
    rcases hsigma with hsigma | hsigma
    · apply Or.inl
      apply (cycleVertexOrder sigma site).injective
      apply Subtype.ext
      exact hcoordinateVal'.trans hsigma
    · apply Or.inr
      apply (cycleVertexOrder sigma site).injective
      apply Subtype.ext
      exact hcoordinateVal'.trans hsigma
  · have hcoordinate :=
      cycleVertexOrder_orderedSiteTauPairing_partner sigma site position
    have hcoordinateVal := congrArg Subtype.val hcoordinate
    have hcoordinateVal' :
        (cycleVertexOrder sigma site
          ((orderedSiteTauPairing sigma site).partner position)).1 =
          site.tau.partner vertex := by
      simpa only [siteTauPairing, Pairing.subtype_partner_val, vertex]
        using hcoordinateVal
    rcases htau with htau | htau
    · apply Or.inl
      apply (cycleVertexOrder sigma site).injective
      apply Subtype.ext
      exact hcoordinateVal'.trans htau
    · apply Or.inr
      apply (cycleVertexOrder sigma site).injective
      apply Subtype.ext
      exact hcoordinateVal'.trans htau

/-- The local `sigma` frontier of a carrier prefix has size at most two. -/
theorem card_orderedSiteSigmaPairing_openEndpoint_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (PairingBoundaryOpenEndpoint
      (orderedSiteSigmaPairing sigma site) (carrierPrefixSelected cut)) ≤ 2 := by
  exact card_pairingBoundaryOpenEndpoint_le_two_of_cyclic_neighbors
    (four_le_cyclePosition sigma site) (orderedSiteSigmaPairing sigma site)
    (fun position => (orderedSitePairings_are_cyclicNeighbors
      sigma site position).1) cut

/-- The local `tau` frontier of a carrier prefix has size at most two. -/
theorem card_orderedSiteTauPairing_openEndpoint_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (PairingBoundaryOpenEndpoint
      (orderedSiteTauPairing sigma site) (carrierPrefixSelected cut)) ≤ 2 := by
  exact card_pairingBoundaryOpenEndpoint_le_two_of_cyclic_neighbors
    (four_le_cyclePosition sigma site) (orderedSiteTauPairing sigma site)
    (fun position => (orderedSitePairings_are_cyclicNeighbors
      sigma site position).2) cut

/-- Together the two carrier-local pairing roles contribute at most four
open endpoints to the saturated-prefix boundary. -/
theorem card_orderedSitePairing_openEndpoints_add_le_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (PairingBoundaryOpenEndpoint
        (orderedSiteSigmaPairing sigma site) (carrierPrefixSelected cut)) +
      Nat.card (PairingBoundaryOpenEndpoint
        (orderedSiteTauPairing sigma site) (carrierPrefixSelected cut)) ≤ 4 := by
  have hsigma :=
    card_orderedSiteSigmaPairing_openEndpoint_le_two sigma site cut
  have htau :=
    card_orderedSiteTauPairing_openEndpoint_le_two sigma site cut
  omega

end

end CarrierLocalPairingBoundary

end Mettapedia.GraphTheory.FourColor.Compositional
