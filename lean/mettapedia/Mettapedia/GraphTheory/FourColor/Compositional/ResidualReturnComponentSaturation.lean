import Mettapedia.GraphTheory.PairingBoundarySaturation
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweep

/-!
# Component-saturated carrier prefixes

A raw prefix of an alternating carrier has one off-carrier residual edge at
every position, so its ambient boundary grows with the prefix.  The first
saturation step fills every common-residual return component whose two carrier
endpoints already lie in the prefix.  Completed returns then contribute no
common-residual boundary edge; only returns open across the cut can leave.

This file proves that statement on the physical common residual graph and
connects every remaining exit to the literal open-arc lists used by the
two-shore LIFO sweep.  It deliberately controls only common-residual edges.
The reference-matching attachments are the next saturation layer and remain
visible rather than being hidden in this interface.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnComponentSaturation

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open NoncrossingPairingSweep
open ResidualReturnSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Select the carrier positions strictly before a displayed sweep cut. -/
def carrierPrefixSelected
    {sigma : Pairing V} {first second : V}
    {site : ProperAlternatingSiteWitness G sigma first second}
    (cut : CyclePosition sigma site) (position : CyclePosition sigma site) :
    Prop :=
  position < cut

/-- Fill every common-residual return component whose two carrier endpoints
are before the cut, while retaining each selected carrier endpoint itself. -/
def carrierPrefixReturnSaturation
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) : V → Prop :=
  pairingBoundarySaturation
    (H := commonResidualGraph G sigma site)
    (fun position => (cycleVertexOrder sigma site position).1)
    (orderedSiteReturnPairing hG sigma hSigma site)
    (carrierPrefixSelected cut)

/-- Every selected carrier position belongs to the saturated prefix. -/
theorem cycleVertex_mem_carrierPrefixReturnSaturation
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut position : CyclePosition sigma site) (hposition : position < cut) :
    carrierPrefixReturnSaturation hG sigma hSigma site cut
      (cycleVertexOrder sigma site position).1 :=
  pairingBoundarySaturation_boundary
    (H := commonResidualGraph G sigma site)
    (fun boundary => (cycleVertexOrder sigma site boundary).1)
    (orderedSiteReturnPairing hG sigma hSigma site)
    (carrierPrefixSelected cut) hposition

/-- A common-residual edge can leave the saturated carrier prefix only at
the selected endpoint of a return which is open across the sweep cut. -/
theorem exists_open_return_of_commonResidual_exit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) {inside outside : V}
    (hadj : (commonResidualGraph G sigma site).Adj inside outside)
    (hinside : carrierPrefixReturnSaturation hG sigma hSigma site cut inside)
    (houtside : ¬ carrierPrefixReturnSaturation hG sigma hSigma site cut outside) :
    ∃ position : CyclePosition sigma site,
      position < cut ∧
        cut ≤ (orderedSiteReturnPairing hG sigma hSigma site).partner position ∧
        (cycleVertexOrder sigma site position).1 = inside := by
  rcases exists_open_boundary_of_adj_saturation_exit
      (H := commonResidualGraph G sigma site)
      (fun boundary => (cycleVertexOrder sigma site boundary).1)
      (orderedSiteReturnPairing hG sigma hSigma site)
      (carrierPrefixSelected cut) hadj hinside houtside with
    ⟨position, hselected, hopen, heq⟩
  exact ⟨position, hselected, le_of_not_gt hopen, heq⟩

/-- Quantitative form: common-residual exits from the saturated prefix inject
into the return pairs that are open across the sweep cut. -/
theorem card_commonResidual_exit_le_openReturnEndpoints
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (PairingBoundaryExitDart
      (H := commonResidualGraph G sigma site)
      (fun position => (cycleVertexOrder sigma site position).1)
      (orderedSiteReturnPairing hG sigma hSigma site)
      (carrierPrefixSelected cut)) ≤
    Nat.card (PairingBoundaryOpenEndpoint
      (orderedSiteReturnPairing hG sigma hSigma site)
      (carrierPrefixSelected cut)) := by
  apply card_pairingBoundaryExitDart_le_openEndpoint
  intro position
  rw [degree_commonResidualGraph hG sigma hSigma site]
  exact if_pos (cycleVertexOrder sigma site position).2

/-- The literal two-stack interface at a carrier sweep cut. -/
def OpenReturnStackEntry
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :=
  Σ shore : Bool,
    {arc : LabeledArc Unit bond.site.cycle.tail.support.length //
      arc ∈ (returnShoreMatching rotation minimal hG sigma hSigma bond shore).openArcs
        cut}

/-- The cardinality of the literal two-stack interface is the sum of the two
open-arc list lengths. -/
theorem natCard_openReturnStackEntry_eq_openArcs_lengths
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :
    Nat.card (OpenReturnStackEntry rotation minimal hG sigma hSigma bond cut) =
      ((returnShoreMatching rotation minimal hG sigma hSigma bond false).openArcs
          cut).length +
        ((returnShoreMatching rotation minimal hG sigma hSigma bond true).openArcs
          cut).length := by
  classical
  letI : Finite
      (LabeledArc Unit bond.site.cycle.tail.support.length) :=
    Finite.of_injective
      (fun arc => (arc.left, arc.right)) (by
        intro left right heq
        cases left with
        | mk leftLeft leftRight leftLabel =>
          cases right with
          | mk rightLeft rightRight rightLabel =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            cases leftLabel
            cases rightLabel
            rfl)
  letI (shore : Bool) : Finite
      {arc : LabeledArc Unit bond.site.cycle.tail.support.length //
        arc ∈ (returnShoreMatching rotation minimal hG sigma hSigma bond shore).openArcs
          cut} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hcard (shore : Bool) :
      Nat.card
          {arc : LabeledArc Unit bond.site.cycle.tail.support.length //
            arc ∈ (returnShoreMatching rotation minimal hG sigma hSigma bond shore).openArcs
              cut} =
        ((returnShoreMatching rotation minimal hG sigma hSigma bond shore).openArcs
          cut).length := by
    let arcs :=
      (returnShoreMatching rotation minimal hG sigma hSigma bond shore).openArcs cut
    calc
      Nat.card {arc : LabeledArc Unit bond.site.cycle.tail.support.length //
          arc ∈ arcs} = Nat.card (Fin arcs.length) :=
        Nat.card_congr
          (List.Nodup.getEquiv arcs
            (openArcs_nodup
              (returnShoreMatching rotation minimal hG sigma hSigma bond shore)
              cut)).symm
      _ = arcs.length := by simp
  unfold OpenReturnStackEntry
  rw [Nat.card_sigma, Fintype.sum_bool, hcard false, hcard true]
  exact Nat.add_comm _ _

/-- An open paired endpoint occurs in its physical shore's literal open-arc
list. -/
theorem openReturnEndpoint_mem_shoreOpenArcs
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site)
    (endpoint : PairingBoundaryOpenEndpoint
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (carrierPrefixSelected cut)) :
    chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
        (fun _ => ()) endpoint.1 ∈
      (returnShoreMatching rotation minimal hG sigma hSigma bond
        (orderedReturnShore rotation hG sigma hSigma bond endpoint.1)).openArcs
          cut := by
  let shore := orderedReturnShore rotation hG sigma hSigma bond endpoint.1
  let selected := OnReturnShore rotation hG sigma hSigma bond shore
  letI : DecidablePred
      (OnReturnShore rotation hG sigma hSigma bond shore) :=
    fun position => by
      unfold OnReturnShore
      infer_instance
  have hleft : endpoint.1 < cut := endpoint.2.1
  have hright :
      cut ≤ (orderedSiteReturnPairing hG sigma hSigma bond.site).partner
        endpoint.1 :=
    le_of_not_gt endpoint.2.2
  have hposition :
      endpoint.1 < (orderedSiteReturnPairing hG sigma hSigma bond.site).partner
        endpoint.1 :=
    lt_of_lt_of_le hleft hright
  have hselected : selected endpoint.1 := by
    simp [selected, shore, OnReturnShore]
  have hnoncrossing :
      ∀ firstChord secondChord : OrderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma bond.site),
        selected firstChord.left → selected secondChord.left →
          ¬ firstChord.Crosses secondChord := by
    intro firstChord secondChord hfirst hsecond
    exact not_crosses_of_orderedReturnShore_eq_of_minimal
      rotation minimal hG sigma hSigma bond firstChord secondChord
        (hfirst.trans hsecond.symm)
  change chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (fun _ => ()) endpoint.1 ∈
    (noncrossingMatchingOfPairing
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      selected (fun _ => ()) hnoncrossing).openArcs cut
  exact chordArc_mem_openArcs_of_lt_cut_le_partner
    (orderedSiteReturnPairing hG sigma hSigma bond.site)
    selected (fun _ => ()) hnoncrossing endpoint.1 cut hposition hselected
      hleft hright

/-- The common-residual boundary is bounded by the literal two-stack
interface, rather than merely by an abstract set of paired endpoints. -/
theorem card_commonResidual_exit_le_openReturnStackEntries
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :
    Nat.card (PairingBoundaryExitDart
      (H := commonResidualGraph G sigma bond.site)
      (fun position => (cycleVertexOrder sigma bond.site position).1)
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (carrierPrefixSelected cut)) ≤
    Nat.card (OpenReturnStackEntry rotation minimal hG sigma hSigma bond cut) := by
  let endpointToStack :
      PairingBoundaryOpenEndpoint
          (orderedSiteReturnPairing hG sigma hSigma bond.site)
          (carrierPrefixSelected cut) →
        OpenReturnStackEntry rotation minimal hG sigma hSigma bond cut :=
    fun endpoint =>
      ⟨orderedReturnShore rotation hG sigma hSigma bond endpoint.1,
        ⟨chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
            (fun _ => ()) endpoint.1,
          openReturnEndpoint_mem_shoreOpenArcs rotation minimal hG sigma hSigma
            bond cut endpoint⟩⟩
  have hinjective : Function.Injective endpointToStack := by
    intro left right heq
    have harc :
        chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
            (fun _ => ()) left.1 =
          chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
            (fun _ => ()) right.1 :=
      congrArg (fun entry => entry.2.1) heq
    have hleftPartner :
        left.1 < (orderedSiteReturnPairing hG sigma hSigma bond.site).partner
          left.1 :=
      lt_of_lt_of_le left.2.1 (le_of_not_gt left.2.2)
    have hrightPartner :
        right.1 < (orderedSiteReturnPairing hG sigma hSigma bond.site).partner
          right.1 :=
      lt_of_lt_of_le right.2.1 (le_of_not_gt right.2.2)
    apply Subtype.ext
    simpa only [chordArc_left_of_lt _ _ _ hleftPartner,
      chordArc_left_of_lt _ _ _ hrightPartner] using
        congrArg LabeledArc.left harc
  have hopen :
      Nat.card (PairingBoundaryOpenEndpoint
        (orderedSiteReturnPairing hG sigma hSigma bond.site)
        (carrierPrefixSelected cut)) ≤
      Nat.card (OpenReturnStackEntry rotation minimal hG sigma hSigma bond cut) := by
    letI : Finite
        (LabeledArc Unit bond.site.cycle.tail.support.length) :=
      Finite.of_injective
        (fun arc => (arc.left, arc.right)) (by
          intro left right heq
          cases left with
          | mk leftLeft leftRight leftLabel =>
            cases right with
            | mk rightLeft rightRight rightLabel =>
              simp only [Prod.mk.injEq] at heq
              rcases heq with ⟨rfl, rfl⟩
              cases leftLabel
              cases rightLabel
              rfl)
    letI : Finite (OpenReturnStackEntry rotation minimal hG sigma hSigma bond cut) :=
      Finite.of_injective
        (fun entry => (entry.1, entry.2.1)) (by
          intro left right heq
          cases left with
          | mk leftShore leftArc =>
            cases right with
            | mk rightShore rightArc =>
              have hshore : leftShore = rightShore :=
                congrArg Prod.fst heq
              subst rightShore
              have harc : leftArc.1 = rightArc.1 :=
                congrArg Prod.snd heq
              cases leftArc with
              | mk leftValue leftMem =>
                cases rightArc with
                | mk rightValue rightMem =>
                  dsimp only at harc
                  subst rightValue
                  rfl)
    exact Nat.card_le_card_of_injective endpointToStack hinjective
  exact (card_commonResidual_exit_le_openReturnEndpoints hG sigma hSigma
    bond.site cut).trans hopen

/-- Final numerical form: the two physical LIFO stack depths bound every
common-residual edge leaving the component-saturated carrier prefix. -/
theorem card_commonResidual_exit_le_stackLengths
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :
    Nat.card (PairingBoundaryExitDart
      (H := commonResidualGraph G sigma bond.site)
      (fun position => (cycleVertexOrder sigma bond.site position).1)
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (carrierPrefixSelected cut)) ≤
      ((returnShoreMatching rotation minimal hG sigma hSigma bond false).stackAt
          cut).length +
        ((returnShoreMatching rotation minimal hG sigma hSigma bond true).stackAt
          cut).length := by
  have hbound :=
    card_commonResidual_exit_le_openReturnStackEntries rotation minimal hG
      sigma hSigma bond cut
  rw [natCard_openReturnStackEntry_eq_openArcs_lengths rotation minimal hG
    sigma hSigma bond cut] at hbound
  simpa only [stackAt_length_eq_openArcs_length] using hbound

/-- The exit from the preceding theorem is not merely an abstract paired
endpoint: its canonical chord occurs in one of the two physical shore sweep
lists and is open at the same cut. -/
theorem exists_open_shore_arc_of_commonResidual_exit
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) {inside outside : V}
    (hadj : (commonResidualGraph G sigma bond.site).Adj inside outside)
    (hinside : carrierPrefixReturnSaturation hG sigma hSigma bond.site cut inside)
    (houtside :
      ¬ carrierPrefixReturnSaturation hG sigma hSigma bond.site cut outside) :
    ∃ (position : CyclePosition sigma bond.site) (shore : Bool),
      (cycleVertexOrder sigma bond.site position).1 = inside ∧
        chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
            (fun _ => ()) position ∈
          (returnShoreMatching rotation minimal hG sigma hSigma bond shore).openArcs
            cut := by
  rcases exists_open_return_of_commonResidual_exit hG sigma hSigma bond.site
      cut hadj hinside houtside with ⟨position, hleft, hright, hembed⟩
  let shore := orderedReturnShore rotation hG sigma hSigma bond position
  let selected := OnReturnShore rotation hG sigma hSigma bond shore
  letI : DecidablePred
      (OnReturnShore rotation hG sigma hSigma bond shore) :=
    fun position => by
      unfold OnReturnShore
      infer_instance
  have hposition :
      position < (orderedSiteReturnPairing hG sigma hSigma bond.site).partner
        position :=
    lt_of_lt_of_le hleft hright
  have hselected : selected position := by
    simp [selected, shore, OnReturnShore]
  have hnoncrossing :
      ∀ firstChord secondChord : OrderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma bond.site),
        selected firstChord.left → selected secondChord.left →
          ¬ firstChord.Crosses secondChord := by
    intro firstChord secondChord hfirst hsecond
    exact not_crosses_of_orderedReturnShore_eq_of_minimal
      rotation minimal hG sigma hSigma bond firstChord secondChord
        (hfirst.trans hsecond.symm)
  refine ⟨position, shore, hembed, ?_⟩
  change chordArc (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (fun _ => ()) position ∈
    (noncrossingMatchingOfPairing
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      selected (fun _ => ()) hnoncrossing).openArcs cut
  exact chordArc_mem_openArcs_of_lt_cut_le_partner
    (orderedSiteReturnPairing hG sigma hSigma bond.site)
    selected (fun _ => ()) hnoncrossing position cut hposition hselected hleft hright

end

end ResidualReturnComponentSaturation

end Mettapedia.GraphTheory.FourColor.Compositional
