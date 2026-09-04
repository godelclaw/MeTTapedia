import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComponentSaturation
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualCircuitPhysicalReachability

/-!
# Ambient boundary of a component-saturated carrier prefix

Saturating a carrier prefix by complete common-residual return components
removes every closed return from its boundary.  This file identifies the
remaining ambient boundary exactly at the level needed by the compositional
sweep: an outgoing edge is either

* a common-residual edge belonging to an open return;
* an edge of the reference matching; or
* a local `tau` edge on the alternating carrier.

Thus the already bounded two-stack interface controls the first class, while
the reference-matching attachment frontier remains explicit.  No annular
embedding or closed-web hypothesis is assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierSaturationBoundaryDecomposition

open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualTwoFactor
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualCircuitParity
open ResidualCircuitPhysicalReachability
open ResidualReturnComponentSaturation
open ResidualReturnSweep
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Oriented ambient edges leaving the component-saturated carrier prefix. -/
def AmbientExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :=
  {dart : G.Dart //
    carrierPrefixReturnSaturation hG sigma hSigma site cut dart.fst ∧
      ¬ carrierPrefixReturnSaturation hG sigma hSigma site cut dart.snd}

/-- Ambient exits which are still edges of the common residual graph. -/
def CommonResidualExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :=
  {exit : AmbientExitDart hG sigma hSigma site cut //
    (commonResidualGraph G sigma site).Adj exit.1.fst exit.1.snd}

/-- Ambient exits supplied by the reference matching.  These include the
off-carrier attachment frontier which remains to be controlled geometrically. -/
def ReferenceMatchingExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :=
  {exit : AmbientExitDart hG sigma hSigma site cut //
    sigma.partner exit.1.fst = exit.1.snd}

/-- Reference-matching exits whose inside endpoint still lies on the
alternating carrier.  These are finite carrier-interface data, not external
attachments along a return path. -/
def LocalSigmaExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :=
  {exit : AmbientExitDart hG sigma hSigma site cut //
    exit.1.fst ∈ site.carrier ∧ sigma.partner exit.1.fst = exit.1.snd}

/-- The genuinely off-carrier part of the reference-matching frontier.  This
is the only reference class which can become an attachment to the interior of
a common-residual return. -/
def OffCarrierReferenceMatchingExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :=
  {exit : AmbientExitDart hG sigma hSigma site cut //
    sigma.partner exit.1.fst = exit.1.snd ∧ exit.1.fst ∉ site.carrier}

/-- Ambient exits supplied by the incoming local matching on the alternating
carrier. -/
def LocalTauExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :=
  {exit : AmbientExitDart hG sigma hSigma site cut //
    exit.1.fst ∈ site.carrier ∧ site.tau.partner exit.1.fst = exit.1.snd}

/-- Every ambient exit has exactly one of the three structural explanations
needed by the sweep.  The statement is intentionally an inclusive disjunction:
no artificial uniqueness premise is needed by downstream counting. -/
theorem ambientExit_classification
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : AmbientExitDart hG sigma hSigma site cut) :
    (commonResidualGraph G sigma site).Adj exit.1.fst exit.1.snd ∨
      sigma.partner exit.1.fst = exit.1.snd ∨
        (exit.1.fst ∈ site.carrier ∧
          site.tau.partner exit.1.fst = exit.1.snd) := by
  by_cases hsigma : sigma.partner exit.1.fst = exit.1.snd
  · exact Or.inr (Or.inl hsigma)
  · have hold : (residualGraph G sigma).Adj exit.1.fst exit.1.snd :=
      ⟨exit.1.adj, hsigma⟩
    rcases (oldResidualGraph_adj_iff_common_or_tau sigma site).1 hold with
      hcommon | htau
    · exact Or.inl hcommon
    · exact Or.inr (Or.inr htau)

/-- Saturation does not secretly acquire extra carrier vertices.  On the
alternating carrier it is exactly the displayed prefix. -/
theorem cycleVertex_mem_carrierPrefixReturnSaturation_iff
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut position : CyclePosition sigma site) :
    carrierPrefixReturnSaturation hG sigma hSigma site cut
        (cycleVertexOrder sigma site position).1 ↔
      position < cut := by
  constructor
  · intro hsaturated
    rcases hsaturated with
      ⟨boundary, hselected, heq⟩ |
        ⟨boundary, hselected, hpartnerSelected, hreachable⟩
    · have hposition : boundary = position := by
        apply (cycleVertexOrder sigma site).injective
        apply Subtype.ext
        exact heq
      simpa only [carrierPrefixSelected, hposition] using hselected
    · rcases eq_or_eq_orderedReturnPartner_of_commonResidual_reachable
          hG sigma hSigma site boundary position hreachable with
        hsame | hpartner
      · simpa only [carrierPrefixSelected, hsame] using hselected
      · simpa only [carrierPrefixSelected, hpartner] using hpartnerSelected
  · exact cycleVertex_mem_carrierPrefixReturnSaturation
      hG sigma hSigma site cut position

/-- A local reference-matching exit is an open endpoint of the reference
pairing transported to cyclic carrier coordinates. -/
noncomputable def localSigmaExitToOpenEndpoint
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    LocalSigmaExitDart hG sigma hSigma site cut →
      PairingBoundaryOpenEndpoint
        (orderedSiteSigmaPairing sigma site) (carrierPrefixSelected cut) := by
  intro exit
  let position : CyclePosition sigma site :=
    (cycleVertexOrder sigma site).symm
      ⟨exit.1.1.fst, exit.2.1⟩
  have hpositionVertex :
      (cycleVertexOrder sigma site position).1 = exit.1.1.fst :=
    congrArg Subtype.val <|
      (cycleVertexOrder sigma site).apply_symm_apply
        ⟨exit.1.1.fst, exit.2.1⟩
  refine ⟨position, ?_, ?_⟩
  · unfold carrierPrefixSelected
    apply (cycleVertex_mem_carrierPrefixReturnSaturation_iff
      hG sigma hSigma site cut position).1
    simpa only [hpositionVertex] using exit.1.2.1
  · intro hpartnerSelected
    have hsaturated := cycleVertex_mem_carrierPrefixReturnSaturation
      hG sigma hSigma site cut
        ((orderedSiteSigmaPairing sigma site).partner position)
        hpartnerSelected
    have hpartnerVertex := congrArg Subtype.val
      (cycleVertexOrder_orderedSiteSigmaPairing_partner sigma site position)
    change
      (cycleVertexOrder sigma site
          ((orderedSiteSigmaPairing sigma site).partner position)).1 =
        sigma.partner (cycleVertexOrder sigma site position).1
      at hpartnerVertex
    apply exit.1.2.2
    rw [hpartnerVertex, hpositionVertex, exit.2.2] at hsaturated
    exact hsaturated

theorem localSigmaExitToOpenEndpoint_injective
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Function.Injective
      (localSigmaExitToOpenEndpoint hG sigma hSigma site cut) := by
  intro left right heq
  have hposition := congrArg Subtype.val heq
  have hfst : left.1.1.fst = right.1.1.fst := by
    have happly := congrArg
      (fun position : CyclePosition sigma site =>
        (cycleVertexOrder sigma site position).1) hposition
    simpa only [localSigmaExitToOpenEndpoint, Equiv.apply_symm_apply] using happly
  have hsnd : left.1.1.snd = right.1.1.snd := by
    calc
      left.1.1.snd = sigma.partner left.1.1.fst := left.2.2.symm
      _ = sigma.partner right.1.1.fst := congrArg sigma.partner hfst
      _ = right.1.1.snd := right.2.2
  apply Subtype.ext
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  exact Prod.ext hfst hsnd

/-- The carrier-local part of the reference frontier is controlled by the
open endpoints of the transported reference pairing. -/
theorem card_localSigmaExitDart_le_openEndpoint
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (LocalSigmaExitDart hG sigma hSigma site cut) ≤
      Nat.card (PairingBoundaryOpenEndpoint
        (orderedSiteSigmaPairing sigma site) (carrierPrefixSelected cut)) := by
  letI : Finite (PairingBoundaryOpenEndpoint
      (orderedSiteSigmaPairing sigma site) (carrierPrefixSelected cut)) := by
    unfold PairingBoundaryOpenEndpoint
    infer_instance
  exact Nat.card_le_card_of_injective
    (localSigmaExitToOpenEndpoint hG sigma hSigma site cut)
    (localSigmaExitToOpenEndpoint_injective hG sigma hSigma site cut)

/-- A local `tau` exit determines an endpoint of a local carrier edge which
is open across the same displayed prefix cut. -/
noncomputable def localTauExitToOpenEndpoint
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    LocalTauExitDart hG sigma hSigma site cut →
      PairingBoundaryOpenEndpoint
        (orderedSiteTauPairing sigma site) (carrierPrefixSelected cut) := by
  intro exit
  let position : CyclePosition sigma site :=
    (cycleVertexOrder sigma site).symm
      ⟨exit.1.1.fst, exit.2.1⟩
  have hpositionVertex :
      (cycleVertexOrder sigma site position).1 = exit.1.1.fst :=
    congrArg Subtype.val <|
      (cycleVertexOrder sigma site).apply_symm_apply
        ⟨exit.1.1.fst, exit.2.1⟩
  refine ⟨position, ?_, ?_⟩
  · unfold carrierPrefixSelected
    apply (cycleVertex_mem_carrierPrefixReturnSaturation_iff
      hG sigma hSigma site cut position).1
    simpa only [hpositionVertex] using exit.1.2.1
  · intro hpartnerSelected
    have hsaturated := cycleVertex_mem_carrierPrefixReturnSaturation
      hG sigma hSigma site cut
        ((orderedSiteTauPairing sigma site).partner position)
        hpartnerSelected
    have hpartnerVertex := congrArg Subtype.val
      (cycleVertexOrder_orderedSiteTauPairing_partner sigma site position)
    change
      (cycleVertexOrder sigma site
          ((orderedSiteTauPairing sigma site).partner position)).1 =
        site.tau.partner (cycleVertexOrder sigma site position).1
      at hpartnerVertex
    apply exit.1.2.2
    rw [hpartnerVertex, hpositionVertex, exit.2.2] at hsaturated
    exact hsaturated

theorem localTauExitToOpenEndpoint_injective
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Function.Injective
      (localTauExitToOpenEndpoint hG sigma hSigma site cut) := by
  intro left right heq
  have hposition := congrArg Subtype.val heq
  have hfst : left.1.1.fst = right.1.1.fst := by
    have happly := congrArg
      (fun position : CyclePosition sigma site =>
        (cycleVertexOrder sigma site position).1) hposition
    simpa only [localTauExitToOpenEndpoint, Equiv.apply_symm_apply] using happly
  have hsnd : left.1.1.snd = right.1.1.snd := by
    calc
      left.1.1.snd = site.tau.partner left.1.1.fst := left.2.2.symm
      _ = site.tau.partner right.1.1.fst := congrArg site.tau.partner hfst
      _ = right.1.1.snd := right.2.2
  apply Subtype.ext
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  exact Prod.ext hfst hsnd

/-- The local-`tau` frontier is no larger than the open-endpoint interface of
the transported local pairing. -/
theorem card_localTauExitDart_le_openEndpoint
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (LocalTauExitDart hG sigma hSigma site cut) ≤
      Nat.card (PairingBoundaryOpenEndpoint
        (orderedSiteTauPairing sigma site) (carrierPrefixSelected cut)) := by
  letI : Finite (PairingBoundaryOpenEndpoint
      (orderedSiteTauPairing sigma site) (carrierPrefixSelected cut)) := by
    unfold PairingBoundaryOpenEndpoint
    infer_instance
  exact Nat.card_le_card_of_injective
    (localTauExitToOpenEndpoint hG sigma hSigma site cut)
    (localTauExitToOpenEndpoint_injective hG sigma hSigma site cut)

/-- Forget whether a reference-matching exit begins on or off the carrier. -/
def unclassifyReferenceExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    LocalSigmaExitDart hG sigma hSigma site cut ⊕
        OffCarrierReferenceMatchingExitDart hG sigma hSigma site cut →
      ReferenceMatchingExitDart hG sigma hSigma site cut
  | Sum.inl exit => ⟨exit.1, exit.2.2⟩
  | Sum.inr exit => ⟨exit.1, exit.2.1⟩

/-- Split a reference-matching exit according to whether its inside endpoint
is a carrier vertex. -/
noncomputable def classifyReferenceExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : ReferenceMatchingExitDart hG sigma hSigma site cut) :
    LocalSigmaExitDart hG sigma hSigma site cut ⊕
      OffCarrierReferenceMatchingExitDart hG sigma hSigma site cut := by
  by_cases hcarrier : exit.1.1.fst ∈ site.carrier
  · exact Sum.inl ⟨exit.1, hcarrier, exit.2⟩
  · exact Sum.inr ⟨exit.1, exit.2, hcarrier⟩

@[simp] theorem unclassifyReferenceExit_classifyReferenceExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : ReferenceMatchingExitDart hG sigma hSigma site cut) :
    unclassifyReferenceExit hG sigma hSigma site cut
        (classifyReferenceExit hG sigma hSigma site cut exit) = exit := by
  unfold classifyReferenceExit
  split <;> rfl

theorem classifyReferenceExit_injective
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Function.Injective (classifyReferenceExit hG sigma hSigma site cut) := by
  intro left right heq
  have hforgotten := congrArg
    (unclassifyReferenceExit hG sigma hSigma site cut) heq
  simpa only [unclassifyReferenceExit_classifyReferenceExit] using hforgotten

/-- Cardinal form of the local/off-carrier split of the reference frontier. -/
theorem card_referenceMatchingExitDart_le_local_add_offCarrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (ReferenceMatchingExitDart hG sigma hSigma site cut) ≤
      Nat.card (LocalSigmaExitDart hG sigma hSigma site cut) +
        Nat.card (OffCarrierReferenceMatchingExitDart
          hG sigma hSigma site cut) := by
  letI : Finite (AmbientExitDart hG sigma hSigma site cut) := by
    unfold AmbientExitDart
    infer_instance
  letI : Finite (ReferenceMatchingExitDart hG sigma hSigma site cut) := by
    unfold ReferenceMatchingExitDart
    infer_instance
  letI : Finite (LocalSigmaExitDart hG sigma hSigma site cut) := by
    unfold LocalSigmaExitDart
    infer_instance
  letI : Finite
      (OffCarrierReferenceMatchingExitDart hG sigma hSigma site cut) := by
    unfold OffCarrierReferenceMatchingExitDart
    infer_instance
  calc
    Nat.card (ReferenceMatchingExitDart hG sigma hSigma site cut) ≤
        Nat.card (LocalSigmaExitDart hG sigma hSigma site cut ⊕
          OffCarrierReferenceMatchingExitDart hG sigma hSigma site cut) :=
      Nat.card_le_card_of_injective
        (classifyReferenceExit hG sigma hSigma site cut)
        (classifyReferenceExit_injective hG sigma hSigma site cut)
    _ = Nat.card (LocalSigmaExitDart hG sigma hSigma site cut) +
        Nat.card (OffCarrierReferenceMatchingExitDart
          hG sigma hSigma site cut) := by
      rw [Nat.card_sum]

/-- The common-residual ambient exits are merely the generic pairing-boundary
exit darts with their ambient adjacency remembered. -/
def commonResidualExitEquiv
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    CommonResidualExitDart hG sigma hSigma site cut ≃
      PairingBoundaryExitDart
        (H := commonResidualGraph G sigma site)
        (fun position => (cycleVertexOrder sigma site position).1)
        (orderedSiteReturnPairing hG sigma hSigma site)
        (carrierPrefixSelected cut) where
  toFun exit :=
    ⟨⟨(exit.1.1.fst, exit.1.1.snd), exit.2⟩, exit.1.2⟩
  invFun exit :=
    ⟨⟨⟨(exit.1.fst, exit.1.snd),
      ((commonResidualGraph_adj sigma site).1 exit.1.adj).1⟩, exit.2⟩,
      exit.1.adj⟩
  left_inv exit := by rfl
  right_inv exit := by rfl

/-- Forget the structural tag on a classified ambient exit. -/
def unclassifyAmbientExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    CommonResidualExitDart hG sigma hSigma site cut ⊕
        (ReferenceMatchingExitDart hG sigma hSigma site cut ⊕
          LocalTauExitDart hG sigma hSigma site cut) →
      AmbientExitDart hG sigma hSigma site cut
  | Sum.inl exit => exit.1
  | Sum.inr (Sum.inl exit) => exit.1
  | Sum.inr (Sum.inr exit) => exit.1

/-- Every ambient exit has a structural tag which forgets back to that same
exit.  Keeping this existence statement in `Prop` avoids eliminating the
classification disjunction directly into data. -/
theorem exists_classifiedAmbientExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : AmbientExitDart hG sigma hSigma site cut) :
    ∃ tagged : CommonResidualExitDart hG sigma hSigma site cut ⊕
        (ReferenceMatchingExitDart hG sigma hSigma site cut ⊕
          LocalTauExitDart hG sigma hSigma site cut),
      unclassifyAmbientExit hG sigma hSigma site cut tagged = exit := by
  rcases ambientExit_classification hG sigma hSigma site cut exit with
    hcommon | hsigma | htau
  · exact ⟨Sum.inl ⟨exit, hcommon⟩, rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨exit, hsigma⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨exit, htau⟩), rfl⟩

/-- A tagged classification of ambient exits, retaining the original dart in
every branch so that the classification map is injective. -/
noncomputable def classifyAmbientExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : AmbientExitDart hG sigma hSigma site cut) :
    CommonResidualExitDart hG sigma hSigma site cut ⊕
      (ReferenceMatchingExitDart hG sigma hSigma site cut ⊕
        LocalTauExitDart hG sigma hSigma site cut) :=
  Classical.choose
    (exists_classifiedAmbientExit hG sigma hSigma site cut exit)

@[simp] theorem unclassifyAmbientExit_classifyAmbientExit
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : AmbientExitDart hG sigma hSigma site cut) :
    unclassifyAmbientExit hG sigma hSigma site cut
        (classifyAmbientExit hG sigma hSigma site cut exit) = exit := by
  exact Classical.choose_spec
    (exists_classifiedAmbientExit hG sigma hSigma site cut exit)

theorem classifyAmbientExit_injective
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Function.Injective (classifyAmbientExit hG sigma hSigma site cut) := by
  intro left right heq
  have hforgotten := congrArg
    (unclassifyAmbientExit hG sigma hSigma site cut) heq
  simpa only [unclassifyAmbientExit_classifyAmbientExit] using hforgotten

/-- Cardinal form of the structural trichotomy. -/
theorem card_ambientExitDart_le_three_frontiers
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (AmbientExitDart hG sigma hSigma site cut) ≤
      Nat.card (CommonResidualExitDart hG sigma hSigma site cut) +
        (Nat.card (ReferenceMatchingExitDart hG sigma hSigma site cut) +
          Nat.card (LocalTauExitDart hG sigma hSigma site cut)) := by
  letI : Finite (AmbientExitDart hG sigma hSigma site cut) := by
    unfold AmbientExitDart
    infer_instance
  letI : Finite (CommonResidualExitDart hG sigma hSigma site cut) := by
    unfold CommonResidualExitDart
    infer_instance
  letI : Finite (ReferenceMatchingExitDart hG sigma hSigma site cut) := by
    unfold ReferenceMatchingExitDart
    infer_instance
  letI : Finite (LocalTauExitDart hG sigma hSigma site cut) := by
    unfold LocalTauExitDart
    infer_instance
  calc
    Nat.card (AmbientExitDart hG sigma hSigma site cut) ≤
        Nat.card (CommonResidualExitDart hG sigma hSigma site cut ⊕
          (ReferenceMatchingExitDart hG sigma hSigma site cut ⊕
            LocalTauExitDart hG sigma hSigma site cut)) :=
      Nat.card_le_card_of_injective
        (classifyAmbientExit hG sigma hSigma site cut)
        (classifyAmbientExit_injective hG sigma hSigma site cut)
    _ = Nat.card (CommonResidualExitDart hG sigma hSigma site cut) +
        (Nat.card (ReferenceMatchingExitDart hG sigma hSigma site cut) +
          Nat.card (LocalTauExitDart hG sigma hSigma site cut)) := by
      rw [Nat.card_sum, Nat.card_sum]

/-- The common-residual summand in the ambient decomposition is the same
finite type already bounded by the two physical return stacks. -/
theorem natCard_commonResidualExitDart_eq_pairingBoundaryExitDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Nat.card (CommonResidualExitDart hG sigma hSigma site cut) =
      Nat.card (PairingBoundaryExitDart
        (H := commonResidualGraph G sigma site)
        (fun position => (cycleVertexOrder sigma site position).1)
        (orderedSiteReturnPairing hG sigma hSigma site)
        (carrierPrefixSelected cut)) :=
  Nat.card_congr (commonResidualExitEquiv hG sigma hSigma site cut)

/-- Full quantitative boundary statement.  The common-residual contribution
is paid for by the two LIFO stacks.  What remains is precisely the
reference-matching attachment frontier and the local carrier-matching
frontier; neither is folded into an unnamed error term. -/
theorem card_ambientExitDart_le_stackLengths_add_reference_add_localTau
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :
    Nat.card (AmbientExitDart hG sigma hSigma bond.site cut) ≤
      ((returnShoreMatching rotation minimal hG sigma hSigma bond false).stackAt
          cut).length +
        ((returnShoreMatching rotation minimal hG sigma hSigma bond true).stackAt
          cut).length +
        Nat.card (ReferenceMatchingExitDart hG sigma hSigma bond.site cut) +
        Nat.card (LocalTauExitDart hG sigma hSigma bond.site cut) := by
  have hthree := card_ambientExitDart_le_three_frontiers
    hG sigma hSigma bond.site cut
  have hcommon := card_commonResidual_exit_le_stackLengths
    rotation minimal hG sigma hSigma bond cut
  have hcommonCard :=
    natCard_commonResidualExitDart_eq_pairingBoundaryExitDart
      hG sigma hSigma bond.site cut
  omega

/-- Refined ambient boundary bound.  Both carrier-local matching frontiers
are paid for by open endpoints of finite cyclic pairings; the only remaining
ambient term is the genuinely off-carrier reference-matching frontier. -/
theorem card_ambientExitDart_le_stackLengths_add_offCarrierReference_add_local
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :
    Nat.card (AmbientExitDart hG sigma hSigma bond.site cut) ≤
      ((returnShoreMatching rotation minimal hG sigma hSigma bond false).stackAt
          cut).length +
        ((returnShoreMatching rotation minimal hG sigma hSigma bond true).stackAt
          cut).length +
        Nat.card (OffCarrierReferenceMatchingExitDart
          hG sigma hSigma bond.site cut) +
        Nat.card (PairingBoundaryOpenEndpoint
          (orderedSiteSigmaPairing sigma bond.site) (carrierPrefixSelected cut)) +
        Nat.card (PairingBoundaryOpenEndpoint
          (orderedSiteTauPairing sigma bond.site) (carrierPrefixSelected cut)) := by
  have hambient :=
    card_ambientExitDart_le_stackLengths_add_reference_add_localTau
      rotation minimal hG sigma hSigma bond cut
  have href := card_referenceMatchingExitDart_le_local_add_offCarrier
    hG sigma hSigma bond.site cut
  have hsigma := card_localSigmaExitDart_le_openEndpoint
    hG sigma hSigma bond.site cut
  have htau := card_localTauExitDart_le_openEndpoint
    hG sigma hSigma bond.site cut
  omega

end

end CarrierSaturationBoundaryDecomposition

end Mettapedia.GraphTheory.FourColor.Compositional
