import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationBoundaryDecomposition
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualCircuitComponentDecomposition
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnAttachmentMatching

/-!
# Off-carrier reference exits are return-path attachments

After common-residual component saturation, a reference-matching edge can
leave the saturated carrier prefix from a vertex away from the alternating
carrier.  This file connects that boundary description to the physical
return-path attachment interface.

The first step is purely component-theoretic: the inside endpoint belongs to
a completed common-residual return whose two carrier endpoints lie before the
sweep cut.  Since a canonical return path exhausts its component, that inside
endpoint occurs strictly inside the path.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace OffCarrierReferenceAttachment

open CarrierSaturationBoundaryDecomposition
open CubicPathAttachment
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnArc
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualCircuitParity
open ResidualCircuitComponentDecomposition
open ResidualReturnAttachmentMatching
open ResidualReturnComponentSaturation
open ResidualReturnPathAttachment
open ResidualReturnSeparatorExitSide
open ResidualReturnSweep
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A completed common-residual return component containing the inside
endpoint of an off-carrier reference-matching exit. -/
structure CompletedReturnExitWitness
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) where
  position : CyclePosition sigma site
  position_lt_cut : position < cut
  partner_lt_cut :
    (orderedSiteReturnPairing hG sigma hSigma site).partner position < cut
  inside_reachable :
    (commonResidualGraph G sigma site).Reachable
      (cycleVertexOrder sigma site position).1 exit.1.1.fst

/-- Unpack saturation at an off-carrier inside endpoint.  The direct carrier
branch is impossible, so the endpoint lies in a return component with both
ends selected. -/
theorem exists_completedReturnExitWitness
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) :
    Nonempty (CompletedReturnExitWitness hG sigma hSigma site cut exit) := by
  rcases exit.1.2.1 with
    ⟨position, hselected, heq⟩ |
      ⟨position, hselected, hpartnerSelected, hreachable⟩
  · exfalso
    apply exit.2.2
    rw [← heq]
    exact (cycleVertexOrder sigma site position).2
  · exact ⟨⟨position, hselected, hpartnerSelected, hreachable⟩⟩

/-- The inside endpoint occurs on the canonical return path of its witnessed
common-residual component. -/
theorem inside_mem_orderedReturnPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut)
    (witness : CompletedReturnExitWitness hG sigma hSigma site cut exit) :
    exit.1.1.fst ∈
      (orderedReturnPath hG sigma hSigma site witness.position).support := by
  have hcomponent : exit.1.1.fst ∈
      ((commonResidualGraph G sigma site).connectedComponentMk
        (cycleVertexOrder sigma site witness.position).1).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound witness.inside_reachable).symm
  rw [← orderedReturnPath_toSubgraph_verts_eq_commonComponent_supp
    hG sigma hSigma site witness.position] at hcomponent
  exact (orderedReturnPath hG sigma hSigma site witness.position).mem_verts_toSubgraph.mp
    hcomponent

/-- Orient the completed return from its smaller cyclic coordinate.  Both
endpoints remain behind the sweep cut, and reachability to the inside endpoint
is preserved when the original witness is reversed. -/
theorem exists_orderedCompletedReturnExitWitness
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) :
    ∃ witness : CompletedReturnExitWitness hG sigma hSigma site cut exit,
      witness.position <
        (orderedSiteReturnPairing hG sigma hSigma site).partner
          witness.position := by
  let raw := Classical.choice
    (exists_completedReturnExitWitness hG sigma hSigma site cut exit)
  let returns := orderedSiteReturnPairing hG sigma hSigma site
  by_cases hforward : raw.position ≤ returns.partner raw.position
  · refine ⟨raw, ?_⟩
    exact lt_of_le_of_ne hforward (returns.partner_ne raw.position).symm
  · let position := returns.partner raw.position
    have hposition_lt : position < raw.position := lt_of_not_ge hforward
    have hreachable : (commonResidualGraph G sigma site).Reachable
        (cycleVertexOrder sigma site position).1 exit.1.1.fst := by
      exact (orderedSiteReturnPairing_reachable hG sigma hSigma site
        raw.position).symm.trans raw.inside_reachable
    let witness : CompletedReturnExitWitness hG sigma hSigma site cut exit :=
      { position := position
        position_lt_cut := raw.partner_lt_cut
        partner_lt_cut := by
          simpa only [position, returns, Pairing.partner_partner] using
            raw.position_lt_cut
        inside_reachable := hreachable }
    refine ⟨witness, ?_⟩
    simpa only [witness, position, returns, Pairing.partner_partner] using
      hposition_lt

/-- With the ordered orientation, the inside endpoint lies on the ambient
path carried by the canonical return chord. -/
theorem exists_orderedReturnChord_inside_mem
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) :
    ∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma site),
      chord.left < cut ∧ chord.right < cut ∧
        exit.1.1.fst ∈
          (orderedChordAmbientPath hG sigma hSigma site chord).support := by
  rcases exists_orderedCompletedReturnExitWitness
      hG sigma hSigma site cut exit with ⟨witness, hordered⟩
  let returns := orderedSiteReturnPairing hG sigma hSigma site
  let chord := orderedReturnChord returns witness.position
  change witness.position < returns.partner witness.position at hordered
  have hleft : chord.left = witness.position := by
    exact min_eq_left hordered.le
  have hright : chord.right = returns.partner witness.position := by
    exact max_eq_right hordered.le
  have hsource := inside_mem_orderedReturnPath
    hG sigma hSigma site cut exit witness
  refine ⟨chord, hleft.trans_lt witness.position_lt_cut,
    hright.trans_lt witness.partner_lt_cut, ?_⟩
  rw [orderedChordAmbientPath, SimpleGraph.Walk.support_copy,
    orderedAmbientReturnPath, SimpleGraph.Walk.support_mapLe_eq_support, hleft]
  exact hsource

/-- A non-endpoint vertex occurring in a walk has a strict internal
coordinate. -/
private theorem exists_internalPosition_vertex_eq
    {start finish vertex : V} (path : G.Walk start finish)
    (hmem : vertex ∈ path.support) (hstart : vertex ≠ start)
    (hfinish : vertex ≠ finish) :
    ∃ position : InternalPosition path, position.vertex = vertex := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem with
    ⟨index, hindex, hindex_le⟩
  have hindex_ne_zero : index ≠ 0 := by
    intro hzero
    apply hstart
    rw [← hindex, hzero, SimpleGraph.Walk.getVert_zero]
  have hindex_ne_length : index ≠ path.length := by
    intro hlength
    apply hfinish
    rw [← hindex, hlength, SimpleGraph.Walk.getVert_length]
  have hindex_lt : index < path.length := lt_of_le_of_ne hindex_le hindex_ne_length
  let position : InternalPosition path := ⟨index - 1, by omega⟩
  refine ⟨position, ?_⟩
  change path.getVert (index - 1 + 1) = vertex
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hindex_ne_zero)]
  exact hindex

/-- A fully physical interpretation of one off-carrier reference exit.  Its
inside endpoint is a strict internal vertex of a completed return, and its
outside endpoint is exactly the return's external third-edge neighbour. -/
structure OffCarrierAttachmentWitness
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) where
  chord : OrderedReturnChord (orderedSiteReturnPairing hG sigma hSigma site)
  position : AmbientReturnInternalPosition hG sigma hSigma site chord
  inside_eq : position.vertex = exit.1.1.fst
  outside_eq :
    ambientReturnAttachmentNeighbor hG sigma hSigma site chord position =
      exit.1.1.snd
  external : IsExternalAttachment
    (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position

/-- Every genuinely off-carrier reference exit is an external attachment on
one completed physical return behind the sweep cut. -/
theorem exists_offCarrierAttachmentWitness
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) :
    Nonempty (OffCarrierAttachmentWitness hG sigma hSigma site cut exit) := by
  rcases exists_orderedReturnChord_inside_mem hG sigma hSigma site cut exit with
    ⟨chord, hleft, hright, hinside⟩
  let path := orderedChordAmbientPath hG sigma hSigma site chord
  have hstart : exit.1.1.fst ≠
      (cycleVertexOrder sigma site chord.left).1 := by
    intro heq
    apply exit.2.2
    rw [heq]
    exact (cycleVertexOrder sigma site chord.left).2
  have hfinish : exit.1.1.fst ≠
      (cycleVertexOrder sigma site chord.right).1 := by
    intro heq
    apply exit.2.2
    rw [heq]
    exact (cycleVertexOrder sigma site chord.right).2
  rcases exists_internalPosition_vertex_eq path hinside hstart hfinish with
    ⟨position, hposition⟩
  have houtside :
      ambientReturnAttachmentNeighbor hG sigma hSigma site chord position =
        exit.1.1.snd := by
    calc
      ambientReturnAttachmentNeighbor hG sigma hSigma site chord position =
          sigma.partner position.vertex :=
        ambientReturnAttachmentNeighbor_eq_partner
          hG sigma hSigma site chord position
      _ = sigma.partner exit.1.1.fst := congrArg sigma.partner hposition
      _ = exit.1.1.snd := exit.2.1
  have hexternal : IsExternalAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position := by
    unfold IsExternalAttachment
    change ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∉
      (orderedChordAmbientPath hG sigma hSigma site chord).support
    rw [houtside]
    intro houtsidePath
    apply exit.1.2.2
    have houtsideSource : exit.1.1.snd ∈
        (orderedReturnPath hG sigma hSigma site chord.left).support := by
      simpa only [path, orderedChordAmbientPath,
        SimpleGraph.Walk.support_copy, orderedAmbientReturnPath,
        SimpleGraph.Walk.support_mapLe_eq_support] using houtsidePath
    have hreachable : (commonResidualGraph G sigma site).Reachable
        (cycleVertexOrder sigma site chord.left).1 exit.1.1.snd :=
      ((orderedReturnPath hG sigma hSigma site chord.left).takeUntil
        exit.1.1.snd houtsideSource).reachable
    apply pairingBoundarySaturation_of_reachable
      (fun boundary => (cycleVertexOrder sigma site boundary).1)
      (orderedSiteReturnPairing hG sigma hSigma site)
      (carrierPrefixSelected cut) hleft
    · simpa only [carrierPrefixSelected, chord.partner_left] using hright
    · exact hreachable
  exact ⟨⟨chord, position, hposition, houtside, hexternal⟩⟩

/-- Every genuinely off-carrier reference exit produces the exact separator
face-side receipt consumed by the ambient-return horn. -/
theorem exists_attachmentExitSideReceipt_of_offCarrierReferenceExit
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (exit : OffCarrierReferenceMatchingExitDart
      hG sigma hSigma site cut) :
    ∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma site chord) := by
  let witness := Classical.choice
    (exists_offCarrierAttachmentWitness hG sigma hSigma site cut exit)
  refine ⟨witness.chord, ?_⟩
  exact nonempty_attachmentExitSideReceipt_of_external
    rotation minimal hG sigma hSigma site witness.chord witness.position
      witness.external

/-- The component-saturated carrier prefix has the route's desired dichotomy:
either a physical separator-exit receipt exists on a completed return, or its
entire ambient boundary is bounded by the two return stacks and the two
carrier-local pairing interfaces. -/
theorem attachmentReceipt_or_card_ambientExitDart_le_stacks_add_local
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (cut : CyclePosition sigma bond.site) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      Nat.card (AmbientExitDart hG sigma hSigma bond.site cut) ≤
        ((returnShoreMatching rotation minimal hG sigma hSigma bond false).stackAt
            cut).length +
          ((returnShoreMatching rotation minimal hG sigma hSigma bond true).stackAt
            cut).length +
          Nat.card (PairingBoundaryOpenEndpoint
            (orderedSiteSigmaPairing sigma bond.site)
            (carrierPrefixSelected cut)) +
          Nat.card (PairingBoundaryOpenEndpoint
            (orderedSiteTauPairing sigma bond.site)
            (carrierPrefixSelected cut)) := by
  by_cases hexit : Nonempty (OffCarrierReferenceMatchingExitDart
      hG sigma hSigma bond.site cut)
  · rcases hexit with ⟨exit⟩
    exact Or.inl <|
      exists_attachmentExitSideReceipt_of_offCarrierReferenceExit
        rotation minimal hG sigma hSigma bond.site cut exit
  · right
    letI : Finite (AmbientExitDart hG sigma hSigma bond.site cut) := by
      unfold AmbientExitDart
      infer_instance
    letI : Finite (OffCarrierReferenceMatchingExitDart
        hG sigma hSigma bond.site cut) := by
      unfold OffCarrierReferenceMatchingExitDart
      infer_instance
    have hcard : Nat.card (OffCarrierReferenceMatchingExitDart
        hG sigma hSigma bond.site cut) = 0 := by
      have hnotPositive : ¬0 < Nat.card (OffCarrierReferenceMatchingExitDart
          hG sigma hSigma bond.site cut) := by
        intro hpositive
        exact hexit (Finite.card_pos_iff.mp hpositive)
      omega
    have hbound :=
      card_ambientExitDart_le_stackLengths_add_offCarrierReference_add_local
        rotation minimal hG sigma hSigma bond cut
    omega

end

end OffCarrierReferenceAttachment

end Mettapedia.GraphTheory.FourColor.Compositional
