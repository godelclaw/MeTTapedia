import Mettapedia.GraphTheory.FourColor.Compositional.ResidualExchangeComponentLocalization

/-!
# Physical decomposition of carrier-touching residual components

The finite residual circuit records which boundary return strands are joined
by the local matching on an alternating carrier.  This file strengthens the
boundary-to-boundary reachability theorem to arbitrary physical vertices:
every vertex in a carrier-touching component lies on common residual material
reached from a boundary position in the same finite circuit.

This is the set-theoretic cover needed before comparing circuit parity with
the cardinality parity of the corresponding physical residual component.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualCircuitComponentDecomposition

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualTwoFactor
open MatchingParity
open ResidualCircuitParity
open ResidualCircuitPhysicalReachability
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Generic boundary-state decomposition for a graph obtained by adding one
local pairing to the common residual graph. -/
theorem exists_eqvGen_and_common_reachable_of_completed_reachable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (localPairing : Pairing (CyclePosition sigma site))
    {physicalGraph : SimpleGraph V}
    (hadj : ∀ {left right : V}, physicalGraph.Adj left right →
      (commonResidualGraph G sigma site).Adj left right ∨
        ∃ position : CyclePosition sigma site,
          (cycleVertexOrder sigma site position).1 = left ∧
          (cycleVertexOrder sigma site
            (localPairing.partner position)).1 = right)
    (root : CyclePosition sigma site) (target : V)
    (hreach : physicalGraph.Reachable
      (cycleVertexOrder sigma site root).1 target) :
    ∃ position : CyclePosition sigma site,
      Relation.EqvGen
        (AlternatingStep
          (orderedSiteReturnPairing hG sigma hSigma site) localPairing)
        root position ∧
      (commonResidualGraph G sigma site).Reachable
        (cycleVertexOrder sigma site position).1 target := by
  let returns := orderedSiteReturnPairing hG sigma hSigma site
  have hpath := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hreach
  have hstateOf : ∀ {current : V},
      Relation.ReflTransGen physicalGraph.Adj
        (cycleVertexOrder sigma site root).1 current →
      ∃ position : CyclePosition sigma site,
        Relation.EqvGen (AlternatingStep returns localPairing) root position ∧
        (commonResidualGraph G sigma site).Reachable
          (cycleVertexOrder sigma site position).1 current := by
    intro current path
    induction path with
    | refl =>
        exact ⟨root, Relation.EqvGen.refl _, SimpleGraph.Reachable.rfl⟩
    | @tail middle right hprefix hedge ih =>
        rcases ih with ⟨position, habstract, hcommon⟩
        rcases hadj hedge with hcommonEdge |
          ⟨boundaryPosition, hboundaryLeft, hboundaryRight⟩
        · exact ⟨position, habstract,
            hcommon.trans hcommonEdge.reachable⟩
        · have htoBoundary : (commonResidualGraph G sigma site).Reachable
              (cycleVertexOrder sigma site position).1
              (cycleVertexOrder sigma site boundaryPosition).1 := by
            simpa only [hboundaryLeft] using hcommon
          have hboundaryCases :=
            eq_or_eq_orderedReturnPartner_of_commonResidual_reachable
              hG sigma hSigma site position boundaryPosition htoBoundary
          have habstractBoundary : Relation.EqvGen
              (AlternatingStep returns localPairing) root boundaryPosition := by
            rcases hboundaryCases with hsame | hreturn
            · simpa only [hsame] using habstract
            · exact Relation.EqvGen.trans root position boundaryPosition
                habstract (Relation.EqvGen.rel _ _ (Or.inl hreturn))
          have habstractLocal : Relation.EqvGen
              (AlternatingStep returns localPairing) root
              (localPairing.partner boundaryPosition) :=
            Relation.EqvGen.trans root boundaryPosition
              (localPairing.partner boundaryPosition) habstractBoundary
              (Relation.EqvGen.rel _ _ (Or.inr rfl))
          refine ⟨localPairing.partner boundaryPosition,
            habstractLocal, ?_⟩
          rw [hboundaryRight]
  exact hstateOf hpath

/-- An old residual component rooted on the carrier is exactly the union of
common-return pieces based at positions in its finite old circuit. -/
theorem oldResidual_reachable_iff_exists_eqvGen_and_common_reachable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) (target : V) :
    (residualGraph G sigma).Reachable
        (cycleVertexOrder sigma site root).1 target ↔
      ∃ position : CyclePosition sigma site,
        Relation.EqvGen
          (AlternatingStep
            (orderedSiteReturnPairing hG sigma hSigma site)
            (orderedSiteTauPairing sigma site)) root position ∧
        (commonResidualGraph G sigma site).Reachable
          (cycleVertexOrder sigma site position).1 target := by
  constructor
  · intro hreach
    apply exists_eqvGen_and_common_reachable_of_completed_reachable
      hG sigma hSigma site (orderedSiteTauPairing sigma site) _ root target hreach
    intro left right hedge
    rcases (oldResidualGraph_adj_iff_common_or_tau sigma site).1 hedge with
      hcommon | ⟨hleft, htau⟩
    · exact Or.inl hcommon
    · let position : CyclePosition sigma site :=
        (cycleVertexOrder sigma site).symm ⟨left, hleft⟩
      have hposition : cycleVertexOrder sigma site position =
          (⟨left, hleft⟩ : BoundaryVertex site.carrier) :=
        (cycleVertexOrder sigma site).apply_symm_apply ⟨left, hleft⟩
      refine Or.inr ⟨position, congrArg Subtype.val hposition, ?_⟩
      have hpartner := congrArg Subtype.val
        (cycleVertexOrder_orderedSiteTauPairing_partner sigma site position)
      calc
        (cycleVertexOrder sigma site
            ((orderedSiteTauPairing sigma site).partner position)).1 =
            site.tau.partner (cycleVertexOrder sigma site position).1 := hpartner
        _ = site.tau.partner left := by rw [congrArg Subtype.val hposition]
        _ = right := htau
  · rintro ⟨position, habstract, hcommon⟩
    exact (oldResidual_reachable_of_eqvGen
      hG sigma hSigma site habstract).trans
        (hcommon.map (SimpleGraph.Hom.ofLE
          (show commonResidualGraph G sigma site ≤ residualGraph G sigma from
            inf_le_left)))

/-- The analogous exact decomposition after exchange, with the local
`sigma` pairing completing the common return material. -/
theorem newResidual_reachable_iff_exists_eqvGen_and_common_reachable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) (target : V) :
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).Reachable
        (cycleVertexOrder sigma site root).1 target ↔
      ∃ position : CyclePosition sigma site,
        Relation.EqvGen
          (AlternatingStep
            (orderedSiteReturnPairing hG sigma hSigma site)
            (orderedSiteSigmaPairing sigma site)) root position ∧
        (commonResidualGraph G sigma site).Reachable
          (cycleVertexOrder sigma site position).1 target := by
  constructor
  · intro hreach
    apply exists_eqvGen_and_common_reachable_of_completed_reachable
      hG sigma hSigma site (orderedSiteSigmaPairing sigma site) _ root target hreach
    intro left right hedge
    rcases (newResidualGraph_adj_iff_common_or_sigma
      sigma hSigma site).1 hedge with
      hcommon | ⟨hleft, hsigma⟩
    · exact Or.inl hcommon
    · let position : CyclePosition sigma site :=
        (cycleVertexOrder sigma site).symm ⟨left, hleft⟩
      have hposition : cycleVertexOrder sigma site position =
          (⟨left, hleft⟩ : BoundaryVertex site.carrier) :=
        (cycleVertexOrder sigma site).apply_symm_apply ⟨left, hleft⟩
      refine Or.inr ⟨position, congrArg Subtype.val hposition, ?_⟩
      have hpartner := congrArg Subtype.val
        (cycleVertexOrder_orderedSiteSigmaPairing_partner sigma site position)
      calc
        (cycleVertexOrder sigma site
            ((orderedSiteSigmaPairing sigma site).partner position)).1 =
            sigma.partner (cycleVertexOrder sigma site position).1 := hpartner
        _ = sigma.partner left := by rw [congrArg Subtype.val hposition]
        _ = right := hsigma
  · rintro ⟨position, habstract, hcommon⟩
    exact (newResidual_reachable_of_eqvGen
      hG sigma hSigma site habstract).trans
        (hcommon.map (SimpleGraph.Hom.ofLE
          (show commonResidualGraph G sigma site ≤
              residualGraph G
                (sigma.exchange site.tau site.carrier
                  site.sigma_closed site.tau_closed) from inf_le_right)))

end

end ResidualCircuitComponentDecomposition

end Mettapedia.GraphTheory.FourColor.Compositional
