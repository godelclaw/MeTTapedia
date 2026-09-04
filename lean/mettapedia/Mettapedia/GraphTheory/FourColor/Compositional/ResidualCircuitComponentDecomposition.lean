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
open GoertzelV24ResidualReturnArc
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

/-- A canonical return path exhausts its connected component in the common
residual graph.  Endpoints have degree one and every internal path vertex has
degree two, so the path already uses every incident edge at each of its
vertices. -/
theorem orderedReturnPath_toSubgraph_verts_eq_commonComponent_supp
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (orderedReturnPath hG sigma hSigma site position).toSubgraph.verts =
      ((commonResidualGraph G sigma site).connectedComponentMk
        (cycleVertexOrder sigma site position).1).supp := by
  classical
  let H := commonResidualGraph G sigma site
  let path := orderedReturnPath hG sigma hSigma site position
  let start := (cycleVertexOrder sigma site position).1
  let finish := (cycleVertexOrder sigma site
    ((orderedSiteReturnPairing hG sigma hSigma site).partner position)).1
  have hpath : path.IsPath :=
    orderedReturnPath_isPath hG sigma hSigma site position
  have hnotNil : ¬ path.Nil :=
    orderedReturnPath_not_nil hG sigma hSigma site position
  have hdegree := degree_commonResidualGraph hG sigma hSigma site
  have hncardDegree (vertex : V) :
      (H.neighborSet vertex).ncard = H.degree vertex := by
    calc
      (H.neighborSet vertex).ncard =
          Fintype.card (H.neighborSet vertex) :=
        (Set.fintypeCard_eq_ncard (H.neighborSet vertex)).symm
      _ = H.degree vertex := H.card_neighborSet_eq_degree vertex
  have hclosed : ∀ vertex ∈ path.toSubgraph.verts, ∀ neighbor,
      H.Adj vertex neighbor → path.toSubgraph.Adj vertex neighbor := by
    intro vertex hvertex neighbor hadjacent
    have hsupport : vertex ∈ path.support :=
      path.mem_verts_toSubgraph.mp hvertex
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hsupport with
      ⟨index, hindex, hindexBound⟩
    have hneighborSubset : path.toSubgraph.neighborSet vertex ⊆
        H.neighborSet vertex := by
      intro candidate hcandidate
      exact hcandidate.adj_sub
    have hpathCard : (path.toSubgraph.neighborSet vertex).ncard =
        if index = 0 ∨ index = path.length then 1 else 2 := by
      by_cases hstartIndex : index = 0
      · rw [if_pos (Or.inl hstartIndex)]
        have hvertexStart : vertex = start := by
          calc
            vertex = path.getVert index := hindex.symm
            _ = start := by simpa [path, start, hstartIndex]
        have hcard := congrArg Set.ncard
          (hpath.neighborSet_toSubgraph_startpoint hnotNil)
        rw [hvertexStart]
        exact hcard.trans (Set.ncard_singleton path.snd)
      · by_cases hfinishIndex : index = path.length
        · rw [if_pos (Or.inr hfinishIndex)]
          have hvertexFinish : vertex = finish := by
            calc
              vertex = path.getVert index := hindex.symm
              _ = finish := by
                simpa [path, finish] using
                  (hpath.getVert_eq_end_iff hindexBound).2 hfinishIndex
          have hcard := congrArg Set.ncard
            (hpath.neighborSet_toSubgraph_endpoint hnotNil)
          rw [hvertexFinish]
          exact hcard.trans (Set.ncard_singleton path.penultimate)
        · rw [if_neg (not_or_intro hstartIndex hfinishIndex)]
          have hindexLt : index < path.length := by omega
          have hcard := hpath.ncard_neighborSet_toSubgraph_internal_eq_two
            hstartIndex hindexLt
          simpa only [hindex] using hcard
    have hambientCard : (H.neighborSet vertex).ncard =
        if index = 0 ∨ index = path.length then 1 else 2 := by
      rw [hncardDegree, hdegree]
      by_cases hendpoint : index = 0 ∨ index = path.length
      · simp only [hendpoint, if_true]
        rcases hendpoint with hstartIndex | hfinishIndex
        · have hvertexStart : vertex = start := by
            calc
              vertex = path.getVert index := hindex.symm
              _ = start := by simpa [path, start, hstartIndex]
          apply if_pos
          simpa [hvertexStart, start] using
            (cycleVertexOrder sigma site position).2
        · have hvertexFinish : vertex = finish := by
            calc
              vertex = path.getVert index := hindex.symm
              _ = finish := by
                simpa [path, finish] using
                  (hpath.getVert_eq_end_iff hindexBound).2 hfinishIndex
          apply if_pos
          simpa [hvertexFinish, finish] using
            (cycleVertexOrder sigma site
              ((orderedSiteReturnPairing hG sigma hSigma site).partner
                position)).2
      · simp only [hendpoint, if_false]
        apply if_neg
        intro hcarrier
        have hcases :=
          eq_start_or_eq_finish_of_mem_orderedReturnPath_support_of_mem_carrier
            hG sigma hSigma site position hsupport hcarrier
        rcases hcases with hvertexStart | hvertexFinish
        · apply hendpoint
          left
          apply (hpath.getVert_eq_start_iff hindexBound).1
          exact hindex.trans hvertexStart
        · apply hendpoint
          right
          apply (hpath.getVert_eq_end_iff hindexBound).1
          exact hindex.trans hvertexFinish
    have hneighborEq : path.toSubgraph.neighborSet vertex =
        H.neighborSet vertex := by
      apply Set.eq_of_subset_of_ncard_le hneighborSubset
      rw [hpathCard, hambientCard]
    change neighbor ∈ path.toSubgraph.neighborSet vertex
    rw [hneighborEq]
    exact hadjacent
  rcases path.toSubgraph_connected.exists_verts_eq_connectedComponentSupp
      hclosed with ⟨component, hcomponent⟩
  have hstartPath : start ∈ path.toSubgraph.verts := by
    exact path.start_mem_verts_toSubgraph
  have hstartComponent : start ∈ component.supp := by
    rw [← hcomponent]
    exact hstartPath
  have hcomponentEq : component = H.connectedComponentMk start :=
    ((component.mem_supp_iff start).1 hstartComponent).symm
  simpa only [H, path, start] using hcomponent.trans
    (congrArg SimpleGraph.ConnectedComponent.supp hcomponentEq)

/-- The support cardinality of one common return component is its canonical
return length plus its initial endpoint. -/
theorem commonComponent_ncard_eq_orderedReturnPath_length_add_one
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    ((commonResidualGraph G sigma site).connectedComponentMk
        (cycleVertexOrder sigma site position).1).supp.ncard =
      (orderedReturnPath hG sigma hSigma site position).length + 1 := by
  let path := orderedReturnPath hG sigma hSigma site position
  have hverts :=
    orderedReturnPath_toSubgraph_verts_eq_commonComponent_supp
      hG sigma hSigma site position
  rw [← hverts]
  have hset : path.toSubgraph.verts =
      (path.support.toFinset : Set V) := by
    ext vertex
    simp
  rw [hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup
    (orderedReturnPath_isPath hG sigma hSigma site position).support_nodup,
    path.length_support]

end

end ResidualCircuitComponentDecomposition

end Mettapedia.GraphTheory.FourColor.Compositional
