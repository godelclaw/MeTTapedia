import Mettapedia.GraphTheory.FourColor.GoertzelV24FinitePathEndpointCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualFormationSwitch

/-!
# The return pairing outside a residual exchange cycle

A finite graph whose marked vertices have degree one and whose other
vertices have degree two canonically pairs the marked endpoints by connected
component.  Apply this to the intersection of the residual graph before and
after a matching exchange.  At an alternating-cycle vertex the intersection
retains only the third edge, while away from the exchange carrier the two
residual graphs agree.  Consequently the common off-cycle material induces a
literal perfect return pairing on the cycle vertices.

This is the physical return object needed by the formation calculus.  No
noncrossing order, component-count formula, oddness change, or compatibility
between distinct mesh sites is asserted in this module.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualReturnPairing

open GoertzelV24FinitePathEndpointCount
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualFormationSwitch
open GoertzelV24ResidualTwoFactor
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TaitMatchingPair
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open SimpleGraph
open SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u w

/-! ## A generic endpoint pairing -/

variable {W : Type w} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The finite carrier of displayed degree-one boundary vertices. -/
abbrev BoundaryVertex (boundary : Finset W) :=
  {vertex : W // vertex ∈ boundary}

/-- In a finite graph with degree one exactly on `boundary` and degree two
elsewhere, every boundary vertex has a unique distinct reachable boundary
partner. -/
theorem existsUnique_reachable_boundaryPartner
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2)
    (start : BoundaryVertex boundary) :
    ∃! finish : BoundaryVertex boundary,
      finish ≠ start ∧ H.Reachable start.1 finish.1 := by
  classical
  let component : H.ConnectedComponent :=
    H.connectedComponentMk start.1
  let root : component.supp :=
    ⟨start.1,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hcomponentDegreeEq (vertex : component.supp) :
      component.toSimpleGraph.degree vertex = H.degree vertex.1 := by
    let neighbors : component.toSimpleGraph.neighborSet vertex ≃
        H.neighborSet vertex.1 :=
      { toFun := fun other =>
          ⟨other.1.1,
            (component.toSimpleGraph_adj vertex.2 other.1.2).1 other.2⟩
        invFun := fun other => by
          have hmem : other.1 ∈ component.supp :=
            component.mem_supp_of_adj_mem_supp vertex.2 other.2
          exact ⟨⟨other.1, hmem⟩,
            (component.toSimpleGraph_adj vertex.2 hmem).2 other.2⟩
        left_inv := fun other => by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := fun other => by
          apply Subtype.ext
          rfl }
    rw [← component.toSimpleGraph.card_neighborSet_eq_degree,
      ← H.card_neighborSet_eq_degree]
    exact Fintype.card_congr neighbors
  have hcomponentDegree (vertex : component.supp) :
      component.toSimpleGraph.degree vertex = 1 ∨
        component.toSimpleGraph.degree vertex = 2 := by
    rw [hcomponentDegreeEq, hdegree]
    split <;> simp
  have hrootDegree : component.toSimpleGraph.degree root = 1 := by
    rw [hcomponentDegreeEq, hdegree]
    simp [root, start.2]
  have hcard :
      (degreeOneVertices component.toSimpleGraph).card = 2 :=
    card_degreeOneVertices_eq_two component.toSimpleGraph
      component.connected_toSimpleGraph hcomponentDegree root hrootDegree
  have hrootMem : root ∈ degreeOneVertices component.toSimpleGraph :=
    (mem_degreeOneVertices_iff component.toSimpleGraph root).2 hrootDegree
  have heraseCard :
      ((degreeOneVertices component.toSimpleGraph).erase root).card = 1 := by
    rw [Finset.card_erase_of_mem hrootMem, hcard]
  rcases Finset.card_eq_one.mp heraseCard with ⟨other, hotherSet⟩
  have hotherErase :
      other ∈ (degreeOneVertices component.toSimpleGraph).erase root := by
    rw [hotherSet]
    simp
  have hotherNe : other ≠ root := Finset.ne_of_mem_erase hotherErase
  have hotherMem :
      other ∈ degreeOneVertices component.toSimpleGraph :=
    Finset.mem_of_mem_erase hotherErase
  have hotherComponentDegree :
      component.toSimpleGraph.degree other = 1 :=
    (mem_degreeOneVertices_iff component.toSimpleGraph other).1 hotherMem
  have hotherAmbientDegree : H.degree other.1 = 1 := by
    rw [← hcomponentDegreeEq other]
    exact hotherComponentDegree
  have hotherBoundary : other.1 ∈ boundary := by
    by_contra hnot
    rw [hdegree other.1, if_neg hnot] at hotherAmbientDegree
    omega
  let finish : BoundaryVertex boundary := ⟨other.1, hotherBoundary⟩
  have hfinishNe : finish ≠ start := by
    intro heq
    have hval : finish.1 = start.1 := congrArg Subtype.val heq
    apply hotherNe
    apply Subtype.ext
    simpa [finish, root] using hval
  have hfinishReachable : H.Reachable start.1 finish.1 :=
    component.reachable_of_mem_supp root.2 other.2
  refine ⟨finish, ⟨hfinishNe, hfinishReachable⟩, ?_⟩
  intro candidate hcand
  have hcandidateMem : candidate.1 ∈ component.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hcand.2).symm
  let candidateInComponent : component.supp :=
    ⟨candidate.1, hcandidateMem⟩
  have hcandidateDegree :
      component.toSimpleGraph.degree candidateInComponent = 1 := by
    rw [hcomponentDegreeEq, hdegree]
    simp [candidateInComponent, candidate.2]
  have hcandidateEndpoint :
      candidateInComponent ∈ degreeOneVertices component.toSimpleGraph :=
    (mem_degreeOneVertices_iff component.toSimpleGraph
      candidateInComponent).2 hcandidateDegree
  have hcandidateNeRoot : candidateInComponent ≠ root := by
    intro heq
    have hval : candidateInComponent.1 = root.1 :=
      congrArg Subtype.val heq
    apply hcand.1
    apply Subtype.ext
    simpa [candidateInComponent, root] using hval
  have hcandidateErase :
      candidateInComponent ∈
        (degreeOneVertices component.toSimpleGraph).erase root :=
    Finset.mem_erase.mpr ⟨hcandidateNeRoot, hcandidateEndpoint⟩
  rw [hotherSet] at hcandidateErase
  have hcandidateOther : candidateInComponent = other := by
    simpa using hcandidateErase
  have hval : candidateInComponent.1 = other.1 :=
    congrArg Subtype.val hcandidateOther
  apply Subtype.ext
  simpa [candidateInComponent, finish] using hval

/-- The other degree-one endpoint in the same component. -/
def boundaryPartner
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2)
    (start : BoundaryVertex boundary) : BoundaryVertex boundary :=
  Classical.choose
    (existsUnique_reachable_boundaryPartner boundary hdegree start)

theorem boundaryPartner_spec
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2)
    (start : BoundaryVertex boundary) :
    boundaryPartner boundary hdegree start ≠ start ∧
      H.Reachable start.1 (boundaryPartner boundary hdegree start).1 :=
  (Classical.choose_spec
    (existsUnique_reachable_boundaryPartner boundary hdegree start)).1

/-- Connected components of the degree-`1/2` graph induce a fixed-point-free
involution on the displayed degree-one boundary. -/
def boundaryReturnPairing
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2) :
    Pairing (BoundaryVertex boundary) where
  partner := boundaryPartner boundary hdegree
  partner_partner := by
    intro start
    let finish := boundaryPartner boundary hdegree start
    have hstart := boundaryPartner_spec boundary hdegree start
    have hfinishUnique :=
      (Classical.choose_spec
        (existsUnique_reachable_boundaryPartner boundary hdegree finish)).2
    exact (hfinishUnique start ⟨hstart.1.symm, hstart.2.symm⟩).symm
  partner_ne := fun start =>
    (boundaryPartner_spec boundary hdegree start).1

theorem boundaryReturnPairing_reachable
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2)
    (start : BoundaryVertex boundary) :
    H.Reachable start.1
      ((boundaryReturnPairing boundary hdegree).partner start).1 :=
  (boundaryPartner_spec boundary hdegree start).2

/-! ## The common graph before and after one residual exchange -/

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- Edges present in the residual graph both before and after exchanging on
one alternating site. -/
def commonResidualGraph
    (G : SimpleGraph V) [DecidableRel G.Adj] (sigma : Pairing V)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    SimpleGraph V :=
  residualGraph G sigma ⊓
    residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)

noncomputable instance commonResidualGraphAdjDecidable
    (G : SimpleGraph V) [DecidableRel G.Adj] (sigma : Pairing V)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    DecidableRel (commonResidualGraph G sigma site).Adj :=
  Classical.decRel _

@[simp] theorem commonResidualGraph_adj
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {left right : V} :
    (commonResidualGraph G sigma site).Adj left right ↔
      G.Adj left right ∧
        sigma.partner left ≠ right ∧
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed).partner left ≠ right := by
  simp only [commonResidualGraph, SimpleGraph.inf_adj, residualGraph_adj]
  constructor
  · rintro ⟨⟨hadjacent, hsigma⟩, _, hswitched⟩
    exact ⟨hadjacent, hsigma, hswitched⟩
  · rintro ⟨hadjacent, hsigma, hswitched⟩
    exact ⟨⟨hadjacent, hsigma⟩, hadjacent, hswitched⟩

theorem neighborFinset_commonResidualGraph
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : V) :
    (commonResidualGraph G sigma site).neighborFinset vertex =
      ((G.neighborFinset vertex).erase (sigma.partner vertex)).erase
        ((sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed).partner vertex) := by
  ext neighbor
  simp only [SimpleGraph.mem_neighborFinset,
    commonResidualGraph_adj, Finset.mem_erase]
  tauto

theorem degree_commonResidualGraph
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : V) :
    (commonResidualGraph G sigma site).degree vertex =
      if vertex ∈ site.carrier then 1 else 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_commonResidualGraph]
  by_cases hvertex : vertex ∈ site.carrier
  · rw [Pairing.exchange_of_mem sigma site.tau site.carrier
      site.sigma_closed site.tau_closed hvertex, if_pos hvertex]
    have hcard : (G.neighborFinset vertex).card = 3 := by
      calc
        (G.neighborFinset vertex).card = G.degree vertex :=
          SimpleGraph.card_neighborFinset_eq_degree G vertex
        _ = (incidentEdgeFinset G vertex).card :=
          (incidentEdgeFinset_card_eq_degree vertex).symm
        _ = 3 :=
          incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
            hG vertex
    have hSigmaMem :
        sigma.partner vertex ∈ G.neighborFinset vertex := by
      simpa using hSigma vertex
    have hTauMem :
        site.tau.partner vertex ∈
          (G.neighborFinset vertex).erase (sigma.partner vertex) := by
      exact Finset.mem_erase.mpr
        ⟨(site.disagree_on_carrier vertex hvertex).symm,
          by simpa using site.tau_supported vertex⟩
    rw [Finset.card_erase_of_mem hTauMem,
      Finset.card_erase_of_mem hSigmaMem]
    omega
  · rw [Pairing.exchange_of_notMem sigma site.tau site.carrier
      site.sigma_closed site.tau_closed hvertex,
      Finset.erase_idem, if_neg hvertex]
    rw [← neighborFinset_residualGraph (G := G) sigma vertex]
    exact card_neighborFinset_residualGraph_eq_two hG sigma hSigma vertex

/-- The actual off-cycle return pairing for one alternating residual site. -/
def siteReturnPairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Pairing (BoundaryVertex site.carrier) :=
  boundaryReturnPairing (H := commonResidualGraph G sigma site) site.carrier
    (degree_commonResidualGraph hG sigma hSigma site)

theorem siteReturnPairing_reachable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : BoundaryVertex site.carrier) :
    (commonResidualGraph G sigma site).Reachable vertex.1
      ((siteReturnPairing hG sigma hSigma site).partner vertex).1 :=
  boundaryReturnPairing_reachable
    (H := commonResidualGraph G sigma site) site.carrier
    (degree_commonResidualGraph hG sigma hSigma site) vertex

/-- Every nontrivial global mesh site carries both its facial local formation
receipts and the physical endpoint pairing induced by the unchanged residual
material. -/
theorem exists_exchangeRigid_with_facialFormation_and_returnPairing_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ GoertzelV24ResidualDefectDescent.residualDefect G sigma ∧
      ∀ step : GlobalMeshStep rotation ordered,
        sigma.partner (globalFirstVertex rotation ordered step) =
            globalSecondVertex rotation ordered step ∨
          ∃ bond : ProperAlternatingSiteFacialBondWitness rotation sigma
              (globalFirstVertex rotation ordered step)
              (globalSecondVertex rotation ordered step),
            (∀ vertex ∈ bond.site.carrier,
              Nonempty
                (FacialFormationSwitchReceipt rotation sigma bond vertex)) ∧
            ∃ returnPairing : Pairing (BoundaryVertex bond.site.carrier),
              ∀ vertex : BoundaryVertex bond.site.carrier,
                (commonResidualGraph G sigma bond.site).Reachable vertex.1
                  (returnPairing.partner vertex).1 := by
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_facialFormationSwitch_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hodd, ?_⟩
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
      fun vertex => by
        rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  intro step
  rcases hsites step with hcentral | hbond
  · exact Or.inl hcentral
  · rcases hbond with ⟨bond, hformation⟩
    refine Or.inr ⟨bond, hformation, siteReturnPairing htriples sigma hSigma bond.site, ?_⟩
    exact siteReturnPairing_reachable htriples sigma hSigma bond.site

end

end GoertzelV24ResidualReturnPairing

end Mettapedia.GraphTheory.FourColor
