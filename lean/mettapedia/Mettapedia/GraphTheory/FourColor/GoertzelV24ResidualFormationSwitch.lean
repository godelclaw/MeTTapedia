import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshResidualSiteFacialBond

/-!
# The local formation carried by a residual matching exchange

At a disagreement cycle of two perfect matchings in a cubic graph, every
cycle vertex has exactly three relevant incident edges: the first matching
edge, the second matching edge, and a unique third edge.  Exchanging the
first matching for the second on the cycle removes the second edge from the
residual two-factor, inserts the first edge, and leaves the third edge fixed.

For a spherical residual mesh site, the alternating cycle is an exact facial
bond.  The fixed third edge therefore has both incident faces in the same
face shore.  This is the literal local formation switch needed before any
global residual-component or oddness calculation.  No decrease of residual
defect and no compatibility between different mesh sites is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualFormationSwitch

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualExchange
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

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- Cubicity leaves one and only one neighbour at a vertex after the two
distinct matching neighbours have been removed.  Unlike the global
`complementPartner` theorem, only disagreement at this one vertex is needed.
-/
theorem existsUnique_thirdNeighborAt
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma tau : Pairing V)
    (hSigma : sigma.SupportedBy G) (hTau : tau.SupportedBy G)
    {vertex : V} (hdisagree : sigma.partner vertex ≠ tau.partner vertex) :
    ∃! third : V,
      G.Adj vertex third ∧
        third ≠ sigma.partner vertex ∧
        third ≠ tau.partner vertex := by
  let candidates :=
    ((G.neighborFinset vertex).erase (sigma.partner vertex)).erase
      (tau.partner vertex)
  have hcard : candidates.card = 1 := by
    have hcubic : (G.neighborFinset vertex).card = 3 := by
      calc
        (G.neighborFinset vertex).card = G.degree vertex :=
          SimpleGraph.card_neighborFinset_eq_degree G vertex
        _ = (incidentEdgeFinset G vertex).card :=
          (incidentEdgeFinset_card_eq_degree vertex).symm
        _ = 3 :=
          incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
            hG vertex
    have hSigmaMem : sigma.partner vertex ∈ G.neighborFinset vertex := by
      simpa using hSigma vertex
    have hTauMem : tau.partner vertex ∈ G.neighborFinset vertex := by
      simpa using hTau vertex
    have hTauErase :
        tau.partner vertex ∈
          (G.neighborFinset vertex).erase (sigma.partner vertex) :=
      Finset.mem_erase.mpr ⟨hdisagree.symm, hTauMem⟩
    have hSigmaCard := Finset.card_erase_of_mem hSigmaMem
    have hTauCard := Finset.card_erase_of_mem hTauErase
    dsimp only [candidates]
    omega
  rcases Finset.card_eq_one.mp hcard with ⟨third, hthird⟩
  refine ⟨third, ?_, ?_⟩
  · have hmem : third ∈ candidates := by simp [hthird]
    simp only [candidates, Finset.mem_erase,
      SimpleGraph.mem_neighborFinset] at hmem
    exact ⟨hmem.2.2, hmem.2.1, hmem.1⟩
  · intro other hother
    have hmem : other ∈ candidates := by
      simp only [candidates, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hother.2.2, hother.2.1, hother.1⟩
    rw [hthird] at hmem
    simpa using hmem

/-- The unique incident edge not used by either matching at a disagreement
vertex. -/
def thirdNeighborAt
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma tau : Pairing V)
    (hSigma : sigma.SupportedBy G) (hTau : tau.SupportedBy G)
    (vertex : V) (hdisagree : sigma.partner vertex ≠ tau.partner vertex) : V :=
  Classical.choose
    (existsUnique_thirdNeighborAt hG sigma tau hSigma hTau hdisagree)

theorem thirdNeighborAt_spec
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma tau : Pairing V)
    (hSigma : sigma.SupportedBy G) (hTau : tau.SupportedBy G)
    (vertex : V) (hdisagree : sigma.partner vertex ≠ tau.partner vertex) :
    G.Adj vertex
        (thirdNeighborAt hG sigma tau hSigma hTau vertex hdisagree) ∧
      thirdNeighborAt hG sigma tau hSigma hTau vertex hdisagree ≠
        sigma.partner vertex ∧
      thirdNeighborAt hG sigma tau hSigma hTau vertex hdisagree ≠
        tau.partner vertex :=
  (Classical.choose_spec
    (existsUnique_thirdNeighborAt hG sigma tau hSigma hTau hdisagree)).1

/-- The complete local receipt at one vertex of a facial alternating site.
The first four residual fields express the formation switch; the last field
says that its unchanged third edge lies wholly in one of the two face shores.
-/
structure FacialFormationSwitchReceipt
    (rotation : Data G) (sigma : Pairing V)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness
      rotation sigma first second)
    (vertex : V) where
  vertex_mem : vertex ∈ bond.site.carrier
  third : V
  third_adjacent : G.Adj vertex third
  third_ne_sigma : third ≠ sigma.partner vertex
  third_ne_tau : third ≠ bond.site.tau.partner vertex
  third_edge_not_cycle : s(vertex, third) ∉ bond.site.cycle.edges
  old_tau_residual :
    (residualGraph G sigma).Adj vertex (bond.site.tau.partner vertex)
  old_sigma_not_residual :
    ¬(residualGraph G sigma).Adj vertex (sigma.partner vertex)
  old_third_residual : (residualGraph G sigma).Adj vertex third
  new_sigma_residual :
    (residualGraph G
      (sigma.exchange bond.site.tau bond.site.carrier
        bond.site.sigma_closed bond.site.tau_closed)).Adj
      vertex (sigma.partner vertex)
  new_tau_not_residual :
    ¬(residualGraph G
      (sigma.exchange bond.site.tau bond.site.carrier
        bond.site.sigma_closed bond.site.tau_closed)).Adj
      vertex (bond.site.tau.partner vertex)
  new_third_residual :
    (residualGraph G
      (sigma.exchange bond.site.tau bond.site.carrier
        bond.site.sigma_closed bond.site.tau_closed)).Adj vertex third
  third_faces_same_shore :
    ∀ dart : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.edgeOf dart).1 = s(vertex, third) →
        (dartOrbitFace rotation.toRotationSystem dart ∈ bond.faces ↔
          dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha dart) ∈ bond.faces)

/-- Construct the exact local formation switch at every vertex of one facial
alternating site. -/
theorem facialFormationSwitchReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (sigma : Pairing V)
    (hSigma : sigma.SupportedBy G)
    {first second vertex : V}
    (bond : ProperAlternatingSiteFacialBondWitness
      rotation sigma first second)
    (hvertex : vertex ∈ bond.site.carrier) :
    Nonempty (FacialFormationSwitchReceipt rotation sigma bond vertex) := by
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
      fun current => by
        rw [incidentEdgeFinset_card_eq_degree, hCubic current]
  have hdisagree :
      sigma.partner vertex ≠ bond.site.tau.partner vertex :=
    bond.site.disagree_on_carrier vertex hvertex
  let third := thirdNeighborAt htriples sigma bond.site.tau
    hSigma bond.site.tau_supported vertex hdisagree
  have hthird := thirdNeighborAt_spec htriples sigma bond.site.tau
    hSigma bond.site.tau_supported vertex hdisagree
  have hthirdNotCycle : s(vertex, third) ∉ bond.site.cycle.edges := by
    intro hedge
    have hcarrierEdge := bond.site.cycle_edges_alternating
      s(vertex, third) hedge
    rw [SimpleGraph.mem_edgeSet,
      GoertzelV24AlternatingMatchingComponent.alternatingGraph_adj] at hcarrierEdge
    rcases hcarrierEdge with hSigmaEdge | hTauEdge
    · exact hthird.2.1 hSigmaEdge.1.symm
    · exact hthird.2.2 hTauEdge.1.symm
  let switched := sigma.exchange bond.site.tau bond.site.carrier
    bond.site.sigma_closed bond.site.tau_closed
  have hswitch : switched.partner vertex = bond.site.tau.partner vertex := by
    exact Pairing.exchange_of_mem sigma bond.site.tau bond.site.carrier
      bond.site.sigma_closed bond.site.tau_closed hvertex
  refine ⟨{
    vertex_mem := hvertex
    third := third
    third_adjacent := hthird.1
    third_ne_sigma := hthird.2.1
    third_ne_tau := hthird.2.2
    third_edge_not_cycle := hthirdNotCycle
    old_tau_residual := ⟨bond.site.tau_supported vertex, hdisagree⟩
    old_sigma_not_residual := by
      intro hold
      exact hold.2 rfl
    old_third_residual := ⟨hthird.1, hthird.2.1.symm⟩
    new_sigma_residual := by
      change G.Adj vertex (sigma.partner vertex) ∧
        switched.partner vertex ≠ sigma.partner vertex
      refine ⟨hSigma vertex, ?_⟩
      rw [hswitch]
      exact hdisagree.symm
    new_tau_not_residual := by
      intro hnew
      exact hnew.2 hswitch
    new_third_residual := by
      change G.Adj vertex third ∧ switched.partner vertex ≠ third
      refine ⟨hthird.1, ?_⟩
      rw [hswitch]
      exact hthird.2.2.symm
    third_faces_same_shore := by
      intro dart hdart
      have hnotSeparator :
          ¬((dartOrbitFace rotation.toRotationSystem dart ∈ bond.faces ∧
                dartOrbitFace rotation.toRotationSystem
                  (rotation.toRotationSystem.alpha dart) ∉ bond.faces) ∨
              (dartOrbitFace rotation.toRotationSystem dart ∉ bond.faces ∧
                dartOrbitFace rotation.toRotationSystem
                  (rotation.toRotationSystem.alpha dart) ∈ bond.faces)) := by
        intro hseparator
        apply hthirdNotCycle
        rw [← hdart]
        exact (bond.cycle_separates_faces dart).2 hseparator
      tauto }⟩

/-- One global residual-defect minimizer supplies the literal local formation
switch at every vertex of every nontrivial ordered-mesh site cycle. -/
theorem exists_exchangeRigid_with_facialFormationSwitch_at_every_globalMeshStep
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
            ∀ vertex ∈ bond.site.carrier,
              Nonempty
                (FacialFormationSwitchReceipt rotation sigma bond vertex) := by
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_facialBond_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hodd, ?_⟩
  intro step
  rcases hsites step with hcentral | hbond
  · exact Or.inl hcentral
  · rcases hbond with ⟨bond⟩
    exact Or.inr ⟨bond, fun vertex hvertex =>
      facialFormationSwitchReceipt rotation minimal sigma hSigma bond hvertex⟩

end

end GoertzelV24ResidualFormationSwitch

end Mettapedia.GraphTheory.FourColor
