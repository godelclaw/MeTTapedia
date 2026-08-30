import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanFacePotential
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnPairing

/-!
# Face-shore transport along a residual return

The common residual graph before and after one alternating matching exchange
contains no edge of the alternating cycle.  Its degree-one edge at each cycle
vertex is the canonical third edge.  These facts connect the physical return
pairing to the generic exact-face-cut trail transport theorem.

The resulting endpoint theorem says that a residual return pairs third edges
on the same facial shore.  Noncrossing order and an oddness formula remain
separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualReturnShore

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24KauffmanFacePotential
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualFormationSwitch
open GoertzelV24ResidualReturnPairing
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

/-- The common residual graph is a literal subgraph of the ambient graph. -/
theorem commonResidualGraph_le
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    commonResidualGraph G sigma site ≤ G :=
  (inf_le_left : commonResidualGraph G sigma site ≤ residualGraph G sigma).trans
  (residualGraph_le sigma)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem penultimate_mapLe
    {H : SimpleGraph V} (h : G ≤ H) {start finish : V}
    (path : G.Walk start finish) :
    (path.mapLe h).penultimate = path.penultimate := by
  change (path.map (SimpleGraph.Hom.ofLE h)).penultimate = path.penultimate
  induction path with
  | nil => rfl
  | cons hadj path ih =>
    by_cases hnil : path.Nil
    · cases hnil
      rfl
    · have hmapNil :
          ¬(path.map (SimpleGraph.Hom.ofLE h)).Nil := by
        exact (SimpleGraph.Walk.nil_map_iff
          (SimpleGraph.Hom.ofLE h)).not.mpr hnil
      rw [SimpleGraph.Walk.map_cons]
      rw [SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hmapNil,
        SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hnil]
      exact ih

/-- No edge surviving both residual states belongs to the alternating cycle
on which the exchange is performed. -/
theorem commonResidualGraph_adj_not_cycle
    (sigma : Pairing V) {first second left right : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (hadj : (commonResidualGraph G sigma site).Adj left right) :
    s(left, right) ∉ site.cycle.edges := by
  intro hcycle
  have hleftSupport : left ∈ site.cycle.support :=
    site.cycle.fst_mem_support_of_mem_edges hcycle
  have hleftCarrier : left ∈ site.carrier := by
    rw [← site.cycle_support_eq]
    simpa using hleftSupport
  have halternating := site.cycle_edges_alternating s(left, right) hcycle
  rw [SimpleGraph.mem_edgeSet,
    GoertzelV24AlternatingMatchingComponent.alternatingGraph_adj] at halternating
  have hcommon := (commonResidualGraph_adj sigma site).1 hadj
  rcases halternating with hsigma | htau
  · exact hcommon.2.1 hsigma.1
  · have hswitch := Pairing.exchange_of_mem sigma site.tau site.carrier
      site.sigma_closed site.tau_closed hleftCarrier
    exact hcommon.2.2 (hswitch.trans htau.1)

/-- The canonical third neighbour at one vertex of an alternating site. -/
def siteThirdNeighbor
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : BoundaryVertex site.carrier) : V :=
  thirdNeighborAt hG sigma site.tau hSigma site.tau_supported vertex.1
    (site.disagree_on_carrier vertex.1 vertex.2)

theorem siteThirdNeighbor_spec
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : BoundaryVertex site.carrier) :
    G.Adj vertex.1 (siteThirdNeighbor hG sigma hSigma site vertex) ∧
      siteThirdNeighbor hG sigma hSigma site vertex ≠ sigma.partner vertex.1 ∧
      siteThirdNeighbor hG sigma hSigma site vertex ≠ site.tau.partner vertex.1 :=
  thirdNeighborAt_spec hG sigma site.tau hSigma site.tau_supported vertex.1
    (site.disagree_on_carrier vertex.1 vertex.2)

/-- The third edge, oriented away from the alternating-cycle vertex. -/
def siteThirdDart
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : BoundaryVertex site.carrier) : G.Dart :=
  ⟨(vertex.1, siteThirdNeighbor hG sigma hSigma site vertex),
    (siteThirdNeighbor_spec hG sigma hSigma site vertex).1⟩

/-- The canonical third edge survives in both residual states. -/
theorem commonResidualGraph_adj_siteThirdNeighbor
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : BoundaryVertex site.carrier) :
    (commonResidualGraph G sigma site).Adj vertex.1
      (siteThirdNeighbor hG sigma hSigma site vertex) := by
  rw [commonResidualGraph_adj]
  have hthird := siteThirdNeighbor_spec hG sigma hSigma site vertex
  refine ⟨hthird.1, hthird.2.1.symm, ?_⟩
  rw [Pairing.exchange_of_mem sigma site.tau site.carrier
    site.sigma_closed site.tau_closed vertex.2]
  exact hthird.2.2.symm

/-- The third neighbour is the unique common-residual neighbour at a cycle
vertex. -/
theorem eq_siteThirdNeighbor_of_commonResidualGraph_adj
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second neighbor : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (vertex : BoundaryVertex site.carrier)
    (hadj : (commonResidualGraph G sigma site).Adj vertex.1 neighbor) :
    neighbor = siteThirdNeighbor hG sigma hSigma site vertex := by
  have hcommon := (commonResidualGraph_adj sigma site).1 hadj
  have htauNe : site.tau.partner vertex.1 ≠ neighbor := by
    have hswitch := Pairing.exchange_of_mem sigma site.tau site.carrier
      site.sigma_closed site.tau_closed vertex.2
    exact hswitch ▸ hcommon.2.2
  exact (Classical.choose_spec
    (existsUnique_thirdNeighborAt hG sigma site.tau hSigma
      site.tau_supported
        (site.disagree_on_carrier vertex.1 vertex.2))).2 neighbor
        ⟨hcommon.1, hcommon.2.1.symm, htauNe.symm⟩

/-- A physical residual return joins canonical third darts on the same
facial shore of the operated alternating cycle. -/
theorem siteReturnPairing_thirdDarts_same_face_shore
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (vertex : BoundaryVertex bond.site.carrier) :
    dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site vertex) ∈ bond.faces ↔
      dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          ((siteReturnPairing hG sigma hSigma bond.site).partner vertex)) ∈
        bond.faces := by
  have hpairedNe : vertex.1 ≠
      ((siteReturnPairing hG sigma hSigma bond.site).partner vertex).1 := by
    intro hvalue
    have hsubtype :
        (siteReturnPairing hG sigma hSigma bond.site).partner vertex = vertex :=
      Subtype.ext hvalue.symm
    exact (siteReturnPairing hG sigma hSigma bond.site).partner_ne vertex hsubtype
  obtain ⟨path, hpath⟩ :=
    (siteReturnPairing_reachable hG sigma hSigma bond.site vertex).exists_isPath
  have hpathNil : ¬path.Nil := path.not_nil_of_ne hpairedNe
  let ambientPath : G.Walk vertex.1
      ((siteReturnPairing hG sigma hSigma bond.site).partner vertex).1 :=
    path.mapLe (commonResidualGraph_le sigma bond.site)
  have hambientNil : ¬ambientPath.Nil := by
    unfold ambientPath SimpleGraph.Walk.mapLe
    exact (SimpleGraph.Walk.nil_map_iff
      (SimpleGraph.Hom.ofLE (commonResidualGraph_le sigma bond.site))).not.mpr
        hpathNil
  have hambientSnd : ambientPath.snd = path.snd := by
    unfold ambientPath SimpleGraph.Walk.mapLe
    simpa using SimpleGraph.Walk.getVert_map
      (SimpleGraph.Hom.ofLE (commonResidualGraph_le sigma bond.site)) path 1
  have hambientPenultimate : ambientPath.penultimate = path.penultimate := by
    exact penultimate_mapLe (commonResidualGraph_le sigma bond.site) path
  have hfirst :
      ambientPath.firstDart hambientNil =
        siteThirdDart hG sigma hSigma bond.site vertex := by
    have hsnd := eq_siteThirdNeighbor_of_commonResidualGraph_adj
      hG sigma hSigma bond.site vertex (path.adj_snd hpathNil)
    apply SimpleGraph.Dart.ext
    rw [SimpleGraph.Walk.firstDart_toProd]
    change (vertex.1, ambientPath.snd) =
        (vertex.1, siteThirdNeighbor hG sigma hSigma bond.site vertex)
    rw [hambientSnd, hsnd]
  have hlast :
      rotation.toRotationSystem.alpha (ambientPath.lastDart hambientNil) =
        siteThirdDart hG sigma hSigma bond.site
          ((siteReturnPairing hG sigma hSigma bond.site).partner vertex) := by
    have hpenultimate := eq_siteThirdNeighbor_of_commonResidualGraph_adj
      hG sigma hSigma bond.site
        ((siteReturnPairing hG sigma hSigma bond.site).partner vertex)
        (path.adj_penultimate hpathNil).symm
    change (ambientPath.lastDart hambientNil).symm =
      siteThirdDart hG sigma hSigma bond.site
        ((siteReturnPairing hG sigma hSigma bond.site).partner vertex)
    apply SimpleGraph.Dart.ext
    rw [SimpleGraph.Dart.symm_toProd,
      SimpleGraph.Walk.lastDart_toProd]
    change
      (((siteReturnPairing hG sigma hSigma bond.site).partner vertex).1,
          ambientPath.penultimate) =
        (((siteReturnPairing hG sigma hSigma bond.site).partner vertex).1,
          siteThirdNeighbor hG sigma hSigma bond.site
            ((siteReturnPairing hG sigma hSigma bond.site).partner vertex))
    rw [hambientPenultimate, hpenultimate]
  have hexact : ∀ dart : rotation.toRotationSystem.D,
      faceSetIndicator rotation bond.faces
          (dartOrbitFace rotation.toRotationSystem dart) ≠
          faceSetIndicator rotation bond.faces
            (dartOrbitFace rotation.toRotationSystem
              (rotation.toRotationSystem.alpha dart)) ↔
        (rotation.toRotationSystem.edgeOf dart).1 ∈ bond.site.cycle.edges := by
    intro dart
    rw [bond.cycle_separates_faces]
    by_cases hleft : dartOrbitFace rotation.toRotationSystem dart ∈ bond.faces <;>
      by_cases hright : dartOrbitFace rotation.toRotationSystem
          (rotation.toRotationSystem.alpha dart) ∈ bond.faces <;>
      simp [faceSetIndicator, hleft]
  have hnot : ∀ edge : G.edgeSet, edge.1 ∈ ambientPath.edges →
      edge.1 ∉ bond.site.cycle.edges := by
    intro edge hedge hcycle
    rcases edge with ⟨edge, hedgeAmbient⟩
    change edge ∈ ambientPath.edges at hedge
    change edge ∈ bond.site.cycle.edges at hcycle
    have hedgePath : edge ∈ path.edges := by
      change edge ∈ (path.mapLe (commonResidualGraph_le sigma bond.site)).edges at hedge
      rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at hedge
    have hedgeCommon : edge ∈ (commonResidualGraph G sigma bond.site).edgeSet :=
      path.edges_subset_edgeSet hedgePath
    induction edge using Sym2.inductionOn with
    | _ left right =>
      have hadj : (commonResidualGraph G sigma bond.site).Adj left right := by
        exact (commonResidualGraph G sigma bond.site).mem_edgeSet.mp hedgeCommon
      exact commonResidualGraph_adj_not_cycle sigma bond.site hadj hcycle
  have hlabels :=
    rotation.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation (faceSetIndicator rotation bond.faces)
        (fun edge : G.edgeSet ↦ edge.1 ∈ bond.site.cycle.edges)
        hexact ambientPath hambientNil (hpath.isTrail.mapLe _ ) hnot
  rw [hfirst, hlast] at hlabels
  change
    dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site vertex) ∈ bond.faces ↔
      dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          ((siteReturnPairing hG sigma hSigma bond.site).partner vertex)) ∈
        bond.faces
  constructor
  · intro hleft
    by_contra hright
    have : (1 : F2) = 0 := by
      simpa [faceSetIndicator, hleft, hright] using hlabels
    norm_num at this
  · intro hright
    by_contra hleft
    have : (0 : F2) = 1 := by
      simpa [faceSetIndicator, hleft, hright] using hlabels
    norm_num at this

/-- The complete local residual receipt currently available at one noncentral
ordered-mesh site: a facial formation switch at every cycle vertex, the
physical return pairing through unchanged residual material, and preservation
of the exact facial shore along every return. -/
structure FacialFormationReturnShoreReceipt
    (rotation : Data G) (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (first second : V) where
  sigma_supported : sigma.SupportedBy G
  bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second
  formation : ∀ vertex : BoundaryVertex bond.site.carrier,
    Nonempty (FacialFormationSwitchReceipt rotation sigma bond vertex.1)
  returnPairing : Pairing (BoundaryVertex bond.site.carrier)
  return_reachable : ∀ vertex : BoundaryVertex bond.site.carrier,
    (commonResidualGraph G sigma bond.site).Reachable vertex.1
      (returnPairing.partner vertex).1
  return_is_canonical : returnPairing =
    siteReturnPairing hG sigma sigma_supported bond.site
  return_same_face_shore : ∀ vertex : BoundaryVertex bond.site.carrier,
    dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma sigma_supported bond.site vertex) ∈
        bond.faces ↔
      dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma sigma_supported bond.site
          (returnPairing.partner vertex)) ∈ bond.faces

/-- One global residual-defect minimizer supplies the full local
formation/return/shore receipt at every noncentral ordered-mesh step.  The
cubic incident-edge triples are constructed from the minimal map rather than
assumed as an independent input. -/
theorem exists_exchangeRigid_with_facialFormation_returnPairing_and_shore_at_every_globalMeshStep
    {a b : Nat}
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ hG : HasCubicIncidentEdgeTriples G,
      ∃ sigma : Pairing V,
        sigma.SupportedBy G ∧
        2 ≤ GoertzelV24ResidualDefectDescent.residualDefect G sigma ∧
        ∀ step : GlobalMeshStep rotation ordered,
          sigma.partner (globalFirstVertex rotation ordered step) =
              globalSecondVertex rotation ordered step ∨
            Nonempty (FacialFormationReturnShoreReceipt rotation hG sigma
              (globalFirstVertex rotation ordered step)
              (globalSecondVertex rotation ordered step)) := by
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  let hG : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
      fun vertex => by
        rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_facialFormationSwitch_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨hG, sigma, hSigma, hodd, ?_⟩
  intro step
  rcases hsites step with hcentral | hbond
  · exact Or.inl hcentral
  · rcases hbond with ⟨bond, hformation⟩
    let returnPairing : Pairing (BoundaryVertex bond.site.carrier) :=
      siteReturnPairing hG sigma hSigma bond.site
    refine Or.inr ⟨{
      sigma_supported := hSigma
      bond := bond
      formation := fun vertex => hformation vertex.1 vertex.2
      returnPairing := returnPairing
      return_reachable := ?_
      return_is_canonical := rfl
      return_same_face_shore := ?_ }⟩
    · intro vertex
      exact siteReturnPairing_reachable hG sigma hSigma bond.site vertex
    · intro vertex
      exact siteReturnPairing_thirdDarts_same_face_shore rotation
        minimal.spherical.cubic minimal.vertexRotationCyclic hG sigma hSigma
        bond vertex

end

end GoertzelV24ResidualReturnShore

end Mettapedia.GraphTheory.FourColor
