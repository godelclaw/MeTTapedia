import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSide
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshResidualSiteMatching

/-!
# Colouring provenance for residual site matchings

The residual-defect argument historically retained only an existential site
matching.  The adjacent-pair overlap theory, however, is expressed using the
globally selected deletion colouring.  This module keeps the missing bridge:
the site matching is the absent colour class of that very colouring, completed
by the deleted central edge.

No compatibility between different sites is asserted.  The purpose of this
receipt is to make the next synchronization question well typed rather than
to assume its answer.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance

open Compositional.AlternatingSiteGeometry
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TaitMatchingDecomposition
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

/-- Cubicity of a graph-backed least counterexample in the incidence-cardinal
form consumed by adjacent-pair deletion theory. -/
theorem incidentEdgeFinset_card_eq_three
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 := by
  have hregular : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  intro vertex
  rw [incidentEdgeFinset_card_eq_degree, hregular vertex]

/-- Proof-carrying origin of the matching used at one globally indexed mesh
site.  The retained `site_eq_selected` field identifies its colouring with
the same global choice used by the overlap-state and holonomy layers. -/
structure GlobalSitePairingProvenance
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (step : GlobalMeshStep rotation ordered) where
  site : GlobalKempeSite rotation ordered minimal step
  site_eq_selected :
    site = selectedGlobalKempeSite rotation minimal ordered step
  absentColor : Fin 3
  absentAtBoundary : ∀ port,
    site.data.degreeTwoBoundaryData.colorWord site.base port ≠
      taitColor absentColor

namespace GlobalSitePairingProvenance

/-- The ambient perfect matching obtained from the recorded absent colour
class and the deleted central edge. -/
def pairing
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {step : GlobalMeshStep rotation ordered}
    (receipt : GlobalSitePairingProvenance rotation minimal ordered step) :
    Pairing V :=
  centralCompletionPairing receipt.site.data
    (incidentEdgeFinset_card_eq_three rotation minimal)
    receipt.site.base receipt.site.baseTait receipt.absentColor
    receipt.absentAtBoundary

/-- The provenance pairing uses only ambient graph edges. -/
theorem pairing_supported
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {step : GlobalMeshStep rotation ordered}
    (receipt : GlobalSitePairingProvenance rotation minimal ordered step) :
    receipt.pairing.SupportedBy G :=
  centralCompletionPairing_supportedBy receipt.site.data
    (incidentEdgeFinset_card_eq_three rotation minimal)
    receipt.site.base receipt.site.baseTait receipt.absentColor
    receipt.absentAtBoundary

/-- The provenance pairing contains the physical mesh edge indexing the
site. -/
theorem pairing_partner_globalFirst
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {step : GlobalMeshStep rotation ordered}
    (receipt : GlobalSitePairingProvenance rotation minimal ordered step) :
    receipt.pairing.partner (globalFirstVertex rotation ordered step) =
      globalSecondVertex rotation ordered step := by
  rw [← receipt.site.first_eq, ← receipt.site.second_eq]
  exact centralCompletionPairing_partner_first receipt.site.data
    (incidentEdgeFinset_card_eq_three rotation minimal)
    receipt.site.base receipt.site.baseTait receipt.absentColor
    receipt.absentAtBoundary

end GlobalSitePairingProvenance

/-- Every global mesh step has a provenance receipt based on the already
selected adjacent-pair deletion colouring. -/
theorem nonempty_globalSitePairingProvenance
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (step : GlobalMeshStep rotation ordered) :
    Nonempty (GlobalSitePairingProvenance rotation minimal ordered step) := by
  let site := selectedGlobalKempeSite rotation minimal ordered step
  have hnot : ¬ TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      site.data (incidentEdgeFinset_card_eq_three rotation minimal) hnot
      site.base site.baseTait
  obtain ⟨absentColor, habsent⟩ :=
    exists_taitColor_absent_of_sameSidePairs
      (site.data.degreeTwoBoundaryData.colorWord site.base)
      hsame.1 hsame.2
  exact ⟨{
    site := site
    site_eq_selected := rfl
    absentColor := absentColor
    absentAtBoundary := habsent }⟩

/-- One global minimum-residual-defect matching is exchange-rigid against a
matching whose exact colouring and absent colour are retained at every mesh
step.  This strengthens the old existential site-matching interface only by
remembering provenance; it adds no cross-site compatibility hypothesis. -/
theorem exists_exchangeRigid_with_provenance_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      ∀ step : GlobalMeshStep rotation ordered,
        ∃ receipt : GlobalSitePairingProvenance rotation minimal ordered step,
          ∀ (s : Finset V)
            (hSigmaS : ∀ vertex ∈ s, sigma.partner vertex ∈ s)
            (hTauS : ∀ vertex ∈ s,
              receipt.pairing.partner vertex ∈ s),
            residualDefect G sigma ≤
              residualDefect G
                (sigma.exchange receipt.pairing s hSigmaS hTauS) := by
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hnoBridge : ∀ edge ∈ G.edgeSet, ¬G.IsBridge edge := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ left right =>
        have hadj : G.Adj left right := G.mem_edgeSet.mp hedge
        let dart : G.Dart := ⟨(left, right), hadj⟩
        have hfree :=
          (edgeBridgeFree_toRotationSystem_iff rotation).1
            minimal.edgeBridgeFree dart
        simpa [dart, SimpleGraph.Dart.edge] using hfree
  have hfree : ∀ edge : G.edgeSet, ¬G.IsBridge edge.1 := by
    intro edge
    exact hnoBridge edge.1 edge.2
  have hnot : ¬TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  obtain ⟨sigma, hSigma, hodd, hminimal⟩ :=
    exists_exchangeRigid_residualOddness_of_cubic_edgeBridgeFree
      hCubic hfree hnot
  refine ⟨sigma, hSigma, hodd, ?_⟩
  intro step
  let receipt := Classical.choice
    (nonempty_globalSitePairingProvenance rotation minimal ordered step)
  refine ⟨receipt, ?_⟩
  intro s hSigmaS hTauS
  exact hminimal receipt.pairing s hSigmaS hTauS
    receipt.pairing_supported

/-- A proper alternating residual cycle whose second matching is tied to the
globally selected deletion colouring by an explicit provenance receipt. -/
structure ProvenancedAlternatingSiteReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered) where
  provenance : GlobalSitePairingProvenance rotation minimal ordered step
  site : ProperAlternatingSiteWitness G sigma
    (globalFirstVertex rotation ordered step)
    (globalSecondVertex rotation ordered step)
  site_tau_eq : site.tau = provenance.pairing

/-- The globally selected deletion colourings can be retained all the way to
the proper alternating-cycle alternative at every mesh step. -/
theorem exists_exchangeRigid_with_provenanced_alternatingSite_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      ∀ step : GlobalMeshStep rotation ordered,
        sigma.partner (globalFirstVertex rotation ordered step) =
            globalSecondVertex rotation ordered step ∨
          Nonempty (ProvenancedAlternatingSiteReceipt
            rotation minimal ordered sigma step) := by
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_provenance_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hodd, ?_⟩
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
      fun vertex => by
        rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  have hnot : ¬TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  intro step
  obtain ⟨provenance, hrigid⟩ := hsites step
  let tau := provenance.pairing
  have hTau : tau.SupportedBy G := provenance.pairing_supported
  have hcentral :
      tau.partner (globalFirstVertex rotation ordered step) =
        globalSecondVertex rotation ordered step :=
    provenance.pairing_partner_globalFirst
  by_cases hSigmaCentral :
      sigma.partner (globalFirstVertex rotation ordered step) =
        globalSecondVertex rotation ordered step
  · exact Or.inl hSigmaCentral
  · right
    let first := globalFirstVertex rotation ordered step
    let second := globalSecondVertex rotation ordered step
    have hcentral' : tau.partner first = second := hcentral
    obtain ⟨site, hsiteTau⟩ :=
      properAlternatingComponentWitness_of_partner_ne
        htriples hnot sigma hSigma tau hTau
          (fun carrier hSigmaClosed hTauClosed =>
            hrigid carrier hSigmaClosed hTauClosed)
          first second hcentral' hSigmaCentral
    refine Nonempty.intro ?_
    exact ({
      provenance := provenance
      site := site
      site_tau_eq := by simpa only [tau] using hsiteTau } :
        ProvenancedAlternatingSiteReceipt
          rotation minimal ordered sigma step)

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance
