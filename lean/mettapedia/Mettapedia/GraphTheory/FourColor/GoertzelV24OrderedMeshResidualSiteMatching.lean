import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairMatchingExtraction
import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingSiteGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshGlobalSites
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge

/-!
# One residual-defect minimizer against every ordered-mesh site

Fix a graph-backed least Tait counterexample containing an ordered mesh.  The
minimum-residual-oddness theorem chooses one graph-supported perfect matching
`sigma` globally.  At every globally indexed row or column step, minimality
also supplies a Tait colouring of the adjacent-pair deletion.  Its absent
colour class extends across the deleted central edge to a second supported
matching `tau`.

The same `sigma` is therefore exchange-rigid against a site matching at every
physical mesh step.  The quantifier order is deliberately
`exists sigma, forall step, exists tau`: no compatibility between the site
matchings at distinct steps is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshResidualSiteMatching

open Compositional.AlternatingSiteGeometry
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphTaitBridge
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

/-- Compatibility name for the semantic proper alternating-component witness.
New code should use `Compositional.AlternatingSiteGeometry` directly. -/
abbrev ProperAlternatingSiteWitness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (sigma : Pairing V) (first second : V) :=
  Compositional.AlternatingSiteGeometry.ProperAlternatingComponentWitness
    G sigma first second

/-- One minimum-residual-oddness matching is rigid against a supported
matching through every physical row/column edge of an ordered mesh.  The
site matching may depend on the step; the minimizer does not. -/
theorem exists_exchangeRigid_with_central_pairing_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      ∀ step : GlobalMeshStep rotation ordered,
        ∃ tau : Pairing V,
          tau.SupportedBy G ∧
          tau.partner (globalFirstVertex rotation ordered step) =
            globalSecondVertex rotation ordered step ∧
          ∀ (s : Finset V)
            (hSigmaS : ∀ vertex ∈ s, sigma.partner vertex ∈ s)
            (hTauS : ∀ vertex ∈ s, tau.partner vertex ∈ s),
            residualDefect G sigma ≤
              residualDefect G
                (sigma.exchange tau s hSigmaS hTauS) := by
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hnoBridge : ∀ edge ∈ G.edgeSet, ¬ G.IsBridge edge := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ left right =>
        have hadj : G.Adj left right := G.mem_edgeSet.mp hedge
        let dart : G.Dart := ⟨(left, right), hadj⟩
        have hfree :=
          (GoertzelV24RotationEdgeBridge.edgeBridgeFree_toRotationSystem_iff
            rotation).1 minimal.edgeBridgeFree dart
        simpa [dart, SimpleGraph.Dart.edge] using hfree
  have hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1 := by
    intro edge
    exact hnoBridge edge.1 edge.2
  have hnot : ¬ TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  obtain ⟨minimizer⟩ :=
    nonempty_residualDefectMinimizer hCubic hfree hnot
  refine ⟨minimizer.pairing, minimizer.supported,
    minimizer.two_le_defect, ?_⟩
  intro step
  let site := selectedGlobalKempeSite rotation minimal ordered step
  have hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 := by
    intro vertex
    rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  obtain ⟨tau, htau, hcentral⟩ :=
    exists_central_supportedPairing_of_not_taitColorable
      site.data hcubic hnot site.base site.baseTait
  have hcentralGlobal :
      tau.partner (globalFirstVertex rotation ordered step) =
        globalSecondVertex rotation ordered step := by
    rw [← site.first_eq, ← site.second_eq]
    exact hcentral
  refine ⟨tau, htau, hcentralGlobal, ?_⟩
  intro s hSigmaS hTauS
  exact minimizer.exchange_minimal tau s hSigmaS hTauS htau

/-- A single minimum-residual-defect matching controls every ordered-mesh
edge.  If the matching does not already use the edge, the edge lies in a
proper alternating component against a site matching, and exchange on that
component cannot decrease residual defect.

No bound on the component and no compatibility between components at
different mesh steps is asserted.  Those are genuinely planar/global
obligations, not consequences of matching algebra alone. -/
theorem exists_exchangeRigid_with_proper_alternatingComponent_at_every_globalMeshStep
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
          Nonempty
            (ProperAlternatingSiteWitness G sigma
              (globalFirstVertex rotation ordered step)
              (globalSecondVertex rotation ordered step)) := by
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_central_pairing_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hodd, ?_⟩
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
      fun vertex => by
        rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  have hnot : ¬ TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  intro step
  obtain ⟨tau, hTau, hcentral, hrigid⟩ := hsites step
  by_cases hSigmaCentral :
      sigma.partner (globalFirstVertex rotation ordered step) =
        globalSecondVertex rotation ordered step
  · exact Or.inl hSigmaCentral
  · right
    obtain ⟨site, _⟩ := properAlternatingComponentWitness_of_partner_ne
        htriples hnot sigma hSigma tau hTau
          (fun carrier hSigmaClosed hTauClosed =>
            hrigid carrier hSigmaClosed hTauClosed)
          (globalFirstVertex rotation ordered step)
          (globalSecondVertex rotation ordered step)
          hcentral hSigmaCentral
    exact ⟨site⟩

end

end GoertzelV24OrderedMeshResidualSiteMatching

end Mettapedia.GraphTheory.FourColor
