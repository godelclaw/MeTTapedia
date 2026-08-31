import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteGeometry
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteMatchingOverlap

/-!
# Alternating geometry on a compatible deletion overlap

Every residual mesh site compares one globally fixed perfect matching with a
second matching extracted from its selected deletion colouring.  If two site
matchings have a compatible finite overlap state, they make the same matching
decision on each ambient edge retained by both deletions.  Taking symmetric
difference with the same global matching therefore gives the same alternating
graph on that common carrier.

This is the semantic bridge from deletion-colouring coherence to residual
cycle geometry.  It is pointwise on common retained edges; it does not claim
that the two distinguished alternating components are globally equal.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.AlternatingOverlapGeometry

open Amplitude
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualSiteGeometry
open ResidualSiteMatchingOverlap
open ResidualSiteProvenance
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- Replacing the second pairing by one with the same decision on a fixed
edge does not change whether that edge belongs to the alternating graph with
a fixed first pairing. -/
theorem alternatingGraph_adj_congr_right
    (sigma source target : Pairing V) {left right : V}
    (hagrees : source.partner left = right ↔ target.partner left = right) :
    (alternatingGraph sigma source).Adj left right ↔
      (alternatingGraph sigma target).Adj left right := by
  rw [alternatingGraph_adj, alternatingGraph_adj]
  constructor
  · rintro (⟨hsigma, hsource⟩ | ⟨hsource, hsigma⟩)
    · exact Or.inl ⟨hsigma, fun htarget => hsource (hagrees.mpr htarget)⟩
    · exact Or.inr ⟨hagrees.mp hsource, hsigma⟩
  · rintro (⟨hsigma, htarget⟩ | ⟨htarget, hsigma⟩)
    · exact Or.inl ⟨hsigma, fun hsource => htarget (hagrees.mp hsource)⟩
    · exact Or.inr ⟨hagrees.mpr htarget, hsigma⟩

/-- Compatible deletion-matching states have identical alternating-graph
membership on every ambient edge retained by both deletions. -/
theorem alternatingGraphs_agree_on_common_retained_edge
    {sourceData targetData : AdjacentPairData G}
    (sigma : Pairing V)
    (source : DeletionColorMatching.DeletionMatchingState sourceData)
    (target : DeletionColorMatching.DeletionMatchingState targetData)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hcompatible : (matchingOverlapState source target).Compatible)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge sourceData edge)
    (htarget : IsRetainedAmbientEdge targetData edge) :
    edge.1 ∈ (alternatingGraph sigma (source.pairing hcubic)).edgeSet ↔
      edge.1 ∈ (alternatingGraph sigma (target.pairing hcubic)).edgeSet := by
  have hpairing := deletionMatchingStates_agree_on_common_retained_edge
    source target hcubic hcompatible edge hsource htarget
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      rw [mem_edges_iff (MatchingBridge.toPerm_mem_pairings _),
        mem_edges_iff (MatchingBridge.toPerm_mem_pairings _)] at hpairing
      change (source.pairing hcubic).partner left = right ↔
        (target.pairing hcubic).partner left = right at hpairing
      change (alternatingGraph sigma (source.pairing hcubic)).Adj left right ↔
        (alternatingGraph sigma (target.pairing hcubic)).Adj left right
      exact alternatingGraph_adj_congr_right sigma
        (source.pairing hcubic) (target.pairing hcubic) hpairing

/-- The global colouring provenance nested in the final two-sector receipt. -/
def pairingProvenance
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {step : GlobalMeshStep rotation ordered}
    (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    GlobalSitePairingProvenance rotation minimal ordered step :=
  receipt.returnShore.facialBond.provenance.provenance

/-- The alternating site nested in the final two-sector receipt. -/
def alternatingSite
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {step : GlobalMeshStep rotation ordered}
    (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    GoertzelV24OrderedMeshResidualSiteMatching.ProperAlternatingSiteWitness G
      sigma (globalFirstVertex rotation ordered step)
        (globalSecondVertex rotation ordered step) :=
  receipt.base.base.bond.site

/-- Two final residual receipts with compatible overlap states have the same
alternating-graph edge set on their exact common retained carrier. -/
theorem provenanced_alternatingGraphs_agree_on_common_retained_edge
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {sourceStep targetStep : GlobalMeshStep rotation ordered}
    (source : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma sourceStep)
    (target : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma targetStep)
    (hcompatible :
      (globalMatchingOverlapState (pairingProvenance source)
        (pairingProvenance target)).Compatible)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge (pairingProvenance source).site.data edge)
    (htarget : IsRetainedAmbientEdge (pairingProvenance target).site.data edge) :
    edge.1 ∈ (alternatingGraph sigma (alternatingSite source).tau).edgeSet ↔
      edge.1 ∈ (alternatingGraph sigma (alternatingSite target).tau).edgeSet := by
  change edge.1 ∈
      (alternatingGraph sigma source.base.base.bond.site.tau).edgeSet ↔
    edge.1 ∈
      (alternatingGraph sigma target.base.base.bond.site.tau).edgeSet
  rw [source.site_tau_eq_pairing, target.site_tau_eq_pairing]
  simpa [pairingProvenance,
    globalMatchingOverlapState, provenanceDeletionMatchingState,
    DeletionColorMatching.DeletionMatchingState.pairing,
    GlobalSitePairingProvenance.pairing] using
    alternatingGraphs_agree_on_common_retained_edge sigma
      (provenanceDeletionMatchingState (pairingProvenance source))
      (provenanceDeletionMatchingState (pairingProvenance target))
      (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal)
      hcompatible edge hsource htarget

/-- Every common retained edge of the source site's distinguished alternating
cycle belongs to the target site's matching symmetric difference whenever the
finite overlap state is compatible.  The target component containing that edge
need not be its distinguished central component. -/
theorem source_cycle_edge_mem_target_alternatingGraph
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {sourceStep targetStep : GlobalMeshStep rotation ordered}
    (source : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma sourceStep)
    (target : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma targetStep)
    (hcompatible :
      (globalMatchingOverlapState (pairingProvenance source)
        (pairingProvenance target)).Compatible)
    (edge : G.edgeSet)
    (hedge : edge.1 ∈ (alternatingSite source).cycle.edges)
    (hsource : IsRetainedAmbientEdge (pairingProvenance source).site.data edge)
    (htarget : IsRetainedAmbientEdge (pairingProvenance target).site.data edge) :
    edge.1 ∈ (alternatingGraph sigma (alternatingSite target).tau).edgeSet := by
  apply (provenanced_alternatingGraphs_agree_on_common_retained_edge
    source target hcompatible edge hsource htarget).mp
  exact (alternatingSite source).cycle_edges_alternating edge.1 hedge

end

end Mettapedia.GraphTheory.FourColor.Compositional.AlternatingOverlapGeometry
