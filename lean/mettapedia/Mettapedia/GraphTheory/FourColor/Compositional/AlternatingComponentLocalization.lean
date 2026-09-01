import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingOverlapGeometry
import Mettapedia.GraphTheory.FiniteEdgeDifference

/-!
# Alternating-component localization across adjacent-pair deletions

Compatible deletion-matching states identify the two matching symmetric
differences on every edge retained by both deletions.  This module makes the
exceptional carrier explicit: one adjacent-pair deletion has a five-edge
footprint, consisting of its central edge and four boundary edges.

Consequently every edge of a source alternating cycle either survives in the
target alternating graph or lies in the union of the two five-edge
footprints.  More generally, every source-cycle arc avoiding that union is a
walk in one target alternating component.  This is a localization theorem,
not an identification of the two distinguished components.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.AlternatingComponentLocalization

open AlternatingOverlapGeometry
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
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- The five ambient edges removed or cut open by an adjacent-pair deletion. -/
def deletionFootprint (data : AdjacentPairData G) : Finset G.edgeSet :=
  insert (centralEdge data) (Finset.univ.image data.boundaryEdge)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Membership in the explicit five-edge footprint is exactly failure of the
ambient-edge retention predicate. -/
theorem mem_deletionFootprint_iff
    (data : AdjacentPairData G) (edge : G.edgeSet) :
    edge ∈ deletionFootprint data ↔ ¬ IsRetainedAmbientEdge data edge := by
  rw [not_isRetainedAmbientEdge_iff]
  simp only [deletionFootprint, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro (hcentral | ⟨port, hport⟩)
    · exact Or.inl (congrArg Subtype.val hcentral)
    · exact Or.inr ⟨port, (congrArg Subtype.val hport).symm⟩
  · rintro (hcentral | ⟨port, hport⟩)
    · exact Or.inl (Subtype.ext hcentral)
    · exact Or.inr ⟨port, Subtype.ext hport.symm⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- An adjacent-pair deletion has exactly five exceptional ambient edges. -/
theorem card_deletionFootprint (data : AdjacentPairData G) :
    (deletionFootprint data).card = 5 := by
  rw [deletionFootprint, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _
      (fun _ _ h =>
        GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_injective
          data (congrArg Subtype.val h))]
    simp
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨port, hport⟩
    exact
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue_ne_boundaryEdgeValue
        data port (congrArg Subtype.val hport.symm)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The exceptional carrier for comparing two adjacent-pair deletions has at
most ten ambient edges. -/
theorem card_union_deletionFootprint_le
    (sourceData targetData : AdjacentPairData G) :
    (deletionFootprint sourceData ∪ deletionFootprint targetData).card ≤ 10 := by
  calc
    (deletionFootprint sourceData ∪ deletionFootprint targetData).card ≤
        (deletionFootprint sourceData).card +
          (deletionFootprint targetData).card := Finset.card_union_le _ _
    _ = 10 := by rw [card_deletionFootprint, card_deletionFootprint]

/-- The value-level exceptional edge set used to delete the two footprints
from a simple graph. -/
def overlapFootprintValues
    (sourceData targetData : AdjacentPairData G) : Finset (Sym2 V) :=
  (deletionFootprint sourceData ∪ deletionFootprint targetData).image
    Subtype.val

omit [Fintype V] [DecidableRel G.Adj] in
/-- Passing from ambient-edge subtypes to their values cannot enlarge the
ten-edge overlap footprint. -/
theorem card_overlapFootprintValues_le
    (sourceData targetData : AdjacentPairData G) :
    (overlapFootprintValues sourceData targetData).card ≤ 10 :=
  (Finset.card_image_le.trans
    (card_union_deletionFootprint_le sourceData targetData))

/-- Two compatible deletion-matching states have identical alternating-graph
membership outside their two five-edge footprints.  This graph-free semantic
form is the local interface later used by mesh and path constructions. -/
theorem alternatingGraphs_agree_outside_deletionFootprints
    {sourceData targetData : AdjacentPairData G}
    (sigma : Pairing V)
    (source : DeletionColorMatching.DeletionMatchingState sourceData)
    (target : DeletionColorMatching.DeletionMatchingState targetData)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hcompatible :
      (ResidualSiteMatchingOverlap.matchingOverlapState source target).Compatible)
    (edge : G.edgeSet)
    (houtside : edge ∉
      deletionFootprint sourceData ∪ deletionFootprint targetData) :
    edge.1 ∈ (alternatingGraph sigma (source.pairing hcubic)).edgeSet ↔
      edge.1 ∈ (alternatingGraph sigma (target.pairing hcubic)).edgeSet := by
  have hsource : IsRetainedAmbientEdge sourceData edge := by
    by_contra hnot
    exact houtside (Finset.mem_union_left _
      ((mem_deletionFootprint_iff _ _).2 hnot))
  have htarget : IsRetainedAmbientEdge targetData edge := by
    by_contra hnot
    exact houtside (Finset.mem_union_right _
      ((mem_deletionFootprint_iff _ _).2 hnot))
  exact AlternatingOverlapGeometry.alternatingGraphs_agree_on_common_retained_edge
    sigma source target hcubic hcompatible edge hsource htarget

/-- Compatible deletion-matching states become literally equal after their
two local footprints are deleted from the alternating graphs. -/
theorem alternatingGraphs_delete_overlapFootprints_eq
    {sourceData targetData : AdjacentPairData G}
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (source : DeletionColorMatching.DeletionMatchingState sourceData)
    (target : DeletionColorMatching.DeletionMatchingState targetData)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hcompatible :
      (ResidualSiteMatchingOverlap.matchingOverlapState source target).Compatible) :
    (alternatingGraph sigma (source.pairing hcubic)).deleteEdges
        (overlapFootprintValues sourceData targetData : Set (Sym2 V)) =
      (alternatingGraph sigma (target.pairing hcubic)).deleteEdges
        (overlapFootprintValues sourceData targetData : Set (Sym2 V)) := by
  let sourceGraph := alternatingGraph sigma (source.pairing hcubic)
  let targetGraph := alternatingGraph sigma (target.pairing hcubic)
  let footprint := overlapFootprintValues sourceData targetData
  have hsourceLe : sourceGraph ≤ G :=
    alternatingGraph_le sigma (source.pairing hcubic) hSigma
      (source.pairing_supported hcubic)
  have htargetLe : targetGraph ≤ G :=
    alternatingGraph_le sigma (target.pairing hcubic) hSigma
      (target.pairing_supported hcubic)
  ext left right
  simp only [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hadj, houtside⟩
    let edge : G.edgeSet := ⟨s(left, right),
      G.mem_edgeSet.mpr (hsourceLe hadj)⟩
    have hedgeOutside : edge ∉
        deletionFootprint sourceData ∪ deletionFootprint targetData := by
      intro hmem
      apply houtside
      change s(left, right) ∈ footprint
      exact Finset.mem_image.2 ⟨edge, hmem, rfl⟩
    have hagrees := alternatingGraphs_agree_outside_deletionFootprints
      sigma source target hcubic hcompatible edge hedgeOutside
    refine ⟨?_, houtside⟩
    exact targetGraph.mem_edgeSet.mp
      (hagrees.mp (sourceGraph.mem_edgeSet.mpr hadj))
  · rintro ⟨hadj, houtside⟩
    let edge : G.edgeSet := ⟨s(left, right),
      G.mem_edgeSet.mpr (htargetLe hadj)⟩
    have hedgeOutside : edge ∉
        deletionFootprint sourceData ∪ deletionFootprint targetData := by
      intro hmem
      apply houtside
      change s(left, right) ∈ footprint
      exact Finset.mem_image.2 ⟨edge, hmem, rfl⟩
    have hagrees := alternatingGraphs_agree_outside_deletionFootprints
      sigma source target hcubic hcompatible edge hedgeOutside
    refine ⟨?_, houtside⟩
    exact sourceGraph.mem_edgeSet.mp
      (hagrees.mpr (targetGraph.mem_edgeSet.mpr hadj))

/-- Compatible provenanced sites have identical alternating-graph membership
on every ambient edge outside their two deletion footprints. -/
theorem provenanced_alternatingGraphs_agree_outside_deletionFootprints
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
    (houtside :
      edge ∉ deletionFootprint (pairingProvenance source).site.data ∪
        deletionFootprint (pairingProvenance target).site.data) :
    edge.1 ∈ (alternatingGraph sigma (alternatingSite source).tau).edgeSet ↔
      edge.1 ∈ (alternatingGraph sigma (alternatingSite target).tau).edgeSet := by
  have hsource :
      IsRetainedAmbientEdge (pairingProvenance source).site.data edge := by
    by_contra hnot
    exact houtside (Finset.mem_union_left _
      ((mem_deletionFootprint_iff _ _).2 hnot))
  have htarget :
      IsRetainedAmbientEdge (pairingProvenance target).site.data edge := by
    by_contra hnot
    exact houtside (Finset.mem_union_right _
      ((mem_deletionFootprint_iff _ _).2 hnot))
  exact provenanced_alternatingGraphs_agree_on_common_retained_edge
    source target hcompatible edge hsource htarget

/-- After deleting at most ten exceptional edge values, the two matching
symmetric-difference graphs are literally equal. -/
theorem provenanced_alternatingGraphs_delete_overlapFootprints_eq
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
        (pairingProvenance target)).Compatible) :
    (alternatingGraph sigma (alternatingSite source).tau).deleteEdges
        (overlapFootprintValues
          (pairingProvenance source).site.data
          (pairingProvenance target).site.data) =
      (alternatingGraph sigma (alternatingSite target).tau).deleteEdges
        (overlapFootprintValues
          (pairingProvenance source).site.data
          (pairingProvenance target).site.data) := by
  let sourceGraph := alternatingGraph sigma (alternatingSite source).tau
  let targetGraph := alternatingGraph sigma (alternatingSite target).tau
  let footprint := overlapFootprintValues
    (pairingProvenance source).site.data
    (pairingProvenance target).site.data
  have hsourceLe : sourceGraph ≤ G :=
    alternatingGraph_le sigma (alternatingSite source).tau
      source.returnShore.base.sigma_supported
      (alternatingSite source).tau_supported
  have htargetLe : targetGraph ≤ G :=
    alternatingGraph_le sigma (alternatingSite target).tau
      target.returnShore.base.sigma_supported
      (alternatingSite target).tau_supported
  ext left right
  simp only [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hadj, houtside⟩
    let edge : G.edgeSet := ⟨s(left, right),
      G.mem_edgeSet.mpr (hsourceLe hadj)⟩
    have hedgeOutside :
        edge ∉ deletionFootprint (pairingProvenance source).site.data ∪
          deletionFootprint (pairingProvenance target).site.data := by
      intro hmem
      apply houtside
      change s(left, right) ∈ footprint
      exact Finset.mem_image.2 ⟨edge, hmem, rfl⟩
    have hagrees :=
      provenanced_alternatingGraphs_agree_outside_deletionFootprints
        source target hcompatible edge hedgeOutside
    refine ⟨?_, houtside⟩
    exact targetGraph.mem_edgeSet.mp
      (hagrees.mp (sourceGraph.mem_edgeSet.mpr hadj))
  · rintro ⟨hadj, houtside⟩
    let edge : G.edgeSet := ⟨s(left, right),
      G.mem_edgeSet.mpr (htargetLe hadj)⟩
    have hedgeOutside :
        edge ∉ deletionFootprint (pairingProvenance source).site.data ∪
          deletionFootprint (pairingProvenance target).site.data := by
      intro hmem
      apply houtside
      change s(left, right) ∈ footprint
      exact Finset.mem_image.2 ⟨edge, hmem, rfl⟩
    have hagrees :=
      provenanced_alternatingGraphs_agree_outside_deletionFootprints
        source target hcompatible edge hedgeOutside
    refine ⟨?_, houtside⟩
    exact sourceGraph.mem_edgeSet.mp
      (hagrees.mpr (targetGraph.mem_edgeSet.mpr hadj))

/-- Compatible residual sites change their complete alternating graphs on at
most ten ambient edge values. -/
theorem card_provenanced_alternatingGraph_edgeDisagreement_le
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
        (pairingProvenance target)).Compatible) :
    (SimpleGraph.edgeDisagreementFinset
      (alternatingGraph sigma (alternatingSite source).tau)
      (alternatingGraph sigma (alternatingSite target).tau)).card ≤ 10 := by
  apply le_trans
    (SimpleGraph.card_edgeDisagreementFinset_le_of_deleteEdges_eq
      (alternatingGraph sigma (alternatingSite source).tau)
      (alternatingGraph sigma (alternatingSite target).tau)
      (overlapFootprintValues
        (pairingProvenance source).site.data
        (pairingProvenance target).site.data)
      (provenanced_alternatingGraphs_delete_overlapFootprints_eq
        source target hcompatible))
  exact card_overlapFootprintValues_le
    (pairingProvenance source).site.data
    (pairingProvenance target).site.data

/-- Two consecutive compatible residual transitions accumulate at most twenty
edge disagreements between their endpoint alternating graphs. -/
theorem card_provenanced_alternatingGraph_edgeDisagreement_le_twenty
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {sourceStep middleStep targetStep : GlobalMeshStep rotation ordered}
    (source : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma sourceStep)
    (middle : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma middleStep)
    (target : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma targetStep)
    (hsourceMiddle :
      (globalMatchingOverlapState (pairingProvenance source)
        (pairingProvenance middle)).Compatible)
    (hmiddleTarget :
      (globalMatchingOverlapState (pairingProvenance middle)
        (pairingProvenance target)).Compatible) :
    (SimpleGraph.edgeDisagreementFinset
      (alternatingGraph sigma (alternatingSite source).tau)
      (alternatingGraph sigma (alternatingSite target).tau)).card ≤ 20 := by
  calc
    (SimpleGraph.edgeDisagreementFinset
      (alternatingGraph sigma (alternatingSite source).tau)
      (alternatingGraph sigma (alternatingSite target).tau)).card ≤
        (SimpleGraph.edgeDisagreementFinset
          (alternatingGraph sigma (alternatingSite source).tau)
          (alternatingGraph sigma (alternatingSite middle).tau)).card +
        (SimpleGraph.edgeDisagreementFinset
          (alternatingGraph sigma (alternatingSite middle).tau)
          (alternatingGraph sigma (alternatingSite target).tau)).card :=
      SimpleGraph.card_edgeDisagreementFinset_triangle _ _ _
    _ ≤ 10 + 10 := Nat.add_le_add
      (card_provenanced_alternatingGraph_edgeDisagreement_le
        source middle hsourceMiddle)
      (card_provenanced_alternatingGraph_edgeDisagreement_le
        middle target hmiddleTarget)
    _ = 20 := by omega

/-- A dependent bundle that lets residual-return receipts from different mesh
steps occur in one finite chain. -/
abbrev BundledResidualReturnReceipt
    {rotation : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G) (sigma : Pairing V) :=
  Sigma fun step : GlobalMeshStep rotation ordered =>
    ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step

namespace BundledResidualReturnReceipt

/-- The complete alternating graph carried by a bundled residual receipt. -/
def toAlternatingGraph
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G} {sigma : Pairing V}
    (receipt : BundledResidualReturnReceipt minimal ordered hG sigma) :
    SimpleGraph V :=
  alternatingGraph sigma (alternatingSite receipt.2).tau

/-- Consecutive bundled receipts are compatible when their finite
matching-overlap state is compatible. -/
def Compatible
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G} {sigma : Pairing V}
    (source target : BundledResidualReturnReceipt minimal ordered hG sigma) :
    Prop :=
  (globalMatchingOverlapState (pairingProvenance source.2)
    (pairingProvenance target.2)).Compatible

/-- Every compatible chain of residual receipts has total alternating-graph
edge-disagreement cost at most ten times its number of transitions. -/
theorem edgeDisagreementPathCost_le
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G} {sigma : Pairing V}
    (receipts : List
      (BundledResidualReturnReceipt minimal ordered hG sigma))
    (hchain : receipts.IsChain Compatible) :
    SimpleGraph.edgeDisagreementPathCost
        (receipts.map toAlternatingGraph) ≤
      (receipts.length - 1) * 10 := by
  have hmapped :
      (receipts.map toAlternatingGraph).IsChain fun source target =>
        (SimpleGraph.edgeDisagreementFinset source target).card ≤ 10 := by
    induction hchain with
    | nil => exact .nil
    | singleton receipt => exact .singleton _
    | cons_cons hcompatible _ ih =>
        exact .cons_cons
          (card_provenanced_alternatingGraph_edgeDisagreement_le
            _ _ hcompatible)
          ih
  simpa using
    SimpleGraph.edgeDisagreementPathCost_le 10
      (receipts.map toAlternatingGraph) hmapped

/-- Endpoint alternating graphs of a compatible residual-receipt chain with
`middle.length + 1` transitions disagree on at most
`10 * (middle.length + 1)` edges. -/
theorem card_endpoint_edgeDisagreement_le
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G} {sigma : Pairing V}
    (source target :
      BundledResidualReturnReceipt minimal ordered hG sigma)
    (middle : List
      (BundledResidualReturnReceipt minimal ordered hG sigma))
    (hchain : (source :: middle ++ [target]).IsChain Compatible) :
    (SimpleGraph.edgeDisagreementFinset
      source.toAlternatingGraph target.toAlternatingGraph).card ≤
        (middle.length + 1) * 10 := by
  calc
    (SimpleGraph.edgeDisagreementFinset
      source.toAlternatingGraph target.toAlternatingGraph).card ≤
        SimpleGraph.edgeDisagreementPathCost
          ((source :: middle ++ [target]).map toAlternatingGraph) := by
      simpa using
        SimpleGraph.card_edgeDisagreementFinset_le_pathCost
          source.toAlternatingGraph target.toAlternatingGraph
          (middle.map toAlternatingGraph)
    _ ≤ ((source :: middle ++ [target]).length - 1) * 10 :=
      edgeDisagreementPathCost_le (source :: middle ++ [target]) hchain
    _ = (middle.length + 1) * 10 := by simp

/-- Along a compatible chain, all endpoint component changes are confined to
an exceptional set of at most ten edges per transition: any source walk that
avoids this set has its endpoints in one target component. -/
theorem exists_endpoint_component_exceptionalEdges
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G} {sigma : Pairing V}
    (source target :
      BundledResidualReturnReceipt minimal ordered hG sigma)
    (middle : List
      (BundledResidualReturnReceipt minimal ordered hG sigma))
    (hchain : (source :: middle ++ [target]).IsChain Compatible) :
    ∃ exceptional : Finset (Sym2 V),
      exceptional.card ≤ (middle.length + 1) * 10 ∧
      ∀ {left right : V}
        (walk : source.toAlternatingGraph.Walk left right),
        (∀ edge ∈ walk.edges, edge ∉ exceptional) →
        target.toAlternatingGraph.connectedComponentMk left =
          target.toAlternatingGraph.connectedComponentMk right := by
  let exceptional := SimpleGraph.edgeDisagreementFinset
    source.toAlternatingGraph target.toAlternatingGraph
  refine ⟨exceptional,
    card_endpoint_edgeDisagreement_le source target middle hchain, ?_⟩
  intro left right walk havoids
  exact walk.connectedComponentMk_eq_of_avoids_edgeDisagreement havoids

end BundledResidualReturnReceipt

/-- Every source distinguished-cycle edge either survives in the target
alternating graph or belongs to one of the two five-edge deletion
footprints. -/
theorem source_cycle_edge_mem_target_or_deletionFootprints
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
    (hedge : edge.1 ∈ (alternatingSite source).cycle.edges) :
    edge.1 ∈ (alternatingGraph sigma (alternatingSite target).tau).edgeSet ∨
      edge ∈ deletionFootprint (pairingProvenance source).site.data ∪
        deletionFootprint (pairingProvenance target).site.data := by
  by_cases hsource :
      IsRetainedAmbientEdge (pairingProvenance source).site.data edge
  · by_cases htarget :
        IsRetainedAmbientEdge (pairingProvenance target).site.data edge
    · exact Or.inl (source_cycle_edge_mem_target_alternatingGraph
        source target hcompatible edge hedge hsource htarget)
    · exact Or.inr (Finset.mem_union_right _
        ((mem_deletionFootprint_iff _ _).2 htarget))
  · exact Or.inr (Finset.mem_union_left _
      ((mem_deletionFootprint_iff _ _).2 hsource))

/-- Failure of a source distinguished-cycle edge to survive in the target
alternating graph is confined to the union of the two deletion footprints. -/
theorem source_cycle_edge_not_mem_target_mem_deletionFootprints
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
    (hnot :
      edge.1 ∉ (alternatingGraph sigma (alternatingSite target).tau).edgeSet) :
    edge ∈ deletionFootprint (pairingProvenance source).site.data ∪
      deletionFootprint (pairingProvenance target).site.data :=
  (source_cycle_edge_mem_target_or_deletionFootprints
    source target hcompatible edge hedge).resolve_left hnot

/-- A source-cycle arc that avoids both deletion footprints is a walk in the
target alternating graph, so its endpoints remain in one target alternating
component. -/
theorem source_cycle_common_arc_reachable_in_target
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
    {left right : V} (arc : G.Walk left right)
    (hcycle : ∀ edge ∈ arc.edges,
      edge ∈ (alternatingSite source).cycle.edges)
    (havoids : ∀ edge : G.edgeSet, edge.1 ∈ arc.edges →
      edge ∉ deletionFootprint (pairingProvenance source).site.data ∪
        deletionFootprint (pairingProvenance target).site.data) :
    (alternatingGraph sigma (alternatingSite target).tau).Reachable
      left right := by
  let targetGraph := alternatingGraph sigma (alternatingSite target).tau
  have htransfer : ∀ edge, edge ∈ arc.edges → edge ∈ targetGraph.edgeSet := by
    intro edge hedge
    let ambient : G.edgeSet := ⟨edge, arc.edges_subset_edgeSet hedge⟩
    have hnotFootprint := havoids ambient hedge
    have hsourceRetained :
        IsRetainedAmbientEdge (pairingProvenance source).site.data ambient := by
      by_contra hnot
      exact hnotFootprint (Finset.mem_union_left _
        ((mem_deletionFootprint_iff _ _).2 hnot))
    have htargetRetained :
        IsRetainedAmbientEdge (pairingProvenance target).site.data ambient := by
      by_contra hnot
      exact hnotFootprint (Finset.mem_union_right _
        ((mem_deletionFootprint_iff _ _).2 hnot))
    exact source_cycle_edge_mem_target_alternatingGraph
      source target hcompatible ambient (hcycle edge hedge)
        hsourceRetained htargetRetained
  exact (arc.transfer targetGraph htransfer).reachable

/-- Component-valued form of `source_cycle_common_arc_reachable_in_target`. -/
theorem source_cycle_common_arc_component_eq_in_target
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
    {left right : V} (arc : G.Walk left right)
    (hcycle : ∀ edge ∈ arc.edges,
      edge ∈ (alternatingSite source).cycle.edges)
    (havoids : ∀ edge : G.edgeSet, edge.1 ∈ arc.edges →
      edge ∉ deletionFootprint (pairingProvenance source).site.data ∪
        deletionFootprint (pairingProvenance target).site.data) :
    (alternatingGraph sigma (alternatingSite target).tau).connectedComponentMk left =
      (alternatingGraph sigma (alternatingSite target).tau).connectedComponentMk right :=
  SimpleGraph.ConnectedComponent.sound
    (source_cycle_common_arc_reachable_in_target
      source target hcompatible arc hcycle havoids)

end

end Mettapedia.GraphTheory.FourColor.Compositional.AlternatingComponentLocalization
