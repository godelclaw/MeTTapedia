import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingOverlapGeometry

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
