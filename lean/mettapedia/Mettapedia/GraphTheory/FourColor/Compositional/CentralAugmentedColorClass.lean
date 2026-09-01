import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingComponentLocalization

/-!
# Central-augmented colour classes on adjacent-pair deletions

An adjacent-pair deletion colouring lives on the graph obtained by removing
two adjacent vertices.  For any fixed Tait colour, this file restores a total
ambient edge-labelled graph by assigning that colour to the deleted central
edge and retaining the four boundary requests and all undeleted colours.

The construction is defined for every colour, without assuming that the
colour is absent from the four boundary requests.  When it is absent, the
result is exactly the graph of the completed perfect matching used by the
residual-return construction.  Keeping the construction meaningful for all
three colours lets a coherent path compare one fixed colour class even when
its locally selected absent colour changes at intermediate coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CentralAugmentedColorClass

open Amplitude
open AlternatingComponentLocalization
open DeletionColorMatching
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24ResidualExchange
open GoertzelV24TaitMatchingDecomposition
open MatchingParity
open SimpleGraph

open scoped symmDiff

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

local instance deletionRetainedFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

/-- The ambient graph formed by one fixed colour class after assigning that
colour to the restored central edge.  Boundary edges keep their deletion-word
colours, so this graph need not be a matching unless `colour` is absent there. -/
def centralAugmentedColorClassGraph
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (colour : Fin 3) : SimpleGraph V :=
  SimpleGraph.EdgeLabeling.labelGraph
    (insertAdjacentPairColorFunction data coloring (taitColor colour))
    (taitColor colour)

/-- Edge membership in a central-augmented colour class is literal equality
with the corresponding value of the total insertion labelling. -/
theorem mem_centralAugmentedColorClassGraph_edgeSet_iff
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (colour : Fin 3) (edge : G.edgeSet) :
    edge.1 ∈ (centralAugmentedColorClassGraph data coloring colour).edgeSet ↔
      insertAdjacentPairColorFunction data coloring (taitColor colour) edge =
        taitColor colour := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      simp only [SimpleGraph.mem_edgeSet,
        centralAugmentedColorClassGraph,
        SimpleGraph.EdgeLabeling.labelGraph_adj]
      constructor
      · rintro ⟨_, hcolour⟩
        exact hcolour
      · intro hcolour
        exact ⟨hedge, hcolour⟩

/-- Every central-augmented colour class uses only ambient edges. -/
theorem centralAugmentedColorClassGraph_le
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (colour : Fin 3) :
    centralAugmentedColorClassGraph data coloring colour ≤ G :=
  SimpleGraph.EdgeLabeling.labelGraph_le
    (insertAdjacentPairColorFunction data coloring (taitColor colour))

/-- The central completion does not select any of the four boundary edges.
It pairs each deleted vertex with the other deleted vertex, whereas a boundary
edge joins a deleted vertex to a retained port. -/
theorem centralCompletionPairing_boundaryEdge_not_mem
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      coloring)
    (colour : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord coloring port ≠
      taitColor colour)
    (port : Fin 4) :
    (boundaryEdge data port).1 ∉ edges
      (centralCompletionPairing data hcubic coloring hTait colour
        habsent).toPerm := by
  let completion :=
    centralCompletionPairing data hcubic coloring hTait colour habsent
  have hfirst : completion.partner data.firstVertex = data.secondVertex := by
    exact centralCompletionPairing_partner_first data hcubic coloring hTait
      colour habsent
  have hsecond : completion.partner data.secondVertex = data.firstVertex := by
    have hinvolution := completion.partner_partner data.firstVertex
    rw [hfirst] at hinvolution
    exact hinvolution
  change (boundaryEdge data port).1 ∉ edges completion.toPerm
  fin_cases port
  · simpa [boundaryEdge, boundaryEdgeValue,
      mem_edges_iff (MatchingBridge.toPerm_mem_pairings completion), hfirst]
      using (data.portNeSecond 0).symm
  · simpa [boundaryEdge, boundaryEdgeValue,
      mem_edges_iff (MatchingBridge.toPerm_mem_pairings completion), hfirst]
      using (data.portNeSecond 1).symm
  · simpa [boundaryEdge, boundaryEdgeValue,
      mem_edges_iff (MatchingBridge.toPerm_mem_pairings completion), hsecond]
      using (data.portNeFirst 2).symm
  · simpa [boundaryEdge, boundaryEdgeValue,
      mem_edges_iff (MatchingBridge.toPerm_mem_pairings completion), hsecond]
      using (data.portNeFirst 3).symm

/-- When `colour` is absent from the four deletion-boundary requests, the
total central-augmented colour class is exactly the completed colour-class
pairing.  This is the semantic bridge between the total fixed-colour graph,
which is meaningful at every coordinate, and the matching used at selected
coordinates. -/
theorem centralAugmentedColorClassGraph_eq_pairingGraph
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      coloring)
    (colour : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord coloring port ≠
      taitColor colour) :
    centralAugmentedColorClassGraph data coloring colour =
      pairingGraph
        (centralCompletionPairing data hcubic coloring hTait colour
          habsent) := by
  let completion :=
    centralCompletionPairing data hcubic coloring hTait colour habsent
  have hcompletionLe : completion.SupportedBy G :=
    centralCompletionPairing_supportedBy data hcubic coloring hTait colour
      habsent
  ext left right
  constructor
  · intro hcolour
    let edge : G.edgeSet :=
      ⟨s(left, right), G.mem_edgeSet.mpr
        ((centralAugmentedColorClassGraph_le data coloring colour) hcolour)⟩
    have hselected : insertAdjacentPairColorFunction data coloring
        (taitColor colour) edge = taitColor colour :=
      (mem_centralAugmentedColorClassGraph_edgeSet_iff
        data coloring colour edge).1 hcolour
    by_cases hretained : IsRetainedAmbientEdge data edge
    · have hmatching := (centralCompletionPairing_mem_retainedEdge_iff
          data hcubic coloring hTait colour habsent edge hretained).2 ?_
      · change completion.partner left = right
        apply (mem_edges_iff
          (MatchingBridge.toPerm_mem_pairings completion) left right).1
        exact hmatching
      · simpa [insertAdjacentPairColorFunction_retained data coloring
          (taitColor colour) edge hretained] using hselected
    · rcases (not_isRetainedAmbientEdge_iff data edge).1 hretained with
        hcentral | ⟨port, hboundary⟩
      · change completion.partner left = right
        apply (mem_edges_iff
          (MatchingBridge.toPerm_mem_pairings completion) left right).1
        change edge.1 ∈ edges completion.toPerm
        rw [hcentral, centralEdgeValue]
        apply (mem_edges_iff
          (MatchingBridge.toPerm_mem_pairings completion)
            data.firstVertex data.secondVertex).2
        exact centralCompletionPairing_partner_first data hcubic coloring hTait
          colour habsent
      · have hedge : edge = boundaryEdge data port := Subtype.ext hboundary
        have hboundaryColor : data.degreeTwoBoundaryData.colorWord coloring
            port = taitColor colour := by
          rw [← insertAdjacentPairColorFunction_boundary data coloring
            (taitColor colour) port, ← hedge]
          exact hselected
        exact False.elim ((habsent port) hboundaryColor)
  · intro hmatching
    change completion.partner left = right at hmatching
    have hambient : G.Adj left right := by
      simpa [hmatching] using hcompletionLe left
    let edge : G.edgeSet := ⟨s(left, right), G.mem_edgeSet.mpr hambient⟩
    apply (centralAugmentedColorClassGraph data coloring colour).mem_edgeSet.mp
    apply (mem_centralAugmentedColorClassGraph_edgeSet_iff
      data coloring colour edge).2
    by_cases hretained : IsRetainedAmbientEdge data edge
    · rw [insertAdjacentPairColorFunction_retained data coloring
        (taitColor colour) edge hretained]
      apply (centralCompletionPairing_mem_retainedEdge_iff
        data hcubic coloring hTait colour habsent edge hretained).1
      rw [mem_edges_iff (MatchingBridge.toPerm_mem_pairings completion)]
      exact hmatching
    · rcases (not_isRetainedAmbientEdge_iff data edge).1 hretained with
        hcentral | ⟨port, hboundary⟩
      · have hedge : edge = centralEdge data := Subtype.ext hcentral
        rw [hedge]
        exact insertAdjacentPairColorFunction_central data coloring
          (taitColor colour)
      · have hedge : edge = boundaryEdge data port := Subtype.ext hboundary
        have hpairingEdge : edge.1 ∈ edges completion.toPerm := by
          rw [mem_edges_iff (MatchingBridge.toPerm_mem_pairings completion)]
          exact hmatching
        have hboundaryEdge : (boundaryEdge data port).1 ∈
            edges completion.toPerm := by
          rw [← hedge]
          exact hpairingEdge
        exact False.elim
          (centralCompletionPairing_boundaryEdge_not_mem data hcubic coloring
            hTait colour habsent port hboundaryEdge)

/-- Common-core agreement preserves every fixed colour-class decision on an
ambient edge retained by both deletions.  No absent-colour choice is needed. -/
theorem centralAugmentedColorClassGraphs_agree_on_common_retained_edge
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hagrees : CommonCoreAgrees source target sourceColoring targetColoring)
    (colour : Fin 3) (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    edge.1 ∈ (centralAugmentedColorClassGraph source sourceColoring
        colour).edgeSet ↔
      edge.1 ∈ (centralAugmentedColorClassGraph target targetColoring
        colour).edgeSet := by
  rw [mem_centralAugmentedColorClassGraph_edgeSet_iff,
    mem_centralAugmentedColorClassGraph_edgeSet_iff,
    insertAdjacentPairColorFunction_retained source sourceColoring
      (taitColor colour) edge hsource,
    insertAdjacentPairColorFunction_retained target targetColoring
      (taitColor colour) edge htarget]
  rw [(commonCoreAgrees_iff_ambient source target sourceColoring
    targetColoring).1 hagrees edge hsource htarget]

/-- The residual graph of one fixed colour class against a fixed ambient
pairing.  It is defined even at coordinates where that colour is not the
locally selected absent colour. -/
def fixedColorAlternatingGraph
    (sigma : Pairing V) (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (colour : Fin 3) : SimpleGraph V :=
  pairingGraph sigma ∆ centralAugmentedColorClassGraph data coloring colour

omit [Fintype V] [DecidableEq V] in
/-- Replacing the right graph of a symmetric difference by a graph with the
same decision on one edge preserves the symmetric-difference decision. -/
theorem symmDiff_adj_congr_right
    (fixed source target : SimpleGraph V) {left right : V}
    (hagrees : source.Adj left right ↔ target.Adj left right) :
    (fixed ∆ source).Adj left right ↔ (fixed ∆ target).Adj left right := by
  simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  tauto

/-- Common-core agreement preserves the fixed-colour residual graph on every
ambient edge retained by both deletions. -/
theorem fixedColorAlternatingGraphs_agree_on_common_retained_edge
    (sigma : Pairing V)
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hagrees : CommonCoreAgrees source target sourceColoring targetColoring)
    (colour : Fin 3) (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    edge.1 ∈ (fixedColorAlternatingGraph sigma source sourceColoring
        colour).edgeSet ↔
      edge.1 ∈ (fixedColorAlternatingGraph sigma target targetColoring
        colour).edgeSet := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      change
        (fixedColorAlternatingGraph sigma source sourceColoring colour).Adj
            left right ↔
          (fixedColorAlternatingGraph sigma target targetColoring colour).Adj
            left right
      apply symmDiff_adj_congr_right
      exact centralAugmentedColorClassGraphs_agree_on_common_retained_edge
        source target sourceColoring targetColoring hagrees colour
        ⟨s(left, right), hedge⟩ hsource htarget

/-- A fixed-colour residual graph uses only ambient edges when the reference
pairing does. -/
theorem fixedColorAlternatingGraph_le
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (colour : Fin 3) :
    fixedColorAlternatingGraph sigma data coloring colour ≤ G := by
  rw [fixedColorAlternatingGraph, symmDiff_def]
  apply sup_le
  · apply sdiff_le.trans
    intro left right hadj
    change sigma.partner left = right at hadj
    simpa [hadj] using hSigma left
  · exact sdiff_le.trans
      (centralAugmentedColorClassGraph_le data coloring colour)

/-- At one fixed colour, common-core-compatible deletion colourings become
literally equal residual graphs after deleting their two local footprints. -/
theorem fixedColorAlternatingGraphs_delete_overlapFootprints_eq
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hagrees : CommonCoreAgrees source target sourceColoring targetColoring)
    (colour : Fin 3) :
    (fixedColorAlternatingGraph sigma source sourceColoring colour).deleteEdges
        (overlapFootprintValues source target : Set (Sym2 V)) =
      (fixedColorAlternatingGraph sigma target targetColoring colour).deleteEdges
        (overlapFootprintValues source target : Set (Sym2 V)) := by
  let sourceGraph := fixedColorAlternatingGraph sigma source sourceColoring colour
  let targetGraph := fixedColorAlternatingGraph sigma target targetColoring colour
  have hsourceLe : sourceGraph ≤ G :=
    fixedColorAlternatingGraph_le sigma hSigma source sourceColoring colour
  have htargetLe : targetGraph ≤ G :=
    fixedColorAlternatingGraph_le sigma hSigma target targetColoring colour
  ext left right
  simp only [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hadj, houtside⟩
    let edge : G.edgeSet := ⟨s(left, right),
      G.mem_edgeSet.mpr (hsourceLe hadj)⟩
    have hedgeOutside : edge ∉ deletionFootprint source ∪
        deletionFootprint target := by
      intro hmem
      apply houtside
      change s(left, right) ∈ overlapFootprintValues source target
      exact Finset.mem_image.2 ⟨edge, hmem, rfl⟩
    have hsource : IsRetainedAmbientEdge source edge := by
      by_contra hnot
      exact hedgeOutside (Finset.mem_union_left _
        ((mem_deletionFootprint_iff source edge).2 hnot))
    have htarget : IsRetainedAmbientEdge target edge := by
      by_contra hnot
      exact hedgeOutside (Finset.mem_union_right _
        ((mem_deletionFootprint_iff target edge).2 hnot))
    refine ⟨?_, houtside⟩
    exact targetGraph.mem_edgeSet.mp
      ((fixedColorAlternatingGraphs_agree_on_common_retained_edge
        sigma source target sourceColoring targetColoring hagrees colour
        edge hsource htarget).mp (sourceGraph.mem_edgeSet.mpr hadj))
  · rintro ⟨hadj, houtside⟩
    let edge : G.edgeSet := ⟨s(left, right),
      G.mem_edgeSet.mpr (htargetLe hadj)⟩
    have hedgeOutside : edge ∉ deletionFootprint source ∪
        deletionFootprint target := by
      intro hmem
      apply houtside
      change s(left, right) ∈ overlapFootprintValues source target
      exact Finset.mem_image.2 ⟨edge, hmem, rfl⟩
    have hsource : IsRetainedAmbientEdge source edge := by
      by_contra hnot
      exact hedgeOutside (Finset.mem_union_left _
        ((mem_deletionFootprint_iff source edge).2 hnot))
    have htarget : IsRetainedAmbientEdge target edge := by
      by_contra hnot
      exact hedgeOutside (Finset.mem_union_right _
        ((mem_deletionFootprint_iff target edge).2 hnot))
    refine ⟨?_, houtside⟩
    exact sourceGraph.mem_edgeSet.mp
      ((fixedColorAlternatingGraphs_agree_on_common_retained_edge
        sigma source target sourceColoring targetColoring hagrees colour
        edge hsource htarget).mpr (targetGraph.mem_edgeSet.mpr hadj))

end

end CentralAugmentedColorClass

end Mettapedia.GraphTheory.FourColor.Compositional
