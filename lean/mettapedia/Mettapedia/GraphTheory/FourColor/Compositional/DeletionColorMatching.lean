import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreLocalization
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairMatchingExtraction

/-!
# Colour classes and completed matchings on overlapping deletions

An edge colouring selects a perfect matching by fixing one colour class.  For
an adjacent-pair deletion, completing that matching across the deleted central
edge changes nothing on the retained carrier.  This module records the exact
edgewise equivalence and then transports common-core colour agreement to
common-core matching agreement.

The result is representation-theoretic rather than planar: no embedding,
catalogue, or local reducibility hypothesis appears.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.DeletionColorMatching

open Amplitude
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24TaitMatchingDecomposition
open MatchingParity
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

local instance deletionRetainedFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

/-- A deletion colouring together with the colour class that completes to an
ambient perfect matching.  This is the semantic payload later carried by a
mesh-site provenance receipt; it is independent of meshes and embeddings. -/
structure DeletionMatchingState (data : AdjacentPairData G) where
  coloring : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).EdgeColoring Color
  isTait : IsTaitEdgeColoring
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) coloring
  absentColor : Fin 3
  absentAtBoundary : ∀ port, data.degreeTwoBoundaryData.colorWord
    coloring port ≠ taitColor absentColor

namespace DeletionMatchingState

/-- Complete the recorded absent colour class by the deleted central edge. -/
def pairing {data : AdjacentPairData G} (state : DeletionMatchingState data)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    Pairing V :=
  centralCompletionPairing (G := G) data hcubic state.coloring state.isTait
    state.absentColor state.absentAtBoundary

/-- The completed matching is supported by the ambient graph. -/
theorem pairing_supported {data : AdjacentPairData G}
    (state : DeletionMatchingState data)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    (state.pairing hcubic).SupportedBy G :=
  centralCompletionPairing_supportedBy (G := G) data hcubic state.coloring
    state.isTait state.absentColor state.absentAtBoundary

end DeletionMatchingState

/-- The pairing recovered from a colour-class perfect matching uses an edge
exactly when that edge has the selected colour. -/
theorem colorClassPairing_mem_edge_iff
    (C : G.EdgeColoring Color) (colour : Color)
    (hM : (colorClassSubgraph C colour).IsPerfectMatching)
    (edge : G.edgeSet) :
    edge.1 ∈ edges (Pairing.ofPerfectMatching hM).toPerm ↔
      C edge = colour := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      rw [mem_edges_iff (MatchingBridge.toPerm_mem_pairings _)]
      change (Pairing.ofPerfectMatching hM).partner left = right ↔ _
      constructor
      · intro hpartner
        have hadj := (hM.1 (hM.2 left)).choose_spec.1
        change (colorClassSubgraph C colour).Adj left
          ((Pairing.ofPerfectMatching hM).partner left) at hadj
        rw [hpartner] at hadj
        rcases hadj with ⟨_, hcolour⟩
        simpa only using hcolour
      · intro hcolour
        exact Pairing.ofPerfectMatching_partner_eq_of_adj hM
          ⟨hedge, hcolour⟩

/-- On the retained deletion, the extracted matching is literally the chosen
colour class. -/
theorem deletedColorClassPairing_mem_edge_iff
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    edge.1 ∈ edges
        (deletedColorClassPairing data hcubic C hC i habsent).toPerm ↔
      C edge = taitColor i := by
  exact colorClassPairing_mem_edge_iff C (taitColor i)
    (colorClassSubgraph_isPerfectMatching_of_boundary_absent
      data.degreeTwoBoundaryData
      (data.degreeTwoBoundaryData_wellFormed hcubic) C hC i habsent)
    edge

/-- Completing the retained colour class across the deleted central edge does
not change whether any retained ambient edge is selected. -/
theorem centralCompletionPairing_mem_retainedEdge_iff
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i)
    (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge data edge) :
    edge.1 ∈ edges
        (centralCompletionPairing data hcubic C hC i habsent).toPerm ↔
      C (ambientEdgeToRetainedEdge data edge hretained) = taitColor i := by
  rw [← deletedColorClassPairing_mem_edge_iff
    data hcubic C hC i habsent
      (ambientEdgeToRetainedEdge data edge hretained)]
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleft : left ∈
          retainedVertexSet data.firstVertex data.secondVertex :=
        endpoints_mem_retainedVertexSet data ⟨s(left, right), hedge⟩
          hretained left (Sym2.mem_mk_left _ _)
      have hright : right ∈
          retainedVertexSet data.firstVertex data.secondVertex :=
        endpoints_mem_retainedVertexSet data ⟨s(left, right), hedge⟩
          hretained right (Sym2.mem_mk_right _ _)
      have hretainedEdgeValue :
          (ambientEdgeToRetainedEdge data
              ⟨s(left, right), hedge⟩ hretained).1 =
            s(⟨left, hleft⟩, ⟨right, hright⟩) := by
        change
          s(left, right).attachWith
              (endpoints_mem_retainedVertexSet data
                ⟨s(left, right), hedge⟩ hretained) = _
        rw [Sym2.attachWith, Sym2.pmap_pair]
      rw [mem_edges_iff (MatchingBridge.toPerm_mem_pairings _)]
      rw [hretainedEdgeValue]
      rw [mem_edges_iff (MatchingBridge.toPerm_mem_pairings _)]
      change
        (centralCompletionPairing data hcubic C hC i habsent).partner left =
            right ↔
          (deletedColorClassPairing data hcubic C hC i habsent).partner
              ⟨left, hleft⟩ = ⟨right, hright⟩
      constructor
      · intro hpartner
        apply Subtype.ext
        simpa [centralCompletionPairing, Amplitude.extendPairing,
          hleft.1, hleft.2] using hpartner
      · intro hpartner
        have hvalue := congrArg Subtype.val hpartner
        simpa [centralCompletionPairing, Amplitude.extendPairing,
          hleft.1, hleft.2] using hvalue

/-- If two deletion colourings agree on their exact common core and use the
same absent colour, then their completed matchings make the same selection on
every ambient edge retained by both deletions.  The shared colour index is an
explicit hypothesis: synchronizing it across many sites is a separate global
obligation. -/
theorem centralCompletionPairings_agree_on_common_retained_edge
    (source target : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (sourceTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      sourceColoring)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (targetTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex)
      targetColoring)
    (i : Fin 3)
    (sourceAbsent : ∀ port, source.degreeTwoBoundaryData.colorWord
      sourceColoring port ≠ taitColor i)
    (targetAbsent : ∀ port, target.degreeTwoBoundaryData.colorWord
      targetColoring port ≠ taitColor i)
    (hagrees : CommonCoreAgrees source target sourceColoring targetColoring)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    edge.1 ∈ edges
        (centralCompletionPairing source hcubic sourceColoring sourceTait i
          sourceAbsent).toPerm ↔
      edge.1 ∈ edges
        (centralCompletionPairing target hcubic targetColoring targetTait i
          targetAbsent).toPerm := by
  rw [centralCompletionPairing_mem_retainedEdge_iff source hcubic
    sourceColoring sourceTait i sourceAbsent edge hsource]
  rw [centralCompletionPairing_mem_retainedEdge_iff target hcubic
    targetColoring targetTait i targetAbsent edge htarget]
  rw [(commonCoreAgrees_iff_ambient source target sourceColoring
    targetColoring).1 hagrees edge hsource htarget]

/-- Finite-state form of
`centralCompletionPairings_agree_on_common_retained_edge`: equality of the
absent-colour coordinate is represented by the shared index `i`, while the
second coordinate is the Boolean common-restriction bit already stored in an
`OverlapKempeState`. -/
theorem centralCompletionPairings_agree_on_common_retained_edge_of_bit
    (source target : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (sourceTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      sourceColoring)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (targetTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex)
      targetColoring)
    (i : Fin 3)
    (sourceAbsent : ∀ port, source.degreeTwoBoundaryData.colorWord
      sourceColoring port ≠ taitColor i)
    (targetAbsent : ∀ port, target.degreeTwoBoundaryData.colorWord
      targetColoring port ≠ taitColor i)
    (hagrees : commonRestrictionAgreementBit source target sourceColoring
      targetColoring = true)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    edge.1 ∈ edges
        (centralCompletionPairing source hcubic sourceColoring sourceTait i
          sourceAbsent).toPerm ↔
      edge.1 ∈ edges
        (centralCompletionPairing target hcubic targetColoring targetTait i
          targetAbsent).toPerm :=
  centralCompletionPairings_agree_on_common_retained_edge source target
    hcubic sourceColoring sourceTait targetColoring targetTait i
    sourceAbsent targetAbsent
    ((commonRestrictionAgreementBit_eq_true_iff source target sourceColoring
      targetColoring).1 hagrees)
    edge hsource htarget

end

end Mettapedia.GraphTheory.FourColor.Compositional.DeletionColorMatching
