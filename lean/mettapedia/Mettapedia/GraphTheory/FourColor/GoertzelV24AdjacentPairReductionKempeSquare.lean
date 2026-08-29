import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairReductionColorExtension
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare

/-!
# The same-side Kempe square survives the paired square cap

The adjacent-pair source argument uses only two boundary switches: one whose
port support is `{0, 1}` and one whose port support is `{2, 3}`.  These switches
preserve compatibility with the planar pairing `join01_23`.  Consequently all
four corners of the commuting deletion square extend to honest Tait colorings
of one and the same paired reduction.

This is deliberately narrower than a general path-lifting assertion.  A
cross-side boundary switch need not preserve a fixed cap pairing.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance reductionKempeSquareGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance reductionKempeSquareRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  reductionExtensionRetainedVertexSetFintype first second

local instance reductionKempeSquareRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  reductionExtensionRetainedVertexSetDecidableEq first second

/-- A predicate invariant across every edge of a reachable walk has the same
truth value at the walk's endpoints. -/
theorem predicate_iff_of_reachable_of_adj_iff
    {W : Type*} {H : SimpleGraph W} (predicate : W → Prop)
    {start finish : W} (hreachable : H.Reachable start finish)
    (hadj : ∀ {left right : W}, H.Adj left right →
      (predicate left ↔ predicate right)) :
    predicate start ↔ predicate finish := by
  rcases hreachable with ⟨walk⟩
  induction walk with
  | nil => exact Iff.rfl
  | @cons first second finish hfirst tail ih =>
      exact (hadj hfirst).trans ih

/-- An internal retained dart, regarded as the same oriented edge in the
induced adjacent-pair deletion.  This is the small inverse needed to classify
the edges of a paired reduction without importing the later bridge chain. -/
def deletedDartOfReductionInternal
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart := by
  let left : retainedVertexSet data.firstVertex data.secondVertex :=
    ⟨internal.1.1.fst, by
      have hkeep := internal.1.2
      change internal.1.1.fst ∉ data.deletedVertices at hkeep
      simpa [deletedVertices] using hkeep⟩
  let right : retainedVertexSet data.firstVertex data.secondVertex :=
    ⟨internal.1.1.snd, by
      have hkeep := internal.2
      change internal.1.1.snd ∉ data.deletedVertices at hkeep
      simpa [deletedVertices] using hkeep⟩
  exact ⟨(left, right), internal.1.1.adj⟩

/-- The deletion edge represented by an internal retained dart. -/
def deletedEdgeOfReductionInternal
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  ⟨(data.deletedDartOfReductionInternal graphData internal).edge,
    (data.deletedDartOfReductionInternal graphData internal).edge_mem⟩

/-- Re-embedding the deletion edge represented by an internal dart recovers
that dart's ambient edge. -/
theorem retainedEdgeToAmbientEdge_deletedEdgeOfReductionInternal
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    data.retainedEdgeToAmbientEdge
        (data.deletedEdgeOfReductionInternal graphData internal) =
      (data.rootedRotationSystem graphData).edgeOf internal.1.1 := by
  apply Subtype.ext
  rfl

/-- Every internal output edge is the image of its induced-deletion edge. -/
theorem reductionEdgeOfDeletedEdge_deletedEdgeOfReductionInternal
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    data.reductionEdgeOfDeletedEdge graphData side
        (data.deletedEdgeOfReductionInternal graphData internal) =
      (data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl internal) := by
  apply (retainedInternalSpliceEdge_eq_iff
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)
    (data.retainedEdgeInternalDart graphData
      (data.deletedEdgeOfReductionInternal graphData internal))
    internal).2
  rw [data.retainedEdgeInternalDart_edgeOf,
    data.retainedEdgeToAmbientEdge_deletedEdgeOfReductionInternal]

/-- Every edge of a paired reduction is uniquely of one of the two relevant
forms: an old deletion edge or a new seam edge. -/
theorem reductionEdge_old_or_seam
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (edge : (data.reductionRewiredDartSystem graphData side).Edge) :
    (∃ old, edge = data.reductionEdgeOfDeletedEdge graphData side old) ∨
      ∃ step, edge = data.reductionSeamEdge graphData side step := by
  rcases retainedSpliceEdge_internal_or_seam
      (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)
      (data.leftCrossing side) (data.rightCrossing side)
      (data.leftCrosses graphData side) (data.rightCrosses graphData side)
      (data.leftCrossing_injective side)
      (data.rightCrossing_injective side)
      (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
      (data.outer_retained graphData) (data.seamEndpoints graphData side)
      edge with ⟨internal, hedge⟩ | ⟨step, hedge⟩
  · left
    refine ⟨data.deletedEdgeOfReductionInternal graphData internal, ?_⟩
    exact hedge.trans
      (data.reductionEdgeOfDeletedEdge_deletedEdgeOfReductionInternal
        graphData side internal).symm
  · exact Or.inr ⟨step, hedge⟩

/-- Endpoint incidence of an old edge is reflected as well as preserved by
the reduction embedding. -/
theorem reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    data.reductionVertexOfDeletedVertex vertex ∈
        (data.reductionRotationSystem graphData side).endpoints
          (data.reductionEdgeOfDeletedEdge graphData side edge) ↔
      vertex ∈ (edge.1 : Sym2 _) := by
  constructor
  · intro hcap
    unfold reductionRotationSystem reductionEdgeOfDeletedEdge at hcap
    rw [endpoints_retainedInternalSpliceEdge] at hcap
    have himage : vertex.1 ∈
        (retainedInternalEndpointPair
          (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.retainedEdgeInternalDart graphData edge)).image Subtype.val :=
      Finset.mem_image.mpr
        ⟨data.reductionVertexOfDeletedVertex vertex, hcap, rfl⟩
    rw [image_val_retainedInternalEndpointPair,
      data.retainedEdgeInternalDart_edgeOf] at himage
    have hambient : vertex.1 ∈
        ((data.retainedEdgeToAmbientEdge edge).1 : Sym2 V) :=
      (mem_simpleGraphRotationSystem_endpoints_iff
        (data.rootedGraphData graphData)
        (data.retainedEdgeToAmbientEdge edge) vertex.1).1 himage
    rw [retainedEdgeToAmbientEdge_val] at hambient
    rcases Sym2.mem_map.mp hambient with ⟨retained, hretained, hvalue⟩
    have heq : retained = vertex := Subtype.ext hvalue
    simpa [heq] using hretained
  · exact data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
      graphData side edge vertex

/-- The endpoints of a named seam are exactly its two named ports. -/
theorem mem_endpoints_reductionSeamEdge_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (step : Fin 2)
    (vertex : RetainedVertex (deletedRegionKeep data.deletedVertices)) :
    vertex ∈ (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side step) ↔
      vertex = data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.leftPort step)) ∨
        vertex = data.reductionVertexOfDeletedVertex
          (data.retainedPort (side.rightPort step)) := by
  constructor
  · intro hvertex
    unfold reductionRotationSystem reductionSeamEdge at hvertex
    rw [endpoints_orderedCutSeamSpliceEdge] at hvertex
    rcases Finset.mem_insert.mp hvertex with hleft | hright
    · left
      apply Subtype.ext
      change vertex.1 = data.portVertex (side.leftPort step)
      rw [hleft]
      exact data.leftBoundaryDart_vertex graphData side step
    · right
      have hright := Finset.mem_singleton.mp hright
      apply Subtype.ext
      change vertex.1 = data.portVertex (side.rightPort step)
      rw [hright]
      exact data.rightBoundaryDart_vertex graphData side step
  · rintro (rfl | rfl)
    · exact data.reductionLeftPort_mem_endpoints_reductionSeamEdge
        graphData side step
    · exact data.reductionRightPort_mem_endpoints_reductionSeamEdge
        graphData side step

/-- The vertex inclusion from the induced deletion into either square
reduction is injective. -/
theorem reductionVertexOfDeletedVertex_injective
    (data : AdjacentPairData G) :
    Function.Injective data.reductionVertexOfDeletedVertex := by
  intro first second heq
  apply Subtype.ext
  exact congrArg
    (fun vertex : RetainedVertex
      (deletedRegionKeep data.deletedVertices) => vertex.1) heq

/-- Adjacency between the images of two old edges reflects back to adjacency
in the induced deletion.  Thus the square cap introduces no new old--old
contact. -/
theorem oldEdge_adj_of_reductionOldEdge_adj
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    {first second : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (hadj : (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
      (data.reductionEdgeOfDeletedEdge graphData side first)
      (data.reductionEdgeOfDeletedEdge graphData side second)) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).lineGraph.Adj first second := by
  rcases (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.1
      hadj with ⟨hne, vertex, hfirst, hsecond⟩
  let oldVertex : retainedVertexSet data.firstVertex data.secondVertex :=
    ⟨vertex.1, by
      have hkeep := vertex.2
      change vertex.1 ∉ data.deletedVertices at hkeep
      simpa [deletedVertices] using hkeep⟩
  have hvertex : data.reductionVertexOfDeletedVertex oldVertex = vertex := by
    apply Subtype.ext
    rfl
  apply (SimpleGraph.lineGraph_adj_iff_exists).2
  refine ⟨?_, oldVertex, ?_, ?_⟩
  · intro heq
    exact hne (congrArg
      (data.reductionEdgeOfDeletedEdge graphData side) heq)
  · apply (data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
      graphData side first oldVertex).1
    rw [hvertex]
    exact hfirst
  · apply (data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
      graphData side second oldVertex).1
    rw [hvertex]
    exact hsecond

/-- The two distinct seam edges of a square cap are not adjacent.  Their
four endpoints are the four distinct boundary ports. -/
theorem not_adj_reductionSeamEdge_of_ne
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    {first second : Fin 2} (hne : first ≠ second) :
    ¬ (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
      (data.reductionSeamEdge graphData side first)
      (data.reductionSeamEdge graphData side second) := by
  intro hadj
  rcases (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.1
      hadj with ⟨_edgeNe, vertex, hfirst, hsecond⟩
  rcases (data.mem_endpoints_reductionSeamEdge_iff
      graphData side first vertex).1 hfirst with hfirstLeft | hfirstRight
  <;> rcases (data.mem_endpoints_reductionSeamEdge_iff
      graphData side second vertex).1 hsecond with hsecondLeft | hsecondRight
  · have hports : side.leftPort first = side.leftPort second := by
      apply data.retainedPort_injective
      apply data.reductionVertexOfDeletedVertex_injective
      exact hfirstLeft.symm.trans hsecondLeft
    exact hne (side.leftPort_injective hports)
  · have hports : side.leftPort first = side.rightPort second := by
      apply data.retainedPort_injective
      apply data.reductionVertexOfDeletedVertex_injective
      exact hfirstLeft.symm.trans hsecondRight
    exact (side.leftPort_ne_rightPort first second) hports
  · have hports : side.leftPort second = side.rightPort first := by
      apply data.retainedPort_injective
      apply data.reductionVertexOfDeletedVertex_injective
      exact hsecondLeft.symm.trans hfirstRight
    exact (side.leftPort_ne_rightPort second first) hports
  · have hports : side.rightPort first = side.rightPort second := by
      apply data.retainedPort_injective
      apply data.reductionVertexOfDeletedVertex_injective
      exact hfirstRight.symm.trans hsecondRight
    exact hne (side.rightPort_injective hports)

/-- If a component's exact port support is the endpoint pair of one seam,
then meeting an endpoint of any seam identifies that seam. -/
theorem seamStep_eq_of_component_meets_seam_endpoint
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (side : SquareReductionSide) (fixed step : Fin 2)
    (hsupport : data.degreeTwoBoundaryData.kempePortSupport C a b K =
      ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)))
    (hmeets : data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K
        (side.leftPort step) ∨
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K
        (side.rightPort step)) :
    step = fixed := by
  have hmember :
      side.leftPort step ∈
          ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)) ∨
      side.rightPort step ∈
          ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)) := by
    rcases hmeets with hleft | hright
    · left
      rw [← hsupport]
      exact (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
        C a b K (side.leftPort step)).2 hleft
    · right
      rw [← hsupport]
      exact (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
        C a b K (side.rightPort step)).2 hright
  fin_cases side <;> fin_cases fixed <;> fin_cases step <;>
    simp [SquareReductionSide.leftPort, SquareReductionSide.rightPort,
      SquareReductionSide.join01_23, SquareReductionSide.join12_30]
      at hmember ⊢

/-- If the image of an old selected edge is adjacent to a new seam, its open
Kempe component meets one of the two ports joined by that seam. -/
theorem openComponent_meets_endpoint_of_oldEdge_adj_seam
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (old : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hold : old ∈ C.kempeComponentSet a b K)
    (step : Fin 2)
    (hadj : (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
      (data.reductionEdgeOfDeletedEdge graphData side old)
      (data.reductionSeamEdge graphData side step)) :
    data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K
        (side.leftPort step) ∨
      data.degreeTwoBoundaryData.KempeComponentMeetsPort C a b K
        (side.rightPort step) := by
  rcases (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.1
      hadj with ⟨_hne, vertex, holdEndpoint, hseamEndpoint⟩
  rcases (data.mem_endpoints_reductionSeamEdge_iff graphData side step vertex).1
      hseamEndpoint with hleft | hright
  · left
    have holdEndpoint' : data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.leftPort step)) ∈
        (data.reductionRotationSystem graphData side).endpoints
          (data.reductionEdgeOfDeletedEdge graphData side old) := by
      simpa [hleft] using holdEndpoint
    have holdPort : data.retainedPort (side.leftPort step) ∈
        (old.1 : Sym2 _) :=
      (data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
        graphData side old (data.retainedPort (side.leftPort step))).1
        holdEndpoint'
    exact ⟨old, Finset.mem_filter.mpr ⟨Finset.mem_univ _, holdPort⟩, hold⟩
  · right
    have holdEndpoint' : data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.rightPort step)) ∈
        (data.reductionRotationSystem graphData side).endpoints
          (data.reductionEdgeOfDeletedEdge graphData side old) := by
      simpa [hright] using holdEndpoint
    have holdPort : data.retainedPort (side.rightPort step) ∈
        (old.1 : Sym2 _) :=
      (data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
        graphData side old (data.retainedPort (side.rightPort step))).1
        holdEndpoint'
    exact ⟨old, Finset.mem_filter.mpr ⟨Finset.mem_univ _, holdPort⟩, hold⟩

/-- The unchanged edges of the four-defect deletion embed as a graph hom
into the edge-adjacency graph of either paired reduction. -/
def reductionOldEdgeGraphHom
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).lineGraph →g
      (data.reductionRotationSystem graphData side).edgeAdjacencyGraph where
  toFun := data.reductionEdgeOfDeletedEdge graphData side
  map_rel' := by
    intro first second hadjacent
    rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadjacent with
      ⟨hne, vertex, hfirst, hsecond⟩
    apply (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.2
    exact ⟨(data.reductionEdgeOfDeletedEdge_injective graphData side).ne hne,
      data.reductionVertexOfDeletedVertex vertex,
      data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
        graphData side first vertex hfirst,
      data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
        graphData side second vertex hsecond⟩

/-- Restricting `reductionOldEdgeGraphHom` to one selected colour pair gives
a graph hom between the corresponding open and capped Kempe graphs. -/
def reductionBicoloredOldEdgeHom
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    (a b : Color) :
    C.bicoloredSubgraph a b →g
      (data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible).bicoloredSubgraph a b where
  toFun := fun edge =>
    ⟨data.reductionEdgeOfDeletedEdge graphData side edge.1, by
      have hedge : C edge.1 = a ∨ C edge.1 = b := edge.2
      simpa using hedge⟩
  map_rel' := by
    intro first second hadjacent
    exact (data.reductionOldEdgeGraphHom graphData side).map_rel hadjacent

/-- Reachability inside an open Kempe component is preserved when its old
edges are embedded in the compatible paired cap. -/
theorem reductionBicoloredOldEdgeHom_reachable
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    (a b : Color) {first second : C.bicoloredSet a b}
    (hreachable : (C.bicoloredSubgraph a b).Reachable first second) :
    ((data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible).bicoloredSubgraph a b).Reachable
      (data.reductionBicoloredOldEdgeHom graphData hcubic C hC side
        hcompatible a b first)
      (data.reductionBicoloredOldEdgeHom graphData hcubic C hC side
        hcompatible a b second) :=
  hreachable.map
    (data.reductionBicoloredOldEdgeHom graphData hcubic C hC side
      hcompatible a b)

/-- If an open Kempe component meets the left port of a selected seam, then
the seam and the images of all old edges in that component belong to one
Kempe component of the capped colouring.  This is the forward, or
"path-closing", half of the fixed-cap lift. -/
theorem exists_cappedComponent_containing_seam_and_openComponent
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (step : Fin 2)
    (hmeets : data.degreeTwoBoundaryData.KempeComponentMeetsPort
      C a b K (side.leftPort step))
    (hselected : data.degreeTwoBoundaryData.colorWord C
        (side.leftPort step) = a ∨
      data.degreeTwoBoundaryData.colorWord C
        (side.leftPort step) = b) :
    let capped := data.reductionExtensionColoring graphData hcubic C hC
      side hcompatible
    ∃ Kcap : (capped.bicoloredSubgraph a b).ConnectedComponent,
      data.reductionSeamEdge graphData side step ∈
          capped.kempeComponentSet a b Kcap ∧
        ∀ edge,
          edge ∈ C.kempeComponentSet a b K →
          data.reductionEdgeOfDeletedEdge graphData side edge ∈
            capped.kempeComponentSet a b Kcap := by
  dsimp only
  let capped := data.reductionExtensionColoring graphData hcubic C hC
    side hcompatible
  rcases hmeets with ⟨root, hrootIncident, hrootSelected, hrootComponent⟩
  let rootOpen : C.bicoloredSet a b := ⟨root, hrootSelected⟩
  let rootCap := data.reductionBicoloredOldEdgeHom graphData hcubic C hC
    side hcompatible a b rootOpen
  let Kcap := (capped.bicoloredSubgraph a b).connectedComponentMk rootCap
  have hrootCap : rootCap.1 ∈ capped.kempeComponentSet a b Kcap :=
    capped.mem_kempeComponentSet_self rootCap.2
  have hseamSelected : capped (data.reductionSeamEdge graphData side step) = a ∨
      capped (data.reductionSeamEdge graphData side step) = b := by
    change data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible (data.reductionSeamEdge graphData side step) = a ∨
      data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible (data.reductionSeamEdge graphData side step) = b
    rw [data.reductionExtensionColoring_reductionSeamEdge_left]
    exact hselected
  have hrootEndpoint : data.retainedPort (side.leftPort step) ∈
      (root.1 : Sym2 (retainedVertexSet data.firstVertex data.secondVertex)) := by
    exact (Finset.mem_filter.mp hrootIncident).2
  have hadjRaw :
      (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
        (data.reductionEdgeOfDeletedEdge graphData side root)
        (data.reductionSeamEdge graphData side step) := by
    apply (data.reductionRotationSystem graphData side).edgeAdjacencyGraph_adj_iff.2
    exact ⟨data.reductionEdgeOfDeletedEdge_ne_reductionSeamEdge
        graphData side root step,
      data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.leftPort step)),
      data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
        graphData side root (data.retainedPort (side.leftPort step))
        hrootEndpoint,
      data.reductionLeftPort_mem_endpoints_reductionSeamEdge
        graphData side step⟩
  have hadj : (capped.bicoloredSubgraph a b).Adj rootCap
      ⟨data.reductionSeamEdge graphData side step, hseamSelected⟩ :=
    hadjRaw
  refine ⟨Kcap, capped.mem_kempeComponentSet_of_adj hrootCap hadj
      hseamSelected, ?_⟩
  intro edge hedge
  rcases hedge with ⟨hedgeSelected, hedgeComponent⟩
  let edgeOpen : C.bicoloredSet a b := ⟨edge, hedgeSelected⟩
  have hopenReachable : (C.bicoloredSubgraph a b).Reachable rootOpen edgeOpen :=
    ConnectedComponent.eq.mp (hrootComponent.trans hedgeComponent.symm)
  have hcapReachable := data.reductionBicoloredOldEdgeHom_reachable
    graphData hcubic C hC side hcompatible a b hopenReachable
  refine ⟨(data.reductionBicoloredOldEdgeHom graphData hcubic C hC side
      hcompatible a b edgeOpen).2, ?_⟩
  exact (ConnectedComponent.eq.mpr hcapReachable).symm

/-- An output edge carries the label of one fixed open Kempe component when
it is either the image of an edge of that component or the one seam closing
its two boundary ends. -/
def CappedFromOpenComponent
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (fixed : Fin 2)
    (edge : (data.reductionRewiredDartSystem graphData side).Edge) : Prop :=
  (∃ old,
    edge = data.reductionEdgeOfDeletedEdge graphData side old ∧
      old ∈ C.kempeComponentSet a b K) ∨
  edge = data.reductionSeamEdge graphData side fixed

/-- The open-component label is invariant across every selected adjacency in
the compatible cap.  This is the local converse to path closing: the cap can
close an open component, but cannot fuse it with a different one. -/
theorem cappedFromOpenComponent_adj_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (fixed : Fin 2)
    (hsupport : data.degreeTwoBoundaryData.kempePortSupport C a b K =
      ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)))
    {first second :
      (data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible).bicoloredSet a b}
    (hadj : (data.reductionExtensionColoring graphData hcubic C hC side
      hcompatible).bicoloredSubgraph a b |>.Adj first second) :
    data.CappedFromOpenComponent graphData side C a b K fixed first.1 ↔
      data.CappedFromOpenComponent graphData side C a b K fixed second.1 := by
  let capped := data.reductionExtensionColoring graphData hcubic C hC
    side hcompatible
  have hdata := data.degreeTwoBoundaryData_wellFormed hcubic
  have hpreserve : ∀ {first second : capped.bicoloredSet a b},
      (capped.bicoloredSubgraph a b).Adj first second →
      data.CappedFromOpenComponent graphData side C a b K fixed first.1 →
      data.CappedFromOpenComponent graphData side C a b K fixed second.1 := by
    intro first second hadj hfirstLabel
    have hadjRaw :
        (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
          first.1 second.1 := hadj
    rcases hfirstLabel with ⟨oldFirst, hfirst, holdFirst⟩ | hfirst
    · rcases data.reductionEdge_old_or_seam graphData side second.1 with
          ⟨oldSecond, hsecond⟩ | ⟨step, hsecond⟩
      · left
        refine ⟨oldSecond, hsecond, ?_⟩
        have hadjOldRaw := hadjRaw
        rw [hfirst, hsecond] at hadjOldRaw
        have hadjOld := data.oldEdge_adj_of_reductionOldEdge_adj
          graphData side hadjOldRaw
        have hsecondSelected : C oldSecond = a ∨ C oldSecond = b := by
          have := second.2
          rw [hsecond] at this
          change data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible
              (data.reductionEdgeOfDeletedEdge graphData side oldSecond) = a ∨
            data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible
              (data.reductionEdgeOfDeletedEdge graphData side oldSecond) = b at this
          simpa only [data.reductionExtensionColoring_reductionEdgeOfDeletedEdge]
            using this
        exact C.mem_kempeComponentSet_of_adj holdFirst hadjOld
          hsecondSelected
      · have hadjSeam :
            (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
              (data.reductionEdgeOfDeletedEdge graphData side oldFirst)
              (data.reductionSeamEdge graphData side step) := by
          rw [← hfirst, ← hsecond]
          exact hadjRaw
        have hmeets := data.openComponent_meets_endpoint_of_oldEdge_adj_seam
          graphData side C K oldFirst holdFirst step hadjSeam
        have hstep := data.seamStep_eq_of_component_meets_seam_endpoint
          C K side fixed step hsupport hmeets
        right
        simpa [hstep] using hsecond
    · rcases data.reductionEdge_old_or_seam graphData side second.1 with
          ⟨oldSecond, hsecond⟩ | ⟨step, hsecond⟩
      · have hsecondSelected : C oldSecond = a ∨ C oldSecond = b := by
          have := second.2
          rw [hsecond] at this
          change data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible
              (data.reductionEdgeOfDeletedEdge graphData side oldSecond) = a ∨
            data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible
              (data.reductionEdgeOfDeletedEdge graphData side oldSecond) = b at this
          simpa only [data.reductionExtensionColoring_reductionEdgeOfDeletedEdge]
            using this
        let oldSelected : C.bicoloredSet a b :=
          ⟨oldSecond, hsecondSelected⟩
        let L := (C.bicoloredSubgraph a b).connectedComponentMk oldSelected
        have holdL : oldSecond ∈ C.kempeComponentSet a b L :=
          C.mem_kempeComponentSet_self oldSelected.2
        have hadjSeam :
            (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
              (data.reductionEdgeOfDeletedEdge graphData side oldSecond)
              (data.reductionSeamEdge graphData side fixed) := by
          rw [← hsecond, ← hfirst]
          exact hadjRaw.symm
        have hmeets := data.openComponent_meets_endpoint_of_oldEdge_adj_seam
          graphData side C L oldSecond holdL fixed hadjSeam
        have hKleft : data.degreeTwoBoundaryData.KempeComponentMeetsPort
            C a b K (side.leftPort fixed) := by
          apply (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
            C a b K (side.leftPort fixed)).1
          rw [hsupport]
          simp
        have hKright : data.degreeTwoBoundaryData.KempeComponentMeetsPort
            C a b K (side.rightPort fixed) := by
          apply (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
            C a b K (side.rightPort fixed)).1
          rw [hsupport]
          simp
        have hfixedLeftSelected :
            data.degreeTwoBoundaryData.colorWord C (side.leftPort fixed) = a ∨
              data.degreeTwoBoundaryData.colorWord C (side.leftPort fixed) = b := by
          have hfirstSelected := first.2
          rw [hfirst] at hfirstSelected
          change data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible (data.reductionSeamEdge graphData side fixed) = a ∨
            data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible (data.reductionSeamEdge graphData side fixed) = b at hfirstSelected
          simpa only [data.reductionExtensionColoring_reductionSeamEdge_left]
            using hfirstSelected
        have hfixedRightSelected :
            data.degreeTwoBoundaryData.colorWord C (side.rightPort fixed) = a ∨
              data.degreeTwoBoundaryData.colorWord C (side.rightPort fixed) = b := by
          have hfirstSelected := first.2
          rw [hfirst] at hfirstSelected
          change data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible (data.reductionSeamEdge graphData side fixed) = a ∨
            data.reductionExtensionColoring graphData hcubic C hC side
              hcompatible (data.reductionSeamEdge graphData side fixed) = b at hfirstSelected
          simpa only [data.reductionExtensionColoring_reductionSeamEdge_right]
            using hfirstSelected
        have hLK : L = K := by
          rcases hmeets with hLleft | hLright
          · exact data.degreeTwoBoundaryData
              |>.kempeComponent_eq_of_meetsPort_of_colorWord_selected
                hdata C hab (side.leftPort fixed)
                hfixedLeftSelected hLleft hKleft
          · exact data.degreeTwoBoundaryData
              |>.kempeComponent_eq_of_meetsPort_of_colorWord_selected
                hdata C hab (side.rightPort fixed)
                hfixedRightSelected hLright hKright
        left
        refine ⟨oldSecond, hsecond, ?_⟩
        simpa [hLK] using holdL
      · have hseamAdj :
            (data.reductionRotationSystem graphData side).edgeAdjacencyGraph.Adj
              (data.reductionSeamEdge graphData side fixed)
              (data.reductionSeamEdge graphData side step) := by
          rw [← hfirst, ← hsecond]
          exact hadjRaw
        by_cases hstep : fixed = step
        · subst step
          exact (hseamAdj.ne rfl).elim
        · exact (data.not_adj_reductionSeamEdge_of_ne graphData side
            hstep hseamAdj).elim
  constructor
  · exact hpreserve hadj
  · exact hpreserve hadj.symm

/-- The component obtained by closing one exact open component with its
matching seam contains precisely the old edges of that open component. -/
theorem reductionOldEdge_mem_cappedComponent_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (fixed : Fin 2)
    (hsupport : data.degreeTwoBoundaryData.kempePortSupport C a b K =
      ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)))
    (Kcap : ((data.reductionExtensionColoring graphData hcubic C hC side
      hcompatible).bicoloredSubgraph a b).ConnectedComponent)
    (hseam : data.reductionSeamEdge graphData side fixed ∈
      (data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible).kempeComponentSet a b Kcap)
    (old : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    data.reductionEdgeOfDeletedEdge graphData side old ∈
        (data.reductionExtensionColoring graphData hcubic C hC side
          hcompatible).kempeComponentSet a b Kcap ↔
      old ∈ C.kempeComponentSet a b K := by
  let capped := data.reductionExtensionColoring graphData hcubic C hC
    side hcompatible
  constructor
  · intro holdCap
    let seamSelected : capped.bicoloredSet a b :=
      ⟨data.reductionSeamEdge graphData side fixed, hseam.1⟩
    let oldSelected : capped.bicoloredSet a b :=
      ⟨data.reductionEdgeOfDeletedEdge graphData side old, holdCap.1⟩
    have hreachable : (capped.bicoloredSubgraph a b).Reachable
        seamSelected oldSelected :=
      ConnectedComponent.eq.mp (hseam.2.trans holdCap.2.symm)
    have hinvariant := predicate_iff_of_reachable_of_adj_iff
      (fun edge : capped.bicoloredSet a b =>
        data.CappedFromOpenComponent graphData side C a b K fixed edge.1)
      hreachable
      (fun {_ _} hadj => data.cappedFromOpenComponent_adj_iff
        graphData hcubic C hC side hcompatible hab K fixed
          hsupport hadj)
    have hfinish : data.CappedFromOpenComponent graphData side C a b K
        fixed oldSelected.1 := hinvariant.1 (Or.inr rfl)
    rcases hfinish with ⟨source, hsource, hsourceK⟩ | hsource
    · have heq : old = source :=
        data.reductionEdgeOfDeletedEdge_injective graphData side hsource
      simpa [heq] using hsourceK
    · exact (data.reductionEdgeOfDeletedEdge_ne_reductionSeamEdge
        graphData side old fixed hsource).elim
  · intro hold
    have hleftMem : side.leftPort fixed ∈
        data.degreeTwoBoundaryData.kempePortSupport C a b K := by
      rw [hsupport]
      simp
    have hmeets := (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
      C a b K (side.leftPort fixed)).1 hleftMem
    have hfixedSelected :
        data.degreeTwoBoundaryData.colorWord C (side.leftPort fixed) = a ∨
          data.degreeTwoBoundaryData.colorWord C (side.leftPort fixed) = b := by
      have hseamSelected := hseam.1
      change data.reductionExtensionColoring graphData hcubic C hC side
          hcompatible (data.reductionSeamEdge graphData side fixed) = a ∨
        data.reductionExtensionColoring graphData hcubic C hC side
          hcompatible (data.reductionSeamEdge graphData side fixed) = b at hseamSelected
      simpa only [data.reductionExtensionColoring_reductionSeamEdge_left]
        using hseamSelected
    rcases data.exists_cappedComponent_containing_seam_and_openComponent
        graphData hcubic C hC side hcompatible K fixed hmeets
        hfixedSelected with
      ⟨Knew, hseamNew, holdNew⟩
    have hsameSeam :
        (⟨data.reductionSeamEdge graphData side fixed, hseamNew.1⟩ :
          capped.bicoloredSet a b) =
        ⟨data.reductionSeamEdge graphData side fixed, hseam.1⟩ := rfl
    have hcomponents : Knew = Kcap := by
      calc
        Knew = (capped.bicoloredSubgraph a b).connectedComponentMk
            ⟨data.reductionSeamEdge graphData side fixed, hseamNew.1⟩ :=
          hseamNew.2.symm
        _ = (capped.bicoloredSubgraph a b).connectedComponentMk
            ⟨data.reductionSeamEdge graphData side fixed, hseam.1⟩ :=
          congrArg _ hsameSeam
        _ = Kcap := hseam.2
    have := holdNew old hold
    simpa [hcomponents] using this

/-- Switching the closed capped component restricts exactly to switching the
original open component. -/
theorem reductionDeletedColoring_swapOn_cappedComponent
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (fixed : Fin 2)
    (hsupport : data.degreeTwoBoundaryData.kempePortSupport C a b K =
      ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)))
    (Kcap : ((data.reductionExtensionColoring graphData hcubic C hC side
      hcompatible).bicoloredSubgraph a b).ConnectedComponent)
    (hseam : data.reductionSeamEdge graphData side fixed ∈
      (data.reductionExtensionColoring graphData hcubic C hC side
        hcompatible).kempeComponentSet a b Kcap) :
    data.reductionDeletedColoring graphData side
        ((data.reductionExtensionColoring graphData hcubic C hC side
          hcompatible).swapOnKempeComponent a b Kcap) =
      C.swapOnKempeComponent a b K := by
  let capped := data.reductionExtensionColoring graphData hcubic C hC
    side hcompatible
  apply DFunLike.ext _ _
  intro old
  rw [data.reductionDeletedColoring_apply]
  have hcomponent := data.reductionOldEdge_mem_cappedComponent_iff
    graphData hcubic C hC side hcompatible hab K fixed hsupport
      Kcap hseam old
  by_cases hold : old ∈ C.kempeComponentSet a b K
  · rw [capped.swapOnKempeComponent_apply_of_mem (hcomponent.2 hold),
      C.swapOnKempeComponent_apply_of_mem hold,
      data.reductionExtensionColoring_reductionEdgeOfDeletedEdge]
  · have holdCap : data.reductionEdgeOfDeletedEdge graphData side old ∉
        capped.kempeComponentSet a b Kcap := by
      intro hcap
      exact hold (hcomponent.1 hcap)
    rw [capped.swapOnKempeComponent_apply_of_not_mem holdCap,
      C.swapOnKempeComponent_apply_of_not_mem hold,
      data.reductionExtensionColoring_reductionEdgeOfDeletedEdge]

/-- An exact same-side open Kempe switch is realized by one ordinary closed
Kempe switch after inserting the matching seam.  The conclusion is stated on
the retained old edges, which is precisely the path-lifting fact needed by the
source formation argument. -/
theorem exists_cappedKempeComponent_restricts_sameSideSwitch
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (side : SquareReductionSide)
    (hcompatible : side.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (fixed : Fin 2)
    (hsupport : data.degreeTwoBoundaryData.kempePortSupport C a b K =
      ({side.leftPort fixed, side.rightPort fixed} : Finset (Fin 4)))
    (hfixedSelected :
      data.degreeTwoBoundaryData.colorWord C (side.leftPort fixed) = a ∨
        data.degreeTwoBoundaryData.colorWord C (side.leftPort fixed) = b) :
    let capped := data.reductionExtensionColoring graphData hcubic C hC
      side hcompatible
    ∃ Kcap : (capped.bicoloredSubgraph a b).ConnectedComponent,
      data.reductionSeamEdge graphData side fixed ∈
          capped.kempeComponentSet a b Kcap ∧
        data.reductionDeletedColoring graphData side
            (capped.swapOnKempeComponent a b Kcap) =
          C.swapOnKempeComponent a b K := by
  dsimp only
  have hleftMem : side.leftPort fixed ∈
      data.degreeTwoBoundaryData.kempePortSupport C a b K := by
    rw [hsupport]
    simp
  have hmeets := (data.degreeTwoBoundaryData.mem_kempePortSupport_iff
    C a b K (side.leftPort fixed)).1 hleftMem
  rcases data.exists_cappedComponent_containing_seam_and_openComponent
      graphData hcubic C hC side hcompatible K fixed hmeets
        hfixedSelected with
    ⟨Kcap, hseam, _⟩
  refine ⟨Kcap, hseam, ?_⟩
  exact data.reductionDeletedColoring_swapOn_cappedComponent
    graphData hcubic C hC side hcompatible hab K fixed hsupport Kcap hseam

/-- Every corner of the canonical same-side boundary orbit remains compatible
with the `01|23` planar cap. -/
theorem join01_23_compatible_sameSideBoundaryKempeOrbit
    (a b : Color) (word : Fin 4 → Color)
    (hcompatible : SquareReductionSide.join01_23.Compatible word)
    (state : Fin 4) :
    SquareReductionSide.join01_23.Compatible
      (sameSideBoundaryKempeOrbit a b word state) := by
  have hpairs : word 0 = word 1 ∧ word 2 = word 3 := by
    simpa [SquareReductionSide.Compatible,
      SquareReductionSide.join01_23] using hcompatible
  fin_cases state <;>
    simp [sameSideBoundaryKempeOrbit, boundaryKempeSwap,
      SquareReductionSide.Compatible, SquareReductionSide.join01_23,
      hpairs.1, hpairs.2]

/-- If one deletion coloring has an exact two-component same-side Kempe
profile and is compatible with the `01|23` cap, all four corners of its Kempe
square extend across that same cap. -/
theorem sameSideKempeSquare_states_extend
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (K01 K23 : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hsupport01 : data.degreeTwoBoundaryData.kempePortSupport C a b K01 =
      {0, 1})
    (hsupport23 : data.degreeTwoBoundaryData.kempePortSupport C a b K23 =
      {2, 3})
    (hcompatible : SquareReductionSide.join01_23.Compatible
      (data.degreeTwoBoundaryData.colorWord C)) :
    ∀ state : Fin 4,
      ∃ capped : (data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).EdgeColoring Color,
        (data.reductionRotationSystem graphData
          SquareReductionSide.join01_23).IsTaitEdgeColoring capped := by
  intro state
  let Cstate := Coloring.kempeSwitchSquareColoring C a b K01 K23 state
  have hCstate : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) Cstate :=
    GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData.isTaitEdgeColoring_kempeSwitchSquareColoring
        C hC hab K01 K23 state
  have hword : data.degreeTwoBoundaryData.colorWord Cstate =
      sameSideBoundaryKempeOrbit a b
        (data.degreeTwoBoundaryData.colorWord C) state :=
    GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData.colorWord_kempeSwitchSquareColoring_eq_sameSideOrbit
      data.degreeTwoBoundaryData C hab K01 K23 hsupport01 hsupport23 state
  have hcompatibleState : SquareReductionSide.join01_23.Compatible
      (data.degreeTwoBoundaryData.colorWord Cstate) := by
    rw [hword]
    exact join01_23_compatible_sameSideBoundaryKempeOrbit
      a b (data.degreeTwoBoundaryData.colorWord C) hcompatible state
  exact ⟨data.reductionExtensionColoring graphData hcubic Cstate hCstate
      SquareReductionSide.join01_23 hcompatibleState,
    data.reductionExtensionColoring_isTait graphData hcubic Cstate hCstate
      SquareReductionSide.join01_23 hcompatibleState⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

/-! Publication-facing aliases. -/

alias GoertzelV24AdjacentPairReductionKempeSquare.sameSideKempeSquare_states_extend :=
  GoertzelV24AdjacentPairBoundary.AdjacentPairData.sameSideKempeSquare_states_extend

alias GoertzelV24AdjacentPairReductionKempeSquare.exists_cappedKempeComponent_restricts_sameSideSwitch :=
  GoertzelV24AdjacentPairBoundary.AdjacentPairData.exists_cappedKempeComponent_restricts_sameSideSwitch

end Mettapedia.GraphTheory.FourColor
