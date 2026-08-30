import Mettapedia.GraphTheory.EdgeColoringEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalSwapKempeGeneration

/-!
# Restricting a Kempe component along a graph embedding

A Kempe component in a subgraph need not be a Kempe component of the larger
graph: an alternating path may leave the image.  This file gives the exact
dichotomy.  Either the small component has a selected neighbour outside the
edge image, or its switch is the restriction of one ordinary Kempe-component
switch in the larger graph.

The result is generic graph theory.  In the Four-Colour application the
embedding is the exact common deletion of two adjacent pairs into either one
of the two pair-deletion graphs.  The boundary horn then says that the Kempe
component reaches an edge exposed by the other deleted pair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KempeComponentEmbeddingBoundary

open GoertzelV24LocalSwapKempeGeneration
open SimpleGraph

universe u v w

variable {SmallVertex : Type u} {LargeVertex : Type v} {ColorType : Type w}
  {smallGraph : SimpleGraph SmallVertex}
  {largeGraph : SimpleGraph LargeVertex}

/-- A property containing the start of a walk and closed under one graph edge
contains the endpoint of the walk. -/
theorem Walk.end_mem_of_start_mem_of_adj_closed
    {start finish : LargeVertex}
    (walk : largeGraph.Walk start finish)
    (property : LargeVertex → Prop)
    (hstart : property start)
    (hclosed : ∀ {left right}, property left →
      largeGraph.Adj left right → property right) :
    property finish := by
  induction walk with
  | nil => exact hstart
  | @cons current next finish hadj tail ih =>
      apply ih
      exact hclosed hstart hadj

/-- A connected component whose image is closed under adjacent vertices is
exactly one connected component of the target graph. -/
theorem exists_target_component_of_neighbor_closed
    (embedding : smallGraph ↪g largeGraph)
    (component : smallGraph.ConnectedComponent)
    (hclosed : ∀ smallVertex, smallVertex ∈ component →
      ∀ largeVertex, largeGraph.Adj (embedding smallVertex) largeVertex →
        ∃ nextSmall, nextSmall ∈ component ∧
          embedding nextSmall = largeVertex) :
    ∃ targetComponent : largeGraph.ConnectedComponent,
      ∀ smallVertex,
        smallVertex ∈ component ↔
          embedding smallVertex ∈ targetComponent := by
  rcases component.nonempty_supp with ⟨root, hroot⟩
  let targetComponent := largeGraph.connectedComponentMk (embedding root)
  refine ⟨targetComponent, fun smallVertex => ?_⟩
  constructor
  · intro hsmall
    have hreachable : smallGraph.Reachable root smallVertex :=
      component.reachable_of_mem_supp hroot hsmall
    have hmapped : largeGraph.Reachable
        (embedding root) (embedding smallVertex) :=
      hreachable.map embedding.toHom
    exact ConnectedComponent.sound hmapped |>.symm
  · intro htarget
    have hreachable : largeGraph.Reachable
        (embedding root) (embedding smallVertex) := by
      apply ConnectedComponent.exact
      exact htarget.symm
    rcases hreachable with ⟨walk⟩
    let imageOfComponent : LargeVertex → Prop := fun largeVertex =>
      ∃ sourceVertex, sourceVertex ∈ component ∧
        embedding sourceVertex = largeVertex
    have hrootImage : imageOfComponent (embedding root) :=
      ⟨root, hroot, rfl⟩
    have himageClosed : ∀ {left right}, imageOfComponent left →
        largeGraph.Adj left right → imageOfComponent right := by
      rintro left right ⟨sourceVertex, hsource, rfl⟩ hadj
      exact hclosed sourceVertex hsource right hadj
    rcases Walk.end_mem_of_start_mem_of_adj_closed
        walk imageOfComponent hrootImage himageClosed with
      ⟨sourceVertex, hsource, heq⟩
    have : sourceVertex = smallVertex := embedding.injective heq
    simpa [this] using hsource

variable [DecidableEq ColorType]

/-- The embedding induced on the two-colour line-graph subgraphs. -/
def bicoloredSubgraphEmbedding
    (coloring : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph)
    (first second : ColorType) :
    ((coloring.pullbackEmbedding embedding).bicoloredSubgraph first second) ↪g
      (coloring.bicoloredSubgraph first second) where
  toFun edge := ⟨embedding.mapEdgeSet edge.1, edge.2⟩
  inj' left right heq := by
    apply Subtype.ext
    exact embedding.mapEdgeSet.injective (congrArg Subtype.val heq)
  map_rel_iff' := by
    intro left right
    change largeGraph.lineGraph.Adj
        (embedding.mapEdgeSet left.1) (embedding.mapEdgeSet right.1) ↔
      smallGraph.lineGraph.Adj left.1 right.1
    exact embedding.toCopy.toLineGraphEmbedding.map_rel_iff

/-- The small component reaches the boundary of the edge image when a
selected large edge outside that image is adjacent to one of its edges. -/
def ComponentTouchesEmbeddingBoundary
    (coloring : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph)
    (first second : ColorType)
    (component : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent) : Prop :=
  ∃ smallEdge,
    smallEdge ∈ (coloring.pullbackEmbedding embedding).kempeComponentSet
      first second component ∧
    ∃ largeEdge,
      largeEdge ∈ coloring.bicoloredSet first second ∧
      largeGraph.lineGraph.Adj
        (embedding.mapEdgeSet smallEdge) largeEdge ∧
      ¬ ∃ preimage, embedding.mapEdgeSet preimage = largeEdge

omit [DecidableEq ColorType] in
/-- If the component does not touch the boundary, its image is neighbour
closed in the large bicoloured subgraph. -/
theorem bicolored_image_neighbor_closed_of_not_touchesBoundary
    (coloring : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph)
    (first second : ColorType)
    (component : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent)
    (hboundary : ¬ ComponentTouchesEmbeddingBoundary coloring embedding
      first second component) :
    ∀ smallEdge,
      smallEdge ∈ component →
      ∀ largeEdge,
        (coloring.bicoloredSubgraph first second).Adj
          (bicoloredSubgraphEmbedding coloring embedding first second smallEdge)
          largeEdge →
        ∃ nextSmall, nextSmall ∈ component ∧
          bicoloredSubgraphEmbedding coloring embedding first second nextSmall =
            largeEdge := by
  intro smallEdge hsmall largeEdge hadj
  have hsmallComponent : smallEdge.1 ∈
      (coloring.pullbackEmbedding embedding).kempeComponentSet
        first second component := ⟨smallEdge.2, hsmall⟩
  have hpreimage : ∃ preimage,
      embedding.mapEdgeSet preimage = largeEdge.1 := by
    by_contra hnone
    apply hboundary
    exact ⟨smallEdge.1, hsmallComponent, largeEdge.1, largeEdge.2,
      hadj, hnone⟩
  rcases hpreimage with ⟨preimage, hpreimage⟩
  have hselected : preimage ∈
      (coloring.pullbackEmbedding embedding).bicoloredSet first second := by
    change coloring (embedding.mapEdgeSet preimage) = first ∨
      coloring (embedding.mapEdgeSet preimage) = second
    rw [hpreimage]
    exact largeEdge.2
  let nextSmall :
      (coloring.pullbackEmbedding embedding).bicoloredSet first second :=
    ⟨preimage, hselected⟩
  have hnextMap :
      bicoloredSubgraphEmbedding coloring embedding first second nextSmall =
        largeEdge := by
    apply Subtype.ext
    exact hpreimage
  have hadjSmall :
      ((coloring.pullbackEmbedding embedding).bicoloredSubgraph first second).Adj
        smallEdge nextSmall := by
    apply (bicoloredSubgraphEmbedding coloring embedding first second).map_rel_iff.1
    rw [hnextMap]
    exact hadj
  have hnext : nextSmall ∈ component :=
    component.mem_supp_of_adj_mem_supp hsmall hadjSmall
  refine ⟨nextSmall, hnext, ?_⟩
  apply Subtype.ext
  exact hpreimage

/-- **Embedding dichotomy for a Kempe switch.**  A component either reaches a
selected edge outside the image, or its switch is the literal restriction of
one large-component switch. -/
theorem touchesBoundary_or_exists_liftedComponentSwitch
    (coloring : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph)
    (first second : ColorType)
    (component : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent) :
    ComponentTouchesEmbeddingBoundary coloring embedding first second component ∨
      ∃ targetComponent :
          (coloring.bicoloredSubgraph first second).ConnectedComponent,
        SimpleGraph.EdgeColoring.pullbackEmbedding
            (coloring.swapOnKempeComponent first second targetComponent)
            embedding =
          (coloring.pullbackEmbedding embedding).swapOnKempeComponent
            first second component := by
  by_cases hboundary : ComponentTouchesEmbeddingBoundary coloring embedding
      first second component
  · exact Or.inl hboundary
  · right
    obtain ⟨targetComponent, hcomponent⟩ :=
      exists_target_component_of_neighbor_closed
        (bicoloredSubgraphEmbedding coloring embedding first second)
        component
        (bicolored_image_neighbor_closed_of_not_touchesBoundary
          coloring embedding first second component hboundary)
    refine ⟨targetComponent, ?_⟩
    apply DFunLike.ext _ _
    intro edge
    have hmembership : edge ∈
          (coloring.pullbackEmbedding embedding).kempeComponentSet
            first second component ↔
        embedding.mapEdgeSet edge ∈
          coloring.kempeComponentSet first second targetComponent := by
      constructor
      · rintro ⟨hselected, hedge⟩
        exact ⟨hselected, (hcomponent ⟨edge, hselected⟩).1 hedge⟩
      · rintro ⟨hselected, hedge⟩
        have hsmallSelected : edge ∈
            (coloring.pullbackEmbedding embedding).bicoloredSet
              first second := hselected
        exact ⟨hsmallSelected,
          (hcomponent ⟨edge, hsmallSelected⟩).2 hedge⟩
    by_cases hedge : edge ∈
        (coloring.pullbackEmbedding embedding).kempeComponentSet
          first second component
    · rw [SimpleGraph.EdgeColoring.pullbackEmbedding_apply,
        coloring.swapOnKempeComponent_apply_of_mem
          (hmembership.1 hedge),
        SimpleGraph.Coloring.swapOnKempeComponent_apply_of_mem
          (coloring.pullbackEmbedding embedding) hedge]
      rfl
    · rw [SimpleGraph.EdgeColoring.pullbackEmbedding_apply,
        coloring.swapOnKempeComponent_apply_of_not_mem
          (fun hmember => hedge (hmembership.2 hmember)),
        SimpleGraph.Coloring.swapOnKempeComponent_apply_of_not_mem
          (coloring.pullbackEmbedding embedding) hedge]
      rfl

/-- A boundary-reaching component occurs at some colouring in the large
Kempe orbit of the supplied base. -/
def HasBoundaryStepInLiftOrbit
    (base : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph) : Prop :=
  ∃ current : largeGraph.EdgeColoring ColorType,
    current ∈ largeGraph.EdgeKempeClosure base ∧
    ∃ first second : ColorType,
      ∃ component : ((current.pullbackEmbedding embedding).bicoloredSubgraph
        first second).ConnectedComponent,
        ComponentTouchesEmbeddingBoundary current embedding
          first second component

/-- A whole finite common-core Kempe sequence either lifts to the large graph
or exposes a boundary-reaching component at one intermediate colouring. -/
theorem boundaryAlongLiftOrbit_or_exists_liftedColoring
    (base : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph)
    (target : smallGraph.EdgeColoring ColorType)
    (hreachable : target ∈ smallGraph.EdgeKempeClosure
      (base.pullbackEmbedding embedding)) :
    HasBoundaryStepInLiftOrbit base embedding ∨
      ∃ lifted : largeGraph.EdgeColoring ColorType,
        lifted ∈ largeGraph.EdgeKempeClosure base ∧
        lifted.pullbackEmbedding embedding = target := by
  induction hreachable with
  | refl =>
      right
      exact ⟨base, largeGraph.mem_edgeKempeClosure_self base, rfl⟩
  | tail hprefix hstep ih =>
      rcases ih with hboundary | ⟨current, hcurrent, hrestrict⟩
      · exact Or.inl hboundary
      · rcases hstep with ⟨first, second, component, rfl⟩
        subst hrestrict
        rcases touchesBoundary_or_exists_liftedComponentSwitch
            current embedding first second component with
          htouches | ⟨targetComponent, hlift⟩
        · left
          exact ⟨current, hcurrent, first, second, component, htouches⟩
        · right
          let lifted := current.swapOnKempeComponent
            first second targetComponent
          have hlifted : lifted ∈ largeGraph.EdgeKempeClosure base :=
            largeGraph.mem_edgeKempeClosure_of_mem_of_step
              hcurrent first second targetComponent
          exact ⟨lifted, hlifted, hlift⟩

/-! ## The Tait-preserving lift -/

/-- Pulling a nonzero edge colouring back along a graph embedding preserves
the nonzero condition. -/
theorem isTaitEdgeColoring_pullbackEmbedding
    (coloring : largeGraph.EdgeColoring Color)
    (embedding : smallGraph ↪g largeGraph)
    (hcoloring : IsTaitEdgeColoring largeGraph coloring) :
    IsTaitEdgeColoring smallGraph
      (coloring.pullbackEmbedding embedding) := by
  intro edge
  exact hcoloring (embedding.mapEdgeSet edge)

/-- A boundary-reaching valid-pair component occurs at some colouring in the
large Tait-Kempe orbit of the supplied base. -/
def HasTaitBoundaryStepInLiftOrbit
    (base : largeGraph.EdgeColoring Color)
    (embedding : smallGraph ↪g largeGraph) : Prop :=
  ∃ current : largeGraph.EdgeColoring Color,
    TaitKempeReachable base current ∧
    ∃ first second : Color, ValidColorPair first second ∧
      ∃ component : ((current.pullbackEmbedding embedding).bicoloredSubgraph
        first second).ConnectedComponent,
        ComponentTouchesEmbeddingBoundary current embedding
          first second component

/-- **Tait-preserving finite lift-or-boundary dichotomy.**  A finite
valid-pair Kempe sequence on the embedded graph either reaches the embedding
boundary or lifts to a finite valid-pair sequence upstairs. -/
theorem taitBoundaryAlongLiftOrbit_or_exists_liftedColoring
    (base : largeGraph.EdgeColoring Color)
    (hbase : IsTaitEdgeColoring largeGraph base)
    (embedding : smallGraph ↪g largeGraph)
    (target : smallGraph.EdgeColoring Color)
    (hreachable : TaitKempeReachable
      (base.pullbackEmbedding embedding) target) :
    HasTaitBoundaryStepInLiftOrbit base embedding ∨
      ∃ lifted : largeGraph.EdgeColoring Color,
        TaitKempeReachable base lifted ∧
        IsTaitEdgeColoring largeGraph lifted ∧
        lifted.pullbackEmbedding embedding = target := by
  induction hreachable with
  | refl =>
      right
      exact ⟨base, Relation.ReflTransGen.refl, hbase, rfl⟩
  | tail hprefix hstep ih =>
      rcases ih with hboundary | ⟨current, hcurrent, hcurrentTait, hrestrict⟩
      · exact Or.inl hboundary
      · rcases hstep with ⟨first, second, hpair, component, rfl⟩
        subst hrestrict
        rcases touchesBoundary_or_exists_liftedComponentSwitch
            current embedding first second component with
          htouches | ⟨targetComponent, hlift⟩
        · left
          exact ⟨current, hcurrent, first, second, hpair,
            component, htouches⟩
        · right
          let lifted := current.swapOnKempeComponent
            first second targetComponent
          have hlargeStep : TaitKempeStep current lifted :=
            ⟨first, second, hpair, targetComponent, rfl⟩
          have hliftedReachable : TaitKempeReachable base lifted :=
            hcurrent.tail hlargeStep
          have hliftedTait : IsTaitEdgeColoring largeGraph lifted :=
            isTaitEdgeColoring_of_taitKempeStep hcurrentTait hlargeStep
          exact ⟨lifted, hliftedReachable, hliftedTait, hlift⟩

end GoertzelV24KempeComponentEmbeddingBoundary

end Mettapedia.GraphTheory.FourColor
