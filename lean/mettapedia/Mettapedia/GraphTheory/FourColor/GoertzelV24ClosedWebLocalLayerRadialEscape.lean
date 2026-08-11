import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerHoleFaceKept
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTotalClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords

/-!
# A radial escape from a source-local four-edge layer cut

The source's closed web has five inner stubs.  Under total closure, every
oriented Tait-pair incidence at an inner stub belongs to a radial component.
The source-local Cell-3 layer deletes exactly four primal edges.  This module
will use the twenty oriented incidences, rather than an unproved topological
picture, to construct one radial comparison walk which avoids that four-edge
cut.  It is the missing input for retaining both named holes through the
source splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComponentCensus
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24DualPathTransversal
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-! `RetainedVertex` has a deliberately broad finite-carrier instance for
splice construction.  This local finite count is over ordinary subtypes of
the six Tait-pair indices, so retain Lean's standard subtype instance here. -/
attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance closedWebLocalLayerRadialEscapeEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Choose the actual radial path through the component containing one
oriented inner endpoint.  The component is determined by the endpoint; the
choice only selects its already-proved path realization. -/
noncomputable def radialPathOfInnerEnd
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (endpoint : InnerEnd data coloring) :
    ComponentRadialPath data coloring endpoint.1.firstColor endpoint.1.secondColor
      (innerEndComponent data hdata coloring endpoint).2 := by
  let hall : EveryColorPairComponentRadial data coloring :=
    everyColorPairComponentRadial_at_five_of_innerTouching
      data hdata coloring htait hinnerTouching
  exact Classical.choice <|
    nonempty_componentRadialPath data hdata coloring htait endpoint.1.valid
      (hall endpoint.1.firstColor endpoint.1.secondColor endpoint.1.valid)
      (innerEndComponent data hdata coloring endpoint).2

/-- The path selected for an oriented inner endpoint starts at that endpoint,
not merely at some unrelated inner stub in the same color-pair component. -/
theorem radialPathOfInnerEnd_inner_eq
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (endpoint : InnerEnd data coloring) :
    (radialPathOfInnerEnd data hdata coloring htait hinnerTouching endpoint).inner =
      endpoint.2.1 := by
  let component := (innerEndComponent data hdata coloring endpoint).2
  let radial := radialPathOfInnerEnd data hdata coloring htait hinnerTouching endpoint
  let hall : EveryColorPairComponentRadial data coloring :=
    everyColorPairComponentRadial_at_five_of_innerTouching
      data hdata coloring htait hinnerTouching
  rcases hall endpoint.1.firstColor endpoint.1.secondColor endpoint.1.valid
      component with ⟨⟨chosenInner, hchosenInner, hchosenUnique⟩, _⟩
  have hendpoint : ComponentContainsInnerStub data coloring
      endpoint.1.firstColor endpoint.1.secondColor component endpoint.2.1 := by
    refine ⟨innerEndVertex data hdata coloring endpoint, ?_, rfl⟩
    dsimp [component, innerEndComponent]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hradial : ComponentContainsInnerStub data coloring
      endpoint.1.firstColor endpoint.1.secondColor component radial.inner :=
    ⟨radial.start, radial.start_mem, radial.start_eq_innerStub⟩
  have hendpointEq : endpoint.2.1 = chosenInner :=
    hchosenUnique endpoint.2.1 hendpoint
  have hradialEq : radial.inner = chosenInner :=
    hchosenUnique radial.inner hradial
  exact hradialEq.trans hendpointEq.symm

/-- Every ambient edge of the chosen radial path uses one of the endpoint's
two indexed Tait colors. -/
theorem radialPathOfInnerEnd_edge_selected
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (endpoint : InnerEnd data coloring) (edge : G.edgeSet)
    (hedge : edge.1 ∈ (ambientRadialPath
      (radialPathOfInnerEnd data hdata coloring htait hinnerTouching endpoint)).edges) :
    endpoint.1.Selects (coloring edge) := by
  simpa only [TaitPairIndex.Selects] using
    mapped_walk_edges_color_pair
      (radialPathOfInnerEnd data hdata coloring htait hinnerTouching endpoint).path
      edge hedge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two radial paths in one selected color-pair graph which traverse one
ambient edge belong to the same support component.  This is the local
disjointness fact needed for the finite cut-capacity count; it uses the
injective inclusion of the support graph, not a drawing. -/
theorem radialComponent_eq_of_common_ambient_edge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {first second : Color}
    {leftComponent rightComponent :
      (colorPairSupportGraph coloring first second).ConnectedComponent}
    (leftPath : ComponentRadialPath data coloring first second leftComponent)
    (rightPath : ComponentRadialPath data coloring first second rightComponent)
    (edge : G.edgeSet)
    (hleft : edge.1 ∈ (ambientRadialPath leftPath).edges)
    (hright : edge.1 ∈ (ambientRadialPath rightPath).edges) :
    leftComponent = rightComponent := by
  change edge.1 ∈ (leftPath.path.map
    (colorPairSupportToAmbientHom coloring first second)).edges at hleft
  rw [SimpleGraph.Walk.edges_map] at hleft
  rcases List.mem_map.mp hleft with ⟨leftEdge, hleftEdge, hleftMap⟩
  change edge.1 ∈ (rightPath.path.map
    (colorPairSupportToAmbientHom coloring first second)).edges at hright
  rw [SimpleGraph.Walk.edges_map] at hright
  rcases List.mem_map.mp hright with ⟨rightEdge, hrightEdge, hrightMap⟩
  have hsourceEq : leftEdge = rightEdge := by
    apply Sym2.map.injective Subtype.val_injective
    exact hleftMap.trans hrightMap.symm
  rcases Sym2.mk_surjective leftEdge with ⟨⟨vertex, neighbor⟩, hleftEdgeRep⟩
  have hvertexLeft : vertex ∈ leftComponent.supp := by
    rw [← leftPath.path_vertices]
    apply leftPath.path.mem_verts_toSubgraph.mpr
    rw [← hleftEdgeRep] at hleftEdge
    exact leftPath.path.fst_mem_support_of_mem_edges hleftEdge
  have hvertexRight : vertex ∈ rightComponent.supp := by
    rw [← rightPath.path_vertices]
    apply rightPath.path.mem_verts_toSubgraph.mpr
    rw [← hsourceEq, ← hleftEdgeRep] at hrightEdge
    exact rightPath.path.fst_mem_support_of_mem_edges hrightEdge
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
    hvertexLeft hvertexRight

/-- One slot records a crossed local-layer edge together with one of the
four oriented Tait pairs selecting its nonzero color.  If every radial
incidence crossed the local wall, it would inject into these slots. -/
abbrev CutPairSlot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :=
  Σ edge : {candidate : G.edgeSet // candidate ∈ layers.cutEdges hunique},
    {pair : TaitPairIndex // pair.Selects (coloring edge.1)}

/-- The source-local four-edge wall has only sixteen oriented color-pair
slots: four cut edges, each selected by four of the six oriented pairs. -/
theorem cutPairSlot_card_eq_sixteen
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Fintype.card (CutPairSlot layers hunique) = 16 := by
  calc
    Fintype.card (CutPairSlot layers hunique) =
        ∑ edge : {candidate : G.edgeSet // candidate ∈ layers.cutEdges hunique},
          Fintype.card {pair : TaitPairIndex // pair.Selects (coloring edge.1)} :=
      Fintype.card_sigma
    _ = ∑ _edge : {candidate : G.edgeSet // candidate ∈ layers.cutEdges hunique}, 4 := by
      apply Finset.sum_congr rfl
      intro edge _
      exact TaitPairIndex.selected_card_eq_four _ (web.tait edge.1)
    _ = Fintype.card {candidate : G.edgeSet // candidate ∈ layers.cutEdges hunique} * 4 := by
      simp
    _ = 16 := by
      rw [Fintype.card_coe, layers.cutEdges_card_eq_four hunique]

/-- Under the contrary assumption that every radial realization crosses the
local layer wall, choose one literal crossed edge for each oriented inner
incidence.  The subsequent counting proof shows that this choice cannot be
injective. -/
noncomputable def crossedCutEdgeOfInnerEnd
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ layers.cutEdges hunique ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges)
    (endpoint : InnerEnd data coloring) :
    {edge : G.edgeSet // edge ∈ layers.cutEdges hunique} :=
  ⟨Classical.choose (hcross endpoint),
    (Classical.choose_spec (hcross endpoint)).1⟩

/-- The chosen crossing edge really occurs on the corresponding radial path. -/
theorem crossedCutEdgeOfInnerEnd_mem_path
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ layers.cutEdges hunique ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges)
    (endpoint : InnerEnd data coloring) :
    (crossedCutEdgeOfInnerEnd layers hunique hinnerTouching hcross endpoint).1.1 ∈
      (ambientRadialPath
        (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
          hinnerTouching endpoint)).edges := by
  exact (Classical.choose_spec (hcross endpoint)).2

/-- If every radial path crossed the four-edge wall, send its oriented inner
incidence to the crossed edge together with its selecting Tait-pair index. -/
noncomputable def radialCutSlotOfInnerEnd
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ layers.cutEdges hunique ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges)
    (endpoint : InnerEnd data coloring) : CutPairSlot layers hunique :=
  ⟨crossedCutEdgeOfInnerEnd layers hunique hinnerTouching hcross endpoint,
    ⟨endpoint.1,
      radialPathOfInnerEnd_edge_selected
        data web.boundary_wellFormed coloring web.tait hinnerTouching endpoint
        (crossedCutEdgeOfInnerEnd layers hunique hinnerTouching hcross endpoint).1
        (crossedCutEdgeOfInnerEnd_mem_path
          layers hunique hinnerTouching hcross endpoint)⟩⟩

/-- The component attached to an inner endpoint contains that endpoint's
actual boundary stub. -/
theorem innerEndComponent_contains_inner
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (endpoint : InnerEnd data coloring) :
    ComponentContainsInnerStub data coloring endpoint.1.firstColor endpoint.1.secondColor
      (innerEndComponent data hdata coloring endpoint).2 endpoint.2.1 := by
  refine ⟨innerEndVertex data hdata coloring endpoint, ?_, rfl⟩
  dsimp [innerEndComponent]
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- The cut-slot assignment is injective: two same-pair radial components
which traverse one ambient cut edge are the same component, and a component
has only one inner endpoint. -/
theorem radialCutSlotOfInnerEnd_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ layers.cutEdges hunique ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges) :
    Function.Injective (radialCutSlotOfInnerEnd layers hunique hinnerTouching hcross) := by
  intro left right heq
  have hpair : left.1 = right.1 :=
    congrArg (fun slot : CutPairSlot layers hunique => slot.2.1) heq
  have hedge :
      (crossedCutEdgeOfInnerEnd layers hunique hinnerTouching hcross left).1 =
        (crossedCutEdgeOfInnerEnd layers hunique hinnerTouching hcross right).1 :=
    congrArg (fun slot : CutPairSlot layers hunique => slot.1.1) heq
  cases left with
  | mk leftPair leftInner =>
    cases right with
    | mk rightPair rightInner =>
      dsimp at hpair hedge ⊢
      subst rightPair
      have hcomponents :
          (innerEndComponent data web.boundary_wellFormed coloring
            ⟨leftPair, leftInner⟩).2 =
            (innerEndComponent data web.boundary_wellFormed coloring
              ⟨leftPair, rightInner⟩).2 := by
        apply radialComponent_eq_of_common_ambient_edge
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching ⟨leftPair, leftInner⟩)
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching ⟨leftPair, rightInner⟩)
          (crossedCutEdgeOfInnerEnd layers hunique hinnerTouching hcross
            ⟨leftPair, leftInner⟩).1
        · exact crossedCutEdgeOfInnerEnd_mem_path
            layers hunique hinnerTouching hcross ⟨leftPair, leftInner⟩
        · rw [hedge]
          exact crossedCutEdgeOfInnerEnd_mem_path
            layers hunique hinnerTouching hcross ⟨leftPair, rightInner⟩
      have hleft : ComponentContainsInnerStub data coloring
          leftPair.firstColor leftPair.secondColor
          (innerEndComponent data web.boundary_wellFormed coloring
            ⟨leftPair, leftInner⟩).2 leftInner.1 :=
        innerEndComponent_contains_inner data web.boundary_wellFormed coloring
          ⟨leftPair, leftInner⟩
      have hright : ComponentContainsInnerStub data coloring
          leftPair.firstColor leftPair.secondColor
          (innerEndComponent data web.boundary_wellFormed coloring
            ⟨leftPair, leftInner⟩).2 rightInner.1 := by
        rw [hcomponents]
        exact innerEndComponent_contains_inner data web.boundary_wellFormed coloring
          ⟨leftPair, rightInner⟩
      have hinner : leftInner.1 = rightInner.1 :=
        (noColorPairComponentHasTwoDistinctInnerStubs_at_five
          data web.boundary_wellFormed coloring web.tait hinnerTouching)
          leftPair.firstColor leftPair.secondColor leftPair.valid
          (innerEndComponent data web.boundary_wellFormed coloring
            ⟨leftPair, leftInner⟩).2 leftInner.1 rightInner.1 hleft hright
      apply Sigma.ext
      · rfl
      · apply (Subtype.heq_iff_coe_eq (by
          intro inner
          rfl)).2
        exact hinner

/-- A source-local Cell-3 layer cannot meet every radial realization.  There
are twenty oriented inner incidences but only sixteen possible
edge-and-color-pair crossing slots; equality of a slot forces equality of the
support component and then of its unique inner stub. -/
theorem exists_radialPathOfInnerEnd_avoiding_cutEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    ∃ endpoint : InnerEnd data coloring,
      ∀ edge : G.edgeSet,
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            (everyColorPairComponentInnerTouching_of_totallyClosed
              data web.boundary_wellFormed web.connected coloring web.tait
                web.totallyClosed)
            endpoint)).edges →
          edge ∉ layers.cutEdges hunique := by
  classical
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data web.boundary_wellFormed web.connected coloring web.tait web.totallyClosed
  by_contra havoids
  push Not at havoids
  have hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ layers.cutEdges hunique ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges := by
    intro endpoint
    rcases havoids endpoint with ⟨edge, hedgePath, hedgeCut⟩
    exact ⟨edge, hedgeCut, hedgePath⟩
  have hinjective : Function.Injective
      (radialCutSlotOfInnerEnd layers hunique hinnerTouching hcross) :=
    radialCutSlotOfInnerEnd_injective layers hunique hinnerTouching hcross
  have hcard : Fintype.card (InnerEnd data coloring) ≤
      Fintype.card (CutPairSlot layers hunique) :=
    Fintype.card_le_of_injective _ hinjective
  rw [innerEnd_card_eq_twenty data coloring web.tait,
    cutPairSlot_card_eq_sixteen layers hunique] at hcard
  omega

/-- Avoiding the literal four-edge layer wall is exactly avoiding the
value-level primal deletion set consumed by the source-crosscut component
API. -/
theorem ambientRadialPath_avoids_primalCut_of_avoids_cutEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    {first second : Color}
    {component : (colorPairSupportGraph coloring first second).ConnectedComponent}
    (radial : ComponentRadialPath data coloring first second component)
    (havoid : ∀ edge : G.edgeSet,
      edge.1 ∈ (ambientRadialPath radial).edges → edge ∉ layers.cutEdges hunique) :
    ∀ edge : G.edgeSet, edge.1 ∈ (ambientRadialPath radial).edges →
      edge.1 ∉ edgeFinsetValueSet
        ((layers.separatedLocalLayerPair hunique).primalCutEdges
          web.annular.cellulation.rotation) := by
  intro edge hedge hvalue
  rcases (mem_edgeFinsetValueSet_iff
    ((layers.separatedLocalLayerPair hunique).primalCutEdges
      web.annular.cellulation.rotation) edge.1).1 hvalue with
    ⟨other, hother, hvalueEq⟩
  apply havoid other
  · rw [hvalueEq]
    exact hedge
  · change other ∈ layers.cutEdges hunique at hother
    exact hother

/-- The finite radial-escape count supplies the source-mandated comparison
walk: an outer-to-inner radial path that avoids the literal deletion wall.
Together with the already-proved boundary avoidance, it retains the complete
inner hole through the source-local splice. -/
theorem sourceLocalLayerPair_innerHoleFaceKept_of_radialEscape
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hseparated :
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).MatchedCrossingsVertexDisjoint web.annular.cellulation.rotation) :
    HoleFaceKept
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique |>.sourceCrosscutLayerSpliceData web.annular.cellulation.rotation
          (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)
          hseparated)
      web.annular.cellulation.innerHole := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  obtain ⟨endpoint, havoids⟩ :=
    exists_radialPathOfInnerEnd_avoiding_cutEdges layers hunique
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data web.boundary_wellFormed web.connected coloring web.tait web.totallyClosed
  let radial := radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
    hinnerTouching endpoint
  let source : G.Dart := outerBoundaryDart data web.boundary_wellFormed radial.outer
  let root : G.Dart := innerBoundaryDart data web.boundary_wellFormed radial.inner
  let bridge : G.Walk source.fst root.fst :=
    (ambientRadialPath radial).reverse.copy
      (by simpa [source] using radial.finish_eq_outerStub)
      (by simpa [root] using radial.start_eq_innerStub)
  have hsourceFace : dartOrbitFace web.annular.RS source =
      web.annular.cellulation.outerHole := by
    simpa [source] using outerBoundaryDart_on_outerHole
      web.annular web.boundary_wellFormed radial.outer
  have hrootFace : dartOrbitFace web.annular.RS root =
      web.annular.cellulation.innerHole := by
    simpa [root] using innerBoundaryDart_on_innerHole
      web.annular web.boundary_wellFormed radial.inner
  have hsourceSide : source.fst ∈
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).componentSide
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext).component := by
    exact sourceLocalLayerPair_outerHole_vertex_mem_componentSide
      corridor hunique leftInterior hnext source hsourceFace
  have hsource : source.fst ∈
      (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext).component.supp :=
    (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique).mem_componentSide_iff
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext).component
        source.fst).1 hsourceSide
  have hradialAvoid : ∀ edge : G.edgeSet,
      edge.1 ∈ (ambientRadialPath radial).edges →
      edge.1 ∉ edgeFinsetValueSet
        ((layers.separatedLocalLayerPair hunique).primalCutEdges
          web.annular.cellulation.rotation) := by
    apply ambientRadialPath_avoids_primalCut_of_avoids_cutEdges layers hunique radial
    intro edge hedge
    exact havoids edge hedge
  intro dart hdart
  apply SourceCrosscutBoundaryData.face_vertex_mem_componentSide_of_bridge_and_boundary_avoids_primalCut
    web.annular.cellulation.rotation
    ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair hunique)
    (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)
    source root dart bridge hsource
  · intro edge hedge
    apply hradialAvoid edge
    have hedgeReverse : (edge : Sym2 V) ∈ (ambientRadialPath radial).edges.reverse := by
      simpa only [bridge, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_reverse] using hedge
    exact List.mem_reverse.mp hedgeReverse
  · intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).primalCutEdges web.annular.cellulation.rotation) edge.1).1 hvalue with
      ⟨other, hother, hotherValue⟩
    have hotherCut : other ∈ dualWalkCrossingEdges
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).dualLoop := by
      simpa [SeparatedAlignedSimpleDualCrosscuts.primalCutEdges] using hother
    have hedgeCut : edge ∈ dualWalkCrossingEdges
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).dualLoop := by
      simpa [Subtype.ext hotherValue] using hotherCut
    rw [hrootFace] at hedge
    exact (Finset.disjoint_left.mp
      (sourceLocalLayerPair_dualLoopCrossingEdges_disjoint_innerHoleBoundary
        corridor hunique leftInterior hnext) hedgeCut hedge)
  · exact hdart.trans hrootFace.symm

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
