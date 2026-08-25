import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerRadialEscape

/-!
# Radial escape from a finite edge cut

The source-local Cell--3 escape theorem counts twenty oriented inner Tait
incidences against four color-pair slots for every deleted edge.  This module
extracts the same argument for an arbitrary finite edge support.  Any support
of cardinality strictly below five therefore misses one literal radial path
from the inner boundary to the outer boundary.

This is a generic counting lemma in the closed-web carrier.  It does not say
that a chosen cut is a dual separator, classify either deletion side, or
transport closed minimality through an opening.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComponentCensus
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebTotalClosure
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance closedWebFiniteCutRadialEscapeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- One possible crossing of a finite cut, tagged by an oriented Tait pair
which selects the crossing edge's color. -/
abbrev FiniteCutPairSlot
    (coloring : G.EdgeColoring Color)
    (removed : Finset G.edgeSet) :=
  Sigma fun edge : {candidate : G.edgeSet // candidate ∈ removed} =>
    {pair : TaitPairIndex // pair.Selects (coloring edge.1)}

/-- A cut with `m` edges has exactly `4m` oriented edge-and-color-pair
crossing slots. -/
theorem finiteCutPairSlot_card_eq_four_mul
    (coloring : G.EdgeColoring Color)
    (htait : IsTaitEdgeColoring G coloring) (removed : Finset G.edgeSet) :
    Fintype.card (FiniteCutPairSlot coloring removed) = removed.card * 4 := by
  calc
    Fintype.card (FiniteCutPairSlot coloring removed) =
        ∑ edge : {candidate : G.edgeSet // candidate ∈ removed},
          Fintype.card {pair : TaitPairIndex //
            pair.Selects (coloring edge.1)} :=
      Fintype.card_sigma
    _ = ∑ _edge : {candidate : G.edgeSet // candidate ∈ removed}, 4 := by
      apply Finset.sum_congr rfl
      intro edge _
      exact TaitPairIndex.selected_card_eq_four _ (htait edge.1)
    _ = removed.card * 4 := by simp

/-- Under the contrary assumption that every radial path crosses the finite
cut, choose one actual crossed edge for every oriented inner incidence. -/
noncomputable def crossedFiniteCutEdgeOfInnerEnd
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} (removed : Finset G.edgeSet)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ removed ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges)
    (endpoint : InnerEnd data coloring) :
    {edge : G.edgeSet // edge ∈ removed} :=
  ⟨Classical.choose (hcross endpoint),
    (Classical.choose_spec (hcross endpoint)).1⟩

/-- The chosen finite-cut edge occurs on its corresponding radial path. -/
theorem crossedFiniteCutEdgeOfInnerEnd_mem_path
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} (removed : Finset G.edgeSet)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ removed ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges)
    (endpoint : InnerEnd data coloring) :
    (crossedFiniteCutEdgeOfInnerEnd (web := web)
      removed hinnerTouching hcross endpoint).1.1 ∈
      (ambientRadialPath
        (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
          hinnerTouching endpoint)).edges := by
  exact (Classical.choose_spec (hcross endpoint)).2

/-- Send an oriented inner incidence to its chosen crossing edge and its own
oriented Tait-pair index. -/
noncomputable def finiteCutSlotOfInnerEnd
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} (removed : Finset G.edgeSet)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ removed ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges)
    (endpoint : InnerEnd data coloring) : FiniteCutPairSlot coloring removed :=
  ⟨crossedFiniteCutEdgeOfInnerEnd (web := web)
      removed hinnerTouching hcross endpoint,
    ⟨endpoint.1,
      radialPathOfInnerEnd_edge_selected
        data web.boundary_wellFormed coloring web.tait hinnerTouching endpoint
        (crossedFiniteCutEdgeOfInnerEnd (web := web)
          removed hinnerTouching hcross endpoint).1
        (crossedFiniteCutEdgeOfInnerEnd_mem_path (web := web)
          removed hinnerTouching hcross endpoint)⟩⟩

/-- Equal finite-cut slots force equal radial components and then equal inner
endpoints. -/
theorem finiteCutSlotOfInnerEnd_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} (removed : Finset G.edgeSet)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    (hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ removed ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges) :
    Function.Injective
      (finiteCutSlotOfInnerEnd (web := web)
        removed hinnerTouching hcross) := by
  intro left right heq
  have hpair : left.1 = right.1 :=
    congrArg (fun slot : FiniteCutPairSlot coloring removed => slot.2.1) heq
  have hedge :
      (crossedFiniteCutEdgeOfInnerEnd (web := web)
        removed hinnerTouching hcross left).1 =
        (crossedFiniteCutEdgeOfInnerEnd (web := web)
          removed hinnerTouching hcross right).1 :=
    congrArg (fun slot : FiniteCutPairSlot coloring removed => slot.1.1) heq
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
          (crossedFiniteCutEdgeOfInnerEnd (web := web) removed hinnerTouching hcross
            ⟨leftPair, leftInner⟩).1
        · exact crossedFiniteCutEdgeOfInnerEnd_mem_path (web := web)
            removed hinnerTouching hcross ⟨leftPair, leftInner⟩
        · rw [hedge]
          exact crossedFiniteCutEdgeOfInnerEnd_mem_path (web := web)
            removed hinnerTouching hcross ⟨leftPair, rightInner⟩
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
        exact innerEndComponent_contains_inner
          data web.boundary_wellFormed coloring ⟨leftPair, rightInner⟩
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

/-- Every finite edge cut with fewer than five edges misses one actual radial
path from an inner stub to an outer stub.  This is the strict finite-capacity
form of the source's radial-escape argument. -/
theorem exists_radialPathOfInnerEnd_avoiding_finiteCut
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} (removed : Finset G.edgeSet)
    (hcard : removed.card < 5) :
    ∃ endpoint : InnerEnd data coloring,
      ∀ edge : G.edgeSet,
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            (everyColorPairComponentInnerTouching_of_totallyClosed
              data web.boundary_wellFormed web.connected coloring web.tait
                web.totallyClosed)
            endpoint)).edges →
          edge ∉ removed := by
  classical
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data web.boundary_wellFormed web.connected coloring web.tait web.totallyClosed
  by_contra havoids
  push Not at havoids
  have hcross : ∀ endpoint : InnerEnd data coloring,
      ∃ edge : G.edgeSet, edge ∈ removed ∧
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            hinnerTouching endpoint)).edges := by
    intro endpoint
    rcases havoids endpoint with ⟨edge, hedgePath, hedgeCut⟩
    exact ⟨edge, hedgeCut, hedgePath⟩
  have hinjective : Function.Injective
      (finiteCutSlotOfInnerEnd (web := web) removed hinnerTouching hcross) :=
    finiteCutSlotOfInnerEnd_injective (web := web)
      removed hinnerTouching hcross
  have hsize : Fintype.card (InnerEnd data coloring) ≤
      Fintype.card (FiniteCutPairSlot coloring removed) :=
    Fintype.card_le_of_injective _ hinjective
  rw [innerEnd_card_eq_twenty data coloring web.tait,
    finiteCutPairSlot_card_eq_four_mul coloring web.tait removed] at hsize
  omega

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
