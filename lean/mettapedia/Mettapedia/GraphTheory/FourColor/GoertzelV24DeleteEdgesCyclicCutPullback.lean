import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut

/-!
# L1: pull cyclic cuts back across pure edge deletion

This module isolates the graph-level transport needed at the Addendum-V
opening boundary.  A cyclic cut of `G.deleteEdges removed` is also a cyclic
cut of `G` when every restored edge has both endpoints on the same side of
the cut.  The proof transports the two cycle witnesses along the subgraph
inclusion and maps the finite cut support injectively into the ambient edge
set.

The one-sided variant handles the actual cap-closing use: the deleted graph
supplies only the enclosed cycle, while the restored ambient graph supplies
the complementary cycle.  Thus it does not require the stub-bearing opened
carrier itself to be cyclic on both sides.

The theorem does **not** claim that an abstract frontier tangle comes from a
closed minimal counterexample, and it does not establish the noncrossing
premise for a particular cap opening.  Those are source-formation facts to be
supplied where the opened carrier is constructed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeleteEdgesCyclicCutPullback

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (removed : Set (Sym2 V))

/-- Regard an edge surviving a deletion as its ambient graph edge. -/
def deletedEdgeToAmbientEdge
    (edge : (G.deleteEdges removed).edgeSet) : G.edgeSet :=
  ⟨edge.1, SimpleGraph.edgeSet_mono (G.deleteEdges_le removed) edge.2⟩

@[simp]
theorem deletedEdgeToAmbientEdge_value
    (edge : (G.deleteEdges removed).edgeSet) :
    (deletedEdgeToAmbientEdge removed edge : Sym2 V) = edge.1 :=
  rfl

/-- The inclusion of surviving edges into ambient edges is injective. -/
def deletedEdgeEmbedding :
    (G.deleteEdges removed).edgeSet ↪ G.edgeSet where
  toFun := deletedEdgeToAmbientEdge removed
  inj' := by
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun edge : G.edgeSet => edge.1) heq

/-- An ambient edge outside the deletion support, regarded as a surviving
edge of the deleted graph. -/
def ambientEdgeToDeletedEdge
    (edge : G.edgeSet) (hnotRemoved : edge.1 ∉ removed) :
    (G.deleteEdges removed).edgeSet :=
  ⟨edge.1, by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨edge.2, hnotRemoved⟩⟩

@[simp]
theorem ambientEdgeToDeletedEdge_value
    (edge : G.edgeSet) (hnotRemoved : edge.1 ∉ removed) :
    (ambientEdgeToDeletedEdge removed edge hnotRemoved : Sym2 V) = edge.1 :=
  rfl

/-- A cycle in an edge-deleted graph is still a cycle in the ambient graph,
with the same vertex-side support. -/
theorem hasCycleOnSide_of_deleteEdges
    (side : V → Prop)
    (hcycle : HasCycleOnSide (G.deleteEdges removed) side) :
    HasCycleOnSide G side := by
  rcases hcycle with ⟨root, hroot, cycle, hcycle, hsupport⟩
  let ambientCycle := cycle.mapLe (G.deleteEdges_le removed)
  exact ⟨root, hroot, ambientCycle,
    hcycle.mapLe (G.deleteEdges_le removed), by
      intro vertex hvertex
      apply hsupport vertex
      rw [SimpleGraph.Walk.support_mapLe_eq_support
        (G.deleteEdges_le removed) cycle] at hvertex
      exact hvertex⟩

/-- Pull a one-sided cut realization through pure edge deletion when the
missing complementary cycle is supplied only after the deleted edges are
restored.  This is strictly weaker input than a cyclic cut of the deleted
graph: the opened carrier need not contain a cycle on the complementary
side. -/
def pullbackDeleteEdgesOfAmbientOutsideCycle
    (edgeCut : Finset (G.deleteEdges removed).edgeSet)
    (side : V → Prop)
    (hcut_eq : ∀ edge : (G.deleteEdges removed).edgeSet,
      edge ∈ edgeCut ↔ EdgeCrossesVertexSide (G.deleteEdges removed) side edge)
    (hcard_le_four : edgeCut.card ≤ 4)
    (hinside_cycle : HasCycleOnSide (G.deleteEdges removed) side)
    (houtside_cycle : HasCycleOnSide G (fun vertex => ¬ side vertex))
    (hremovedNoncrossing : ∀ edge : G.edgeSet, edge.1 ∈ removed →
      ¬ EdgeCrossesVertexSide G side edge) :
    SmallCyclicEdgeCut G where
  edgeCut := edgeCut.map (deletedEdgeEmbedding removed)
  side := side
  hcut_eq := by
    intro edge
    constructor
    · intro hedge
      rcases Finset.mem_map.mp hedge with ⟨deletedEdge, hdeleted, heq⟩
      have hcrossDeleted := (hcut_eq deletedEdge).1 hdeleted
      subst edge
      exact hcrossDeleted
    · intro hcross
      have hnotRemoved : edge.1 ∉ removed := by
        intro hremoved
        exact hremovedNoncrossing edge hremoved hcross
      let deletedEdge := ambientEdgeToDeletedEdge removed edge hnotRemoved
      apply Finset.mem_map.mpr
      refine ⟨deletedEdge, (hcut_eq deletedEdge).2 ?_, ?_⟩
      · exact hcross
      · apply Subtype.ext
        rfl
  hcard_le_four := by
    rw [Finset.card_map]
    exact hcard_le_four
  hinside_cycle := hasCycleOnSide_of_deleteEdges removed side hinside_cycle
  houtside_cycle := houtside_cycle

@[simp]
theorem pullbackDeleteEdgesOfAmbientOutsideCycle_edgeCut_card
    (edgeCut : Finset (G.deleteEdges removed).edgeSet)
    (side : V → Prop)
    (hcut_eq : ∀ edge : (G.deleteEdges removed).edgeSet,
      edge ∈ edgeCut ↔ EdgeCrossesVertexSide (G.deleteEdges removed) side edge)
    (hcard_le_four : edgeCut.card ≤ 4)
    (hinside_cycle : HasCycleOnSide (G.deleteEdges removed) side)
    (houtside_cycle : HasCycleOnSide G (fun vertex => ¬ side vertex))
    (hremovedNoncrossing : ∀ edge : G.edgeSet, edge.1 ∈ removed →
      ¬ EdgeCrossesVertexSide G side edge) :
    (pullbackDeleteEdgesOfAmbientOutsideCycle removed edgeCut side hcut_eq
      hcard_le_four hinside_cycle houtside_cycle
      hremovedNoncrossing).edgeCut.card = edgeCut.card := by
  simp [pullbackDeleteEdgesOfAmbientOutsideCycle]

/-- Pull a bundled cyclic cut back through pure edge deletion.  The
noncrossing premise says precisely that adding the deleted edges back does
not enlarge the cut. -/
def pullbackDeleteEdges
    (cut : SmallCyclicEdgeCut (G.deleteEdges removed))
    (hremovedNoncrossing : ∀ edge : G.edgeSet, edge.1 ∈ removed →
      ¬ EdgeCrossesVertexSide G cut.side edge) :
    SmallCyclicEdgeCut G where
  edgeCut := cut.edgeCut.map (deletedEdgeEmbedding removed)
  side := cut.side
  hcut_eq := by
    intro edge
    constructor
    · intro hedge
      rcases Finset.mem_map.mp hedge with ⟨deletedEdge, hdeleted, heq⟩
      have hcrossDeleted := (cut.hcut_eq deletedEdge).1 hdeleted
      subst edge
      exact hcrossDeleted
    · intro hcross
      have hnotRemoved : edge.1 ∉ removed := by
        intro hremoved
        exact hremovedNoncrossing edge hremoved hcross
      let deletedEdge := ambientEdgeToDeletedEdge removed edge hnotRemoved
      apply Finset.mem_map.mpr
      refine ⟨deletedEdge, (cut.hcut_eq deletedEdge).2 ?_, ?_⟩
      · exact hcross
      · apply Subtype.ext
        rfl
  hcard_le_four := by
    rw [Finset.card_map]
    exact cut.hcard_le_four
  hinside_cycle := hasCycleOnSide_of_deleteEdges removed cut.side cut.hinside_cycle
  houtside_cycle := hasCycleOnSide_of_deleteEdges removed
    (fun vertex => ¬ cut.side vertex) cut.houtside_cycle

@[simp]
theorem pullbackDeleteEdges_edgeCut_card
    (cut : SmallCyclicEdgeCut (G.deleteEdges removed))
    (hremovedNoncrossing : ∀ edge : G.edgeSet, edge.1 ∈ removed →
      ¬ EdgeCrossesVertexSide G cut.side edge) :
    (pullbackDeleteEdges removed cut hremovedNoncrossing).edgeCut.card =
      cut.edgeCut.card := by
  simp [pullbackDeleteEdges]

/-- Ambient cyclic connectivity bounds every cyclic cut of an edge-deleted
graph whose restored edges stay on one side.  This is the consumer form used
at formation sites: no global connectivity claim about the opened carrier is
needed. -/
theorem card_ge_of_ambient_cyclicEdgeConnectivityAtLeast
    {k : Nat} (hcyclic : CyclicEdgeConnectivityAtLeast G k)
    (cut : SmallCyclicEdgeCut (G.deleteEdges removed))
    (hremovedNoncrossing : ∀ edge : G.edgeSet, edge.1 ∈ removed →
      ¬ EdgeCrossesVertexSide G cut.side edge) :
    k ≤ cut.edgeCut.card := by
  rw [← pullbackDeleteEdges_edgeCut_card removed cut hremovedNoncrossing]
  exact hcyclic (pullbackDeleteEdges removed cut hremovedNoncrossing)

end GoertzelV24DeleteEdgesCyclicCutPullback

end Mettapedia.GraphTheory.FourColor
