import Mathlib.Data.Fintype.Card
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningOpenRegionComparison

/-!
# Exact carrier counts for the literal two-pentagon opening

The toolchain presentation keeps the original vertex carrier and removes the
five cycle edges of each of two vertex-disjoint pentagon caps.  This module
proves that numerical statement and transports it to the simple graph backing
of the manuscript-side opening.

These are C-3 Euler ingredients, not an Euler theorem: no face count,
connectedness, or annular cellulation is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapOpeningCounts

open SimpleGraph
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24PentagonCapOpening
open GoertzelV24TwoPentagonCapOpening

attribute [-instance] GoertzelV24OpenRegionRotation.retainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  G.fintypeEdgeSet

namespace PentagonCap

/-- A literal pentagon cap has exactly five cycle edges. -/
@[simp] theorem cycleSupport_card (cap : PentagonCap G) :
    cap.cycleSupport.card = 5 := by
  simp [GoertzelV24PentagonCapOpening.PentagonCap.cycleSupport]

end PentagonCap

namespace PentagonCapPair

local instance openGraphDecidableRel (caps : PentagonCapPair G) :
    DecidableRel caps.openGraph.Adj :=
  Classical.decRel _

local instance openGraphEdgeSetFintype (caps : PentagonCapPair G) :
    Fintype caps.openGraph.edgeSet :=
  caps.openGraph.fintypeEdgeSet

/-- Vertex-disjoint cap supports force their two cycle-edge families to be
disjoint as ambient graph edges. -/
theorem inner_cycleSupport_disjoint_outer
    (caps : PentagonCapPair G) :
    Disjoint caps.inner.cycleSupport caps.outer.cycleSupport := by
  rw [Finset.disjoint_left]
  intro edge hinner houter
  rcases Finset.mem_map.mp hinner with ⟨innerStep, -, hinnerEdge⟩
  rcases Finset.mem_map.mp houter with ⟨outerStep, -, houterEdge⟩
  have hedgeEq : caps.inner.cycleEdge innerStep =
      caps.outer.cycleEdge outerStep := hinnerEdge.trans houterEdge.symm
  obtain ⟨⟨first, second⟩, hrep⟩ := Quot.exists_rep edge.1
  have hfirstEdge : first ∈ edge.1 := by
    rw [← hrep]
    exact Sym2.mem_mk_left first second
  have hfirstInner : first ∈ (caps.inner.cycleEdge innerStep).1 := by
    rw [hinnerEdge]
    exact hfirstEdge
  have hfirstOuter : first ∈ (caps.outer.cycleEdge outerStep).1 := by
    rw [← hedgeEq]
    exact hfirstInner
  rcases caps.inner.cycleEdge_endpoint_eq_vertex innerStep first hfirstInner with
    ⟨innerVertex, hinnerVertex⟩
  rcases caps.outer.cycleEdge_endpoint_eq_vertex outerStep first hfirstOuter with
    ⟨outerVertex, houterVertex⟩
  exact (Finset.disjoint_left.mp caps.vertexSupport_disjoint)
    ((caps.inner.mem_vertexSupport_iff _).mpr
      ⟨innerVertex, hinnerVertex⟩)
    ((caps.outer.mem_vertexSupport_iff _).mpr
      ⟨outerVertex, houterVertex⟩)

/-- The simultaneous opening removes exactly ten distinct cycle edges. -/
@[simp] theorem cycleSupport_card (caps : PentagonCapPair G) :
    caps.cycleSupport.card = 10 := by
  change (caps.inner.cycleSupport ∪ caps.outer.cycleSupport).card = 10
  calc
    _ = caps.inner.cycleSupport.card + caps.outer.cycleSupport.card :=
      Finset.card_union_of_disjoint (inner_cycleSupport_disjoint_outer caps)
    _ = 10 := by simp

/-- Edges of the literal opening are exactly ambient edges outside the ten
named cycle edges. -/
def openEdgeEquivComplement (caps : PentagonCapPair G) :
    caps.openGraph.edgeSet ≃ {edge : G.edgeSet // edge ∉ caps.cycleSupport} where
  toFun := fun edge =>
    ⟨⟨edge.1, caps.openGraph_edgeSet_subset edge.2⟩, by
      intro hremoved
      have hvalue : edge.1 ∈ edgeFinsetValueSet caps.cycleSupport :=
        (mem_edgeFinsetValueSet_iff caps.cycleSupport edge.1).mpr
          ⟨⟨edge.1, caps.openGraph_edgeSet_subset edge.2⟩, hremoved, rfl⟩
      exact ((caps.mem_openGraph_edgeSet_iff edge.1
        (caps.openGraph_edgeSet_subset edge.2)).mp edge.2) hvalue⟩
  invFun := fun edge =>
    ⟨edge.1.1, (caps.mem_openGraph_edgeSet_iff edge.1.1 edge.1.2).mpr (by
      intro hvalue
      rcases (mem_edgeFinsetValueSet_iff caps.cycleSupport edge.1.1).mp hvalue with
        ⟨removed, hremoved, hremovedValue⟩
      exact edge.2 (by
        have hremovedEq : removed = edge.1 := Subtype.ext hremovedValue
        simpa [← hremovedEq] using hremoved))⟩
  left_inv := by
    intro edge
    apply Subtype.ext
    rfl
  right_inv := by
    intro edge
    apply Subtype.ext
    rfl

/-- Edge deletion is exact: surviving edges plus the ten removed edges recover
the ambient edge count. -/
theorem card_openGraph_edgeSet_add_cycleSupport
    (caps : PentagonCapPair G) :
    Fintype.card caps.openGraph.edgeSet + caps.cycleSupport.card =
      Fintype.card G.edgeSet := by
  classical
  have hcomplement :
      Fintype.card {edge : G.edgeSet // edge ∉ caps.cycleSupport} =
        Fintype.card G.edgeSet -
          Fintype.card {edge : G.edgeSet // edge ∈ caps.cycleSupport} :=
    Fintype.card_subtype_compl (fun edge : G.edgeSet =>
      edge ∈ caps.cycleSupport)
  have hremoved :
      Fintype.card {edge : G.edgeSet // edge ∈ caps.cycleSupport} =
        caps.cycleSupport.card := by
    simpa using Fintype.card_subtype
      (fun edge : G.edgeSet => edge ∈ caps.cycleSupport)
  have hsurviving : Fintype.card caps.openGraph.edgeSet =
      Fintype.card G.edgeSet - caps.cycleSupport.card := by
    rw [Fintype.card_congr (openEdgeEquivComplement caps),
      hcomplement, hremoved]
  have hle : caps.cycleSupport.card ≤ Fintype.card G.edgeSet := by
    simpa using Finset.card_le_univ caps.cycleSupport
  omega

/-- Numerical form specialized to the two five-edge cap cycles. -/
theorem card_openGraph_edgeSet_add_ten (caps : PentagonCapPair G) :
    Fintype.card caps.openGraph.edgeSet + 10 = Fintype.card G.edgeSet := by
  simpa using card_openGraph_edgeSet_add_cycleSupport caps

/-- The graph-backed manuscript opening has the same number of vertices as
the ambient graph: ten deleted cap vertices are replaced by ten fresh stubs. -/
theorem card_openPrimalGraph_vertices
    (data : SimpleGraphDartRotation.Data G) (caps : PentagonCapPair G)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport)) :
    Fintype.card
        (GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem
          (keep caps.deletedVertexSupport)) =
      Fintype.card V := by
  exact Fintype.card_congr
    (caps.openingGraphIsoOpenPrimalGraph data root).toEquiv.symm

/-- The same exact ten-edge loss holds on the graph-backed manuscript carrier. -/
theorem card_openPrimalGraph_edgeSet_add_ten
    (data : SimpleGraphDartRotation.Data G) (caps : PentagonCapPair G)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport)) :
    Fintype.card
        (PrimalGraph data.toRotationSystem
          (keep caps.deletedVertexSupport) root).edgeSet + 10 =
      Fintype.card G.edgeSet := by
  rw [← Fintype.card_congr
    (caps.openingGraphIsoOpenPrimalGraph data root).mapEdgeSet]
  exact card_openGraph_edgeSet_add_ten caps

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpeningCounts

end Mettapedia.GraphTheory.FourColor
