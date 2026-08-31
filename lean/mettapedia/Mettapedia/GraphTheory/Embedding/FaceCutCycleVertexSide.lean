import Mettapedia.GraphTheory.Embedding.FaceCutCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport

/-!
# Vertex sides induced by an exact cut around a cycle

An exact face cut supported by a simple primal cycle separates facial
orbits.  For graph surgery one instead needs a predicate on vertices.  The
canonical conversion fills the cycle itself into one side and classifies an
off-cycle vertex by the common face label of its incident non-cycle darts.

This file proves the local coherence needed by that conversion.  In
particular, an edge whose endpoints both lie off the cycle cannot change the
filled vertex side.  Consequently any edge cut induced by the filled side is
supported at the cycle.  Cardinality and cyclic-side witnesses are separate
graph-theoretic consequences.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace ExactFaceCut

/-- The vertex side obtained by filling a primal cycle into one facial side
of its exact binary cut.  Off the cycle, membership is witnessed by any
incident dart outside the cycle carrying the selected face label. -/
def filledCycleSide
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (vertex : V) : Prop :=
  vertex ∈ cycle.support ∨
    ∃ dart : data.toRotationSystem.D,
      data.toRotationSystem.vertOf dart = vertex ∧
        (data.toRotationSystem.edgeOf dart).1 ∉ cycle.edges ∧
          cut.label (dartOrbitFace data.toRotationSystem dart) = selected

/-- Every vertex of the bounding cycle belongs to the filled side. -/
theorem mem_filledCycleSide_of_mem_support
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) {vertex : V} (hvertex : vertex ∈ cycle.support) :
    cut.filledCycleSide data cycle selected vertex :=
  Or.inl hvertex

/-- An edge based at a vertex outside a walk cannot occur in the walk. -/
theorem edge_not_mem_cycle_of_vert_not_mem_support
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (dart : data.toRotationSystem.D)
    (hvertex : data.toRotationSystem.vertOf dart ∉ cycle.support) :
    (data.toRotationSystem.edgeOf dart).1 ∉ cycle.edges := by
  intro hedge
  apply hvertex
  simpa only [Data.toRotationSystem_vertOf,
    Data.toRotationSystem_edgeOf] using
      cycle.fst_mem_support_of_mem_edges hedge

/-- At a vertex outside the cycle, all incident dart faces carry the same
exact-cut label.  Every incident edge avoids the selected cycle support, so
cyclic vertex rotation transports the label between arbitrary darts. -/
theorem label_eq_of_same_vertex_of_not_mem_cycle_support
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    {first second : data.toRotationSystem.D}
    (hbase : data.toRotationSystem.vertOf second =
      data.toRotationSystem.vertOf first)
    (hoff : data.toRotationSystem.vertOf first ∉ cycle.support) :
    cut.label (dartOrbitFace data.toRotationSystem first) =
      cut.label (dartOrbitFace data.toRotationSystem second) := by
  apply labels_eq_of_same_vertex_of_all_edges_not_cut
    data.toRotationSystem hrotation cut.label
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) cut.separates
      first second hbase
  intro dart hdart
  apply edge_not_mem_cycle_of_vert_not_mem_support data cycle dart
  simpa only [hdart] using hoff

/-- At an off-cycle vertex, any chosen incident dart reads the filled-side
membership, because all incident dart faces have the same cut label. -/
theorem filledCycleSide_iff_label_of_not_mem_support
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (dart : data.toRotationSystem.D)
    (hoff : data.toRotationSystem.vertOf dart ∉ cycle.support) :
    cut.filledCycleSide data cycle selected
        (data.toRotationSystem.vertOf dart) ↔
      cut.label (dartOrbitFace data.toRotationSystem dart) = selected := by
  constructor
  · rintro (hcycle | ⟨incident, hincident, _haway, hselected⟩)
    · exact (hoff hcycle).elim
    · have hlabels := label_eq_of_same_vertex_of_not_mem_cycle_support
        data hrotation cycle cut hincident hoff
      exact hlabels.trans hselected
  · intro hselected
    exact Or.inr ⟨dart, rfl,
      edge_not_mem_cycle_of_vert_not_mem_support data cycle dart hoff,
      hselected⟩

/-- A non-cycle edge whose endpoints both lie off the cycle preserves the
filled vertex side.  This is the local separator statement needed to show
that every crossing edge of the induced push-off cut is incident to the
cycle. -/
theorem filledCycleSide_iff_of_edge_endpoints_not_mem_support
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (dart : data.toRotationSystem.D)
    (hfirst : data.toRotationSystem.vertOf dart ∉ cycle.support)
    (hsecond : data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha dart) ∉ cycle.support) :
    cut.filledCycleSide data cycle selected
        (data.toRotationSystem.vertOf dart) ↔
      cut.filledCycleSide data cycle selected
        (data.toRotationSystem.vertOf
          (data.toRotationSystem.alpha dart)) := by
  rw [cut.filledCycleSide_iff_label_of_not_mem_support
      data hrotation cycle selected dart hfirst,
    cut.filledCycleSide_iff_label_of_not_mem_support
      data hrotation cycle selected (data.toRotationSystem.alpha dart)
        hsecond]
  have haway :
      (data.toRotationSystem.edgeOf dart).1 ∉ cycle.edges :=
    edge_not_mem_cycle_of_vert_not_mem_support data cycle dart hfirst
  rw [cut.label_eq_opposite_of_not_selected dart haway]

end ExactFaceCut

end

end Mettapedia.GraphTheory.Embedding
