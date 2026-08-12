import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Light bridge from graph-backed rotation systems to simple graphs

This module contains only the generic identifications needed to move between
a finite simple graph and its dart rotation system.  Keeping them here avoids
pulling the minimal-counterexample stack into consumers that need only local
graph-backed incidence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationVertexCutProfile

open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Rotation-system endpoints for a finite simple graph are exactly membership
in the underlying unordered graph edge. -/
theorem mem_simpleGraphRotationSystem_endpoints_iff
    (data : Data G) (edge : G.edgeSet) (vertex : V) :
    vertex ∈ data.toRotationSystem.endpoints edge ↔
      vertex ∈ (edge : Sym2 V) := by
  rw [RotationSystem.mem_endpoints_iff]
  constructor
  · rintro ⟨dart, hdart, hvert⟩
    have hedgeSubtype :
        data.toRotationSystem.edgeOf dart = edge :=
      (data.toRotationSystem.mem_dartsOn).1 hdart
    have hedge : dart.edge = (edge : Sym2 V) :=
      congrArg Subtype.val hedgeSubtype
    change dart.fst = vertex at hvert
    have hfst : dart.fst ∈ dart.edge := by
      simp [SimpleGraph.Dart.edge]
    rw [hedge] at hfst
    simpa [hvert] using hfst
  · intro hvertex
    let other := Sym2.Mem.other' hvertex
    have hadj : G.Adj vertex other := by
      rw [← SimpleGraph.mem_edgeSet]
      rw [Sym2.other_spec' hvertex]
      exact edge.property
    let dart : G.Dart := ⟨(vertex, other), hadj⟩
    refine ⟨dart, ?_, rfl⟩
    rw [data.toRotationSystem.mem_dartsOn]
    apply Subtype.ext
    change s(vertex, other) = (edge : Sym2 V)
    exact Sym2.other_spec' hvertex

end GoertzelV24RotationVertexCutProfile

namespace GoertzelV24SimpleGraphTaitBridge

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedEdgeTrail
open GoertzelV24RotationVertexCutProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- For rotation data built from a finite simple graph, the faithful
rotation-system edge-adjacency graph is exactly the ordinary line graph. -/
theorem toRotationSystem_edgeAdjacencyGraph_eq_lineGraph
    (data : Data G) :
    data.toRotationSystem.edgeAdjacencyGraph = G.lineGraph := by
  ext first second
  rw [data.toRotationSystem.edgeAdjacencyGraph_adj_iff,
    SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, vertex, hfirst, hsecond⟩
    exact ⟨hne, vertex,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data first vertex).1 hfirst,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data second vertex).1 hsecond⟩
  · rintro ⟨hne, vertex, hfirst, hsecond⟩
    exact ⟨hne, vertex,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data first vertex).2 hfirst,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data second vertex).2 hsecond⟩

/-- Rotation-system cubicity of graph-backed data is the exact local
three-incident-edge hypothesis used by the deleted-edge Trail bridge. -/
theorem incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic) :
    ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 := by
  intro vertex
  rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
  exact (data.toRotationSystem_isCubic_iff.mp hcubic) vertex

end

end GoertzelV24SimpleGraphTaitBridge

end Mettapedia.GraphTheory.FourColor
