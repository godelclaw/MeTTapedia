import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorColorTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileConnectivityUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceUpdate

/-!
# One geometric coverage premise for terminal-profile transfer

The source Cell-3 profile updates tracked connectivity and capped facial
progress together.  The two graph-composition lemmas already isolate their
respective coverage conditions; this file derives both from one literal
edge-adjacency condition on the old prefix and the adjoining Cell.

Thus a concrete corridor seam cannot justify the connectivity coordinate and
the face coordinate using incompatible decompositions.  No determinism is
introduced: this remains a premise for the relational transfer law.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileRegionalCoverage

open GoertzelV24FaceDualConnectedness
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexFaceRungType
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileFaceUpdate

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Every ambient edge adjacency retained by the union of an old prefix and
one Cell is already wholly retained by one of the two pieces.  For an
edge-cut seam this says that the common cut edges, rather than a hidden
cross-piece vertex adjacency, carry all communication between the pieces. -/
def RegionalEdgeAdjacencyCovered
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E) : Prop :=
  ∀ {left right : E},
    RS.edgeAdjacencyGraph.Adj left right →
    left ∈ leftRegion ∪ rightRegion →
    right ∈ leftRegion ∪ rightRegion →
    (left ∈ leftRegion ∧ right ∈ leftRegion) ∨
      (left ∈ rightRegion ∧ right ∈ rightRegion)

/-- Consecutive occurrences on an actual face cycle carry adjacent underlying
rotation-system edges. -/
theorem edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    {left right : Fin (RS.faceOrbit root).card}
    (hadj : (faceCyclePositionGraph RS root).Adj left right) :
    RS.edgeAdjacencyGraph.Adj
      (faceCycleEdge RS root left) (faceCycleEdge RS root right) := by
  rcases hadj.2 with hforward | hbackward
  · have hcorner := cornerEdges_pairwise_ne_and_incident RS hcubic hrotation
      (faceCycleDart RS root left)
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    · simpa only [faceCycleEdge, hforward] using hcorner.1
    · simpa only [faceCycleEdge] using hcorner.2.2.2.1
    · simpa only [faceCycleEdge, hforward] using hcorner.2.2.2.2.1
  · have hcorner := cornerEdges_pairwise_ne_and_incident RS hcubic hrotation
      (faceCycleDart RS root right)
    apply SimpleGraph.Adj.symm
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    · simpa only [faceCycleEdge, hbackward] using hcorner.1
    · simpa only [faceCycleEdge] using hcorner.2.2.2.1
    · simpa only [faceCycleEdge, hbackward] using hcorner.2.2.2.2.1

/-- The common uncolored seam-coverage fact supplies the tracked-connectivity
coverage premise for every coloring and every tracked color pair. -/
theorem regionalTrackedAdjacencyCovered_of_edgeAdjacencyCovered
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (hcovered : RegionalEdgeAdjacencyCovered RS leftRegion rightRegion)
    (C : E → Color) (a b : Color) :
    RegionalTrackedAdjacencyCovered RS leftRegion rightRegion C a b := by
  intro left right hadj hleft hright
  exact hcovered hadj.1 hleft hright

/-- The same seam-coverage fact supplies occurrence-sensitive coverage on
every face cycle.  Cubicity and cyclic vertex rotation are used only to turn
one facial step into an adjacency of its two underlying edges. -/
theorem regionalFaceAdjacencyCovered_of_edgeAdjacencyCovered
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (leftRegion rightRegion : Finset E)
    (hcovered : RegionalEdgeAdjacencyCovered RS leftRegion rightRegion)
    (root : RS.D) :
    RegionalFaceAdjacencyCovered RS root leftRegion rightRegion := by
  intro left right hadj hleft hright
  exact hcovered
    (edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
      RS hcubic hrotation root hadj)
    hleft hright

end

end GoertzelV24TerminalProfileRegionalCoverage

end Mettapedia.GraphTheory.FourColor
