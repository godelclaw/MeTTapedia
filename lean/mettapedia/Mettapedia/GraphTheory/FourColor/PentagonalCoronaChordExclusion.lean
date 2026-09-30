import Mettapedia.GraphTheory.FourColor.PentagonalCoronaBoundary
import Mettapedia.GraphTheory.FourColor.CyclicFiveBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize
import Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound

/-!
# Minimality excludes additional chords in the face-derived corona

An extra chord would consume two of the six outward darts. The retained
sixteen vertices contain the central cycle. With at least three vertices
outside, cubicity makes the resulting cut cyclic, contradicting cyclic
five-edge connectivity. Minimality supplies both the connectivity and an
ambient vertex bound of twenty. Distinctness of the traced vertices is
still an explicit hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

open _root_.SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FourEdgeCutGluing
open GoertzelV24MinimalFaceSize GoertzelV24CubicSmallBoundaryCycle

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaChordEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaChordEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

/-- The traced outer cycle is induced in any sufficiently large cubic graph
with the stated local face periods and cyclic connectivity. -/
theorem outerInduced_of_cyclicallyFive
    (hC : Cubic3 rotation.toRotationSystem)
    (hroot : (rotation.toRotationSystem.phi ^ 5) root = root)
    (hn : NeighborPeriods rotation root)
    (hv : Function.Injective (tracedVertex rotation root))
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hsize : 19 ≤ Fintype.card V) : OuterInduced rotation root := by
  classical
  have hside := card_tracedSide rotation root hv
  have hcompl := Fintype.card_subtype_compl (tracedSide rotation root)
  have hfive := CyclicFiveBoundary.five_le_crossing_card hcubic hcyclic
    (tracedSide rotation root) (tracedSide_hasCycle rotation root hroot hv hcubic) (by omega)
  intro i j ha
  by_contra hnbr
  have hnot := not_or.mp hnbr
  have hfour := crossing_card_le_four_of_chord rotation root hC hroot hn hv hcubic
    ha hnot.1 hnot.2
  omega

/-- Vertex minimality discharges the outer-inducedness premise; only the
sixteen traced vertices' distinctness remains as a local geometric input. -/
theorem outerInduced_of_minimality
    (hfaces : FaceLengths rotation root)
    (hv : Function.Injective (tracedVertex rotation root))
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    OuterInduced rotation root := by
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic) v)
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem minimal.spherical
    (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
  exact outerInduced_of_cyclicallyFive rotation root
    (cubic3_of rotation.toRotationSystem minimal.spherical.cubic minimal.vertexRotationCyclic)
    (hfaces.central_period rotation root) (hfaces.neighbour_periods rotation root) hv hcubic
    (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample rotation minimal) (by omega)

end
end Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry
