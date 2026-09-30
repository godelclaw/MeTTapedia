import Mettapedia.GraphTheory.FourColor.PentagonalCoronaImmersion
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree

/-!
# Noncollision of the face-derived pentagonal corona

The finite diagram's separation theorem is interpreted in the original
graph. Cyclic five-edge connectivity and more than four vertices imply
triangle-freeness; alternatively, vertex minimality supplies it directly.
The sixteen traced vertices are therefore distinct, without assuming a
cycle frame, a patch isomorphism, or distinct facial boundary vertices.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

open _root_.SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open PartialCubicDartSeparation GoertzelV24MinimalTriangleFree
open GoertzelV24TwoEdgeCutMinimality GoertzelV24CubicSmallBoundaryCycle

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaNoncollisionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaNoncollisionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G)

include rotation in
/-- The only cubic cyclically five-edge-connected simple graph that can
contain a triangle has four vertices. -/
theorem triangleFree_of_cyclicallyFive_of_four_lt_card
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hsize : 4 < Fintype.card V) : Realization.TriangleFree (G := G) := by
  intro a b c hab hbc hca
  have hcomplement := natCard_complement_triangle_eq_one_of_cyclicallyFive
    rotation (fun v => (degree_instance_independent v _ _).trans (hcubic v))
    hcyclic hab hca.symm hbc
  have hfour := fintype_card_eq_four_of_triangle_complement_natCard_eq_one
    hab.ne hca.symm.ne hbc.ne hcomplement
  omega

variable (root : G.Dart)

/-- Local face periods and the ambient cyclic-connectivity/size hypotheses
force noncollision of every traced position. -/
theorem tracedVertex_injective_of_cyclicallyFive
    (hC : Cubic3 rotation.toRotationSystem)
    (hroot : (rotation.toRotationSystem.phi ^ 5) root = root)
    (hn : NeighborPeriods rotation root)
    (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hsize : 4 < Fintype.card V) :
    Function.Injective (tracedVertex rotation root) :=
  tracedVertex_injective_of_triangleFree rotation root hC hroot hn
    (triangleFree_of_cyclicallyFive_of_four_lt_card rotation hcubic hcyclic hsize)

/-- In a vertex-minimal counterexample the actual six face lengths suffice:
distinctness of the traced vertices is a conclusion, not an input. -/
theorem tracedVertex_injective_of_minimality
    (hfaces : FaceLengths rotation root)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    Function.Injective (tracedVertex rotation root) := by
  apply tracedVertex_injective_of_triangleFree rotation root
    (cubic3_of rotation.toRotationSystem minimal.spherical.cubic minimal.vertexRotationCyclic)
    (hfaces.central_period rotation root) (hfaces.neighbour_periods rotation root)
  intro a b c hab hbc hca
  exact no_common_neighbor_of_vertexMinimalTaitCounterexample rotation minimal hab c hca.symm hbc

end
end Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry
