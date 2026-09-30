import MettapediaFourColor.PentagonalLobeRecognition
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaIncidence

/-!
# Strict reduction of a corona recognized from its faces

The input consists of actual face sizes, distinctness of the vertices
traced from them, and absence of outer chords. Face traversal constructs
both cycles and all outer rotations before applying the existing repair.
The whole graph loses twelve vertices, including the four introduced by
the replacement. Exterior colouring choices may be repaired jointly.
-/

namespace FourColor.PentagonalLobePatch.Tangle.Corona

open Mettapedia.GraphTheory.FourColor
open PentagonalCoronaGeometry PhysicalForkCodeFaces SimpleGraphDartRotation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaReductionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaReductionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)
  (hfaces : FaceLengths rotation root)
  (hvertices : Function.Injective (tracedVertex rotation root))
  (houter : OuterInduced rotation root)

include hfaces hvertices houter

/-- Face geometry supplies the recognized source of the reconstructible
six-port replacement. No cycle frame or tangle isomorphism is an input. -/
theorem strict_reduction
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4) :
    let hC := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic
    let L := incidence rotation root hC (hfaces.central_period rotation root)
      (hfaces.neighbour_periods rotation root) hvertices houter
    ∃ recognition : OpenTangleIsomorphism.Iso piece
        (ofVertexSide rotation.toRotationSystem L.patchKeep (Recognition.root L rotation)),
      let candidate := Embedded.smaller rotation L.patchVertices
        (Embedded.ports rotation L.patchVertices (Recognition.root L rotation) recognition 0).1
        (Recognition.root L rotation) recognition
      Fintype.card ({v : V // deletedRegionKeep L.patchVertices v} ⊕ Fin 4) + 12 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep L.patchVertices v} ⊕ Fin 4) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData candidate ∧
      (RotationSystemTaitColorable candidate → RotationSystemTaitColorable rotation.toRotationSystem) := by
  let hC := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic
  exact Recognition.strict_reduction_of_geometry _ rotation
    (incidence_rotation rotation root hC (hfaces.central_period rotation root)
      (hfaces.neighbour_periods rotation root) hvertices houter) h htwo hminimum hcyclic

/-- A vertex-minimal counterexample cannot have this face pattern with
distinct traced vertices and an induced outer boundary. -/
theorem not_in_minimal_counterexample
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  let hC := cubic3_of rotation.toRotationSystem minimal.spherical.cubic minimal.vertexRotationCyclic
  exact Recognition.not_in_minimal_counterexample _ rotation
    (incidence_rotation rotation root hC (hfaces.central_period rotation root)
      (hfaces.neighbour_periods rotation root) hvertices houter) minimal

end
end FourColor.PentagonalLobePatch.Tangle.Corona
