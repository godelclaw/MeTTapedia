import MettapediaFourColor.PentagonalCoronaMinimalReduction
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaNoncollision

/-!
# Strict reduction from the six actual face lengths

A central pentagon with four pentagonal neighbours and one hexagonal
neighbour supplies the complete local recognition. Vertex noncollision
and absence of extra outer chords are derived. The existing joint repair
then removes sixteen vertices, introduces four, preserves the spherical
bridgeless cubic class, and reconstructs a genuine colouring.

The ambient normal-form hypotheses remain explicit. This theorem reduces
every occurrence of the stated pattern; it does not assert that every
source graph contains one.
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

local instance coronaFaceEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaFaceEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : FaceLengths rotation root)

include hfaces

/-- The six face lengths and ambient normal form construct every local
geometric witness used by the strict twelve-vertex reduction. -/
theorem strict_reduction_of_face_pattern
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ∃ hvertices : Function.Injective (tracedVertex rotation root),
    ∃ houter : OuterInduced rotation root,
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
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  have hv := tracedVertex_injective_of_cyclicallyFive rotation root
    (cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic)
    (hfaces.central_period rotation root) (hfaces.neighbour_periods rotation root)
    hcubic hcyclic (by omega)
  exact ⟨hv, strict_reduction_of_cyclicallyFive rotation root hfaces hv h htwo hminimum hcyclic⟩

/-- A vertex-minimal counterexample contains no central pentagonal face
whose neighbours are four pentagons and one hexagon. -/
theorem not_in_minimal_counterexample_of_face_pattern
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  not_in_minimal_counterexample_of_distinct_vertices rotation root hfaces
    (tracedVertex_injective_of_minimality rotation root hfaces minimal) minimal

end
end FourColor.PentagonalLobePatch.Tangle.Corona
