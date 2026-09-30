import Mettapedia.GraphTheory.FourColor.PentagonalPaddedCapSeparation
import Mettapedia.GraphTheory.FourColor.PaddedCycleCapExteriorConnectivity
import Mettapedia.GraphTheory.FourColor.PartialCubicDartNormalForm
import Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound

/-!
# A pentagonal face pattern gives an actual strict cap reduction

Ambient normal form supplies girth, and joint dart routes prove all forty
traced vertices distinct. Short seam faces expose the ten ports and connect
the exterior. Replacing the cap by a ten-cycle removes thirty vertices from
the whole map. The shared all-width colouring repair reconstructs a genuine
source colouring; neither local injectivity nor exterior connectivity is
assumed. Occurrence of this pattern is still a separate coverage question.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.PentagonalFaceReduction

open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24TwoEdgeCutMinimality GoertzelV24DeletedRegionRotationSplice
open GoertzelV24MinimalFaceSize GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FourEdgeCutGluing

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance pentagonalCapEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance pentagonalCapEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)
  (hfaces : FaceTraversal.FaceLengths rotation.toRotationSystem 5 root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hcyclic : CyclicallyFiveEdgeConnected G)

abbrev cubic := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic

include hfaces h hminimum hcyclic in
/-- Ambient normal form and local face closure derive separation. -/
theorem vertex_injective_of_normal_form :
    Function.Injective (FaceTraversal.vertex rotation.toRotationSystem 5 root) := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  have hgirth := PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive
    rotation hcubic hcyclic (by omega)
  exact PentagonalSeparation.actual_vertex_injective rotation root
    (cubic rotation h) hfaces hgirth.1 hgirth.2

variable (hseam : FaceTraversal.BoundaryShortFaces rotation.toRotationSystem 5 root)

/-- The exact exterior is retained. The replacement is a ten-cycle with
the boundary matching derived from the actual face coordinates. -/
def smaller := FaceTraversal.reducedSystem rotation 5 (by decide) root
  (cubic rotation h) hfaces
  (vertex_injective_of_normal_form rotation root hfaces h hminimum hcyclic) hseam

include hfaces h hminimum hcyclic hseam in
/-- Every occurrence of the face pattern is reducible, independently of
the exterior's size. All thirty removed vertices are counted globally. -/
theorem strict_reduction_of_face_pattern
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    Fintype.card ({v : V // deletedRegionKeep
      (FaceTraversal.deleted rotation.toRotationSystem 5 root) v} ⊕ Fin 10) + 30 =
        Fintype.card V ∧
    Fintype.card ({v : V // deletedRegionKeep
      (FaceTraversal.deleted rotation.toRotationSystem 5 root) v} ⊕ Fin 10) <
        Fintype.card V ∧
    BridgelessSphericalCubicMapData (smaller rotation root hfaces h hminimum hcyclic hseam) ∧
    (RotationSystemTaitColorable (smaller rotation root hfaces h hminimum hcyclic hseam) →
      RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hv := vertex_injective_of_normal_form rotation root hfaces h hminimum hcyclic
  have hcount := FaceTraversal.face_traced_vertex_count rotation 5 root hv
  have hr := FaceTraversal.face_traced_strict_reduction rotation 5 (by decide) root
    (cubic rotation h) hfaces hv hseam h htwo
  exact ⟨by simpa using hcount.symm,hr⟩

omit h hminimum hcyclic in
include hfaces hseam in
/-- In a vertex-minimal counterexample only the stated face lengths are
supplied. The source class, girth, recognition and exterior are derived. -/
theorem not_in_minimal_counterexample_of_face_pattern
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  obtain ⟨_,hcard,hsmall,hreconstruct⟩ := strict_reduction_of_face_pattern rotation root hfaces
    minimal.toBridgelessSphericalCubicMapData
    (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
    (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample rotation minimal)
    hseam minimal.facesTwoSided
  exact minimal.notColorable (hreconstruct (minimal.smallerColorable _ hcard hsmall))

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.PentagonalFaceReduction
