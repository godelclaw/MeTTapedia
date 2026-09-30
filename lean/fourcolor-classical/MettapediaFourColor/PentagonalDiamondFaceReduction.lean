import MettapediaFourColor.PentagonalDiamondRecognition
import Mettapedia.GraphTheory.FourColor.PartialCubicDartNormalForm

/-!
# A face-pattern family reduced through the shared diamond core

A central pentagon and three consecutive pentagonal neighbours suffice.
The other two neighbour lengths and the size of the surrounding map are
unrestricted. Normal-form geometry supplies the twelve distinct vertices,
all six genuine ports and the connected exterior. The integrated diamond
repair then removes twelve vertices, introduces four, and reconstructs a
colouring of the whole source.

This is a recognition-and-reduction theorem for every occurrence of the
pattern. It does not assert that the pattern occurs in every planar map.
-/

namespace FourColor.PentagonalDiamondPatch.Tangle.FaceReduction

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24MinimalFaceSize GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FourEdgeCutGluing GoertzelV24ThreeEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance diamondFaceEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance diamondFaceEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : PentagonalDiamond.FaceLengths rotation root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hcyclic : CyclicallyFiveEdgeConnected G)

abbrev cubic := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic

/-- Face lengths and ambient normal form construct the entire occurrence. -/
def recognized : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (Recognition.keep rotation root)
      (Recognition.rootIn rotation root (cubic rotation h) hfaces)) := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  have hgirth := PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive
    rotation hcubic hcyclic (by omega)
  have hv := PentagonalDiamond.vertex_injective_of_girth rotation root
    (cubic rotation h) hfaces hgirth.1 hgirth.2
  exact Recognition.recognized rotation root (cubic rotation h) hfaces hv hcubic hcyclic (by omega)

/-- Every occurrence has a valid strict reduction. The two unconstrained
neighbours are part of the exterior and may be recoloured jointly with it. -/
theorem strict_reduction_of_face_pattern
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    let R := recognized rotation root hfaces h hminimum hcyclic
    let deleted := Recognition.deleted rotation root
    let rin := Recognition.rootIn rotation root (cubic rotation h) hfaces
    let rout := (SixPortTreeReplacement.Embedded.ports scheme rotation deleted rin R 0).1
    let candidate := SixPortTreeReplacement.Embedded.smaller scheme rotation deleted rout rin R
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + 8 = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) < Fintype.card V ∧
      BridgelessSphericalCubicMapData candidate ∧
      (RotationSystemTaitColorable candidate → RotationSystemTaitColorable rotation.toRotationSystem) := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hc4 : CyclicEdgeConnectivityAtLeast G 4 := fun cut => by
    have hc := hcyclic cut
    change 5 ≤ cut.edgeCut.card at hc
    change 4 ≤ cut.edgeCut.card
    omega
  exact SixPortTreeReplacement.Embedded.strict_reduction scheme rotation
    (Recognition.deleted rotation root) _ _ (recognized rotation root hfaces h hminimum hcyclic)
    h htwo (SixPortTreeReplacement.Embedded.exterior_connected scheme rotation
      (Recognition.deleted rotation root) _ (recognized rotation root hfaces h hminimum hcyclic)
      h.spherical.cubic hc4 (by omega))

omit h hminimum hcyclic in
include hfaces in
/-- Only the four local face lengths are supplied in a vertex-minimal
counterexample; every exterior and geometric condition is derived. -/
theorem not_in_minimal_counterexample_of_face_pattern
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  SixPortTreeReplacement.Embedded.not_in_minimal_counterexample_of_recognition scheme
    rotation (Recognition.deleted rotation root) _
    (recognized rotation root hfaces minimal.toBridgelessSphericalCubicMapData
      (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
      (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample rotation minimal))
    (by decide) minimal

omit hfaces h hminimum hcyclic in
/-- The earlier six-face corona is one instance of this four-face pattern. -/
theorem ofCorona (hf : PentagonalCoronaGeometry.FaceLengths rotation root) :
    PentagonalDiamond.FaceLengths rotation root := by
  refine ⟨hf.central, ?_⟩
  intro i hi _
  have hn : i ≠ 0 := by intro he; subst i; contradiction
  simpa [hn] using hf.neighbours i

omit hfaces h hminimum hcyclic in
/-- This application reuses the joint diamond repair and does not consume
the corona's separate terminal-colouring or Kempe-answer checks. -/
theorem corona_excluded_via_diamond
    (hf : PentagonalCoronaGeometry.FaceLengths rotation root)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  not_in_minimal_counterexample_of_face_pattern rotation root (ofCorona rotation root hf) minimal

end
end FourColor.PentagonalDiamondPatch.Tangle.FaceReduction
