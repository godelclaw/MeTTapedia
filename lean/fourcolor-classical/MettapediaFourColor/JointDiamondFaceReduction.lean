import MettapediaFourColor.JointDiamondRecognition
import MettapediaFourColor.JointDiamondOccurrenceReduction
import Mettapedia.GraphTheory.FourColor.PartialCubicDartNormalForm

/-!
# The face traversal consumes the coupled strict reduction

Normal form and the four face lengths force fourteen distinct vertices.
The additional, finite BoundaryClear check recognizes the exact eight-port
piece. Its coupled replacement then removes twelve vertices net, remains in
the connected bridgeless spherical cubic class, and reconstructs an actual
colouring of the original map.

The outgoing-endpoint check is retained explicitly. No claim is made here
that normal form alone discharges it or supplies this face pattern.
-/

namespace FourColor.JointDiamondPatch.Tangle.FaceReduction

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WeightedOrbitFaceCorridor GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DeletedRegionRotationSplice GoertzelV24MinimalFaceSize
open GoertzelV24OrbitFaceTwoSided

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : JointDiamond.FaceLengths rotation root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

abbrev cubic := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic

include hfaces h hminimum hinternal in
/-- Cyclic-five connectivity excludes the one remaining identification
that girth and joint dart transport do not exclude by themselves. -/
theorem vertex_injective : Function.Injective (JointDiamond.vertex rotation root) := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  have hgirth := PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive
    rotation hcubic hinternal.1 (by omega)
  exact JointDiamond.vertex_injective
    (JointDiamond.realization rotation root (cubic rotation h) hfaces)
    hgirth.1 hgirth.2 hcubic hinternal.1 (by omega)

variable (hclear : Recognition.BoundaryClear rotation root)

/-- Every representation field is constructed; the only remaining local
geometric check is that the eight candidate ports leave the core. -/
def recognized : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (Recognition.keep rotation root)
      (Recognition.rootIn rotation root (cubic rotation h) hfaces)) :=
  Recognition.recognized rotation root (cubic rotation h) hfaces
    (vertex_injective rotation root hfaces h hminimum hinternal) hclear

abbrev smaller := Occurrence.wired rotation (Recognition.deleted rotation root)
  (Recognition.rootIn rotation root (cubic rotation h) hfaces)
  (recognized rotation root hfaces h hminimum hinternal hclear) h hminimum hinternal

include hfaces h hminimum hinternal hclear in
/-- The whole operation removes fourteen vertices and introduces two.
The repair retains coupled choices and may recolour the exterior. -/
theorem strict_reduction_of_checked_face_pattern
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 2) + 12 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 2) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation root hfaces h hminimum hinternal hclear) ∧
      (RotationSystemTaitColorable (smaller rotation root hfaces h hminimum hinternal hclear) →
        RotationSystemTaitColorable rotation.toRotationSystem) :=
  Occurrence.strict_reduction_of_occurrence rotation (Recognition.deleted rotation root)
    (Recognition.rootIn rotation root (cubic rotation h) hfaces)
    (recognized rotation root hfaces h hminimum hinternal hclear) h hminimum hinternal htwo

omit h hminimum hinternal in
include hfaces hclear in
/-- A minimal counterexample cannot contain a face pattern passing the
outgoing-endpoint check. The pattern and the check are separate hypotheses. -/
theorem not_in_minimal_counterexample_of_checked_face_pattern
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  let h := minimal.toBridgelessSphericalCubicMapData
  let hminimum := orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal
  let hinternal := cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample rotation minimal
  exact Occurrence.not_in_minimal_counterexample_of_occurrence rotation
    (Recognition.deleted rotation root) (Recognition.rootIn rotation root (cubic rotation h) hfaces)
    (recognized rotation root hfaces h hminimum hinternal hclear) minimal

end
end FourColor.JointDiamondPatch.Tangle.FaceReduction
