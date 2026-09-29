import MettapediaFourColor.PentagonalLobeDistinctAttachments
import Mettapedia.GraphTheory.FourColor.SixPortBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize

/-!
# Minimality supplies the recognized lobe's connected exterior

The six exterior attachments need not be distinct. Euler counting and
minimum face size give at least twenty ambient vertices, leaving at least
four outside the sixteen-vertex patch. The patch contains a cycle by cubic
incidence. The general six-port connectivity theorem now connects the
exterior using the cyclic cut bound.

Every hypothesis of this connectivity argument follows from graph-backed
vertex minimality and exact recognition of the local tangle. The resulting
strict reduction still replaces sixteen vertices by four and reconstructs
the original colouring through joint boundary repair. Recognition from
alternating-lobe geometry and global supply remain separate obligations.
-/

namespace FourColor.PentagonalLobePatch.Tangle.Embedded

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24ThreeEdgeCutMinimality GoertzelV24MinimalFaceSize
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24WeightedOrbitFaceCorridor
open MatchingBoundaryConnectivity SixPortBoundaryConnectivity

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance minimalExteriorEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
  (rootIn : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (recognition : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) rootIn))

include recognition

theorem inside_hasCycle (hcubic : rotation.toRotationSystem.IsCubic) :
    HasCycleOnSide G (deletedSideKeep deleted) := by
  classical
  have hs := Fintype.card_congr recognition.vertex
  change 16 = Fintype.card {v : V // deletedSideKeep deleted v} at hs
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedSideKeep deleted)).trans recognition.boundary.symm)
  simp only [Fintype.card_fin] at hb
  apply hasCycle_of_boundary_card_lt_card_add_two
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hcubic) v))
    (deletedSideKeep deleted) (inside_connected rotation deleted rootIn recognition)
  omega

/-- Minimum face size and Euler ensure that the exterior has at least four
vertices. Repeated attachment endpoints are allowed. -/
theorem exterior_connected_of_minimum_face_size
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4) :
    (G.induce {v | deletedRegionKeep deleted v}).Connected := by
  classical
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem hsphere hminimum
  have hsize := size_decrease rotation deleted rootIn recognition
  simp only [Fintype.card_sum, Fintype.card_fin] at hsize
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedRegionKeep deleted)).trans
      (ports rotation deleted rootIn recognition).symm)
  simp only [Fintype.card_fin] at hb
  apply connected_of_two_lt_card_of_boundary_card_le_six (deletedRegionKeep deleted)
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hsphere.cubic) v)) hcyclic
  · exact inside_hasCycle rotation deleted rootIn recognition hsphere.cubic
  · omega
  · omega

theorem strict_reduction_of_minimum_face_size
    (rootOut : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4) :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + 12 = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation deleted rootOut rootIn recognition) ∧
      (RotationSystemTaitColorable (smaller rotation deleted rootOut rootIn recognition) →
        RotationSystemTaitColorable rotation.toRotationSystem) :=
  strict_reduction rotation deleted rootOut rootIn recognition h htwo
    (exterior_connected_of_minimum_face_size rotation deleted rootIn recognition
      h.spherical hminimum hcyclic)

theorem exterior_connected_of_minimality
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    (G.induce {v | deletedRegionKeep deleted v}).Connected :=
  exterior_connected_of_minimum_face_size rotation deleted rootIn recognition minimal.spherical
    (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
    (cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample rotation minimal)

/-- Exact local recognition alone is sufficient to exclude this occurrence
from a vertex-minimal counterexample. Minimality supplies every exterior
condition; the six ports supply an actual exterior root. -/
theorem not_in_minimal_counterexample_of_recognition
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  not_in_minimal_counterexample rotation deleted
    (ports rotation deleted rootIn recognition 0).1 rootIn recognition
    (exterior_connected_of_minimality rotation deleted rootIn recognition minimal) minimal

end
end FourColor.PentagonalLobePatch.Tangle.Embedded
