import MettapediaFourColor.MixedDiamondExteriorClosure
import MettapediaFourColor.SevenPortTree

/-!
# Strict reduction of the mixed-diamond face pattern

Under the stated normal-form hypotheses, a central pentagon with consecutive
neighbouring lengths five, six, five has a thirteen-vertex, seven-port core.
Its five-vertex path replacement
preserves the connected bridgeless spherical cubic class. Restricting a
colouring of the smaller map supplies an actual exterior witness; physical
Kempe closure and the shared diamond repair then colour the original map.

Every introduced vertex is counted: thirteen are removed and five added.
The other two neighbouring face lengths and exterior size are unrestricted
beyond the ambient hypotheses.
The theorem does not assert that this local pattern occurs in every map.
-/

namespace FourColor.MixedDiamondPatch.Tangle.FaceReduction

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph GoertzelV24CompositeSeamCubic
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24VertexSideReassembly GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSideOpenTangle
open GoertzelV24SimpleGraphFaceDualConnectedness GoertzelV24MinimalFaceSize
open GoertzelV24CubicSmallBoundaryCycle
open FaceRecognition

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance mixedReductionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance mixedReductionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : MixedDiamond.FaceLengths rotation root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

/-- The exterior is kept literally; the only new vertices are the five
vertices of the path. Each of the seven cut edges remains a separate edge. -/
abbrev smaller := (outside rotation root hfaces h hminimum hinternal).composeRotationSystem
  SevenPortTree.piece (ports rotation root hfaces h hminimum hinternal).symm

include hfaces h hminimum hinternal

theorem reassembled_class :
    BridgelessSphericalCubicMapData
      ((outside rotation root hfaces h hminimum hinternal).composeRotationSystem piece
        (ports rotation root hfaces h hminimum hinternal).symm) := by
  exact (recognized rotation root hfaces h hminimum hinternal).symm.sewn_class
    (outside rotation root hfaces h hminimum hinternal)
    (complementBoundaryAlphaEquiv rotation.toRotationSystem (Recognition.deleted rotation root))
    (VertexSideExactReassembly.mapClass rotation.toRotationSystem
      (Recognition.deleted rotation root) _ _ h)

/-- Exact ordered face returns and Euler mass supply the topological part
of the same general replacement law used by the six-port reductions. -/
theorem smaller_class :
    BridgelessSphericalCubicMapData (smaller rotation root hfaces h hminimum hinternal) := by
  let O := outside rotation root hfaces h hminimum hinternal
  let seam := ports rotation root hfaces h hminimum hinternal
  have hout : (sideMultigraph O).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using
      exterior_connected rotation root hfaces h hminimum hinternal
  apply OpenTangleReplacementClass.mapClass O piece SevenPortTree.piece seam.symm
    (piece_returnCode.trans SevenPortTree.piece_returnCode.symm)
    (piece_eulerMass.trans SevenPortTree.piece_eulerMass.symm)
    SevenPortTree.cubic SevenPortTree.cyclic hout SevenPortTree.connected
    (OpenTangleConnectedReplacement.essential_of_surjective (sideMultigraph SevenPortTree.piece)
      (SevenPortTree.piece.boundaryVert ∘ seam.symm)
      (SevenPortTree.ports_surjective.comp seam.symm.surjective))
    (p := seam 0) (q := seam 1)
  · intro he
    have hh := seam.injective he
    exact (by decide : (0 : Fin 7) ≠ 1) hh
  · exact reassembled_class rotation root hfaces h hminimum hinternal

/-- This is the whole-map count, including all five introduced vertices. -/
theorem size_decrease :
    Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 5) + 8 =
      Fintype.card V := by
  have hs := exterior_card rotation root hfaces h hminimum hinternal
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Restriction keeps a genuine exterior assignment. The existing joint
repair may recolour it before reconstructing the source, preserving coupling. -/
theorem colorable_of_smaller
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hc : RotationSystemTaitColorable (smaller rotation root hfaces h hminimum hinternal)) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨r, _, hr, _, _, _⟩ := OpenTangleClosedWitness.restrictOpen
    (outside rotation root hfaces h hminimum hinternal) SevenPortTree.piece
    (ports rotation root hfaces h hminimum hinternal).symm c hc
  exact colorable_of_exterior rotation root hfaces h hminimum hinternal htwo r hr

/-- Every recognized occurrence gives a strict reduction in the actual
ambient map, with its class and colouring reconstruction proved. -/
theorem strict_reduction_of_face_pattern
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 5) + 8 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 5) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation root hfaces h hminimum hinternal) ∧
      (RotationSystemTaitColorable (smaller rotation root hfaces h hminimum hinternal) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hs := size_decrease rotation root hfaces h hminimum hinternal
  exact ⟨hs, by omega, smaller_class rotation root hfaces h hminimum hinternal,
    colorable_of_smaller rotation root hfaces h hminimum hinternal htwo⟩

omit h hminimum hinternal in
/-- Only the local face pattern is supplied. Minimality derives all normal
form hypotheses and colours the genuinely smaller replacement map. -/
theorem not_in_minimal_counterexample_of_face_pattern
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  obtain ⟨_, hlt, hs, hr⟩ := strict_reduction_of_face_pattern rotation root hfaces
    minimal.toBridgelessSphericalCubicMapData
    (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
    (cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample rotation minimal)
    minimal.facesTwoSided
  exact minimal.notColorable (hr (minimal.smallerColorable _ hlt hs))

end
end FourColor.MixedDiamondPatch.Tangle.FaceReduction
