import MettapediaFourColor.PentagonalLobeCoordinates
import MettapediaFourColor.PentagonalLobeMinimalExterior
import Mettapedia.GraphTheory.FourColor.OpenTangleDartRecognition

/-!
# Recognizing and reducing the actual pentagonal-lobe family

Two disjoint cycles, their spoke matching and the alternating outer turns
are independently stated graph data. Spherical geometry forces the inner
order. Exact dart transport then constructs the literal patch isomorphism
and consumes the existing twelve-vertex reduction with genuine colouring
reconstruction. No local recognition isomorphism is assumed.
-/

namespace FourColor.PentagonalLobePatch.Tangle.Recognition

open Mettapedia.GraphTheory.FourColor
open ElevenLobeSpokeOrder SimpleGraphDartRotation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness GoertzelV24TwoEdgeCutMinimality
open GoertzelV24DeletedRegionRotationSplice GoertzelV24WeightedOrbitFaceCorridor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance recognitionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance recognitionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (L : Incidence G) (rotation : Data G)

/-- A real retained dart at the start of the closing gap. -/
def root : RetainedDart rotation.toRotationSystem L.patchKeep :=
  ⟨L.outer.star 0 0, (L.patchKeep_iff _).2 (.inl (L.outer.vertex_keep 0))⟩

/-- The one shared orientation is used by every vertex, edge and port map. -/
def withOrientation
    (b : Bool)
    (hm : ∀ i, L.matching (if b then i + 1 else i - 1) = L.matching i + 1)
    (hcubic : G.IsRegularOfDegree 3)
    (houter : ∀ d : CycleBoundaryOrientation.Dart 11,
      rotation.vertexRotation (L.outer.star d.1 d.2) =
        L.outer.star (CycleBoundaryOrientation.turn 11 reverseAt d).1
          (CycleBoundaryOrientation.turn 11 reverseAt d).2)
    (hinner : ∀ d : CycleBoundaryOrientation.Dart 5,
      rotation.vertexRotation (L.inner.star d.1 d.2) =
        L.inner.star (CycleBoundaryOrientation.turn 5 (fun _ => b) d).1
          (CycleBoundaryOrientation.turn 5 (fun _ => b) d).2) :
    OpenTangleIsomorphism.Iso piece
      (ofVertexSide rotation.toRotationSystem L.patchKeep (root L rotation)) := by
  apply OpenTangleIsomorphism.ofRetainedDarts piece rotation.toRotationSystem L.patchKeep
    (root L rotation) (Coordinates.vertices.trans (L.patchVertexEquiv b hm))
    (Coordinates.darts.trans (L.patchDartEquiv b hm rotation hcubic))
  · intro i
    change L.patchKeep (L.coordinateDart b hm (Coordinates.darts (.inl i))).snd
    exact Classical.byContradiction fun h =>
      Coordinates.internal i ((L.coordinateDart_boundary b hm hcubic _).mp h)
  · intro p
    exact (L.coordinateDart_boundary b hm hcubic _).mpr (Coordinates.boundary p)
  · intro i
    change L.coordinateDart b hm (Coordinates.darts (.inl (piece.interiorAlpha i))) =
      (L.coordinateDart b hm (Coordinates.darts (.inl i))).symm
    rw [Coordinates.alpha]
    exact L.coordinateDart_flip b hm hcubic _ (Coordinates.internal i)
  · intro d
    apply Subtype.ext
    change L.coordinateVertex b hm (Coordinates.vertices (piece.vertOf d)) =
      (L.coordinateDart b hm (Coordinates.darts d)).fst
    rw [L.coordinateDart_fst, Coordinates.vertex]
  · intro d
    apply Subtype.ext
    change L.coordinateDart b hm (Coordinates.darts (piece.rho d)) =
      rotation.vertexRotation (L.coordinateDart b hm (Coordinates.darts d))
    rw [Coordinates.rotation]
    exact L.coordinateDart_turn b hm rotation houter hinner _

/-- Independent two-cycle geometry supplies the full literal patch, with
all half-edges and rotations retained. -/
theorem recognized
    (houter : ∀ d : CycleBoundaryOrientation.Dart 11,
      rotation.vertexRotation (L.outer.star d.1 d.2) =
        L.outer.star (CycleBoundaryOrientation.turn 11 reverseAt d).1
          (CycleBoundaryOrientation.turn 11 reverseAt d).2)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem) :
    Nonempty (OpenTangleIsomorphism.Iso piece
      (ofVertexSide rotation.toRotationSystem L.patchKeep (root L rotation))) := by
  obtain ⟨b, hb, hm⟩ := L.inner_geometry rotation houter hsphere htwo hconnected hrotation
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (SimpleGraph.degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hsphere.cubic) v)
  exact ⟨withOrientation L rotation b hm hcubic houter hb⟩

/-- The same family has a strict reconstructible reduction independently
of a counterexample hypothesis. All four replacement vertices are counted. -/
theorem strict_reduction_of_geometry
    (houter : ∀ d : CycleBoundaryOrientation.Dart 11,
      rotation.vertexRotation (L.outer.star d.1 d.2) =
        L.outer.star (CycleBoundaryOrientation.turn 11 reverseAt d).1
          (CycleBoundaryOrientation.turn 11 reverseAt d).2)
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4) :
    ∃ recognition : OpenTangleIsomorphism.Iso piece
        (ofVertexSide rotation.toRotationSystem L.patchKeep (root L rotation)),
      let candidate := Embedded.smaller rotation L.patchVertices
        (Embedded.ports rotation L.patchVertices (root L rotation) recognition 0).1
        (root L rotation) recognition
      Fintype.card ({v : V // deletedRegionKeep L.patchVertices v} ⊕ Fin 4) + 12 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep L.patchVertices v} ⊕ Fin 4) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData candidate ∧
      (RotationSystemTaitColorable candidate → RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hc : G.Connected := by
    have hc := h.primalConnected
    rwa [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq] at hc
  obtain ⟨recognition⟩ := recognized L rotation houter h.spherical htwo hc h.vertexRotationCyclic
  refine ⟨recognition, ?_⟩
  exact Embedded.strict_reduction_of_minimum_face_size rotation L.patchVertices (root L rotation)
    recognition (Embedded.ports rotation L.patchVertices (root L rotation) recognition 0).1
    h htwo hminimum hcyclic

/-- This actual geometric family cannot occur in a vertex-minimal
counterexample. The proof constructs recognition, derives the necessary
exterior geometry from minimality, strictly reduces and reconstructs. -/
theorem not_in_minimal_counterexample
    (houter : ∀ d : CycleBoundaryOrientation.Dart 11,
      rotation.vertexRotation (L.outer.star d.1 d.2) =
        L.outer.star (CycleBoundaryOrientation.turn 11 reverseAt d).1
          (CycleBoundaryOrientation.turn 11 reverseAt d).2)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  have hc : G.Connected := by
    have h := minimal.primalConnected
    rwa [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq] at h
  obtain ⟨recognition⟩ := recognized L rotation houter minimal.spherical
    minimal.facesTwoSided hc minimal.vertexRotationCyclic
  exact Embedded.not_in_minimal_counterexample_of_recognition rotation L.patchVertices
    (root L rotation) recognition minimal

end
end FourColor.PentagonalLobePatch.Tangle.Recognition
