import MettapediaFourColor.JointDiamondExteriorClosure
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryReindexWitness
import Mettapedia.GraphTheory.FourColor.PartialCubicDartNormalForm

/-!
# The coupled wiring at an actual joint-diamond occurrence

Normal-form triangle exclusion separates both free wires' exterior endpoints.
The exact boundary-coordinate transport then realizes the wiring on the
literal exterior of the occurrence, and a colouring of it reconstructs the
original graph. The full vertex decrease is twelve.

This establishes the construction and reconstruction. Preservation of the
bridgeless spherical class by the smaller map is not asserted here.
-/

namespace FourColor.JointDiamondPatch.Tangle.Occurrence

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24WeightedOrbitFaceCorridor

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance wiredOccurrenceEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance wiredOccurrenceEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (deleted : Finset V)
  (root : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (R : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) root))
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

abbrev normalizedOutside := (outside rotation deleted root R).reindexBoundary
  (ports rotation deleted root R)

include h hminimum hinternal in
/-- A coincident pair of wire endpoints would close a triangle through
the adjacent original core vertices. -/
theorem wire_separated : DiamondCoupledWiring.Rotation.Separated
    (normalizedOutside rotation deleted root R) := by
  let act := actual rotation.toRotationSystem (deletedSideKeep deleted) root R
  have ht := (PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive rotation
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)) hinternal.1
    (by have hh := twenty_lt_vertices rotation.toRotationSystem (deletedSideKeep deleted)
          root R h.spherical hminimum; omega)).1
  have same (d e : Dart) (hv : vertex d = vertex e) : (act d).fst = (act e).fst := by
    change rotation.toRotationSystem.vertOf (act d) = rotation.toRotationSystem.vertOf (act e)
    rw [actual_vertex, actual_vertex, hv]
  have adjacent (i : Fin 34) : G.Adj (act (.inl i)).fst
      (act (.inl (piece.interiorAlpha i))).fst := by
    change G.Adj (act (.inl i)).fst
      (actual rotation.toRotationSystem (deletedSideKeep deleted) root R
        (.inl (piece.interiorAlpha i))).fst
    rw [actual_alpha]
    exact (act (.inl i)).adj
  have different (a b : Fin 8) (hab : G.Adj (act (.inr a)).fst (act (.inr b)).fst) :
      (normalizedOutside rotation deleted root R).boundaryVert a ≠
        (normalizedOutside rotation deleted root R).boundaryVert b := by
    intro he
    have he' : (act (.inr a)).snd = (act (.inr b)).snd := congrArg Subtype.val he
    exact ht _ _ _ hab (by rw [he']; exact (act (.inr b)).adj) (act (.inr a)).adj.symm
  constructor
  · apply different 0 1
    rw [same (.inr 0) (.inl (piece.interiorAlpha 0)) (by decide),
      same (.inr 1) (.inl 0) (by decide)]
    exact (adjacent 0).symm
  · apply different 4 5
    rw [same (.inr 4) (.inl (piece.interiorAlpha 14)) (by decide),
      same (.inr 5) (.inl 14) (by decide)]
    exact (adjacent 14).symm

/-- Keep the actual exterior, pair two port pairs and insert the two
coupled cubic vertices. Normal form derives the absence of wire loops. -/
abbrev wired := DiamondCoupledWiring.Rotation.closed (normalizedOutside rotation deleted root R)
  (wire_separated rotation deleted root R h hminimum hinternal)

include R in
theorem wired_vertex_decrease :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 2) + 12 = Fintype.card V := by
  have hh := exterior_card rotation deleted root R
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

variable (htwo : OrbitFacesTwoSided rotation.toRotationSystem)

include htwo in
/-- The whole physical wiring supplies a joint witness. Exact coordinate
transport and physical Kempe closure reconstruct the original graph. -/
theorem colorable_of_actual_wiring
    (hc : RotationSystemTaitColorable (wired rotation deleted root R h hminimum hinternal)) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  obtain ⟨k, hk⟩ := (DiamondCoupledWiring.Rotation.colorable_iff
    (normalizedOutside rotation deleted root R)
    (wire_separated rotation deleted root R h hminimum hinternal)).mp hc
  have ht := OpenTangleKempeRepair.trace_transport
    (OpenTangleIsomorphism.boundaryReindex (outside rotation deleted root R)
      (ports rotation deleted root R)) (Equiv.refl _) hk
  exact colorable_of_joint_exterior rotation deleted root R h hminimum hinternal htwo k ht

end
end FourColor.JointDiamondPatch.Tangle.Occurrence
