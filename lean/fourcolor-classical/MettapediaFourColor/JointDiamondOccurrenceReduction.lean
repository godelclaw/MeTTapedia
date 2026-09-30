import MettapediaFourColor.JointDiamondCutOccurrence
import MettapediaFourColor.DiamondCoupledWiringFaces
import MettapediaFourColor.DiamondCoupledWiringVertices
import Mettapedia.GraphTheory.FourColor.OpenTanglePortFaceCount
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize

/-! # Strict reduction at an actual joint-diamond occurrence

The complete coupled replacement preserves the connected bridgeless spherical
cubic class. It removes fourteen vertices and inserts two. The exact ordered
exterior return accounts for both free wires: vertices, edges and faces decrease
by twelve, eighteen and six respectively.

The colouring reconstruction retains the joint eight-port witness. It may
recolour the exterior before restoring the original core. The occurrence is
supplied as an exact open-tangle isomorphism; this theorem does not assert
that every target contains one.
-/

namespace FourColor.JointDiamondPatch.Tangle.Occurrence
open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24DeletedRegionRotationSplice
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceOrbitIncidence GoertzelV24MinimalFaceSize
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24RotationSpliceConstructor
open OpenTanglePortReplacement OpenTangleMarkedFace
open Equiv Equiv.Perm

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (deleted : Finset V)
  (root : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (R : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) root))
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)

include h in
theorem original_class : BridgelessSphericalCubicMapData
    (original rotation deleted root R) := by
  apply RotationSystemExactTransport.mapClass rotation.toRotationSystem
    (original rotation deleted root R) (sourceDarts rotation deleted root R).symm
    (sourceVertices rotation deleted root R).symm ?_ ?_ ?_ h
  · intro d
    apply (sourceDarts rotation deleted root R).injective
    rw [Equiv.apply_symm_apply, sourceDarts_alpha, Equiv.apply_symm_apply]
  · intro d
    apply (sourceVertices rotation deleted root R).injective
    rw [Equiv.apply_symm_apply, sourceDarts_vertex, Equiv.apply_symm_apply]
  · intro d
    apply (sourceDarts rotation deleted root R).injective
    rw [Equiv.apply_symm_apply, sourceDarts_rotation, Equiv.apply_symm_apply]

variable (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)
  (htwo : OrbitFacesTwoSided rotation.toRotationSystem)

include h hminimum hinternal htwo in
theorem normalized_return : returnCode (normalizedOutside rotation deleted root R) =
    (finRotate 8)⁻¹ := by
  apply (ports rotation deleted root R).permCongr.injective
  have hr := (OpenTangleIsomorphism.boundaryReindex (outside rotation deleted root R)
    (ports rotation deleted root R)).returnCode
  change (ports rotation deleted root R).permCongr
    (returnCode (normalizedOutside rotation deleted root R)) =
    returnCode (outside rotation deleted root R) at hr
  have hi : (ports rotation deleted root R).permCongr ((finRotate 8)⁻¹) =
      ((ports rotation deleted root R).permCongr (finRotate 8))⁻¹ :=
    (ports rotation deleted root R).permCongrHom.map_inv _
  rw [hr, hi, exterior_order rotation deleted root R h hminimum hinternal htwo, inv_inv]
  exact OpenTangleVertexSideReturn.returnCode_eq _ _ _

include htwo

/-- Both free wires are included in the face calculation. The exterior's
interior face count cancels, so the result is independent of exterior size. -/
theorem wired_face_decrease :
    Fintype.card (OrbitFace (wired rotation deleted root R h hminimum hinternal)) + 6 =
      Fintype.card (OrbitFace (original rotation deleted root R)) := by
  let O := normalizedOutside rotation deleted root R
  have hr := normalized_return rotation deleted root R h hminimum hinternal htwo
  have ho := OpenTanglePortFaceCount.face_count O piece (Equiv.refl _)
  rw [hr, piece_returnCode, piece_face_count] at ho
  have hbefore : (partition (Equiv.sumCongr (finRotate 8)⁻¹ (finRotate 8))).parts.card = 2 := by
    decide +kernel
  have hafter : (partition (Equiv.sumCongr (finRotate 8)⁻¹ (finRotate 8) *
      MatchedSeam.seamSwap (Equiv.refl (Fin 8)))).parts.card = 8 := by decide +kernel
  have hn := DiamondCoupledWiring.Rotation.face_count_opposite O
    (wire_separated rotation deleted root R h hminimum hinternal) hr
  change Fintype.card (OrbitFace (original rotation deleted root R)) + _ = _ at ho
  change Fintype.card (OrbitFace (wired rotation deleted root R h hminimum hinternal)) = _ at hn
  omega

/-- Source cuts supply bridgelessness; exact port returns supply Euler.
Neither field is assumed of the replacement. -/
theorem wired_class : BridgelessSphericalCubicMapData
    (wired rotation deleted root R h hminimum hinternal) := by
  let O := normalizedOutside rotation deleted root R
  have ho := original_class rotation deleted root R h
  have hs := wired_structural rotation deleted root R h hminimum hinternal
  refine ⟨⟨?_, ?_⟩, hs.1, ?_, hs.2⟩
  · exact DiamondCoupledWiring.Rotation.cubic O _
      (OpenTangleVertexReflection.exterior_isCubic O piece (Equiv.refl _) ho.spherical.cubic)
  · have heo := (original rotation deleted root R).card_darts_eq_twice_card_edges
    have hen := (wired rotation deleted root R h hminimum hinternal).card_darts_eq_twice_card_edges
    change Fintype.card ((InternalDart rotation.toRotationSystem (deletedRegionKeep deleted) ⊕
      Fin 34) ⊕ (Fin 8 ⊕ Fin 8)) = _ at heo
    change Fintype.card ((InternalDart rotation.toRotationSystem (deletedRegionKeep deleted) ⊕
      Fin 8) ⊕ Fin 6) = _ at hen
    simp only [Fintype.card_sum, Fintype.card_fin] at heo hen
    have hf := wired_face_decrease rotation deleted root R h hminimum hinternal htwo
    have he := ho.spherical.euler
    simp only [Fintype.card_sum, Fintype.card_fin] at he ⊢
    omega
  · exact DiamondCoupledWiring.Rotation.rotation_cyclic O _
      (OpenTangleVertexReflection.exterior_rotationCyclic O piece (Equiv.refl _)
        ho.vertexRotationCyclic)

/-- A genuine strict reduction, with all introduced vertices counted and
the compatible colouring witness reconstructed in the actual source. -/
theorem strict_reduction_of_occurrence :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 2) + 12 = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 2) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (wired rotation deleted root R h hminimum hinternal) ∧
      (RotationSystemTaitColorable (wired rotation deleted root R h hminimum hinternal) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hv := wired_vertex_decrease rotation deleted root R
  exact ⟨hv, by omega, wired_class rotation deleted root R h hminimum hinternal htwo,
    colorable_of_actual_wiring rotation deleted root R h hminimum hinternal htwo⟩

omit h hminimum hinternal htwo in
include R in
/-- Minimality supplies a colouring of the smaller map. Only the exact
occurrence is additional input; no colouring richness is assumed. -/
theorem not_in_minimal_counterexample_of_occurrence
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  obtain ⟨_, hlt, hs, hr⟩ := strict_reduction_of_occurrence rotation deleted root R
    minimal.toBridgelessSphericalCubicMapData
    (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
    (cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample rotation minimal)
    minimal.facesTwoSided
  exact minimal.notColorable (hr (minimal.smallerColorable _ hlt hs))

end
end FourColor.JointDiamondPatch.Tangle.Occurrence
