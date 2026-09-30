import Mettapedia.GraphTheory.FourColor.PaddedCycleCapStructural
import Mettapedia.GraphTheory.FourColor.PaddedCycleCapContext
import Mettapedia.GraphTheory.FourColor.CycleCapGeometry
import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryJoint
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement

/-! # Padded-cap replacement preserves the closed map class

The cap and its smaller outer cycle have the same ordered face return,
the same open Euler contribution, and connected bridgeless interiors.
Consequently replacement preserves the spherical cubic bridgeless class
in every fixed exterior, including disconnected exteriors.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24TwoEdgeCutMinimality GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph OpenTangleVertexReflection
open OpenTanglePortReplacement OpenTangleReplacementEuler OpenTangleRewireFaces
open OpenTangleClosedWitness

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)

theorem indexed_returnCode :
    returnCode (asOpen (indexedCap m hm)) = CycleCap.boundaryPerm (m*2) := by
  rw [returnCode_asOpen, indexedCap, TwoSidedBoundaryJoint.face_reindex, encode_cap]
  ext b
  rcases b with e | j
  · exact nomatch e
  · obtain ⟨⟨i,b⟩,rfl⟩ := (portIndex m).surjective j
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.symm_apply_apply, Equiv.sumCongr_symm]
    cases b
    · change Sum.inr (portIndex m (i-1,true)) = Sum.inr (portIndex m (i,false)-1)
      congr 1
      apply eq_sub_iff_add_eq.mpr
      simpa only [sub_add_cancel] using portIndex_true_next m (i-1)
    · change Sum.inr (portIndex m (i,false)) = Sum.inr (portIndex m (i,true)-1)
      congr 1
      exact eq_sub_iff_add_eq.mpr (portIndex_false_next m i)

theorem indexed_mass : OpenTangleReplacementEuler.eulerMass (asOpen (indexedCap m hm)) = 4 := by
  rw [indexedCap, TwoSidedBoundaryJoint.mass_reindex]
  exact PaddedCycleCap.eulerMass m hm

section Context
variable {V I B : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Empty ⊕ Fin (m*2))

/-- The geometric replacement is valid at every width, independently of
the colouring reconstruction's domain. -/
theorem replacement_class
    (h : BridgelessSphericalCubicMapData (sewn outside (indexedCap m hm) seam)) :
    BridgelessSphericalCubicMapData
      (sewn outside (CycleCap.cap (m*2) (by omega)) seam) := by
  have structural := OpenTangleInternalReplacement.replacement_structural outside
    (asOpen (indexedCap m hm)) (CycleCap.openCap (m*2) (by omega)) seam seam
    (by simpa only [indexedCap, TwoSidedBoundaryJoint.side_reindex] using
      cap_connected_bridgeless m hm)
    (CycleCap.cap_connected_bridgeless (m*2) (by omega))
  have heuler : compositeEuler outside (asOpen (indexedCap m hm)) seam =
      compositeEuler outside (CycleCap.openCap (m*2) (by omega)) seam := by
    apply (euler_eq_iff_mass _ _ ?_ outside seam).mpr
    · exact (indexed_mass m hm).trans (CycleCap.eulerMass (m*2) (by omega)).symm
    · rw [indexed_returnCode, returnCode_asOpen, CycleCap.encode_cap]
  exact {
    spherical := {
      cubic := isCubic_composeRotationSystem outside (CycleCap.openCap (m*2) (by omega)) seam
        (exterior_isCubic outside _ seam h.spherical.cubic)
        (CycleCap.cap_isCubic (m*2) (by omega))
      euler := by
        change compositeEuler outside (CycleCap.openCap (m*2) (by omega)) seam = 2
        rw [← heuler]
        exact h.spherical.euler }
    primalConnected := (structural.mp ⟨h.primalConnected,h.edgeBridgeFree⟩).1
    vertexRotationCyclic := vertexRotationCyclic_composeRotationSystem outside
      (CycleCap.openCap (m*2) (by omega)) seam
      (exterior_rotationCyclic outside _ seam h.vertexRotationCyclic)
      (CycleCap.cap_rotationCyclic (m*2) (by omega))
    edgeBridgeFree := (structural.mp ⟨h.primalConnected,h.edgeBridgeFree⟩).2 }

omit [DecidableEq V] in
/-- The entire closed map loses exactly `6m` vertices. -/
theorem replacement_strict :
    Fintype.card (V ⊕ Fin (m*2)) < Fintype.card (V ⊕ Vertex m) := by
  have h := closed_vertex_loss m (V := V)
  have hm' := NeZero.pos m
  omega

end Context
end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
