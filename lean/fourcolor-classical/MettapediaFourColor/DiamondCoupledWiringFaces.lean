import MettapediaFourColor.DiamondCoupledWiringRotation
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement

/-! # Face counting through the coupled wiring's complete seam

The exterior face permutation is arbitrary. Its ordered boundary return,
together with the six new vertex darts, computes the entire change in
face count. In particular both free wires participate in the calculation.
-/

namespace FourColor.DiamondCoupledWiring.Rotation
open Mettapedia.GraphTheory.FourColor
open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition OpenTangleMarkedFace
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedSpliceFaceCount
open GoertzelV24FaceOrbitPartitionBridge OpenTangleReplacementEuler
open OpenTanglePortReplacement SerialTangleFaceCode FaceReturnSum SerialTangleFaceTransfer
open GoertzelV24FaceOrbitIncidence

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin 8))

def faceMarks : Dart I → Prop := Sum.elim Boundary (fun _ => True)

def faceCoordinate : {d : Dart I // faceMarks d} ≃ Fin 8 ⊕ Fin 6 :=
  Equiv.subtypeSum.trans
    (Equiv.sumCongr (boundaryCoordinate I (Fin 8)) (Equiv.subtypeUnivEquiv (fun _ => trivial)))

def before : Perm (Dart I) := Equiv.sumCongr (openPhi O) coreRotation

omit [Fintype V] [DecidableEq V] in
theorem face_return : (faceCoordinate (I := I)).permCongr
    (nextHitPerm (before O) faceMarks) = Equiv.sumCongr (returnCode O) coreRotation := by
  unfold before
  change (faceCoordinate (I := I)).permCongr
    (nextHitPerm (Equiv.sumCongr (openPhi O) coreRotation)
      (Sum.elim Boundary (fun _ => True))) = _
  rw [nextHitPerm_sum]
  apply Equiv.ext
  rintro (b | j)
  · rfl
  · change Sum.inr ((nextHitPerm coreRotation (fun _ => True) ⟨j, trivial⟩).1) = _
    rw [PermutationFirstReturnRestriction.nextHit_apply_of_step _ _ _ trivial]
    rfl

theorem face_phi (hs : Separated O) : (closed O hs).phi =
    before O * ofSubtype ((faceCoordinate (I := I)).symm.permCongr seam) := by
  change Equiv.sumCongr O.rho coreRotation * alpha O = _
  ext d
  simp only [Perm.mul_apply]
  rcases d with (i | b) | j
  · rw [ ofSubtype_apply_of_not_mem _ (by exact id : ¬ faceMarks (.inl (.inl i)))]
    rfl
  · rw [ ofSubtype_apply_of_mem _ (by trivial : faceMarks (.inl (.inr b)))]
    fin_cases b <;> rfl
  · rw [ ofSubtype_apply_of_mem _ (by trivial : faceMarks (.inr j))]
    fin_cases j <;> rfl

theorem face_count (hs : Separated O) :
    Fintype.card (OrbitFace (closed O hs)) +
      (partition (Equiv.sumCongr (returnCode O) coreRotation)).parts.card =
    (openPhi O).partition.parts.card + coreRotation.partition.parts.card +
      (partition (Equiv.sumCongr (returnCode O) coreRotation * seam)).parts.card := by
  let code := faceCoordinate (I := I)
  let r := nextHitPerm (before O) faceMarks
  let s := code.symm.permCongr seam
  have hr := card_permCongr_partition_parts code r
  rw [face_return] at hr
  have hs' : code.permCongr s = seam := code.permCongr.apply_symm_apply _
  have hrs := card_permCongr_partition_parts code (r * s)
  rw [Equiv.permCongr_mul, hs', face_return] at hrs
  have hh := BoundaryRewireCycles.cycle_count_rewire (before O) faceMarks s
  rw [← face_phi O hs, before, cycle_count_sum] at hh
  change Fintype.card (Quotient (SameCycle.setoid (closed O hs).phi)) + _ = _
  rw [card_permOrbit_eq_card_partition_parts]
  dsimp [r, s, before] at hr hrs
  dsimp [s] at hh
  omega

theorem face_count_opposite (hs : Separated O)
    (hr : returnCode O = (finRotate 8)⁻¹) :
    Fintype.card (OrbitFace (closed O hs)) = (openPhi O).partition.parts.card + 5 := by
  have h := face_count O hs
  rw [hr] at h
  have hc : coreRotation.partition.parts.card = 2 := by decide +kernel
  have ho : (partition (Equiv.sumCongr (finRotate 8)⁻¹ coreRotation)).parts.card = 3 := by
    decide +kernel
  have hn : (partition (Equiv.sumCongr (finRotate 8)⁻¹ coreRotation * seam)).parts.card = 6 := by
    decide +kernel
  omega

end
end FourColor.DiamondCoupledWiring.Rotation
