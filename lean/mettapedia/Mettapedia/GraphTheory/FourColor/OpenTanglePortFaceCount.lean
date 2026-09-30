import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement

/-! # Whole-map face counting from both ordered port returns

The count uses each open piece's interior face count and the exact joint
port permutation. Neither the number of interior darts nor the lengths of
the exterior facial arcs enter the boundary correction.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTanglePortFaceCount
open Equiv Equiv.Perm GoertzelV24OpenTangleComposition
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedSpliceFaceCount
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationSpliceConstructor GoertzelV24CompositeSeamMultigraph
open SerialTangleFaceTransfer SerialTangleFaceCode FaceReturnSum

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I J L R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def marks : (I ⊕ L) ⊕ (J ⊕ R) → Prop := Sum.elim Boundary Boundary

def coordinate : {d : (I ⊕ L) ⊕ (J ⊕ R) // marks d} ≃ L ⊕ R :=
  Equiv.subtypeSum.trans (Equiv.sumCongr (boundaryCoordinate I L) (boundaryCoordinate J R))

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
theorem seam_mark (d : (I ⊕ L) ⊕ (J ⊕ R)) (h : IsSeam d) : marks d := by
  rcases d with (i | l) | (j | r) <;> exact h

variable (O : OpenTangleData V I L) (P : OpenTangleData W J R) (m : L ≃ R)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem return_code : (coordinate (I := I) (J := J)).permCongr
    (nextHitPerm (Equiv.sumCongr (openPhi O) (openPhi P)) marks) =
      Equiv.sumCongr (returnCode O) (returnCode P) := by
  change (coordinate (I := I) (J := J)).permCongr
    (nextHitPerm (Equiv.sumCongr (openPhi O) (openPhi P)) (Sum.elim Boundary Boundary)) = _
  rw [nextHitPerm_sum]
  ext d
  cases d <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
theorem swap_code : (coordinate (I := I) (J := J)).permCongr
    (observedSwap m marks seam_mark) = MatchedSeam.seamSwap m := by
  ext d
  cases d <;> rfl

theorem face_count : Fintype.card (OrbitFace (O.composeRotationSystem P m)) +
    (partition (Equiv.sumCongr (returnCode O) (returnCode P))).parts.card =
      (openPhi O).partition.parts.card + (openPhi P).partition.parts.card +
      (partition (Equiv.sumCongr (returnCode O) (returnCode P) * MatchedSeam.seamSwap m)).parts.card := by
  let e := coordinate (I := I) (J := J) (L := L) (R := R)
  let r := nextHitPerm (Equiv.sumCongr (openPhi O) (openPhi P)) marks
  let s := observedSwap m marks (seam_mark (I := I) (J := J))
  have hr := card_permCongr_partition_parts e r
  rw [return_code] at hr
  have hs := card_permCongr_partition_parts e (r * s)
  rw [Equiv.permCongr_mul, return_code, swap_code] at hs
  have hh := observed_face_count O P m marks (seam_mark (I := I) (J := J))
  change Fintype.card (OrbitFace (O.composeRotationSystem P m)) + _ = _ at hh
  dsimp [r, s] at hr hs
  omega

end
end Mettapedia.GraphTheory.FourColor.OpenTanglePortFaceCount
