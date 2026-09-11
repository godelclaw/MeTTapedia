import Mettapedia.GraphTheory.FourColor.BoundaryRewireCycles
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSphericity

/-!
# Boundary-cycle formula for the actual open-tangle composite

Temporarily fixing every unpaired boundary dart defines an unsewn face
permutation. The actual composed rotation system changes it by the lifted
seam matching. Consequently its total face-count change is precisely the
cycle-count change on the complete boundary first-return permutation.
No assumption of disc sides or a single boundary cycle is made.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleRewireFaces

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationSpliceConstructor GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity GoertzelV24SeamFaceArc
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedSpliceFaceCount
open GoertzelV24FaceOrbitPartitionBridge BoundaryRewireCycles

noncomputable section
variable {V W I L J R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

local instance : DecidablePred (IsSeamDart (I := I ⊕ J) (L := L) (R := R)) :=
  fun d => match d with
    | Sum.inl _ => isFalse id
    | Sum.inr _ => isTrue trivial

def unsewnPhi (left : OpenTangleData V I L) (right : OpenTangleData W J R) :
    Perm (MatchedSeam.Dart (I ⊕ J) L R) :=
  composeDartEquiv.permCongr (Equiv.sumCongr left.rho right.rho) *
    Equiv.sumCongr (Equiv.sumCongr left.interiorAlpha right.interiorAlpha) 1

def seamPerm (matching : L ≃ R) : Perm {d : MatchedSeam.Dart (I ⊕ J) L R // IsSeamDart d} :=
  seamDartEquiv.permCongr (MatchedSeam.seamSwap matching)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
theorem ofSubtype_seamPerm (matching : L ≃ R) :
    ofSubtype (seamPerm (I := I) (J := J) matching) =
      Equiv.sumCongr (1 : Perm (I ⊕ J)) (MatchedSeam.seamSwap matching) := by
  classical
  ext d
  rcases d with (i | j) | (l | r)
  · rw [ofSubtype_apply_of_not_mem _ (by simp [IsSeamDart])]
    rfl
  · rw [ofSubtype_apply_of_not_mem _ (by simp [IsSeamDart])]
    rfl
  · rw [ofSubtype_apply_of_mem _ (isSeamDart_left l)]
    rfl
  · rw [ofSubtype_apply_of_mem _ (isSeamDart_right r)]
    rfl

/-- Identification with the stored composite, not an extra face-law input. -/
theorem compositePhi_eq_unsewn_mul
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (matching : L ≃ R) :
    compositePhi left right matching =
      unsewnPhi left right * ofSubtype (seamPerm (I := I) (J := J) matching) := by
  classical
  rw [ofSubtype_seamPerm]
  ext d
  rcases d with (i | j) | (l | r) <;>
    simp [compositePhi, compositeDarts, MatchedSeam.Data.toRewiredDartSystem,
      composeData, unsewnPhi, Perm.mul_apply, Equiv.permCongr_apply]

/-- The boundary state is computed by first return through the two pieces. -/
def boundaryReturn (left : OpenTangleData V I L) (right : OpenTangleData W J R) :
    Perm {d : MatchedSeam.Dart (I ⊕ J) L R // IsSeamDart d} :=
  nextHitPerm (unsewnPhi left right) IsSeamDart

theorem composite_face_count
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (matching : L ≃ R) :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right matching)) +
        (boundaryReturn left right).partition.parts.card =
      (unsewnPhi left right).partition.parts.card +
        (boundaryReturn left right * seamPerm matching).partition.parts.card := by
  classical
  have h := cycle_count_rewire (unsewnPhi left right) IsSeamDart
    (seamPerm (I := I) (J := J) matching)
  rw [← compositePhi_eq_unsewn_mul] at h
  change Fintype.card (Quotient (SameCycle.setoid (compositePhi left right matching))) + _ = _
  rw [card_permOrbit_eq_card_partition_parts]
  exact h

/-- For fixed pieces, arbitrary matching choices have the same face count
exactly when the corresponding finite boundary permutations do. -/
theorem composite_faces_eq_iff
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (m n : L ≃ R) :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right m)) =
        Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right n)) ↔
      (boundaryReturn left right * seamPerm m).partition.parts.card =
        (boundaryReturn left right * seamPerm n).partition.parts.card := by
  have hm := composite_face_count left right m
  have hn := composite_face_count left right n
  omega

/-- Remove the ambient dart type from the interface state altogether. -/
def boundaryCode (left : OpenTangleData V I L) (right : OpenTangleData W J R) : Perm (L ⊕ R) :=
  seamDartEquiv.symm.permCongr (boundaryReturn left right)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem boundary_code_cycle_count
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (matching : L ≃ R) :
    (boundaryCode left right * MatchedSeam.seamSwap matching).partition.parts.card =
      (boundaryReturn left right * seamPerm matching).partition.parts.card := by
  let e := seamDartEquiv (I := I ⊕ J) (L := L) (R := R)
  have hs : e.symm.permCongr (seamPerm (I := I) (J := J) matching) =
      MatchedSeam.seamSwap matching := e.permCongr.symm_apply_apply _
  calc
    _ = (e.symm.permCongr (boundaryReturn left right * seamPerm matching)).partition.parts.card := by
      rw [Equiv.permCongr_mul, hs]
      rfl
    _ = _ := card_permCongr_partition_parts e.symm _

theorem composite_faces_eq_iff_code
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (m n : L ≃ R) :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right m)) =
        Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right n)) ↔
      (boundaryCode left right * MatchedSeam.seamSwap m).partition.parts.card =
        (boundaryCode left right * MatchedSeam.seamSwap n).partition.parts.card := by
  rw [boundary_code_cycle_count, boundary_code_cycle_count]
  exact composite_faces_eq_iff left right m n

theorem card_boundary_codes : Fintype.card (Perm (L ⊕ R)) =
    (Fintype.card L + Fintype.card R).factorial := by
  simp [Fintype.card_perm]

/-- Replacing the matching changes partners but never the edge count. -/
theorem composite_edge_count_eq
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (m n : L ≃ R) :
    Fintype.card (compositeDarts left right m).Edge =
      Fintype.card (compositeDarts left right n).Edge := by
  have hm := two_mul_card_edge (compositeRS left right m)
  have hn := two_mul_card_edge (compositeRS left right n)
  change 2 * Fintype.card (compositeDarts left right m).Edge =
    Fintype.card (MatchedSeam.Dart (I ⊕ J) L R) at hm
  change 2 * Fintype.card (compositeDarts left right n).Edge =
    Fintype.card (MatchedSeam.Dart (I ⊕ J) L R) at hn
  omega

def compositeEuler
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (m : L ≃ R) : ℤ :=
  Fintype.card (V ⊕ W) - (Fintype.card (compositeDarts left right m).Edge : ℤ) +
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right m))

/-- Euler change under a matching choice is decided by the finite boundary
code. Connectedness and bridgelessness remain separate properties. -/
theorem composite_euler_eq_iff_code
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) (m n : L ≃ R) :
    compositeEuler left right m = compositeEuler left right n ↔
      (boundaryCode left right * MatchedSeam.seamSwap m).partition.parts.card =
        (boundaryCode left right * MatchedSeam.seamSwap n).partition.parts.card := by
  rw [← composite_faces_eq_iff_code, compositeEuler, compositeEuler,
    composite_edge_count_eq left right m n]
  omega

end
end Mettapedia.GraphTheory.FourColor.OpenTangleRewireFaces
