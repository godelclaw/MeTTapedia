import Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction

/-!
# Face return and Euler correction for literal serial composition

Keep all input boundary darts during sewing, then forget the consumed
seam. Both the outgoing return permutation and the change in the total
number of face cycles are determined by this boundary calculation.
Internal face cycles are counted, not silently assumed absent. No sphere,
connectedness, or uniform interface-width hypothesis is used.
-/

namespace Mettapedia.GraphTheory.FourColor.SerialTangleFaceTransfer

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedRegionBoundaryOrder
open SerialTangleSmallCutTransfer OpenTangleMarkedFace
open PermutationFirstReturnRestriction BoundaryRewireCycles
open GoertzelV24FaceOrbitPartitionBridge OpenTangleReplacementEuler
open GoertzelV24RetainedSpliceFaceCount

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L P R : Type*}

abbrev Source (I J L P R : Type*) := (I ⊕ (L ⊕ P)) ⊕ (J ⊕ (P ⊕ R))

def Boundary {I B : Type*} : I ⊕ B → Prop
  | .inl _ => False
  | .inr _ => True

def AllBoundary : Source I J L P R → Prop := Sum.elim Boundary Boundary

def External : Source I J L P R → Prop
  | .inl (.inr (.inl _)) => True
  | .inr (.inr (.inr _)) => True
  | _ => False

theorem external_boundary (d : Source I J L P R) (h : External d) : AllBoundary d := by
  rcases d with (i | (l | p)) | (j | (p | r)) <;>
    simp_all [External, AllBoundary, Boundary]

/-- Only the two seam copies change partners; the exterior stays open. -/
def swap : Perm (Source I J L P R) where
  toFun
    | .inl (.inr (.inr p)) => .inr (.inr (.inl p))
    | .inr (.inr (.inl p)) => .inl (.inr (.inr p))
    | d => d
  invFun
    | .inl (.inr (.inr p)) => .inr (.inr (.inl p))
    | .inr (.inr (.inl p)) => .inl (.inr (.inr p))
    | d => d
  left_inv := by rintro ((i | (l | p)) | (j | (p | r))) <;> rfl
  right_inv := by rintro ((i | (l | p)) | (j | (p | r))) <;> rfl

def boundarySwap : Perm {d : Source I J L P R // AllBoundary d} :=
  swap.subtypePerm (by rintro ((i | (l | p)) | (j | (p | r))) <;> rfl)

theorem boundarySwap_extend :
    ofSubtype (boundarySwap (I := I) (J := J) (L := L) (P := P) (R := R)) = swap := by
  apply ofSubtype_subtypePerm
  rintro ((i | (l | p)) | (j | (p | r))) h <;> simp_all [swap, AllBoundary, Boundary]

variable (A : TwoSidedOpenTangleData V I L P) (B : TwoSidedOpenTangleData W J P R)

def before : Perm (Source I J L P R) := Equiv.sumCongr (openPhi (asOpen A)) (openPhi (asOpen B))

/-- The exact permutation of the existing serial constructor. -/
theorem serial_phi :
    openPhi (asOpen (A.serialCompose B (Equiv.refl P))) =
      serialDartEquiv.permCongr (before A B * swap) := by
  apply Equiv.ext
  intro d
  obtain ⟨x, rfl⟩ := serialDartEquiv.surjective d
  rcases x with (i | (l | p)) | (j | (p | r)) <;> rfl

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R]

def combinedReturn : Perm {d : Source I J L P R // AllBoundary d} :=
  nextHitPerm (before A B) AllBoundary

/-- Input records combine by disjoint union before the seam rewire. -/
theorem combinedReturn_eq : combinedReturn A B =
    Equiv.subtypeSum.symm.permCongr
      (Equiv.sumCongr (nextHitPerm (openPhi (asOpen A)) Boundary)
        (nextHitPerm (openPhi (asOpen B)) Boundary)) :=
  FaceReturnSum.nextHitPerm_sum _ _ _ _

/-- Rewire at all old ports, then restrict to the unconsumed ports. -/
def outputReturn : Perm {d : Source I J L P R // External d} :=
  (nestedMarks External AllBoundary external_boundary).symm.permCongr
    (nextHitPerm (combinedReturn A B * boundarySwap) (fun d => External d.1))

theorem outputReturn_eq : outputReturn A B = nextHitPerm (before A B * swap) External := by
  have h := nextHit_nested (before A B * swap) External AllBoundary external_boundary
  rw [← boundarySwap_extend, nextHitPerm_mul_ofSubtype] at h
  rw [boundarySwap_extend] at h
  apply (nestedMarks External AllBoundary external_boundary).permCongr.injective
  rw [← h]
  ext d
  simp [outputReturn, combinedReturn, Equiv.permCongr_apply]

/-- The computed outgoing return is the actual next boundary dart of the
serial tangle, with literal port identities retained. -/
theorem serial_return (d : {d : Source I J L P R // External d}) :
    (nextHitPerm (openPhi (asOpen (A.serialCompose B (Equiv.refl P)))) Boundary
      ⟨serialDartEquiv d.1, by
        rcases d with ⟨(i | (l | p)) | (j | (p | r)), h⟩ <;> exact h⟩).1 =
      serialDartEquiv (outputReturn A B d).1 := by
  rw [outputReturn_eq]
  apply PermutationFirstReturnRestriction.nextHit_map
  · intro x
    rw [serial_phi]
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  · rintro ((i | (l | p)) | (j | (p | r))) <;> rfl

/-- Exact face-cycle correction, including cycles that become closed when
the seam is forgotten. Natural-number subtraction is deliberately avoided. -/
theorem serial_face_count :
    (openPhi (asOpen (A.serialCompose B (Equiv.refl P)))).partition.parts.card +
        (combinedReturn A B).partition.parts.card =
      (openPhi (asOpen A)).partition.parts.card + (openPhi (asOpen B)).partition.parts.card +
        (combinedReturn A B * boundarySwap).partition.parts.card := by
  have h := cycle_count_rewire (before A B) AllBoundary boundarySwap
  rw [boundarySwap_extend] at h
  rw [serial_phi, card_permCongr_partition_parts]
  simpa only [combinedReturn, before, cycle_count_sum] using h

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
/-- Euler mass updates using boundary cycle counts and seam arity alone.
The integer mass is not asserted to have finite range for arbitrary tangles. -/
theorem serial_eulerMass :
    eulerMass (asOpen (A.serialCompose B (Equiv.refl P))) +
        2 * ((combinedReturn A B).partition.parts.card : ℤ) + 2 * Fintype.card P =
      eulerMass (asOpen A) + eulerMass (asOpen B) +
        2 * ((combinedReturn A B * boundarySwap).partition.parts.card : ℤ) := by
  have h := serial_face_count A B
  simp only [eulerMass, Fintype.card_sum]
  omega

end
end Mettapedia.GraphTheory.FourColor.SerialTangleFaceTransfer
