import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder

/-!
# Adjacent returns for an oppositely ordered splice seam

Addendum XXVII's splice checklist takes profiles on simple transversals and
requires the matching to be a homeomorphism of the complementary pieces.  This
module isolates the finite return-permutation calculation behind that
noncrossing obligation.  For either orientation of an ordered boundary, the
capped return is an involution.  A return cycle containing two distinct roots
has one root on each side, and their offsets are necessarily adjacent.

The result holds at arbitrary interface width.  It is not a construction of
the source crosscuts and it does not assert edge-disjointness of the geometric
seam arcs.  Its role is to reduce that remaining source-geometric obligation
from arbitrary pairs of seam roots to neighboring strips of the long,
end-capped corridor supplied downstream of Lean flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RotationSpliceConstructor

namespace GoertzelV24OrderedSeamReturnAdjacency

/-- Every cycle of an involutive permutation has one or two points. -/
theorem sameCycle_iff_eq_or_apply_of_sq_eq_one
    {A : Type*} [Finite A] (perm : Equiv.Perm A)
    (hsq : perm ^ 2 = 1) (first second : A) :
    perm.SameCycle first second ↔ first = second ∨ perm first = second := by
  constructor
  · intro hcycle
    rcases hcycle.exists_pow_eq' with ⟨power, hpower, heq⟩
    have horder : orderOf perm ≤ 2 :=
      orderOf_le_of_pow_eq_one (by omega) hsq
    have : power = 0 ∨ power = 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl (by simpa using heq)
    · exact Or.inr (by simpa using heq)
  · rintro (rfl | hstep)
    · exact Equiv.Perm.SameCycle.refl perm first
    · exact ⟨1, by simpa using hstep⟩

theorem apply_eq_iff_reverse_apply_eq_of_sq_eq_one
    {A : Type*} (perm : Equiv.Perm A) (hsq : perm ^ 2 = 1)
    (first second : A) :
    perm first = second ↔ perm second = first := by
  have hinvolutive (position : A) : perm (perm position) = position := by
    have hpoint := DFunLike.congr_fun hsq position
    simpa [pow_two, Equiv.Perm.mul_apply] using hpoint
  constructor
  · intro hstep
    calc
      perm second = perm (perm first) := by rw [hstep]
      _ = first := hinvolutive first
  · intro hstep
    calc
      perm first = perm (perm second) := by rw [hstep]
      _ = second := hinvolutive second

/-- The positive-boundary capped return is an involution at every width. -/
theorem forward_sq (n : Nat) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n) ^ 2 = 1 := by
  let coordinates := oppositeBoundaryPositionEquiv n
  apply coordinates.permCongrHom.injective
  rw [map_pow, map_one]
  change (coordinates.permCongr
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n)) ^ 2 = 1
  rw [oppositeBoundary_capPerm_congr,
    finRotate_mul_revPerm_eq_neg, negFin_perm_sq]

theorem inv_mul_involution_sq_of_mul_sq
    {A : Type*} (boundary cap : Equiv.Perm A)
    (hforward : (boundary * cap) ^ 2 = 1)
    (hcap : cap ^ 2 = 1) :
    (boundary⁻¹ * cap) ^ 2 = 1 := by
  have hword : boundary * cap * boundary * cap = 1 := by
    simpa [pow_two, mul_assoc] using hforward
  have hcapWord : cap * cap = 1 := by
    simpa [pow_two] using hcap
  have hthree : cap * boundary * cap = boundary⁻¹ := by
    calc
      cap * boundary * cap =
          boundary⁻¹ * (boundary * cap * boundary * cap) := by group
      _ = boundary⁻¹ * 1 := by rw [hword]
      _ = boundary⁻¹ := by simp
  have hcommute : cap * boundary = boundary⁻¹ * cap := by
    calc
      cap * boundary = (cap * boundary) * (cap * cap) := by
        rw [hcapWord, mul_one]
      _ = (cap * boundary * cap) * cap := by group
      _ = boundary⁻¹ * cap := by rw [hthree]
  calc
    (boundary⁻¹ * cap) ^ 2 = (cap * boundary) ^ 2 := by rw [hcommute]
    _ = cap * boundary * cap * boundary := by simp only [pow_two]; group
    _ = boundary⁻¹ * boundary := by rw [hthree]
    _ = 1 := by simp

theorem inv_mul_cap_eq_cap_mul_forward_mul_cap
    {A : Type*} (boundary cap : Equiv.Perm A)
    (hforward : (boundary * cap) ^ 2 = 1) :
    boundary⁻¹ * cap = cap * (boundary * cap) * cap := by
  have hword : boundary * cap * boundary * cap = 1 := by
    simpa [pow_two, mul_assoc] using hforward
  have hthree : cap * boundary * cap = boundary⁻¹ := by
    calc
      cap * boundary * cap =
          boundary⁻¹ * (boundary * cap * boundary * cap) := by group
      _ = boundary⁻¹ * 1 := by rw [hword]
      _ = boundary⁻¹ := by simp
  calc
    boundary⁻¹ * cap = (cap * boundary * cap) * cap := by rw [hthree]
    _ = cap * (boundary * cap) * cap := by group

/-- Reversing the boundary orientation again gives an involutive return. -/
theorem inverse_sq (n : Nat) :
    ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n) ^ 2 = 1 := by
  apply inv_mul_involution_sq_of_mul_sq
  · exact forward_sq n
  · apply Equiv.ext
    intro position
    rcases position with step | step <;> rfl

theorem forward_apply_inl_eq_inr_iff {n : Nat}
    (left right : Fin n) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inl left) =
        Sum.inr right ↔
      left.val = right.val + 1 := by
  letI : NeZero (n + n) := ⟨by have := left.isLt; omega⟩
  let coordinates := oppositeBoundaryPositionEquiv n
  have hcongr : coordinates.permCongr
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) =
      (Equiv.neg (Fin (n + n)) : Equiv.Perm (Fin (n + n))) := by
    rw [oppositeBoundary_capPerm_congr, finRotate_mul_revPerm_eq_neg]
  have happly := DFunLike.congr_fun hcongr (coordinates (Sum.inl left))
  have happly' : coordinates
      ((oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inl left)) =
      -(coordinates (Sum.inl left)) := by
    simpa [coordinates, Equiv.permCongr_apply] using happly
  constructor
  · intro heq
    have heq' := congrArg coordinates heq
    rw [happly'] at heq'
    simp only [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv] at heq'
    have heqVal := congrArg Fin.val heq'
    simp [Fin.val_neg] at heqVal
    split at heqVal <;> rename_i hzero <;> omega
  · intro hval
    apply coordinates.injective
    rw [happly']
    simp only [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv]
    apply Fin.ext
    simp [Fin.val_neg]
    split
    · rename_i hzero
      have hzeroVal := congrArg Fin.val hzero
      simp at hzeroVal
      omega
    · omega

theorem forward_apply_inr_eq_inl_iff {n : Nat}
    (right left : Fin n) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inr right) =
        Sum.inl left ↔
      left.val = right.val + 1 := by
  letI : NeZero (n + n) := ⟨by have := left.isLt; omega⟩
  let coordinates := oppositeBoundaryPositionEquiv n
  have hcongr : coordinates.permCongr
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) =
      (Equiv.neg (Fin (n + n)) : Equiv.Perm (Fin (n + n))) := by
    rw [oppositeBoundary_capPerm_congr, finRotate_mul_revPerm_eq_neg]
  have happly := DFunLike.congr_fun hcongr (coordinates (Sum.inr right))
  have happly' : coordinates
      ((oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inr right)) =
      -(coordinates (Sum.inr right)) := by
    simpa [coordinates, Equiv.permCongr_apply] using happly
  constructor
  · intro heq
    have heq' := congrArg coordinates heq
    rw [happly'] at heq'
    simp only [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv] at heq'
    have heqVal := congrArg Fin.val heq'
    simp [Fin.val_neg] at heqVal
    split at heqVal
    · rename_i hzero
      have hzeroVal := congrArg Fin.val hzero
      simp at hzeroVal
      omega
    · omega
  · intro hval
    apply coordinates.injective
    rw [happly']
    simp only [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv]
    apply Fin.ext
    simp [Fin.val_neg]
    split
    · rename_i hzero
      have hzeroVal := congrArg Fin.val hzero
      simp at hzeroVal
      omega
    · omega

theorem forward_apply_inl_eq_inl_imp {n : Nat}
    (first second : Fin n)
    (hstep :
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inl first) =
        Sum.inl second) :
    first = second := by
  letI : NeZero (n + n) := ⟨by have := first.isLt; omega⟩
  let coordinates := oppositeBoundaryPositionEquiv n
  have hcongr : coordinates.permCongr
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) =
      (Equiv.neg (Fin (n + n)) : Equiv.Perm (Fin (n + n))) := by
    rw [oppositeBoundary_capPerm_congr, finRotate_mul_revPerm_eq_neg]
  have happly := DFunLike.congr_fun hcongr (coordinates (Sum.inl first))
  have happly' : coordinates
      ((oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inl first)) =
      -(coordinates (Sum.inl first)) := by
    simpa [coordinates, Equiv.permCongr_apply] using happly
  have heq := congrArg coordinates hstep
  rw [happly'] at heq
  simp only [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv] at heq
  have heqVal := congrArg Fin.val heq
  simp [Fin.val_neg] at heqVal
  split at heqVal
  · rename_i hzero
    apply Fin.ext
    have hzeroVal := congrArg Fin.val hzero
    simp at hzeroVal
    omega
  · omega

theorem forward_apply_inr_eq_inr_imp {n : Nat}
    (first second : Fin n)
    (hstep :
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inr first) =
        Sum.inr second) :
    first = second := by
  letI : NeZero (n + n) := ⟨by have := first.isLt; omega⟩
  let coordinates := oppositeBoundaryPositionEquiv n
  have hcongr : coordinates.permCongr
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) =
      (Equiv.neg (Fin (n + n)) : Equiv.Perm (Fin (n + n))) := by
    rw [oppositeBoundary_capPerm_congr, finRotate_mul_revPerm_eq_neg]
  have happly := DFunLike.congr_fun hcongr (coordinates (Sum.inr first))
  have happly' : coordinates
      ((oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inr first)) =
      -(coordinates (Sum.inr first)) := by
    simpa [coordinates, Equiv.permCongr_apply] using happly
  have heq := congrArg coordinates hstep
  rw [happly'] at heq
  simp only [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv] at heq
  have heqVal := congrArg Fin.val heq
  simp [Fin.val_neg] at heqVal
  split at heqVal
  · rename_i hzero
    have hzeroVal := congrArg Fin.val hzero
    simp at hzeroVal
    omega
  · apply Fin.ext
    omega

theorem inverse_apply_inl_eq_inr_iff {n : Nat}
    (left right : Fin n) :
    ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n) (Sum.inl left) =
        Sum.inr right ↔
      right.val = left.val + 1 := by
  letI : NeZero (n + n) := ⟨by have := left.isLt; omega⟩
  let coordinates := oppositeBoundaryPositionEquiv n
  let returnPerm : Equiv.Perm (Fin (n + n)) :=
    (finRotate (n + n))⁻¹ * Fin.revPerm
  have hboundary : coordinates.permCongrHom (oppositeBoundaryCycle n) =
      finRotate (n + n) := by
    apply Equiv.ext
    intro position
    simp [coordinates, oppositeBoundaryCycle, Equiv.permCongr_apply]
  have hcap : coordinates.permCongrHom (orderedPositionSeamSwap n) =
      Fin.revPerm :=
    oppositeBoundaryPosition_seamSwap_eq_revPerm n
  have hcongr : coordinates.permCongr
      ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n) =
      returnPerm := by
    dsimp only [returnPerm]
    change coordinates.permCongrHom
      ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n) = _
    rw [map_mul, map_inv, hboundary, hcap]
  have happly := DFunLike.congr_fun hcongr (coordinates (Sum.inl left))
  have happly' : coordinates
      (((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
        (Sum.inl left)) =
      returnPerm (coordinates (Sum.inl left)) := by
    simpa [coordinates, Equiv.permCongr_apply] using happly
  have hrevne :
      Fin.revPerm (coordinates (Sum.inl left)) ≠ 0 := by
    intro hzero
    have hzeroVal := congrArg Fin.val hzero
    simp [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv,
      Fin.revPerm, Fin.rev] at hzeroVal
    omega
  have hreturnVal :
      (returnPerm (coordinates (Sum.inl left))).val =
        (Fin.revPerm (coordinates (Sum.inl left))).val - 1 := by
    simpa [returnPerm, Equiv.Perm.mul_apply] using
      (coe_finRotate_symm_of_ne_zero hrevne)
  constructor
  · intro heq
    have heq' := congrArg coordinates heq
    rw [happly'] at heq'
    have heqVal := congrArg Fin.val heq'
    rw [hreturnVal] at heqVal
    simp [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv,
      Fin.revPerm, Fin.rev] at heqVal
    omega
  · intro hval
    apply coordinates.injective
    rw [happly']
    apply Fin.ext
    rw [hreturnVal]
    simp [coordinates, oppositeBoundaryPositionEquiv, finSumFinEquiv,
      Fin.revPerm, Fin.rev]
    omega

theorem inverse_apply_inr_eq_inl_iff {n : Nat}
    (right left : Fin n) :
    ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n) (Sum.inr right) =
        Sum.inl left ↔
      right.val = left.val + 1 := by
  rw [apply_eq_iff_reverse_apply_eq_of_sq_eq_one _ (inverse_sq n),
    inverse_apply_inl_eq_inr_iff]

theorem inverse_apply_inl_eq_inl_imp {n : Nat}
    (first second : Fin n)
    (hstep :
      ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
          (Sum.inl first) = Sum.inl second) :
    first = second := by
  have hinverse := inv_mul_cap_eq_cap_mul_forward_mul_cap
    (oppositeBoundaryCycle n) (orderedPositionSeamSwap n) (forward_sq n)
  rw [hinverse] at hstep
  have hforward :
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inr first) =
        Sum.inr second := by
    apply (orderedPositionSeamSwap n).injective
    simpa [Equiv.Perm.mul_apply, orderedPositionSeamSwap,
      MatchedSeam.seamSwap] using hstep
  exact forward_apply_inr_eq_inr_imp first second hforward

theorem inverse_apply_inr_eq_inr_imp {n : Nat}
    (first second : Fin n)
    (hstep :
      ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
          (Sum.inr first) = Sum.inr second) :
    first = second := by
  have hinverse := inv_mul_cap_eq_cap_mul_forward_mul_cap
    (oppositeBoundaryCycle n) (orderedPositionSeamSwap n) (forward_sq n)
  rw [hinverse] at hstep
  have hforward :
      (oppositeBoundaryCycle n * orderedPositionSeamSwap n) (Sum.inl first) =
        Sum.inl second := by
    apply (orderedPositionSeamSwap n).injective
    simpa [Equiv.Perm.mul_apply, orderedPositionSeamSwap,
      MatchedSeam.seamSwap] using hstep
  exact forward_apply_inl_eq_inl_imp first second hforward

/-- In the positive orientation, a left/right pair shares a face exactly at
consecutive offsets, with the left root one step ahead. -/
theorem forward_sameCycle_inl_inr_iff {n : Nat}
    (left right : Fin n) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n).SameCycle
        (Sum.inl left) (Sum.inr right) ↔
      left.val = right.val + 1 := by
  rw [sameCycle_iff_eq_or_apply_of_sq_eq_one _ (forward_sq n)]
  constructor
  · rintro (heq | hstep)
    · cases heq
    · exact (forward_apply_inl_eq_inr_iff left right).mp hstep
  · intro hindex
    exact Or.inr ((forward_apply_inl_eq_inr_iff left right).mpr hindex)

/-- In the reverse orientation, the neighboring-offset relation reverses. -/
theorem inverse_sameCycle_inl_inr_iff {n : Nat}
    (left right : Fin n) :
    ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n).SameCycle
        (Sum.inl left) (Sum.inr right) ↔
      right.val = left.val + 1 := by
  rw [sameCycle_iff_eq_or_apply_of_sq_eq_one _ (inverse_sq n)]
  constructor
  · rintro (heq | hstep)
    · cases heq
    · exact (inverse_apply_inl_eq_inr_iff left right).mp hstep
  · intro hindex
    exact Or.inr ((inverse_apply_inl_eq_inr_iff left right).mpr hindex)

/-- In the positive orientation, two left roots share a cycle only when equal. -/
theorem forward_sameCycle_inl_inl_iff {n : Nat}
    (first second : Fin n) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n).SameCycle
        (Sum.inl first) (Sum.inl second) ↔
      first = second := by
  rw [sameCycle_iff_eq_or_apply_of_sq_eq_one _ (forward_sq n)]
  constructor
  · rintro (heq | hstep)
    · exact Sum.inl.inj heq
    · exact forward_apply_inl_eq_inl_imp first second hstep
  · intro heq
    exact Or.inl (congrArg Sum.inl heq)

/-- In the positive orientation, two right roots share a cycle only when equal. -/
theorem forward_sameCycle_inr_inr_iff {n : Nat}
    (first second : Fin n) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n).SameCycle
        (Sum.inr first) (Sum.inr second) ↔
      first = second := by
  rw [sameCycle_iff_eq_or_apply_of_sq_eq_one _ (forward_sq n)]
  constructor
  · rintro (heq | hstep)
    · exact Sum.inr.inj heq
    · exact forward_apply_inr_eq_inr_imp first second hstep
  · intro heq
    exact Or.inl (congrArg Sum.inr heq)

/-- The reverse orientation also has no distinct same-side left pair. -/
theorem inverse_sameCycle_inl_inl_iff {n : Nat}
    (first second : Fin n) :
    ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n).SameCycle
        (Sum.inl first) (Sum.inl second) ↔
      first = second := by
  rw [sameCycle_iff_eq_or_apply_of_sq_eq_one _ (inverse_sq n)]
  constructor
  · rintro (heq | hstep)
    · exact Sum.inl.inj heq
    · exact inverse_apply_inl_eq_inl_imp first second hstep
  · intro heq
    exact Or.inl (congrArg Sum.inl heq)

/-- The reverse orientation also has no distinct same-side right pair. -/
theorem inverse_sameCycle_inr_inr_iff {n : Nat}
    (first second : Fin n) :
    ((oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n).SameCycle
        (Sum.inr first) (Sum.inr second) ↔
      first = second := by
  rw [sameCycle_iff_eq_or_apply_of_sq_eq_one _ (inverse_sq n)]
  constructor
  · rintro (heq | hstep)
    · exact Sum.inr.inj heq
    · exact inverse_apply_inr_eq_inr_imp first second hstep
  · intro heq
    exact Or.inl (congrArg Sum.inr heq)
end GoertzelV24OrderedSeamReturnAdjacency

end Mettapedia.GraphTheory.FourColor
