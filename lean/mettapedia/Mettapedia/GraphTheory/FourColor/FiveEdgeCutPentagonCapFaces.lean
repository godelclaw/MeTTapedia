import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount

/-!
# Face count of the pentagon-capped shore

Faces are counted through the first return of the capped face permutation
to the old retained darts.  Internal darts return in one step; a boundary
dart passes through an incoming cycle dart and the next spoke, returning
in three steps to the next boundary position — so against the facial
first-return order the five sector faces close one per position.  The
five outgoing cycle darts form one face cycle of their own, the inner
pentagon, which never meets a retained dart.  The complete count is
therefore six new faces plus the untouched ambient faces.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

namespace FiveEdgeCutPentagonCapData

noncomputable section

variable {RS : RotationSystem V E} (data : FiveEdgeCutPentagonCapData RS)

/-! ## The transported edge flip and face permutation -/

/-- The cap edge flip transported to the reassociated carrier. -/
def capTargetAlpha :
    Equiv.Perm (RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :=
  data.capDartEquiv.permCongr data.capRotationSystem.alpha

/-- The cap face permutation transported to the reassociated carrier. -/
def capTargetPhi :
    Equiv.Perm (RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :=
  data.capDartEquiv.permCongr data.capRotationSystem.phi

@[simp]
theorem capTargetAlpha_internal (dart : InternalDart RS data.keep) :
    data.capTargetAlpha (Sum.inl dart.1) =
      Sum.inl (internalAlpha RS data.keep dart).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained dart.1)) = _
  rw [data.capDartOfRetained_internal,
    data.capRewiredDartSystem_alpha_internal]
  rfl

@[simp]
theorem capTargetAlpha_boundary (position : Fin 5) :
    data.capTargetAlpha
        (Sum.inl (data.crossingBoundaryDartEquiv position).1) =
      Sum.inr (Sum.inr position) := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained
          (data.crossingBoundaryDartEquiv position).1)) = _
  rw [data.capDartOfRetained_boundary,
    data.capRewiredDartSystem_alpha_boundary]
  rfl

@[simp]
theorem capTargetAlpha_cycle (dart : Fin 5 × Bool) :
    data.capTargetAlpha (Sum.inr (Sum.inl dart)) =
      Sum.inr (Sum.inl (pentagonCyclePairing dart)) := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha (Sum.inl (Sum.inr dart))) = _
  rw [data.capRewiredDartSystem_alpha_cycle]
  rfl

@[simp]
theorem capTargetAlpha_spoke (j : Fin 5) :
    data.capTargetAlpha (Sum.inr (Sum.inr j)) =
      Sum.inl (data.crossingBoundaryDartEquiv j).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha (Sum.inr (Sum.inr j))) = _
  rw [data.capRewiredDartSystem_alpha_spoke,
    data.capDartEquiv_boundary]

theorem capTargetPhi_apply
    (dart : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :
    data.capTargetPhi dart =
      data.capTargetRho (data.capTargetAlpha dart) := by
  unfold capTargetPhi capTargetAlpha
  simp only [Equiv.permCongr_apply, RotationSystem.phi]
  change data.capDartEquiv
      (data.capRho (data.capRewiredDartSystem.alpha
        (data.capDartEquiv.symm dart))) =
    data.capTargetRho
      (data.capDartEquiv (data.capRewiredDartSystem.alpha
        (data.capDartEquiv.symm dart)))
  rw [data.capDartEquiv_capRho]

@[simp]
theorem capTargetPhi_internal (dart : InternalDart RS data.keep) :
    data.capTargetPhi (Sum.inl dart.1) =
      Sum.inl (retainedRho RS data.keep
        (internalAlpha RS data.keep dart).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_internal]
  rfl

@[simp]
theorem capTargetPhi_boundary (position : Fin 5) :
    data.capTargetPhi
        (Sum.inl (data.crossingBoundaryDartEquiv position).1) =
      Sum.inr (Sum.inl (position, true)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_boundary]
  rfl

@[simp]
theorem capTargetPhi_cycleTrue (j : Fin 5) :
    data.capTargetPhi (Sum.inr (Sum.inl (j, true))) =
      Sum.inr (Sum.inr (j + 1)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_cycle]
  rfl

@[simp]
theorem capTargetPhi_cycleFalse (j : Fin 5) :
    data.capTargetPhi (Sum.inr (Sum.inl (j, false))) =
      Sum.inr (Sum.inl (j - 1, false)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_cycle]
  rfl

@[simp]
theorem capTargetPhi_spoke (j : Fin 5) :
    data.capTargetPhi (Sum.inr (Sum.inr j)) =
      Sum.inl (retainedRho RS data.keep
        (data.crossingBoundaryDartEquiv j).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_spoke]
  rfl

/-! ## First return to the old retained darts -/

/-- Predicate selecting the transported old retained darts. -/
def IsTargetRetained :
    RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

instance isTargetRetainedDecidablePred :
    DecidablePred data.IsTargetRetained
  | Sum.inl _ => isTrue trivial
  | Sum.inr _ => isFalse id

/-- The marked old-dart subtype is canonically the retained-dart carrier. -/
def targetRetainedEquiv :
    {point // data.IsTargetRetained point} ≃ RetainedDart RS data.keep where
  toFun point := by
    rcases point with ⟨retained | pentagon, hpoint⟩
    · exact retained
    · exact False.elim hpoint
  invFun retained := ⟨Sum.inl retained, trivial⟩
  left_inv point := by
    rcases point with ⟨retained | pentagon, hpoint⟩
    · rfl
    · exact False.elim hpoint
  right_inv _ := rfl

@[simp]
theorem targetRetainedEquiv_symm_val
    (dart : RetainedDart RS data.keep) :
    (data.targetRetainedEquiv.symm dart).1 = Sum.inl dart :=
  rfl

/-- First return of cap faces to the old retained dart carrier. -/
def capTargetReturn : Equiv.Perm (RetainedDart RS data.keep) :=
  data.targetRetainedEquiv.permCongr
    (nextHitPerm data.capTargetPhi data.IsTargetRetained)

theorem firstPositiveHitTime_capTargetPhi_internal
    (dart : InternalDart RS data.keep) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl dart.1) trivial = 1 := by
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl dart.1) trivial ≤ 1 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [data.capTargetPhi_internal, IsTargetRetained]
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained (Sum.inl dart.1) trivial
  omega

theorem firstPositiveHitTime_capTargetPhi_boundary (position : Fin 5) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial = 3 := by
  have hthree :
      (data.capTargetPhi ^ (3 : ℕ))
          (Sum.inl (data.crossingBoundaryDartEquiv position).1) =
        Sum.inl (retainedRho RS data.keep
          (data.crossingBoundaryDartEquiv (position + 1)).1) := by
    have h3 : (3 : ℕ) = 2 + 1 := rfl
    rw [h3, pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply,
      pow_one]
    rw [data.capTargetPhi_boundary, data.capTargetPhi_cycleTrue,
      data.capTargetPhi_spoke]
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial ≤ 3 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · rw [hthree]
      trivial
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained
    (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial
  have hneOne : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial ≠ 1 := by
    intro hone
    have hhit := firstPositiveHitTime_hits data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial
    rw [hone] at hhit
    simp [data.capTargetPhi_boundary, IsTargetRetained] at hhit
  have hneTwo : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial ≠ 2 := by
    intro htwo
    have hhit := firstPositiveHitTime_hits data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial
    rw [htwo] at hhit
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, Equiv.Perm.mul_apply,
      pow_one, data.capTargetPhi_boundary,
      data.capTargetPhi_cycleTrue] at hhit
    simp [IsTargetRetained] at hhit
  omega

/-! ## The boundary action of the return -/

/-- Each sector closes onto the next boundary position. -/
def pentBoundaryCycle : Equiv.Perm (BoundaryDart RS data.keep) :=
  data.crossingBoundaryDartEquiv.permCongr (finRotate 5)

@[simp]
theorem pentBoundaryCycle_apply (position : Fin 5) :
    data.pentBoundaryCycle (data.crossingBoundaryDartEquiv position) =
      data.crossingBoundaryDartEquiv (position + 1) := by
  unfold pentBoundaryCycle
  simp [Equiv.permCongr_apply, finRotate_succ_apply]

/-- Eliminating the pentagon darts turns the cap face permutation into the
retained capped face permutation followed by the sector shift. -/
theorem capTargetReturn_eq :
    data.capTargetReturn =
      retainedCappedFacePerm RS data.keep *
        extendBoundaryPerm RS data.keep data.pentBoundaryCycle := by
  apply Equiv.ext
  intro dart
  by_cases hopposite : data.keep (RS.vertOf (RS.alpha dart.1))
  · let internal : InternalDart RS data.keep := ⟨dart, hopposite⟩
    unfold capTargetReturn
    simp only [Equiv.permCongr_apply]
    apply data.targetRetainedEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
        data.IsTargetRetained (Sum.inl dart) trivial) (Sum.inl dart) = _
    rw [data.firstPositiveHitTime_capTargetPhi_internal internal]
    rw [pow_one, data.capTargetPhi_internal internal]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_internal RS data.keep
      data.pentBoundaryCycle internal]
    apply congrArg (retainedRho RS data.keep)
    apply Subtype.ext
    rw [internalAlpha_val]
    exact (retainedCappedAlpha_apply_internal RS data.keep dart hopposite).symm
  · rcases data.crossingBoundaryDartEquiv.surjective ⟨dart, hopposite⟩ with
      ⟨position, hposition⟩
    obtain rfl : dart = (data.crossingBoundaryDartEquiv position).1 := by
      rw [hposition]
    unfold capTargetReturn
    simp only [Equiv.permCongr_apply]
    apply data.targetRetainedEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
        data.IsTargetRetained
        (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial)
          (Sum.inl (data.crossingBoundaryDartEquiv position).1) = _
    rw [data.firstPositiveHitTime_capTargetPhi_boundary position]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Equiv.Perm.mul_apply,
      pow_succ, Equiv.Perm.mul_apply, pow_one,
      data.capTargetPhi_boundary, data.capTargetPhi_cycleTrue,
      data.capTargetPhi_spoke]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_boundary RS data.keep
      data.pentBoundaryCycle (data.crossingBoundaryDartEquiv position),
      data.pentBoundaryCycle_apply]
    apply congrArg (retainedRho RS data.keep)
    rw [retainedCappedAlpha_apply_boundary RS data.keep
      (data.crossingBoundaryDartEquiv (position + 1)).1
      (data.crossingBoundaryDartEquiv (position + 1)).2]

end

end FiveEdgeCutPentagonCapData

end Mettapedia.GraphTheory.FourColor
