import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryStubFaceStep
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamFaceArc

/-!
# Open-region face orbits and the retained boundary successor

The capped retained-side ribbon has a finite first-return permutation on its
exposed darts.  The literal open-region rotation realizes one step of that
permutation by following an actual face orbit from one degree-one stub to the
next.  This file starts the C-2 collar calculation by recording the local
permutation identity; the later cap theorem must still prove that the five
named spoke darts form one cycle of the boundary successor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionBoundaryOrbit

open GoertzelV24OpenRegionBoundaryStubFaceStep
open GoertzelV24OpenRegionRotation
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Leaving a fresh degree-one stub in the literal open rotation is exactly
the first capped-retained face step from its associated exposed dart. -/
theorem rotationSystem_phi_stub_eq_retainedCappedFacePerm
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    (rotationSystem RS keep outer).phi (Sum.inr boundary) =
      Sum.inl ((retainedCappedFacePerm RS keep) boundary.1) := by
  rw [rotationSystem_phi_stub]
  change Sum.inl (retainedRho RS keep boundary.1) =
    Sum.inl ((retainedCappedFacePerm RS keep) boundary.1)
  congr 1
  rw [retainedCappedFacePerm, Equiv.Perm.mul_apply,
    retainedCappedAlpha_apply_boundary]
  exact boundary.2

/-- On an old retained dart whose opposite endpoint is retained, an opened
face step is the corresponding capped-retained face step. -/
theorem rotationSystem_phi_old_eq_retainedCappedFacePerm_of_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : RetainedDart RS keep)
    (hinternal : keep (RS.vertOf (RS.alpha dart.1))) :
    (rotationSystem RS keep outer).phi (Sum.inl dart) =
      Sum.inl ((retainedCappedFacePerm RS keep) dart) := by
  have hcapped : retainedCappedAlpha RS keep dart =
      ⟨RS.alpha dart.1, hinternal⟩ := by
    apply Subtype.ext
    exact retainedCappedAlpha_apply_internal RS keep dart hinternal
  rw [RotationSystem.phi_apply, rotationSystem_alpha_old_of_internal,
    rotationSystem_rho_old]
  rw [retainedCappedFacePerm, Equiv.Perm.mul_apply, hcapped]

/-- An old exposed dart takes one opened face step to its fresh boundary
stub. -/
theorem rotationSystem_phi_old_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
  (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    (rotationSystem RS keep outer).phi (Sum.inl boundary.1) =
      Sum.inr boundary := by
  rw [RotationSystem.phi_apply,
    rotationSystem_alpha_old_of_boundary RS keep outer boundary.1 boundary.2,
    rotationSystem_rho_stub]
  apply congrArg Sum.inr
  apply Subtype.ext
  rfl

/-- Before the capped retained walk returns to an exposed dart, its positive
iterates are followed literally by the opened face permutation after leaving
the fresh stub. -/
theorem rotationSystem_phi_pow_stub_eq_old_cappedFacePerm_pow
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep)
    {step : Nat} (hstepPos : 0 < step)
    (hstepLe : step ≤ firstPositiveHitTime
      (retainedCappedFacePerm RS keep)
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1 boundary.2) :
    ((rotationSystem RS keep outer).phi ^ step) (Sum.inr boundary) =
      Sum.inl ((retainedCappedFacePerm RS keep ^ step) boundary.1) := by
  induction step with
  | zero => omega
  | succ step ih =>
      by_cases hstepZero : step = 0
      · subst step
        simpa [pow_one] using
          rotationSystem_phi_stub_eq_retainedCappedFacePerm RS keep outer boundary
      · have hpreviousPos : 0 < step := Nat.pos_of_ne_zero hstepZero
        have hpreviousLt : step < firstPositiveHitTime
            (retainedCappedFacePerm RS keep)
            (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1
              boundary.2 := by
          omega
        have hpreviousLe : step ≤ firstPositiveHitTime
            (retainedCappedFacePerm RS keep)
            (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1
              boundary.2 := Nat.le_of_lt hpreviousLt
        have hnotBoundary : ¬ ¬ keep (RS.vertOf (RS.alpha
            ((retainedCappedFacePerm RS keep ^ step) boundary.1).1)) := by
          exact not_hit_before_firstPositiveHitTime
            (retainedCappedFacePerm RS keep)
            (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1
              boundary.2 hpreviousPos hpreviousLt
        have hinternal : keep (RS.vertOf (RS.alpha
            ((retainedCappedFacePerm RS keep ^ step) boundary.1).1)) := by
          simpa only [not_not] using hnotBoundary
        calc
          ((rotationSystem RS keep outer).phi ^ Nat.succ step)
              (Sum.inr boundary) =
              (rotationSystem RS keep outer).phi
                (((rotationSystem RS keep outer).phi ^ step)
                  (Sum.inr boundary)) := by
                rw [pow_succ', Equiv.Perm.mul_apply]
          _ = (rotationSystem RS keep outer).phi
                (Sum.inl ((retainedCappedFacePerm RS keep ^ step) boundary.1)) := by
                rw [ih hpreviousPos hpreviousLe]
          _ = Sum.inl ((retainedCappedFacePerm RS keep)
                ((retainedCappedFacePerm RS keep ^ step) boundary.1)) :=
              rotationSystem_phi_old_eq_retainedCappedFacePerm_of_internal
                RS keep outer _ hinternal
          _ = Sum.inl ((retainedCappedFacePerm RS keep ^ Nat.succ step)
                boundary.1) := by
              rw [pow_succ', Equiv.Perm.mul_apply]

/-- One full first-return step on the capped retained boundary is realized by
an actual opened face orbit from one fresh stub to the next fresh stub. -/
theorem dartOrbitFace_stub_eq_boundarySuccessor
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    dartOrbitFace (rotationSystem RS keep outer) (Sum.inr boundary) =
      dartOrbitFace (rotationSystem RS keep outer)
        (Sum.inr (retainedRegionBoundarySuccessor RS keep boundary)) := by
  let facePerm := retainedCappedFacePerm RS keep
  let returnTime := firstPositiveHitTime facePerm
    (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1 boundary.2
  let successor : BoundaryDart RS keep :=
    ⟨(facePerm ^ returnTime) boundary.1,
      firstPositiveHitTime_hits facePerm
        (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1 boundary.2⟩
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos facePerm
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) boundary.1 boundary.2
  have hpower := rotationSystem_phi_pow_stub_eq_old_cappedFacePerm_pow
    RS keep outer boundary hreturnPos (Nat.le_refl returnTime)
  have hlast : (rotationSystem RS keep outer).phi
      (Sum.inl ((facePerm ^ returnTime) boundary.1)) = Sum.inr successor := by
    apply rotationSystem_phi_old_boundary RS keep outer successor
  have hwalk : ((rotationSystem RS keep outer).phi ^ (returnTime + 1))
      (Sum.inr boundary) = Sum.inr successor := by
    rw [pow_succ', Equiv.Perm.mul_apply, hpower]
    exact hlast
  have hsuccessor : successor = retainedRegionBoundarySuccessor RS keep boundary := by
    rfl
  change Quotient.mk (Equiv.Perm.SameCycle.setoid
      (rotationSystem RS keep outer).phi) (Sum.inr boundary) =
    Quotient.mk (Equiv.Perm.SameCycle.setoid
      (rotationSystem RS keep outer).phi)
      (Sum.inr (retainedRegionBoundarySuccessor RS keep boundary))
  apply Quotient.sound
  rw [← hsuccessor, ← hwalk]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl (rotationSystem RS keep outer).phi
      (Sum.inr boundary))

/-- Iterating the capped retained boundary successor keeps fresh stubs on one
literal opened face orbit. -/
theorem dartOrbitFace_stub_eq_boundarySuccessor_pow
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (first : BoundaryDart RS keep) (power : Nat) :
    dartOrbitFace (rotationSystem RS keep outer) (Sum.inr first) =
      dartOrbitFace (rotationSystem RS keep outer)
        (Sum.inr ((retainedRegionBoundarySuccessor RS keep ^ power) first)) := by
  induction power generalizing first with
  | zero => simp
  | succ power ih =>
      calc
        dartOrbitFace (rotationSystem RS keep outer) (Sum.inr first) =
            dartOrbitFace (rotationSystem RS keep outer)
              (Sum.inr (retainedRegionBoundarySuccessor RS keep first)) :=
          dartOrbitFace_stub_eq_boundarySuccessor RS keep outer first
        _ = dartOrbitFace (rotationSystem RS keep outer)
              (Sum.inr ((retainedRegionBoundarySuccessor RS keep ^ power)
                (retainedRegionBoundarySuccessor RS keep first))) :=
          ih (retainedRegionBoundarySuccessor RS keep first)
        _ = dartOrbitFace (rotationSystem RS keep outer)
              (Sum.inr ((retainedRegionBoundarySuccessor RS keep ^ Nat.succ power)
                first)) := by
          rw [pow_succ, Equiv.Perm.mul_apply]

/-- The literal open rotation gathers exactly the exposed darts lying in one
cycle of the capped retained boundary successor.  Thus a cap-collar proof may
establish a common opened hole face by proving the corresponding finite
boundary-successor cycle, with no topological picture principle hidden in the
conversion. -/
theorem dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (first second : BoundaryDart RS keep)
    (hsame : (retainedRegionBoundarySuccessor RS keep).SameCycle first second) :
    dartOrbitFace (rotationSystem RS keep outer) (Sum.inr first) =
      dartOrbitFace (rotationSystem RS keep outer) (Sum.inr second) := by
  rcases hsame.exists_nat_pow_eq with ⟨power, hpower⟩
  rw [← hpower]
  exact dartOrbitFace_stub_eq_boundarySuccessor_pow RS keep outer first power

end
end GoertzelV24OpenRegionBoundaryOrbit

end Mettapedia.GraphTheory.FourColor
