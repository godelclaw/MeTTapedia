import Mettapedia.Computability.PNP.PostSwitchResidualWitnessCore

/-!
# Active post-switch residual witness support and mass
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*}

def activeOrbitSupport (z0 : Z) :=
  {u : ExactVisiblePostSwitchSurface Z 1 //
    u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0}

noncomputable def activeOrbitSupportEquivBool (z0 : Z) :
    {u : ExactVisiblePostSwitchSurface Z 1 //
      u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0} ≃ Bool := by
  classical
  refine
    { toFun := fun u =>
        if u.1 = activeOrbitInputFalse z0 then false else true
      invFun := fun b =>
        cond b
          ⟨activeOrbitInputTrue z0, Or.inr rfl⟩
          ⟨activeOrbitInputFalse z0, Or.inl rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro u
    rcases u with ⟨u, hu⟩
    rcases hu with rfl | rfl
    · simp
    · have hneq : activeOrbitInputTrue z0 ≠ activeOrbitInputFalse z0 := by
        intro h
        exact activeOrbitInputFalse_ne_inputTrue z0 h.symm
      simp [hneq]
  · intro b
    cases b with
    | false =>
        simp
    | true =>
        have hneq : activeOrbitInputTrue z0 ≠ activeOrbitInputFalse z0 := by
          intro h
          exact activeOrbitInputFalse_ne_inputTrue z0 h.symm
        simp [hneq]

theorem sliceMass_activeOrbitSupport [Fintype Z] (z0 : Z) :
    (by
      classical
      exact
        sliceMass
            (fun u : ExactVisiblePostSwitchSurface Z 1 =>
              u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0)
            (activeOrbitWeight z0)
          = 2) := by
  classical
  unfold sliceMass
  calc
    (∑ u : {u : ExactVisiblePostSwitchSurface Z 1 //
        u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0},
        activeOrbitWeight z0 u.1)
        = ∑ b : Bool, 1 := by
            exact Fintype.sum_equiv
              (activeOrbitSupportEquivBool z0)
              (fun u : {u : ExactVisiblePostSwitchSurface Z 1 //
                u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0} =>
                activeOrbitWeight z0 u.1)
                  (fun _ : Bool => 1)
                  (by
                    intro u
                    rcases u with ⟨u, hu⟩
                    rcases hu with rfl | rfl <;> simp [activeOrbitWeight])
    _ = 2 := by simp

theorem outsideMass_activeOrbitSupport [Fintype Z] (z0 : Z) :
    (by
      classical
      exact
        outsideMass
            (fun u : ExactVisiblePostSwitchSurface Z 1 =>
              u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0)
            (activeOrbitWeight z0)
          = 0) := by
  classical
  unfold outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro u _
  simp [activeOrbitWeight, u.2]

theorem weightedTotalMass_activeOrbitWeight (z0 : Z) [Fintype Z] :
    weightedTotalMass (activeOrbitWeight z0) = 2 := by
  classical
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := fun u : ExactVisiblePostSwitchSurface Z 1 =>
        u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0)
      (w := activeOrbitWeight z0)
  simpa [sliceMass_activeOrbitSupport (Z := Z) z0,
    outsideMass_activeOrbitSupport (Z := Z) z0] using hsplit

theorem activeOrbitSide_ne_of_positiveWeight
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : 0 < activeOrbitWeight z0 u) :
    (tiInputMap u).b ≠ u.b := by
  classical
  have hsupp : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 := by
    by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
    · exact h
    · have hzero : activeOrbitWeight z0 u = 0 := by
        simp [activeOrbitWeight, h]
      omega
  rcases hsupp with rfl | rfl
  · intro h
    have h0 := congrArg (fun b : BitVec 1 => b 0) h
    simp at h0
  · intro h
    have h0 := congrArg (fun b : BitVec 1 => b 0) h
    simp at h0


end

end Mettapedia.Computability.PNP
