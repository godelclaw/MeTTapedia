import Mettapedia.Computability.PNP.PostSwitchForkObstruction
import Mettapedia.Computability.PNP.VisiblePostSwitchSurface
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Active post-switch residual witness core
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*}

/-- The unique active one-bit VV column. -/
def oneBitVec : BitVec 1 := fun _ => true

/-- The supported exact post-switch input with side bit `false`. -/
def activeOrbitInputFalse (z0 : Z) : ExactVisiblePostSwitchSurface Z 1 :=
  ⟨z0, oneBitVec, zeroVec⟩

/-- The supported exact post-switch input with side bit `true`. -/
def activeOrbitInputTrue (z0 : Z) : ExactVisiblePostSwitchSurface Z 1 :=
  ⟨z0, oneBitVec, oneBitVec⟩

/-- The invariant-base plus side-channel feature used by the witness route. -/
def activeOrbitFeatures (u : ExactVisiblePostSwitchSurface Z 1) :
    InvariantPostSwitchSurface Z 1 × BitVec 1 :=
  (invariantVisibleData u, u.b)

/-- The target bit is the retained one-bit side channel itself. -/
def activeOrbitTarget (u : ExactVisiblePostSwitchSurface Z 1) : Bool :=
  u.b 0

/-- The classifier simply reads that retained side bit. -/
def activeOrbitClassifier :
    InvariantPostSwitchSurface Z 1 × BitVec 1 → Bool :=
  fun t => t.2 0

/-- Weight one on the chosen active two-point orbit, and zero elsewhere. -/
noncomputable def activeOrbitWeight (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1) : ℕ := by
  classical
  exact if u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 then 1 else 0

@[simp] theorem oneBitVec_apply (i : Fin 1) : oneBitVec i = true := by
  fin_cases i
  rfl

@[simp] theorem activeOrbitInputFalse_b_apply (z0 : Z) (i : Fin 1) :
    (activeOrbitInputFalse z0).b i = false := by
  simp [activeOrbitInputFalse, zeroVec]

@[simp] theorem activeOrbitInputTrue_b_apply (z0 : Z) (i : Fin 1) :
    (activeOrbitInputTrue z0).b i = true := by
  simp [activeOrbitInputTrue, oneBitVec_apply]

theorem activeOrbitInputFalse_ne_inputTrue (z0 : Z) :
    activeOrbitInputFalse z0 ≠ activeOrbitInputTrue z0 := by
  intro h
  have h0 := congrArg (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b 0) h
  simp at h0

@[simp] theorem tiInputMap_activeOrbitInputFalse (z0 : Z) :
    tiInputMap (activeOrbitInputFalse z0) = activeOrbitInputTrue z0 := by
  rfl

@[simp] theorem tiInputMap_activeOrbitInputTrue (z0 : Z) :
    tiInputMap (activeOrbitInputTrue z0) = activeOrbitInputFalse z0 := by
  rfl

@[simp] theorem activeOrbitWeight_false (z0 : Z) :
    activeOrbitWeight z0 (activeOrbitInputFalse z0) = 1 := by
  classical
  simp [activeOrbitWeight]

@[simp] theorem activeOrbitWeight_true (z0 : Z) :
    activeOrbitWeight z0 (activeOrbitInputTrue z0) = 1 := by
  classical
  simp [activeOrbitWeight]

theorem activeOrbitWeight_tiInputMap (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1) :
    activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u := by
  classical
  by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
  · rcases h with rfl | rfl <;> simp [activeOrbitWeight]
  · have hti :
        ¬ (tiInputMap u = activeOrbitInputFalse z0 ∨
            tiInputMap u = activeOrbitInputTrue z0) := by
      intro hsupp
      apply h
      rcases hsupp with hfalse | htrue
      · right
        have hfalse' := congrArg tiInputMap hfalse
        simpa [tiInputMap_involutive u] using hfalse'
      · left
        have htrue' := congrArg tiInputMap htrue
        simpa [tiInputMap_involutive u] using htrue'
    simp [activeOrbitWeight, h, hti]

theorem activeOrbitTarget_flip_of_positiveWeight
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : 0 < activeOrbitWeight z0 u) :
    activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u) := by
  classical
  have hsupp : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 := by
    by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
    · exact h
    · have hzero : activeOrbitWeight z0 u = 0 := by
        simp [activeOrbitWeight, h]
      omega
  rcases hsupp with rfl | rfl <;> simp [activeOrbitTarget]

theorem activeOrbitCorrect_of_positiveWeight
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : 0 < activeOrbitWeight z0 u) :
    Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier u := by
  classical
  have hsupp : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 := by
    by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
    · exact h
    · have hzero : activeOrbitWeight z0 u = 0 := by
        simp [activeOrbitWeight, h]
      omega
  rcases hsupp with rfl | rfl <;> rfl

theorem activeOrbitWeight_eq_zero_of_not_correct
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : ¬ Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier u) :
    activeOrbitWeight z0 u = 0 := by
  by_cases hpos : 0 < activeOrbitWeight z0 u
  · exact False.elim (hu (activeOrbitCorrect_of_positiveWeight z0 u hpos))
  · exact Nat.eq_zero_of_not_pos hpos

theorem weightedCorrectMass_activeOrbit_eq_weightedTotalMass
    [Fintype Z] (z0 : Z) :
    weightedCorrectMass
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier
      =
    weightedTotalMass (activeOrbitWeight z0) := by
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier)
      (w := activeOrbitWeight z0)
  have hout :
      outsideMass
          (Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier)
          (activeOrbitWeight z0)
        = 0 := by
    classical
    unfold outsideMass sliceMass
    apply Finset.sum_eq_zero
    intro u _
    exact activeOrbitWeight_eq_zero_of_not_correct z0 u.1 u.2
  simpa [weightedCorrectMass, sliceMass, hout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hsplit.symm

end

end Mettapedia.Computability.PNP
