import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyProfileCore
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Windowed Smooth-Transition Energy Profile Obstruction

This module was split out of `ModeStateEnergyProfileFork.lean` to keep the
Navier-Stokes route-audit library organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileWindowed

/-- A genuinely windowed smooth profile: it turns on and later turns off. -/
def windowedSmoothTransitionProfile (c : ℝ) : ℝ → ℝ :=
  fun u => u * (Real.smoothTransition (c * u + 1) - Real.smoothTransition (c * u))

theorem windowedSmoothTransitionProfile_nonneg
    (c : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ windowedSmoothTransitionProfile c u := by
  unfold windowedSmoothTransitionProfile
  have hmono :
      Real.smoothTransition (c * u) ≤ Real.smoothTransition (c * u + 1) := by
    apply Real.smoothTransition.monotone
    linarith
  exact mul_nonneg hu (sub_nonneg.mpr hmono)

theorem windowedSmoothTransitionProfile_le
    (c : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    windowedSmoothTransitionProfile c u ≤ u := by
  unfold windowedSmoothTransitionProfile
  have hdiff_le : Real.smoothTransition (c * u + 1) - Real.smoothTransition (c * u) ≤ 1 := by
    have hle : Real.smoothTransition (c * u + 1) ≤ 1 := Real.smoothTransition.le_one _
    have hnonneg : 0 ≤ Real.smoothTransition (c * u) := Real.smoothTransition.nonneg _
    linarith
  simpa using mul_le_mul_of_nonneg_left hdiff_le hu

theorem windowedSmoothTransitionProfile_inv_eq_zero
    (c : ℝ) (hc : 0 < c) :
    windowedSmoothTransitionProfile c c⁻¹ = 0 := by
  unfold windowedSmoothTransitionProfile
  have hcne : c ≠ 0 := ne_of_gt hc
  have hbase : c * c⁻¹ = 1 := by
    field_simp [hcne]
  have h1 : 1 ≤ c * c⁻¹ := by simp [hbase]
  have h2 : 1 ≤ c * c⁻¹ + 1 := by linarith
  rw [Real.smoothTransition.one_of_one_le h2, Real.smoothTransition.one_of_one_le h1]
  ring

theorem not_exists_energyProfile_windowedSmoothTransitionProfile
    (c : ℝ) (hc : 0 < c) :
    ¬ ∃ P : EnergyProfile, P.profile = windowedSmoothTransitionProfile c := by
  intro h
  rcases h with ⟨P, hP⟩
  have hcinv : 0 < c⁻¹ := by
    simpa [one_div] using (one_div_pos.mpr hc)
  have hpos : 0 < P.profile c⁻¹ := P.profile_pos _ hcinv
  rw [hP, windowedSmoothTransitionProfile_inv_eq_zero c hc] at hpos
  linarith

end ModeStateEnergyProfileWindowed

end NavierStokes
end FluidDynamics
end Mettapedia
