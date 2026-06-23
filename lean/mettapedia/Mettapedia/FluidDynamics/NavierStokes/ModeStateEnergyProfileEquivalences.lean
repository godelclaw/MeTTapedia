import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyProfileConcrete

/-!
# Energy Profile Equivalences with Existing ModeState Radii

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

section ModeStateEnergyProfileEquivalences

theorem profiledEnergyTerm_identity_eq_sobolevEnergyTerm
    (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm identityEnergyProfile m x n = sobolevEnergyTerm m x n := by
  simp [profiledEnergyTerm, identityEnergyProfile, sobolevEnergyTerm]

theorem profiledEnergyRadius_identity_eq_sobolevEnergyRadius
    (m : ℕ) :
    profiledEnergyRadius identityEnergyProfile m = sobolevEnergyRadius m := by
  funext x
  unfold profiledEnergyRadius sobolevEnergyRadius
  simp [profiledEnergyTerm_identity_eq_sobolevEnergyTerm]

theorem profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm
    (m : ℕ) (x : ModeState) (n : ℕ) :
    profiledEnergyTerm logOnePlusMaxEnergyProfile m x n = logEnergyTerm m x n := by
  have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
  simp [profiledEnergyTerm, logOnePlusMaxEnergyProfile, logEnergyTerm, max_eq_left hsq_nonneg]

theorem profiledEnergyRadius_logOnePlusMax_eq_logEnergyRadius
    (m : ℕ) :
    profiledEnergyRadius logOnePlusMaxEnergyProfile m = logEnergyRadius m := by
  funext x
  unfold profiledEnergyRadius logEnergyRadius
  simp [profiledEnergyTerm_logOnePlusMax_eq_logEnergyTerm]

theorem hardProfileThresholdRadius_logOnePlusMax_eq_hardLogEnergyThresholdRadius
    (m : ℕ) :
    hardProfileThresholdRadius logOnePlusMaxEnergyProfile m = hardLogEnergyThresholdRadius m := by
  funext x
  let p : Prop := ∃ n, 0 < logOnePlusMaxEnergyProfile.profile ((sobolevAmplification m x n) ^ (2 : ℕ))
  let q : Prop := ∃ n, 0 < Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ))
  have hpq : p ↔ q := by
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
      simpa [p, q, logOnePlusMaxEnergyProfile, max_eq_left hsq_nonneg] using hn
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
      simpa [p, q, logOnePlusMaxEnergyProfile, max_eq_left hsq_nonneg] using hn
  by_cases hp : p
  · have hq : q := hpq.mp hp
    simp [hardProfileThresholdRadius, hardLogEnergyThresholdRadius, p, q, hp, hq]
  · have hq : ¬ q := by
      intro hq
      exact hp (hpq.mpr hq)
    simp [hardProfileThresholdRadius, hardLogEnergyThresholdRadius, p, q, hp, hq]

theorem hardProfileThresholdRadius_rationalMax_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius rationalMaxEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := rationalMaxEnergyProfile) m

theorem hardProfileThresholdRadius_expNegMax_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius expNegMaxEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := expNegMaxEnergyProfile) m

theorem hardProfileThresholdRadius_smoothTransition_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius smoothTransitionEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := smoothTransitionEnergyProfile) m

theorem hardProfileThresholdRadius_scaledSmoothTransition_eq_hardSobolevRadius
    (c : ℝ) (hc : 0 < c) (m : ℕ) :
    hardProfileThresholdRadius (scaledSmoothTransitionEnergyProfile c hc) m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := scaledSmoothTransitionEnergyProfile c hc) m

theorem hardProfileThresholdRadius_affineSmoothTransition_eq_hardSobolevRadius
    (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d) (m : ℕ) :
    hardProfileThresholdRadius (affineSmoothTransitionEnergyProfile c d hc hd) m
      = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := affineSmoothTransitionEnergyProfile c d hc hd) m

end ModeStateEnergyProfileEquivalences

end NavierStokes
end FluidDynamics
end Mettapedia
