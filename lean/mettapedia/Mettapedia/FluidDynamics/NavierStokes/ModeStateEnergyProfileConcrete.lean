import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyProfileCore
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Concrete Energy Profiles on ModeState

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

section ModeStateEnergyProfileConcrete

/-- The identity profile recovers the raw soft energy on the good side. -/
def identityEnergyProfile : EnergyProfile where
  profile := fun u => u
  continuous_profile := continuous_id
  profile_nonneg := by
    intro u hu
    exact hu
  profile_le := by
    intro u hu
    exact le_rfl
  profile_zero := by simp
  profile_pos := by
    intro u hu
    exact hu

/-- A globally continuous clipped log profile agreeing with `log (1 + u)` on
nonnegative inputs. -/
def logOnePlusMaxEnergyProfile : EnergyProfile where
  profile := fun u => Real.log (1 + max u 0)
  continuous_profile := by
    have harg : Continuous fun u : ℝ => 1 + max u 0 := by
      exact continuous_const.add (continuous_id.max continuous_const)
    refine harg.log ?_
    intro u
    have hmax_nonneg : 0 ≤ max u 0 := le_max_right _ _
    linarith
  profile_nonneg := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    rw [show 1 + max u 0 = 1 + u by simp [hmax]]
    apply Real.log_nonneg
    linarith
  profile_le := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    have harg_pos : 0 < 1 + max u 0 := by
      rw [hmax]
      linarith
    have h := Real.log_le_sub_one_of_pos harg_pos
    simpa [hmax] using h
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu.le
    have hgt : 1 < 1 + max u 0 := by
      rw [hmax]
      linarith
    simpa [hmax] using Real.log_pos hgt

/-- A bounded rational saturation profile agreeing with `u / (1 + u)` on
nonnegative inputs. -/
def rationalMaxEnergyProfile : EnergyProfile where
  profile := fun u => max u 0 / (1 + max u 0)
  continuous_profile := by
    have hmax : Continuous fun u : ℝ => max u 0 := continuous_id.max continuous_const
    exact hmax.div (continuous_const.add hmax) (by
      intro u
      have hmax_nonneg : 0 ≤ max u 0 := le_max_right _ _
      linarith)
  profile_nonneg := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    rw [show max u 0 / (1 + max u 0) = u / (1 + u) by simp [hmax]]
    exact div_nonneg hu (by linarith)
  profile_le := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    rw [show max u 0 / (1 + max u 0) = u / (1 + u) by simp [hmax]]
    exact div_le_self hu (by linarith)
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu.le
    rw [show max u 0 / (1 + max u 0) = u / (1 + u) by simp [hmax]]
    exact div_pos hu (by linarith)

/-- A smooth bounded saturation profile agreeing with `1 - exp(-u)` on
nonnegative inputs. -/
def expNegMaxEnergyProfile : EnergyProfile where
  profile := fun u => 1 - Real.exp (- max u 0)
  continuous_profile := by
    have hmax : Continuous fun u : ℝ => max u 0 := continuous_id.max continuous_const
    exact continuous_const.sub (Real.continuous_exp.comp (continuous_neg.comp hmax))
  profile_nonneg := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    have hexp_le : Real.exp (-u) ≤ 1 := by
      have : Real.exp (-u) ≤ Real.exp 0 := by
        gcongr
        linarith
      simpa using this
    have : 0 ≤ 1 - Real.exp (-u) := by
      exact sub_nonneg.mpr hexp_le
    simpa [hmax] using this
  profile_le := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu
    have h := Real.add_one_le_exp (-u)
    have : 1 - Real.exp (-u) ≤ u := by
      linarith
    simpa [hmax] using this
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hmax : max u 0 = u := max_eq_left hu.le
    have hexp_lt : Real.exp (-u) < 1 := by
      have : Real.exp (-u) < Real.exp 0 := by
        gcongr
        linarith
      simpa using this
    have : 0 < 1 - Real.exp (-u) := by
      exact sub_pos.mpr hexp_lt
    simpa [hmax] using this

/-- A smooth transition profile `u * smoothTransition u`. It is identically
zero on nonpositive inputs and agrees with `u` for large positive inputs. -/
def smoothTransitionEnergyProfile : EnergyProfile where
  profile := fun u => u * Real.smoothTransition u
  continuous_profile := continuous_id.mul Real.smoothTransition.continuous
  profile_nonneg := by
    intro u hu
    exact mul_nonneg hu (Real.smoothTransition.nonneg u)
  profile_le := by
    intro u hu
    simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one u) hu
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    exact mul_pos hu (Real.smoothTransition.pos_of_pos hu)

/-- A positive-scale smooth transition family `u * smoothTransition (c u)`. -/
def scaledSmoothTransitionEnergyProfile (c : ℝ) (hc : 0 < c) : EnergyProfile where
  profile := fun u => u * Real.smoothTransition (c * u)
  continuous_profile := by
    exact continuous_id.mul
      (Real.smoothTransition.continuous.comp (continuous_const.mul continuous_id))
  profile_nonneg := by
    intro u hu
    exact mul_nonneg hu (Real.smoothTransition.nonneg (c * u))
  profile_le := by
    intro u hu
    simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (c * u)) hu
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have hcu : 0 < c * u := mul_pos hc hu
    exact mul_pos hu (Real.smoothTransition.pos_of_pos hcu)

/-- A positive-scale, nonnegative-shift smooth transition family
`u * smoothTransition (c u + d)`. -/
def affineSmoothTransitionEnergyProfile
    (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d) : EnergyProfile where
  profile := fun u => u * Real.smoothTransition (c * u + d)
  continuous_profile := by
    exact continuous_id.mul
      (Real.smoothTransition.continuous.comp
        ((continuous_const.mul continuous_id).add continuous_const))
  profile_nonneg := by
    intro u hu
    exact mul_nonneg hu (Real.smoothTransition.nonneg (c * u + d))
  profile_le := by
    intro u hu
    simpa using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (c * u + d)) hu
  profile_zero := by
    simp
  profile_pos := by
    intro u hu
    have harg_pos : 0 < c * u + d := by
      have hcu : 0 < c * u := mul_pos hc hu
      linarith
    exact mul_pos hu (Real.smoothTransition.pos_of_pos harg_pos)

end ModeStateEnergyProfileConcrete

end NavierStokes
end FluidDynamics
end Mettapedia
