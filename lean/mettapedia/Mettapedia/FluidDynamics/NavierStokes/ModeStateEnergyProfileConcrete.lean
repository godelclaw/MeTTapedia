import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyProfileCore

/-!
# An affine smooth-transition energy profile

The profile `u ↦ u · smoothTransition (c u + d)` for `c > 0` and `d ≥ 0`, alongside the
concrete profiles defined in `ModeStateEnergyProfileFork`. Its zero law is derived there.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileConcrete

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
