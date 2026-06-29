import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth

/-!
# Regression checks for BKM vorticity-growth estimates
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression

theorem bkm_material_diffusion_remainder_uniform_bound_regression
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * B ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤ G * B :=
  uniform_vorticityMaterialDiffusionRemainder_boundUpTo hEq hG hω

theorem bkm_material_diffusion_power_uniform_bound_regression
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * (B * B) ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        |vorticityMaterialDiffusionPower ν u t x| ≤ G * (B * B) :=
  uniform_vorticityMaterialDiffusionPower_boundUpTo hEq hG hω

theorem bkm_standard_vorticity_growth_estimate_closed_regression :
    BKMStandardVorticityGrowthEstimateClosed :=
  BKMStandardVorticityGrowthEstimateClosed_proved

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
