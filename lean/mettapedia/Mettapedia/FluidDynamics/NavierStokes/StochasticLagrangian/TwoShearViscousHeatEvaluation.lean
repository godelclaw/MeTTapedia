import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousCoefficientEvaluation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RationalStretchingFluxContraction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxHorizontalParity

/-!
# Physical heat variation of the two-shear field

The rational work below is linked to the unrestricted NS right-hand side
using the checked inviscid cancellation. Individual coefficient evaluations
do not assert a sign for the sum over all output frequencies.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousHeatEvaluation

open PeriodicFourierTriad PeriodicTensorParseval PancakeInfiniteSpatialLaplacian
open TwoShearViscousData TwoShearViscousCoefficientEvaluation
open RationalStretchingFlux RationalStretchingFluxHeat RationalStretchingFluxContraction
open StretchingFluxCoefficients StretchingFluxMixedCoefficients StretchingFluxSpectralEvolution

theorem full_work_eq_rational_heat (ν : ℝ) :
    spectralRHSWork ν velocity = ν * (2 * Real.pi) ^ 8 * (rationalHeatWork modes rationalData : ℝ) := by
  rw [StretchingFluxHorizontalParity.twoShear_full_work_eq_heat, ← imaginaryLift_rationalData,
    spectral_heat_work_eq_rational modes rationalData rationalData_supported
      (by simpa only [imaginaryLift_rationalData] using reality)]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
theorem rational_heat_divergence_mode_zero_one_one :
    rationalHeatDivergenceCoefficient modes rationalData ![0, 1, 1] = ![-2805 / 512, 0, 0] := by
  ext i
  fin_cases i <;> rw [heat_divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

theorem heat_divergence_mode_zero_one_one :
    divergenceCoeff ![0, 1, 1]
        (fun j ↦ variationCoefficients velocity (laplacianCoeff velocity) j ![0, 1, 1]) =
      (Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 6)) • ![-2805 / 512, 0, 0] := by
  rw [← imaginaryLift_rationalData]
  ext i
  rw [heat_divergence_imaginaryLift modes rationalData rationalData_supported,
    rational_heat_divergence_mode_zero_one_one]
  fin_cases i <;> simp

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousHeatEvaluation
