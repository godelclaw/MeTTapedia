import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousHeatEvaluation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousCertificate

/-!
# Exact longitudinal families in the physical two-shear convolution

These identities match the canonical axis and mixed-horizontal families
to the previously evaluated one-dimensional certificate. They concern
the actual three-dimensional convolution, not separately stipulated data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousCoefficientFamilies

open PeriodicFourierTriad TwoShearViscousData TwoShearViscousCoefficientEvaluation
open RationalStretchingFlux RationalStretchingFluxHeat RationalStretchingFluxContraction
open TwoShearViscousCertificate

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem divergence_axis_family (k : Fin 10) :
    rationalDivergenceCoefficient modes rationalData ![0, 1, (k.val : ℤ)] =
      ![coefficientsA k / 2, 0, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem heat_divergence_axis_family (k : Fin 10) :
    rationalHeatDivergenceCoefficient modes rationalData ![0, 1, (k.val : ℤ)] =
      ![coefficientsARate k / 2, 0, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [heat_divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem divergence_mixed_family (k : Fin 10) :
    rationalDivergenceCoefficient modes rationalData ![2, 1, (k.val : ℤ)] =
      ![coefficientsB k / 4, (-1) ^ k.val * coefficientsC k / 4, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem heat_divergence_mixed_family (k : Fin 10) :
    rationalHeatDivergenceCoefficient modes rationalData ![2, 1, (k.val : ℤ)] =
      ![coefficientsBRate k / 4, (-1) ^ k.val * coefficientsCRate k / 4, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [heat_divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousCoefficientFamilies
