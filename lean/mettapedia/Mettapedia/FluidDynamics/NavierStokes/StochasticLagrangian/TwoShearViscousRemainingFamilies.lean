import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousCoefficientFamilies

/-!
# Remaining nonnegative horizontal families in the two-shear witness

The transposed axis and mixed families retain their longitudinal parity.
The pure third harmonics have zero source divergence, so they contribute
zero work regardless of their variation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousRemainingFamilies

open PeriodicFourierTriad TwoShearViscousData TwoShearViscousCoefficientEvaluation
open RationalStretchingFlux RationalStretchingFluxHeat RationalStretchingFluxContraction
open TwoShearViscousCertificate

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem divergence_transposed_axis_family (k : Fin 10) :
    rationalDivergenceCoefficient modes rationalData ![1, 0, (k.val : ℤ)] =
      ![0, (-1) ^ k.val * coefficientsA k / 2, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem heat_divergence_transposed_axis_family (k : Fin 10) :
    rationalHeatDivergenceCoefficient modes rationalData ![1, 0, (k.val : ℤ)] =
      ![0, (-1) ^ k.val * coefficientsARate k / 2, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [heat_divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem divergence_transposed_mixed_family (k : Fin 10) :
    rationalDivergenceCoefficient modes rationalData ![1, 2, (k.val : ℤ)] =
      ![coefficientsC k / 4, (-1) ^ k.val * coefficientsB k / 4, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem heat_divergence_transposed_mixed_family (k : Fin 10) :
    rationalHeatDivergenceCoefficient modes rationalData ![1, 2, (k.val : ℤ)] =
      ![coefficientsCRate k / 4, (-1) ^ k.val * coefficientsBRate k / 4, 0] := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [heat_divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem divergence_third_first_family (k : Fin 10) :
    rationalDivergenceCoefficient modes rationalData ![3, 0, (k.val : ℤ)] =
      0 := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem divergence_third_second_family (k : Fin 10) :
    rationalDivergenceCoefficient modes rationalData ![0, 3, (k.val : ℤ)] =
      0 := by
  fin_cases k <;> ext i <;> fin_cases i <;> rw [divergence_eq_double_sum] <;>
    simp_rw [sum_modes] <;> decide +kernel

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousRemainingFamilies
