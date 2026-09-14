import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousRemainingFamilies
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousOutputGrid

/-! Signed work of each nonnegative horizontal family, with exact multiplicities. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousWorkFamilies

open PeriodicFourierTriad TwoShearViscousData TwoShearViscousCoefficientEvaluation
open RationalStretchingFlux RationalStretchingFluxHeat TwoShearViscousCertificate
open TwoShearViscousCoefficientFamilies TwoShearViscousRemainingFamilies
open TwoShearViscousReflection TwoShearViscousOutputGrid

def axisWork (k : Fin 10) : ℚ :=
  coefficientsA k * coefficientsARate k / (4 * (1 + (k.val : ℚ) ^ 2))

def mixedWork (k : Fin 10) : ℚ :=
  (coefficientsB k * coefficientsBRate k + coefficientsC k * coefficientsCRate k) /
    (16 * (5 + (k.val : ℚ) ^ 2))

theorem work_axis (k : Fin 10) : workCoefficient ![0, 1, (k.val : ℤ)] = axisWork k := by
  rw [workCoefficient, divergence_axis_family, heat_divergence_axis_family]
  fin_cases k <;> norm_num [axisWork, coefficientsA, coefficientsARate,
    rationalModeSquare, Fin.sum_univ_three, Matrix.cons_val_two]

theorem work_transposed_axis (k : Fin 10) : workCoefficient ![1, 0, (k.val : ℤ)] = axisWork k := by
  rw [workCoefficient, divergence_transposed_axis_family, heat_divergence_transposed_axis_family]
  fin_cases k <;> norm_num [axisWork, coefficientsA, coefficientsARate,
    rationalModeSquare, Fin.sum_univ_three, Matrix.cons_val_two]

theorem work_mixed (k : Fin 10) : workCoefficient ![2, 1, (k.val : ℤ)] = mixedWork k := by
  rw [workCoefficient, divergence_mixed_family, heat_divergence_mixed_family]
  fin_cases k <;> norm_num [mixedWork, coefficientsB, coefficientsBRate,
    coefficientsC, coefficientsCRate, rationalModeSquare, Fin.sum_univ_three, Matrix.cons_val_two]

theorem work_transposed_mixed (k : Fin 10) : workCoefficient ![1, 2, (k.val : ℤ)] = mixedWork k := by
  rw [workCoefficient, divergence_transposed_mixed_family, heat_divergence_transposed_mixed_family]
  fin_cases k <;> norm_num [mixedWork, coefficientsB, coefficientsBRate,
    coefficientsC, coefficientsCRate, rationalModeSquare, Fin.sum_univ_three, Matrix.cons_val_two]

theorem work_third_first (k : Fin 10) : workCoefficient ![3, 0, (k.val : ℤ)] = 0 := by
  simp [workCoefficient, divergence_third_first_family]

theorem work_third_second (k : Fin 10) : workCoefficient ![0, 3, (k.val : ℤ)] = 0 := by
  simp [workCoefficient, divergence_third_second_family]

theorem workCoefficient_abs (x y z : ℤ) :
    workCoefficient ![x, y, z] = workCoefficient ![|x|, |y|, |z|] := by
  let q : Wavevector := ![x, y, z]
  let r : Fin 3 → Bool := fun i ↦ decide (q i < 0)
  have href : reflection r q = (fun i ↦ |q i|) := by
    ext i
    by_cases h : q i < 0
    · simp [reflection, r, h, abs_of_neg h]
    · simp [reflection, r, h, abs_of_nonneg (le_of_not_gt h)]
  have he := (workCoefficient_reflection r q).symm
  rw [href] at he
  have hvec : (fun i ↦ |q i|) = ![|x|, |y|, |z|] := by
    ext i
    fin_cases i <;> rfl
  rwa [hvec] at he

theorem rationalWork_eq_nonnegative_grid :
    rationalHeatWork modes rationalData =
      ∑ h ∈ outputHorizontals, ∑ k ∈ Finset.Icc (-9 : ℤ) 9,
        workCoefficient ![|h.1|, |h.2|, |k|] := by
  rw [rationalWork_eq_grid]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  exact workCoefficient_abs _ _ _

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousWorkFamilies
