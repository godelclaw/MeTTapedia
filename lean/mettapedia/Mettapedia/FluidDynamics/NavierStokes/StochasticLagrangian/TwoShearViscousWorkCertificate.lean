import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousWorkFamilies

/-!
# Positive physical viscous work for smooth two-shear data

The full output grid is reduced by proved reflection identities and
coefficient families to the signed rational certificate. Consequently
viscosity does not make this derived flux functional monotone. This is
not a blowup construction or a refutation of a time-integrated NS budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousWorkCertificate

open scoped RealInnerProductSpace
open Mettapedia.Analysis UnitTorusGradientProjection
open TwoShearViscousData TwoShearViscousCoefficientEvaluation TwoShearViscousHeatEvaluation
open RationalStretchingFluxHeat TwoShearViscousCertificate
open TwoShearViscousReflection TwoShearViscousOutputGrid TwoShearViscousWorkFamilies
open StretchingFluxCoefficients StretchingFluxSpectralEvolution PancakeInfiniteSpatialLaplacian
open LongitudinalGradientFlux StretchingFluxVariation

theorem longitudinal_outputs_eq :
    Finset.Icc (-9 : ℤ) 9 = {-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
  decide

theorem work_axis_int (k : ℤ) (h0 : 0 ≤ k) (h10 : k < 10) :
    workCoefficient ![0, 1, k] = axisWork ⟨k.toNat, by omega⟩ := by
  simpa only [Int.toNat_of_nonneg h0] using work_axis ⟨k.toNat, by omega⟩

theorem work_transposed_axis_int (k : ℤ) (h0 : 0 ≤ k) (h10 : k < 10) :
    workCoefficient ![1, 0, k] = axisWork ⟨k.toNat, by omega⟩ := by
  simpa only [Int.toNat_of_nonneg h0] using work_transposed_axis ⟨k.toNat, by omega⟩

theorem work_mixed_int (k : ℤ) (h0 : 0 ≤ k) (h10 : k < 10) :
    workCoefficient ![2, 1, k] = TwoShearViscousWorkFamilies.mixedWork ⟨k.toNat, by omega⟩ := by
  simpa only [Int.toNat_of_nonneg h0] using work_mixed ⟨k.toNat, by omega⟩

theorem work_transposed_mixed_int (k : ℤ) (h0 : 0 ≤ k) (h10 : k < 10) :
    workCoefficient ![1, 2, k] = TwoShearViscousWorkFamilies.mixedWork ⟨k.toNat, by omega⟩ := by
  simpa only [Int.toNat_of_nonneg h0] using work_transposed_mixed ⟨k.toNat, by omega⟩

theorem work_third_first_int (k : ℤ) (h0 : 0 ≤ k) (h10 : k < 10) :
    workCoefficient ![3, 0, k] = 0 := by
  simpa only [Int.toNat_of_nonneg h0] using work_third_first ⟨k.toNat, by omega⟩

theorem work_third_second_int (k : ℤ) (h0 : 0 ≤ k) (h10 : k < 10) :
    workCoefficient ![0, 3, k] = 0 := by
  simpa only [Int.toNat_of_nonneg h0] using work_third_second ⟨k.toNat, by omega⟩

set_option maxHeartbeats 4000000 in
theorem rationalHeatWork_eq_certificate :
    rationalHeatWork modes rationalData = spectralWork := by
  rw [rationalWork_eq_nonnegative_grid]
  norm_num [outputHorizontals, longitudinal_outputs_eq]
  simp (disch := omega) only [work_axis_int, work_transposed_axis_int, work_mixed_int, work_transposed_mixed_int, work_third_first_int, work_third_second_int]
  rw [spectralWork_eq]
  decide +kernel

theorem full_ns_work_eq (ν : ℝ) :
    spectralRHSWork ν velocity =
      ν * (2 * Real.pi) ^ 8 * (16932543012172819 / 351018510581760) := by
  rw [full_work_eq_rational_heat, rationalHeatWork_eq_certificate, spectralWork_eq]
  push_cast
  rfl

theorem full_ns_work_pos (ν : ℝ) (hν : 0 < ν) : 0 < spectralRHSWork ν velocity := by
  rw [full_ns_work_eq]
  positivity

theorem heat_work_pos : 0 < spectralVariationWork velocity (laplacianCoeff velocity) := by
  have h := full_ns_work_pos 1 zero_lt_one
  rwa [StretchingFluxHorizontalParity.twoShear_full_work_eq_heat, one_mul] at h

theorem physical_heat_work_pos :
    0 < ⟪projectedFlux 0 velocity, toTensorL2 (variationField velocity (laplacianCoeff velocity))⟫ := by
  rw [physical_variation_work _ _ (all_moments 1) (heat_all_moments 1) reality heat_reality]
  exact heat_work_pos

theorem dissipation_lt_twice_mixed_work :
    StretchingFluxProjectedDiffusion.dissipation velocity <
      2 * StretchingFluxProjectedDiffusion.mixedWork velocity := by
  have h := heat_work_pos
  rw [spectral_heat_work_eq_mixed_sub_dissipation velocity (all_moments 3) transverse reality] at h
  linarith

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousWorkCertificate
