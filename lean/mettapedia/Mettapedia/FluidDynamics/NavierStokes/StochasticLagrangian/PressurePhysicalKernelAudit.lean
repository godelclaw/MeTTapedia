import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputDyadicBudget

/-! Physical-coordinate, nonzero-symbol, and summability regressions for low-output pressure. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePhysicalKernelAudit

open MeasureTheory Mettapedia.Analysis.SmoothAnnulus Mettapedia.Analysis.EuclideanCrossProduct
open PressureLowOutputCutoff PressureLowOutputSymbol PressureLowOutputCoordinates
open PressureLowOutputChange PressureLowOutputPhysicalKernel PressureLowOutputScaledKernel
open PressureLowOutputDyadicBudget CoherentPressurePair PressureTiltSymbol PancakeAnisotropyDepletion
open scoped RealInnerProductSpace FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

private def vec3 (a b c : ℝ) : R3 := WithLp.toLp 2 ![a, b, c]

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [vec3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

example (k p : R3) : frequencyChange (1 / 2) (pairEquiv.symm (k, p)) =
    pairEquiv.symm (k, (2 : ℝ) • (k + p)) := by
  simp [frequencyChange]

example (x : E6) : ‖(spatialChange (1 / 2) (by norm_num)).symm x‖ ≤ 6 * ‖x‖ := by
  have h := norm_spatialChange_symm_le (1 / 2) (by norm_num) (by norm_num) x
  norm_num at h ⊢
  exact h

/-- Exact input cancellation has zero pressure at every positive common frequency scale. -/
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e k w v : R3) (i : Fin 3) :
    (𝓕 (scaledKernel N hN (t, e) w v i)) (pairEquiv.symm (k, -k)) = 0 := by
  rw [fourier_scaledKernel]
  simp [tiltPair, tiltSymbol_zero]

/-- Common negative scaling also leaves the pressure-pair amplitude unchanged. -/
example (e k p w v : R3) : tiltPair e ((-2 : ℝ) • k) ((-2 : ℝ) • p) w v =
    tiltPair e k p w v := tiltPair_smul_frequencies (-2) (by norm_num) e k p w v

/-- A retained physical pressure entry is explicitly nonzero after the coordinate change. -/
example : (𝓕 (physicalKernel (1 / 2, vec3 1 0 0) (vec3 0 0 1) (vec3 0 0 1) 1))
    (pairEquiv.symm (vec3 1 0 0, vec3 (-255 / 256) (1 / 256) 0)) = (-1 / 130052 : ℂ) := by
  have hk : ‖vec3 1 0 0‖ = 1 := by
    have h := norm_vec3_sq 1 0 0
    nlinarith [norm_nonneg (vec3 1 0 0)]
  have hq0 : 1 ≤ ‖vec3 1 1 0‖ := by
    have h := norm_vec3_sq 1 1 0
    nlinarith [norm_nonneg (vec3 1 1 0)]
  have hq1 : ‖vec3 1 1 0‖ ≤ 2 := by
    have h := norm_vec3_sq 1 1 0
    nlinarith [norm_nonneg (vec3 1 1 0)]
  have hck := cutoff_eq_one (vec3 1 0 0) (by rw [hk]) (by rw [hk]; norm_num)
  have hcq := cutoff_eq_one (vec3 1 1 0) hq0 hq1
  have hq : (ratio (1 / 2))⁻¹ • (vec3 1 0 0 + vec3 (-255 / 256) (1 / 256) 0) = vec3 1 1 0 := by
    ext i
    fin_cases i <;> norm_num [ratio, vec3]
  have hc : physicalCutoff (1 / 2)
      (pairEquiv.symm (vec3 1 0 0, vec3 (-255 / 256) (1 / 256) 0)) = 1 := by
    rw [physicalCutoff, pairEquiv.apply_symm_apply, hq,
      parameterCutoff_eq_one (1 / 2) (by constructor <;> norm_num), hck, hcq]
    norm_num
  rw [fourier_physicalKernel, hc]
  norm_num [tiltPair, tracePair, tiltSymbol, lineRemainder, cross, cross_apply, vec3,
    EuclideanSpace.norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The output/input ratios have an actual finite infinite sum. -/
example : (∑' n : ℕ, ratio (dyadicParameter n)) = (1 / 128 : ℝ) ∧
    (∑' n : ℕ, (ratio (dyadicParameter n)) ^ 2) = (1 / 49152 : ℝ) :=
  ⟨hasSum_ratio.tsum_eq, hasSum_ratio_sq.tsum_eq⟩

end Mettapedia.FluidDynamics.NavierStokes.PressurePhysicalKernelAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget.dyadicParameter_mem
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget.ratio_dyadicParameter
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget.hasSum_ratio
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget.hasSum_ratio_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget.exists_uniform_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget.exists_uniform_firstMoment_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel.fourier_scaledKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel.mass_scaledKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel.firstMoment_scaledKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel.exists_uniform_basis_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel.exists_uniform_basis_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel.fourier_physicalKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel.physicalKernel_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel.mass_physicalKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel.exists_uniform_basis_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel.firstMoment_physicalKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel.exists_uniform_basis_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.norm_sq_pair
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.norm_first_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.norm_second_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.norm_pair_symm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.inner_pair
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.spatialChange_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.spatialChange_symm_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.norm_spatialChange_symm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.opNorm_spatialChange_symm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange.inverse_adjoint_eq_frequencyChange
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates.tracePair_smul_frequencies
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates.tiltPair_smul_frequencies
