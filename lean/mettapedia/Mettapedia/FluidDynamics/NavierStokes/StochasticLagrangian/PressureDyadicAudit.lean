import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPartition

/-! Nonzero and zero-output checks for exact-partition pressure kernels. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAudit

open Mettapedia.Analysis.DyadicAnnulus Mettapedia.Analysis.EuclideanCrossProduct
open PressureLowOutputCutoff (ratio parameterCutoff_eq_one)
open PressureLowOutputSymbol (pairEquiv)
open PressureDyadicPhysicalKernel PressureDyadicPartition
open CoherentPressurePair PressureTiltSymbol PancakeAnisotropyDepletion
open scoped RealInnerProductSpace FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

private def vec3 (a b c : ℝ) : R3 := WithLp.toLp 2 ![a, b, c]

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [vec3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- Both normalized annuli contribute a factor one half to this nonzero coefficient. -/
example : (𝓕 (physicalKernel (1 / 2, vec3 1 0 0) (vec3 0 0 1) (vec3 0 0 1) 1))
    (pairEquiv.symm (vec3 1 0 0, vec3 (-1277 / 1280) (1 / 320) 0)) =
      (-48 / 40768625 : ℂ) := by
  have hk : ‖vec3 1 0 0‖ = 1 := by
    have h := norm_vec3_sq 1 0 0
    nlinarith [norm_nonneg (vec3 1 0 0)]
  have hqnorm : ‖vec3 (3 / 5) (4 / 5) 0‖ = 1 := by
    have h := norm_vec3_sq (3 / 5) (4 / 5) 0
    nlinarith [norm_nonneg (vec3 (3 / 5) (4 / 5) 0)]
  have hq : (ratio (1 / 2))⁻¹ • (vec3 1 0 0 + vec3 (-1277 / 1280) (1 / 320) 0) =
      vec3 (3 / 5) (4 / 5) 0 := by
    ext i
    fin_cases i <;> norm_num [ratio, vec3]
  have hc : physicalCutoff (1 / 2)
      (pairEquiv.symm (vec3 1 0 0, vec3 (-1277 / 1280) (1 / 320) 0)) = 1 / 4 := by
    rw [physicalCutoff, pairEquiv.apply_symm_apply, hq,
      parameterCutoff_eq_one (1 / 2) (by constructor <;> norm_num),
      normalizedCutoff_eq_half_of_norm_eq_one _ hk,
      normalizedCutoff_eq_half_of_norm_eq_one _ hqnorm]
    norm_num
  rw [fourier_physicalKernel, hc]
  norm_num [tiltPair, tracePair, tiltSymbol, lineRemainder, cross, cross_apply, vec3,
    EuclideanSpace.norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The reconstruction theorem includes zero output, without a false partition identity there. -/
example (N : ℝ) (hN : 0 < N) (e k w v : R3) (i : Fin 3) :
    HasSum (fun n : ℕ ↦ (𝓕 (scaledKernel N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n, e) w v i)) (pairEquiv.symm (k, -k))) 0 := by
  have h := hasSum_fourier_scaledKernel N hN e w v i (pairEquiv.symm (k, -k))
    (by simpa using div_nonneg hN.le (by norm_num : (0 : ℝ) ≤ 256))
  simpa [tiltPair, tiltSymbol_zero] using h

/-- Summing the same nonzero coefficient restores the output partition, leaving
only the one-half input-annulus weight. -/
example : HasSum (fun n : ℕ ↦ (𝓕 (scaledKernel 1 (by norm_num)
      (PressureLowOutputDyadicBudget.dyadicParameter n, vec3 1 0 0)
      (vec3 0 0 1) (vec3 0 0 1) 1))
      (pairEquiv.symm (vec3 1 0 0, vec3 (-1277 / 1280) (1 / 320) 0)))
    (-96 / 40768625 : ℂ) := by
  have hk : ‖vec3 1 0 0‖ = 1 := by
    have h := norm_vec3_sq 1 0 0
    nlinarith [norm_nonneg (vec3 1 0 0)]
  have he : vec3 1 0 0 + vec3 (-1277 / 1280) (1 / 320) 0 = vec3 (3 / 1280) (1 / 320) 0 := by
    ext i
    fin_cases i <;> norm_num [vec3]
  have hsmall : ‖vec3 1 0 0 + vec3 (-1277 / 1280) (1 / 320) 0‖ ≤ 1 / 256 := by
    rw [he]
    have h := norm_vec3_sq (3 / 1280) (1 / 320) 0
    nlinarith [norm_nonneg (vec3 (3 / 1280) (1 / 320) 0)]
  have h := hasSum_fourier_scaledKernel 1 (by norm_num) (vec3 1 0 0)
    (vec3 0 0 1) (vec3 0 0 1) 1
    (pairEquiv.symm (vec3 1 0 0, vec3 (-1277 / 1280) (1 / 320) 0)) (by simpa using hsmall)
  simp only [pairEquiv.apply_symm_apply, inv_one, one_smul,
    normalizedCutoff_eq_half_of_norm_eq_one _ hk] at h
  convert h using 1
  norm_num [tiltPair, tracePair, tiltSymbol, lineRemainder, cross, cross_apply, vec3,
    EuclideanSpace.norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The corrected kernels, not the old overlapping family, have a uniform summed first moment. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
    (∑' n, ∫ x : E6, ‖x‖ * ‖dyadicKernel N hN e i j l n x‖) ≤ C / N := by
  obtain ⟨C, hC, h⟩ := exists_uniform_firstMoment_budget
  exact ⟨C, hC, fun N hN e he i j l ↦ (h N hN e he i j l).2⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.inverse_ratio_dyadicParameter
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.physicalCutoff_dyadicParameter
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.summable_physicalCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.tsum_physicalCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.tsum_scaled_physicalCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.hasSum_fourier_scaledKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.exists_uniform_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition.exists_uniform_firstMoment_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.fourier_physicalKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.mass_physicalKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.exists_uniform_basis_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.exists_uniform_basis_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.fourier_scaledKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.exists_uniform_scaled_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel.exists_uniform_scaled_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.fourier_kernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.exists_uniform_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.fourier_retainedKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.moment_retainedKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.exists_uniform_retained_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.retainedKernel_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel.exists_uniform_basis_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.retained_eq_corrected
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.entry_eq_pressure
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.contDiff_entry
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.tsupport_entry_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.symbol_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.contDiff_symbol
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol.tsupport_symbol_subset
