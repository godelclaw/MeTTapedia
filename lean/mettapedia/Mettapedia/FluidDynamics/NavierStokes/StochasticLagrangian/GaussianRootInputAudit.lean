import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootInputBudget

/-! Temperature normalization, true Fourier data, and the constructed input-scale family. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputAudit

open PeriodicFourierTriad PancakeCurlOutputTail PancakeFrequencyProjectorCommutator
open AdaptiveGaussianLinePartition GaussianRootInputBudget

local notation "T3" => UnitAddTorus (Fin 3)

example (rho : ℝ) : temperature 1 rho = rho ^ 2 / 4 := by simp [temperature]

/-- Increasing the cover size genuinely lowers the temperature. -/
example : temperature 2 1 < temperature 1 1 := by
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simp only [temperature, Nat.cast_ofNat, one_pow, Nat.cast_one, Real.log_one, add_zero, mul_one]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + Real.log 2))).mpr
  nlinarith

example : inputScale 3 4 = 48 := by norm_num [inputScale]

/-- A genuine finite Fourier field has every required moment, including nonzero modes. -/
example (k : Wavevector) (v : VelocityCoefficient) : Summable (fourierMoment 3 (Pi.single k v)) := by
  classical
  apply summable_of_ne_finset_zero (s := {k})
  intro q hq
  have hne : q ≠ k := by simpa only [Finset.mem_singleton] using hq
  simp [fourierMoment, Pi.single_eq_of_ne hne, coefficientVec]

/-- The same cover-size bound works before choosing any contractive filter sequence. -/
example (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (gamma : ℝ) (hg : 0 < gamma) (rho : ℝ) (hrho : 0 < rho) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ chi : ℕ → Wavevector → ℂ, ∀ modes : ℕ → Finset Wavevector,
      (∀ j q, q ∈ modes j → ‖chi j q‖ ≤ 1) →
      ∃ centers : ℕ → Finset T3,
        (∀ j, (centers j).Nonempty ∧ (centers j).card ≤ M) ∧
        Summable (fun j : ℕ ↦ fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
          gamma (chi j) (modes j) u (centers j) rho) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_input_budget
  obtain ⟨M, hM, hfamily⟩ := h u hu gamma hg rho hrho
  refine ⟨M, hM, ?_⟩
  intro N hN chi modes hchi
  obtain ⟨centers, hp, hs, _⟩ := hfamily N hN chi modes hchi
  exact ⟨centers, fun j ↦ ⟨(hp j).1, (hp j).2.1⟩, hs⟩

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition.gaussian_line_partition_of_cover
#print axioms Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition.exists_gaussian_line_partition
#print axioms Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition.temperature_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition.temperature_antitone_card
#print axioms Mettapedia.FluidDynamics.NavierStokes.BoundedGaussianLinePartition.exists_bounded_gaussian_line_partition
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient.locallyLipschitz_gate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient.continuous_gate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient.ae_coordinate_differentiable_gate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient.norm_deriv_gate_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient.norm_coordinate_gate_deriv_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient.gradientSquare_gate_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget.partitionMultiplier_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget.continuous_gradientDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget.localAmplitude_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget.ae_rootGradient_le_of_patch_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget.exists_uniform_root_gradient_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformStrainGradientBudget.envelope_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformStrainGradientBudget.strainGradientAmplitude_le_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformStrainGradientBudget.norm_strainGradient_le_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.UniformStrainGradientBudget.sum_norm_strainGradient_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget.gradientEnergyBudget_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget.integral_gradientDensity_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget.inputScale_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget.exists_uniform_input_budget
