import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy

/-! Regression checks and foundational dependencies for the actual eighth-moment balance. -/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity LocalVorticityEighthMoment
open LocalLowDiffusionBudget
open GaussianRootWeightedIncrement (weightedPalinstrophyDensity)

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (u : FourierVelocity) (x : T3) : energy u x = ‖fullVorticity u x‖ ^ 8 :=
  energy_eq_norm_pow u x

example (u : FourierVelocity) (x : T3) (hw : fullVorticity u x = 0) :
    energy u x = 0 ∧ weightedPalinstrophyDensity u x = 0 ∧
      radialGradientDensity u x = 0 ∧ stretchingDensity u x = 0 := by
  simp [energy, weightedPalinstrophyDensity, radialGradientDensity, stretchingDensity, hw]

example (u : FourierVelocity) : 0 ≤ weightedPalinstrophy u ∧ 0 ≤ radialDissipation u :=
  ⟨weightedPalinstrophy_nonneg u, radialDissipation_nonneg u⟩

example (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, materialRate u 0 x) / 8 = stretching u := by
  simpa only [zero_mul, mul_zero, add_zero, stretching] using
    integral_materialRate_add_dissipation_eq u 0 hu

example (u : FourierVelocity) (nu : ℝ) (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, materialRate u nu x) / 8 =
      stretching u - nu * weightedPalinstrophy u - 6 * nu * radialDissipation u := by
  have h := integral_materialRate_add_dissipation_eq u nu hu
  change _ + nu * weightedPalinstrophy u + 6 * nu * radialDissipation u = stretching u at h
  linarith only [h]

example {T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution 0 u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)
    (hT : 0 < T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 8 = meanEnergy u₀ / 8 +
      ∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ) := by
  simpa only [zero_mul, mul_zero, add_zero] using energy_identity s g hg hSum hu hT t ht

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)
    (hT : 0 < T) :
    meanEnergy (s.coefficients 0) / 8 = meanEnergy u₀ / 8 := by
  simpa only [intervalIntegral.integral_same, mul_zero, add_zero] using
    energy_identity s g hg hSum hu hT 0 ⟨le_rfl, hT.le⟩

example (t : ℝ) : deriv (deriv (fun s : ℝ ↦ s ^ 4)) t = 12 * t ^ 2 := by
  have h := Mettapedia.Analysis.deriv_deriv_fun_pow_add_two
    (f := fun s : ℝ ↦ s) (contDiffAt_id : ContDiffAt ℝ 2 (fun s : ℝ ↦ s) t) 2
  norm_num at h ⊢
  exact h

example (T : ℝ) (hT : 0 < T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    -2 * t + (∫ _ in (0 : ℝ)..t, (1 : ℝ)) = ∫ _ in (0 : ℝ)..t, (-1 : ℝ) := by
  have h := intervalIntegral.endpoint_identity_of_interior
    (A := fun r ↦ -2 * r) (Z := fun _ ↦ 1) (R := fun _ ↦ -1)
    hT (by fun_prop) (by fun_prop) (by fun_prop)
    (fun a b _ _ _ ↦ by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring) t ht
  simpa only [mul_zero, zero_add] using h

#print axioms Mettapedia.Analysis.deriv_deriv_fun_pow_add_two
#print axioms intervalIntegral.endpoint_identity_of_interior_of_integrable
#print axioms intervalIntegral.endpoint_identity_of_interior
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.energySecond_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.energyLaplacian_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.materialRate_sub_diffusion_add_dissipation_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.hasDerivAt_frozenEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.integrable_energySecond_and_integral_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.integrable_energyLaplacian_and_integral_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.integral_materialRate_add_dissipation_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.continuous_energy_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.continuous_weightedPalinstrophyDensity_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.continuous_radialGradientDensity_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.continuous_stretchingDensity_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.locallyLipschitz_extendedEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.frozenMaterialRate_extension_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.intervalIntegral_materialRate_eq_meanEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.interior_energy_identity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.energy_identity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.energy_add_half_dissipation_le_of_stretching_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment.exists_physical_local_energy_identity
