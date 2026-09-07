import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalSpatialVelocity

/-!
# Joint uniform spatial convergence of the actual Galerkin subsequence

Uniformly small Sobolev tails combine with finitely many converging coefficient
paths. The resulting convergence holds in the time-space supremum norm for
the reconstructed fields, not just separately at each Fourier coefficient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinSpatialLimit

open scoped BigOperators Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeSobolevSpaceTime PancakeSobolevAbsoluteTail PancakeSobolevVelocityRate
open PancakePhysicalFourierDerivative PancakeLocalVelocityExistence PancakeConvectionPathLimit
open PancakeInfiniteFourierDerivative

theorem norm_modeSpaceTime_sub_le {T : ℝ} (a b : CoefficientLimit T)
    (k : Wavevector) (i : Fin 3) :
    ‖modeSpaceTime a k i - modeSpaceTime b k i‖ ≤ ‖a k i - b k i‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro z
  simp only [BoundedContinuousFunction.sub_apply, modeSpaceTime_apply]
  rw [← mul_sub, norm_mul, norm_character, one_mul]
  exact (a k i - b k i).norm_coe_le_norm z.1

theorem tendsto_modeSpaceTime {T : ℝ} (aₙ : ℕ → CoefficientLimit T) (a : CoefficientLimit T)
    (k : Wavevector) (i : Fin 3)
    (h : Tendsto (fun n ↦ aₙ n k i) atTop (𝓝 (a k i))) :
    Tendsto (fun n ↦ modeSpaceTime (aₙ n) k i) atTop (𝓝 (modeSpaceTime a k i)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp h ε hε] with n hn
  exact lt_of_le_of_lt
    (by simpa only [dist_eq_norm] using norm_modeSpaceTime_sub_le (aₙ n) a k i) hn

theorem tendsto_spatialPath {T : ℝ} (aₙ : ℕ → CoefficientLimit T) (a : CoefficientLimit T)
    (h : ∀ k i, Tendsto (fun n ↦ aₙ n k i) atTop (𝓝 (a k i)))
    (B : ℝ) (hB : ∀ n t F, sobolevEnergy F (limitField (aₙ n) t) ≤ B)
    (hA : ∀ t F, sobolevEnergy F (limitField a t) ≤ B) (i : Fin 3) :
    Tendsto (fun n ↦ spatialPath (aₙ n) i) atTop (𝓝 (spatialPath a i)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ := exists_small_tailAllowance B (ε/3) (by positivity)
  have hf := tendsto_finsetSum F (fun k _ ↦ tendsto_modeSpaceTime aₙ a k i (h k i))
  filter_upwards [Metric.tendsto_nhds.mp hf (ε/3) (by positivity)] with n hn
  have h1 : dist (spatialPath (aₙ n) i) (∑ k ∈ F, modeSpaceTime (aₙ n) k i) ≤
      tailAllowance B F := by
    simpa only [dist_eq_norm] using norm_spatialPath_sub_sum_le (aₙ n) B (hB n) F i
  have h2 : dist (∑ k ∈ F, modeSpaceTime a k i) (spatialPath a i) ≤ tailAllowance B F := by
    rw [dist_comm]
    simpa only [dist_eq_norm] using norm_spatialPath_sub_sum_le a B hA F i
  have ht := (dist_triangle (spatialPath (aₙ n) i)
    (∑ k ∈ F, modeSpaceTime (aₙ n) k i) (spatialPath a i)).trans
      (add_le_add le_rfl (dist_triangle (∑ k ∈ F, modeSpaceTime (aₙ n) k i)
        (∑ k ∈ F, modeSpaceTime a k i) (spatialPath a i)))
  linarith

/-- The same actual subsequence converges uniformly on the full time-space cylinder. -/
theorem coefficientLimit_spatial_uniform {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (B : ℝ)
    (hB : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B) (i : Fin 3) :
    TendstoUniformly
      (fun n (z : SpaceTime T) ↦ fullFourierField id ((s (phi n)).coefficients z.1) z.2 i)
      (fun z : SpaceTime T ↦ fullFourierField id (limitField a z.1) z.2 i) atTop := by
  have happrox (n : ℕ) (t : Set.Icc (0 : ℝ) T) (F : Finset Wavevector) :
      sobolevEnergy F (limitField (solutionPaths (s (phi n))) t) ≤ B :=
    (sobolevEnergy_of_support_le _ F _ ((s (phi n)).support t)).trans
      (hB (phi n) t t.2)
  have hlimit := limitField_finite_sobolev_bound s phi a h B hB
  have hn := tendsto_spatialPath (fun n ↦ solutionPaths (s (phi n))) a
    (fun k j ↦ BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr (h k j))
    B happrox hlimit i
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hn
  have he (n : ℕ) (z : SpaceTime T) :
      spatialPath (solutionPaths (s (phi n))) i z =
        fullFourierField id ((s (phi n)).coefficients z.1) z.2 i :=
    spatialPath_eq_fullFourierField _ B (happrox n) i z
  have ha (z : SpaceTime T) : spatialPath a i z =
      fullFourierField id (limitField a z.1) z.2 i :=
    spatialPath_eq_fullFourierField a B hlimit i z
  change TendstoUniformly (fun n z ↦ spatialPath (solutionPaths (s (phi n))) i z)
    (fun z ↦ spatialPath a i z) atTop at hu
  simpa only [he, ha] using hu

end Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinSpatialLimit
