import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourceContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedSourceBound

/-!
# A signed time-integrated annular remainder suffices for the L8 energy estimate

Only the integrals of the remainders must have a cutoff-independent upper
bound. Neither a pointwise envelope nor convergence of those remainders is
assumed. The local Fourier envelope justifies dominated convergence of the
actual sources and does not occur in the resulting energy bound.

The remainder budget itself remains an explicit hypothesis, not a constructed
dynamical estimate or a claim of global regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral

open MeasureTheory Filter PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakePeriodicVorticityEquation
open LocalVorticityEighthMoment LocalAnnularSourceContinuity VorticityAnnularPolynomialSource
open VorticityRegularizedIncrement
open scoped Topology

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hSum hu

theorem intervalIntegrable_pairedSource (n N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ pairedSource n N (s.coefficients τ)) volume 0 t :=
  ((continuousOn_pairedSource s g hSum hu n N).mono
    (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1

theorem intervalIntegrable_highAmplitudeSource (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ highAmplitudeSource n L N (s.coefficients τ)) volume 0 t :=
  ((continuousOn_highAmplitudeSource s g hSum hu n N L hL).mono
    (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1

theorem tendsto_integral_pairedSource (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N : ℕ ↦ ∫ τ in (0 : ℝ)..t, pairedSource 6 N (s.coefficients τ)) atTop
      (𝓝 (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ))) := by
  let bound := fun τ ↦ (9 * ‖unitTorusDerivativePhase‖ * ∑' q, g q) * meanEnergy (s.coefficients τ)
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hmem : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self
  have hu1 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) (q : Wavevector) :
      fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by norm_num : 1 ≤ 3) q).trans (hu τ (hsub hτ) q)
  have hsum1 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) :
      Summable (fourierMoment 1 (s.coefficients τ)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu1 τ hτ)
  have hB : IntervalIntegrable bound volume 0 t :=
    (((continuousOn_meanEnergy s g hSum hu).mono hsub).intervalIntegrable_of_Icc ht.1).const_mul _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall (fun N ↦ (intervalIntegrable_pairedSource s g hSum hu 6 N t ht).def'.1)
  · apply Eventually.of_forall
    intro N
    exact Eventually.of_forall (fun τ hτ ↦ by
      rw [← source_eq_pairedSource 6 N _ (hsum1 τ (hmem hτ))]
      exact VorticityRegularizedSource.norm_source_six_le_envelope N _ g hSum (hu1 τ (hmem hτ))
        (s.reality τ) (s.transverse τ))
  · exact hB
  · exact Eventually.of_forall (fun τ hτ ↦ by
      have h := VorticityRegularizedSource.tendsto_eighthMoment_source
        (s.coefficients τ) (hsum1 τ (hmem hτ)) (s.reality τ) (s.transverse τ)
      simpa only [source_eq_pairedSource 6 _ _ (hsum1 τ (hmem hτ))] using h)

/-- The upper budget is needed only after time integration. Its sign is unrestricted. -/
theorem integral_stretching_le_of_remainder_integral_le (hnu : 0 < nu)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (remainder : ℝ)
    (hbudget : ∀ N, (∫ τ in (0 : ℝ)..t,
      highAmplitudeSource 6 (dissipationThreshold nu) N (s.coefficients τ)) ≤ remainder) :
    (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ)) ≤
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) + remainder := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hG := ((continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  apply le_of_tendsto (tendsto_integral_pairedSource s g hSum hu t ht)
  apply Eventually.of_forall
  intro N
  have hR := intervalIntegrable_highAmplitudeSource s g hSum hu 6 N
    (dissipationThreshold nu) (dissipationThreshold_pos nu hnu) t ht
  calc
    _ ≤ ∫ τ in (0 : ℝ)..t, nu / 2 * weightedPalinstrophy (s.coefficients τ) +
        highAmplitudeSource 6 (dissipationThreshold nu) N (s.coefficients τ) :=
      intervalIntegral.integral_mono_on ht.1 (intervalIntegrable_pairedSource s g hSum hu 6 N t ht)
        ((hG.const_mul (nu / 2)).add hR) (fun τ hτ ↦
          pairedSource_le_half_dissipation_add_remainder nu hnu N _
            (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ))))
    _ = nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
        (∫ τ in (0 : ℝ)..t, highAmplitudeSource 6 (dissipationThreshold nu) N (s.coefficients τ)) := by
      rw [intervalIntegral.integral_add (hG.const_mul (nu / 2)) hR, intervalIntegral.integral_const_mul]
    _ ≤ _ := add_le_add le_rfl (hbudget N)

include hg in
theorem energy_add_half_dissipation_le_of_remainder_integral_le (hnu : 0 < nu) (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (remainder : ℝ)
    (hbudget : ∀ N, (∫ τ in (0 : ℝ)..t,
      highAmplitudeSource 6 (dissipationThreshold nu) N (s.coefficients τ)) ≤ remainder) :
    meanEnergy (s.coefficients t) / 8 +
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤
        meanEnergy u₀ / 8 + remainder :=
  energy_add_half_dissipation_le_of_stretching_bound s g hg hSum hu hnu.le hT t ht remainder
    (integral_stretching_le_of_remainder_integral_le s g hSum hu hnu t ht remainder hbudget)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral
