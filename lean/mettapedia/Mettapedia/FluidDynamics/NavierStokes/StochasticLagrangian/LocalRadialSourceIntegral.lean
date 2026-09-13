import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialMeanBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RadialSourceLocalBound

/-!
# Removing the radial cutoff from the signed local time balance

On a compact smooth interval, the actual radial sources converge under the
time integral. Their signed time-weighted mean rates consequently converge
as whole integrals, without a termwise image/time/cutoff exchange. The local
Fourier majorant justifies this passage but does not pay the open budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral

open MeasureTheory Filter Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakePeriodicVorticityEquation
open LocalVorticityEighthMoment LocalRadialMeanRegularity LocalRadialMeanBalance
open scoped Topology

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem intervalIntegrable_source (n N : ℕ) :
    IntervalIntegrable (fun τ ↦ VorticityRadialSource.source (2 * (n + 1)) N (s.coefficients τ))
      volume a b :=
  (absolutelyContinuousOnInterval_source s a b hab hI g hg hSum hu n N).continuousOn.intervalIntegrable

theorem tendsto_integral_source :
    Tendsto (fun N : ℕ ↦ ∫ τ in a..b, VorticityRadialSource.source 6 N (s.coefficients τ)) atTop
      (𝓝 (∫ τ in a..b, stretching (s.coefficients τ))) := by
  let bound := fun τ ↦ (9 * ‖unitTorusDerivativePhase‖ * ∑' q, g q) * meanEnergy (s.coefficients τ)
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ Ioo_subset_Icc_self (hI hτ)
  have hmem : uIoc a b ⊆ Icc a b := by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
  have hu1 (τ : ℝ) (hτ : τ ∈ Icc a b) (q : Wavevector) :
      fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by norm_num : 1 ≤ 3) q).trans (hu τ (hsub hτ) q)
  have hsum1 (τ : ℝ) (hτ : τ ∈ Icc a b) : Summable (fourierMoment 1 (s.coefficients τ)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu1 τ hτ)
  have hB : IntervalIntegrable bound volume a b :=
    (((continuousOn_meanEnergy s g hSum hu).mono hsub).intervalIntegrable_of_Icc hab).const_mul _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall (fun N ↦ (intervalIntegrable_source s a b hab hI g hg hSum hu 2 N).def'.1)
  · exact Eventually.of_forall (fun N ↦ Eventually.of_forall (fun τ hτ ↦
      VorticityRadialSource.norm_source_six_le_envelope N _ g hSum (hu1 τ (hmem hτ))
        (s.reality τ) (s.transverse τ)))
  · exact hB
  · exact Eventually.of_forall (fun τ hτ ↦ VorticityRadialSource.tendsto_eighthMoment_source
      (s.coefficients τ) (hsum1 τ (hmem hτ)) (s.reality τ) (s.transverse τ))

/-- Convergence of the complete signed integrals; no individual rate limit is asserted. -/
theorem tendsto_integral_weighted_meanRate :
    Tendsto (fun N : ℕ ↦ ∫ τ in a..b, (b - τ) * meanRate 2 N nu (s.coefficients τ)) atTop
      (𝓝 ((∫ τ in a..b, stretching (s.coefficients τ)) - (b - a) * stretching (s.coefficients a))) := by
  have ha := VorticityRadialSource.tendsto_eighthMoment_source (s.coefficients a)
    (summable_fourierMoment_of_le _ (by norm_num : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu a (Ioo_subset_Icc_self (hI ⟨le_rfl, hab⟩)))))
    (s.reality a) (s.transverse a)
  have he (N : ℕ) : (∫ τ in a..b, (b - τ) * meanRate 2 N nu (s.coefficients τ)) =
      (∫ τ in a..b, VorticityRadialSource.source 6 N (s.coefficients τ)) -
        (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) := by
    have h := (integral_source_eq_initial_add_weighted_rate s a b hab hI g hg hSum hu 2 N).2
    change _ = (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) + _ at h
    linarith only [h]
  simp_rw [he]
  exact (tendsto_integral_source s a b hab hI g hg hSum hu).sub (ha.const_mul (b - a))

/-- An explicit sufficient upper-budget obligation, with the endpoint term retained. -/
theorem integral_stretching_le_of_weighted_rate_le (remainder : ℝ)
    (hbudget : ∀ N, (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) +
      (∫ τ in a..b, (b - τ) * meanRate 2 N nu (s.coefficients τ)) ≤
        nu / 2 * (∫ τ in a..b, weightedPalinstrophy (s.coefficients τ)) + remainder) :
    (∫ τ in a..b, stretching (s.coefficients τ)) ≤
      nu / 2 * (∫ τ in a..b, weightedPalinstrophy (s.coefficients τ)) + remainder := by
  apply le_of_tendsto (tendsto_integral_source s a b hab hI g hg hSum hu)
  apply Eventually.of_forall
  intro N
  rw [(integral_source_eq_initial_add_weighted_rate s a b hab hI g hg hSum hu 2 N).2]
  exact hbudget N

/-- Conditional absorption into the actual eighth-moment energy identity.
The signed rate budget above is an explicit hypothesis, not a proved estimate. -/
theorem energy_add_half_dissipation_le_of_weighted_rate_le (hnu : 0 ≤ nu) (remainder : ℝ)
    (hbudget : ∀ N, (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) +
      (∫ τ in a..b, (b - τ) * meanRate 2 N nu (s.coefficients τ)) ≤
        nu / 2 * (∫ τ in a..b, weightedPalinstrophy (s.coefficients τ)) + remainder) :
    meanEnergy (s.coefficients b) / 8 +
      nu / 2 * (∫ τ in a..b, weightedPalinstrophy (s.coefficients τ)) ≤
        meanEnergy (s.coefficients a) / 8 + remainder := by
  have hs := integral_stretching_le_of_weighted_rate_le s a b hab hI g hg hSum hu remainder hbudget
  have he := interior_energy_identity s g hg hSum hu a b hab hI
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T := hI.trans Ioo_subset_Icc_self
  have hG := ((continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hR := ((continuousOn_radialDissipation s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  rw [intervalIntegral.integral_add (hG.const_mul nu) (hR.const_mul (6 * nu)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  have hr : 0 ≤ 6 * nu * (∫ τ in a..b, radialDissipation (s.coefficients τ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hnu)
      (intervalIntegral.integral_nonneg_of_forall hab (fun τ ↦ radialDissipation_nonneg _))
  linarith only [he, hs, hr]

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral
