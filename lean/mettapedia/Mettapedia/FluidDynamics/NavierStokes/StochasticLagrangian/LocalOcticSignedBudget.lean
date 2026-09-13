import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticEndpointBalance

/-!
# Signed integrated cost of the octic correction

The correction's contribution to the integrated residual is an endpoint
correlation difference plus the mixed curvature integral. This identity
retains time cancellation. It gives a cutoff-uniform bound from the eighth
moment and its dissipation, and a closed bound when stretching vanishes.
Vanishing stretching is not asserted for arbitrary Navier–Stokes data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalOcticSignedBudget

open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalOcticCorrelation LocalOcticMeanBalance
open LocalOcticCorrectedEnergy LocalOcticEndpointBalance
open LocalVorticityEighthMoment (meanEnergy weightedPalinstrophy radialDissipation stretching)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuousOn_signedRate (N : ℕ) :
    ContinuousOn (fun t ↦ signedRate N ν (s.coefficients t)) (Icc 0 T) :=
  (continuousOn_nonviscousMeanRate s g hSum hu N).sub
    (((continuousOn_pureContribution s g hSum hu N).add
      (continuousOn_mixedContribution s g hSum hu N)).const_mul ν)

include hg hSum hu in
theorem integral_signedRate_eq_initial (N : ℕ) (hT : 0 < T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, signedRate N ν (s.coefficients τ)) =
      correlation N (s.coefficients t) - correlation N u₀ := by
  have h := intervalIntegral.endpoint_identity_of_interior hT
    (continuousOn_correlation s g hSum hu N) (continuousOn_const (c := (0 : ℝ)))
    (continuousOn_signedRate s g hSum hu N)
    (fun a b ha hab hb ↦ by
      have he := (integral_signedRate_eq s a b hab.le
        (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩) g hg hSum hu N).2
      simp only [intervalIntegral.integral_zero, add_zero]
      linarith only [he]) t ht
  simp only [intervalIntegral.integral_zero, add_zero, s.initial] at h
  linarith only [h]

include hg hSum hu in
theorem integral_residual_sub_stretching_eq (N : ℕ) (ε : ℝ) (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, LocalOcticCorrectedEnergy.residual N ν ε (s.coefficients τ)) -
        (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ)) =
      ε * (correlation N (s.coefficients t) - correlation N u₀) +
        ν * ε * (∫ τ in (0 : ℝ)..t, mixedGradientContribution N (s.coefficients τ)) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hS := ((LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hR := ((continuousOn_signedRate s g hSum hu N).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hM := ((continuousOn_mixedContribution s g hSum hu N).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  simp_rw [residual_eq_signedRate_add_mixed]
  rw [intervalIntegral.integral_add (hS.add (hR.const_mul ε)) (hM.const_mul (ν * ε)),
    intervalIntegral.integral_add hS (hR.const_mul ε),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_signedRate_eq_initial s g hg hSum hu N hT t ht]
  ring

include hg hSum hu in
theorem abs_integral_residual_sub_stretching_le (N : ℕ) (ε : ℝ) (hν : 0 ≤ ν)
    (hT : 0 < T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    |(∫ τ in (0 : ℝ)..t, LocalOcticCorrectedEnergy.residual N ν ε (s.coefficients τ)) -
        (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ))| ≤
      |ε| * (9 * (meanEnergy (s.coefficients t) + meanEnergy u₀) +
        288 * ν * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ))) := by
  have hm (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ)
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hG := ((LocalVorticityEighthMoment.continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hM := ((continuousOn_mixedContribution s g hSum hu N).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hMb : |∫ τ in (0 : ℝ)..t, mixedGradientContribution N (s.coefficients τ)| ≤
      288 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) := by
    calc
      _ ≤ ∫ τ in (0 : ℝ)..t, |mixedGradientContribution N (s.coefficients τ)| :=
        intervalIntegral.abs_integral_le_integral_abs ht.1
      _ ≤ ∫ τ in (0 : ℝ)..t, 288 * weightedPalinstrophy (s.coefficients τ) :=
        intervalIntegral.integral_mono_on ht.1 hM.abs (hG.const_mul 288)
          (fun τ hτ ↦ abs_mixedGradientContribution_le N _
            (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) (hm τ (hsub hτ))))
      _ = _ := intervalIntegral.integral_const_mul _ _
  have h0 : Summable (fourierMoment 1 u₀) := by
    simpa only [s.initial] using summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) (hm 0 ⟨le_rfl, hT.le⟩)
  have hC : |correlation N (s.coefficients t) - correlation N u₀| ≤
      9 * (meanEnergy (s.coefficients t) + meanEnergy u₀) :=
    (abs_sub _ _).trans ((add_le_add
      (abs_correlation_le N _ (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) (hm t ht)))
      (abs_correlation_le N u₀ h0)).trans_eq (by ring))
  rw [integral_residual_sub_stretching_eq s g hg hSum hu N ε hT t ht]
  calc
    _ ≤ |ε * (correlation N (s.coefficients t) - correlation N u₀)| +
        |ν * ε * (∫ τ in (0 : ℝ)..t, mixedGradientContribution N (s.coefficients τ))| := abs_add_le _ _
    _ = |ε| * |correlation N (s.coefficients t) - correlation N u₀| +
        ν * |ε| * |∫ τ in (0 : ℝ)..t, mixedGradientContribution N (s.coefficients τ)| := by
      simp only [abs_mul, abs_of_nonneg hν]
    _ ≤ |ε| * (9 * (meanEnergy (s.coefficients t) + meanEnergy u₀)) +
        ν * |ε| * (288 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ))) :=
      add_le_add (mul_le_mul_of_nonneg_left hC (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hMb (mul_nonneg hν (abs_nonneg _)))
    _ = _ := by ring

include hg hSum hu in
/-- A closed signed budget for solutions with zero stretching. No smallness
of the correction coefficient is required for this estimate. -/
theorem abs_integral_residual_le_of_stretching_zero (N : ℕ) (ε : ℝ) (hν : 0 ≤ ν)
    (hT : 0 < T) (hS : ∀ τ ∈ Icc (0 : ℝ) T, stretching (s.coefficients τ) = 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    |∫ τ in (0 : ℝ)..t, LocalOcticCorrectedEnergy.residual N ν ε (s.coefficients τ)| ≤
      45 * |ε| * meanEnergy u₀ := by
  have hSi : (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ)) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro τ hτ
        have hm : τ ∈ Ioo (0 : ℝ) t := by simpa only [uIoo_of_le ht.1] using hτ
        exact hS τ ⟨hm.1.le, hm.2.le.trans ht.2⟩
      _ = 0 := intervalIntegral.integral_zero
  have he := LocalVorticityEighthMoment.energy_identity s g hg hSum hu hT t ht
  rw [hSi, add_zero] at he
  have hrad : 0 ≤ ∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ) :=
    intervalIntegral.integral_nonneg ht.1 (fun _ _ ↦ LocalVorticityEighthMoment.radialDissipation_nonneg _)
  have hb : 9 * (meanEnergy (s.coefficients t) + meanEnergy u₀) +
      288 * ν * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤ 45 * meanEnergy u₀ := by
    nlinarith [LocalVorticityEighthMoment.meanEnergy_nonneg (s.coefficients t), mul_nonneg hν hrad]
  have h := abs_integral_residual_sub_stretching_le s g hg hSum hu N ε hν hT t ht
  rw [hSi, sub_zero] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hb (abs_nonneg ε)).trans_eq (by ring))

end Mettapedia.FluidDynamics.NavierStokes.LocalOcticSignedBudget
