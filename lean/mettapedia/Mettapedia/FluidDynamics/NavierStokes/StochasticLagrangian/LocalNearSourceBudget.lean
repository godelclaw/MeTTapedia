import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityNearIncrement
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSeparatedSourceBudget

/-!
# Adjustable amplitude thresholds in the actual stretching bound

Every fixed positive threshold admits a field-independent near radius.
Changing the near threshold consumes half of the remaining viscous allowance;
the separated growth coefficient still has an initial-energy time budget.
No estimate on the signed near retained source is supplied or assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalNearSourceBudget

open MeasureTheory Set PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget VorticityNearIncrement
open VorticitySeparatedSource VorticityRegularizedIncrement LocalSeparatedSourceBudget
open PancakeGalerkinKineticEnergy InfiniteConvectionEnergy

theorem abs_nearSource_sub_le (r L M : ℝ) (hL : 0 < L) (hM : 0 < M) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    |nearSource r L N u - nearSource r M N u| ≤
      2 * (L + M) * nearIncrement r N u := by
  have h₁ := abs_nearPairedSource_sub_retained_le r L hL N u hu
  have h₂ := abs_nearPairedSource_sub_retained_le r M hM N u hu
  have h := abs_sub_le (nearSource r L N u) (nearPairedSource r N u) (nearSource r M N u)
  rw [abs_sub_comm (nearSource r L N u) (nearPairedSource r N u)] at h
  nlinarith only [h₁, h₂, h]

def thresholdRadius (nu L : ℝ) : ℝ :=
  absorptionRadius (nu / 2) (dissipationThreshold (nu / 2) + L)

theorem thresholdRadius_pos (nu L : ℝ) (hnu : 0 < nu) (hL : 0 < L) :
    0 < thresholdRadius nu L :=
  absorptionRadius_pos _ _ (by positivity)
    (add_pos (dissipationThreshold_pos _ (by positivity)) hL)

theorem exists_uniform_source_bound_at_threshold (nu L : ℝ) (hnu : 0 < nu) (hL : 0 < L) :
    ∃ C ≥ (0 : ℝ), ∀ N u, Summable (fourierMoment 3 u) →
      VorticityAnnularPolynomialSource.pairedSource 6 N u ≤
        nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
          nearSource (thresholdRadius nu L) L N u +
          growthCoefficient C u * LocalVorticityEighthMoment.meanEnergy u := by
  have hnu₂ : 0 < nu / 2 := by positivity
  have hL₀ := dissipationThreshold_pos (nu / 2) hnu₂
  have hr := thresholdRadius_pos nu L hnu hL
  obtain ⟨C, hC, hb⟩ := exists_uniform_source_bound (thresholdRadius nu L) hr (nu / 2) hnu₂
  refine ⟨C, hC, ?_⟩
  intro N u hu
  have hs := hb N u hu
  have hd := (le_abs_self _).trans (abs_nearSource_sub_le (thresholdRadius nu L)
    (dissipationThreshold (nu / 2)) L hL₀ hL N u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
  have hp := nearIncrement_pays (nu / 2) (dissipationThreshold (nu / 2) + L)
    (thresholdRadius nu L) (add_pos hL₀ hL) hr.le le_rfl N u hu
  simp only [growthCoefficient] at *
  linarith only [hs, hd, hp]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hg hSum hu

/-- The coefficient is paid by the actual local solution's unforced energy
identity. The radius and threshold are fixed in time, not chosen from an
unknown vorticity supremum. -/
theorem exists_uniform_source_growth_budget (hnu : 0 < nu) (L : ℝ) (hL : 0 < L) :
    ∃ C ≥ (0 : ℝ),
      (∀ τ ∈ Icc (0 : ℝ) T, ∀ N,
        VorticityAnnularPolynomialSource.pairedSource 6 N (s.coefficients τ) ≤
          nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients τ) +
            nearSource (thresholdRadius nu L) L N (s.coefficients τ) +
            growthCoefficient C (s.coefficients τ) * LocalVorticityEighthMoment.meanEnergy (s.coefficients τ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        IntervalIntegrable (fun τ ↦ growthCoefficient C (s.coefficients τ)) volume 0 t ∧
          (∫ τ in (0 : ℝ)..t, growthCoefficient C (s.coefficients τ)) ≤
            C / 2 * t + C * kineticEnergy u₀ / (4 * nu) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_source_bound_at_threshold nu L hnu hL
  have hu₂ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) _).trans (hu τ hτ q)
  refine ⟨C, hC, ?_, ?_⟩
  · intro τ hτ N
    exact hb N _ (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ))
  · intro t ht
    exact integral_growthCoefficient_le s g hg hSum hu₂ hnu C hC t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalNearSourceBudget
