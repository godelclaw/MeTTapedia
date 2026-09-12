import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityCoherenceBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy

/-!
# Initial-energy payment under an explicit direction-coherence bound

The actual local unforced solution pays the enstrophy coefficient in the
angular source estimate. A common projective Lipschitz bound is an explicit
extra hypothesis, not an output of the equation. Neither its propagation
nor an unconditional continuation theorem is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalCoherenceBudget

open MeasureTheory Set PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity InfiniteConvectionEnergy LocalKineticEnergy
open VorticityCoherenceBudget PancakeGalerkinKineticEnergy

def growthCoefficient (nu C K : ℝ) (u : FourierVelocity) : ℝ :=
  C * K ^ 2 / nu * kineticEnergy (fourierCurl u)

theorem growthCoefficient_nonneg (nu C K : ℝ) (hnu : 0 ≤ nu) (hC : 0 ≤ C)
    (u : FourierVelocity) : 0 ≤ growthCoefficient nu C K u := by
  unfold growthCoefficient
  positivity [kineticEnergy_nonneg (fourierCurl u)]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hg hSum hu

theorem continuousOn_growthCoefficient (C K : ℝ) :
    ContinuousOn (fun t ↦ growthCoefficient nu C K (s.coefficients t)) (Icc (0 : ℝ) T) :=
  (continuousOn_enstrophy s g hg hSum (fun τ hτ q ↦
    (fourierMoment_mono _ (by omega : 2 ≤ 3) _).trans (hu τ hτ q))).const_mul (C * K ^ 2 / nu)

theorem integral_growthCoefficient_le (hnu : 0 < nu) (C K : ℝ) (hC : 0 ≤ C)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ growthCoefficient nu C K (s.coefficients τ)) volume 0 t ∧
      (∫ τ in (0 : ℝ)..t, growthCoefficient nu C K (s.coefficients τ)) ≤
        C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2) := by
  have hu₂ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) _).trans (hu τ hτ q)
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  refine ⟨((continuousOn_growthCoefficient s g hg hSum hu C K).mono hsub).intervalIntegrable_of_Icc ht.1, ?_⟩
  have hb := enstrophy_integral_le_initial s g hg hSum hu₂ t ht
  have hb' : (∫ τ in (0 : ℝ)..t, kineticEnergy (fourierCurl (s.coefficients τ))) ≤
      kineticEnergy u₀ / (2 * nu) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
    nlinarith only [hb]
  simp only [growthCoefficient, intervalIntegral.integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ C * K ^ 2 / nu)).trans_eq (by ring)

/-- Both the actual source estimate and the initial-energy coefficient budget
are derived. Only the direction-coherence bound is supplied. -/
theorem exists_source_growth_budget (hnu : 0 < nu) (K : ℝ)
    (hK : ∀ τ ∈ Icc (0 : ℝ) T, ProjectiveLipschitz (s.coefficients τ) K) :
    ∃ C ≥ (0 : ℝ),
      (∀ τ ∈ Icc (0 : ℝ) T,
        |LocalVorticityEighthMoment.stretching (s.coefficients τ)| ≤
          nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients τ) +
            growthCoefficient nu C K (s.coefficients τ) * LocalVorticityEighthMoment.meanEnergy (s.coefficients τ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        IntervalIntegrable (fun τ ↦ growthCoefficient nu C K (s.coefficients τ)) volume 0 t ∧
          (∫ τ in (0 : ℝ)..t, growthCoefficient nu C K (s.coefficients τ)) ≤
            C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_stretching_bound nu hnu
  refine ⟨C, hC, ?_, fun t ht ↦ integral_growthCoefficient_le s g hg hSum hu hnu C K hC t ht⟩
  intro τ hτ
  exact hb K _ (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ))
    (s.reality τ) (s.transverse τ) (hK τ hτ)

/-- The weighted energy identity consumes the proved source estimate. The
coefficient is paid, but removing the coherence hypothesis remains open. -/
theorem exists_energy_growth_budget (hnu : 0 < nu) (hT : 0 < T) (K : ℝ)
    (hK : ∀ τ ∈ Icc (0 : ℝ) T, ProjectiveLipschitz (s.coefficients τ) K) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T,
      ((∫ τ in (0 : ℝ)..t, growthCoefficient nu C K (s.coefficients τ)) ≤
        C * K ^ 2 * kineticEnergy u₀ / (2 * nu ^ 2)) ∧
      LocalVorticityEighthMoment.meanEnergy (s.coefficients t) / 8 +
        nu / 2 * (∫ τ in (0 : ℝ)..t, LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients τ)) ≤
          LocalVorticityEighthMoment.meanEnergy u₀ / 8 +
            ∫ τ in (0 : ℝ)..t, growthCoefficient nu C K (s.coefficients τ) *
              LocalVorticityEighthMoment.meanEnergy (s.coefficients τ) := by
  obtain ⟨C, hC, hs, hb⟩ := exists_source_growth_budget s g hg hSum hu hnu K hK
  refine ⟨C, hC, ?_⟩
  intro t ht
  refine ⟨(hb t ht).2, ?_⟩
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hG := ((LocalVorticityEighthMoment.continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hS := ((LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hE := (((continuousOn_growthCoefficient s g hg hSum hu C K).mul
    (LocalVorticityEighthMoment.continuousOn_meanEnergy s g hSum hu)).mono hsub).intervalIntegrable_of_Icc
      (μ := volume) ht.1
  apply LocalVorticityEighthMoment.energy_add_half_dissipation_le_of_stretching_bound
    s g hg hSum hu hnu.le hT t ht
  have hi := intervalIntegral.integral_mono_on ht.1 hS ((hG.const_mul (nu / 2)).add hE)
    (fun τ hτ ↦ (le_abs_self _).trans (hs τ (hsub hτ)))
  rwa [intervalIntegral.integral_add (hG.const_mul (nu / 2)) hE,
    intervalIntegral.integral_const_mul] at hi

end Mettapedia.FluidDynamics.NavierStokes.LocalCoherenceBudget
