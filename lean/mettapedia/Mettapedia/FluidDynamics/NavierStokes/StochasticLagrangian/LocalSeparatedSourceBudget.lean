import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticitySeparatedSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy

/-!
# Initial-energy payment of the separated-source growth coefficient

The coefficient is a genuine function of the actual local solution, with
a time integral bounded using viscosity, initial kinetic energy, time and
the fixed separation radius. This is a linear eighth-moment growth term,
not an absolute bound on the source integral or a bound on the near source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSeparatedSourceBudget

open MeasureTheory Set PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity InfiniteConvectionEnergy LocalKineticEnergy
open VorticitySeparatedSource VorticityRegularizedIncrement
open PancakeGalerkinKineticEnergy

def growthCoefficient (C : ℝ) (u : FourierVelocity) : ℝ :=
  C / 2 * (1 + kineticEnergy (fourierCurl u))

theorem growthCoefficient_nonneg (C : ℝ) (hC : 0 ≤ C) (u : FourierVelocity) :
    0 ≤ growthCoefficient C u := by
  unfold growthCoefficient
  positivity [kineticEnergy_nonneg (fourierCurl u)]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)

include hg hSum hu

theorem continuousOn_growthCoefficient (C : ℝ) :
    ContinuousOn (fun t ↦ growthCoefficient C (s.coefficients t)) (Icc (0 : ℝ) T) :=
  (continuousOn_const.add (continuousOn_enstrophy s g hg hSum hu)).const_mul (C / 2)

theorem integral_growthCoefficient_le (hnu : 0 < nu) (C : ℝ) (hC : 0 ≤ C)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ growthCoefficient C (s.coefficients τ)) volume 0 t ∧
      (∫ τ in (0 : ℝ)..t, growthCoefficient C (s.coefficients τ)) ≤
        C / 2 * t + C * kineticEnergy u₀ / (4 * nu) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun τ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hi := ((continuousOn_enstrophy s g hg hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  refine ⟨((continuousOn_growthCoefficient s g hg hSum hu C).mono hsub).intervalIntegrable_of_Icc
    ht.1, ?_⟩
  have hb := enstrophy_integral_le_initial s g hg hSum hu t ht
  have hb' : (∫ τ in (0 : ℝ)..t, kineticEnergy (fourierCurl (s.coefficients τ))) ≤
      kineticEnergy u₀ / (2 * nu) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
    nlinarith only [hb]
  simp only [growthCoefficient]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) hi,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_one]
  have hm := mul_le_mul_of_nonneg_left hb' (show 0 ≤ C / 2 by positivity)
  calc
    _ ≤ C / 2 * (t + kineticEnergy u₀ / (2 * nu)) := by nlinarith only [hm]
    _ = _ := by ring

theorem exists_uniform_farSource_growth_budget (hnu : 0 < nu) (r : ℝ) (hr : 0 < r) :
    ∃ C ≥ (0 : ℝ),
      (∀ τ ∈ Icc (0 : ℝ) T, ∀ L, 0 < L → ∀ N,
        |farSource r L N (s.coefficients τ)| ≤
          growthCoefficient C (s.coefficients τ) * LocalVorticityEighthMoment.meanEnergy (s.coefficients τ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        IntervalIntegrable (fun τ ↦ growthCoefficient C (s.coefficients τ)) volume 0 t ∧
          (∫ τ in (0 : ℝ)..t, growthCoefficient C (s.coefficients τ)) ≤
            C / 2 * t + C * kineticEnergy u₀ / (4 * nu) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_farSource_bound r hr
  refine ⟨C, hC, ?_, fun t ht ↦ integral_growthCoefficient_le s g hg hSum hu hnu C hC t ht⟩
  intro τ hτ L hL N
  exact hb L hL N _ (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ)))

end Mettapedia.FluidDynamics.NavierStokes.LocalSeparatedSourceBudget
