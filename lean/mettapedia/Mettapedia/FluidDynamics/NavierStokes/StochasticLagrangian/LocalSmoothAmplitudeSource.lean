import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticitySmoothAmplitudeSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourceIntegral

/-!
# Actual L8 energy reduction for the smooth retained source

The smooth amplitude split uses the same positive threshold and consumes
the same half of the weighted dissipation as the original split. A signed
time-integrated retained-source budget suffices; it is not constructed by
these continuity and limiting arguments.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothAmplitudeSource

open MeasureTheory Filter PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget LocalVorticityEighthMoment
open LocalAnnularSourceContinuity LocalAnnularSourceIntegral VorticityRegularizedIncrement
open VorticitySmoothAmplitudeSource VorticityAnnularPolynomialSource
open Mettapedia.Analysis SmoothAmplitudePairing

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hSum hu

theorem continuousOn_retainedSource (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ContinuousOn (fun t ↦ retainedSource n L N (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hd : Continuous (fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦
      retainedStretch n L (PeriodicRieszPolynomial.kernel N (z.2.1 - z.2.2))
        (fullVorticity (s.coefficients z.1) z.2.1)
        (fullVorticity (s.coefficients z.1) z.2.2)) :=
    continuous_retainedStretch n L hL
      ((PeriodicRieszPolynomial.continuous_kernel N).comp
        (continuous_snd.fst.sub continuous_snd.snd))
      (hw.comp (f := fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦ (z.1, z.2.1)) (by fun_prop))
      (hw.comp (f := fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦ (z.1, z.2.2)) (by fun_prop))
  exact (continuousOn_pairIntegral _ hd).const_mul _

theorem intervalIntegrable_retainedSource (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ retainedSource n L N (s.coefficients τ)) volume 0 t :=
  ((continuousOn_retainedSource s g hSum hu n N L hL).mono
    (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1

theorem integral_stretching_le_of_retained_integral_le (hnu : 0 < nu)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (remainder : ℝ)
    (hbudget : ∀ N, (∫ τ in (0 : ℝ)..t,
      retainedSource 6 (dissipationThreshold nu) N (s.coefficients τ)) ≤ remainder) :
    (∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ)) ≤
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) + remainder := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hG := ((continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  apply le_of_tendsto (tendsto_integral_pairedSource s g hSum hu t ht)
  apply Eventually.of_forall
  intro N
  have hR := intervalIntegrable_retainedSource s g hSum hu 6 N
    (dissipationThreshold nu) (dissipationThreshold_pos nu hnu) t ht
  calc
    _ ≤ ∫ τ in (0 : ℝ)..t, nu / 2 * weightedPalinstrophy (s.coefficients τ) +
        retainedSource 6 (dissipationThreshold nu) N (s.coefficients τ) :=
      intervalIntegral.integral_mono_on ht.1 (intervalIntegrable_pairedSource s g hSum hu 6 N t ht)
        ((hG.const_mul (nu / 2)).add hR) (fun τ hτ ↦
          pairedSource_le_half_dissipation_add_retained nu hnu N _
            (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ))))
    _ = nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
        (∫ τ in (0 : ℝ)..t, retainedSource 6 (dissipationThreshold nu) N (s.coefficients τ)) := by
      rw [intervalIntegral.integral_add (hG.const_mul (nu / 2)) hR, intervalIntegral.integral_const_mul]
    _ ≤ _ := add_le_add le_rfl (hbudget N)

include hg in
theorem energy_add_half_dissipation_le_of_retained_integral_le (hnu : 0 < nu) (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (remainder : ℝ)
    (hbudget : ∀ N, (∫ τ in (0 : ℝ)..t,
      retainedSource 6 (dissipationThreshold nu) N (s.coefficients τ)) ≤ remainder) :
    meanEnergy (s.coefficients t) / 8 +
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤
        meanEnergy u₀ / 8 + remainder :=
  energy_add_half_dissipation_le_of_stretching_bound s g hg hSum hu hnu.le hT t ht remainder
    (integral_stretching_le_of_retained_integral_le s g hSum hu hnu t ht remainder hbudget)

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothAmplitudeSource
