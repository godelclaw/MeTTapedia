import Mettapedia.Analysis.SmoothAmplitudePairing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityAnnularPolynomialSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets

/-!
# Smooth amplitude retention with the same actual dissipation payment

The rational pair weight replaces the sharp-threshold weight in an
additional signed source. Its low complement is paid by the same
cutoff-independent threshold and the actual eighth-moment dissipation.
The original split is unchanged. No retained-source budget is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticitySmoothAmplitudeSource

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget VorticityAnnularPolynomialSource VorticityRegularizedIncrement
open Mettapedia.Analysis SmoothAmplitudePairing SignedCrossKernel RadialPower
open scoped ContDiff

local notation "T3" => UnitAddTorus (Fin 3)
local notation "H" => PeriodicRieszPolynomial.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def retainedSource (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    retainedStretch n L (H N (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem contDiff_retainedDensity_commonShift (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (h x : T3) (j : Fin 3) :
    ContDiff ℝ 2 (fun t : ℝ ↦ retainedStretch (2 * n) L (H N h)
      (fullVorticity u (x + PancakeFourierTranslationCurve.coordinateShift j t))
      (fullVorticity u ((x - h) + PancakeFourierTranslationCurve.coordinateShift j t))) := by
  exact contDiff_retainedStretch_comp_even 2 n L hL
    (K := fun _ : ℝ ↦ H N h)
    (a := fun t ↦ fullVorticity u (x + PancakeFourierTranslationCurve.coordinateShift j t))
    (b := fun t ↦ fullVorticity u ((x - h) + PancakeFourierTranslationCurve.coordinateShift j t))
    contDiff_const (LocalSpatialVorticityJets.contDiff_fullVorticity_shift u hu j x)
    (LocalSpatialVorticityJets.contDiff_fullVorticity_shift u hu j (x - h))

theorem continuous_retainedDensity (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (fun p : T3 × T3 ↦ retainedStretch n L (H N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) :=
  continuous_retainedStretch n L hL
    ((PeriodicRieszPolynomial.continuous_kernel N).comp (continuous_fst.sub continuous_snd))
    ((continuous_fullVorticity u hu).comp continuous_fst)
    ((continuous_fullVorticity u hu).comp continuous_snd)

theorem abs_pairedSource_sub_retainedSource_le (L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    |pairedSource 6 N u - retainedSource 6 L N u| ≤ 2 * L * incrementIntegral N u := by
  have hw := continuous_fullVorticity u hu
  have hH := (PeriodicRieszPolynomial.continuous_kernel N).comp
    (continuous_fst.sub continuous_snd : Continuous (fun p : T3 × T3 ↦ p.1 - p.2))
  have hp := (continuous_pairedStretch (fun x y : T3 ↦ H N (x - y))
    (fullVorticity u) hH hw 6).integrable_of_hasCompactSupport
      (μ := (volume : Measure T3).prod volume) (HasCompactSupport.of_compactSpace _)
  have hr := (continuous_retainedDensity 6 N L hL u hu).integrable_of_hasCompactSupport
    (μ := (volume : Measure T3).prod volume) (HasCompactSupport.of_compactSpace _)
  have hb := (continuous_bareRadialCost (fun x y : T3 ↦ H N (x - y))
    (fullVorticity u) hH hw 3).integrable_of_hasCompactSupport
      (μ := (volume : Measure T3).prod volume) (HasCompactSupport.of_compactSpace _)
  have he : (∫ x : T3, ∫ y : T3, ‖H N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) =
      incrementIntegral N u := by
    rw [PeriodicRieszPolynomial.integral_pair_eq (d := 3) N
      (fun x y K ↦ ‖K‖ * ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2)]
    exact VorticityRegularizedPayment.bareRadialIntegral_eq_incrementIntegral N u hu
  have hi := abs_integral_paired_sub_retained_le volume
    (fun x y : T3 ↦ H N (x - y)) (fullVorticity u) 3 L hL hp hr hb
  rw [he] at hi
  rw [pairedSource, retainedSource, ← mul_sub, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith only [hi]

theorem pairedSource_le_half_dissipation_add_retained (nu : ℝ) (hnu : 0 < nu) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    pairedSource 6 N u ≤ nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
      retainedSource 6 (dissipationThreshold nu) N u := by
  have h := (le_abs_self _).trans (abs_pairedSource_sub_retainedSource_le _
    (dissipationThreshold_pos nu hnu) N u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
  have hp := dissipationThreshold_pays nu hnu.le N u hu
  linarith only [h, hp]

end Mettapedia.FluidDynamics.NavierStokes.VorticitySmoothAmplitudeSource
