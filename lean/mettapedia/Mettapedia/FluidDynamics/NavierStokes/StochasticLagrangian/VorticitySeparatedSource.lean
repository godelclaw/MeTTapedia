import Mettapedia.Analysis.PeriodicRieszSeparated
import Mettapedia.Analysis.SmoothAmplitudePairingBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticitySmoothAmplitudeSource

/-!
# Separated interactions in the actual retained vorticity source

The far piece is linear in the actual eighth moment with an
enstrophy-controlled coefficient, uniformly in the kernel cutoff.
The near piece retains its sign and remains an unpaid dynamical term.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticitySeparatedSource

open MeasureTheory Set PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget Mettapedia.Analysis SmoothAmplitudePairing SmoothAmplitudeCutoff
open SignedCrossKernel PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def farKernel (r : ℝ) (N : ℕ) (h : T3) : R3 →L[ℝ] R3 :=
  if r ≤ ‖h‖ then H N h else 0

def farSource (r L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    retainedStretch 6 L (farKernel r N (x - y)) (fullVorticity u x) (fullVorticity u y)

def nearSource (r L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    if ‖x - y‖ < r then retainedStretch 6 L (H N (x - y))
      (fullVorticity u x) (fullVorticity u y) else 0

theorem integrable_retained (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ retainedStretch n L (H N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  have hw := continuous_fullVorticity u hu
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦ pairWeight L (fullVorticity u p.1) (fullVorticity u p.2),
    (contDiff_pairWeight L hL).continuous.comp
      ((hw.comp continuous_fst).prodMk (hw.comp continuous_snd))⟩
  have hi := IntegrableKernelPairing.integrable_mul ((volume : Measure T3).prod volume) _
    (VorticityRegularizedPayment.integrable_pairedStretch n N u hu) f
  apply hi.congr
  filter_upwards [] with p
  exact mul_comm _ _

theorem farDensity_eq (r L : ℝ) (N : ℕ) (u : FourierVelocity) (x y : T3) :
    retainedStretch 6 L (farKernel r N (x - y)) (fullVorticity u x) (fullVorticity u y) =
      if r ≤ ‖x - y‖ then retainedStretch 6 L (H N (x - y))
        (fullVorticity u x) (fullVorticity u y) else 0 := by
  unfold farKernel
  split_ifs <;> simp [retainedStretch, pairedStretch]

theorem integrable_farDensity (r L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ retainedStretch 6 L (farKernel r N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  simp_rw [farDensity_eq]
  exact (integrable_retained 6 N L hL u hu).indicator
    (measurableSet_le measurable_const (continuous_fst.sub continuous_snd).norm.measurable)

theorem retainedSource_eq_near_add_far (r L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    VorticitySmoothAmplitudeSource.retainedSource 6 L N u =
      nearSource r L N u + farSource r L N u := by
  have hi := integrable_retained 6 N L hL u hu
  have hf := integrable_farDensity r L hL N u hu
  have hn := hi.indicator
    (measurableSet_lt (continuous_fst.sub continuous_snd).norm.measurable (measurable_const (a := r)))
  change Integrable (fun p : T3 × T3 ↦ if ‖p.1 - p.2‖ < r then
    retainedStretch 6 L (H N (p.1 - p.2)) (fullVorticity u p.1) (fullVorticity u p.2) else 0)
      ((volume : Measure T3).prod volume) at hn
  unfold VorticitySmoothAmplitudeSource.retainedSource
  rw [PeriodicRieszPolynomial.integral_pair_eq (d := 3) N
    (fun x y K ↦ retainedStretch 6 L K (fullVorticity u x) (fullVorticity u y))]
  unfold nearSource farSource
  rw [← integral_prod _ hi, ← integral_prod _ hn, ← integral_prod _ hf, ← mul_add,
    ← integral_add hn hf]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [farDensity_eq]
  by_cases h : ‖p.1 - p.2‖ < r
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

theorem firstMoment_le_half_one_add_enstrophy (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ‖fullVorticity u x‖) ≤
      (1 + InfiniteConvectionEnergy.kineticEnergy (fourierCurl u)) / 2 := by
  have hw := (continuous_fullVorticity u hu).norm
  have hi := hw.integrable_of_hasCompactSupport (μ := (volume : Measure T3))
    (HasCompactSupport.of_compactSpace _)
  have hs := (hw.pow 2).integrable_of_hasCompactSupport (μ := (volume : Measure T3))
    (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono (hi.const_mul 2) (integrable_const 1 |>.add hs)
    (fun x ↦ by dsimp only [Pi.add_apply]; nlinarith [sq_nonneg (‖fullVorticity u x‖ - 1)])
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (integrable_const 1) hs, integral_const] at hb
  norm_num at hb
  have hp := integral_norm_fullVorticity_sq_le u hu
  linarith

theorem exists_uniform_farSource_bound (r : ℝ) (hr : 0 < r) :
    ∃ C ≥ (0 : ℝ), ∀ L, 0 < L → ∀ N u, Summable (fourierMoment 1 u) →
      |farSource r L N u| ≤ (C / 2 *
        (1 + InfiniteConvectionEnergy.kineticEnergy (fourierCurl u))) *
          LocalVorticityEighthMoment.meanEnergy u := by
  obtain ⟨C, hC, hb⟩ := PeriodicRieszSeparated.exists_uniform_operator_bound (d := 3) r hr
  refine ⟨C, hC, ?_⟩
  intro L hL N u hu
  have hw := (continuous_fullVorticity u hu).norm
  have hi := hw.integrable_of_hasCompactSupport (μ := (volume : Measure T3))
    (HasCompactSupport.of_compactSpace _)
  have hp := (hw.pow 8).integrable_of_hasCompactSupport (μ := (volume : Measure T3))
    (HasCompactSupport.of_compactSpace _)
  have hfar (x y : T3) : ‖farKernel r N (x - y)‖ ≤ C := by
    unfold farKernel
    split_ifs with h
    · exact hb N (x - y) h
    · simpa only [norm_zero] using hC
  have hf := abs_half_integral_retained_le_of_bound volume
    (fun x y : T3 ↦ farKernel r N (x - y)) (fullVorticity u) 6 L hL C hi hp
    (integrable_farDensity r L hL N u hu) hfar
  have hfirst := firstMoment_le_half_one_add_enstrophy u hu
  have hE : 0 ≤ ∫ x : T3, ‖fullVorticity u x‖ ^ 8 := integral_nonneg (fun x ↦ by positivity)
  have hm := mul_le_mul_of_nonneg_left hfirst (mul_nonneg hC hE)
  simp only [LocalVorticityEighthMoment.meanEnergy, LocalVorticityEighthMoment.energy_eq_norm_pow]
  change |farSource r L N u| ≤ _ at hf
  nlinarith only [hf, hm]

/-- Bounded amplitudes are absorbed into actual viscosity; separated
interactions are linear in the eighth moment. Only the near retained
source is left without an upper estimate. -/
theorem exists_uniform_source_bound (r : ℝ) (hr : 0 < r) (nu : ℝ) (hnu : 0 < nu) :
    ∃ C ≥ (0 : ℝ), ∀ N u, Summable (fourierMoment 3 u) →
      VorticityAnnularPolynomialSource.pairedSource 6 N u ≤
        nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
          nearSource r (VorticityRegularizedIncrement.dissipationThreshold nu) N u +
          (C / 2 * (1 + InfiniteConvectionEnergy.kineticEnergy (fourierCurl u))) *
            LocalVorticityEighthMoment.meanEnergy u := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_farSource_bound r hr
  refine ⟨C, hC, ?_⟩
  intro N u hu
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hL := VorticityRegularizedIncrement.dissipationThreshold_pos nu hnu
  have hp := VorticitySmoothAmplitudeSource.pairedSource_le_half_dissipation_add_retained nu hnu N u hu
  rw [retainedSource_eq_near_add_far r _ hL N u hu1] at hp
  have hf := (le_abs_self _).trans (hb _ hL N u hu1)
  linarith only [hp, hf]

end Mettapedia.FluidDynamics.NavierStokes.VorticitySeparatedSource
