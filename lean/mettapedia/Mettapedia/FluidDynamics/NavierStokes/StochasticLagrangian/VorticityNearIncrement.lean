import Mettapedia.Analysis.PeriodicRieszNearMoment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticitySeparatedSource

/-!
# Radius-dependent payment of near vorticity increments

The near increment cost has a coefficient proportional to the separation
radius, uniformly in the Fourier cutoff. Every fixed positive amplitude
threshold can therefore be absorbed by choosing a sufficiently small fixed
radius. No bound on the retained high-amplitude source is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityNearIncrement

open MeasureTheory Set PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget VorticityRegularizedIncrement
open Mettapedia.Analysis RadialPower SmoothAmplitudePairing SignedCrossKernel

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local notation "C" => PeriodicRieszNearMoment.firstMomentBound 3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

def nearKernel (r : ℝ) (N : ℕ) (h : T3) : R3 →L[ℝ] R3 :=
  if ‖h‖ < r then H N h else 0

def nearIncrement (r : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h in Metric.ball (0 : T3) r, ‖H N h‖ * ∫ x : T3,
    ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u (x - h))‖ ^ 2

theorem nearIncrement_nonneg (r : ℝ) (N : ℕ) (u : FourierVelocity) :
    0 ≤ nearIncrement r N u := integral_nonneg (fun _ ↦ by
      exact mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ ↦ sq_nonneg _)))

theorem nearIncrement_le (r : ℝ) (hr : 0 ≤ r) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    nearIncrement r N u ≤ 48 * r * C * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hi := (PeriodicRieszOperator.integrable_secondMoment (d := 3) N).const_mul
    (48 * LocalVorticityEighthMoment.weightedPalinstrophy u)
  have hb := integral_mono (μ := volume.restrict (Metric.ball (0 : T3) r))
    (integrable_increment N u hu).integrableOn hi.integrableOn (fun h ↦ by
    have hm := mul_le_mul_of_nonneg_left (increment_at_displacement_le u hu h) (norm_nonneg (H N h))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm)
  rw [integral_const_mul] at hb
  have hm := mul_le_mul_of_nonneg_left (PeriodicRieszNearMoment.nearSecondMoment_le (d := 3) r hr N)
    (show 0 ≤ 48 * LocalVorticityEighthMoment.weightedPalinstrophy u by
      positivity [LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u])
  exact hb.trans (hm.trans_eq (by ring))

/-- The radius is independent of the field and frequency cutoff. -/
def absorptionRadius (nu L : ℝ) : ℝ := nu / (192 * L * (C + 1))

theorem absorptionRadius_pos (nu L : ℝ) (hnu : 0 < nu) (hL : 0 < L) :
    0 < absorptionRadius nu L := by
  unfold absorptionRadius
  positivity [PeriodicRieszNearMoment.firstMomentBound_nonneg 3]

theorem nearIncrement_pays (nu L r : ℝ) (hL : 0 < L)
    (hr : 0 ≤ r) (hradius : r ≤ absorptionRadius nu L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    2 * L * nearIncrement r N u ≤
      nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hC := PeriodicRieszNearMoment.firstMomentBound_nonneg 3
  have hp : 96 * L * r * C ≤ nu / 2 := by
    have hden : 0 < 192 * L * (C + 1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hradius
    nlinarith [mul_nonneg hr hL.le]
  have hi := mul_le_mul_of_nonneg_left (nearIncrement_le r hr N u hu)
    (show 0 ≤ 2 * L by positivity)
  have hg := mul_le_mul_of_nonneg_right hp (LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u)
  nlinarith only [hi, hg]

theorem integrable_nearKernel (r : ℝ) (N : ℕ) : Integrable (nearKernel r N) := by
  have hi := Integrable.indicator (f := H N) (μ := (volume : Measure T3))
    (PeriodicRieszOperator.integrable_kernel (d := 3) N)
    (s := Metric.ball (0 : T3) r) measurableSet_ball
  apply hi.congr
  filter_upwards [] with h
  by_cases hh : h ∈ Metric.ball (0 : T3) r
  · rw [Set.indicator_of_mem hh]
    simp only [Metric.mem_ball, dist_zero_right] at hh
    simp only [nearKernel, if_pos hh]
  · rw [Set.indicator_of_notMem hh]
    simp only [Metric.mem_ball, dist_zero_right] at hh
    simp only [nearKernel, if_neg hh]

theorem pairedStretch_nearKernel (n : ℕ) (r : ℝ) (N : ℕ) (h : T3) (a b : R3) :
    pairedStretch n (nearKernel r N h) a b =
      if ‖h‖ < r then pairedStretch n (H N h) a b else 0 := by
  unfold nearKernel
  split_ifs <;> simp [pairedStretch]

theorem retainedStretch_nearKernel (n : ℕ) (r L : ℝ) (N : ℕ) (h : T3) (a b : R3) :
    retainedStretch n L (nearKernel r N h) a b =
      if ‖h‖ < r then retainedStretch n L (H N h) a b else 0 := by
  unfold nearKernel
  split_ifs <;> simp [retainedStretch, pairedStretch]

theorem integrable_nearPairedDensity (r : ℝ) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ pairedStretch 6 (nearKernel r N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  simp_rw [pairedStretch_nearKernel]
  exact (VorticityRegularizedPayment.integrable_pairedStretch 6 N u hu).indicator
    (measurableSet_lt (continuous_fst.sub continuous_snd).norm.measurable measurable_const)

theorem integrable_nearRetainedDensity (r L : ℝ) (hL : 0 < L) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ retainedStretch 6 L (nearKernel r N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  simp_rw [retainedStretch_nearKernel]
  exact (VorticitySeparatedSource.integrable_retained 6 N L hL u hu).indicator
    (measurableSet_lt (continuous_fst.sub continuous_snd).norm.measurable measurable_const)

theorem integrable_nearRadialCost (r : ℝ) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ ‖nearKernel r N (p.1 - p.2)‖ *
      ‖radialPower 3 (fullVorticity u p.1) - radialPower 3 (fullVorticity u p.2)‖ ^ 2)
      ((volume : Measure T3).prod volume) := by
  have hg := (continuous_radialPower 3).comp (continuous_fullVorticity u hu)
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦
      ‖radialPower 3 (fullVorticity u p.1) - radialPower 3 (fullVorticity u p.2)‖ ^ 2,
    ((hg.comp continuous_fst).sub (hg.comp continuous_snd)).norm.pow 2⟩
  have hi := (measurePreserving_sub_prod (volume : Measure T3) volume).integrable_comp_of_integrable
    ((integrable_nearKernel r N).norm.comp_fst (volume : Measure T3))
  exact IntegrableKernelPairing.integrable_mul _ _ hi f

theorem nearRadialIntegral_eq (r : ℝ) (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ∫ y : T3, ‖nearKernel r N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) =
      nearIncrement r N u := by
  have hg := (continuous_radialPower 3).comp (continuous_fullVorticity u hu)
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦ ‖radialPower 3 (fullVorticity u p.2) -
      radialPower 3 (fullVorticity u (p.2 - p.1))‖ ^ 2,
    ((hg.comp continuous_snd).sub (hg.comp (continuous_snd.sub continuous_fst))).norm.pow 2⟩
  have hi := IntegrableKernelPairing.integrable_mul _ _
    ((integrable_nearKernel r N).norm.comp_fst (volume : Measure T3)) f
  have he : (∫ x : T3, ∫ y : T3, ‖nearKernel r N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) =
      ∫ x : T3, ∫ h : T3, ‖nearKernel r N h‖ * ‖radialPower 3 (fullVorticity u x) -
        radialPower 3 (fullVorticity u (x - h))‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    have ht := integral_sub_left_eq_self (fun y : T3 ↦ ‖nearKernel r N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) volume x
    simpa only [sub_sub_cancel] using ht.symm
  rw [he, ← integral_integral_swap hi]
  simp only [integral_const_mul, nearIncrement]
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with h
  by_cases hh : h ∈ Metric.ball (0 : T3) r
  · rw [Set.indicator_of_mem hh]
    simp only [Metric.mem_ball, dist_zero_right] at hh
    simp only [nearKernel, if_pos hh]
  · rw [Set.indicator_of_notMem hh]
    simp only [Metric.mem_ball, dist_zero_right] at hh
    simp only [nearKernel, if_neg hh, norm_zero, zero_mul]

def nearPairedSource (r : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    pairedStretch 6 (nearKernel r N (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem abs_nearPairedSource_sub_retained_le (r L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    |nearPairedSource r N u - VorticitySeparatedSource.nearSource r L N u| ≤
      2 * L * nearIncrement r N u := by
  have h := abs_integral_paired_sub_retained_le volume
    (fun x y : T3 ↦ nearKernel r N (x - y)) (fullVorticity u) 3 L hL
    (integrable_nearPairedDensity r N u hu) (integrable_nearRetainedDensity r L hL N u hu)
    (integrable_nearRadialCost r N u hu)
  rw [nearRadialIntegral_eq r N u hu] at h
  simp only [retainedStretch_nearKernel] at h
  simp only [nearPairedSource, VorticitySeparatedSource.nearSource, ← mul_sub, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith only [h]

theorem nearPairedSource_le_half_dissipation_add_retained (nu L r : ℝ)
    (hL : 0 < L) (hr : 0 ≤ r) (hradius : r ≤ absorptionRadius nu L)
    (N : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    nearPairedSource r N u ≤ nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u +
      VorticitySeparatedSource.nearSource r L N u := by
  have h := (le_abs_self _).trans (abs_nearPairedSource_sub_retained_le r L hL N u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
  have hp := nearIncrement_pays nu L r hL hr hradius N u hu
  linarith only [h, hp]

end Mettapedia.FluidDynamics.NavierStokes.VorticityNearIncrement
