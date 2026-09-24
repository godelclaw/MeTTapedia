import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedPairing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedIncrement

/-!
# Cutoff-uniform dissipation payment for the actual signed source

One positive threshold, depending on viscosity and the constructed kernel
moment constant only, pays the bounded-amplitude part of every regularized
source. The source converges to actual eighth-moment stretching. The signed
high-amplitude remainder is retained, with no dynamical estimate assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment

open MeasureTheory Filter PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeBlockReality LocalLowDiffusionBudget
open VorticityRegularizedPairing VorticityRegularizedSource VorticityRegularizedIncrement
open Mettapedia.Analysis SignedCrossKernel RadialPower
open scoped Topology
local notation "T3" => UnitAddTorus (Fin 3)
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem integrable_pairedStretch (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ pairedStretch n (H N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  have hi := integrable_weightedStretch n N u hu
  have hj := hi.swap
  apply (hi.add hj).congr
  filter_upwards [] with p
  change weightedStretch n (H N (p.1 - p.2)) (fullVorticity u p.1) (fullVorticity u p.2) +
    weightedStretch n (H N (p.2 - p.1)) (fullVorticity u p.2) (fullVorticity u p.1) = _
  rw [PeriodicRieszOperator.kernel_sub_swap, weightedStretch_add_swap]

theorem integrable_highAmplitudeStretch (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ highAmplitudeStretch n L (H N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  have hw := continuous_fullVorticity u hu
  have ha : Continuous (fun p : T3 × T3 ↦ ‖fullVorticity u p.1‖) :=
    (hw.comp continuous_fst).norm
  have hb : Continuous (fun p : T3 × T3 ↦ ‖fullVorticity u p.2‖) :=
    (hw.comp continuous_snd).norm
  have hl : Continuous (fun p : T3 × T3 ↦ lowAmplitudeWeight L
      (fullVorticity u p.1) (fullVorticity u p.2)) := by
    unfold lowAmplitudeWeight
    exact continuous_const.div (continuous_const.max (ha.min hb))
      (fun _ ↦ (hL.trans_le (le_max_left _ _)).ne')
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦ 1 - lowAmplitudeWeight L
      (fullVorticity u p.1) (fullVorticity u p.2),
    continuous_const.sub hl⟩
  have hi := IntegrableKernelPairing.integrable_mul ((volume : Measure T3).prod volume) _
    (integrable_pairedStretch n N u hu) f
  apply hi.congr
  filter_upwards [] with p
  exact mul_comm _ _

theorem integrable_bareRadialCost (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ ‖H N (p.1 - p.2)‖ *
      ‖radialPower n (fullVorticity u p.1) - radialPower n (fullVorticity u p.2)‖ ^ 2)
        ((volume : Measure T3).prod volume) := by
  have hg := (continuous_radialPower n).comp (continuous_fullVorticity u hu)
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦
      ‖radialPower n (fullVorticity u p.1) - radialPower n (fullVorticity u p.2)‖ ^ 2,
    ((hg.comp continuous_fst).sub (hg.comp continuous_snd)).norm.pow 2⟩
  have hi := (measurePreserving_sub_prod (volume : Measure T3) volume).integrable_comp_of_integrable
    ((PeriodicRieszOperator.integrable_kernel (d := 3) N).norm.comp_fst (volume : Measure T3))
  exact IntegrableKernelPairing.integrable_mul _ _ hi f

theorem bareRadialIntegral_eq_incrementIntegral (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ∫ y : T3, ‖H N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) =
        incrementIntegral N u := by
  have hg := (continuous_radialPower 3).comp (continuous_fullVorticity u hu)
  let f : C(T3 × T3, ℝ) := ⟨fun p ↦ ‖radialPower 3 (fullVorticity u p.2) -
      radialPower 3 (fullVorticity u (p.2 - p.1))‖ ^ 2,
    ((hg.comp continuous_snd).sub (hg.comp (continuous_snd.sub continuous_fst))).norm.pow 2⟩
  have hi := IntegrableKernelPairing.integrable_mul _ _
    ((PeriodicRieszOperator.integrable_kernel (d := 3) N).norm.comp_fst (volume : Measure T3)) f
  have he : (∫ x : T3, ∫ y : T3, ‖H N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) =
      ∫ x : T3, ∫ h : T3, ‖H N h‖ * ‖radialPower 3 (fullVorticity u x) -
        radialPower 3 (fullVorticity u (x - h))‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    have ht := integral_sub_left_eq_self (fun y : T3 ↦ ‖H N (x - y)‖ *
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u y)‖ ^ 2) volume x
    simpa only [sub_sub_cancel] using ht.symm
  rw [he, ← integral_integral_swap hi]
  simp only [integral_const_mul, incrementIntegral]

def highAmplitudeSource (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    highAmplitudeStretch n L (H N (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem abs_source_sub_highAmplitudeSource_le (L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    |source 6 N u - highAmplitudeSource 6 L N u| ≤ 2 * L * incrementIntegral N u := by
  rw [source_eq_pairedSource 6 N u hu, pairedSource, highAmplitudeSource,
    ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := abs_integral_paired_sub_high_le_of_integrable volume
    (fun x y : T3 ↦ H N (x - y)) (fullVorticity u) 3 L hL
    (integrable_pairedStretch 6 N u hu) (integrable_highAmplitudeStretch 6 N L hL u hu)
    (integrable_bareRadialCost 3 N u hu)
  rw [bareRadialIntegral_eq_incrementIntegral N u hu] at h
  nlinarith only [h]

/-- The same viscosity-dependent threshold works at every cutoff and for every admissible field. -/
theorem source_le_half_dissipation_add_remainder (nu : ℝ) (hnu : 0 < nu) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    source 6 N u ≤ (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy u +
      highAmplitudeSource 6 (dissipationThreshold nu) N u := by
  have hu1 := summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu
  have hb := (le_abs_self _).trans (abs_source_sub_highAmplitudeSource_le _
    (dissipationThreshold_pos nu hnu) N u hu1)
  have hp := dissipationThreshold_pays nu hnu.le N u hu
  linarith only [hb, hp]

theorem highAmplitudeStretch_eq_zero_of_endpoint_le (L : ℝ) (hL : 0 < L)
    (N : ℕ) (u : FourierVelocity) (x y : T3)
    (h : ‖fullVorticity u x‖ ≤ L ∨ ‖fullVorticity u y‖ ≤ L) :
    highAmplitudeStretch 6 L (H N (x - y)) (fullVorticity u x) (fullVorticity u y) = 0 := by
  apply highAmplitudeStretch_eq_zero_of_min_le _ L hL
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans h

/-- A uniform upper bound on the signed remainder passes to the actual source.
This does not construct that bound and does not require convergence of the remainder. -/
theorem stretching_le_half_dissipation_add_of_remainder_le (nu b : ℝ) (hnu : 0 < nu)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0)
    (hb : ∀ N, highAmplitudeSource 6 (dissipationThreshold nu) N u ≤ b) :
    LocalVorticityEighthMoment.stretching u ≤
      (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy u + b := by
  apply le_of_tendsto (tendsto_eighthMoment_source u
    (summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu) hr hd)
  exact Eventually.of_forall (fun N ↦
    (source_le_half_dissipation_add_remainder nu hnu N u hu).trans (add_le_add_right (hb N) _))

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment
