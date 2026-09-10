import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralCommutatorEnvelope

/-!
# Unsmoothed commutator-sensitive anisotropy

The simple-top branch separates a quadratic transverse cost from a
commutator-driven tilt cost. Exact top collisions retain the previous
coarse fallback. Measurability follows from continuous approximants, not
from a measurable choice of top eigenvector.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralCommutatorLimit

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open SpectralSourceCommutator SpectralDiffusionWeightLimit SpectralCommutatorEnvelope
open SpectralAnisotropyLimit

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def limitingEnvelope (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  if 0 < topGap S then
    min (SpectralAnisotropyLimit.limitingEnvelope S R w)
      (2 * ‖R‖ * limitingWeight S w +
        2 * (‖commutator S R‖ / topGap S) * ‖w‖ * Real.sqrt (limitingWeight S w))
  else 2 * ‖R‖ * ‖w‖ ^ 2

theorem limitingEnvelope_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ limitingEnvelope S R w := by
  have hw := limitingWeight_nonneg S w
  have hg := topGap_nonneg S
  unfold limitingEnvelope
  split
  · exact le_min (SpectralAnisotropyLimit.limitingEnvelope_nonneg S R w) (by positivity)
  · positivity

theorem limitingEnvelope_le_previous (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    limitingEnvelope S R w ≤ SpectralAnisotropyLimit.limitingEnvelope S R w := by
  unfold limitingEnvelope
  split_ifs with hg
  · exact min_le_left _ _
  · simp only [SpectralAnisotropyLimit.limitingEnvelope, if_neg hg, le_refl]

theorem limitingEnvelope_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    limitingEnvelope S R w ≤ 2 * ‖R‖ * ‖w‖ ^ 2 :=
  (limitingEnvelope_le_previous S R w).trans (SpectralAnisotropyLimit.limitingEnvelope_le_coarse S R w)

theorem tendsto_envelope {ι : Type*} {l : Filter ι} (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ι → ℝ)
    (heps : ∀ᶠ i in l, 0 < epsilon i) (hzero : Tendsto epsilon l (𝓝 0)) :
    Tendsto (fun i ↦ envelope S R w (epsilon i)) l (𝓝 (limitingEnvelope S R w)) := by
  by_cases hg : 0 < topGap S
  · have hW := tendsto_weight S w epsilon heps hzero
    have htilt : Tendsto (fun i ↦ tiltBound S R (epsilon i)) l
        (𝓝 (‖commutator S R‖ / topGap S)) := by
      have hn : Tendsto (fun i ↦ ‖commutator S R‖ + epsilon i * ‖R‖) l
          (𝓝 ‖commutator S R‖) := by
        simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hzero.mul_const ‖R‖)
      have hd : Tendsto (fun i ↦ topGap S + epsilon i) l (𝓝 (topGap S)) := by
        simpa only [add_zero] using hzero.const_add (topGap S)
      exact hn.div hd (ne_of_gt hg)
    have hr := (hW.const_mul (2 * ‖R‖)).add
      (((htilt.const_mul 2).mul_const ‖w‖).mul hW.sqrt)
    have hn : 0 ≤ 2 * ‖R‖ * limitingWeight S w +
        2 * (‖commutator S R‖ / topGap S) * ‖w‖ * Real.sqrt (limitingWeight S w) := by
      have hw := limitingWeight_nonneg S w
      positivity
    have h := (SpectralAnisotropyLimit.tendsto_envelope S R w epsilon heps hzero).min
      (hr.max (tendsto_const_nhds (x := (0 : ℝ))))
    simpa only [envelope, refinedBound, limitingEnvelope, if_pos hg, max_eq_left hn] using h
  · have hz : topGap S = 0 := le_antisymm (le_of_not_gt hg) (topGap_nonneg S)
    apply tendsto_const_nhds.congr'
    filter_upwards [heps] with i hi
    simp only [limitingEnvelope, if_neg hg, envelope_eq_coarse_of_topGap_zero S R w (epsilon i) hi hz]

theorem abs_remainderAnisotropy_le_limitingEnvelope (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) :
    |remainderAnisotropy R (topVector S) w| ≤ limitingEnvelope S R w :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_envelope S R w approximationParameter (Eventually.of_forall approximationParameter_pos)
      tendsto_approximationParameter)
    (fun n ↦ abs_remainderAnisotropy_le_envelope S R w _ (approximationParameter_pos n))

theorem limitingEnvelope_le_refined (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3)
    (hg : 0 < topGap S) :
    limitingEnvelope S R w ≤ 2 * ‖R‖ * limitingWeight S w +
      2 * (‖commutator S R‖ / topGap S) * ‖w‖ * Real.sqrt (limitingWeight S w) := by
  rw [limitingEnvelope, if_pos hg]
  exact min_le_right _ _

theorem limitingEnvelope_le_quadratic_of_commutator_eq_zero (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (hg : 0 < topGap S) (hcomm : commutator S R = 0) :
    limitingEnvelope S R w ≤ 2 * ‖R‖ * limitingWeight S w := by
  simpa only [hcomm, norm_zero, zero_div, mul_zero, zero_mul, add_zero] using
    limitingEnvelope_le_refined S R w hg

theorem limitingEnvelope_eq_coarse_of_topGap_zero (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (hg : topGap S = 0) :
    limitingEnvelope S R w = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  simp only [limitingEnvelope, hg, lt_self_iff_false, if_false]

theorem limitingEnvelope_aligned (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (alpha : ℝ) (hg : 0 < topGap S) : limitingEnvelope S R (alpha • topVector S) = 0 :=
  le_antisymm (by simpa only [SpectralAnisotropyLimit.limitingEnvelope_aligned S R alpha hg] using
    limitingEnvelope_le_previous S R (alpha • topVector S)) (limitingEnvelope_nonneg _ _ _)

theorem measurable_limitingEnvelope {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Measurable (fun x ↦ limitingEnvelope (S x) (R x) (w x)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x ↦ envelope (S x) (R x) (w x) (approximationParameter n))
    (fun n ↦ (continuous_envelope S R w _ (approximationParameter_pos n) hS hR hw).measurable)
  exact tendsto_pi_nhds.mpr (fun x ↦ tendsto_envelope (S x) (R x) (w x) approximationParameter
    (Eventually.of_forall approximationParameter_pos) tendsto_approximationParameter)

end Mettapedia.FluidDynamics.NavierStokes.SpectralCommutatorLimit
