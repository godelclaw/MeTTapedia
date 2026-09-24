import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing the auxiliary smoothing from the anisotropy envelope

The positive-parameter envelope has a pointwise limit. On the simple-top
branch this uses unregularized alignment energy; at a top collision it
keeps the coarse bound. The limit is measurable, not asserted continuous
through collisions, and vanishes on a separated aligned eigenline.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralAnisotropyLimit

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeRegularizedMaterialRate
open PancakeAnisotropyDepletion SpectralAnisotropyEnvelope

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def limitingEnvelope (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  if 0 < topGap S then
    min (2 * ‖R‖ * ‖w‖ ^ 2) (4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect S w / topGap S))
  else 2 * ‖R‖ * ‖w‖ ^ 2

theorem limitingEnvelope_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ limitingEnvelope S R w := by unfold limitingEnvelope; split <;> positivity

theorem limitingEnvelope_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    limitingEnvelope S R w ≤ 2 * ‖R‖ * ‖w‖ ^ 2 := by
  unfold limitingEnvelope
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem abs_remainderAnisotropy_le_limitingEnvelope (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) :
    |remainderAnisotropy R (topVector S) w| ≤ limitingEnvelope S R w := by
  unfold limitingEnvelope
  split_ifs with hg
  · apply le_min (abs_remainderAnisotropy_le R _ w (topVector_norm S))
    have hq : ‖lineRemainder (topVector S) w‖ ^ 2 ≤ topSpectralDefect S w / topGap S :=
      (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using topGap_mul_lineRemainder_sq_le S w)
    exact (abs_remainderAnisotropy_depleted R _ w (topVector_norm S)).trans
      (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hq) (by positivity))
  · exact abs_remainderAnisotropy_le R _ w (topVector_norm S)

theorem tendsto_envelope {ι : Type*} {l : Filter ι} (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ι → ℝ)
    (heps : ∀ᶠ i in l, 0 < epsilon i) (hzero : Tendsto epsilon l (𝓝 0)) :
    Tendsto (fun i ↦ envelope S R w (epsilon i)) l (𝓝 (limitingEnvelope S R w)) := by
  by_cases hg : 0 < topGap S
  · have hE : Tendsto (fun i ↦ regularizedEnergy S (epsilon i) w) l (𝓝 (topSpectralDefect S w)) := by
      simp_rw [regularizedEnergy_eq]
      simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hzero.mul_const (‖w‖ ^ 2))
    have hgap : Tendsto (fun i ↦ topGap S + epsilon i) l (𝓝 (topGap S)) := by
      simpa only [add_zero] using hzero.const_add (topGap S)
    have hroot := (hE.div hgap (ne_of_gt hg)).sqrt
    simpa only [envelope, limitingEnvelope, if_pos hg, Pi.div_apply] using
      tendsto_const_nhds.min (hroot.const_mul (4 * ‖R‖ * ‖w‖))
  · have hz : topGap S = 0 := le_antisymm (le_of_not_gt hg) (topGap_nonneg S)
    apply tendsto_const_nhds.congr'
    filter_upwards [heps] with i hi
    simp only [limitingEnvelope, if_neg hg, envelope_eq_coarse_of_topGap_zero S R w (epsilon i) hi hz]

theorem limitingEnvelope_aligned (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (alpha : ℝ) (hg : 0 < topGap S) :
    limitingEnvelope S R (alpha • topVector S) = 0 := by
  have hA : topSpectralDefect S (alpha • topVector S) = 0 := by
    simpa only [regularizedEnergy_eq, zero_mul, add_zero] using regularizedEnergy_aligned S 0 alpha
  simp only [limitingEnvelope, if_pos hg, hA, zero_div, Real.sqrt_zero, mul_zero,
    min_eq_right (by positivity : 0 ≤ 2 * ‖R‖ * ‖alpha • topVector S‖ ^ 2)]

def approximationParameter (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem approximationParameter_pos (n : ℕ) : 0 < approximationParameter n := by
  unfold approximationParameter
  positivity

theorem tendsto_approximationParameter : Tendsto approximationParameter atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem measurable_limitingEnvelope {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Measurable (fun x ↦ limitingEnvelope (S x) (R x) (w x)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x ↦ envelope (S x) (R x) (w x) (approximationParameter n))
    (fun n ↦ (continuous_envelope S R w _ (approximationParameter_pos n) hS hR hw).measurable)
  exact tendsto_pi_nhds.mpr (fun x ↦ tendsto_envelope (S x) (R x) (w x) approximationParameter
    (Eventually.of_forall approximationParameter_pos) tendsto_approximationParameter)

end Mettapedia.FluidDynamics.NavierStokes.SpectralAnisotropyLimit
