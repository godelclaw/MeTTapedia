import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionWeight
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyLimit

/-!
# Removing auxiliary smoothing from the capped diffusion weight

The limit uses the unregularized defect on the simple-top branch and
retains full vorticity at collisions. It is measurable, not necessarily
continuous. Dominated convergence is paid by the full vorticity square.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionWeightLimit

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeRegularizedMaterialRate
open PancakeAnisotropyDepletion SpectralAnisotropyEnvelope SpectralAnisotropyLimit SpectralDiffusionWeight

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def limitingWeight (S : SymmetricStrain) (w : R3) : ℝ :=
  if 0 < topGap S then min (‖w‖ ^ 2) (topSpectralDefect S w / topGap S) else ‖w‖ ^ 2

theorem limitingWeight_nonneg (S : SymmetricStrain) (w : R3) : 0 ≤ limitingWeight S w := by
  unfold limitingWeight
  split_ifs with hg
  · exact le_min (sq_nonneg _) (div_nonneg (topSpectralDefect_nonneg S w) hg.le)
  · positivity

theorem limitingWeight_le_norm_sq (S : SymmetricStrain) (w : R3) :
    limitingWeight S w ≤ ‖w‖ ^ 2 := by unfold limitingWeight; split <;> simp only [min_le_left, le_refl]

theorem limitingWeight_eq_norm_sq_of_topGap_zero (S : SymmetricStrain) (w : R3)
    (hg : topGap S = 0) : limitingWeight S w = ‖w‖ ^ 2 := by
  simp only [limitingWeight, hg, lt_self_iff_false, if_false]

theorem lineRemainder_sq_le_limitingWeight (S : SymmetricStrain) (w : R3) :
    ‖lineRemainder (topVector S) w‖ ^ 2 ≤ limitingWeight S w := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_lineRemainder_le _ w (topVector_norm S)) 2
  unfold limitingWeight
  split_ifs with hg
  · exact le_min hn ((le_div_iff₀ hg).mpr
      (by simpa only [mul_comm] using topGap_mul_lineRemainder_sq_le S w))
  · exact hn

theorem tendsto_weight {ι : Type*} {l : Filter ι} (S : SymmetricStrain) (w : R3)
    (epsilon : ι → ℝ) (heps : ∀ᶠ i in l, 0 < epsilon i) (hzero : Tendsto epsilon l (𝓝 0)) :
    Tendsto (fun i ↦ weight S w (epsilon i)) l (𝓝 (limitingWeight S w)) := by
  by_cases hg : 0 < topGap S
  · have hE : Tendsto (fun i ↦ regularizedEnergy S (epsilon i) w) l (𝓝 (topSpectralDefect S w)) := by
      simp_rw [regularizedEnergy_eq]
      simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hzero.mul_const (‖w‖ ^ 2))
    have hgap : Tendsto (fun i ↦ topGap S + epsilon i) l (𝓝 (topGap S)) := by
      simpa only [add_zero] using hzero.const_add (topGap S)
    simpa only [weight, limitingWeight, if_pos hg, Pi.div_apply] using
      tendsto_const_nhds.min (hE.div hgap (ne_of_gt hg))
  · have hz : topGap S = 0 := le_antisymm (le_of_not_gt hg) (topGap_nonneg S)
    apply tendsto_const_nhds.congr'
    filter_upwards [heps] with i hi
    simp only [limitingWeight, if_neg hg, weight_eq_norm_sq_of_topGap_zero S w (epsilon i) hi hz]

theorem limitingWeight_aligned (S : SymmetricStrain) (c : ℝ) (hg : 0 < topGap S) :
    limitingWeight S (c • topVector S) = 0 := by
  have hA : topSpectralDefect S (c • topVector S) = 0 := by
    simpa only [regularizedEnergy_eq, zero_mul, add_zero] using regularizedEnergy_aligned S 0 c
  simp only [limitingWeight, if_pos hg, hA, zero_div, min_eq_right (sq_nonneg _)]

theorem measurable_limitingWeight {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (w : X → R3) (hS : Continuous S) (hw : Continuous w) :
    Measurable (fun x ↦ limitingWeight (S x) (w x)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x ↦ weight (S x) (w x) (approximationParameter n))
    (fun n ↦ (continuous_weight S w _ (approximationParameter_pos n) hS hw).measurable)
  exact tendsto_pi_nhds.mpr (fun x ↦ tendsto_weight (S x) (w x) approximationParameter
    (Eventually.of_forall approximationParameter_pos) tendsto_approximationParameter)

theorem integrable_limitingWeight {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (S : X → SymmetricStrain) (w : X → R3)
    (hS : Continuous S) (hw : Continuous w) (hW : Integrable (fun x ↦ ‖w x‖ ^ 2) μ) :
    Integrable (fun x ↦ limitingWeight (S x) (w x)) μ := by
  apply hW.mono' (measurable_limitingWeight S w hS hw).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (limitingWeight_nonneg _ _)]
    exact limitingWeight_le_norm_sq _ _)

theorem tendsto_integral_weight {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (S : X → SymmetricStrain) (w : X → R3)
    (hS : Continuous S) (hw : Continuous w) (hW : Integrable (fun x ↦ ‖w x‖ ^ 2) μ) :
    Tendsto (fun n ↦ ∫ x, weight (S x) (w x) (approximationParameter n) ∂μ) atTop
      (𝓝 (∫ x, limitingWeight (S x) (w x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖w x‖ ^ 2)
    (fun n ↦ (continuous_weight S w _ (approximationParameter_pos n) hS hw).measurable.aestronglyMeasurable) hW
  · intro n
    exact Eventually.of_forall (fun x ↦ by
      rw [Real.norm_of_nonneg (weight_nonneg _ _ _ (approximationParameter_pos n))]
      exact weight_le_norm_sq _ _ _)
  · exact Eventually.of_forall (fun x ↦ tendsto_weight (S x) (w x) approximationParameter
      (Eventually.of_forall approximationParameter_pos) tendsto_approximationParameter)

end Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionWeightLimit
