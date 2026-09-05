import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierBilinearTransfer

/-!
# Stability of the periodic bilinear kernel action

Fourier truncation of a spatial cutoff produces an input error.  This module
isolates the universal analytic estimate that turns such input errors into an
operator error.  It is independent of the particular pancake multiplier and
can therefore be reused once a quantitative cutoff-tail bound is available.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBilinearActionStability

open MeasureTheory
open PeriodicFourierTriad
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeFiniteFourierBilinearTransfer

theorem applyCoherentBilinearOperator_sub_left
    (A : CoherentBilinearOperator) (u₁ u₂ v : ComplexVec3) :
    applyCoherentBilinearOperator A (u₁ - u₂) v =
      applyCoherentBilinearOperator A u₁ v -
        applyCoherentBilinearOperator A u₂ v := by
  ext i
  simp only [applyCoherentBilinearOperator, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

theorem applyCoherentBilinearOperator_sub_right
    (A : CoherentBilinearOperator) (u v₁ v₂ : ComplexVec3) :
    applyCoherentBilinearOperator A u (v₁ - v₂) =
      applyCoherentBilinearOperator A u v₁ -
        applyCoherentBilinearOperator A u v₂ := by
  ext i
  simp only [applyCoherentBilinearOperator, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

/-- The integrand defining the torus bilinear action is integrable whenever
the kernel is integrable and both continuous inputs have explicit sup bounds. -/
theorem integrable_torusBilinearKernelAction_integrand
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) (M N : ℝ)
    (hKint : Integrable K frequencyPairUnitTorusMeasure)
    (hKmeas : Measurable K) (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ y, ‖f y‖ ≤ M) (hgb : ∀ y, ‖g y‖ ≤ N) :
    Integrable (fun q : FrequencyPairUnitTorus ↦
      applyCoherentBilinearOperator (K q)
        (f (x - firstTorusDisplacement q))
        (g (x - secondTorusDisplacement q)))
      frequencyPairUnitTorusMeasure := by
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hN : 0 ≤ N := (norm_nonneg (g x)).trans (hgb x)
  have hmeas : Measurable (fun q : FrequencyPairUnitTorus ↦
      applyCoherentBilinearOperator (K q)
        (f (x - firstTorusDisplacement q))
        (g (x - secondTorusDisplacement q))) := by
    unfold applyCoherentBilinearOperator
    fun_prop
  have hdom : Integrable
      (fun q : FrequencyPairUnitTorus ↦ 9 * ‖K q‖ * M * N)
      frequencyPairUnitTorusMeasure :=
    (hKint.norm.const_mul 9).mul_const M |>.mul_const N
  apply hdom.mono' hmeas.aestronglyMeasurable
  filter_upwards with q
  refine (norm_applyCoherentBilinearOperator_le (K q) _ _).trans ?_
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hfb _)
      (mul_nonneg (by norm_num) (norm_nonneg (K q))))
    (hgb _) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg (K q))) hM)

/-- **Bilinear input-stability estimate.**  Replacing both inputs costs one
first-input error term and one second-input error term.  In particular, no
Fourier support cardinality occurs. -/
theorem norm_torusBilinearKernelAction_sub_le
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (f f₀ g g₀ : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) (E N M F : ℝ)
    (hKint : Integrable K frequencyPairUnitTorusMeasure)
    (hKmeas : Measurable K)
    (hf : Continuous f) (hf₀ : Continuous f₀)
    (hg : Continuous g) (hg₀ : Continuous g₀)
    (hfError : ∀ y, ‖f y - f₀ y‖ ≤ E)
    (hgBound : ∀ y, ‖g y‖ ≤ N)
    (hf₀Bound : ∀ y, ‖f₀ y‖ ≤ M)
    (hgError : ∀ y, ‖g y - g₀ y‖ ≤ F) :
    ‖torusBilinearKernelAction K f g x -
        torusBilinearKernelAction K f₀ g₀ x‖ ≤
      9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * E * N +
        9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * M * F := by
  have hE : 0 ≤ E := (norm_nonneg (f x - f₀ x)).trans (hfError x)
  have hN : 0 ≤ N := (norm_nonneg (g x)).trans (hgBound x)
  have hM : 0 ≤ M := (norm_nonneg (f₀ x)).trans (hf₀Bound x)
  have hF : 0 ≤ F := (norm_nonneg (g x - g₀ x)).trans (hgError x)
  have hfBound : ∀ y, ‖f y‖ ≤ E + M := by
    intro y
    calc
      ‖f y‖ = ‖(f y - f₀ y) + f₀ y‖ := by congr 1; abel
      _ ≤ ‖f y - f₀ y‖ + ‖f₀ y‖ := norm_add_le _ _
      _ ≤ E + M := add_le_add (hfError y) (hf₀Bound y)
  have hg₀Bound : ∀ y, ‖g₀ y‖ ≤ N + F := by
    intro y
    calc
      ‖g₀ y‖ = ‖g y - (g y - g₀ y)‖ := by congr 1; abel
      _ ≤ ‖g y‖ + ‖g y - g₀ y‖ := norm_sub_le _ _
      _ ≤ N + F := add_le_add (hgBound y) (hgError y)
  have hdiffF : Continuous (fun y ↦ f y - f₀ y) := hf.sub hf₀
  have hdiffG : Continuous (fun y ↦ g y - g₀ y) := hg.sub hg₀
  have hfg := integrable_torusBilinearKernelAction_integrand
    K f g x (E + M) N hKint hKmeas hf hg hfBound hgBound
  have hf₀g₀ := integrable_torusBilinearKernelAction_integrand
    K f₀ g₀ x M (N + F) hKint hKmeas hf₀ hg₀ hf₀Bound hg₀Bound
  have hdiffg := integrable_torusBilinearKernelAction_integrand
    K (fun y ↦ f y - f₀ y) g x E N hKint hKmeas
      hdiffF hg hfError hgBound
  have hf₀diff := integrable_torusBilinearKernelAction_integrand
    K f₀ (fun y ↦ g y - g₀ y) x M F hKint hKmeas
      hf₀ hdiffG hf₀Bound hgError
  have hsplit :
      torusBilinearKernelAction K f g x -
          torusBilinearKernelAction K f₀ g₀ x =
        torusBilinearKernelAction K (fun y ↦ f y - f₀ y) g x +
          torusBilinearKernelAction K f₀ (fun y ↦ g y - g₀ y) x := by
    unfold torusBilinearKernelAction
    rw [← integral_sub hfg hf₀g₀, ← integral_add hdiffg hf₀diff]
    apply integral_congr_ae
    filter_upwards with q
    rw [applyCoherentBilinearOperator_sub_left,
      applyCoherentBilinearOperator_sub_right]
    abel
  rw [hsplit]
  calc
    ‖torusBilinearKernelAction K (fun y ↦ f y - f₀ y) g x +
        torusBilinearKernelAction K f₀ (fun y ↦ g y - g₀ y) x‖ ≤
      ‖torusBilinearKernelAction K (fun y ↦ f y - f₀ y) g x‖ +
        ‖torusBilinearKernelAction K f₀ (fun y ↦ g y - g₀ y) x‖ :=
      norm_add_le _ _
    _ ≤ 9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * E * N +
        9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * M * F :=
      add_le_add
        (norm_torusBilinearKernelAction_le K _ _ x E N
          hKint hKmeas hdiffF hg hfError hgBound)
        (norm_torusBilinearKernelAction_le K _ _ x M F
          hKint hKmeas hf₀ hdiffG hf₀Bound hgError)

end PancakeBilinearActionStability
end NavierStokes
end FluidDynamics
end Mettapedia
