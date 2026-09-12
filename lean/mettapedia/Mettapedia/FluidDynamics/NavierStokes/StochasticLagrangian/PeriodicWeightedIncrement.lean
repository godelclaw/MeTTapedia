import Mettapedia.Analysis.RadialPower
import Mettapedia.Analysis.BilinearTranslatedCoefficient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTranslationEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicVectorWeakDerivative

/-!
# Product-weighted periodic increments

Spatial increments weighted by the cube of each endpoint norm are controlled
by the sixth-power-weighted weak gradient energy. The constant is 48 with the
wrapped sup norm on the three-dimensional unit torus. No uniform Lipschitz
constant of the field appears in the estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement

open MeasureTheory PeriodicVectorWeakDerivative PeriodicFourierGradientEnergy
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve
open PancakePeriodicVorticityEquation
open PancakeHaarTransportRate
open Mettapedia.Analysis.RadialPower

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def gradientDensity (f : T3 → R3) (x : T3) : ℝ :=
  ∑ j : Fin 3, ‖coordinateRate f j x‖ ^ 2

def weightedGradientDensity (f : T3 → R3) (x : T3) : ℝ :=
  ‖f x‖ ^ 6 * gradientDensity f x

def incrementDensity (f : T3 → R3) (y z : T3) : ℝ :=
  ‖f y‖ ^ 3 * ‖f z‖ ^ 3 * ‖f y - f z‖ ^ 2

theorem gradientDensity_eq_sum (f : T3 → R3) (x : T3) :
    gradientDensity f x = ∑ i : Fin 3, gradientSquare (fun y ↦ f y i) x := by
  simp only [gradientDensity, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    coordinateRate_apply, gradientSquare]
  exact Finset.sum_comm

theorem integrable_gradientDensity (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    Integrable (gradientDensity f) :=
  integrable_finsetSum _ (fun j _ ↦
    (PeriodicVectorWeakDerivative.memLp_coordinateRate f j hf hfL).integrable_norm_pow (by norm_num))

theorem integrable_weightedGradientDensity (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    Integrable (weightedGradientDensity f) := by
  let c : C(T3, ℝ) := ⟨_, hf.norm.pow 6⟩
  exact (integrable_gradientDensity f hf hfL).bdd_mul c.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall c.norm_coe_le_norm)

theorem integral_norm_sub_translate_sq_le (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (a : T3) :
    (∫ x : T3, ‖f x - f (x - a)‖ ^ 2) ≤
      3 * ‖a‖ ^ 2 * ∫ x : T3, gradientDensity f x := by
  have h := PeriodicTranslationEnergy.sum_integral_sub_translate_sq_le
    (fun i x ↦ f x i) (continuous_component f hf) (locallyLipschitz_component f hfL) a
  have hi (i : Fin 3) : Integrable (fun x : T3 ↦ (f x i - f (x - a) i) ^ 2) :=
    (((continuous_component f hf i).sub ((continuous_component f hf i).comp
      (continuous_id.sub continuous_const))).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg (i : Fin 3) : Integrable (gradientSquare (fun x ↦ f x i)) :=
    integrable_gradientSquare _ (continuous_component f hf i) (locallyLipschitz_component f hfL i)
  simp only [EuclideanSpace.norm_sq_eq, PiLp.sub_apply, Real.norm_eq_abs, sq_abs,
    integral_finsetSum _ (fun i _ ↦ hi i), gradientDensity_eq_sum,
    integral_finsetSum _ (fun i _ ↦ hg i)]
  exact h

theorem ae_gradientDensity_radialPower_three_le (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    ∀ᵐ x : T3, gradientDensity (fun y ↦ radialPower 3 (f y)) x ≤
      16 * weightedGradientDensity f x := by
  let g := fun y ↦ radialPower 3 (f y)
  have hg : Continuous g := (continuous_radialPower 3).comp hf
  have hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r)) :=
    locallyLipschitz_radialPower_three.comp hfL
  have hd (j : Fin 3) := ae_hasDerivAt_coordinateRate f j hf hfL
  have he (j : Fin 3) := ae_hasDerivAt_coordinateRate g j hg hgL
  filter_upwards [ae_all_iff.mpr hd, ae_all_iff.mpr he] with x hx hy
  have hb (j : Fin 3) : ‖coordinateRate g j x‖ ^ 2 ≤
      16 * ‖f x‖ ^ 6 * ‖coordinateRate f j x‖ ^ 2 := by
    have h := norm_derivative_radialPower_three_le (hx j) (hy j)
    simp only [coordinateShift_zero, add_zero] at h
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    exact hs.trans_eq (by ring)
  simpa only [gradientDensity, weightedGradientDensity, Finset.mul_sum, mul_assoc] using
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦ hb j)

/-- The cubic radial increment itself is paid by the weighted gradient. -/
theorem integral_radialPower_three_sub_le (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (a : T3) :
    (∫ x : T3, ‖radialPower 3 (f x) - radialPower 3 (f (x - a))‖ ^ 2) ≤
      48 * ‖a‖ ^ 2 * ∫ x : T3, weightedGradientDensity f x := by
  let g := fun y ↦ radialPower 3 (f y)
  have hg : Continuous g := (continuous_radialPower 3).comp hf
  have hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r)) :=
    locallyLipschitz_radialPower_three.comp hfL
  have hd := integral_mono_ae (integrable_gradientDensity g hg hgL)
    ((integrable_weightedGradientDensity f hf hfL).const_mul 16)
    (ae_gradientDensity_radialPower_three_le f hf hfL)
  rw [integral_const_mul] at hd
  calc
    _ ≤ 3 * ‖a‖ ^ 2 * ∫ x : T3, gradientDensity g x :=
      integral_norm_sub_translate_sq_le g hg hgL a
    _ ≤ 3 * ‖a‖ ^ 2 * (16 * ∫ x : T3, weightedGradientDensity f x) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

/-- The sixth-power-weighted weak gradient pays for the bare increment channel.
Additional endpoint-dependent coefficients are not discarded. -/
theorem integral_incrementDensity_sub_le (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (a : T3) :
    (∫ x : T3, incrementDensity f x (x - a)) ≤
      48 * ‖a‖ ^ 2 * ∫ x : T3, weightedGradientDensity f x := by
  let g := fun y ↦ radialPower 3 (f y)
  have hg : Continuous g := (continuous_radialPower 3).comp hf
  have hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r)) :=
    locallyLipschitz_radialPower_three.comp hfL
  have hfi : Integrable (fun x : T3 ↦ incrementDensity f x (x - a)) :=
    ((((hf.norm.pow 3).mul ((hf.comp (continuous_id.sub continuous_const)).norm.pow 3)).mul
      ((hf.sub (hf.comp (continuous_id.sub continuous_const))).norm.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (fun x : T3 ↦ ‖g x - g (x - a)‖ ^ 2) :=
    ((hg.sub (hg.comp (continuous_id.sub continuous_const))).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hd := integral_mono_ae (integrable_gradientDensity g hg hgL)
    ((integrable_weightedGradientDensity f hf hfL).const_mul 16)
    (ae_gradientDensity_radialPower_three_le f hf hfL)
  rw [integral_const_mul] at hd
  calc
    _ ≤ ∫ x : T3, ‖g x - g (x - a)‖ ^ 2 :=
      integral_mono hfi hgi (fun x ↦ product_weighted_norm_sub_sq_le 3 (f x) (f (x - a)))
    _ ≤ 3 * ‖a‖ ^ 2 * ∫ x : T3, gradientDensity g x :=
      integral_norm_sub_translate_sq_le g hg hgL a
    _ ≤ 3 * ‖a‖ ^ 2 * (16 * ∫ x : T3, weightedGradientDensity f x) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

theorem integral_incrementDensity_translate_le (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (a b : T3) :
    (∫ x : T3, incrementDensity f (x - a) (x - b)) ≤
      48 * ‖a - b‖ ^ 2 * ∫ x : T3, weightedGradientDensity f x := by
  have h := integral_incrementDensity_sub_le f hf hfL (b - a)
  rw [← integral_sub_right_eq_self (fun x : T3 ↦ incrementDensity f x (x - (b - a))) a] at h
  have he (x : T3) : (x - a) - (b - a) = x - b := by abel
  simpa only [he, norm_sub_rev b a] using h

local notation "T6" => UnitAddTorus (Fin 6)

theorem continuous_incrementDensity (f : T3 → R3) (hf : Continuous f) :
    Continuous (fun p : T3 × T3 ↦ incrementDensity f p.1 p.2) :=
  (((hf.comp continuous_fst).norm.pow 3).mul ((hf.comp continuous_snd).norm.pow 3)).mul
    (((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm.pow 2)

theorem integrable_envelope_incrementDensity (f : T3 → R3) (hf : Continuous f)
    (M : T6 → ℝ) (hM : Integrable M) (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ M p.1 * incrementDensity f (p.2 - a p.1) (p.2 - b p.1))
      ((volume : Measure T6).prod (volume : Measure T3)) := by
  have h := Mettapedia.Analysis.BilinearTranslatedCoefficient.integrable_weighted_translate_mul_continuous
    (μ := (volume : Measure T6)) (ν := (volume : Measure T3))
    M (fun _ : T3 ↦ (1 : ℝ)) hM (integrable_const 1) a b ha hb
    ⟨_, continuous_incrementDensity f hf⟩
  simpa only [mul_one, ContinuousMap.coe_mk] using h

/-- Integrating the relative displacement preserves its second-moment gain. -/
theorem integral_envelope_incrementDensity_le (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b)
    (hm : Integrable (fun q ↦ ‖a q - b q‖ ^ 2 * M q)) :
    (∫ x : T3, ∫ q : T6, M q * incrementDensity f (x - a q) (x - b q)) ≤
      48 * (∫ q : T6, ‖a q - b q‖ ^ 2 * M q) * ∫ x : T3, weightedGradientDensity f x := by
  have hi := integrable_envelope_incrementDensity f hf M hM a b ha hb
  rw [← integral_integral_swap hi]
  have hbnd (q : T6) : (∫ x : T3, M q * incrementDensity f (x - a q) (x - b q)) ≤
      (48 * (‖a q - b q‖ ^ 2 * M q)) * ∫ x : T3, weightedGradientDensity f x := by
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left
      (integral_incrementDensity_translate_le f hf hfL (a q) (b q)) (hMn q)
    exact h.trans_eq (by ring)
  have h := integral_mono hi.integral_prod_left ((hm.const_mul 48).mul_const _) hbnd
  simpa only [integral_mul_const, integral_const_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement
