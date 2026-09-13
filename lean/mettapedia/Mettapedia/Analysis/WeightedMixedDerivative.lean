import Mettapedia.Analysis.UnitTorusContinuousRate
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Weighted mixed derivatives from diagonal derivatives and first jets

The difference of two periodic flux divergences cancels the common third
derivative. Completing squares bounds the remaining mixed derivative by
diagonal second derivatives and fourth powers of first derivatives. This
is a spatial integration-by-parts estimate; there is no pointwise Hessian
coercivity assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedMixedDerivative

open scoped RealInnerProductSpace
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def flux (a v c : E) : ℝ := ‖a‖ ^ 6 * ⟪v, c⟫

def fluxRate (a v c da dv dc : E) : ℝ :=
  6 * ‖a‖ ^ 4 * ⟪a, da⟫ * ⟪v, c⟫ + ‖a‖ ^ 6 * (⟪dv, c⟫ + ⟪v, dc⟫)

def mixedDensity (a v w b c h : E) : ℝ :=
  ‖a‖ ^ 6 * ⟪b, c⟫ + 6 * ‖a‖ ^ 4 * ⟪a, v⟫ * ⟪v, c⟫ -
    6 * ‖a‖ ^ 4 * ⟪a, w⟫ * ⟪v, h⟫

theorem hasDerivAt_flux {a v c : ℝ → E} {da dv dc : E} {t : ℝ}
    (ha : HasDerivAt a da t) (hv : HasDerivAt v dv t) (hc : HasDerivAt c dc t) :
    HasDerivAt (fun τ ↦ flux (a τ) (v τ) (c τ)) (fluxRate (a t) (v t) (c t) da dv dc) t := by
  have h := (ha.norm_sq.fun_pow 3).mul (hv.inner ℝ hc)
  simp only [← pow_mul, Nat.reduceMul] at h
  apply h.congr_deriv
  unfold fluxRate
  ring

theorem fluxRate_sub (a v w b c h q : E) :
    fluxRate a v c v b q - fluxRate a v h w h q = mixedDensity a v w b c h - ‖a‖ ^ 6 * ‖h‖ ^ 2 := by
  simp only [fluxRate, mixedDensity, real_inner_self_eq_norm_sq]
  ring

theorem two_mul_mixedDensity_le (a v w b c h : E) :
    2 * mixedDensity a v w b c h ≤
      ‖a‖ ^ 6 * ‖h‖ ^ 2 + ‖a‖ ^ 6 * ‖b‖ ^ 2 + 7 * ‖a‖ ^ 6 * ‖c‖ ^ 2 +
        24 * ‖a‖ ^ 4 * ‖v‖ ^ 4 + 18 * ‖a‖ ^ 4 * ‖w‖ ^ 4 := by
  have hbc := sq_nonneg ‖b - c‖
  rw [norm_sub_sq_real] at hbc
  have hbc' := mul_nonneg (show 0 ≤ ‖a‖ ^ 6 by positivity) hbc
  have hvcs : ⟪a, v⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le a v
  have hwcs : ⟪a, w⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖w‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le a w
  have hs1 := sq_nonneg ‖(‖a‖ * ⟪a, v⟫) • v - ‖a‖ ^ 3 • c‖
  have hs2 := sq_nonneg ‖(6 * ‖a‖ * ⟪a, w⟫) • v + ‖a‖ ^ 3 • h‖
  simp only [norm_sub_sq_real, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right] at hs1 hs2
  have hvbound := mul_le_mul_of_nonneg_left hvcs
    (show 0 ≤ ‖a‖ ^ 2 * ‖v‖ ^ 2 by positivity)
  have hwbound := mul_le_mul_of_nonneg_left hwcs
    (show 0 ≤ 36 * ‖a‖ ^ 2 * ‖v‖ ^ 2 by positivity)
  have hprod := mul_nonneg (show 0 ≤ 18 * ‖a‖ ^ 4 by positivity)
    (sq_nonneg (‖v‖ ^ 2 - ‖w‖ ^ 2))
  unfold mixedDensity
  nlinarith only [hbc', hs1, hs2, hvbound, hwbound, hprod]

variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (a v w b c h q : UnitAddTorus d → E) (sj sk : ℝ → UnitAddTorus d)
  (ha : Continuous a) (hv : Continuous v) (hw : Continuous w) (hb : Continuous b)
  (hc : Continuous c) (hh : Continuous h) (hq : Continuous q)
  (hsj : Continuous sj) (hsk : Continuous sk) (hsj0 : sj 0 = 0) (hsk0 : sk 0 = 0)
  (haj : ∀ x t, HasDerivAt (fun τ ↦ a (x + sj τ)) (v (x + sj t)) t)
  (hak : ∀ x t, HasDerivAt (fun τ ↦ a (x + sk τ)) (w (x + sk t)) t)
  (hvj : ∀ x t, HasDerivAt (fun τ ↦ v (x + sj τ)) (b (x + sj t)) t)
  (hvk : ∀ x t, HasDerivAt (fun τ ↦ v (x + sk τ)) (h (x + sk t)) t)
  (hcj : ∀ x t, HasDerivAt (fun τ ↦ c (x + sj τ)) (q (x + sj t)) t)
  (hhk : ∀ x t, HasDerivAt (fun τ ↦ h (x + sk τ)) (q (x + sk t)) t)

include ha hv hw hb hc hh hq hsj hsk hsj0 hsk0 haj hak hvj hvk hcj hhk in
theorem integral_mixedDensity_eq :
    (∫ x : T, mixedDensity (a x) (v x) (w x) (b x) (c x) (h x)) =
      ∫ x : T, ‖a x‖ ^ 6 * ‖h x‖ ^ 2 := by
  have hj := UnitTorusContinuousRate.integral_rate_eq_zero (d := d)
    (fun x ↦ flux (a x) (v x) (c x)) (fun x ↦ fluxRate (a x) (v x) (c x) (v x) (b x) (q x)) sj
    (by unfold flux; fun_prop) (by unfold fluxRate; fun_prop) hsj hsj0
    (fun x t ↦ hasDerivAt_flux (haj x t) (hvj x t) (hcj x t))
  have hk := UnitTorusContinuousRate.integral_rate_eq_zero (d := d)
    (fun x ↦ flux (a x) (v x) (h x)) (fun x ↦ fluxRate (a x) (v x) (h x) (w x) (h x) (q x)) sk
    (by unfold flux; fun_prop) (by unfold fluxRate; fun_prop) hsk hsk0
    (fun x t ↦ hasDerivAt_flux (hak x t) (hvk x t) (hhk x t))
  have hiJ : Integrable (fun x : T ↦ fluxRate (a x) (v x) (c x) (v x) (b x) (q x)) :=
    (by unfold fluxRate; fun_prop : Continuous (fun x : T ↦
      fluxRate (a x) (v x) (c x) (v x) (b x) (q x))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hiK : Integrable (fun x : T ↦ fluxRate (a x) (v x) (h x) (w x) (h x) (q x)) :=
    (by unfold fluxRate; fun_prop : Continuous (fun x : T ↦
      fluxRate (a x) (v x) (h x) (w x) (h x) (q x))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hiM : Integrable (fun x : T ↦ mixedDensity (a x) (v x) (w x) (b x) (c x) (h x)) :=
    (by unfold mixedDensity; fun_prop : Continuous (fun x : T ↦
      mixedDensity (a x) (v x) (w x) (b x) (c x) (h x))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun x : T ↦ ‖a x‖ ^ 6 * ‖h x‖ ^ 2) :=
    ((ha.norm.pow 6).mul (hh.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := integral_sub hiJ hiK
  simp_rw [fluxRate_sub] at he
  rw [integral_sub hiM hiH, hj, hk] at he
  linarith only [he]

include ha hv hw hb hc hh hq hsj hsk hsj0 hsk0 haj hak hvj hvk hcj hhk in
theorem integral_weighted_mixed_sq_le :
    (∫ x : T, ‖a x‖ ^ 6 * ‖h x‖ ^ 2) ≤
      (∫ x : T, ‖a x‖ ^ 6 * ‖b x‖ ^ 2) + 7 * (∫ x : T, ‖a x‖ ^ 6 * ‖c x‖ ^ 2) +
        24 * (∫ x : T, ‖a x‖ ^ 4 * ‖v x‖ ^ 4) + 18 * (∫ x : T, ‖a x‖ ^ 4 * ‖w x‖ ^ 4) := by
  have he := integral_mixedDensity_eq a v w b c h q sj sk ha hv hw hb hc hh hq hsj hsk hsj0 hsk0
    haj hak hvj hvk hcj hhk
  have hiM : Integrable (fun x : T ↦ mixedDensity (a x) (v x) (w x) (b x) (c x) (h x)) :=
    (by unfold mixedDensity; fun_prop : Continuous (fun x : T ↦
      mixedDensity (a x) (v x) (w x) (b x) (c x) (h x))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi6 (f : T → E) (hf : Continuous f) : Integrable (fun x : T ↦ ‖a x‖ ^ 6 * ‖f x‖ ^ 2) :=
    ((ha.norm.pow 6).mul (hf.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi4 (f : T → E) (hf : Continuous f) : Integrable (fun x : T ↦ ‖a x‖ ^ 4 * ‖f x‖ ^ 4) :=
    ((ha.norm.pow 4).mul (hf.norm.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hle := integral_mono (hiM.const_mul 2)
    (((((hi6 h hh).add (hi6 b hb)).add ((hi6 c hc).const_mul 7)).add ((hi4 v hv).const_mul 24)).add
      ((hi4 w hw).const_mul 18)) (fun x ↦ by
        simpa only [Pi.add_apply, mul_assoc] using
          two_mul_mixedDensity_le (a x) (v x) (w x) (b x) (c x) (h x))
  have h1 := integral_add ((((hi6 h hh).add (hi6 b hb)).add ((hi6 c hc).const_mul 7)).add
    ((hi4 v hv).const_mul 24)) ((hi4 w hw).const_mul 18)
  have h2 := integral_add (((hi6 h hh).add (hi6 b hb)).add ((hi6 c hc).const_mul 7)) ((hi4 v hv).const_mul 24)
  have h3 := integral_add ((hi6 h hh).add (hi6 b hb)) ((hi6 c hc).const_mul 7)
  have h4 := integral_add (hi6 h hh) (hi6 b hb)
  simp only [Pi.add_apply] at h1 h2 h3 h4 hle
  rw [h1, h2, h3, h4] at hle
  simp only [integral_const_mul, he] at hle
  linarith only [hle]

end Mettapedia.Analysis.WeightedMixedDerivative
