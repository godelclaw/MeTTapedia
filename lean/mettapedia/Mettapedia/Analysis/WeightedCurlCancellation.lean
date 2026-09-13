import Mettapedia.Analysis.UnitTorusWeakDerivative
import Mettapedia.Analysis.EuclideanCrossProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-!
# Radially weighted curl-gradient cancellation

The unweighted cancellation underlies Evan Miller's strain-vorticity identity
(Theorem 3.1, https://arxiv.org/abs/2407.02691). The radial weight leaves a
specific longitudinal-amplitude/helicity term; it does not preserve zero.
The proofs below are direct differentiation and periodic integration.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCurlCancellation

open scoped RealInnerProductSpace
open MeasureTheory UnitTorusWeakDerivative
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance curlCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance curlCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance curlCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The curl of a first spatial jet, indexed by differentiation coordinate. -/
def curlJet (D : Fin 3 → R3) : R3 :=
  WithLp.toLp 2 ![D 1 2 - D 2 1, D 2 0 - D 0 2, D 0 1 - D 1 0]

theorem norm_curlJet_sq_le (D : Fin 3 → R3) :
    ‖curlJet D‖ ^ 2 ≤ 2 * ∑ j : Fin 3, ‖D j‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, curlJet, Fin.sum_univ_three]
  nlinarith [sq_nonneg (D 1 2 + D 2 1), sq_nonneg (D 2 0 + D 0 2),
    sq_nonneg (D 0 1 + D 1 0), sq_nonneg (D 0 0), sq_nonneg (D 1 1), sq_nonneg (D 2 2)]

theorem curl_inner_transport (a : R3) (D : Fin 3 → R3) :
    (∑ j : Fin 3, a j * ⟪D j, curlJet D⟫) =
      ∑ j : Fin 3, ⟪a, D j⟫ * curlJet D j := by
  simp [curlJet, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

def weightRate (n : ℕ) (a v : R3) : ℝ :=
  (n : ℝ) * (‖a‖ ^ 2) ^ (n - 1) * (2 * ⟪a, v⟫)

def flux (n : ℕ) (a q : R3) (j : Fin 3) : ℝ :=
  (‖a‖ ^ 2) ^ n * a j * ⟪a, q⟫ -
    (‖a‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ)) * q j

def fluxRate (n : ℕ) (a q v z : R3) (j : Fin 3) : ℝ :=
  weightRate n a v * a j * ⟪a, q⟫ +
    (‖a‖ ^ 2) ^ n * v j * ⟪a, q⟫ +
    (‖a‖ ^ 2) ^ n * a j * (⟪v, q⟫ + ⟪a, z⟫) -
    (‖a‖ ^ 2) ^ n * ⟪a, v⟫ * q j -
    (‖a‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ)) * z j

theorem hasDerivAt_flux (n : ℕ) {a q : ℝ → R3} {v z : R3} {t : ℝ}
    (ha : HasDerivAt a v t) (hq : HasDerivAt q z t) (j : Fin 3) :
    HasDerivAt (fun τ ↦ flux n (a τ) (q τ) j) (fluxRate n (a t) (q t) v z j) t := by
  have haj : HasDerivAt (fun τ ↦ a τ j) (v j) t := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const t (EuclideanSpace.single j (1 : ℝ))).inner ℝ ha
  have hqj : HasDerivAt (fun τ ↦ q τ j) (z j) t := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const t (EuclideanSpace.single j (1 : ℝ))).inner ℝ hq
  have hd := (((ha.norm_sq.fun_pow n).mul haj).mul (ha.inner ℝ hq)).sub
    (((ha.norm_sq.fun_pow (n + 1)).div_const (2 * (n + 1 : ℕ))).mul hqj)
  apply hd.congr_deriv
  simp only [fluxRate, weightRate, Nat.add_sub_cancel, Pi.mul_apply]
  have hn : (2 : ℝ) * (n + 1 : ℕ) ≠ 0 := by positivity
  field_simp
  ring

theorem sum_fluxRate (n : ℕ) (a q : R3) (D E : Fin 3 → R3)
    (hc : q = curlJet D) (hD : ∑ j : Fin 3, D j j = 0)
    (hE : ∑ j : Fin 3, E j j = 0) :
    (∑ j : Fin 3, fluxRate n a q (D j) (E j) j) =
      (‖a‖ ^ 2) ^ n * (∑ j : Fin 3, a j * ⟪a, E j⟫) +
        (∑ j : Fin 3, a j * weightRate n a (D j)) * ⟪a, q⟫ := by
  have hc' := curl_inner_transport a D
  rw [← hc] at hc'
  simp only [Fin.sum_univ_three, fluxRate] at hD hE hc' ⊢
  linear_combination ((‖a‖ ^ 2) ^ n * ⟪a, q⟫) * hD -
    ((‖a‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ))) * hE + (‖a‖ ^ 2) ^ n * hc'

theorem contDiff_flux (n : ℕ) (j : Fin 3) :
    ContDiff ℝ 1 (fun p : R3 × R3 ↦ flux n p.1 p.2 j) := by
  unfold flux
  have hfst : ContDiff ℝ 1 (fun p : R3 × R3 ↦ p.1) := contDiff_fst
  have hsnd : ContDiff ℝ 1 (fun p : R3 × R3 ↦ p.2) := contDiff_snd
  have ha : ContDiff ℝ 1 (fun p : R3 × R3 ↦ (p.1 j : ℝ)) := by
    simpa [EuclideanSpace.inner_single_left] using
      (contDiff_const (c := EuclideanSpace.single j (1 : ℝ))).inner ℝ hfst
  have hq : ContDiff ℝ 1 (fun p : R3 × R3 ↦ (p.2 j : ℝ)) := by
    simpa [EuclideanSpace.inner_single_left] using
      (contDiff_const (c := EuclideanSpace.single j (1 : ℝ))).inner ℝ hsnd
  exact (((contDiff_fst.norm_sq ℝ).pow n).mul ha |>.mul (contDiff_fst.inner ℝ contDiff_snd)).sub
    ((((contDiff_fst.norm_sq ℝ).pow (n + 1)).div_const _).mul hq)

variable (a q : T3 → R3) (D E : Fin 3 → T3 → R3)
  (ha : Continuous a) (hq : Continuous q)
  (hD : ∀ j, Continuous (D j)) (hE : ∀ j, Continuous (E j))
  (haL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ a (torusPoint r)))
  (hqL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ q (torusPoint r)))
  (hda : ∀ j x, HasDerivAt (fun h ↦ a (x + coordinateShift j h)) (D j x) 0)
  (hdq : ∀ j x, HasDerivAt (fun h ↦ q (x + coordinateShift j h)) (E j x) 0)
  (hcurl : ∀ x, q x = curlJet (fun j ↦ D j x))
  (hdiva : ∀ x, ∑ j : Fin 3, D j x j = 0)
  (hdivq : ∀ x, ∑ j : Fin 3, E j x j = 0)

include ha hq hD hE haL hqL hda hdq hcurl hdiva hdivq in
/-- The radial weight leaves a longitudinal derivative times helicity.
All jets in this statement are ordinary spatial derivatives. -/
theorem integral_weighted_curl_gradient_eq (n : ℕ) :
    (∫ x : T3, (‖a x‖ ^ 2) ^ n * (∑ j : Fin 3, a x j * ⟪a x, E j x⟫)) =
      -(∫ x : T3, (∑ j : Fin 3, a x j * weightRate n (a x) (D j x)) * ⟪a x, q x⟫) := by
  have hz (j : Fin 3) :
      Integrable (fun x : T3 ↦ fluxRate n (a x) (q x) (D j x) (E j x) j) ∧
      (∫ x : T3, fluxRate n (a x) (q x) (D j x) (E j x) j) = 0 := by
    have hd : shiftRate (fun y ↦ flux n (a y) (q y) j) (coordinateShift j) =
        fun x ↦ fluxRate n (a x) (q x) (D j x) (E j x) j := by
      funext x
      simpa only [shiftRate, coordinateShift_zero, add_zero] using
        (hasDerivAt_flux n (hda j x) (hdq j x) j).deriv
    simpa only [hd] using integral_coordinateRate_zero
      (fun x ↦ flux n (a x) (q x) j) j
      ((contDiff_flux n j).continuous.comp (f := fun x : T3 ↦ (a x, q x)) (ha.prodMk hq))
      ((contDiff_flux n j).locallyLipschitz.comp (g := fun r ↦ (a (torusPoint r), q (torusPoint r)))
        (haL.prodMk hqL))
  have hs : (∫ x : T3, ∑ j : Fin 3, fluxRate n (a x) (q x) (D j x) (E j x) j) = 0 := by
    rw [integral_finsetSum _ (fun j _ ↦ (hz j).1)]
    simp only [(hz _).2, Finset.sum_const_zero]
  have he (x : T3) := sum_fluxRate n (a x) (q x) (fun j ↦ D j x) (fun j ↦ E j x)
    (hcurl x) (hdiva x) (hdivq x)
  simp_rw [he] at hs
  have hleft : Continuous (fun x : T3 ↦
      (‖a x‖ ^ 2) ^ n * (∑ j : Fin 3, a x j * ⟪a x, E j x⟫)) := by
    exact ((ha.norm.pow 2).pow n).mul (continuous_finsetSum _
      (fun j _ ↦ ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp ha).mul (ha.inner (hE j))))
  have hright : Continuous (fun x : T3 ↦
      (∑ j : Fin 3, a x j * weightRate n (a x) (D j x)) * ⟪a x, q x⟫) := by
    unfold weightRate
    exact (continuous_finsetSum _ (fun j _ ↦
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp ha).mul
        ((continuous_const.mul ((ha.norm.pow 2).pow (n - 1))).mul
          (continuous_const.mul (ha.inner (hD j)))))).mul (ha.inner hq)
  rw [integral_add (hleft.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hright.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hs
  linarith only [hs]

include ha hq hD hE haL hqL hda hdq hcurl hdiva hdivq in
theorem integral_curl_gradient_eq_zero :
    (∫ x : T3, ∑ j : Fin 3, a x j * ⟪a x, E j x⟫) = 0 := by
  simpa [weightRate] using integral_weighted_curl_gradient_eq
    a q D E ha hq hD hE haL hqL hda hdq hcurl hdiva hdivq 0

include ha hq hD hE haL hqL hda hdq hcurl hdiva hdivq in
theorem integral_sixth_weighted_curl_gradient_eq :
    (∫ x : T3, ‖a x‖ ^ 6 * (∑ j : Fin 3, a x j * ⟪a x, E j x⟫)) =
      -6 * (∫ x : T3, ‖a x‖ ^ 4 * (∑ j : Fin 3, a x j * ⟪a x, D j x⟫) * ⟪a x, q x⟫) := by
  have h := integral_weighted_curl_gradient_eq
    a q D E ha hq hD hE haL hqL hda hdq hcurl hdiva hdivq 3
  have hr (x : T3) :
      (∑ j : Fin 3, a x j * weightRate 3 (a x) (D j x)) * ⟪a x, q x⟫ =
        6 * (‖a x‖ ^ 4 * (∑ j : Fin 3, a x j * ⟪a x, D j x⟫) * ⟪a x, q x⟫) := by
    norm_num [weightRate, ← pow_mul, Fin.sum_univ_three]
    ring
  simp only [← pow_mul, hr, integral_const_mul] at h
  convert h using 1
  ring

end Mettapedia.Analysis.WeightedCurlCancellation
