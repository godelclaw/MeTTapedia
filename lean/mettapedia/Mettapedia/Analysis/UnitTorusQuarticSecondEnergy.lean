import Mettapedia.Analysis.UnitTorusContinuousRate

/-!
# Integrated coercivity of the second derivative of a fourth power

For a real periodic scalar field, integration by parts controls both
`f^6 (f'')^2` and `f^4 (f')^4` by the squared second derivative of `f^4`.
This is an integrated statement, not a pointwise Hessian lower bound.
The translation derivatives are actual derivatives, including at zeros.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusQuarticSecondEnergy

open MeasureTheory
variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def quarticSecond (f v z : ℝ) : ℝ := 12 * f ^ 2 * v ^ 2 + 4 * f ^ 3 * z

theorem hasDerivAt_quarticFirst {f v : ℝ → ℝ} {z t : ℝ}
    (hf : HasDerivAt f (v t) t) (hv : HasDerivAt v z t) :
    HasDerivAt (fun τ ↦ 4 * f τ ^ 3 * v τ) (quarticSecond (f t) (v t) z) t := by
  apply (((hf.fun_pow 3).const_mul 4).mul hv).congr_deriv
  unfold quarticSecond
  ring

variable (f v z : UnitAddTorus d → ℝ) (s : ℝ → UnitAddTorus d)
  (hf : Continuous f) (hv : Continuous v) (hz : Continuous z)
  (hs : Continuous s) (hs0 : s 0 = 0)
  (hf' : ∀ x h, HasDerivAt (fun t ↦ f (x + s t)) (v (x + s h)) h)
  (hv' : ∀ x h, HasDerivAt (fun t ↦ v (x + s t)) (z (x + s h)) h)

include hf hv hz hs hs0 hf' hv' in
theorem integral_mixed_identity :
    5 * (∫ x : T, f x ^ 4 * v x ^ 4) +
      3 * (∫ x : T, f x ^ 5 * v x ^ 2 * z x) = 0 := by
  have h := UnitTorusContinuousRate.integral_rate_eq_zero (d := d)
    (fun x ↦ f x ^ 5 * v x ^ 3)
    (fun x ↦ 5 * (f x ^ 4 * v x ^ 4) + 3 * (f x ^ 5 * v x ^ 2 * z x)) s
    (by fun_prop) (by fun_prop) hs hs0 (fun x h ↦ by
      apply (((hf' x h).fun_pow 5).mul ((hv' x h).fun_pow 3)).congr_deriv
      ring)
  have hI : Integrable (fun x : T ↦ f x ^ 4 * v x ^ 4) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 4 * v x ^ 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hM : Integrable (fun x : T ↦ f x ^ 5 * v x ^ 2 * z x) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 5 * v x ^ 2 * z x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rwa [integral_add (hI.const_mul 5) (hM.const_mul 3), integral_const_mul, integral_const_mul] at h

include hf hv hz hs hs0 hf' hv' in
/-- The exact integrated square keeps the cancellation from the mixed term. -/
theorem integral_quarticSecond_sq :
    (∫ x : T, quarticSecond (f x) (v x) (z x) ^ 2) =
      16 * ((∫ x : T, f x ^ 6 * z x ^ 2) - (∫ x : T, f x ^ 4 * v x ^ 4)) := by
  have hM := integral_mixed_identity (d := d) f v z s hf hv hz hs hs0 hf' hv'
  have hI : Integrable (fun x : T ↦ f x ^ 4 * v x ^ 4) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 4 * v x ^ 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x : T ↦ f x ^ 6 * z x ^ 2) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 6 * z x ^ 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiM : Integrable (fun x : T ↦ f x ^ 5 * v x ^ 2 * z x) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 5 * v x ^ 2 * z x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T) : quarticSecond (f x) (v x) (z x) ^ 2 =
      144 * (f x ^ 4 * v x ^ 4) + 96 * (f x ^ 5 * v x ^ 2 * z x) + 16 * (f x ^ 6 * z x ^ 2) := by
    unfold quarticSecond
    ring
  simp_rw [he]
  have h1 := integral_add ((hI.const_mul 144).add (hiM.const_mul 96)) (hJ.const_mul 16)
  simp only [Pi.add_apply] at h1
  rw [h1, integral_add (hI.const_mul 144) (hiM.const_mul 96)]
  simp only [integral_const_mul]
  linarith only [hM]

include hf hv hz hs hs0 hf' hv' in
theorem integral_weightedFirst_fourth_le :
    25 * (∫ x : T, f x ^ 4 * v x ^ 4) ≤ 9 * (∫ x : T, f x ^ 6 * z x ^ 2) := by
  have hM := integral_mixed_identity (d := d) f v z s hf hv hz hs hs0 hf' hv'
  have hI : Integrable (fun x : T ↦ f x ^ 4 * v x ^ 4) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 4 * v x ^ 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x : T ↦ f x ^ 6 * z x ^ 2) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 6 * z x ^ 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiM : Integrable (fun x : T ↦ f x ^ 5 * v x ^ 2 * z x) :=
    (by fun_prop : Continuous (fun x : T ↦ f x ^ 5 * v x ^ 2 * z x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpos : 0 ≤ ∫ x : T, (5 * f x ^ 2 * v x ^ 2 + 3 * f x ^ 3 * z x) ^ 2 :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  have he (x : T) : (5 * f x ^ 2 * v x ^ 2 + 3 * f x ^ 3 * z x) ^ 2 =
      25 * (f x ^ 4 * v x ^ 4) + 30 * (f x ^ 5 * v x ^ 2 * z x) + 9 * (f x ^ 6 * z x ^ 2) := by ring
  simp_rw [he] at hpos
  have h1 := integral_add ((hI.const_mul 25).add (hiM.const_mul 30)) (hJ.const_mul 9)
  simp only [Pi.add_apply] at h1
  rw [h1, integral_add (hI.const_mul 25) (hiM.const_mul 30)] at hpos
  simp only [integral_const_mul] at hpos
  linarith only [hM, hpos]

include hf hv hz hs hs0 hf' hv' in
theorem integral_weightedSecond_sq_le :
    (∫ x : T, f x ^ 6 * z x ^ 2) ≤
      (25 / 256 : ℝ) * ∫ x : T, quarticSecond (f x) (v x) (z x) ^ 2 := by
  have h1 := integral_quarticSecond_sq (d := d) f v z s hf hv hz hs hs0 hf' hv'
  have h2 := integral_weightedFirst_fourth_le (d := d) f v z s hf hv hz hs hs0 hf' hv'
  linarith only [h1, h2]

end Mettapedia.Analysis.UnitTorusQuarticSecondEnergy
