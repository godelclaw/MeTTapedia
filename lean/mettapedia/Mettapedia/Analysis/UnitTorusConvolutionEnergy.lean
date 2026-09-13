import Mettapedia.Analysis.UnitTorusFourierEnergy
import Mettapedia.Analysis.UnitTorusFourierTranslation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Fourier-energy bounds for continuous periodic convolution -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusConvolutionEnergy

open MeasureTheory UnitAddTorus
variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def convolution (K f : T → ℂ) (x : T) : ℂ := ∫ h : T, K h * f (x - h)

theorem continuous_convolution (K f : T → ℂ) (hK : Continuous K) (hf : Continuous f) :
    Continuous (convolution K f) := by
  have hc : Continuous (fun p : T × T ↦ K p.2 * f (p.1 - p.2)) :=
    (hK.comp continuous_snd).mul (hf.comp (continuous_fst.sub continuous_snd))
  change Continuous (fun x : T ↦ ∫ h : T, K h * f (x - h))
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := (volume : Measure T)) hc isCompact_univ

theorem mFourier_add_argument (k : d → ℤ) (x y : T) :
    mFourier k (x + y) = mFourier k x * mFourier k y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [AddCircle.toCircle_add, Circle.coe_mul]

theorem mFourierCoeff_translate (f : T → ℂ) (k : d → ℤ) (h : T) :
    (∫ x : T, mFourier (-k) x * f (x - h)) = mFourier (-k) h * mFourierCoeff f k := by
  rw [← integral_add_right_eq_self (fun x : T ↦ mFourier (-k) x * f (x - h)) h]
  simp only [add_sub_cancel_right, mFourier_add_argument]
  simp_rw [mul_right_comm (mFourier (-k) _) (mFourier (-k) h)]
  rw [integral_mul_const]
  change mFourierCoeff f k * mFourier (-k) h = _
  ring

theorem mFourierCoeff_convolution (K f : T → ℂ) (hK : Continuous K) (hf : Continuous f)
    (k : d → ℤ) :
    mFourierCoeff (convolution K f) k = mFourierCoeff K k * mFourierCoeff f k := by
  have hc : Continuous (fun p : T × T ↦ mFourier (-k) p.1 * (K p.2 * f (p.1 - p.2))) :=
    ((mFourier (-k)).continuous.comp continuous_fst).mul
      ((hK.comp continuous_snd).mul (hf.comp (continuous_fst.sub continuous_snd)))
  have hi : Integrable (fun p : T × T ↦ mFourier (-k) p.1 * (K p.2 * f (p.1 - p.2)))
      ((volume : Measure T).prod volume) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : T, mFourier (-k) x * ∫ h : T, K h * f (x - h)) = _
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hi]
  have he (h : T) : (∫ x : T, mFourier (-k) x * (K h * f (x - h))) =
      (mFourier (-k) h * K h) * mFourierCoeff f k := by
    simp_rw [mul_left_comm (mFourier (-k) _) (K h)]
    rw [integral_const_mul, mFourierCoeff_translate]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  rfl

theorem integral_norm_sq_le_of_coeff_le (f g : T → ℂ) (hf : MemLp f 2) (hg : MemLp g 2)
    (h : ∀ k, ‖mFourierCoeff f k‖ ≤ ‖mFourierCoeff g k‖) :
    (∫ x : T, ‖f x‖ ^ 2) ≤ ∫ x : T, ‖g x‖ ^ 2 := by
  have hsf := UnitTorusFourierEnergy.hasSum_norm_mFourierCoeff_sq f hf
  have hsg := UnitTorusFourierEnergy.hasSum_norm_mFourierCoeff_sq g hg
  rw [← hsf.tsum_eq, ← hsg.tsum_eq]
  exact hsf.summable.tsum_le_tsum (fun k ↦ pow_le_pow_left₀ (norm_nonneg _) (h k) 2) hsg.summable

theorem integral_norm_convolution_sq_le (K f : T → ℂ) (hK : Continuous K) (hf : Continuous f)
    (hm : ∀ k, ‖mFourierCoeff K k‖ ≤ 1) :
    (∫ x : T, ‖convolution K f x‖ ^ 2) ≤ ∫ x : T, ‖f x‖ ^ 2 := by
  apply integral_norm_sq_le_of_coeff_le _ _
    ((continuous_convolution K f hK hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro k
  rw [mFourierCoeff_convolution K f hK hf k, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _)).trans_eq (one_mul _)

def realConvolution (K f : T → ℝ) (x : T) : ℝ := ∫ h : T, K h * f (x - h)

theorem ofReal_realConvolution (K f : T → ℝ) (x : T) :
    (realConvolution K f x : ℂ) =
      convolution (fun h ↦ (K h : ℂ)) (fun h ↦ (f h : ℂ)) x := by
  simp only [realConvolution, convolution, ← Complex.ofReal_mul, integral_complex_ofReal]

theorem continuous_realConvolution (K f : T → ℝ) (hK : Continuous K) (hf : Continuous f) :
    Continuous (realConvolution K f) := by
  have h := Complex.continuous_re.comp (continuous_convolution
    (fun x ↦ (K x : ℂ)) (fun x ↦ (f x : ℂ)) (Complex.continuous_ofReal.comp hK)
    (Complex.continuous_ofReal.comp hf))
  change Continuous (fun x ↦ (convolution (fun y ↦ (K y : ℂ)) (fun y ↦ (f y : ℂ)) x).re) at h
  simpa only [← ofReal_realConvolution, Complex.ofReal_re] using h

theorem integral_realConvolution_sq_le (K f : T → ℝ) (hK : Continuous K) (hf : Continuous f)
    (hm : ∀ k, ‖mFourierCoeff (fun x ↦ (K x : ℂ)) k‖ ≤ 1) :
    (∫ x : T, realConvolution K f x ^ 2) ≤ ∫ x : T, f x ^ 2 := by
  have h := integral_norm_convolution_sq_le (fun x ↦ (K x : ℂ)) (fun x ↦ (f x : ℂ)) (Complex.continuous_ofReal.comp hK)
    (Complex.continuous_ofReal.comp hf) hm
  simpa only [← ofReal_realConvolution, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- A signed pairing bound; no pointwise absolute value is imposed on the kernel. -/
theorem abs_integral_mul_realConvolution_le (K f g : T → ℝ)
    (hK : Continuous K) (hf : Continuous f) (hg : Continuous g)
    (hm : ∀ k, ‖mFourierCoeff (fun x ↦ (K x : ℂ)) k‖ ≤ 1) :
    |∫ x : T, g x * realConvolution K f x| ≤
      ((∫ x : T, g x ^ 2) + ∫ x : T, f x ^ 2) / 2 := by
  have hH := continuous_realConvolution K f hK hf
  have hi (v : T → ℝ) (hv : Continuous v) : Integrable v :=
    hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : T, |g x * realConvolution K f x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : T, (g x ^ 2 + realConvolution K f x ^ 2) / 2 := by
      apply integral_mono (hi _ (hg.mul hH).abs)
        (hi _ (((hg.pow 2).add (hH.pow 2)).div_const 2))
      intro x
      change |g x * realConvolution K f x| ≤ (g x ^ 2 + realConvolution K f x ^ 2) / 2
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (g x - realConvolution K f x),
        sq_nonneg (g x + realConvolution K f x)]
    _ = ((∫ x : T, g x ^ 2) + ∫ x : T, realConvolution K f x ^ 2) / 2 := by
      rw [integral_div, integral_add (hi _ (hg.pow 2)) (hi _ (hH.pow 2))]
    _ ≤ _ := by linarith [integral_realConvolution_sq_le K f hK hf hm]

end Mettapedia.Analysis.UnitTorusConvolutionEnergy
