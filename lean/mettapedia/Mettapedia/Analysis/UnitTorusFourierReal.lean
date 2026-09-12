import Mettapedia.Analysis.UnitTorusFourierTranslation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Real parts and reversal of integrable torus Fourier coefficients -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierReal

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate

variable {d : Type*} [Fintype d]
local notation "Td" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem integrable_coefficient_integrand (f : Td → ℂ) (hf : Integrable f) (k : d → ℤ) :
    Integrable (fun x : Td ↦ mFourier (-k) x * f x) :=
  hf.bdd_mul (mFourier (-k)).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ by
      simpa only [mFourier_norm] using (mFourier (-k)).norm_coe_le_norm x))

theorem mFourierCoeff_conj (f : Td → ℂ) (k : d → ℤ) :
    mFourierCoeff (fun x ↦ conj (f x)) k = conj (mFourierCoeff f (-k)) := by
  rw [mFourierCoeff, mFourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, mFourier_neg, neg_neg, starRingEnd_apply]

theorem mFourierCoeff_comp_neg (f : Td → ℂ) (k : d → ℤ) :
    mFourierCoeff (fun x ↦ f (-x)) k = mFourierCoeff f (-k) := by
  unfold mFourierCoeff
  rw [← integral_neg_eq_self (fun x : Td ↦ mFourier (-k) x • f (-x)) volume]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [mFourier]

theorem mFourierCoeff_realPart (f : Td → ℂ) (hf : Integrable f) (k : d → ℤ) :
    mFourierCoeff (fun x ↦ ((f x).re : ℂ)) k =
      (mFourierCoeff f k + conj (mFourierCoeff f (-k))) / 2 := by
  have he (x : Td) : ((f x).re : ℂ) = (f x + conj (f x)) / 2 :=
    Complex.re_eq_add_conj _
  have hfc : Integrable (fun x ↦ conj (f x)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf
  simp only [he, mFourierCoeff, smul_eq_mul, ← mul_div_assoc, mul_add]
  rw [integral_div, integral_add (integrable_coefficient_integrand f hf k)
    (integrable_coefficient_integrand _ hfc k)]
  change (mFourierCoeff f k + mFourierCoeff (fun x ↦ conj (f x)) k) / 2 = _
  rw [mFourierCoeff_conj]
  rfl

theorem mFourierCoeff_realPart_of_coefficients (f : Td → ℂ) (hf : Integrable f)
    (k : d → ℤ) (a : ℝ) (hk : mFourierCoeff f k = (a : ℂ))
    (hn : mFourierCoeff f (-k) = (a : ℂ)) :
    mFourierCoeff (fun x ↦ ((f x).re : ℂ)) k = (a : ℂ) := by
  rw [mFourierCoeff_realPart f hf k, hk, hn]
  simp

def realEvenPart (f : Td → ℂ) (x : Td) : ℝ := (1 / 2 : ℝ) * ((f x).re + (f (-x)).re)

theorem integrable_realEvenPart (f : Td → ℂ) (hf : Integrable f) :
    Integrable (realEvenPart f) :=
  (hf.re.add hf.comp_neg.re).const_mul _

theorem mFourierCoeff_realEvenPart_of_coefficients (f : Td → ℂ) (hf : Integrable f)
    (k : d → ℤ) (a : ℝ) (hk : mFourierCoeff f k = (a : ℂ))
    (hn : mFourierCoeff f (-k) = (a : ℂ)) :
    mFourierCoeff (fun x ↦ (realEvenPart f x : ℂ)) k = (a : ℂ) := by
  have hi : Integrable (fun x ↦ ((f x).re : ℂ)) := hf.re.ofReal
  have hin : Integrable (fun x ↦ ((f (-x)).re : ℂ)) := hi.comp_neg
  have hb := mFourierCoeff_realPart_of_coefficients f hf k a hk hn
  have hc := mFourierCoeff_comp_neg (fun x ↦ ((f x).re : ℂ)) k
  rw [mFourierCoeff_realPart_of_coefficients f hf (-k) a hn (by simpa only [neg_neg] using hk)] at hc
  unfold mFourierCoeff realEvenPart
  push_cast
  simp only [smul_eq_mul]
  simp_rw [mul_left_comm (mFourier (-k) _) (1 / 2 : ℂ)]
  rw [integral_const_mul]
  simp only [mul_add]
  rw [integral_add (integrable_coefficient_integrand _ hi k)
    (integrable_coefficient_integrand _ hin k)]
  change (1 / 2 : ℂ) * (mFourierCoeff (fun x ↦ ((f x).re : ℂ)) k +
    mFourierCoeff (fun x ↦ ((f (-x)).re : ℂ)) k) = _
  rw [hb, hc]
  ring

end Mettapedia.Analysis.UnitTorusFourierReal
