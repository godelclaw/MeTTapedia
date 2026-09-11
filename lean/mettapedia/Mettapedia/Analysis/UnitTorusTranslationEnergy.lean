import Mettapedia.Analysis.UnitTorusFourierEnergy
import Mettapedia.Analysis.UnitTorusFourierTranslation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Translation energy on the unit torus

Finite Fourier gradient-energy bounds control the full spatial translation
error by Parseval. The displacement is the wrapped torus norm, not the norm
of an arbitrary representative. No absolute summability of Fourier
coefficients is required.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusTranslationEnergy

open scoped BigOperators Topology
open MeasureTheory UnitAddTorus
open Mettapedia.Analysis.UnitTorusFourierEnergy
open Mettapedia.Analysis.UnitTorusFourierTranslation

variable {d : Type*} [Fintype d]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_norm_preserving_lift (a : UnitAddTorus d) :
    ∃ r : d → ℝ, (fun j ↦ (r j : UnitAddCircle)) = a ∧ ‖r‖ = ‖a‖ := by
  let r : d → ℝ := fun j ↦ (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) (a j)).1
  have hr (j : d) : (r j : UnitAddCircle) = a j := AddCircle.coe_equivIoc
  have hn (j : d) : ‖r j‖ = ‖a j‖ := by
    have hj := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) (a j)).2
    have habs : |r j| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_one, abs_le]
      change -(1 / 2 : ℝ) < r j ∧ r j ≤ -(1 / 2 : ℝ) + 1 at hj
      constructor <;> linarith
    simpa only [hr, Real.norm_eq_abs] using
      ((AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr habs).symm
  refine ⟨r, funext hr, le_antisymm ?_ ?_⟩
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
      (fun j ↦ (hn j).trans_le (norm_le_pi_norm a j))
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg r)).mpr
      (fun j ↦ (hn j).symm.trans_le (norm_le_pi_norm r j))

theorem mFourier_lift (q : d → ℤ) (r : d → ℝ) :
    mFourier q (fun j ↦ (r j : UnitAddCircle)) =
      Complex.exp (Complex.I * ((2 * Real.pi * ∑ j, (q j : ℝ) * r j : ℝ) : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Complex.ofReal_intCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_mFourier_sub_one_sq_le (q : d → ℤ) (a : UnitAddTorus d) :
    ‖mFourier q a - 1‖ ^ 2 ≤
      (Fintype.card d : ℝ) * ‖a‖ ^ 2 * (2 * Real.pi) ^ 2 * ∑ j, (q j : ℝ) ^ 2 := by
  obtain ⟨r, hr, hnorm⟩ := exists_norm_preserving_lift a
  have hexp := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * ∑ j, (q j : ℝ) * r j)
  rw [← mFourier_lift q r, hr] at hexp
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hexp 2
  simp only [norm_mul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j ↦ (q j : ℝ)) r
  have hrbound : (∑ j, r j ^ 2) ≤ (Fintype.card d : ℝ) * ‖a‖ ^ 2 := by
    calc
      _ ≤ ∑ _j : d, ‖r‖ ^ 2 := Finset.sum_le_sum (fun j _ ↦ by
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm r j) 2)
      _ = _ := by simp [hnorm]
  calc
    _ ≤ (2 * Real.pi) ^ 2 * (∑ j, (q j : ℝ) * r j) ^ 2 := by
      simpa only [mul_pow] using hsq
    _ ≤ (2 * Real.pi) ^ 2 * ((∑ j, (q j : ℝ) ^ 2) * ∑ j, r j ^ 2) := by
      gcongr
    _ ≤ (2 * Real.pi) ^ 2 * ((∑ j, (q j : ℝ) ^ 2) *
        ((Fintype.card d : ℝ) * ‖a‖ ^ 2)) := by gcongr
    _ = _ := by ring

theorem mFourierCoeff_translate (f : UnitAddTorus d → ℂ) (a : UnitAddTorus d) (q : d → ℤ) :
    mFourierCoeff (fun x ↦ f (x + a)) q = mFourier q a * mFourierCoeff f q := by
  rw [mFourierCoeff, ← integral_sub_right_eq_self
    (fun x ↦ mFourier (-q) x • f (x + a)) a]
  simp only [sub_add_cancel, mFourier_sub, neg_neg, smul_eq_mul]
  simp_rw [mul_right_comm (mFourier (-q) _) (mFourier q a),
    mul_comm _ (mFourier q a)]
  rw [integral_const_mul]
  rfl

theorem mFourierCoeff_sub (f g : UnitAddTorus d → ℂ) (hf : Continuous f) (hg : Continuous g)
    (q : d → ℤ) : mFourierCoeff (fun x ↦ f x - g x) q =
      mFourierCoeff f q - mFourierCoeff g q := by
  simp only [mFourierCoeff, smul_eq_mul, mul_sub]
  exact integral_sub
    (((mFourier (-q)).continuous.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (((mFourier (-q)).continuous.mul hg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

/-- A uniform bound on finite Fourier gradient energies controls the full
translation error. The dimensional factor comes from the sup norm on the torus. -/
theorem integral_norm_translate_sub_sq_le (f : UnitAddTorus d → ℂ) (hf : Continuous f)
    (G : ℝ)
    (hG : ∀ P : Finset (d → ℤ), (2 * Real.pi) ^ 2 *
      (∑ q ∈ P, (∑ j, (q j : ℝ) ^ 2) * ‖mFourierCoeff f q‖ ^ 2) ≤ G)
    (a : UnitAddTorus d) :
    (∫ x, ‖f (x + a) - f x‖ ^ 2) ≤ (Fintype.card d : ℝ) * ‖a‖ ^ 2 * G := by
  have ha : Continuous (fun x ↦ f (x + a)) := hf.comp (continuous_id.add continuous_const)
  have hm : MemLp (fun x ↦ f (x + a) - f x) 2 :=
    (ha.sub hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := hasSum_norm_mFourierCoeff_sq _ hm
  apply le_of_tendsto' hs
  intro P
  simp_rw [mFourierCoeff_sub _ _ ha hf, mFourierCoeff_translate,
    ← sub_one_mul, norm_mul, mul_pow]
  calc
    _ ≤ ∑ q ∈ P, ((Fintype.card d : ℝ) * ‖a‖ ^ 2 * (2 * Real.pi) ^ 2 *
        ∑ j, (q j : ℝ) ^ 2) * ‖mFourierCoeff f q‖ ^ 2 :=
      Finset.sum_le_sum (fun q _ ↦ mul_le_mul_of_nonneg_right
        (norm_mFourier_sub_one_sq_le q a) (sq_nonneg _))
    _ = (Fintype.card d : ℝ) * ‖a‖ ^ 2 * ((2 * Real.pi) ^ 2 *
        ∑ q ∈ P, (∑ j, (q j : ℝ) ^ 2) * ‖mFourierCoeff f q‖ ^ 2) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hG P) (by positivity)

end Mettapedia.Analysis.UnitTorusTranslationEnergy
