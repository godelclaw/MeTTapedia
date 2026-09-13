import Mettapedia.Analysis.UnitTorusContinuousRate
import Mettapedia.Analysis.SolenoidalRadialFlux

/-! # A radial gradient paired with a second solenoidal periodic field -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SolenoidalRadialPairing

open MeasureTheory
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def flux (n : ℕ) (a b : R3) (j : Fin 3) : ℝ :=
  (‖a‖ ^ 2) ^ (n + 1) * b j / (2 * (n + 1 : ℕ))

def fluxRate (n : ℕ) (a b v z : R3) (j : Fin 3) : ℝ :=
  (‖a‖ ^ 2) ^ n * b j * ⟪a, v⟫ +
    (‖a‖ ^ 2) ^ (n + 1) * z j / (2 * (n + 1 : ℕ))

theorem hasDerivAt_flux (n : ℕ) {a b : ℝ → R3} {v z : R3} {t : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b z t) (j : Fin 3) :
    HasDerivAt (fun τ ↦ flux n (a τ) (b τ) j) (fluxRate n (a t) (b t) v z j) t := by
  have hbj : HasDerivAt (fun τ ↦ b τ j) (z j) t := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const t (EuclideanSpace.single j (1 : ℝ))).inner ℝ hb
  apply (((ha.norm_sq.fun_pow (n + 1)).mul hbj).div_const (2 * (n + 1 : ℕ))).congr_deriv
  simp only [fluxRate, Nat.add_sub_cancel]
  have hn : (2 : ℝ) * (n + 1 : ℕ) ≠ 0 := by positivity
  field_simp

theorem sum_fluxRate (n : ℕ) (a b : R3) (D E : Fin 3 → R3)
    (hE : ∑ j : Fin 3, E j j = 0) :
    (∑ j : Fin 3, fluxRate n a b (D j) (E j) j) =
      (‖a‖ ^ 2) ^ n * ∑ j : Fin 3, b j * ⟪a, D j⟫ := by
  simp only [fluxRate, Fin.sum_univ_three] at hE ⊢
  linear_combination ((‖a‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ))) * hE

theorem integral_radial_pairing_eq_zero (a b : T3 → R3) (D E : Fin 3 → T3 → R3)
    (s : Fin 3 → ℝ → T3) (ha : Continuous a) (hb : Continuous b)
    (hD : ∀ j, Continuous (D j)) (hE : ∀ j, Continuous (E j))
    (hs : ∀ j, Continuous (s j)) (hs0 : ∀ j, s j 0 = 0)
    (hda : ∀ j x h, HasDerivAt (fun t ↦ a (x + s j t)) (D j (x + s j h)) h)
    (hdb : ∀ j x h, HasDerivAt (fun t ↦ b (x + s j t)) (E j (x + s j h)) h)
    (hdiv : ∀ x, ∑ j : Fin 3, E j x j = 0) (n : ℕ) :
    (∫ x : T3, (‖a x‖ ^ 2) ^ n * ∑ j : Fin 3, b x j * ⟪a x, D j x⟫) = 0 := by
  have hf (j : Fin 3) : Continuous (fun x ↦ flux n (a x) (b x) j) :=
    (((ha.norm.pow 2).pow (n + 1)).mul ((PiLp.continuous_apply 2 _ j).comp hb)).div_const _
  have hr (j : Fin 3) : Continuous (fun x ↦ fluxRate n (a x) (b x) (D j x) (E j x) j) :=
    ((((ha.norm.pow 2).pow n).mul ((PiLp.continuous_apply 2 _ j).comp hb)).mul (ha.inner (hD j))).add
      ((((ha.norm.pow 2).pow (n + 1)).mul ((PiLp.continuous_apply 2 _ j).comp (hE j))).div_const _)
  have hi (j : Fin 3) : Integrable (fun x ↦ fluxRate n (a x) (b x) (D j x) (E j x) j) :=
    (hr j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz (j : Fin 3) : (∫ x : T3, fluxRate n (a x) (b x) (D j x) (E j x) j) = 0 :=
    UnitTorusContinuousRate.integral_rate_eq_zero _ _ (s j) (hf j) (hr j) (hs j) (hs0 j)
      (fun x h ↦ hasDerivAt_flux n (hda j x h) (hdb j x h) j)
  have h : (∫ x : T3, ∑ j : Fin 3, fluxRate n (a x) (b x) (D j x) (E j x) j) = 0 := by
    rw [integral_finsetSum _ (fun j _ ↦ hi j)]
    simp only [hz, Finset.sum_const_zero]
  simpa only [sum_fluxRate n _ _ _ _ (hdiv _)] using h

end Mettapedia.Analysis.SolenoidalRadialPairing
