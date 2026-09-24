import Mettapedia.Analysis.LongitudinalHelicityBudget

/-! # Radial amplitude fluxes of divergence-free periodic fields -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SolenoidalRadialFlux

open MeasureTheory UnitTorusWeakDerivative LongitudinalHelicityBudget
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance radialFluxCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance radialFluxCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance radialFluxCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def flux (n : ℕ) (a : R3) (j : Fin 3) : ℝ :=
  (‖a‖ ^ 2) ^ (n + 1) * a j / (2 * (n + 1 : ℕ))

def fluxRate (n : ℕ) (a v : R3) (j : Fin 3) : ℝ :=
  (‖a‖ ^ 2) ^ n * a j * ⟪a, v⟫ + (‖a‖ ^ 2) ^ (n + 1) * v j / (2 * (n + 1 : ℕ))

theorem hasDerivAt_flux (n : ℕ) {a : ℝ → R3} {v : R3} {t : ℝ}
    (ha : HasDerivAt a v t) (j : Fin 3) :
    HasDerivAt (fun τ ↦ flux n (a τ) j) (fluxRate n (a t) v j) t := by
  have haj : HasDerivAt (fun τ ↦ a τ j) (v j) t := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const t (EuclideanSpace.single j (1 : ℝ))).inner ℝ ha
  apply (((ha.norm_sq.fun_pow (n + 1)).mul haj).div_const (2 * (n + 1 : ℕ))).congr_deriv
  simp only [fluxRate, Nat.add_sub_cancel]
  have hn : (2 : ℝ) * (n + 1 : ℕ) ≠ 0 := by positivity
  field_simp

theorem contDiff_flux (n : ℕ) (j : Fin 3) : ContDiff ℝ 1 (fun a : R3 ↦ flux n a j) := by
  have hj : ContDiff ℝ 1 (fun a : R3 ↦ a j) := by
    simpa [EuclideanSpace.inner_single_left] using
      (contDiff_const (c := EuclideanSpace.single j (1 : ℝ))).inner ℝ contDiff_id
  exact (((contDiff_id.norm_sq ℝ).pow (n + 1)).mul hj).div_const _

theorem sum_fluxRate (n : ℕ) (a : R3) (D : Fin 3 → R3)
    (hdiv : ∑ j : Fin 3, D j j = 0) :
    (∑ j : Fin 3, fluxRate n a (D j) j) =
      (‖a‖ ^ 2) ^ n * longitudinalAmplitude a D := by
  simp only [fluxRate, longitudinalAmplitude, Fin.sum_univ_three] at hdiv ⊢
  linear_combination ((‖a‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ))) * hdiv

theorem integral_radial_longitudinal_eq_zero (a : T3 → R3) (D : Fin 3 → T3 → R3)
    (ha : Continuous a)
    (haL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ a (torusPoint r)))
    (hda : ∀ j x, HasDerivAt (fun h ↦ a (x + coordinateShift j h)) (D j x) 0)
    (hdiv : ∀ x, ∑ j : Fin 3, D j x j = 0) (n : ℕ) :
    (∫ x : T3, (‖a x‖ ^ 2) ^ n * longitudinalAmplitude (a x) (fun j ↦ D j x)) = 0 := by
  have hz (j : Fin 3) :
      Integrable (fun x : T3 ↦ fluxRate n (a x) (D j x) j) ∧
      (∫ x : T3, fluxRate n (a x) (D j x) j) = 0 := by
    have hd : shiftRate (fun x ↦ flux n (a x) j) (coordinateShift j) =
        fun x ↦ fluxRate n (a x) (D j x) j := by
      funext x
      simpa only [shiftRate, coordinateShift_zero, add_zero] using
        (hasDerivAt_flux n (hda j x) j).deriv
    simpa only [hd] using integral_coordinateRate_zero (fun x ↦ flux n (a x) j) j
      ((contDiff_flux n j).continuous.comp ha)
      ((contDiff_flux n j).locallyLipschitz.comp haL)
  have hs : (∫ x : T3, ∑ j : Fin 3, fluxRate n (a x) (D j x) j) = 0 := by
    rw [integral_finsetSum _ (fun j _ ↦ (hz j).1)]
    simp only [(hz _).2, Finset.sum_const_zero]
  simpa only [sum_fluxRate n _ _ (hdiv _)] using hs

/-- A spatially varying multiplier leaves its derivative along the field.
The derivative of the multiplier is the actual translation derivative; no
independent gradient or vanishing transport condition is assumed. -/
theorem integral_mul_radial_longitudinal_eq (a : T3 → R3) (D : Fin 3 → T3 → R3)
    (ha : Continuous a)
    (haL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ a (torusPoint r)))
    (hda : ∀ j x, HasDerivAt (fun h ↦ a (x + coordinateShift j h)) (D j x) 0)
    (hdiv : ∀ x, ∑ j : Fin 3, D j x j = 0)
    (ρ : T3 → ℝ) (hρ : Continuous ρ)
    (hρL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ ρ (torusPoint r))) (n : ℕ) :
    (∫ x : T3, ρ x * ((‖a x‖ ^ 2) ^ n * longitudinalAmplitude (a x) (fun j ↦ D j x))) =
      -(∫ x : T3, (‖a x‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ)) *
        (∑ j : Fin 3, a x j * shiftRate ρ (coordinateShift j) x)) := by
  have hd (j : Fin 3) : shiftRate (fun x ↦ flux n (a x) j) (coordinateShift j) =
      fun x ↦ fluxRate n (a x) (D j x) j := by
    funext x
    simpa only [shiftRate, coordinateShift_zero, add_zero] using
      (hasDerivAt_flux n (hda j x) j).deriv
  have hc (j : Fin 3) := (contDiff_flux n j).continuous.comp ha
  have hL (j : Fin 3) := (contDiff_flux n j).locallyLipschitz.comp haL
  have hI (j : Fin 3) : Integrable (fun x ↦ fluxRate n (a x) (D j x) j * ρ x) := by
    have h := (integral_coordinateRate_zero (fun x ↦ flux n (a x) j) j (hc j) (hL j)).1
    rw [hd] at h
    exact integrable_mul_continuous _ ρ h hρ
  have hJ (j : Fin 3) :
      Integrable (fun x ↦ flux n (a x) j * shiftRate ρ (coordinateShift j) x) := by
    simpa only [Function.comp_apply, mul_comm] using integrable_mul_continuous _ _
      (integral_coordinateRate_zero ρ j hρ hρL).1 (hc j)
  have he (j : Fin 3) :
      (∫ x : T3, fluxRate n (a x) (D j x) j * ρ x) =
        -(∫ x : T3, flux n (a x) j * shiftRate ρ (coordinateShift j) x) := by
    simpa only [hd] using integral_coordinateRate_mul
      (fun x ↦ flux n (a x) j) ρ j (hc j) hρ (hL j) hρL
  have hsum := congrArg (fun f : Fin 3 → ℝ ↦ ∑ j, f j) (funext he)
  rw [← integral_finsetSum _ (fun j _ ↦ hI j), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun j _ ↦ hJ j)] at hsum
  have hleft (x : T3) :
      (∑ j : Fin 3, fluxRate n (a x) (D j x) j * ρ x) =
        ρ x * ((‖a x‖ ^ 2) ^ n * longitudinalAmplitude (a x) (fun j ↦ D j x)) := by
    rw [← Finset.sum_mul, sum_fluxRate n _ _ (hdiv x), mul_comm]
  have hright (x : T3) :
      (∑ j : Fin 3, flux n (a x) j * shiftRate ρ (coordinateShift j) x) =
        (‖a x‖ ^ 2) ^ (n + 1) / (2 * (n + 1 : ℕ)) *
          (∑ j : Fin 3, a x j * shiftRate ρ (coordinateShift j) x) := by
    simp only [flux, Fin.sum_univ_three]
    ring
  simpa only [hleft, hright] using hsum

end Mettapedia.Analysis.SolenoidalRadialFlux
