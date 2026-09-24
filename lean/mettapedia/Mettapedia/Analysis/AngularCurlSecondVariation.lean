import Mettapedia.Analysis.AngularCurlEvolution
import Mathlib.Tactic.Module

/-!
# Second variation of the angular curl density

The quadratic variation in a value and its first jet is separated from
the linear contribution of their accelerations. This is the curvature
term in a diffusion chain rule; it is not assigned a favorable sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def angularJetSecondVariation (a : R3) (D : Fin 3 → R3)
    (da : R3) (dD : Fin 3 → R3) (j : Fin 3) : R3 :=
  (2 * ‖da‖ ^ 2) • D j + (4 * ⟪a, da⟫) • dD j -
    (2 * ⟪da, dD j⟫) • a - (2 * (⟪da, D j⟫ + ⟪a, dD j⟫)) • da

def angularCurlSecondVariation (a : R3) (D : Fin 3 → R3)
    (da : R3) (dD : Fin 3 → R3) : R3 :=
  curlJet (angularJetSecondVariation a D da dD)

def angularCurlDensitySecondVariation (a : R3) (D : Fin 3 → R3)
    (da : R3) (dD : Fin 3 → R3) : ℝ :=
  2 * ‖da‖ ^ 2 * ‖angularCurl a D‖ ^ 2 +
    8 * ⟪a, da⟫ * ⟪angularCurl a D, angularCurlRate a D da dD⟫ +
    2 * ‖a‖ ^ 2 * ‖angularCurlRate a D da dD‖ ^ 2 +
    2 * ‖a‖ ^ 2 * ⟪angularCurl a D, angularCurlSecondVariation a D da dD⟫

theorem hasDerivAt_angularJetRate {a da : ℝ → R3} {D dD : ℝ → Fin 3 → R3}
    {dda : R3} {ddD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a (da t) t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD t j) t)
    (hea : HasDerivAt da dda t) (heD : ∀ j, HasDerivAt (fun τ ↦ dD τ j) (ddD j) t)
    (j : Fin 3) :
    HasDerivAt (fun τ ↦ angularJetRate (a τ) (D τ) (da τ) (dD τ) j)
      (angularJetSecondVariation (a t) (D t) (da t) (dD t) j +
        angularJetRate (a t) (D t) dda ddD j) t := by
  have h := ((((ha.inner ℝ hea).const_mul 2).smul (hD j)).add
    (ha.norm_sq.smul (heD j))).sub
      (((hea.inner ℝ (hD j)).add (ha.inner ℝ (heD j))).smul ha) |>.sub
        ((ha.inner ℝ (hD j)).smul hea)
  apply h.congr_deriv
  simp only [angularJetRate, angularJetSecondVariation, real_inner_self_eq_norm_sq, Pi.add_apply]
  module

theorem hasDerivAt_angularCurlRate {a da : ℝ → R3} {D dD : ℝ → Fin 3 → R3}
    {dda : R3} {ddD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a (da t) t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD t j) t)
    (hea : HasDerivAt da dda t) (heD : ∀ j, HasDerivAt (fun τ ↦ dD τ j) (ddD j) t) :
    HasDerivAt (fun τ ↦ angularCurlRate (a τ) (D τ) (da τ) (dD τ))
      (angularCurlSecondVariation (a t) (D t) (da t) (dD t) +
        angularCurlRate (a t) (D t) dda ddD) t := by
  have h := hasDerivAt_curlJet (hasDerivAt_angularJetRate ha hD hea heD)
  apply h.congr_deriv
  ext i
  fin_cases i <;> simp [angularCurlSecondVariation, angularCurlRate, curlJet] <;> ring

theorem hasDerivAt_angularCurlDensityRate {a da : ℝ → R3} {D dD : ℝ → Fin 3 → R3}
    {dda : R3} {ddD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a (da t) t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD t j) t)
    (hea : HasDerivAt da dda t) (heD : ∀ j, HasDerivAt (fun τ ↦ dD τ j) (ddD j) t) :
    HasDerivAt (fun τ ↦ angularCurlDensityRate (a τ) (D τ) (da τ) (dD τ))
      (angularCurlDensitySecondVariation (a t) (D t) (da t) (dD t) +
        angularCurlDensityRate (a t) (D t) dda ddD) t := by
  have hH := hasDerivAt_angularCurl ha hD
  have heH := hasDerivAt_angularCurlRate ha hD hea heD
  have h := (((ha.inner ℝ hea).const_mul 2).mul hH.norm_sq).add
    ((ha.norm_sq.const_mul 2).mul (hH.inner ℝ heH))
  apply h.congr_deriv
  simp only [angularCurlDensitySecondVariation, angularCurlDensityRate,
    real_inner_self_eq_norm_sq, inner_add_right]
  ring

theorem continuous_angularCurlSecondVariation {X : Type*} [TopologicalSpace X]
    (a da : X → R3) (D dD : Fin 3 → X → R3)
    (ha : Continuous a) (hea : Continuous da) (hD : ∀ j, Continuous (D j))
    (heD : ∀ j, Continuous (dD j)) :
    Continuous (fun x ↦ angularCurlSecondVariation (a x) (fun j ↦ D j x)
      (da x) (fun j ↦ dD j x)) := by
  have hJ (j : Fin 3) : Continuous (fun x ↦ angularJetSecondVariation (a x) (fun k ↦ D k x)
      (da x) (fun k ↦ dD k x) j) :=
    ((((hea.norm.pow 2).const_mul 2).smul (hD j)).add
      (((ha.inner (𝕜 := ℝ) hea).const_mul 4).smul (heD j))).sub
        (((hea.inner (𝕜 := ℝ) (heD j)).const_mul 2).smul ha) |>.sub
          ((((hea.inner (𝕜 := ℝ) (hD j)).add (ha.inner (𝕜 := ℝ) (heD j))).const_mul 2).smul hea)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact ((PiLp.continuous_apply 2 _ _).comp (hJ _)).sub
      ((PiLp.continuous_apply 2 _ _).comp (hJ _))

theorem continuous_angularCurlDensitySecondVariation {X : Type*} [TopologicalSpace X]
    (a da : X → R3) (D dD : Fin 3 → X → R3)
    (ha : Continuous a) (hea : Continuous da) (hD : ∀ j, Continuous (D j))
    (heD : ∀ j, Continuous (dD j)) :
    Continuous (fun x ↦ angularCurlDensitySecondVariation (a x) (fun j ↦ D j x)
      (da x) (fun j ↦ dD j x)) := by
  have hH := continuous_angularCurl a D ha hD
  have hdH := continuous_angularCurlRate a da D dD ha hea hD heD
  have hddH := continuous_angularCurlSecondVariation a da D dD ha hea hD heD
  exact ((((hea.norm.pow 2).const_mul 2).mul (hH.norm.pow 2)).add
    (((ha.inner hea).const_mul 8).mul (hH.inner hdH))).add
      (((ha.norm.pow 2).const_mul 2).mul (hdH.norm.pow 2)) |>.add
        (((ha.norm.pow 2).const_mul 2).mul (hH.inner hddH))

end Mettapedia.Analysis.AngularCurlDecomposition
