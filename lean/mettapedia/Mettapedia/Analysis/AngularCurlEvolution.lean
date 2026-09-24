import Mettapedia.Analysis.AngularCurlDecomposition
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# First variation of the polynomial angular curl

The amplitude subtraction is differentiated as well as the original jet.
Every term, including the changing squared-amplitude weight, is retained.
These are exact derivatives for differentiable inputs, without a sign bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def angularJetRate (a : R3) (D : Fin 3 → R3) (da : R3) (dD : Fin 3 → R3) (j : Fin 3) : R3 :=
  (2 * ⟪a, da⟫) • D j + ‖a‖ ^ 2 • dD j -
    (⟪da, D j⟫ + ⟪a, dD j⟫) • a - ⟪a, D j⟫ • da

def angularCurlRate (a : R3) (D : Fin 3 → R3) (da : R3) (dD : Fin 3 → R3) : R3 :=
  curlJet (angularJetRate a D da dD)

def angularCurlDensityRate (a : R3) (D : Fin 3 → R3) (da : R3) (dD : Fin 3 → R3) : ℝ :=
  2 * ⟪a, da⟫ * ‖angularCurl a D‖ ^ 2 +
    2 * ‖a‖ ^ 2 * ⟪angularCurl a D, angularCurlRate a D da dD⟫

theorem hasDerivAt_angularJet {a : ℝ → R3} {D : ℝ → Fin 3 → R3}
    {da : R3} {dD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a da t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD j) t) (j : Fin 3) :
    HasDerivAt (fun τ ↦ angularJet (a τ) (D τ) j) (angularJetRate (a t) (D t) da dD j) t := by
  have h := (ha.norm_sq.smul (hD j)).sub ((ha.inner ℝ (hD j)).smul ha)
  apply h.congr_deriv
  simp only [angularJetRate]
  abel

theorem hasDerivAt_curlJet {D : ℝ → Fin 3 → R3} {dD : Fin 3 → R3} {t : ℝ}
    (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD j) t) :
    HasDerivAt (fun τ ↦ curlJet (D τ)) (curlJet dD) t := by
  have hc (j i : Fin 3) := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t (hD j)
  have hcoord : HasDerivAt (fun τ ↦ WithLp.ofLp (curlJet (D τ))) (WithLp.ofLp (curlJet dD)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hc 1 2).sub (hc 2 1)
    · exact (hc 2 0).sub (hc 0 2)
    · exact (hc 0 1).sub (hc 1 0)
  let L := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv
  exact L.hasFDerivAt.comp_hasDerivAt t hcoord

theorem hasDerivAt_angularCurl {a : ℝ → R3} {D : ℝ → Fin 3 → R3}
    {da : R3} {dD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a da t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD j) t) :
    HasDerivAt (fun τ ↦ angularCurl (a τ) (D τ)) (angularCurlRate (a t) (D t) da dD) t :=
  hasDerivAt_curlJet (hasDerivAt_angularJet ha hD)

theorem hasDerivAt_angularCurlDensity {a : ℝ → R3} {D : ℝ → Fin 3 → R3}
    {da : R3} {dD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a da t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD j) t) :
    HasDerivAt (fun τ ↦ angularCurlDensity (a τ) (D τ))
      (angularCurlDensityRate (a t) (D t) da dD) t := by
  have h := ha.norm_sq.mul ((hasDerivAt_angularCurl ha hD).norm_sq)
  apply h.congr_deriv
  simp only [angularCurlDensityRate]
  ring

/-- Cubic homogeneity of the angular curl under common amplitude motion. -/
theorem angularCurlRate_proportional (a : R3) (D : Fin 3 → R3) (c : ℝ) :
    angularCurlRate a D (c • a) (fun j ↦ c • D j) = (3 * c) • angularCurl a D := by
  ext i
  fin_cases i <;> simp [angularCurlRate, angularJetRate, angularCurl, angularJet, curlJet,
    real_inner_smul_left, real_inner_smul_right] <;> ring

/-- Removing radial derivatives does not remove overall amplitude growth. -/
theorem angularCurlDensityRate_proportional (a : R3) (D : Fin 3 → R3) (c : ℝ) :
    angularCurlDensityRate a D (c • a) (fun j ↦ c • D j) = 8 * c * angularCurlDensity a D := by
  rw [angularCurlDensityRate, angularCurlRate_proportional]
  simp only [angularCurlDensity, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem angularCurlDensityRate_eq_zero_of_angularCurl_eq_zero
    (a : R3) (D : Fin 3 → R3) (da : R3) (dD : Fin 3 → R3) (h : angularCurl a D = 0) :
    angularCurlDensityRate a D da dD = 0 := by
  simp [angularCurlDensityRate, h]

theorem angularCurlRate_add (a : R3) (D : Fin 3 → R3)
    (da ea : R3) (dD eD : Fin 3 → R3) :
    angularCurlRate a D (da + ea) (fun j ↦ dD j + eD j) =
      angularCurlRate a D da dD + angularCurlRate a D ea eD := by
  ext i
  fin_cases i <;> simp [angularCurlRate, angularJetRate, curlJet,
    inner_add_left, inner_add_right, add_smul, smul_add] <;> ring

theorem angularCurlRate_smul (a : R3) (D : Fin 3 → R3)
    (da : R3) (dD : Fin 3 → R3) (c : ℝ) :
    angularCurlRate a D (c • da) (fun j ↦ c • dD j) = c • angularCurlRate a D da dD := by
  ext i
  fin_cases i <;> simp [angularCurlRate, angularJetRate, curlJet,
    real_inner_smul_left, real_inner_smul_right] <;> ring

theorem angularCurlDensityRate_add (a : R3) (D : Fin 3 → R3)
    (da ea : R3) (dD eD : Fin 3 → R3) :
    angularCurlDensityRate a D (da + ea) (fun j ↦ dD j + eD j) =
      angularCurlDensityRate a D da dD + angularCurlDensityRate a D ea eD := by
  simp only [angularCurlDensityRate, angularCurlRate_add, inner_add_right]
  ring

theorem angularCurlDensityRate_smul (a : R3) (D : Fin 3 → R3)
    (da : R3) (dD : Fin 3 → R3) (c : ℝ) :
    angularCurlDensityRate a D (c • da) (fun j ↦ c • dD j) = c * angularCurlDensityRate a D da dD := by
  simp only [angularCurlDensityRate, angularCurlRate_smul, real_inner_smul_right]
  ring

theorem continuous_angularCurlRate {X : Type*} [TopologicalSpace X]
    (a da : X → R3) (D dD : Fin 3 → X → R3)
    (ha : Continuous a) (hea : Continuous da) (hD : ∀ j, Continuous (D j))
    (heD : ∀ j, Continuous (dD j)) :
    Continuous (fun x ↦ angularCurlRate (a x) (fun j ↦ D j x) (da x) (fun j ↦ dD j x)) := by
  have hJ (j : Fin 3) : Continuous (fun x ↦ angularJetRate (a x) (fun k ↦ D k x)
      (da x) (fun k ↦ dD k x) j) :=
    ((((ha.inner (𝕜 := ℝ) hea).const_mul 2).smul (hD j)).add ((ha.norm.pow 2).smul (heD j))).sub
      (((hea.inner (𝕜 := ℝ) (hD j)).add (ha.inner (𝕜 := ℝ) (heD j))).smul ha) |>.sub
        ((ha.inner (𝕜 := ℝ) (hD j)).smul hea)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact ((PiLp.continuous_apply 2 _ _).comp (hJ _)).sub
      ((PiLp.continuous_apply 2 _ _).comp (hJ _))

theorem continuous_angularCurlDensityRate {X : Type*} [TopologicalSpace X]
    (a da : X → R3) (D dD : Fin 3 → X → R3)
    (ha : Continuous a) (hea : Continuous da) (hD : ∀ j, Continuous (D j))
    (heD : ∀ j, Continuous (dD j)) :
    Continuous (fun x ↦ angularCurlDensityRate (a x) (fun j ↦ D j x) (da x) (fun j ↦ dD j x)) := by
  have hH := continuous_angularCurl a D ha hD
  have hdH := continuous_angularCurlRate a da D dD ha hea hD heD
  exact (((ha.inner hea).const_mul 2).mul (hH.norm.pow 2)).add
    (((ha.norm.pow 2).const_mul 2).mul (hH.inner hdH))

end Mettapedia.Analysis.AngularCurlDecomposition
