import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Tactic.Ring

/-!
# Signed evolution of an eighth-order kernel correlation

Both vorticity endpoints and the moving operator are differentiated. These
polynomial identities include zero vorticity and impose no sign on the rate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OcticKernelCorrelation

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "Op" => E →L[ℝ] E

def density (H : Op) (a b : E) : ℝ := ‖a‖ ^ 2 * ‖b‖ ^ 4 * ⟪a, H a⟫

def endpointRate (H : Op) (a b v w : E) : ℝ :=
  2 * ⟪a, v⟫ * ‖b‖ ^ 4 * ⟪a, H a⟫ +
    4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 * ⟪b, w⟫ * ⟪a, H a⟫ +
    ‖a‖ ^ 2 * ‖b‖ ^ 4 * (⟪v, H a⟫ + ⟪a, H v⟫)

def materialRate (H Hdot : Op) (a b v w : E) : ℝ :=
  endpointRate H a b v w + density Hdot a b

theorem hasDerivAt_density {a b : ℝ → E} {H : ℝ → Op} {v w : E} {Hdot : Op} {t : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) (hH : HasDerivAt H Hdot t) :
    HasDerivAt (fun τ ↦ density (H τ) (a τ) (b τ))
      (materialRate (H t) Hdot (a t) (b t) v w) t := by
  have h := (ha.norm_sq.mul (hb.norm_sq.fun_pow 2)).mul (ha.inner ℝ (hH.clm_apply ha))
  simp only [← pow_mul] at h
  apply h.congr_deriv
  simp only [materialRate, endpointRate, density, inner_add_right, Nat.cast_ofNat, Pi.mul_apply]
  ring

theorem materialRate_add_smul_endpoint (H Hdot : Op) (a b v w f g : E) (c : ℝ) :
    materialRate H Hdot a b (v + c • f) (w + c • g) =
      materialRate H Hdot a b v w + c * endpointRate H a b f g := by
  simp only [materialRate, endpointRate, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, map_add, map_smul]
  ring

theorem continuous_density {X : Type*} [TopologicalSpace X] {H : X → Op} {a b : X → E}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x ↦ density (H x) (a x) (b x)) :=
  ((ha.norm.pow 2).mul (hb.norm.pow 4)).mul (ha.inner (hH.clm_apply ha))

def sourceForm (H : Op) (a : E) : ℝ := ‖a‖ ^ 2 * ⟪a, H a⟫

def sourceRate (H : Op) (a v : E) : ℝ :=
  2 * ⟪a, v⟫ * ⟪a, H a⟫ + ‖a‖ ^ 2 * (⟪v, H a⟫ + ⟪a, H v⟫)

def sourceCurvature (H : Op) (a v : E) : ℝ :=
  2 * ‖v‖ ^ 2 * ⟪a, H a⟫ +
    4 * ⟪a, v⟫ * (⟪v, H a⟫ + ⟪a, H v⟫) + 2 * ‖a‖ ^ 2 * ⟪v, H v⟫

def amplitudeRate (b w : E) : ℝ := 4 * ‖b‖ ^ 2 * ⟪b, w⟫

def amplitudeCurvature (b w : E) : ℝ := 8 * ⟪b, w⟫ ^ 2 + 4 * ‖b‖ ^ 2 * ‖w‖ ^ 2

def pureCurvature (H : Op) (a b v w : E) : ℝ :=
  sourceCurvature H a v * ‖b‖ ^ 4 + sourceForm H a * amplitudeCurvature b w

def mixedCurvature (H : Op) (a b v w : E) : ℝ := 2 * sourceRate H a v * amplitudeRate b w

theorem endpointRate_eq_factored (H : Op) (a b v w : E) :
    endpointRate H a b v w = sourceRate H a v * ‖b‖ ^ 4 + sourceForm H a * amplitudeRate b w := by
  unfold endpointRate sourceRate sourceForm amplitudeRate
  ring

theorem hasDerivAt_sourceForm (H : Op) {a : ℝ → E} {v : E} {t : ℝ}
    (ha : HasDerivAt a v t) :
    HasDerivAt (fun τ ↦ sourceForm H (a τ)) (sourceRate H (a t) v) t := by
  have h := ha.norm_sq.mul (ha.inner ℝ (H.hasFDerivAt.comp_hasDerivAt t ha))
  apply h.congr_deriv
  simp only [sourceRate, Function.comp_def]
  ring

theorem hasDerivAt_sourceRate (H : Op) {a v : ℝ → E} {z : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hv : HasDerivAt v z t) :
    HasDerivAt (fun τ ↦ sourceRate H (a τ) (v τ))
      (sourceRate H (a t) z + sourceCurvature H (a t) (v t)) t := by
  have hHa := H.hasFDerivAt.comp_hasDerivAt t ha
  have hHv := H.hasFDerivAt.comp_hasDerivAt t hv
  have h₁ := ((ha.inner ℝ hv).const_mul 2).mul (ha.inner ℝ hHa)
  have h₂ := ha.norm_sq.mul ((hv.inner ℝ hHa).add (ha.inner ℝ hHv))
  apply (h₁.add h₂).congr_deriv
  simp only [sourceRate, sourceCurvature, Function.comp_def, Pi.add_apply,
    real_inner_self_eq_norm_sq]
  ring

theorem hasDerivAt_amplitudeRate {b w : ℝ → E} {z : E} {t : ℝ}
    (hb : HasDerivAt b (w t) t) (hw : HasDerivAt w z t) :
    HasDerivAt (fun τ ↦ amplitudeRate (b τ) (w τ))
      (amplitudeRate (b t) z + amplitudeCurvature (b t) (w t)) t := by
  apply (((hb.norm_sq).const_mul 4).mul (hb.inner ℝ hw)).congr_deriv
  simp only [amplitudeRate, amplitudeCurvature, real_inner_self_eq_norm_sq]
  ring

/-- The exact common-translation second variation, with pure and mixed terms separate. -/
theorem hasDerivAt_endpointRate (H : Op) {a b v w : ℝ → E} {z q : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (w t) t)
    (hv : HasDerivAt v z t) (hw : HasDerivAt w q t) :
    HasDerivAt (fun τ ↦ endpointRate H (a τ) (b τ) (v τ) (w τ))
      (endpointRate H (a t) (b t) z q + pureCurvature H (a t) (b t) (v t) (w t) +
        mixedCurvature H (a t) (b t) (v t) (w t)) t := by
  have h := ((hasDerivAt_sourceRate H ha hv).mul (hb.norm_sq.fun_pow 2)).add
    ((hasDerivAt_sourceForm H ha).mul (hasDerivAt_amplitudeRate hb hw))
  simp only [← pow_mul] at h
  simp_rw [endpointRate_eq_factored]
  apply h.congr_deriv
  simp only [pureCurvature, mixedCurvature, amplitudeRate, Nat.cast_ofNat]
  ring

end Mettapedia.Analysis.OcticKernelCorrelation
