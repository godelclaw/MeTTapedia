import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Two derivatives of an operator-valued quadratic form

The second derivative records both operator-motion terms and the vector
gradient square. Specializing the operator to an orthogonal projection
gives the local product rule needed to keep signed viscous dissipation.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology ContDiff RealInnerProductSpace

namespace Mettapedia.Analysis.OperatorQuadraticForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def value (P : H →L[ℝ] H) (w : H) : ℝ := ⟪w, P w⟫

def rate (P D : H →L[ℝ] H) (w v : H) : ℝ := 2 * ⟪P w, v⟫ + ⟪w, D w⟫

theorem hasDerivAt_value {P : ℝ → H →L[ℝ] H} {w : ℝ → H}
    {D : H →L[ℝ] H} {v : H} {t : ℝ}
    (hP : HasDerivAt P D t) (hw : HasDerivAt w v t)
    (hs : ∀ a b, ⟪P t a, b⟫ = ⟪a, P t b⟫) :
    HasDerivAt (fun τ ↦ value (P τ) (w τ)) (rate (P t) D (w t) v) t := by
  apply (hw.inner ℝ (hP.clm_apply hw)).congr_deriv
  simp only [inner_add_right, rate]
  rw [← hs (w t) v, real_inner_comm v (P t (w t))]
  ring

theorem isSymmetric_derivative {P : ℝ → H →L[ℝ] H} {D : H →L[ℝ] H} {t : ℝ}
    (hP : HasDerivAt P D t) (hs : ∀ᶠ τ in 𝓝 t, ∀ a b, ⟪P τ a, b⟫ = ⟪a, P τ b⟫) :
    ∀ a b, ⟪D a, b⟫ = ⟪a, D b⟫ := by
  intro u v
  have hl := (hasDerivAt_const t u).inner ℝ (hP.clm_apply (hasDerivAt_const t v))
  have hr := (hP.clm_apply (hasDerivAt_const t u)).inner ℝ (hasDerivAt_const t v)
  have he : (fun τ ↦ ⟪u, P τ v⟫) =ᶠ[𝓝 t] (fun τ ↦ ⟪P τ u, v⟫) :=
    hs.mono (fun τ hτ ↦ (hτ u v).symm)
  have h := (hl.congr_of_eventuallyEq he.symm).unique hr
  simpa only [map_zero, add_zero, inner_zero_left, inner_zero_right, zero_add] using h.symm

theorem hasDerivAt_rate {P D : ℝ → H →L[ℝ] H} {w v : ℝ → H}
    {L : H →L[ℝ] H} {z : H} {t : ℝ}
    (hP : HasDerivAt P (D t) t) (hD : HasDerivAt D L t)
    (hw : HasDerivAt w (v t) t) (hv : HasDerivAt v z t)
    (hsD : ∀ a b, ⟪D t a, b⟫ = ⟪a, D t b⟫) :
    HasDerivAt (fun τ ↦ rate (P τ) (D τ) (w τ) (v τ))
      (2 * ⟪P t (w t), z⟫ + 2 * ⟪v t, P t (v t)⟫ +
        4 * ⟪v t, D t (w t)⟫ + ⟪w t, L (w t)⟫) t := by
  have h := (((hP.clm_apply hw).inner ℝ hv).const_mul 2).add
    (hw.inner ℝ (hD.clm_apply hw))
  apply h.congr_deriv
  simp only [inner_add_left, inner_add_right]
  rw [← hsD (w t) (v t), real_inner_comm (D t (w t)) (v t), real_inner_comm (P t (v t)) (v t)]
  ring

theorem hasDerivAt_deriv_value {P : ℝ → H →L[ℝ] H} {w : ℝ → H} {t : ℝ}
    (hP : ContDiffAt ℝ 2 P t) (hw : ContDiffAt ℝ 2 w t)
    (hs : ∀ᶠ τ in 𝓝 t, ∀ a b, ⟪P τ a, b⟫ = ⟪a, P τ b⟫) :
    HasDerivAt (deriv (fun τ ↦ value (P τ) (w τ)))
      (2 * ⟪P t (w t), deriv (deriv w) t⟫ + 2 * ⟪deriv w t, P t (deriv w t)⟫ +
        4 * ⟪deriv w t, deriv P t (w t)⟫ + ⟪w t, deriv (deriv P) t (w t)⟫) t := by
  have hPd := (hP.differentiableAt (by norm_num)).hasDerivAt
  have hwd := (hw.differentiableAt (by norm_num)).hasDerivAt
  have hPdd := ((hP.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hwdd := ((hw.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  apply (hasDerivAt_rate hPd hPdd hwd hwdd (isSymmetric_derivative hPd hs)).congr_of_eventuallyEq
  filter_upwards [hP.eventually (by norm_num), hw.eventually (by norm_num), hs] with τ hPτ hwτ hsτ
  exact (hasDerivAt_value (hPτ.differentiableAt (by norm_num)).hasDerivAt
    (hwτ.differentiableAt (by norm_num)).hasDerivAt hsτ).deriv

theorem deriv_deriv_value {P : ℝ → H →L[ℝ] H} {w : ℝ → H} {t : ℝ}
    (hP : ContDiffAt ℝ 2 P t) (hw : ContDiffAt ℝ 2 w t)
    (hs : ∀ᶠ τ in 𝓝 t, ∀ a b, ⟪P τ a, b⟫ = ⟪a, P τ b⟫) :
    deriv (deriv (fun τ ↦ value (P τ) (w τ))) t =
      2 * ⟪P t (w t), deriv (deriv w) t⟫ + 2 * ⟪deriv w t, P t (deriv w t)⟫ +
        4 * ⟪deriv w t, deriv P t (w t)⟫ + ⟪w t, deriv (deriv P) t (w t)⟫ :=
  (hasDerivAt_deriv_value hP hw hs).deriv

end Mettapedia.Analysis.OperatorQuadraticForm
