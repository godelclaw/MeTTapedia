import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalizedQuadraticEnergy

/-!
# Material motion of an orthogonal projector is off-diagonal

Differentiating a projector path gives a tangent identity. Adding its
transport commutator preserves that identity and self-adjointness. The
quadratic material-frame transfer therefore contains both coherent and
misaligned amplitudes, rather than an unrestricted full-energy term.

The operator norm of the material rate remains to be bounded by the actual
strain-frame dynamics. These identities do not supply that analytic bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialProjectorTangent

open scoped RealInnerProductSpace
open PancakeLocalizedQuadraticEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem derivative_projector_tangent (P : ℝ → H →L[ℝ] H) (Pdot : H →L[ℝ] H) (t : ℝ)
    (hd : HasDerivAt P Pdot t) (hp : ∀ tau, P tau * P tau = P tau) :
    Pdot * P t + P t * Pdot = Pdot := by
  have h := hd.mul hd
  change HasDerivAt (fun tau ↦ P tau * P tau) (Pdot * P t + P t * Pdot) t at h
  have he : (fun tau ↦ P tau * P tau) = P := funext hp
  rw [he] at h
  exact h.unique hd

theorem derivative_selfAdjoint (P : ℝ → H →L[ℝ] H) (Pdot : H →L[ℝ] H) (t : ℝ)
    (hd : HasDerivAt P Pdot t) (hs : ∀ tau, IsSelfAdjoint (P tau)) :
    IsSelfAdjoint Pdot := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hx := hd.clm_apply (hasDerivAt_const t x)
  have hy := hd.clm_apply (hasDerivAt_const t y)
  have hleft := hx.inner ℝ (hasDerivAt_const t y)
  have hright := (hasDerivAt_const t x).inner ℝ hy
  have he : (fun tau ↦ ⟪P tau x, y⟫) = (fun tau ↦ ⟪x, P tau y⟫) := by
    funext tau
    exact (hs tau).isSymmetric x y
  rw [he] at hleft
  simpa using hleft.unique hright

def materialProjectorRate (P Pdot B : H →L[ℝ] H) : H →L[ℝ] H :=
  Pdot + B * P - P * B

theorem materialProjectorRate_selfAdjoint (P Pdot B : H →L[ℝ] H)
    (hP : IsSelfAdjoint P) (hd : IsSelfAdjoint Pdot) (hB : B.adjoint = -B) :
    IsSelfAdjoint (materialProjectorRate P Pdot B) := by
  have hp' : star P = P := hP
  have hd' : star Pdot = Pdot := hd
  have hb' : star B = -B := hB
  change star (materialProjectorRate P Pdot B) = materialProjectorRate P Pdot B
  simp only [materialProjectorRate, star_sub, star_add, star_mul, hp', hd', hb']
  noncomm_ring

omit [CompleteSpace H] in
theorem materialProjectorRate_tangent (P Pdot B : H →L[ℝ] H)
    (hp : P * P = P) (hd : Pdot * P + P * Pdot = Pdot) :
    materialProjectorRate P Pdot B * P + P * materialProjectorRate P Pdot B =
      materialProjectorRate P Pdot B := by
  calc
    _ = (Pdot * P + P * Pdot) + (B * (P * P) - (P * P) * B) := by
      unfold materialProjectorRate
      noncomm_ring
    _ = _ := by rw [hp, hd]; unfold materialProjectorRate; abel

omit [CompleteSpace H] in
/-- Tangent motion has no diagonal coherent-to-coherent block. -/
theorem projector_tangent_diagonal_zero (P F : H →L[ℝ] H)
    (hp : P * P = P) (hf : F * P + P * F = F) (w : H) :
    P (F (P w)) = 0 := by
  have he := congrArg (fun A : H →L[ℝ] H ↦ A (P w)) hf
  have hpp := congrArg (fun A : H →L[ℝ] H ↦ A w) hp
  change P (P w) = P w at hpp
  change F (P (P w)) + P (F (P w)) = F (P w) at he
  rw [hpp] at he
  simpa using he

/-- The exact material-frame quadratic form is a coherent/misaligned
cross term. In particular it vanishes on either pure sector. -/
theorem projector_tangent_quadratic (P F : H →L[ℝ] H)
    (hp : P * P = P) (hP : IsSelfAdjoint P) (hF : IsSelfAdjoint F)
    (hf : F * P + P * F = F) (w : H) :
    ⟪w, F w⟫ = 2 * ⟪P w, F ((1 - P) w)⟫ := by
  have he := congrArg (fun A : H →L[ℝ] H ↦ A w) hf
  change F (P w) + P (F w) = F w at he
  have ha := hF.isSymmetric w (P w)
  have hb := hP.isSymmetric w (F w)
  have hc := hP.isSymmetric w (F (P w))
  change ⟪F w, P w⟫ = ⟪w, F (P w)⟫ at ha
  change ⟪P w, F w⟫ = ⟪w, P (F w)⟫ at hb
  change ⟪P w, F (P w)⟫ = ⟪w, P (F (P w))⟫ at hc
  rw [projector_tangent_diagonal_zero P F hp hf w, inner_zero_right] at hc
  have hi := congrArg (fun z : H ↦ ⟪w, z⟫) he
  rw [inner_add_right, ← ha, ← hb, real_inner_comm (P w) (F w)] at hi
  simp only [sub_apply, one_apply_eq_self, map_sub, inner_sub_right, hc, sub_zero]
  exact hi.symm.trans (by ring)

theorem projector_tangent_quadratic_bound (P F : H →L[ℝ] H)
    (hp : P * P = P) (hP : IsSelfAdjoint P) (hF : IsSelfAdjoint F)
    (hf : F * P + P * F = F) (w : H) :
    |⟪w, F w⟫| ≤ 2 * ‖F‖ * ‖P w‖ * ‖(1 - P) w‖ := by
  rw [projector_tangent_quadratic P F hp hP hF hf w, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (‖P w‖ * ‖F ((1 - P) w)‖) := by gcongr; exact abs_real_inner_le_norm _ _
    _ ≤ 2 * (‖P w‖ * (‖F‖ * ‖(1 - P) w‖)) := by gcongr; exact F.le_opNorm _
    _ = _ := by ring

theorem material_projector_quadratic_bound
    (P : ℝ → H →L[ℝ] H) (Pdot B : H →L[ℝ] H) (t : ℝ) (w : H)
    (hd : HasDerivAt P Pdot t) (hp : ∀ tau, P tau * P tau = P tau)
    (hs : ∀ tau, IsSelfAdjoint (P tau)) (hB : B.adjoint = -B) :
    |⟪w, materialProjectorRate (P t) Pdot B w⟫| ≤
      2 * ‖materialProjectorRate (P t) Pdot B‖ * ‖P t w‖ * ‖(1 - P t) w‖ := by
  exact projector_tangent_quadratic_bound (P t) _ (hp t) (hs t)
    (materialProjectorRate_selfAdjoint _ _ _ (hs t) (derivative_selfAdjoint P Pdot t hd hs) hB)
    (materialProjectorRate_tangent _ _ _ (hp t) (derivative_projector_tangent P Pdot t hd hp)) w

omit [CompleteSpace H] in
theorem materialMotionRate_projector_part (C Cdot P Pdot B : H →L[ℝ] H) (w : H) :
    materialMotionRate C Cdot P Pdot B w -
      2 * ⟪P (C w), Cdot w + B (C w) - C (B w)⟫ =
        ⟪C w, materialProjectorRate P Pdot B (C w)⟫ := by
  simp [materialMotionRate, materialProjectorRate]

/-- Frame transfer can be paid with misalignment damping and an explicit
coherent cost. Integrability of the squared material rate is not inferred. -/
theorem projector_tangent_quadratic_young (P F : H →L[ℝ] H)
    (hp : P * P = P) (hP : IsSelfAdjoint P) (hF : IsSelfAdjoint F)
    (hf : F * P + P * F = F) (w : H) (rho : ℝ) (hrho : 0 < rho) :
    |⟪w, F w⟫| ≤ rho * ‖(1 - P) w‖ ^ 2 + ‖F‖ ^ 2 / rho * ‖P w‖ ^ 2 := by
  apply (projector_tangent_quadratic_bound P F hp hP hF hf w).trans
  calc
    _ ≤ (rho ^ 2 * ‖(1 - P) w‖ ^ 2 + (‖F‖ * ‖P w‖) ^ 2) / rho := by
      apply (le_div_iff₀ hrho).mpr
      nlinarith [sq_nonneg (‖F‖ * ‖P w‖ - rho * ‖(1 - P) w‖)]
    _ = _ := by field_simp

theorem material_projector_motion_budget
    (C Cdot : H →L[ℝ] H) (P : ℝ → H →L[ℝ] H) (Pdot B : H →L[ℝ] H)
    (t : ℝ) (w : H) (rho : ℝ) (hrho : 0 < rho)
    (hd : HasDerivAt P Pdot t) (hp : ∀ tau, P tau * P tau = P tau)
    (hs : ∀ tau, IsSelfAdjoint (P tau)) (hB : B.adjoint = -B) :
    |materialMotionRate C Cdot (P t) Pdot B w -
      2 * ⟪P t (C w), Cdot w + B (C w) - C (B w)⟫| ≤
        rho * ‖(1 - P t) (C w)‖ ^ 2 +
          ‖materialProjectorRate (P t) Pdot B‖ ^ 2 / rho * ‖P t (C w)‖ ^ 2 := by
  rw [materialMotionRate_projector_part]
  exact projector_tangent_quadratic_young (P t) _ (hp t) (hs t)
    (materialProjectorRate_selfAdjoint _ _ _ (hs t) (derivative_selfAdjoint P Pdot t hd hs) hB)
    (materialProjectorRate_tangent _ _ _ (hp t) (derivative_projector_tangent P Pdot t hd hp)) (C w) rho hrho

end Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialProjectorTangent
