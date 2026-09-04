import Mettapedia.FluidDynamics.NavierStokes.OneFormFrameCalculus

/-!
# One-form frame calculus: regression checks

Theorem-level checks that the one-form Lie-derivative calculus and the
frame-Laplacian identity of `OneFormFrameCalculus` evaluate correctly on
concrete one-forms:

* constant one-forms (all second-order terms vanish; the frame sum is `0`);
* the quadratic one-form `y ↦ ⟪u, y⟫² • w`, whose second directional
  derivative is the nonzero constant `(2 ⟪u, e⟫²) • w` — this exercises the
  genuinely second-order content of the pair-collapse identity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace OneFormFrameCalculusRegression

open scoped RealInnerProductSpace BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Lie derivative along the zero vector field vanishes. -/
theorem lieOneForm_zero_left (μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) :
    lieOneForm (fun _ => 0) μ x = 0 := by
  simp [lieOneForm]
  ext b
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- Second directional derivatives of a constant one-form vanish. -/
theorem dirDeriv2_const (e c x : EuclideanSpace ℝ ι) :
    dirDeriv2 e (fun _ => c) x = 0 := by
  simp [dirDeriv2]

/-- On a constant one-form, the Lie derivative along a profile mode reduces to
the pure gradient-direction term `(dφ ⟪k,x⟫ * ⟪e, c⟫) • k`. -/
theorem lieOneForm_profileMode_const {φ dφ : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (dφ t) t) (k e c x : EuclideanSpace ℝ ι) :
    lieOneForm (profileMode φ k e) (fun _ => c) x =
      (dφ ⟪k, x⟫ * ⟪e, c⟫) • k := by
  rw [lieOneForm_profileMode_apply hφ]
  simp

/-- The cosine/sine pair collapse evaluates to `0` on constant one-forms. -/
theorem lieOneForm_sq_cos_add_sin_const (a : ℝ) {k e : EuclideanSpace ℝ ι}
    (horth : ⟪k, e⟫ = 0) (c x : EuclideanSpace ℝ ι) :
    lieOneForm (profileMode (fun t => a * Real.cos t) k e)
        (lieOneForm (profileMode (fun t => a * Real.cos t) k e) (fun _ => c)) x +
      lieOneForm (profileMode (fun t => a * Real.sin t) k e)
        (lieOneForm (profileMode (fun t => a * Real.sin t) k e) (fun _ => c)) x =
      0 := by
  rw [lieOneForm_sq_cos_add_sin a horth contDiff_const x, dirDeriv2_const,
    smul_zero]

omit [DecidableEq ι] in
/-- The quadratic one-form `y ↦ ⟪u, y⟫² • w` is `C²`. -/
theorem contDiff_quadraticOneForm (u w : EuclideanSpace ℝ ι) :
    ContDiff ℝ 2 (fun y : EuclideanSpace ℝ ι => (⟪u, y⟫ ^ 2) • w) :=
  ((innerSL ℝ u).contDiff.pow 2).smul contDiff_const

omit [DecidableEq ι] in
/-- First derivative of the quadratic one-form in direction `e`. -/
theorem fderiv_quadraticOneForm (u w e x : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => (⟪u, y⟫ ^ 2) • w) x e =
      (2 * ⟪u, x⟫ * ⟪u, e⟫) • w := by
  have hs := (hasFDerivAt_inner_left u x).pow 2
  have h := hs.smul_const w
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  match_scalars
  ring

omit [DecidableEq ι] in
/-- Second directional derivative of the quadratic one-form: the nonzero
constant `(2 ⟪u, e⟫²) • w`. -/
theorem dirDeriv2_quadraticOneForm (u w e x : EuclideanSpace ℝ ι) :
    dirDeriv2 e (fun y : EuclideanSpace ℝ ι => (⟪u, y⟫ ^ 2) • w) x =
      (2 * ⟪u, e⟫ ^ 2) • w := by
  unfold dirDeriv2
  have hfun : (fun y : EuclideanSpace ℝ ι =>
      fderiv ℝ (fun z : EuclideanSpace ℝ ι => (⟪u, z⟫ ^ 2) • w) y e) =
      fun y : EuclideanSpace ℝ ι => (2 * ⟪u, y⟫ * ⟪u, e⟫) • w := by
    funext y
    exact fderiv_quadraticOneForm u w e y
  rw [hfun]
  have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ ι => 2 * ⟪u, y⟫)
      ((2 : ℝ) • innerSL ℝ u) x := (hasFDerivAt_inner_left u x).const_mul 2
  have hs : HasFDerivAt (fun y : EuclideanSpace ℝ ι => 2 * ⟪u, y⟫ * ⟪u, e⟫)
      (⟪u, e⟫ • ((2 : ℝ) • innerSL ℝ u)) x := h2.mul_const ⟪u, e⟫
  have h : HasFDerivAt
      (fun y : EuclideanSpace ℝ ι => (2 * ⟪u, y⟫ * ⟪u, e⟫) • w)
      ((⟪u, e⟫ • ((2 : ℝ) • innerSL ℝ u)).smulRight w) x := hs.smul_const w
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  match_scalars
  ring

/-- Pair collapse on the quadratic one-form: a genuinely nonzero second-order
output `a² • (2 ⟪u, e⟫²) • w`. -/
theorem lieOneForm_sq_cos_add_sin_quadratic (a : ℝ) {k e : EuclideanSpace ℝ ι}
    (horth : ⟪k, e⟫ = 0) (u w x : EuclideanSpace ℝ ι) :
    lieOneForm (profileMode (fun t => a * Real.cos t) k e)
        (lieOneForm (profileMode (fun t => a * Real.cos t) k e)
          (fun y => (⟪u, y⟫ ^ 2) • w)) x +
      lieOneForm (profileMode (fun t => a * Real.sin t) k e)
        (lieOneForm (profileMode (fun t => a * Real.sin t) k e)
          (fun y => (⟪u, y⟫ ^ 2) • w)) x =
      a ^ 2 • (2 * ⟪u, e⟫ ^ 2) • w := by
  rw [lieOneForm_sq_cos_add_sin a horth (contDiff_quadraticOneForm u w) x,
    dirDeriv2_quadraticOneForm]

/-- The normalized dimension-3 frame identity evaluates to `0` on constant
one-forms. -/
theorem frameLaplacian_oneForm_normalized_const (c : EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ j, ∑ p ∈ Finset.univ.erase j,
        (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
            (fun _ => c)) x +
        lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
            (fun _ => c)) x) =
      0 := by
  rw [frameLaplacian_oneForm_normalized contDiff_const x]
  simp [coordLaplacian, dirDeriv2_const]

end OneFormFrameCalculusRegression
end NavierStokes
end FluidDynamics
end Mettapedia
