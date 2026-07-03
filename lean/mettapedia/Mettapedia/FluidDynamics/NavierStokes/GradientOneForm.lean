import Mettapedia.FluidDynamics.NavierStokes.OneFormFrameCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Gradient one-forms and Lie-derivative identities

The gradient one-form of a scalar potential, in coordinates
(`gradField W x = Σ_a (∂_a W x) e_a`), together with the two Lie-derivative
identities that drive momentum-transport computations for incompressible
flow:

* `lieOneForm_gradField` (Cartan's formula for exact one-forms):
  `L_u (dW) = d ⟪u, ∇W⟫` — the Lie derivative of an exact one-form is
  exact, by symmetry of the second derivative of the potential.
* `lieOneForm_self`:
  `L_u u♭ = (u·∇)u + d(½ ⟪u, u⟫)` — transport of the velocity's own
  one-form splits into the convective derivative plus an exact form.

Together these show that, modulo exact one-forms, the Lie derivative of a
momentum one-form `u♭ + dW` along `u` is the convective derivative
`(u·∇)u` — the mechanism by which pressure absorbs the exact parts in the
Weber-transform representation of incompressible flow (H. Weber, J. Reine
Angew. Math. **68** (1868), 286–292; P. Constantin, Comm. Math. Phys.
**216** (2001), 663–686; P. Constantin, G. Iyer, Comm. Pure Appl. Math.
**61** (2008), 330–345).

Also provides the additivity lemmas for `lieOneForm`, `dirDeriv2`,
`coordLaplacian`, and `gradField` needed to assemble momentum-transport
computations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section CoordinateHelpers

omit [Fintype ι] in
/-- Scaling a coordinate unit vector. -/
lemma smul_single_one (b : ι) (c : ℝ) :
    c • (EuclideanSpace.single b 1 : EuclideanSpace ℝ ι) =
      EuclideanSpace.single b c := by
  ext d
  simp

/-- A vector is the sum of its coordinate components. -/
lemma sum_single_coords (v : EuclideanSpace ℝ ι) :
    ∑ b, EuclideanSpace.single b (v b) = v := by
  simpa using sum_single_mul_apply (ι := ι) 1 v

end CoordinateHelpers

/-- Gradient one-form of a scalar potential, in coordinates. -/
def gradField (W : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  ∑ a, EuclideanSpace.single a (fderiv ℝ W x (EuclideanSpace.single a 1))

/-- Componentwise evaluation of the gradient one-form. -/
theorem gradField_apply (W : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (a : ι) :
    gradField W x a = fderiv ℝ W x (EuclideanSpace.single a 1) := by
  unfold gradField
  simp

/-- The gradient one-form of a `C^(n+1)` potential is `C^n`. -/
theorem contDiff_gradField {n : ℕ} {W : EuclideanSpace ℝ ι → ℝ}
    (hW : ContDiff ℝ (n + 1) W) : ContDiff ℝ n (gradField W) := by
  unfold gradField
  apply ContDiff.sum
  intro a _
  have hfd : ContDiff ℝ n (fderiv ℝ W) := hW.fderiv_right (by exact_mod_cast le_rfl)
  have happ : ContDiff ℝ n (fun y => fderiv ℝ W y (EuclideanSpace.single a 1)) :=
    hfd.clm_apply contDiff_const
  have hsingle : ContDiff ℝ n
      (fun c : ℝ => (EuclideanSpace.single a c : EuclideanSpace ℝ ι)) := by
    have hfun : (fun c : ℝ => (EuclideanSpace.single a c : EuclideanSpace ℝ ι)) =
        fun c : ℝ => c • (EuclideanSpace.single a 1 : EuclideanSpace ℝ ι) := by
      funext c
      rw [smul_single_one]
    rw [hfun]
    exact contDiff_id.smul contDiff_const
  exact hsingle.comp happ

section Additivity

variable {E μ₁ μ₂ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
variable {x : EuclideanSpace ℝ ι}

/-- The Lie derivative is additive in the one-form argument. -/
theorem lieOneForm_add_right (h₁ : DifferentiableAt ℝ μ₁ x)
    (h₂ : DifferentiableAt ℝ μ₂ x) :
    lieOneForm E (fun y => μ₁ y + μ₂ y) x =
      lieOneForm E μ₁ x + lieOneForm E μ₂ x := by
  unfold lieOneForm
  rw [fderiv_fun_add h₁ h₂]
  have hsplit : ∀ a : ι,
      (EuclideanSpace.single a
        ⟪fderiv ℝ E x (EuclideanSpace.single a 1), (fun y => μ₁ y + μ₂ y) x⟫ :
          EuclideanSpace ℝ ι) =
      EuclideanSpace.single a
          ⟪fderiv ℝ E x (EuclideanSpace.single a 1), μ₁ x⟫ +
        EuclideanSpace.single a
          ⟪fderiv ℝ E x (EuclideanSpace.single a 1), μ₂ x⟫ := by
    intro a
    have hval : ⟪fderiv ℝ E x (EuclideanSpace.single a 1),
        (fun y => μ₁ y + μ₂ y) x⟫ =
        ⟪fderiv ℝ E x (EuclideanSpace.single a 1), μ₁ x⟫ +
          ⟪fderiv ℝ E x (EuclideanSpace.single a 1), μ₂ x⟫ :=
      inner_add_right _ _ _
    rw [hval]
    ext b
    by_cases hba : b = a <;> simp [hba]
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib,
    add_apply]

  abel

omit [DecidableEq ι] in
/-- Second directional derivatives are additive (for `C²` summands). -/
theorem dirDeriv2_add (e : EuclideanSpace ℝ ι) (h₁ : ContDiff ℝ 2 μ₁)
    (h₂ : ContDiff ℝ 2 μ₂) :
    dirDeriv2 e (fun y => μ₁ y + μ₂ y) x =
      dirDeriv2 e μ₁ x + dirDeriv2 e μ₂ x := by
  unfold dirDeriv2
  have hfun : (fun y => fderiv ℝ (fun z => μ₁ z + μ₂ z) y e) =
      fun y => fderiv ℝ μ₁ y e + fderiv ℝ μ₂ y e := by
    funext y
    rw [fderiv_fun_add ((h₁.differentiable (by norm_num)).differentiableAt)
      ((h₂.differentiable (by norm_num)).differentiableAt)]
    rfl
  rw [hfun]
  have hw : ∀ (μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι), ContDiff ℝ 2 μ →
      DifferentiableAt ℝ (fun y => fderiv ℝ μ y e) x := by
    intro μ hμ
    have hfd : ContDiff ℝ 1 (fderiv ℝ μ) := hμ.fderiv_right (by norm_num)
    exact ((hfd.differentiable (by norm_num)).differentiableAt).clm_apply
      (differentiableAt_const e)
  rw [fderiv_fun_add (hw μ₁ h₁) (hw μ₂ h₂)]
  rfl

/-- The coordinate Laplacian is additive (for `C²` summands). -/
theorem coordLaplacian_add (h₁ : ContDiff ℝ 2 μ₁) (h₂ : ContDiff ℝ 2 μ₂) :
    coordLaplacian (fun y => μ₁ y + μ₂ y) x =
      coordLaplacian μ₁ x + coordLaplacian μ₂ x := by
  unfold coordLaplacian
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => dirDeriv2_add _ h₁ h₂

end Additivity

section GradientAlgebra

variable {V₁ V₂ : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}

/-- Gradient one-forms are additive. -/
theorem gradField_add (h₁ : DifferentiableAt ℝ V₁ x)
    (h₂ : DifferentiableAt ℝ V₂ x) :
    gradField (fun y => V₁ y + V₂ y) x = gradField V₁ x + gradField V₂ x := by
  unfold gradField
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_fun_add h₁ h₂]
  ext b
  by_cases hba : b = a <;> simp [hba]

/-- Gradient one-forms respect scalar multiples. -/
theorem gradField_const_mul (c : ℝ) (h₁ : DifferentiableAt ℝ V₁ x) :
    gradField (fun y => c * V₁ y) x = c • gradField V₁ x := by
  unfold gradField
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_const_mul h₁ c]
  ext b
  simp

/-- Gradient one-forms respect subtraction. -/
theorem gradField_sub (h₁ : DifferentiableAt ℝ V₁ x)
    (h₂ : DifferentiableAt ℝ V₂ x) :
    gradField (fun y => V₁ y - V₂ y) x = gradField V₁ x - gradField V₂ x := by
  unfold gradField
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_fun_sub h₁ h₂]
  ext b
  by_cases hba : b = a <;> simp [hba]

section ScalarProfile

variable {φ dφ : ℝ → ℝ}

/-- Gradient of a scalar profile of a linear phase:
`∇(φ ⟪K, ·⟫) = φ'(⟪K, x⟫) • K`. -/
theorem gradField_scalarProfile (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (K x : EuclideanSpace ℝ ι) :
    gradField (fun y => φ ⟪K, y⟫) x = dφ ⟪K, x⟫ • K := by
  have hs : HasFDerivAt (fun y : EuclideanSpace ℝ ι => φ ⟪K, y⟫)
      (dφ ⟪K, x⟫ • innerSL ℝ K) x :=
    (hφ ⟪K, x⟫).comp_hasFDerivAt x (hasFDerivAt_inner_left K x)
  unfold gradField
  rw [hs.fderiv]
  have hterm : ∀ a : ι,
      (EuclideanSpace.single a
        ((dφ ⟪K, x⟫ • innerSL ℝ K) (EuclideanSpace.single a 1)) :
          EuclideanSpace ℝ ι) =
      EuclideanSpace.single a (dφ ⟪K, x⟫ * K a) := by
    intro a
    congr 1
    rw [smul_apply, innerSL_apply_apply, smul_eq_mul]
    congr 1
    simp [EuclideanSpace.inner_single_right]
  rw [Finset.sum_congr rfl fun a _ => hterm a, sum_single_mul_apply]

end ScalarProfile

end GradientAlgebra

section LieIdentities

variable {u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
variable {W : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}

/-- Derivative data for the gradient one-form of a `C²` potential. -/
theorem hasFDerivAt_gradField (hW : ContDiff ℝ 2 W) (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (gradField W)
      (∑ b, (fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x).smulRight
        (EuclideanSpace.single b 1)) x := by
  have hterm : ∀ b : ι, HasFDerivAt
      (fun y => (EuclideanSpace.single b
        (fderiv ℝ W y (EuclideanSpace.single b 1)) : EuclideanSpace ℝ ι))
      ((fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x).smulRight
        (EuclideanSpace.single b 1)) x := by
    intro b
    have hcb : DifferentiableAt ℝ
        (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x := by
      have hfd : ContDiff ℝ 1 (fderiv ℝ W) := hW.fderiv_right (by norm_num)
      exact ((hfd.differentiable (by norm_num)).differentiableAt).clm_apply
        (differentiableAt_const _)
    have h := (hcb.hasFDerivAt).smul_const
      (EuclideanSpace.single b 1 : EuclideanSpace ℝ ι)
    have hfun : (fun y => fderiv ℝ W y (EuclideanSpace.single b 1) •
        (EuclideanSpace.single b 1 : EuclideanSpace ℝ ι)) =
        fun y => (EuclideanSpace.single b
          (fderiv ℝ W y (EuclideanSpace.single b 1)) : EuclideanSpace ℝ ι) := by
      funext y
      rw [smul_single_one]
    rw [← hfun]
    exact h
  have hsum := HasFDerivAt.sum (fun b (_ : b ∈ Finset.univ) => hterm b)
  have hfun2 : (∑ b, fun y => (EuclideanSpace.single b
      (fderiv ℝ W y (EuclideanSpace.single b 1)) : EuclideanSpace ℝ ι)) =
      gradField W := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun2] at hsum
  exact hsum

/-- Pairing a vector against the coordinate representation of a covector
recovers the covector's value. -/
lemma inner_sum_single_clm (L : EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ ι) :
    ⟪v, ∑ b, (EuclideanSpace.single b (L (EuclideanSpace.single b 1)) :
      EuclideanSpace ℝ ι)⟫ = L v := by
  have hexp : ⟪v, ∑ b, (EuclideanSpace.single b (L (EuclideanSpace.single b 1)) :
      EuclideanSpace ℝ ι)⟫ =
      ∑ b, v b * L (EuclideanSpace.single b 1) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hcomp : (∑ c, (EuclideanSpace.single c (L (EuclideanSpace.single c 1)) :
        EuclideanSpace ℝ ι)) b = L (EuclideanSpace.single b 1) := by
      simp
    rw [hcomp]
    simp [RCLike.inner_apply, mul_comm]
  rw [hexp]
  calc ∑ b, v b * L (EuclideanSpace.single b 1)
      = ∑ b, L (EuclideanSpace.single b (v b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← smul_single_one b (v b), map_smul, smul_eq_mul]
    _ = L (∑ b, EuclideanSpace.single b (v b)) := (map_sum L _ _).symm
    _ = L v := by rw [sum_single_coords]

/-- **Cartan's formula for exact one-forms** (coordinate form): the Lie
derivative of the gradient one-form of a `C²` potential along a vector field
`u` (differentiable at `x`) is again a gradient one-form,
`L_u (dW) = d ⟪u, ∇W⟫`.  Uses symmetry of the second derivative of `W`. -/
theorem lieOneForm_gradField (hu : DifferentiableAt ℝ u x)
    (hW : ContDiff ℝ 2 W) :
    lieOneForm u (gradField W) x =
      gradField (fun y => ⟪u y, gradField W y⟫) x := by
  have hgradW := hasFDerivAt_gradField (ι := ι) hW x
  have hsymm : IsSymmSndFDerivAt ℝ W x :=
    (hW.contDiffAt).isSymmSndFDerivAt (by norm_num)
  have hWdiff : DifferentiableAt ℝ (fderiv ℝ W) x := by
    have : ContDiff ℝ 1 (fderiv ℝ W) := hW.fderiv_right (by norm_num)
    exact (this.differentiable (by norm_num)).differentiableAt
  have hcb : ∀ (b : ι) (v : EuclideanSpace ℝ ι),
      fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x v =
        fderiv ℝ (fderiv ℝ W) x v (EuclideanSpace.single b 1) := by
    intro b v
    rw [fderiv_clm_apply hWdiff (differentiableAt_const _)]
    simp
  -- The derivative of the gradient field: components are second derivatives.
  have hDgrad : ∀ (v : EuclideanSpace ℝ ι) (a : ι),
      fderiv ℝ (gradField W) x v a =
        fderiv ℝ (fderiv ℝ W) x v (EuclideanSpace.single a 1) := by
    intro v a
    rw [hgradW.fderiv]
    have happ : (∑ b, (fderiv ℝ
        (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x).smulRight
          (EuclideanSpace.single b 1)) v =
        ∑ b, (EuclideanSpace.single b
          (fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x v) :
            EuclideanSpace ℝ ι) := by
      rw [sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ContinuousLinearMap.smulRight_apply, smul_single_one]
    rw [happ]
    have hval : (∑ b, (EuclideanSpace.single b
        (fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single b 1)) x v) :
          EuclideanSpace ℝ ι)) a =
        fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single a 1)) x v := by
      simp
    rw [hval, hcb]
  -- Assemble, componentwise.
  ext a
  -- Left side: second derivative in the pair (u x, e_a) plus the
  -- transpose-gradient term.
  have hLHS : lieOneForm u (gradField W) x a =
      fderiv ℝ (fderiv ℝ W) x (u x) (EuclideanSpace.single a 1) +
        ⟪fderiv ℝ u x (EuclideanSpace.single a 1), gradField W x⟫ := by
    unfold lieOneForm
    have hcomp : (fderiv ℝ (gradField W) x (u x) +
        ∑ b, EuclideanSpace.single b
          ⟪fderiv ℝ u x (EuclideanSpace.single b 1), gradField W x⟫ :
            EuclideanSpace ℝ ι) a =
        fderiv ℝ (gradField W) x (u x) a +
          ⟪fderiv ℝ u x (EuclideanSpace.single a 1), gradField W x⟫ := by
      simp
    rw [hcomp, hDgrad]
  -- Right side: derivative of the pairing.
  have hinner := (hu.hasFDerivAt).inner ℝ (hgradW.differentiableAt.hasFDerivAt)
  have hRHS : gradField (fun y => ⟪u y, gradField W y⟫) x a =
      ⟪u x, fderiv ℝ (gradField W) x (EuclideanSpace.single a 1)⟫ +
        ⟪fderiv ℝ u x (EuclideanSpace.single a 1), gradField W x⟫ := by
    rw [gradField_apply, hinner.fderiv]
    rw [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply]
    simp
  rw [hLHS, hRHS]
  -- The second-derivative terms agree by symmetry of `D²W`.
  have hsecond : ⟪u x, fderiv ℝ (gradField W) x (EuclideanSpace.single a 1)⟫ =
      fderiv ℝ (fderiv ℝ W) x (u x) (EuclideanSpace.single a 1) := by
    have hvec : fderiv ℝ (gradField W) x (EuclideanSpace.single a 1) =
        ∑ b, (EuclideanSpace.single b
          ((fderiv ℝ (fderiv ℝ W) x (EuclideanSpace.single b 1))
            (EuclideanSpace.single a 1)) : EuclideanSpace ℝ ι) := by
      ext c
      rw [hDgrad]
      have : (∑ b, (EuclideanSpace.single b
          ((fderiv ℝ (fderiv ℝ W) x (EuclideanSpace.single b 1))
            (EuclideanSpace.single a 1)) : EuclideanSpace ℝ ι)) c =
          (fderiv ℝ (fderiv ℝ W) x (EuclideanSpace.single c 1))
            (EuclideanSpace.single a 1) := by
        simp
      rw [this]
      exact hsymm.eq _ _
    rw [hvec]
    have hpair := inner_sum_single_clm
      ((fderiv ℝ (fderiv ℝ W) x).flip (EuclideanSpace.single a 1)) (u x)
    have hflip : ∀ w : EuclideanSpace ℝ ι,
        ((fderiv ℝ (fderiv ℝ W) x).flip (EuclideanSpace.single a 1)) w =
          fderiv ℝ (fderiv ℝ W) x w (EuclideanSpace.single a 1) := fun w => rfl
    calc ⟪u x, ∑ b, (EuclideanSpace.single b
          ((fderiv ℝ (fderiv ℝ W) x (EuclideanSpace.single b 1))
            (EuclideanSpace.single a 1)) : EuclideanSpace ℝ ι)⟫
        = ((fderiv ℝ (fderiv ℝ W) x).flip (EuclideanSpace.single a 1)) (u x) := by
          rw [← hpair]
          rfl
      _ = fderiv ℝ (fderiv ℝ W) x (u x) (EuclideanSpace.single a 1) := hflip _
  rw [hsecond]

/-- **Self-transport identity**: the Lie derivative of the velocity's own
(flat) one-form along itself is the convective derivative plus an exact
one-form, `L_u u♭ = (u·∇)u + d(½ ⟪u, u⟫)`. -/
theorem lieOneForm_self (hu : DifferentiableAt ℝ u x) :
    lieOneForm u u x =
      fderiv ℝ u x (u x) +
        gradField (fun y => (1 / 2 : ℝ) * ⟪u y, u y⟫) x := by
  unfold lieOneForm
  congr 1
  have hinner := (hu.hasFDerivAt).inner ℝ (hu.hasFDerivAt)
  have hhalf := hinner.const_mul (1 / 2 : ℝ)
  ext a
  have hlhs : (∑ b, EuclideanSpace.single b
      ⟪fderiv ℝ u x (EuclideanSpace.single b 1), u x⟫ :
        EuclideanSpace ℝ ι) a =
      ⟪fderiv ℝ u x (EuclideanSpace.single a 1), u x⟫ := by
    simp
  rw [hlhs, gradField_apply, hhalf.fderiv]
  rw [smul_apply, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply]
  simp only [ContinuousLinearMap.prod_apply, smul_eq_mul]
  rw [real_inner_comm (u x) (fderiv ℝ u x (EuclideanSpace.single a 1))]
  ring

end LieIdentities

end NavierStokes
end FluidDynamics
end Mettapedia
