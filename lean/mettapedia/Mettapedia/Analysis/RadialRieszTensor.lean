import Mettapedia.Analysis.RadialHessian
import Mettapedia.Analysis.RadialRieszHessian
import Mettapedia.Analysis.PeriodicRieszOperatorFourier
import Mettapedia.Analysis.ScalarTripleProductEvolution

/-!
# Radial tensor structure of the constructed Riesz kernel

The real kernel entries are assembled before any periodization. Their
scalar-plus-radial decomposition follows from the constructed potential.
The signed stretching pair therefore retains the scalar triple product
with the actual Euclidean displacement. A periodic sum must retain each
lifted displacement separately.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszRegularization

open SchwartzMap LineDeriv
open scoped SchwartzMap ContDiff RealInnerProductSpace

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def realPotential (N : ℕ) : 𝓢(Rd, ℝ) := (potential N).postcompCLM Complex.reCLM

theorem realPotential_isometry (N : ℕ) (A : Rd ≃ₗᵢ[ℝ] Rd) (x : Rd) :
    realPotential N (A x) = realPotential N x := by
  change (potential N (A x)).re = (potential N x).re
  rw [potential_isometry]

theorem lineDerivOp_postcomp_re (f : 𝓢(Rd, ℂ)) (v : Rd) :
    (∂_{v} (f.postcompCLM Complex.reCLM) : 𝓢(Rd, ℝ)) =
      (∂_{v} f : 𝓢(Rd, ℂ)).postcompCLM Complex.reCLM := by
  ext x
  have h := (Complex.reCLM.hasFDerivAt.comp x (f.hasFDerivAt x)).fderiv
  change (fderiv ℝ (fun y ↦ (f y).re) x) v = (fderiv ℝ f x v).re
  change fderiv ℝ (fun y ↦ (f y).re) x = _ at h
  rw [h]
  rfl

theorem secondFDeriv_realPotential (N : ℕ) (i j : Fin d) (x : Rd) :
    fderiv ℝ (fun y ↦ fderiv ℝ (realPotential (d := d) N) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      -(2 * Real.pi) ^ 2 * (kernel N i j x).re := by
  change (∂_{EuclideanSpace.single i (1 : ℝ)}
    (∂_{EuclideanSpace.single j (1 : ℝ)} (realPotential (d := d) N) : 𝓢(Rd, ℝ)) : 𝓢(Rd, ℝ)) x = _
  rw [realPotential, lineDerivOp_postcomp_re, lineDerivOp_postcomp_re,
    lineDerivOp_lineDerivOp_potential]
  simp only [postcompCLM_apply, smul_apply, smul_eq_mul]
  simp [pow_two, Complex.mul_re, Complex.mul_im]

def tensor (N : ℕ) (x : Rd) : Rd →L[ℝ] Rd :=
  ∑ i, ∑ j, (kernel N i j x).re • PeriodicRieszOperator.basisOperator i j

def scalarCoefficient (N : ℕ) (e x : Rd) : ℝ :=
  -((2 * Real.pi) ^ 2)⁻¹ * (2 * deriv (RadialHessian.profile (realPotential N) e) (‖x‖ ^ 2))

def radialCoefficient (N : ℕ) (e x : Rd) : ℝ :=
  -((2 * Real.pi) ^ 2)⁻¹ *
    (4 * deriv (deriv (RadialHessian.profile (realPotential N) e)) (‖x‖ ^ 2))

theorem kernel_re_eq (N : ℕ) (e : Rd) (he : ‖e‖ = 1) {x : Rd} (hx : x ≠ 0)
    (i j : Fin d) :
    (kernel N i j x).re = scalarCoefficient N e x *
      ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫ +
        radialCoefficient N e x * x i * x j := by
  have h := RadialHessian.secondFDeriv_eq (realPotential N) ((realPotential N).smooth ⊤)
    (realPotential_isometry N) e he hx (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [secondFDeriv_realPotential] at h
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at h
  calc
    _ = -((2 * Real.pi) ^ 2)⁻¹ * (-(2 * Real.pi) ^ 2 * (kernel N i j x).re) := by
      field_simp
    _ = _ := by
      rw [h]
      simp only [scalarCoefficient, radialCoefficient, EuclideanSpace.inner_single_right,
        conj_trivial, one_mul]
      ring

theorem tensor_apply_component (N : ℕ) (x a : Rd) (i : Fin d) :
    (tensor N x a) i = ∑ j : Fin d, (kernel N i j x).re * a j := by
  simp only [tensor, sum_apply, smul_apply, PeriodicRieszOperator.basisOperator_apply, smul_smul]
  simp [Pi.single_apply]

theorem tensor_eq (N : ℕ) (e : Rd) (he : ‖e‖ = 1) {x : Rd} (hx : x ≠ 0) :
    tensor N x = scalarCoefficient N e x • ContinuousLinearMap.id ℝ Rd +
      radialCoefficient N e x • (innerSL ℝ x).smulRight x := by
  ext a i
  rw [tensor_apply_component]
  change (∑ j, (kernel N i j x).re * a j) =
    scalarCoefficient N e x * a i + radialCoefficient N e x * (⟪x, a⟫ * x i)
  simp only [kernel_re_eq N e he hx, EuclideanSpace.inner_single_left,
    PiLp.single_apply, map_one, mul_ite, mul_one, mul_zero, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pairedStretch_tensor (N n : ℕ) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    {h : EuclideanSpace ℝ (Fin 3)} (hh : h ≠ 0) (a b : EuclideanSpace ℝ (Fin 3)) :
    SignedCrossKernel.pairedStretch n (tensor N h) a b =
      radialCoefficient N e h * EuclideanCrossProduct.tripleProduct a b h *
        ⟪h, RadialPower.radialPower n a - RadialPower.radialPower n b⟫ := by
  rw [tensor_eq N e he hh]
  exact EuclideanCrossProduct.pairedStretch_radialOperator n _ _ h a b

theorem pairedStretch_tensor_eq_zero_of_coplanar (N n : ℕ)
    (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    {h : EuclideanSpace ℝ (Fin 3)} (hh : h ≠ 0) (a b : EuclideanSpace ℝ (Fin 3))
    (hab : EuclideanCrossProduct.tripleProduct a b h = 0) :
    SignedCrossKernel.pairedStretch n (tensor N h) a b = 0 := by
  rw [pairedStretch_tensor N n e he hh, hab, mul_zero, zero_mul]

end Mettapedia.Analysis.RadialRieszRegularization
