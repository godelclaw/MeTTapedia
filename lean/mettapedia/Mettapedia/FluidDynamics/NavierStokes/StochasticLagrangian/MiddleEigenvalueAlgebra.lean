import Mathlib.Analysis.InnerProductSpace.Trace
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralProjectorRegularity

/-!
# Strain cubes and the middle eigenvalue

For a velocity-gradient matrix `A` (`A a b = ∂_b u_a`) with zero trace, let `S` be its
symmetric part and `ω` its curl. The traces of the powers of `A` split exactly:

```text
tr(A²) = |S|² - |ω|²/2,
tr(A³) = tr(S³) + (3/4) ⟪ω, A ω⟫,
```

and `⟪ω, A ω⟫ = ⟪ω, S ω⟫` is the stretching. For a symmetric trace-free `S` with ordered
eigenvalues `λ₀ ≥ λ₁ ≥ λ₂`, the cube trace is `3 λ₀ λ₁ λ₂`, and

```text
-(4/3) tr(S³) ≤ 2 max(λ₁, 0) |S|².
```

When the middle eigenvalue is not positive (at most one expanding direction, the
line-stretching, tube-forming configuration), the left side is not positive. Only a
positive middle eigenvalue (two expanding directions: sheet-forming, "pancake" strain)
makes it positive. Integrated over a periodic box, where `tr(A³)` and `tr(A²)` are
divergences, these identities turn the enstrophy production into `-(4/3) ∫ tr(S³)`, the
identity of Betchov.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MiddleEigenvalueAlgebra

open scoped RealInnerProductSpace BigOperators
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- A real `3 × 3` matrix, read as a velocity gradient `A a b = ∂_b u_a`. -/
abbrev GradMatrix := Fin 3 → Fin 3 → ℝ

def trSq (A : GradMatrix) : ℝ := ∑ a, ∑ b, A a b * A b a

def trCube (A : GradMatrix) : ℝ := ∑ a, ∑ b, ∑ c, A a b * A b c * A c a

def symm (A : GradMatrix) : GradMatrix := fun a b ↦ (A a b + A b a) / 2

theorem symm_apply (A : GradMatrix) (a b : Fin 3) : symm A a b = (A a b + A b a) / 2 := rfl

/-- The curl of the gradient: `ω = (∂₁u₂ - ∂₂u₁, ∂₂u₀ - ∂₀u₂, ∂₀u₁ - ∂₁u₀)`. -/
def vort (A : GradMatrix) : Fin 3 → ℝ := ![A 2 1 - A 1 2, A 0 2 - A 2 0, A 1 0 - A 0 1]

def stretch (A : GradMatrix) : ℝ := ∑ a, ∑ b, vort A a * A a b * vort A b

def normSq (S : GradMatrix) : ℝ := ∑ a, ∑ b, S a b ^ 2

def vortSq (A : GradMatrix) : ℝ := ∑ a, vort A a ^ 2

/-- **The square trace.** -/
theorem trSq_eq (A : GradMatrix) : trSq A = normSq (symm A) - vortSq A / 2 := by
  simp only [trSq, normSq, symm, vortSq, vort, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The cube trace.** For a trace-free gradient, the cube trace is that of the strain plus
three quarters of the stretching. -/
theorem trCube_eq (A : GradMatrix) (htr : A 0 0 + A 1 1 + A 2 2 = 0) :
    trCube A = trCube (symm A) + 3 / 4 * stretch A := by
  simp only [trCube, symm, stretch, vort, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-(3 : ℝ) / 4 * ((A 2 1 - A 1 2) ^ 2 + (A 0 2 - A 2 0) ^ 2 +
    (A 1 0 - A 0 1) ^ 2)) * htr

theorem symm_symm (A : GradMatrix) (a b : Fin 3) : symm A a b = symm A b a := by
  simp only [symm, add_comm]

theorem symm_trace (A : GradMatrix) :
    symm A 0 0 + symm A 1 1 + symm A 2 2 = A 0 0 + A 1 1 + A 2 2 := by
  simp only [symm]
  ring

/-! ## Divergence form of the traces

Let `v` be a velocity, `A a b = ∂_b v_a` its gradient and `D i j k = ∂_i ∂_j v_k` its second
derivatives, symmetric in `i, j`. For a divergence-free field, `tr(A²)` is the divergence
of `(v·∇)v` and `tr(A³)` is the divergence of `F_i = ∑ v_j ∂_j v_k ∂_k v_i - v_i tr(A²)/2`.
The expressions below are the divergences produced by the product rule. -/

/-- The divergence of `(v·∇)v`. -/
def sqFluxDiv (v : Fin 3 → ℝ) (A : GradMatrix) (D : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ k, ∑ j, (A j k * A k j + v j * D k j k)

/-- The divergence of the cube flux. -/
def cubeFluxDiv (v : Fin 3 → ℝ) (A : GradMatrix) (D : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ((∑ j, ∑ k, (A j i * A k j * A i k + v j * D i j k * A i k + v j * A k j * D i k i)) -
    (A i i * trSq A + v i * ∑ a, ∑ b, (D i b a * A b a + A a b * D i a b)) / 2)

theorem sqFluxDiv_eq (v : Fin 3 → ℝ) (A : GradMatrix) (D : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hdd : ∀ k, D 0 k 0 + D 1 k 1 + D 2 k 2 = 0) : sqFluxDiv v A D = trSq A := by
  have h0 := hdd 0
  have h1 := hdd 1
  have h2 := hdd 2
  simp only [sqFluxDiv, trSq, Fin.sum_univ_three]
  linear_combination v 0 * h0 + v 1 * h1 + v 2 * h2

theorem cubeFluxDiv_eq (v : Fin 3 → ℝ) (A : GradMatrix) (D : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (htr : A 0 0 + A 1 1 + A 2 2 = 0) (hdd : ∀ k, D 0 k 0 + D 1 k 1 + D 2 k 2 = 0)
    (hsym : ∀ i j k, D i j k = D j i k) : cubeFluxDiv v A D = trCube A := by
  have e10 (k : Fin 3) : D 1 0 k = D 0 1 k := hsym 1 0 k
  have e20 (k : Fin 3) : D 2 0 k = D 0 2 k := hsym 2 0 k
  have e21 (k : Fin 3) : D 2 1 k = D 1 2 k := hsym 2 1 k
  have h0 := hdd 0
  have h1 := hdd 1
  have h2 := hdd 2
  simp only [e10, e20, e21] at h0 h1 h2
  simp only [cubeFluxDiv, trSq, trCube, Fin.sum_univ_three, e10, e20, e21]
  linear_combination (v 0 * A 0 0 + v 1 * A 0 1 + v 2 * A 0 2) * h0 +
    (v 0 * A 1 0 + v 1 * A 1 1 + v 2 * A 1 2) * h1 +
    (v 0 * A 2 0 + v 1 * A 2 1 + v 2 * A 2 2) * h2 -
    (1 / 2 : ℝ) * (A 0 0 * A 0 0 + A 0 1 * A 1 0 + A 0 2 * A 2 0 + A 1 0 * A 0 1 +
      A 1 1 * A 1 1 + A 1 2 * A 2 1 + A 2 0 * A 0 2 + A 2 1 * A 1 2 + A 2 2 * A 2 2) * htr

/-! ## The matrix as an operator on physical space -/

/-- The linear map of a matrix. -/
def matLin (S : GradMatrix) : R3 →ₗ[ℝ] R3 where
  toFun v := WithLp.toLp 2 (fun a ↦ ∑ b, S a b * v b)
  map_add' v w := by
    ext a
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext a
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- The continuous linear map of a matrix. -/
def matCLM (S : GradMatrix) : R3 →L[ℝ] R3 := LinearMap.toContinuousLinearMap (matLin S)

theorem matCLM_apply (S : GradMatrix) (v : R3) (a : Fin 3) :
    matCLM S v a = ∑ b, S a b * v b := rfl

theorem inner_eq_sum (u v : R3) : ⟪u, v⟫ = ∑ a, u a * v a := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

theorem matCLM_symmetric (S : GradMatrix) (hS : ∀ a b, S a b = S b a) (u v : R3) :
    ⟪u, matCLM S v⟫ = ⟪matCLM S u, v⟫ := by
  simp only [inner_eq_sum, matCLM_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by rw [hS a b]; ring

/-- The symmetric strain of a symmetric matrix. -/
def toStrain (S : GradMatrix) (hS : ∀ a b, S a b = S b a) : SymmetricStrain :=
  ⟨matCLM S, matCLM_symmetric S hS⟩

/-- Traces of the operator in the standard basis are the matrix traces. -/
theorem trace_std (T : R3 →L[ℝ] R3) :
    LinearMap.trace ℝ R3 T.toLinearMap = ∑ a, T (EuclideanSpace.single a 1) a := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  rfl

theorem matCLM_single (S : GradMatrix) (a c : Fin 3) :
    matCLM S (EuclideanSpace.single a 1) c = S c a := by
  rw [matCLM_apply]
  simp only [PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem trace_matCLM (S : GradMatrix) :
    LinearMap.trace ℝ R3 (matCLM S).toLinearMap = S 0 0 + S 1 1 + S 2 2 := by
  rw [trace_std]
  simp only [matCLM_single, Fin.sum_univ_three]

theorem trace_matCLM_sq (S : GradMatrix) :
    LinearMap.trace ℝ R3 ((matCLM S).comp (matCLM S)).toLinearMap = trSq S := by
  rw [trace_std]
  simp only [ContinuousLinearMap.comp_apply, matCLM_apply, trSq, PiLp.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem trace_matCLM_cube (S : GradMatrix) :
    LinearMap.trace ℝ R3 ((matCLM S).comp ((matCLM S).comp (matCLM S))).toLinearMap =
      trCube S := by
  rw [trace_std]
  simp only [ContinuousLinearMap.comp_apply, matCLM_apply, trCube, PiLp.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun c _ ↦ by ring

/-! ## Eigenvalues -/

/-- Traces in the ordered eigenframe. -/
theorem trace_eigen (S : SymmetricStrain) (T : R3 →L[ℝ] R3) :
    LinearMap.trace ℝ R3 T.toLinearMap =
      ∑ i, ⟪(orderedEigenframe S.1 S.2).eigenbasis i,
        T ((orderedEigenframe S.1 S.2).eigenbasis i)⟫ :=
  LinearMap.trace_eq_sum_inner _ _

/-- **The cube trace and the middle eigenvalue.** For a symmetric trace-free matrix,
`-(4/3) tr(S³) ≤ 2 max(λ₁, 0) |S|²`, with `λ₁` the middle eigenvalue. -/
theorem neg_trCube_le (S : GradMatrix) (hS : ∀ a b, S a b = S b a)
    (htr : S 0 0 + S 1 1 + S 2 2 = 0) :
    -(4 / 3) * trCube S ≤
      2 * max (SymmetricStrain.secondEigenvalue (toStrain S hS)) 0 * normSq S := by
  set F := orderedEigenframe (toStrain S hS).1 (toStrain S hS).2 with hF
  have hunit (i : Fin 3) : ⟪F.eigenbasis i, F.eigenbasis i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, F.eigenbasis.orthonormal.1 i, one_pow]
  have happ (i : Fin 3) : matCLM S (F.eigenbasis i) = F.eigenvalue i • F.eigenbasis i :=
    F.apply_eigenbasis i
  have h1 : S 0 0 + S 1 1 + S 2 2 = ∑ i, F.eigenvalue i := by
    rw [← trace_matCLM, trace_eigen (toStrain S hS) (matCLM S)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ⟪F.eigenbasis i, matCLM S (F.eigenbasis i)⟫ = _
    rw [happ, real_inner_smul_right, hunit, mul_one]
  have h2 : trSq S = ∑ i, F.eigenvalue i ^ 2 := by
    rw [← trace_matCLM_sq, trace_eigen (toStrain S hS)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ⟪F.eigenbasis i, matCLM S (matCLM S (F.eigenbasis i))⟫ = _
    rw [happ, map_smul, happ, smul_smul, real_inner_smul_right, hunit, mul_one]
    ring
  have h3 : trCube S = ∑ i, F.eigenvalue i ^ 3 := by
    rw [← trace_matCLM_cube, trace_eigen (toStrain S hS)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ⟪F.eigenbasis i, matCLM S (matCLM S (matCLM S (F.eigenbasis i)))⟫ = _
    rw [happ, map_smul, happ, map_smul, map_smul, happ, smul_smul, smul_smul,
      real_inner_smul_right, hunit, mul_one]
    ring
  have hnorm : normSq S = trSq S := by
    simp only [normSq, trSq, sq]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by rw [hS b a]
  have hmid : SymmetricStrain.secondEigenvalue (toStrain S hS) = F.eigenvalue 1 := rfl
  have h01 : F.eigenvalue 1 ≤ F.eigenvalue 0 := F.antitone_eigenvalue (by decide)
  have h12 : F.eigenvalue 2 ≤ F.eigenvalue 1 := F.antitone_eigenvalue (by decide)
  rw [hnorm, h2, h3, hmid]
  rw [htr] at h1
  simp only [Fin.sum_univ_three] at h1 ⊢
  set l0 := F.eigenvalue 0
  set l1 := F.eigenvalue 1
  set l2 := F.eigenvalue 2
  have hl2 : l2 = -l0 - l1 := by linarith
  rcases le_or_gt l1 0 with h | h
  · rw [max_eq_right h]
    have hl0 : 0 ≤ l0 := by linarith
    have hprod : 0 ≤ l0 * (l1 * l2) := mul_nonneg hl0 (mul_nonneg_of_nonpos_of_nonpos h (by linarith))
    rw [hl2] at hprod ⊢
    nlinarith [hprod]
  · rw [max_eq_left h.le]
    rw [hl2]
    nlinarith [sq_nonneg (l0 - (l0 + l1)), mul_pos h h, sq_nonneg l1, sq_nonneg l0,
      mul_nonneg h.le (sq_nonneg (l0 - (-l0 - l1))), mul_nonneg h.le (sq_nonneg l1)]

end Mettapedia.FluidDynamics.NavierStokes.MiddleEigenvalueAlgebra
