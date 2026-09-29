import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inverse transported-frame metric

For the parabolic operator `D = ∂t + u·∇ - νΔ`, suppose a vector and a
positive frame tensor satisfy `Dv = Bv + f` and `DM = BM + MBᵀ`. Put
`Q = M⁻¹` and `K_j = (∂j M) Q`. Differentiating the inverse gives

* `∂j Q = -Q K_j`, with `Q K_j = K_jᵀ Q`;
* `DQ = -QB - BᵀQ - 2ν Σ K_jᵀ Q K_j`.

The exact quadratic production is then

`D(vᵀ Q v) = 2 vᵀ Q f - 2ν Σ (∂j v - K_j v)ᵀ Q (∂j v - K_j v)`.

This file proves the finite-dimensional algebra of that cancellation and
its nonpositive sign in the unforced case. The input rates are explicit
matrices and vectors, not actual derivatives of constructed stochastic
fields. Their PDE realization, positivity of the evolving tensor, and a
comparison principle remain separate analytic obligations. In particular,
this identity supplies no uniform coercivity of the changing metric and
does not imply arbitrary-data regularity by itself.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TransportedFrameMetric

open scoped BigOperators Matrix

variable {ι δ : Type*} [Fintype ι] [Fintype δ]

/-- The real bilinear pairing in a matrix metric. -/
def pair (Q : Matrix ι ι ℝ) (v w : ι → ℝ) : ℝ := v ⬝ᵥ (Q *ᵥ w)

theorem pair_symm (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (v w : ι → ℝ) :
    pair Q v w = pair Q w v := by
  simpa only [pair, hQ.eq] using Matrix.dotProduct_transpose_mulVec Q v w

theorem pair_add_right (Q : Matrix ι ι ℝ) (v w z : ι → ℝ) :
    pair Q v (w + z) = pair Q v w + pair Q v z := by
  simp only [pair, Matrix.mulVec_add, dotProduct_add]

theorem pair_sub_self (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (v w : ι → ℝ) :
    pair Q (v - w) (v - w) = pair Q v v - 2 * pair Q v w + pair Q w w := by
  simp only [pair, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  change pair Q v v - pair Q w v - (pair Q v w - pair Q w w) = _
  rw [pair_symm Q hQ w v]
  simp only [pair]
  ring

theorem pair_matrix_sub (Q R : Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (Q - R) v w = pair Q v w - pair R v w := by
  simp only [pair, Matrix.sub_mulVec, dotProduct_sub]

theorem pair_matrix_neg (Q : Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (-Q) v w = -pair Q v w := by
  simp only [pair, Matrix.neg_mulVec, dotProduct_neg]

theorem pair_matrix_smul (c : ℝ) (Q : Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (c • Q) v w = c * pair Q v w := by
  simp only [pair, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem pair_matrix_sum (Q : δ → Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (∑ j, Q j) v w = ∑ j, pair (Q j) v w := by
  classical
  unfold pair
  have hm : (∑ j, Q j) *ᵥ w = ∑ j, Q j *ᵥ w := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hm, dotProduct_sum]

theorem pair_mul (Q B : Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (Q * B) v w = pair Q v (B *ᵥ w) := by
  simp only [pair, Matrix.mulVec_mulVec]

theorem pair_transpose_mul (Q B : Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (B.transpose * Q) v w = pair Q (B *ᵥ v) w := by
  simp only [pair, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem pair_congruence (Q B : Matrix ι ι ℝ) (v w : ι → ℝ) :
    pair (B.transpose * Q * B) v w = pair Q (B *ᵥ v) (B *ᵥ w) := by
  rw [pair_mul, pair_transpose_mul]

/-- A spatial derivative of an inverse frame metric. -/
def gradient (Q K : Matrix ι ι ℝ) : Matrix ι ι ℝ := -(Q * K)

/-- The parabolic rate of the inverse metric, retaining the diffusion term. -/
def rate (ν : ℝ) (Q B : Matrix ι ι ℝ) (K : δ → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  -(Q * B) - B.transpose * Q - (2 * ν) • ∑ j, (K j).transpose * Q * K j

/-- The product/chain rule for a symmetric matrix quadratic form under
`∂t + u·∇ - νΔ`, with its vector and matrix rates supplied explicitly. -/
def production (ν : ℝ) (Q : Matrix ι ι ℝ) (v vRate : ι → ℝ)
    (qRate : Matrix ι ι ℝ) (dv : δ → ι → ℝ) (dq : δ → Matrix ι ι ℝ) : ℝ :=
  2 * pair Q v vRate + pair qRate v v -
    2 * ν * ∑ j, pair Q (dv j) (dv j) -
    4 * ν * ∑ j, pair (dq j) v (dv j)

/-- The strain cancels exactly; forcing and the diffusion square remain. -/
theorem production_eq (ν : ℝ) (Q B : Matrix ι ι ℝ) (hQ : Q.IsSymm)
    (K : δ → Matrix ι ι ℝ) (hK : ∀ j, Q * K j = (K j).transpose * Q)
    (v f : ι → ℝ) (dv : δ → ι → ℝ) :
    production ν Q v (B *ᵥ v + f) (rate ν Q B K) dv (fun j ↦ gradient Q (K j)) =
      2 * pair Q v f -
        2 * ν * ∑ j, pair Q (dv j - K j *ᵥ v) (dv j - K j *ᵥ v) := by
  have hg (j : δ) : pair (gradient Q (K j)) v (dv j) =
      -pair Q (dv j) (K j *ᵥ v) := by
    rw [gradient, pair_matrix_neg, hK j, pair_transpose_mul, pair_symm Q hQ]
  have hr : pair (rate ν Q B K) v v =
      -2 * pair Q v (B *ᵥ v) -
        2 * ν * ∑ j, pair Q (K j *ᵥ v) (K j *ᵥ v) := by
    simp only [rate, pair_matrix_sub, pair_matrix_neg, pair_matrix_smul,
      pair_matrix_sum, pair_congruence]
    rw [pair_mul, pair_transpose_mul, pair_symm Q hQ (B *ᵥ v) v]
    ring
  simp only [production, pair_add_right, hr, hg, Finset.sum_neg_distrib,
    pair_sub_self Q hQ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

/-- Symmetric frame-tensor derivatives give precisely the required metric
compatibility when `K_j = (∂j M) Q`. -/
theorem frame_gradient_compatible (Q P : Matrix ι ι ℝ)
    (hQ : Q.IsSymm) (hP : P.IsSymm) :
    Q * (P * Q) = (P * Q).transpose * Q := by
  rw [Matrix.transpose_mul, hQ, hP, Matrix.mul_assoc]

/-- For a nonnegative metric and positive diffusion, unforced production
is nonpositive. No coercivity constant is provided by this statement. -/
theorem production_nonpos (ν : ℝ) (hν : 0 ≤ ν) (Q B : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) (K : δ → Matrix ι ι ℝ)
    (hK : ∀ j, Q * K j = (K j).transpose * Q) (v : ι → ℝ) (dv : δ → ι → ℝ) :
    production ν Q v (B *ᵥ v) (rate ν Q B K) dv (fun j ↦ gradient Q (K j)) ≤ 0 := by
  have hs : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.1
  have he := production_eq ν Q B hs K hK v 0 dv
  simp only [add_zero, pair, Matrix.mulVec_zero, dotProduct_zero, mul_zero, zero_sub] at he
  rw [he]
  apply neg_nonpos.mpr
  apply mul_nonneg (mul_nonneg (by norm_num) hν)
  apply Finset.sum_nonneg
  intro j _
  simpa using hQ.dotProduct_mulVec_nonneg (dv j - K j *ᵥ v)

end Mettapedia.FluidDynamics.NavierStokes.TransportedFrameMetric
