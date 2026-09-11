import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputSymbol
import Mettapedia.Analysis.SchwartzLinearChange

/-!
# The physical low-output coordinate change

The spatial map is `(x,y) ↦ (x-y,rho*y)`. Its inverse costs at most
`3/rho` for positive ratios at most one. The inverse adjoint sends the
original input frequencies `(k,p)` to `(k,(k+p)/rho)`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange

open PressureLowOutputSymbol
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3

theorem norm_sq_pair (x : E6) :
    ‖x‖ ^ 2 = ‖(pairEquiv x).1‖ ^ 2 + ‖(pairEquiv x).2‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_six, Fin.sum_univ_three,
    pairEquiv, pairLinearEquiv]
  ring

theorem norm_first_le (x : E6) : ‖(pairEquiv x).1‖ ≤ ‖x‖ := by
  have h := norm_sq_pair x
  nlinarith [norm_nonneg x, norm_nonneg (pairEquiv x).1, sq_nonneg ‖(pairEquiv x).2‖]

theorem norm_second_le (x : E6) : ‖(pairEquiv x).2‖ ≤ ‖x‖ := by
  have h := norm_sq_pair x
  nlinarith [norm_nonneg x, norm_nonneg (pairEquiv x).2, sq_nonneg ‖(pairEquiv x).1‖]

theorem norm_pair_symm_le (a b : R3) : ‖pairEquiv.symm (a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  have h := norm_sq_pair (pairEquiv.symm (a, b))
  simp only [pairEquiv.apply_symm_apply] at h
  nlinarith [norm_nonneg (pairEquiv.symm (a, b)), norm_nonneg a, norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem inner_pair (x y : E6) :
    ⟪x, y⟫ = ⟪(pairEquiv x).1, (pairEquiv y).1⟫ + ⟪(pairEquiv x).2, (pairEquiv y).2⟫ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_six, Fin.sum_univ_three,
    pairEquiv, pairLinearEquiv]
  ring

def pairChangeLinearEquiv (rho : ℝ) (hr : rho ≠ 0) : P ≃ₗ[ℝ] P where
  toFun p := (p.1 - p.2, rho • p.2)
  invFun p := (p.1 + rho⁻¹ • p.2, rho⁻¹ • p.2)
  left_inv p := by apply Prod.ext <;> simp [smul_smul, hr]
  right_inv p := by apply Prod.ext <;> simp [smul_smul, hr]
  map_add' p q := by apply Prod.ext <;> simp [smul_add]; abel
  map_smul' c p := by apply Prod.ext <;> simp [smul_sub, smul_smul, mul_comm]

def spatialChange (rho : ℝ) (hr : rho ≠ 0) : E6 ≃L[ℝ] E6 :=
  (pairEquiv.trans (pairChangeLinearEquiv rho hr).toContinuousLinearEquiv).trans pairEquiv.symm

theorem spatialChange_apply (rho : ℝ) (hr : rho ≠ 0) (x : E6) :
    spatialChange rho hr x = pairEquiv.symm ((pairEquiv x).1 - (pairEquiv x).2,
      rho • (pairEquiv x).2) := rfl

theorem spatialChange_symm_apply (rho : ℝ) (hr : rho ≠ 0) (x : E6) :
    (spatialChange rho hr).symm x = pairEquiv.symm
      ((pairEquiv x).1 + rho⁻¹ • (pairEquiv x).2, rho⁻¹ • (pairEquiv x).2) := rfl

theorem norm_spatialChange_symm_le (rho : ℝ) (hr : 0 < rho) (hhi : rho ≤ 1) (x : E6) :
    ‖(spatialChange rho hr.ne').symm x‖ ≤ (3 / rho) * ‖x‖ := by
  rw [spatialChange_symm_apply]
  calc
    ‖pairEquiv.symm ((pairEquiv x).1 + rho⁻¹ • (pairEquiv x).2,
        rho⁻¹ • (pairEquiv x).2)‖ ≤
        ‖(pairEquiv x).1 + rho⁻¹ • (pairEquiv x).2‖ + ‖rho⁻¹ • (pairEquiv x).2‖ :=
      norm_pair_symm_le _ _
    _ ≤ (‖(pairEquiv x).1‖ + ‖rho⁻¹ • (pairEquiv x).2‖) + ‖rho⁻¹ • (pairEquiv x).2‖ := by
      gcongr
      exact norm_add_le _ _
    _ = ‖(pairEquiv x).1‖ + 2 * rho⁻¹ * ‖(pairEquiv x).2‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      ring
    _ ≤ ‖x‖ + 2 * rho⁻¹ * ‖x‖ := by
      gcongr
      · exact norm_first_le x
      · exact norm_second_le x
    _ ≤ (3 / rho) * ‖x‖ := by
      have hinv : 1 ≤ rho⁻¹ := (one_le_inv₀ hr).mpr hhi
      rw [div_eq_mul_inv]
      nlinarith [norm_nonneg x]

theorem opNorm_spatialChange_symm_le (rho : ℝ) (hr : 0 < rho) (hhi : rho ≤ 1) :
    ‖(spatialChange rho hr.ne').symm.toContinuousLinearMap‖ ≤ 3 / rho :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_spatialChange_symm_le rho hr hhi)

def frequencyChange (rho : ℝ) (x : E6) : E6 :=
  pairEquiv.symm ((pairEquiv x).1, rho⁻¹ • ((pairEquiv x).1 + (pairEquiv x).2))

theorem inverse_adjoint_eq_frequencyChange (rho : ℝ) (hr : rho ≠ 0) (ξ : E6) :
    (spatialChange rho hr).symm.toContinuousLinearMap.adjoint ξ = frequencyChange rho ξ := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪(spatialChange rho hr).symm x, ξ⟫ = ⟪x, frequencyChange rho ξ⟫
  rw [spatialChange_symm_apply]
  rw [inner_pair, inner_pair x]
  simp only [frequencyChange, pairEquiv.apply_symm_apply, inner_add_left,
    real_inner_smul_left, inner_add_right, inner_smul_right]
  ring

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputChange
