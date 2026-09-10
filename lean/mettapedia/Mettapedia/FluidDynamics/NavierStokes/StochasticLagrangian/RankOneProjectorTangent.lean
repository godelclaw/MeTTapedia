import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialProjectorTangent
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeEigenframePerturbation

/-!
# Tangent operators at a rank-one orthogonal projector

A self-adjoint projector tangent is determined by its action on the
reference unit vector. Its rank-two representation gives an operator-norm
bound without constructing a derivative of a signed eigenvector.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RankOneProjectorTangent

open scoped RealInnerProductSpace
open PancakeEigenframePerturbation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem lineProjector_isSelfAdjoint (e : H) : IsSelfAdjoint (lineProjector e) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪lineProjector e x, y⟫ = ⟪x, lineProjector e y⟫
  simp only [lineProjector, InnerProductSpace.rankOne_apply,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm e x]
  ring

omit [CompleteSpace H] in
theorem lineProjector_mul_self (e : H) (he : ‖e‖ = 1) :
    lineProjector e * lineProjector e = lineProjector e :=
  InnerProductSpace.isIdempotentElem_rankOne_self he

omit [CompleteSpace H] in
theorem lineProjector_apply_self (e : H) (he : ‖e‖ = 1) : lineProjector e e = e := by
  simp [lineProjector, he]

omit [CompleteSpace H] in
theorem inner_tangent_self_eq_zero (e : H) (he : ‖e‖ = 1) (D : H →L[ℝ] H)
    (ht : D * lineProjector e + lineProjector e * D = D) : ⟪e, D e⟫ = 0 := by
  have h := congrArg (fun A : H →L[ℝ] H ↦ ⟪e, A e⟫) ht
  simp only [add_apply, mul_apply_eq_comp,
    inner_add_right, lineProjector, InnerProductSpace.rankOne_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one, one_smul] at h
  linarith

theorem tangent_eq_rankOne_sum (e : H) (D : H →L[ℝ] H) (hD : IsSelfAdjoint D)
    (ht : D * lineProjector e + lineProjector e * D = D) :
    D = InnerProductSpace.rankOne ℝ (D e) e + InnerProductSpace.rankOne ℝ e (D e) := by
  ext w
  have h := congrArg (fun A : H →L[ℝ] H ↦ A w) ht
  simp only [add_apply, mul_apply_eq_comp, lineProjector, InnerProductSpace.rankOne_apply,
    map_smul] at h
  have hs : ⟪D e, w⟫ = ⟪e, D w⟫ := hD.isSymmetric e w
  rw [← hs] at h
  simpa only [add_apply, InnerProductSpace.rankOne_apply] using h.symm

theorem norm_tangent_le_two_mul (e : H) (he : ‖e‖ = 1) (D : H →L[ℝ] H)
    (hD : IsSelfAdjoint D) (ht : D * lineProjector e + lineProjector e * D = D) :
    ‖D‖ ≤ 2 * ‖D e‖ := by
  calc
    ‖D‖ = ‖InnerProductSpace.rankOne ℝ (D e) e + InnerProductSpace.rankOne ℝ e (D e)‖ :=
      congrArg norm (tangent_eq_rankOne_sum e D hD ht)
    _ ≤ ‖InnerProductSpace.rankOne ℝ (D e) e‖ +
        ‖InnerProductSpace.rankOne ℝ e (D e)‖ := norm_add_le _ _
    _ = _ := by rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne, he]; ring

end Mettapedia.FluidDynamics.NavierStokes.RankOneProjectorTangent
