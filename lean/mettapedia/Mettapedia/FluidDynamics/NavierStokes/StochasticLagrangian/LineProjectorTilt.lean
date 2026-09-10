import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralTiltFreezing

/-!
# Transverse action through an unoriented line projector

The operator `(1 - P) R P` for a rank-one orthogonal projector has norm
equal to the transverse action on any unit representative of its line.
Consequently the squared tilt is continuous whenever the projector and
the operator are continuous, even if the selected unit vector is not.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LineProjectorTilt

open scoped RealInnerProductSpace
open PancakeAnisotropyDepletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem transverse_projector_action_eq_rankOne (R : E →L[ℝ] E) (e : E) :
    (ContinuousLinearMap.id ℝ E - InnerProductSpace.rankOne ℝ e e) * R *
      InnerProductSpace.rankOne ℝ e e =
        InnerProductSpace.rankOne ℝ (lineRemainder e (R e)) e := by
  ext x
  simp only [mul_apply_eq_comp, sub_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply, map_smul,
    lineRemainder, smul_sub, smul_smul]

theorem norm_transverse_projector_action (R : E →L[ℝ] E) (e : E) (he : ‖e‖ = 1) :
    ‖(ContinuousLinearMap.id ℝ E - InnerProductSpace.rankOne ℝ e e) * R *
      InnerProductSpace.rankOne ℝ e e‖ = ‖lineRemainder e (R e)‖ := by
  rw [transverse_projector_action_eq_rankOne, InnerProductSpace.norm_rankOne, he, mul_one]

theorem continuous_transverse_norm_sq {X : Type*} [TopologicalSpace X]
    (R : X → (E →L[ℝ] E)) (hR : Continuous R) (e : X → E) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ InnerProductSpace.rankOne ℝ (e x) (e x))) :
    Continuous (fun x ↦ ‖lineRemainder (e x) (R x (e x))‖ ^ 2) := by
  have h : Continuous (fun x ↦ ‖(ContinuousLinearMap.id ℝ E -
      InnerProductSpace.rankOne ℝ (e x) (e x)) * R x *
        InnerProductSpace.rankOne ℝ (e x) (e x)‖ ^ 2) :=
    (((continuous_const.sub hP).mul hR).mul hP).norm.pow 2
  simpa only [norm_transverse_projector_action _ _ (he _)] using h

end Mettapedia.FluidDynamics.NavierStokes.LineProjectorTilt
