import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueContinuity

/-!
# Ordered strain eigenvalue rates without a moving eigenbasis

The extreme eigenvalue derivatives follow from variational extrema.
The trace identity then supplies the middle eigenvalue derivative.
Only scalar differentiability of the two extremes is required, including
at collisions; the reference eigenbasis is fixed at the evaluation time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StrainEigenvalueRates

open scoped Topology RealInnerProductSpace
open Filter PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeTopEigenvalueDerivative
open StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem thirdEigenvalue_derivative_eq_of_hasDerivAt
    (S : ℝ → SymmetricStrain) (Sdot : R3 →L[ℝ] R3) (rate t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (hL : HasDerivAt (fun τ ↦ thirdEigenvalue (S τ)) rate t)
    (e : R3) (he : ‖e‖ = 1) (hv : (S t).1 e = thirdEigenvalue (S t) • e) :
    rate = ⟪e, Sdot e⟫ := by
  have hq := (hasDerivAt_const t e).inner ℝ (hS.clm_apply (hasDerivAt_const t e))
  have hd := hq.sub hL
  simp only [inner_zero_left, map_zero, add_zero] at hd
  have hz : ⟪e, (S t).1 e⟫ - thirdEigenvalue (S t) = 0 := by
    rw [hv, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hm : IsLocalMin (fun τ ↦ ⟪e, (S τ).1 e⟫ - thirdEigenvalue (S τ)) t := by
    apply Eventually.of_forall
    intro τ
    dsimp only
    rw [hz]
    exact sub_nonneg.mpr (constructedBottomEigenvalue_le_rayleigh (S τ).1 (S τ).2 e he)
  exact (sub_eq_zero.mp (hm.hasDerivAt_eq_zero hd)).symm

theorem hasDerivAt_thirdEigenvalue_of_differentiableAt
    (S : ℝ → SymmetricStrain) (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (hL : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t) :
    HasDerivAt (fun τ ↦ thirdEigenvalue (S τ))
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 2,
        Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 2)⟫ t := by
  have h := hL.hasDerivAt
  rw [thirdEigenvalue_derivative_eq_of_hasDerivAt S Sdot _ t hS h _
    ((orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 2)
    ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 2)] at h
  exact h

theorem hasDerivAt_trace (S : ℝ → SymmetricStrain) (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t) :
    HasDerivAt (fun τ ↦ LinearMap.trace ℝ R3 (S τ).1.toLinearMap)
      (LinearMap.trace ℝ R3 Sdot.toLinearMap) t := by
  simp_rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [ContinuousLinearMap.coe_coe, inner_zero_left, map_zero, add_zero] using
    (hasDerivAt_const t ((EuclideanSpace.basisFun (Fin 3) ℝ) i)).inner ℝ
      (hS.clm_apply (hasDerivAt_const t ((EuclideanSpace.basisFun (Fin 3) ℝ) i)))

theorem hasDerivAt_secondEigenvalue (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t) :
    HasDerivAt (fun τ ↦ secondEigenvalue (S τ))
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 1,
        Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 1)⟫ t := by
  have h0 := hasDerivAt_topEigenvalue_of_differentiableAt S Sdot t hS htop
  have h2 := hasDerivAt_thirdEigenvalue_of_differentiableAt S Sdot t hS hbottom
  have h := ((hasDerivAt_trace S Sdot t hS).sub h0).sub h2
  change HasDerivAt (fun τ ↦ LinearMap.trace ℝ R3 (S τ).1.toLinearMap -
    topEigenvalue (S τ) - thirdEigenvalue (S τ)) _ t at h
  have he (τ : ℝ) : LinearMap.trace ℝ R3 (S τ).1.toLinearMap -
      topEigenvalue (S τ) - thirdEigenvalue (S τ) = secondEigenvalue (S τ) := by
    rw [trace_eq_sum_orderedEigenvalues]
    ring
  simp_rw [he] at h
  apply h.congr_deriv
  rw [LinearMap.trace_eq_sum_inner _ (orderedEigenframe (S t).1 (S t).2).eigenbasis]
  simp [Fin.sum_univ_succ]

theorem hasDerivAt_topGap (S : ℝ → SymmetricStrain) (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t) :
    HasDerivAt (fun τ ↦ topGap (S τ))
      (⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
          Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ -
        ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 1,
          Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 1)⟫) t :=
  (hasDerivAt_topEigenvalue_of_differentiableAt S Sdot t hS htop).sub
    (hasDerivAt_secondEigenvalue S Sdot t hS htop hbottom)

end Mettapedia.FluidDynamics.NavierStokes.StrainEigenvalueRates
