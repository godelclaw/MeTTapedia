import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomSpectralProjectorPolynomial
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RankOneProjectorTangent

/-!
# Remainder-driven motion of the bottom spectral projector

The strain-square term preserves every strain eigenspace. Testing the
differentiated spectral equation against the transverse projector motion
therefore leaves only the remainder. Bottom-gap coercivity controls that
motion even when the two top eigenvalues coincide.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BottomProjectorMotion

open scoped RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeEigenframePerturbation
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeTransverseEnergyCoercivity
open PancakeMaterialProjectorTangent RankOneProjectorTangent
open SpectralClusterAnisotropy

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def bottomVector (S : SymmetricStrain) : R3 := (orderedEigenframe S.1 S.2).eigenbasis 2

theorem bottomVector_norm (S : SymmetricStrain) : ‖bottomVector S‖ = 1 :=
  (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one 2

theorem apply_bottomVector (S : SymmetricStrain) :
    S.1 (bottomVector S) = thirdEigenvalue S • bottomVector S :=
  (orderedEigenframe S.1 S.2).apply_eigenbasis 2

/-- The block of the remainder carrying the bottom line into its complementary plane. -/
def bottomCoupling (S : SymmetricStrain) (R : R3 →L[ℝ] R3) : R3 →L[ℝ] R3 :=
  expandingPlaneProjector S * R * bottomEigenlineProjector S

theorem expandingPlaneProjector_apply_bottomVector (S : SymmetricStrain) :
    expandingPlaneProjector S (bottomVector S) = 0 := by
  change bottomVector S - lineProjector (bottomVector S) (bottomVector S) = 0
  rw [lineProjector_apply_self _ (bottomVector_norm S), sub_self]

theorem bottomCoupling_eq_rankOne (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    bottomCoupling S R =
      InnerProductSpace.rankOne ℝ (expandingPlaneProjector S (R (bottomVector S))) (bottomVector S) := by
  apply ContinuousLinearMap.ext
  intro w
  change expandingPlaneProjector S (R (⟪bottomVector S, w⟫ • bottomVector S)) =
    ⟪bottomVector S, w⟫ • expandingPlaneProjector S (R (bottomVector S))
  rw [map_smul, map_smul]

theorem norm_bottomCoupling (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    ‖bottomCoupling S R‖ = ‖expandingPlaneProjector S (R (bottomVector S))‖ := by
  rw [bottomCoupling_eq_rankOne, InnerProductSpace.norm_rankOne, bottomVector_norm, mul_one]

theorem norm_bottomCoupling_le (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    ‖bottomCoupling S R‖ ≤ ‖R‖ := by
  rw [norm_bottomCoupling]
  calc
    _ ≤ ‖R (bottomVector S)‖ := norm_expandingPlaneProjector_apply_le S _
    _ ≤ ‖R‖ * ‖bottomVector S‖ := R.le_opNorm _
    _ = _ := by rw [bottomVector_norm, mul_one]

theorem bottomCoupling_eq_zero_of_preserves_bottom (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (a : ℝ) (hR : R (bottomVector S) = a • bottomVector S) :
    bottomCoupling S R = 0 := by
  rw [bottomCoupling_eq_rankOne, hR, map_smul, expandingPlaneProjector_apply_bottomVector, smul_zero]
  simp

/-- Adding a remainder component which preserves the bottom line does not
change the coupling. This includes scalar identities and polynomials in S. -/
theorem bottomCoupling_add_preserving (S : SymmetricStrain) (R A : R3 →L[ℝ] R3)
    (a : ℝ) (hA : A (bottomVector S) = a • bottomVector S) :
    bottomCoupling S (R + A) = bottomCoupling S R := by
  have hzero := bottomCoupling_eq_zero_of_preserves_bottom S A a hA
  have hadd : bottomCoupling S (R + A) = bottomCoupling S R + bottomCoupling S A := by
    unfold bottomCoupling
    noncomm_ring
  rw [hadd, hzero, add_zero]

theorem inner_remainder_bottom_eq_plane (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (v : R3)
    (hv : ⟪bottomVector S, v⟫ = 0) :
    ⟪v, R (bottomVector S)⟫ = ⟪v, expandingPlaneProjector S (R (bottomVector S))⟫ := by
  have hz : ⟪v, bottomVector S⟫ = 0 := by rw [real_inner_comm]; exact hv
  change ⟪v, R (bottomVector S)⟫ =
    ⟪v, R (bottomVector S) - ⟪bottomVector S, R (bottomVector S)⟫ • bottomVector S⟫
  rw [inner_sub_right, real_inner_smul_right, hz, mul_zero, sub_zero]

theorem strain_mul_bottomProjector (S : SymmetricStrain) :
    S.1 * bottomEigenlineProjector S = thirdEigenvalue S • bottomEigenlineProjector S := by
  apply ContinuousLinearMap.ext
  intro w
  change S.1 (⟪bottomVector S, w⟫ • bottomVector S) =
    thirdEigenvalue S • (⟪bottomVector S, w⟫ • bottomVector S)
  rw [map_smul, apply_bottomVector]
  module

theorem bottomProjector_derivative_equation (S : ℝ → SymmetricStrain)
    (Sdot D : R3 →L[ℝ] R3) (muRate t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (hP : HasDerivAt (fun τ ↦ bottomEigenlineProjector (S τ)) D t)
    (hmu : HasDerivAt (fun τ ↦ thirdEigenvalue (S τ)) muRate t) :
    Sdot * bottomEigenlineProjector (S t) + (S t).1 * D =
      muRate • bottomEigenlineProjector (S t) + thirdEigenvalue (S t) • D := by
  have h := hS.mul hP
  change HasDerivAt (fun τ ↦ (S τ).1 * bottomEigenlineProjector (S τ)) _ t at h
  simp_rw [strain_mul_bottomProjector] at h
  have h' := h.unique (hmu.smul hP)
  simpa only [add_comm] using h'

theorem bottomGap_mul_norm_sq_le_rayleighExcess (S : SymmetricStrain) (v : R3)
    (hv : ⟪bottomVector S, v⟫ = 0) :
    bottomGap S * ‖v‖ ^ 2 ≤ ⟪v, S.1 v⟫ - thirdEigenvalue S * ‖v‖ ^ 2 := by
  let F := orderedEigenframe S.1 S.2
  have hp := parseval_three_norm_sq F.eigenbasis v
  have hr := rayleigh_three S.1 S.2 F.eigenvalue F.eigenbasis F.apply_eigenbasis v
  have hz : ⟪v, F.eigenbasis 2⟫ = 0 := by
    change ⟪v, bottomVector S⟫ = 0
    rw [real_inner_comm]
    exact hv
  rw [hz] at hp hr
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, add_zero] at hp hr
  change (F.eigenvalue 1 - F.eigenvalue 2) * ‖v‖ ^ 2 ≤
    ⟪v, S.1 v⟫ - F.eigenvalue 2 * ‖v‖ ^ 2
  have hgap := F.antitone_eigenvalue (show (0 : Fin 3) ≤ 1 by decide)
  rw [← hp, hr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hgap) (sq_nonneg ⟪v, F.eigenbasis 0⟫)]

theorem inner_strainEquation_bottom (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (v : R3)
    (hv : ⟪bottomVector S, v⟫ = 0) :
    ⟪v, (-S.1 * S.1 + R) (bottomVector S)⟫ = ⟪v, R (bottomVector S)⟫ := by
  have hz : ⟪v, bottomVector S⟫ = 0 := by rw [real_inner_comm]; exact hv
  simp only [add_apply, mul_apply_eq_comp, neg_apply, apply_bottomVector,
    map_smul, inner_add_right, inner_neg_right, real_inner_smul_right, hz, mul_zero, neg_zero, zero_add]

theorem projectorMotion_energy_eq (S : SymmetricStrain) (R D : R3 →L[ℝ] R3) (muRate : ℝ)
    (ht : D * bottomEigenlineProjector S + bottomEigenlineProjector S * D = D)
    (heq : (-S.1 * S.1 + R) * bottomEigenlineProjector S + S.1 * D =
      muRate • bottomEigenlineProjector S + thirdEigenvalue S • D) :
    ⟪D (bottomVector S), S.1 (D (bottomVector S))⟫ -
      thirdEigenvalue S * ‖D (bottomVector S)‖ ^ 2 =
        -⟪D (bottomVector S), R (bottomVector S)⟫ := by
  have hv := inner_tangent_self_eq_zero (bottomVector S) (bottomVector_norm S) D ht
  have h := congrArg (fun A : R3 →L[ℝ] R3 ↦ ⟪D (bottomVector S), A (bottomVector S)⟫) heq
  have hp : bottomEigenlineProjector S (bottomVector S) = bottomVector S :=
    lineProjector_apply_self _ (bottomVector_norm S)
  change ⟪D (bottomVector S), (-S.1 * S.1 + R) (bottomEigenlineProjector S (bottomVector S)) +
      S.1 (D (bottomVector S))⟫ =
    ⟪D (bottomVector S), muRate • bottomEigenlineProjector S (bottomVector S) +
      thirdEigenvalue S • D (bottomVector S)⟫ at h
  rw [hp, inner_add_right, inner_add_right, inner_strainEquation_bottom S R _ hv] at h
  have hz : ⟪D (bottomVector S), bottomVector S⟫ = 0 := by rw [real_inner_comm]; exact hv
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, hz, mul_zero, zero_add] at h
  linarith

theorem norm_bottomProjector_tangent_apply_le (S : SymmetricStrain) (R D : R3 →L[ℝ] R3)
    (muRate : ℝ) (hg : 0 < bottomGap S)
    (ht : D * bottomEigenlineProjector S + bottomEigenlineProjector S * D = D)
    (heq : (-S.1 * S.1 + R) * bottomEigenlineProjector S + S.1 * D =
      muRate • bottomEigenlineProjector S + thirdEigenvalue S • D) :
    ‖D (bottomVector S)‖ ≤ ‖bottomCoupling S R‖ / bottomGap S := by
  have hv := inner_tangent_self_eq_zero (bottomVector S) (bottomVector_norm S) D ht
  have hc := bottomGap_mul_norm_sq_le_rayleighExcess S _ hv
  rw [projectorMotion_energy_eq S R D muRate ht heq] at hc
  rw [inner_remainder_bottom_eq_plane S R _ hv] at hc
  have hi : -⟪D (bottomVector S), expandingPlaneProjector S (R (bottomVector S))⟫ ≤
      ‖D (bottomVector S)‖ * ‖bottomCoupling S R‖ := by
    calc
      _ ≤ |⟪D (bottomVector S), expandingPlaneProjector S (R (bottomVector S))⟫| := neg_le_abs _
      _ ≤ ‖D (bottomVector S)‖ * ‖expandingPlaneProjector S (R (bottomVector S))‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [norm_bottomCoupling]
  apply (le_div_iff₀ hg).mpr
  by_cases hz : ‖D (bottomVector S)‖ = 0
  · rw [hz, zero_mul]; exact norm_nonneg _
  · have hp : 0 < ‖D (bottomVector S)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

theorem norm_bottomProjector_tangent_le (S : SymmetricStrain) (R D : R3 →L[ℝ] R3)
    (muRate : ℝ) (hg : 0 < bottomGap S) (hD : IsSelfAdjoint D)
    (ht : D * bottomEigenlineProjector S + bottomEigenlineProjector S * D = D)
    (heq : (-S.1 * S.1 + R) * bottomEigenlineProjector S + S.1 * D =
      muRate • bottomEigenlineProjector S + thirdEigenvalue S • D) :
    ‖D‖ ≤ 2 * ‖bottomCoupling S R‖ / bottomGap S := by
  calc
    _ ≤ 2 * ‖D (bottomVector S)‖ := norm_tangent_le_two_mul _ (bottomVector_norm S) D hD ht
    _ ≤ 2 * (‖bottomCoupling S R‖ / bottomGap S) := by
      gcongr
      exact norm_bottomProjector_tangent_apply_le S R D muRate hg ht heq
    _ = _ := by ring

theorem norm_deriv_bottomEigenlineProjector_le (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) :
    ‖deriv (fun τ ↦ bottomEigenlineProjector (S τ)) t‖ ≤
      2 * ‖bottomCoupling (S t) R‖ / bottomGap (S t) := by
  have hP := (BottomSpectralProjectorPolynomial.differentiableAt_bottomEigenlineProjector
    S _ t hS htop hbottom hg).hasDerivAt
  have hD := derivative_selfAdjoint _ _ t hP
    (fun τ ↦ lineProjector_isSelfAdjoint (bottomVector (S τ)))
  have ht := derivative_projector_tangent _ _ t hP
    (fun τ ↦ lineProjector_mul_self _ (bottomVector_norm (S τ)))
  exact norm_bottomProjector_tangent_le (S t) R _ _ hg hD ht
    (bottomProjector_derivative_equation S _ _ _ t hS hP hbottom.hasDerivAt)

theorem deriv_expandingPlaneProjector_eq_neg (S : ℝ → SymmetricStrain) (t : ℝ)
    (hP : DifferentiableAt ℝ (fun τ ↦ bottomEigenlineProjector (S τ)) t) :
    deriv (fun τ ↦ expandingPlaneProjector (S τ)) t =
      -deriv (fun τ ↦ bottomEigenlineProjector (S τ)) t := by
  have h := (hasDerivAt_const t (ContinuousLinearMap.id ℝ R3)).sub hP.hasDerivAt
  change HasDerivAt (fun τ ↦ expandingPlaneProjector (S τ))
    (0 - deriv (fun τ ↦ bottomEigenlineProjector (S τ)) t) t at h
  simpa only [zero_sub] using h.deriv

theorem norm_deriv_expandingPlaneProjector_le (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) :
    ‖deriv (fun τ ↦ expandingPlaneProjector (S τ)) t‖ ≤
      2 * ‖bottomCoupling (S t) R‖ / bottomGap (S t) := by
  rw [deriv_expandingPlaneProjector_eq_neg S t
    (BottomSpectralProjectorPolynomial.differentiableAt_bottomEigenlineProjector S _ t hS htop hbottom hg),
    norm_neg]
  exact norm_deriv_bottomEigenlineProjector_le S R t hS htop hbottom hg

/-- Instantaneous zero motion, not an assertion of invariance over time. -/
theorem deriv_expandingPlaneProjector_eq_zero_of_preserves_bottom (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t a : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) (hR : R (bottomVector (S t)) = a • bottomVector (S t)) :
    deriv (fun τ ↦ expandingPlaneProjector (S τ)) t = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [bottomCoupling_eq_zero_of_preserves_bottom (S t) R a hR, norm_zero, mul_zero, zero_div]
    using norm_deriv_expandingPlaneProjector_le S R t hS htop hbottom hg

theorem abs_inner_deriv_bottomProjector_le (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) (w : R3) :
    |⟪w, deriv (fun τ ↦ bottomEigenlineProjector (S τ)) t w⟫| ≤
      4 * ‖bottomCoupling (S t) R‖ / bottomGap (S t) * ‖bottomEigenlineProjector (S t) w‖ *
        ‖expandingPlaneProjector (S t) w‖ := by
  have hP := (BottomSpectralProjectorPolynomial.differentiableAt_bottomEigenlineProjector
    S _ t hS htop hbottom hg).hasDerivAt
  have hD := derivative_selfAdjoint _ _ t hP
    (fun τ ↦ lineProjector_isSelfAdjoint (bottomVector (S τ)))
  have ht := derivative_projector_tangent _ _ t hP
    (fun τ ↦ lineProjector_mul_self _ (bottomVector_norm (S τ)))
  have h := projector_tangent_quadratic_bound (bottomEigenlineProjector (S t)) _
    (lineProjector_mul_self _ (bottomVector_norm (S t)))
    (lineProjector_isSelfAdjoint (bottomVector (S t))) hD ht w
  change |⟪w, deriv (fun τ ↦ bottomEigenlineProjector (S τ)) t w⟫| ≤
    2 * ‖deriv (fun τ ↦ bottomEigenlineProjector (S τ)) t‖ *
      ‖bottomEigenlineProjector (S t) w‖ * ‖expandingPlaneProjector (S t) w‖ at h
  calc
    _ ≤ _ := h
    _ ≤ 2 * (2 * ‖bottomCoupling (S t) R‖ / bottomGap (S t)) * ‖bottomEigenlineProjector (S t) w‖ *
        ‖expandingPlaneProjector (S t) w‖ := by
      gcongr
      exact norm_deriv_bottomEigenlineProjector_le S R t hS htop hbottom hg
    _ = _ := by ring

theorem abs_inner_deriv_expandingPlaneProjector_le (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) (w : R3) :
    |⟪w, deriv (fun τ ↦ expandingPlaneProjector (S τ)) t w⟫| ≤
      4 * ‖bottomCoupling (S t) R‖ / bottomGap (S t) * ‖bottomEigenlineProjector (S t) w‖ *
        ‖expandingPlaneProjector (S t) w‖ := by
  rw [deriv_expandingPlaneProjector_eq_neg S t
    (BottomSpectralProjectorPolynomial.differentiableAt_bottomEigenlineProjector S _ t hS htop hbottom hg),
    neg_apply, inner_neg_right, abs_neg]
  exact abs_inner_deriv_bottomProjector_le S R t hS htop hbottom hg w

/-- The cross-sector term can be absorbed with an explicit positive weight.
This algebraic payment does not establish integrability of the remainder cost. -/
theorem planeTransfer_le_weightedEnergy (r gap a b rho : ℝ) (hg : 0 < gap) (hrho : 0 < rho) :
    4 * r / gap * a * b ≤ rho * a ^ 2 + 4 * r ^ 2 / (rho * gap ^ 2) * b ^ 2 := by
  calc
    _ ≤ (rho ^ 2 * a ^ 2 + (2 * r / gap * b) ^ 2) / rho := by
      apply (le_div_iff₀ hrho).mpr
      have he : 4 * r / gap * a * b * rho = 2 * (rho * a) * (2 * r / gap * b) := by ring
      rw [he]
      nlinarith [sq_nonneg (rho * a - 2 * r / gap * b)]
    _ = _ := by field_simp; ring

theorem abs_inner_deriv_expandingPlaneProjector_le_young (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) (w : R3) (rho : ℝ) (hrho : 0 < rho) :
    |⟪w, deriv (fun τ ↦ expandingPlaneProjector (S τ)) t w⟫| ≤
      rho * ‖bottomEigenlineProjector (S t) w‖ ^ 2 +
        4 * ‖bottomCoupling (S t) R‖ ^ 2 / (rho * bottomGap (S t) ^ 2) *
          ‖expandingPlaneProjector (S t) w‖ ^ 2 :=
  (abs_inner_deriv_expandingPlaneProjector_le S R t hS htop hbottom hg w).trans
    (planeTransfer_le_weightedEnergy _ _ _ _ rho hg hrho)

end Mettapedia.FluidDynamics.NavierStokes.BottomProjectorMotion
