import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyEnvelope

/-!
# Collision-safe alignment depletion of finite spectral increments

The top Rayleigh supporting remainder pays the aligned part of the
operator/vector increment. The remaining cost contains only transverse
vorticity. No eigenvalue gap or eigenvector differentiability is required.
This is a finite-increment estimate, not a passage to a weak PDE limit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionIncrementDepletion

open scoped RealInnerProductSpace
open PancakeRegularizedDiffusion PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open PancakeAnisotropyDepletion PancakeStrainSpectralFrame
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem supportingRemainder_eq_gap_energy (S T : SymmetricStrain) :
    supportingRemainder S T = ⟪topVector S, regularizedGap T 0 (topVector S)⟫ := by
  simp only [supportingRemainder, regularizedGap, add_zero, sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    topVector_norm, topVector_rayleigh]
  ring

theorem gap_increment_topVector (S T : SymmetricStrain) (delta : ℝ) :
    (regularizedGap T delta - regularizedGap S delta) (topVector S) =
      regularizedGap T 0 (topVector S) := by
  have he : S.1 (topVector S) = topEigenvalue S • topVector S :=
    (orderedEigenframe S.1 S.2).apply_eigenbasis 0
  simp only [regularizedGap, sub_apply, smul_apply, one_apply_eq_self, add_zero, he]
  module

theorem increment_aligned_completion (S T : SymmetricStrain) (delta : ℝ) (w v : R3) :
    let c := ⟪topVector S, w⟫
    let d := lineRemainder (topVector S) w
    let G := regularizedGap T delta - regularizedGap S delta;
    regularizedEnergy T delta (w + v) - regularizedEnergy S delta w - incrementRate S T delta w v =
      ⟪v + c • topVector S, regularizedGap T 0 (v + c • topVector S)⟫ +
        supportingRemainder S T * ‖d‖ ^ 2 + 2 * ⟪v, G d⟫ + delta * ‖v‖ ^ 2 := by
  dsimp only
  rw [regularizedEnergy_increment, norm_lineRemainder_sq _ _ (topVector_norm S)]
  have ha : ⟪v, regularizedGap T delta v⟫ = ⟪v, regularizedGap T 0 v⟫ + delta * ‖v‖ ^ 2 := by
    simp only [regularizedGap_energy, zero_mul, add_zero]
  rw [ha]
  simp only [lineRemainder, map_sub, map_add, map_smul, inner_add_left, inner_add_right,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, gap_increment_topVector,
    regularizedGap_symmetric T 0 v (topVector S), real_inner_comm (topVector S) (regularizedGap T 0 v),
    ← supportingRemainder_eq_gap_energy]
  ring

/-- The full aligned square is nonnegative even when the top eigenvalue
collides or the selected top direction changes discontinuously. -/
theorem incrementRate_paid_depleted (S T : SymmetricStrain) (delta : ℝ) (w v : R3) (hd : 0 < delta) :
    let d := lineRemainder (topVector S) w;
    incrementRate S T delta w v + (delta / 2) * ‖v‖ ^ 2 + supportingRemainder S T * ‖d‖ ^ 2 ≤
      regularizedEnergy T delta (w + v) - regularizedEnergy S delta w +
        (8 / delta) * ‖T.1 - S.1‖ ^ 2 * ‖d‖ ^ 2 := by
  let d := lineRemainder (topVector S) w
  let G := regularizedGap T delta - regularizedGap S delta
  have he := increment_aligned_completion S T delta w v
  have hk := regularizedGap_coercive T 0 (v + ⟪topVector S, w⟫ • topVector S)
  simp only [zero_mul] at hk
  have hy := spectralDefect_forcing_young v (-G d) (delta / 2) (by positivity)
  simp only [inner_neg_right, norm_neg] at hy
  have hG := regularizedGap_sub_norm S T delta
  have hop := G.le_opNorm d
  have hs : ‖G d‖ ^ 2 ≤ 4 * ‖T.1 - S.1‖ ^ 2 * ‖d‖ ^ 2 := by
    calc
      _ ≤ (‖G‖ * ‖d‖) ^ 2 := by gcongr
      _ ≤ ((2 * ‖T.1 - S.1‖) * ‖d‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hp := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ delta / 2)
  have hdiv : ‖G d‖ ^ 2 / (delta / 2) ≤ (8 / delta) * ‖T.1 - S.1‖ ^ 2 * ‖d‖ ^ 2 := by
    convert! hp using 1
    ring
  dsimp only at he ⊢
  nlinarith only [he, hk, hy, hdiv]

theorem incrementRate_paid_aligned (S T : SymmetricStrain) (delta c : ℝ) (v : R3) (hd : 0 < delta) :
    incrementRate S T delta (c • topVector S) v + (delta / 2) * ‖v‖ ^ 2 ≤
      regularizedEnergy T delta (c • topVector S + v) - regularizedEnergy S delta (c • topVector S) := by
  have h := incrementRate_paid_depleted S T delta (c • topVector S) v hd
  simpa only [lineRemainder, real_inner_smul_right, real_inner_self_eq_norm_sq,
    topVector_norm, one_pow, mul_one, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] using h

/-- The scalar majorant is continuous through collisions. Its smoothing
parameter is independent of the energy regularization used to pay increments. -/
theorem incrementRate_paid_scalar (S T : SymmetricStrain) (delta epsilon : ℝ)
    (w v : R3) (hd : 0 < delta) (heps : 0 < epsilon) :
    incrementRate S T delta w v + (delta / 2) * ‖v‖ ^ 2 ≤
      regularizedEnergy T delta (w + v) - regularizedEnergy S delta w +
        (8 / delta) * ‖T.1 - S.1‖ ^ 2 *
          (regularizedEnergy S epsilon w / (topGap S + epsilon)) := by
  have hp := incrementRate_paid_depleted S T delta w v hd
  have hm : ‖lineRemainder (topVector S) w‖ ^ 2 ≤ regularizedEnergy S epsilon w / (topGap S + epsilon) :=
    (le_div_iff₀ (add_pos_of_nonneg_of_pos (topGap_nonneg S) heps)).mpr
      (by simpa only [mul_comm] using
        SpectralAnisotropyEnvelope.regularizedGap_mul_lineRemainder_sq_le S w epsilon heps.le)
  have hc := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (8 / delta) * ‖T.1 - S.1‖ ^ 2)
  have hs := mul_nonneg (supportingRemainder_nonneg S T) (sq_nonneg ‖lineRemainder (topVector S) w‖)
  dsimp only at hp
  linarith only [hp, hc, hs]

end Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionIncrementDepletion
