import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionIncrementDepletion

/-!
# Continuous capped weight for alignment-depleted diffusion

The transverse square is bounded by scalar spectral data, with the full
vorticity square as a cap. The weight is continuous through collisions
and never exceeds the coarse weight. Its positive smoothing parameter is
independent of the regularizer in the energy being differentiated.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionWeight

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeRegularizedDiffusion PancakeAnisotropyDepletion
open SpectralAnisotropyEnvelope StrainEigenvalueContinuity
open PancakeTopEigenvalueDerivative

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def weight (S : SymmetricStrain) (w : R3) (epsilon : ℝ) : ℝ :=
  min (‖w‖ ^ 2) (regularizedEnergy S epsilon w / (topGap S + epsilon))

theorem lineRemainder_sq_le_weight (S : SymmetricStrain) (w : R3)
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ‖lineRemainder (topVector S) w‖ ^ 2 ≤ weight S w epsilon := by
  apply le_min (pow_le_pow_left₀ (norm_nonneg _) (norm_lineRemainder_le _ _ (topVector_norm S)) 2)
  exact (le_div_iff₀ (add_pos_of_nonneg_of_pos (topGap_nonneg S) heps)).mpr
    (by simpa only [mul_comm] using regularizedGap_mul_lineRemainder_sq_le S w epsilon heps.le)

theorem weight_nonneg (S : SymmetricStrain) (w : R3) (epsilon : ℝ) (heps : 0 < epsilon) :
    0 ≤ weight S w epsilon :=
  (sq_nonneg _).trans (lineRemainder_sq_le_weight S w epsilon heps)

theorem weight_le_norm_sq (S : SymmetricStrain) (w : R3) (epsilon : ℝ) :
    weight S w epsilon ≤ ‖w‖ ^ 2 := min_le_left _ _

theorem weight_eq_norm_sq_of_topGap_zero (S : SymmetricStrain) (w : R3)
    (epsilon : ℝ) (heps : 0 < epsilon) (hg : topGap S = 0) :
    weight S w epsilon = ‖w‖ ^ 2 := by
  unfold weight
  rw [hg, zero_add, min_eq_left]
  exact (le_div_iff₀ heps).mpr
    (by simpa only [regularizedEnergy, mul_comm] using regularizedGap_coercive S epsilon w)

theorem weight_aligned (S : SymmetricStrain) (epsilon c : ℝ) (heps : 0 < epsilon) :
    weight S (c • topVector S) epsilon =
      epsilon / (topGap S + epsilon) * ‖c • topVector S‖ ^ 2 := by
  unfold weight
  rw [regularizedEnergy_aligned, min_eq_right]
  · ring
  · apply (div_le_iff₀ (add_pos_of_nonneg_of_pos (topGap_nonneg S) heps)).mpr
    nlinarith [mul_nonneg (topGap_nonneg S) (sq_nonneg ‖c • topVector S‖)]

theorem continuous_weight {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (w : X → R3) (epsilon : ℝ) (heps : 0 < epsilon)
    (hS : Continuous S) (hw : Continuous w) :
    Continuous (fun x ↦ weight (S x) (w x) epsilon) := by
  have hE : Continuous (fun x ↦ regularizedEnergy (S x) epsilon (w x)) := by
    simp only [regularizedEnergy, regularizedGap, sub_apply, smul_apply, one_apply_eq_self]
    exact hw.inner (((lipschitzWith_topEigenvalue.continuous.comp hS).add continuous_const).smul hw |>.sub
      ((continuous_subtype_val.comp hS).clm_apply hw))
  exact (hw.norm.pow 2).min (hE.div ((continuous_topGap.comp hS).add continuous_const)
    (fun x ↦ ne_of_gt (add_pos_of_nonneg_of_pos (topGap_nonneg (S x)) heps)))

theorem incrementRate_paid_weight (S T : SymmetricStrain) (delta epsilon : ℝ)
    (w v : R3) (hd : 0 < delta) (heps : 0 < epsilon) :
    incrementRate S T delta w v + (delta / 2) * ‖v‖ ^ 2 ≤
      regularizedEnergy T delta (w + v) - regularizedEnergy S delta w +
        (8 / delta) * ‖T.1 - S.1‖ ^ 2 * weight S w epsilon := by
  have hp := SpectralDiffusionIncrementDepletion.incrementRate_paid_depleted S T delta w v hd
  have hc := mul_le_mul_of_nonneg_left (lineRemainder_sq_le_weight S w epsilon heps)
    (by positivity : 0 ≤ (8 / delta) * ‖T.1 - S.1‖ ^ 2)
  have hs := mul_nonneg (supportingRemainder_nonneg S T) (sq_nonneg ‖lineRemainder (topVector S) w‖)
  dsimp only at hp
  linarith only [hp, hc, hs]

end Mettapedia.FluidDynamics.NavierStokes.SpectralDiffusionWeight
