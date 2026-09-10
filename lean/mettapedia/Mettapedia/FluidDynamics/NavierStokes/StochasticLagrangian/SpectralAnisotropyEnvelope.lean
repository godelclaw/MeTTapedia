import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnisotropyDepletion

/-!
# A continuous alignment-depleted anisotropy envelope

Regularized transverse coercivity bounds the line remainder by scalar
energy and gap data. Taking the minimum with the coarse norm envelope
retains a bound through collisions while improving it near alignment.
The regularizer remains positive and is not sent to zero here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralAnisotropyEnvelope

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeRegularizedDiffusion
open PancakeAnisotropyDepletion PancakeTransverseEnergyCoercivity PancakeTransverseEnergyFreezing
open PancakeRegularizedMaterialRate PancakeTopEigenvalueDerivative StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem topGap_mul_lineRemainder_sq_le (S : SymmetricStrain) (w : R3) :
    topGap S * ‖lineRemainder (topVector S) w‖ ^ 2 ≤ topSpectralDefect S w := by
  have h := gap_mul_transverseLineEnergy_le_strainDefect S.1 S.2 w (topGap S)
    le_rfl (topGap_le_top_sub_third S)
  rw [norm_lineRemainder_sq _ _ (topVector_norm S)]
  simpa only [topVector, transverseLineEnergy, real_inner_comm,
    topSpectralDefect, spectralDefect, topEigenvalue] using h

theorem regularizedGap_mul_lineRemainder_sq_le (S : SymmetricStrain) (w : R3)
    (delta : ℝ) (hd : 0 ≤ delta) :
    (topGap S + delta) * ‖lineRemainder (topVector S) w‖ ^ 2 ≤ regularizedEnergy S delta w := by
  have hg := topGap_mul_lineRemainder_sq_le S w
  have hw := norm_lineRemainder_le (topVector S) w (topVector_norm S)
  have hdw := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hw 2) hd
  rw [regularizedEnergy_eq]
  nlinarith

theorem norm_lineRemainder_le_sqrt (S : SymmetricStrain) (w : R3)
    (delta : ℝ) (hd : 0 < delta) :
    ‖lineRemainder (topVector S) w‖ ≤
      Real.sqrt (regularizedEnergy S delta w / (topGap S + delta)) := by
  have hg : 0 < topGap S + delta := add_pos_of_nonneg_of_pos (topGap_nonneg S) hd
  have hq : ‖lineRemainder (topVector S) w‖ ^ 2 ≤
      regularizedEnergy S delta w / (topGap S + delta) := (le_div_iff₀ hg).mpr
    (by simpa only [mul_comm] using regularizedGap_mul_lineRemainder_sq_le S w delta hd.le)
  exact Real.le_sqrt_of_sq_le hq

def envelope (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (delta : ℝ) : ℝ :=
  min (2 * ‖R‖ * ‖w‖ ^ 2)
    (4 * ‖R‖ * ‖w‖ * Real.sqrt (regularizedEnergy S delta w / (topGap S + delta)))

theorem abs_remainderAnisotropy_le_envelope (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (delta : ℝ) (hd : 0 < delta) :
    |remainderAnisotropy R (topVector S) w| ≤ envelope S R w delta := by
  apply le_min (abs_remainderAnisotropy_le R _ w (topVector_norm S))
  exact (abs_remainderAnisotropy_depleted R _ w (topVector_norm S)).trans
    (mul_le_mul_of_nonneg_left (norm_lineRemainder_le_sqrt S w delta hd) (by positivity))

theorem envelope_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (delta : ℝ) :
    0 ≤ envelope S R w delta := by unfold envelope; positivity

theorem envelope_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (delta : ℝ) :
    envelope S R w delta ≤ 2 * ‖R‖ * ‖w‖ ^ 2 := min_le_left _ _

/-- A quantified gain when alignment energy is small relative to the
regularized gap. The smallness condition is explicit, not automatic. -/
theorem envelope_le_of_energy_le (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3)
    (delta c : ℝ) (hd : 0 < delta) (hc : 0 ≤ c)
    (hE : regularizedEnergy S delta w ≤ c ^ 2 * (topGap S + delta) * ‖w‖ ^ 2) :
    envelope S R w delta ≤ 4 * c * ‖R‖ * ‖w‖ ^ 2 := by
  have hg : 0 < topGap S + delta := add_pos_of_nonneg_of_pos (topGap_nonneg S) hd
  have hq : regularizedEnergy S delta w / (topGap S + delta) ≤ (c * ‖w‖) ^ 2 := by
    apply (div_le_iff₀ hg).mpr
    nlinarith only [hE]
  have hs : Real.sqrt (regularizedEnergy S delta w / (topGap S + delta)) ≤ c * ‖w‖ :=
    (Real.sqrt_le_left (mul_nonneg hc (norm_nonneg w))).mpr hq
  calc
    _ ≤ 4 * ‖R‖ * ‖w‖ * Real.sqrt (regularizedEnergy S delta w / (topGap S + delta)) := min_le_right _ _
    _ ≤ 4 * ‖R‖ * ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- At a top-eigenvalue collision this envelope falls back to the coarse
bound; it does not claim a line-coherence gain inside a multiple eigenspace. -/
theorem envelope_eq_coarse_of_topGap_zero (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (delta : ℝ) (hd : 0 < delta) (hg : topGap S = 0) :
    envelope S R w delta = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  have hE := regularizedGap_coercive S delta w
  have hq : ‖w‖ ^ 2 ≤ regularizedEnergy S delta w / delta :=
    (le_div_iff₀ hd).mpr (by simpa only [regularizedEnergy, mul_comm] using hE)
  have hr := Real.le_sqrt_of_sq_le hq
  unfold envelope
  rw [hg, zero_add, min_eq_left]
  have h := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 4 * ‖R‖ * ‖w‖)
  nlinarith [mul_nonneg (norm_nonneg R) (sq_nonneg ‖w‖)]

theorem regularizedEnergy_aligned (S : SymmetricStrain) (delta alpha : ℝ) :
    regularizedEnergy S delta (alpha • topVector S) = delta * ‖alpha • topVector S‖ ^ 2 := by
  have he : S.1 (topVector S) = topEigenvalue S • topVector S :=
    (PancakeStrainSpectralFrame.orderedEigenframe S.1 S.2).apply_eigenbasis 0
  simp only [regularizedEnergy_eq, topSpectralDefect, spectralDefect, map_smul, he,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, sq_abs, topVector_norm, one_pow, mul_one]
  ring

/-- A concrete improvement: aligned vorticity and a gap at least 63δ
give an anisotropy envelope at most one quarter of the coarse bound. -/
theorem envelope_le_quarter_coarse_of_aligned (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (delta alpha : ℝ) (hd : 0 < delta) (hg : 63 * delta ≤ topGap S) :
    envelope S R (alpha • topVector S) delta ≤
      (1 / 4 : ℝ) * (2 * ‖R‖ * ‖alpha • topVector S‖ ^ 2) := by
  have hE : regularizedEnergy S delta (alpha • topVector S) ≤
      (1 / 8 : ℝ) ^ 2 * (topGap S + delta) * ‖alpha • topVector S‖ ^ 2 := by
    rw [regularizedEnergy_aligned]
    have h := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖alpha • topVector S‖)
    nlinarith
  have h := envelope_le_of_energy_le S R (alpha • topVector S) delta (1 / 8) hd (by norm_num) hE
  nlinarith

theorem continuous_envelope {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (delta : ℝ) (hd : 0 < delta) (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Continuous (fun x ↦ envelope (S x) (R x) (w x) delta) := by
  have hg : Continuous (fun x ↦ topGap (S x) + delta) :=
    (continuous_topGap.comp hS).add continuous_const
  have hE : Continuous (fun x ↦ regularizedEnergy (S x) delta (w x)) := by
    simp only [regularizedEnergy, regularizedGap, sub_apply, smul_apply, one_apply_eq_self]
    exact hw.inner (((lipschitzWith_topEigenvalue.continuous.comp hS).add continuous_const).smul hw |>.sub
      ((continuous_subtype_val.comp hS).clm_apply hw))
  have hroot := (hE.div hg (fun x ↦ ne_of_gt (add_pos_of_nonneg_of_pos (topGap_nonneg (S x)) hd))).sqrt
  exact ((continuous_const.mul hR.norm).mul (hw.norm.pow 2)).min
    (((continuous_const.mul hR.norm).mul hw.norm).mul hroot)

end Mettapedia.FluidDynamics.NavierStokes.SpectralAnisotropyEnvelope
