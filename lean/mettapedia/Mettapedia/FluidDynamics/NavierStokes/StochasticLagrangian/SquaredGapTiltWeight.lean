import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GapTruncatedProjector
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedLineFreezing
import Mettapedia.Analysis.LocallyLipschitz

/-!
# A gap weight with quantitatively regular square root

The square of the linear ramp replaces the linear ramp in the energy
weight. Its square root is then linear at the cutoff boundary. The
weighted projector satisfies an explicit two-state estimate through
collisions, and the source bound retains the full complementary cost.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference SpectralGapTiltWeight GapTruncatedProjector
open SpectralDiffusionWeightLimit PancakeAnisotropyDepletion SpectralTiltFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def amplitude (gamma : ℝ) (S : SymmetricStrain) (w : R3) : ℝ :=
  gapCutoff gamma (topGap S) * ‖w‖ / max (topGap S) gamma

def weight (gamma : ℝ) (S : SymmetricStrain) (w : R3) : ℝ := amplitude gamma S w ^ 2

def weightedProjector (gamma : ℝ) (S : SymmetricStrain) (w : R3) : R3 →L[ℝ] R3 :=
  ‖w‖ • inverseGapProjector gamma S

theorem weight_eq_cutoff_mul_tiltWeight (gamma : ℝ) (S : SymmetricStrain) (w : R3) :
    weight gamma S w = gapCutoff gamma (topGap S) * tiltWeight gamma S w := by
  unfold weight amplitude tiltWeight
  ring

theorem weight_le_tiltWeight (gamma : ℝ) (S : SymmetricStrain) (w : R3) :
    weight gamma S w ≤ tiltWeight gamma S w := by
  rw [weight_eq_cutoff_mul_tiltWeight]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (gapCutoff_le_one gamma (topGap S))
    (tiltWeight_nonneg gamma S w)

theorem amplitude_nonneg (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) (w : R3) :
    0 ≤ amplitude gamma S w :=
  div_nonneg (mul_nonneg (gapCutoff_nonneg _ _) (norm_nonneg _))
    (hg.trans_le (le_max_right _ _)).le

theorem sqrt_weight (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) (w : R3) :
    Real.sqrt (weight gamma S w) = amplitude gamma S w :=
  Real.sqrt_sq (amplitude_nonneg gamma hg S w)

theorem weightedProjector_eq (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) (w : R3) :
    weightedProjector gamma S w = Real.sqrt (weight gamma S w) • topEigenlineProjector S := by
  rw [sqrt_weight gamma hg]
  unfold weightedProjector inverseGapProjector gatedProjector amplitude
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem norm_weightedProjector_sub_le (gamma : ℝ) (hg : 0 < gamma)
    (A B : SymmetricStrain) (w v : R3) :
    ‖weightedProjector gamma A w - weightedProjector gamma B v‖ ≤
      ‖w - v‖ / gamma + 20 * ‖v‖ * ‖A.1 - B.1‖ / gamma ^ 2 := by
  have hid : weightedProjector gamma A w - weightedProjector gamma B v =
      (‖w‖ - ‖v‖) • inverseGapProjector gamma A +
      ‖v‖ • (inverseGapProjector gamma A - inverseGapProjector gamma B) := by
    unfold weightedProjector
    module
  rw [hid]
  have hn := norm_add_le ((‖w‖ - ‖v‖) • inverseGapProjector gamma A)
    (‖v‖ • (inverseGapProjector gamma A - inverseGapProjector gamma B))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)] at hn
  have hfirst := mul_le_mul (abs_norm_sub_norm_le w v) (norm_inverseGapProjector_le gamma hg A)
    (norm_nonneg _) (norm_nonneg _)
  have hsecond := mul_le_mul_of_nonneg_left (norm_inverseGapProjector_sub_le gamma hg A B) (norm_nonneg v)
  calc
    _ ≤ ‖w - v‖ * (1 / gamma) + ‖v‖ * ((20 / gamma ^ 2) * ‖A.1 - B.1‖) :=
      hn.trans (add_le_add hfirst hsecond)
    _ = _ := by ring

theorem weighted_lineDistance_le (gamma : ℝ) (hg : 0 < gamma)
    (A B : SymmetricStrain) (w v : R3) :
    weight gamma A w * lineDistanceSq (topVector A) (topVector B) ≤
      4 * (‖w - v‖ / gamma) ^ 2 + 1600 * (‖v‖ * ‖A.1 - B.1‖ / gamma ^ 2) ^ 2 := by
  have hline := WeightedLineFreezing.mul_lineDistanceSq_le
    (topVector A) (topVector B) (topVector_norm A) (topVector_norm B)
    (weight gamma A w) (weight gamma B v) (sq_nonneg _)
  change _ ≤ 2 * ‖Real.sqrt (weight gamma A w) • topEigenlineProjector A -
    Real.sqrt (weight gamma B v) • topEigenlineProjector B‖ ^ 2 at hline
  rw [← weightedProjector_eq gamma hg, ← weightedProjector_eq gamma hg] at hline
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_weightedProjector_sub_le gamma hg A B w v) 2
  have hs := sq_nonneg (‖w - v‖ / gamma - 20 * ‖v‖ * ‖A.1 - B.1‖ / gamma ^ 2)
  simp only [div_eq_mul_inv] at h hs ⊢
  nlinarith only [hline, h, hs]

theorem continuous_weightedProjector {X : Type*} [TopologicalSpace X]
    (gamma : ℝ) (hg : 0 < gamma) (S : X → SymmetricStrain) (w : X → R3)
    (hS : Continuous S) (hw : Continuous w) :
    Continuous (fun x ↦ weightedProjector gamma (S x) (w x)) := by
  exact hw.norm.smul ((lipschitzWith_inverseGapProjector gamma hg).continuous.comp hS)

theorem locallyLipschitz_weightedProjector {X : Type*} [PseudoMetricSpace X]
    (gamma : ℝ) (hg : 0 < gamma) (S : X → SymmetricStrain) (w : X → R3)
    (hS : LocallyLipschitz (fun x ↦ (S x).1)) (hw : LocallyLipschitz w) :
    LocallyLipschitz (fun x ↦ weightedProjector gamma (S x) (w x)) := by
  change LocallyLipschitz (fun x ↦ ‖w x‖ • inverseGapProjector gamma (S x))
  have hSL : LocallyLipschitz S := fun x ↦ hS x
  have hP : LocallyLipschitz (fun x ↦ inverseGapProjector gamma (S x)) :=
    (lipschitzWith_inverseGapProjector gamma hg).locallyLipschitz.comp hSL
  have hn : LocallyLipschitz (fun x ↦ ‖w x‖) := lipschitzWith_one_norm.locallyLipschitz.comp hw
  exact hn.smul_real hP

/-- A derivative estimate obtained from the two-state bound. No derivative
of a signed eigenvector is introduced, and no positive top gap is required.
Differentiability of the weighted field can be supplied almost everywhere
by its local Lipschitz regularity. -/
theorem norm_derivative_weightedProjector_le (gamma : ℝ) (hg : 0 < gamma)
    (S : ℝ → SymmetricStrain) (w : ℝ → R3) (t : ℝ)
    (Sdot Mdot : R3 →L[ℝ] R3) (wdot : R3)
    (hS : HasDerivAt (fun s ↦ (S s).1) Sdot t) (hw : HasDerivAt w wdot t)
    (hM : HasDerivAt (fun s ↦ weightedProjector gamma (S s) (w s)) Mdot t) :
    ‖Mdot‖ ≤ ‖wdot‖ / gamma + 20 * ‖w t‖ * ‖Sdot‖ / gamma ^ 2 := by
  have hlim := (hw.tendsto_slope.norm.div_const gamma).add
    ((hS.tendsto_slope.norm.const_mul (20 * ‖w t‖)).div_const (gamma ^ 2))
  apply le_of_tendsto_of_tendsto' hM.tendsto_slope.norm hlim
  intro s
  have h := mul_le_mul_of_nonneg_left
    (norm_weightedProjector_sub_le gamma hg (S s) (S t) (w s) (w t))
    (norm_nonneg ((s - t)⁻¹))
  simp only [slope_def_module, norm_smul]
  calc
    _ ≤ ‖(s - t)⁻¹‖ * (‖w s - w t‖ / gamma + 20 * ‖w t‖ * ‖(S s).1 - (S t).1‖ / gamma ^ 2) := h
    _ = _ := by ring

theorem continuous_weight {X : Type*} [TopologicalSpace X]
    (gamma : ℝ) (hg : 0 < gamma) (S : X → SymmetricStrain) (w : X → R3)
    (hS : Continuous S) (hw : Continuous w) : Continuous (fun x ↦ weight gamma (S x) (w x)) := by
  have hgap := StrainEigenvalueContinuity.continuous_topGap.comp hS
  exact ((((continuous_gapCutoff gamma).comp hgap).mul hw.norm).div
    (hgap.max continuous_const) (fun x ↦ ne_of_gt (hg.trans_le (le_max_right _ _)))).pow 2

theorem weight_eq (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) (w : R3) :
    weight gamma S w = gapCutoff gamma (topGap S) ^ 2 * ‖w‖ ^ 2 / topGap S ^ 2 := by
  by_cases h : gamma ≤ topGap S
  · simp only [weight, amplitude, max_eq_left h, div_pow, mul_pow]
  · simp only [weight, amplitude, gapCutoff_eq_zero gamma _ hg (le_of_not_ge h),
      zero_mul, zero_div, zero_pow (by decide : 2 ≠ 0)]

def collisionCost (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  (1 - gapCutoff gamma (topGap S) ^ 2) * (2 * ‖R‖ * ‖w‖ ^ 2)

/-- Regularizing the square root transfers an explicit additional cost
to the transition region; it is not a free reduction of the source. -/
theorem collisionCost_eq_linear_add (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    collisionCost gamma S R w = SpectralGapTiltWeight.collisionCost gamma S R w +
      gapCutoff gamma (topGap S) * (1 - gapCutoff gamma (topGap S)) * (2 * ‖R‖ * ‖w‖ ^ 2) := by
  unfold collisionCost SpectralGapTiltWeight.collisionCost
  ring

theorem collisionCost_nonneg (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ collisionCost gamma S R w := by
  have h := gapCutoff_nonneg gamma (topGap S)
  have h1 := gapCutoff_le_one gamma (topGap S)
  exact mul_nonneg (by nlinarith) (by positivity)

theorem excess_le_weighted_tilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    SpectralTiltExcess.excess S R w ≤
      gapCutoff gamma (topGap S) ^ 2 *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) +
      8 * weight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2 + collisionCost gamma S R w := by
  have hmain : gapCutoff gamma (topGap S) ^ 2 * SpectralTiltExcess.excess S R w ≤
      gapCutoff gamma (topGap S) ^ 2 * SpectralTiltExcess.refinedCost S R w := by
    by_cases hz : gapCutoff gamma (topGap S) = 0
    · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl]
    · have hsep : gamma < topGap S := lt_of_not_ge (fun h ↦ hz (gapCutoff_eq_zero _ _ hg h))
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simp only [SpectralTiltExcess.excess, if_pos (hg.trans hsep)]
      exact min_le_right _ _
  have htheta : 0 ≤ 1 - gapCutoff gamma (topGap S) ^ 2 := by
    have h := gapCutoff_nonneg gamma (topGap S)
    have h1 := gapCutoff_le_one gamma (topGap S)
    nlinarith
  have hrest := mul_le_mul_of_nonneg_left (SpectralTiltExcess.excess_le_coarse S R w) htheta
  have hid : gapCutoff gamma (topGap S) ^ 2 * SpectralTiltExcess.refinedCost S R w =
      gapCutoff gamma (topGap S) ^ 2 *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) +
      8 * weight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2 := by
    rw [weight_eq gamma hg]
    unfold SpectralTiltExcess.refinedCost
    simp only [div_pow]
    ring
  rw [hid] at hmain
  unfold collisionCost
  nlinarith only [hmain, hrest]

end Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight
