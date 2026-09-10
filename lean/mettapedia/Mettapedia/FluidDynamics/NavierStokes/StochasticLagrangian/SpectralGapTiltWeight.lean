import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralTiltExcess
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedProjectorTilt

/-!
# A continuous spectral-gap weight and its collision remainder

The ramp is zero below `gamma` and one above `2 * gamma`. Its weighted
projector extends continuously through top-eigenvalue collisions. The
source estimate retains the complementary coarse cost explicitly; cutting
off the inverse gap does not discard that region of the physical balance.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeAnisotropyDepletion StrainEigenvalueContinuity SpectralDiffusionWeightLimit

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def gapCutoff (gamma g : ℝ) : ℝ := max 0 (min 1 ((g - gamma) / gamma))

theorem gapCutoff_nonneg (gamma g : ℝ) : 0 ≤ gapCutoff gamma g := le_max_left _ _

theorem gapCutoff_le_one (gamma g : ℝ) : gapCutoff gamma g ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem gapCutoff_eq_zero (gamma g : ℝ) (hg : 0 < gamma) (h : g ≤ gamma) :
    gapCutoff gamma g = 0 := by
  have hd : (g - gamma) / gamma ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hg.le
  exact max_eq_left ((min_le_right _ _).trans hd)

theorem gapCutoff_eq_one (gamma g : ℝ) (hg : 0 < gamma) (h : 2 * gamma ≤ g) :
    gapCutoff gamma g = 1 := by
  have hd : 1 ≤ (g - gamma) / gamma := (le_div_iff₀ hg).mpr (by linarith)
  simp only [gapCutoff, min_eq_left hd, max_eq_right zero_le_one]

theorem continuous_gapCutoff (gamma : ℝ) : Continuous (gapCutoff gamma) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const gamma))

def tiltWeight (gamma : ℝ) (S : SymmetricStrain) (w : R3) : ℝ :=
  gapCutoff gamma (topGap S) * ‖w‖ ^ 2 / max (topGap S) gamma ^ 2

theorem tiltWeight_nonneg (gamma : ℝ) (S : SymmetricStrain) (w : R3) :
    0 ≤ tiltWeight gamma S w := by
  unfold tiltWeight
  exact div_nonneg (mul_nonneg (gapCutoff_nonneg _ _) (sq_nonneg _)) (sq_nonneg _)

theorem tiltWeight_eq_zero (gamma : ℝ) (S : SymmetricStrain) (w : R3)
    (hg : 0 < gamma) (h : topGap S ≤ gamma) : tiltWeight gamma S w = 0 := by
  simp only [tiltWeight, gapCutoff_eq_zero gamma _ hg h, zero_mul, zero_div]

/-- The regular denominator is only used where the cutoff is zero. -/
theorem tiltWeight_eq (gamma : ℝ) (S : SymmetricStrain) (w : R3) (hg : 0 < gamma) :
    tiltWeight gamma S w = gapCutoff gamma (topGap S) * ‖w‖ ^ 2 / topGap S ^ 2 := by
  by_cases h : gamma ≤ topGap S
  · simp only [tiltWeight, max_eq_left h]
  · simp only [tiltWeight_eq_zero gamma S w hg (le_of_not_ge h),
      gapCutoff_eq_zero gamma _ hg (le_of_not_ge h), zero_mul, zero_div]

theorem continuous_tiltWeight {X : Type*} [TopologicalSpace X]
    (gamma : ℝ) (hg : 0 < gamma) (S : X → SymmetricStrain) (w : X → R3)
    (hS : Continuous S) (hw : Continuous w) : Continuous (fun x ↦ tiltWeight gamma (S x) (w x)) := by
  have hgS := continuous_topGap.comp hS
  exact (((continuous_gapCutoff gamma).comp hgS).mul (hw.norm.pow 2)).div
    ((hgS.max continuous_const).pow 2)
      (fun x ↦ pow_ne_zero 2 (ne_of_gt (hg.trans_le (le_max_right _ _))))

/-- Continuity of the weighted projector is derived, including on the
cutoff boundary; no continuous eigenvector is selected. -/
theorem continuous_weighted_projector {X : Type*} [TopologicalSpace X]
    (gamma : ℝ) (hg : 0 < gamma) (S : X → SymmetricStrain) (w : X → R3)
    (hS : Continuous S) (hw : Continuous w) :
    Continuous (fun x ↦ Real.sqrt (tiltWeight gamma (S x) (w x)) • topEigenlineProjector (S x)) := by
  classical
  have hgap := continuous_topGap.comp hS
  have ha := (continuous_tiltWeight gamma hg S w hS hw).sqrt
  have hP := continuousOn_topEigenlineProjector_comp_of_topGap_pos S hS
    {x | gamma ≤ topGap (S x)} (fun _ hx ↦ hg.trans_le hx)
  have hF : ContinuousOn (fun x ↦ Real.sqrt (tiltWeight gamma (S x) (w x)) •
      topEigenlineProjector (S x)) {x | gamma ≤ topGap (S x)} := ha.continuousOn.smul hP
  have hboundary (x : X) (hx : gamma = topGap (S x)) :
      Real.sqrt (tiltWeight gamma (S x) (w x)) • topEigenlineProjector (S x) = 0 := by
    rw [tiltWeight_eq_zero gamma (S x) (w x) hg hx.ge, Real.sqrt_zero]
    exact _root_.zero_smul ℝ (topEigenlineProjector (S x))
  have h : Continuous (fun x ↦ if gamma ≤ topGap (S x) then
      Real.sqrt (tiltWeight gamma (S x) (w x)) • topEigenlineProjector (S x) else 0) :=
    continuous_if_le continuous_const hgap hF continuousOn_const hboundary
  apply h.congr
  intro x
  by_cases hx : gamma ≤ topGap (S x)
  · rw [if_pos hx]
  · rw [if_neg hx, tiltWeight_eq_zero gamma (S x) (w x) hg (le_of_not_ge hx),
      Real.sqrt_zero]
    exact (_root_.zero_smul ℝ (topEigenlineProjector (S x))).symm

theorem continuous_weighted_tilt_sq {X : Type*} [TopologicalSpace X]
    (gamma : ℝ) (hg : 0 < gamma) (S : X → SymmetricStrain) (w : X → R3)
    (R : X → R3 →L[ℝ] R3) (hS : Continuous S) (hw : Continuous w) (hR : Continuous R) :
    Continuous (fun x ↦ tiltWeight gamma (S x) (w x) * SpectralTiltExcess.tiltNorm (S x) (R x) ^ 2) := by
  simpa only [SpectralTiltExcess.tiltNorm_eq] using
    WeightedProjectorTilt.continuous_weighted_transverse_norm_sq _
      (continuous_tiltWeight gamma hg S w hS hw) (fun _ ↦ tiltWeight_nonneg _ _ _)
      R hR (fun x ↦ PancakeSpectralFiniteDifference.topVector (S x))
      (fun _ ↦ PancakeSpectralFiniteDifference.topVector_norm _)
      (continuous_weighted_projector gamma hg S w hS hw)

/-- The collision remainder is supported below twice the chosen gap
threshold. It is retained in the source estimate, not declared small. -/
def collisionCost (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  (1 - gapCutoff gamma (topGap S)) * (2 * ‖R‖ * ‖w‖ ^ 2)

theorem collisionCost_nonneg (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ collisionCost gamma S R w :=
  mul_nonneg (sub_nonneg.mpr (gapCutoff_le_one _ _)) (by positivity)

theorem collisionCost_eq_zero (gamma : ℝ) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3)
    (hg : 0 < gamma) (h : 2 * gamma ≤ topGap S) : collisionCost gamma S R w = 0 := by
  simp only [collisionCost, gapCutoff_eq_one gamma _ hg h, sub_self, zero_mul]

/-- Convexly split the actual capped excess into the separated, weighted
tilt channel and the complementary collision-region cost. -/
theorem excess_le_weighted_tilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    SpectralTiltExcess.excess S R w ≤
      gapCutoff gamma (topGap S) *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) +
      8 * tiltWeight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2 + collisionCost gamma S R w := by
  have hc := gapCutoff_nonneg gamma (topGap S)
  have hmain : gapCutoff gamma (topGap S) * SpectralTiltExcess.excess S R w ≤
      gapCutoff gamma (topGap S) * SpectralTiltExcess.refinedCost S R w := by
    by_cases hz : gapCutoff gamma (topGap S) = 0
    · simp only [hz, zero_mul, le_refl]
    · have hsep : gamma < topGap S := lt_of_not_ge (fun h ↦ hz (gapCutoff_eq_zero _ _ hg h))
      apply mul_le_mul_of_nonneg_left _ hc
      simp only [SpectralTiltExcess.excess, if_pos (hg.trans hsep)]
      exact min_le_right _ _
  have hrest := mul_le_mul_of_nonneg_left (SpectralTiltExcess.excess_le_coarse S R w)
    (sub_nonneg.mpr (gapCutoff_le_one gamma (topGap S)))
  have hid : gapCutoff gamma (topGap S) * SpectralTiltExcess.refinedCost S R w =
      gapCutoff gamma (topGap S) *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) +
      8 * tiltWeight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2 := by
    rw [tiltWeight_eq gamma S w hg]
    unfold SpectralTiltExcess.refinedCost
    simp only [div_pow]
    ring
  rw [hid] at hmain
  unfold collisionCost
  nlinarith only [hmain, hrest]

/-- The inverse-gap channel can still be capped by the coarse source
cost. Introducing the gap cutoff need not discard that safeguard. -/
theorem excess_le_capped_weighted_tilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    SpectralTiltExcess.excess S R w ≤
      gapCutoff gamma (topGap S) *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) +
      min (2 * ‖R‖ * ‖w‖ ^ 2) (8 * tiltWeight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2) +
      collisionCost gamma S R w := by
  by_cases h : 8 * tiltWeight gamma S w * SpectralTiltExcess.tiltNorm S R ^ 2 ≤ 2 * ‖R‖ * ‖w‖ ^ 2
  · rw [min_eq_right h]
    exact excess_le_weighted_tilt_add_collision gamma hg S R w
  · rw [min_eq_left (le_of_not_ge h)]
    have ha : 0 ≤ gapCutoff gamma (topGap S) *
        (max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w) :=
      mul_nonneg (gapCutoff_nonneg _ _) (mul_nonneg (le_max_right _ _) (limitingWeight_nonneg _ _))
    linarith only [SpectralTiltExcess.excess_le_coarse S R w, ha, collisionCost_nonneg gamma S R w]

end Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight
