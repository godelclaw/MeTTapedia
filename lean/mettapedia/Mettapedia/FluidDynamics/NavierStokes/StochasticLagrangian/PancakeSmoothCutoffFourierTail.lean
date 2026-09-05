import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBufferedLocalizationStability

/-!
# Uniform finite-Fourier approximation of smooth cell cutoffs

An absolutely summable Fourier series on the three-torus converges uniformly.
This module packages that standard theorem in the exact finite scalar
reconstruction used by the pancake localization development.

The remaining scale-sensitive task is stronger: choose the approximating
finite set inside the anisotropic cutoff-margin box at scale `N`.  Absolute
summability implies that result once those boxes are proved to exhaust the
lattice.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSmoothCutoffFourierTail

open PeriodicFourierTriad
open PancakeMisalignmentEnergyBridge
open PancakeAnnularSectorProjector
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakeFiniteFourierLocalization
open PancakeBufferedAnnularMultiplier
open MeasureTheory
open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **Uniform cutoff truncation.**  If a continuous scalar cutoff has
absolutely summable Fourier coefficients, then for every positive error it
has a finite Fourier reconstruction uniformly within that error. -/
theorem exists_finiteFourierApproximation_sup
    (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hsummable : Summable (UnitAddTorus.mFourierCoeff χ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Wavevector, ∀ x : UnitAddTorus (Fin 3),
      ‖χ x - finiteScalarFourierReconstruction s
        (UnitAddTorus.mFourierCoeff χ) x‖ < ε := by
  classical
  have hsum := UnitAddTorus.hasSum_mFourier_series_of_summable hsummable
  rw [HasSum, Metric.tendsto_nhds] at hsum
  have hevent := hsum ε hε
  obtain ⟨s, hs⟩ := hevent.exists
  refine ⟨s, ?_⟩
  intro x
  have hs' :
      ‖χ - ∑ k ∈ s,
        UnitAddTorus.mFourierCoeff χ k • UnitAddTorus.mFourier k‖ < ε := by
    simpa [dist_eq_norm, norm_sub_rev] using hs
  have hpoint := (χ - ∑ k ∈ s,
    UnitAddTorus.mFourierCoeff χ k • UnitAddTorus.mFourier k).norm_coe_le_norm x
  have heq :
      χ x - finiteScalarFourierReconstruction s
          (UnitAddTorus.mFourierCoeff χ) x =
        (χ - ∑ k ∈ s,
          UnitAddTorus.mFourierCoeff χ k • UnitAddTorus.mFourier k) x := by
    simp [finiteScalarFourierReconstruction, Finset.sum_apply, mul_comm]
  rw [heq]
  exact hpoint.trans_lt hs'

/-- Every fixed lattice mode eventually lies in the normalized cutoff-margin
box under square-dyadic scaling in any fixed oriented frame. -/
theorem eventually_mode_mem_localizationShift
    (F : OrientedFrameEquiv) (p : Wavevector) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      InNormalizedPancakeShift
        localizationTransverseMargin localizationAxialMargin
        (orientedFrameSquareDyadicNormalizedMode F N p) := by
  let ξ := orientedFrameEuclideanLinearIsometryEquiv F
    (euclideanWavevectorOfWavevector p)
  let R : ℝ := max 2
    (max (4 * |ξ 0|) (max (4 * |ξ 1|) (8 * |ξ 2|)))
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt R
  have htwoR : (2 : ℝ) < N₀ :=
    lt_of_le_of_lt (le_max_left _ _) hN₀
  have htwo : (2 : ℕ) ≤ N₀ := by
    have : (2 : ℕ) < N₀ := by exact_mod_cast htwoR
    exact this.le
  refine ⟨N₀, htwo, ?_⟩
  intro N hN₀N
  have hN : 2 ≤ N := htwo.trans hN₀N
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  have hN₀NR : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
  have hx : 4 * |ξ 0| < (N₀ : ℝ) := by
    exact lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hN₀
  have hy : 4 * |ξ 1| < (N₀ : ℝ) := by
    exact lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_max_right _ _))) hN₀
  have hz : 8 * |ξ 2| < (N₀ : ℝ) := by
    exact lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_max_right _ _))) hN₀
  have hNleSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith
  change |ξ 0 / (N : ℝ)| ≤ localizationTransverseMargin ∧
    |ξ 1 / (N : ℝ)| ≤ localizationTransverseMargin ∧
      |ξ 2 / ((N : ℝ) ^ 2)| ≤ localizationAxialMargin
  simp only [localizationTransverseMargin, localizationAxialMargin]
  constructor
  · rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).2 (by nlinarith [abs_nonneg (ξ 0)])
  constructor
  · rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).2 (by nlinarith [abs_nonneg (ξ 1)])
  · rw [abs_div, abs_of_pos (sq_pos_of_pos hNR)]
    exact (div_le_iff₀ (sq_pos_of_pos hNR)).2
      (by nlinarith [abs_nonneg (ξ 2)])

/-- The scale threshold can be chosen independently of the oriented frame:
orthogonal frame changes preserve the Euclidean norm, which bounds every
rotated coordinate. -/
theorem eventually_mode_mem_localizationShift_uniformFrame
    (p : Wavevector) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ (F : OrientedFrameEquiv) (N : ℕ), N₀ ≤ N →
      InNormalizedPancakeShift
        localizationTransverseMargin localizationAxialMargin
        (orientedFrameSquareDyadicNormalizedMode F N p) := by
  let v := euclideanWavevectorOfWavevector p
  let R : ℝ := max 2 (8 * ‖v‖)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt R
  have htwoR : (2 : ℝ) < N₀ :=
    lt_of_le_of_lt (le_max_left _ _) hN₀
  have htwo : (2 : ℕ) ≤ N₀ := by
    have : (2 : ℕ) < N₀ := by exact_mod_cast htwoR
    exact this.le
  refine ⟨N₀, htwo, ?_⟩
  intro F N hN₀N
  let ξ := orientedFrameEuclideanLinearIsometryEquiv F v
  have hcoord (i : Fin 3) : |ξ i| ≤ ‖v‖ := by
    calc
      |ξ i| = ‖ξ i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ξ‖ := PiLp.norm_apply_le ξ i
      _ = ‖v‖ := (orientedFrameEuclideanLinearIsometryEquiv F).norm_map v
  have hN : 2 ≤ N := htwo.trans hN₀N
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  have hN₀NR : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
  have hnorm : 8 * ‖v‖ < (N₀ : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN₀
  have hx : 4 * |ξ 0| < (N₀ : ℝ) := by
    nlinarith [hcoord 0, norm_nonneg v]
  have hy : 4 * |ξ 1| < (N₀ : ℝ) := by
    nlinarith [hcoord 1, norm_nonneg v]
  have hz : 8 * |ξ 2| < (N₀ : ℝ) := by
    nlinarith [hcoord 2, norm_nonneg v]
  have hNleSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith
  change |ξ 0 / (N : ℝ)| ≤ localizationTransverseMargin ∧
    |ξ 1 / (N : ℝ)| ≤ localizationTransverseMargin ∧
      |ξ 2 / ((N : ℝ) ^ 2)| ≤ localizationAxialMargin
  simp only [localizationTransverseMargin, localizationAxialMargin]
  constructor
  · rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).2 (by nlinarith [abs_nonneg (ξ 0)])
  constructor
  · rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).2 (by nlinarith [abs_nonneg (ξ 1)])
  · rw [abs_div, abs_of_pos (sq_pos_of_pos hNR)]
    exact (div_le_iff₀ (sq_pos_of_pos hNR)).2
      (by nlinarith [abs_nonneg (ξ 2)])

/-- A finite set of cutoff modes eventually fits inside the fixed normalized
margin box, uniformly for all larger square-dyadic scales. -/
theorem eventually_finset_mem_localizationShift
    (F : OrientedFrameEquiv) (s : Finset Wavevector) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p ∈ s,
      InNormalizedPancakeShift
        localizationTransverseMargin localizationAxialMargin
        (orientedFrameSquareDyadicNormalizedMode F N p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨2, le_rfl, by simp⟩
  | @insert p s hp ih =>
      obtain ⟨Np, hNpTwo, hNp⟩ := eventually_mode_mem_localizationShift F p
      obtain ⟨Ns, hNsTwo, hNs⟩ := ih
      refine ⟨max Np Ns, le_max_of_le_left hNpTwo, ?_⟩
      intro N hmax q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hqs
      · exact hNp N ((le_max_left _ _).trans hmax)
      · exact hNs N ((le_max_right _ _).trans hmax) q hqs

/-- The preceding finite-support threshold is uniform over every oriented
frame. -/
theorem eventually_finset_mem_localizationShift_uniformFrame
    (s : Finset Wavevector) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), N₀ ≤ N → ∀ p ∈ s,
        InNormalizedPancakeShift
          localizationTransverseMargin localizationAxialMargin
          (orientedFrameSquareDyadicNormalizedMode F N p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨2, le_rfl, by simp⟩
  | @insert p s hp ih =>
      obtain ⟨Np, hNpTwo, hNp⟩ :=
        eventually_mode_mem_localizationShift_uniformFrame p
      obtain ⟨Ns, hNsTwo, hNs⟩ := ih
      refine ⟨max Np Ns, le_max_of_le_left hNpTwo, ?_⟩
      intro F N hmax q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hqs
      · exact hNp F N ((le_max_left _ _).trans hmax)
      · exact hNs F N ((le_max_right _ _).trans hmax) q hqs

/-- **Scale-compatible cutoff approximation.**  An absolutely summable
Fourier cutoff admits one uniformly accurate finite approximation whose whole
support lies in the required localization-margin box at every sufficiently
large square-dyadic scale. -/
theorem exists_eventually_margin_finiteFourierApproximation
    (F : OrientedFrameEquiv) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hsummable : Summable (UnitAddTorus.mFourierCoeff χ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Wavevector, ∃ N₀ : ℕ,
      2 ≤ N₀ ∧
      (∀ x : UnitAddTorus (Fin 3),
        ‖χ x - finiteScalarFourierReconstruction s
          (UnitAddTorus.mFourierCoeff χ) x‖ < ε) ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ p ∈ s,
        InNormalizedPancakeShift
          localizationTransverseMargin localizationAxialMargin
          (orientedFrameSquareDyadicNormalizedMode F N p) := by
  obtain ⟨s, hs⟩ := exists_finiteFourierApproximation_sup χ hsummable hε
  obtain ⟨N₀, hN₀, hmargin⟩ := eventually_finset_mem_localizationShift F s
  exact ⟨s, N₀, hN₀, hs, hmargin⟩

/-- The scale-compatible approximation can be selected uniformly over all
oriented frames.  This matters when the frozen strain frame varies from cell
to cell or with the dyadic scale. -/
theorem exists_eventually_margin_finiteFourierApproximation_uniformFrame
    (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hsummable : Summable (UnitAddTorus.mFourierCoeff χ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Wavevector, ∃ N₀ : ℕ,
      2 ≤ N₀ ∧
      (∀ x : UnitAddTorus (Fin 3),
        ‖χ x - finiteScalarFourierReconstruction s
          (UnitAddTorus.mFourierCoeff χ) x‖ < ε) ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), N₀ ≤ N → ∀ p ∈ s,
        InNormalizedPancakeShift
          localizationTransverseMargin localizationAxialMargin
          (orientedFrameSquareDyadicNormalizedMode F N p) := by
  obtain ⟨s, hs⟩ := exists_finiteFourierApproximation_sup χ hsummable hε
  obtain ⟨N₀, hN₀, hmargin⟩ :=
    eventually_finset_mem_localizationShift_uniformFrame s
  exact ⟨s, N₀, hN₀, hs, hmargin⟩

end PancakeSmoothCutoffFourierTail
end NavierStokes
end FluidDynamics
end Mettapedia
