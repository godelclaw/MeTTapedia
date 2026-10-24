import Mettapedia.FluidDynamics.NavierStokes.ModeStateObservableClass
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Manuscript-Flavored Chart Datum for the NS Grassroots Lane

This file upgrades the geometric finite-mode model into a closer analogue of
Appendix D.4 from the manuscript:

- a squared weighted chart radius;
- a bounded linear observable `ℓ`;
- the chart-cutoff datum `W₀ = χ · ℓ`;
- the Cole-Hopf datum `φ = exp(-W₀ / (2ν))`.

Everything remains finite-mode and local.  The point is to turn the D.4
formula shape into a concrete Lean model that feeds the already-existing
approximation and topology shells.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped BigOperators

section ManuscriptChartDatum

/-- Weighted squared contribution of the `n`-th mode to the chart radius. -/
def radiusSqTerm (x : ModeState) (n : ℕ) : ℝ :=
  (x.coeff n) ^ 2 * modeWeight n

/-- Squared weighted chart radius, closer to the manuscript's `‖κ(g)‖²`. -/
def radiusSq (x : ModeState) : ℝ :=
  ∑' n, radiusSqTerm x n

theorem summable_radiusSqTerm (x : ModeState) : Summable (radiusSqTerm x) :=
  (squareModeObservable geometricModeWeights).summable_term x

theorem radiusSq_truncate_eq_sum (x : ModeState) (N : ℕ) :
    radiusSq (truncateModes N x) = ∑ n ∈ Finset.range N, radiusSqTerm x n :=
  (squareModeObservable geometricModeWeights).value_truncate_eq_partial (by
    simp [squareModeObservable]) N x

theorem truncateModes_radiusSq_tendsto (x : ModeState) :
    Tendsto (fun N => radiusSq (truncateModes N x)) atTop (nhds (radiusSq x)) :=
  (squareModeObservable geometricModeWeights).approximationData.radius_tendsto x

/-- Concrete D.4-style approximation package on the geometric mode state. -/
def manuscriptApproximationData (L : WeightedObservable) :
    CutoffApproximationData radiusSq (matchingObservable L) where
  approx := truncateModes
  radius_tendsto := truncateModes_radiusSq_tendsto
  statistic_tendsto := truncateModes_matchingObservable_tendsto L

/-- Concrete chart-cutoff datum `W₀ = χ · ℓ`. -/
def manuscriptW0 (cutoff : ℝ → ℝ) (L : WeightedObservable) : ModeState → ℝ :=
  cutoffPotential cutoff radiusSq (matchingObservable L)

/-- Concrete chart heat datum `φ = exp(-W₀ / (2ν))`. -/
def manuscriptPhi (ν : ℝ) (cutoff : ℝ → ℝ) (L : WeightedObservable) : ModeState → ℝ :=
  coleHopfPhi ν (manuscriptW0 cutoff L)

theorem manuscriptW0_tendsto
    (L : WeightedObservable) {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto (fun N => manuscriptW0 cutoff L (truncateModes N x))
      Filter.atTop (nhds (manuscriptW0 cutoff L x)) := by
  exact (manuscriptApproximationData L).cutoffPotential_tendsto hcutoff x

theorem manuscriptPhi_tendsto
    (L : WeightedObservable) {ν : ℝ} {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto (fun N => manuscriptPhi ν cutoff L (truncateModes N x))
      Filter.atTop (nhds (manuscriptPhi ν cutoff L x)) := by
  exact (manuscriptApproximationData L).coleHopfPhi_tendsto hcutoff x

theorem manuscriptW0_eq_zero_of_cutoff_eq_zero
    (L : WeightedObservable) {cutoff : ℝ → ℝ} {x : ModeState}
    (hcutoff : cutoff (radiusSq x) = 0) :
    manuscriptW0 cutoff L x = 0 := by
  simp [manuscriptW0, cutoffPotential, hcutoff]

theorem abs_manuscriptW0_le
    (L : WeightedObservable) {cutoff : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    |manuscriptW0 cutoff L x| ≤ B * observableEnvelopeSum L := by
  calc
    |manuscriptW0 cutoff L x|
      = |cutoff (radiusSq x)| * |matchingObservable L x| := by
          simp [manuscriptW0, cutoffPotential, abs_mul]
    _ ≤ B * observableEnvelopeSum L := by
      refine mul_le_mul (hcutoff _) (matchingObservable_abs_le L x) ?_ hB
      exact abs_nonneg _

theorem manuscriptPhi_pos
    (L : WeightedObservable) (ν : ℝ) {cutoff : ℝ → ℝ} (x : ModeState) :
    0 < manuscriptPhi ν cutoff L x := by
  simp [manuscriptPhi, manuscriptW0, coleHopfPhi, coleHopfScalar, Real.exp_pos]

theorem manuscriptPhi_lower_bound
    (L : WeightedObservable) {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    Real.exp (-(B * observableEnvelopeSum L) / (2 * ν)) ≤ manuscriptPhi ν cutoff L x := by
  have hW := abs_manuscriptW0_le L hB hcutoff x
  have hW' := abs_le.mp hW
  have harg :
      -(B * observableEnvelopeSum L) / (2 * ν) ≤ -(manuscriptW0 cutoff L x) / (2 * ν) := by
    have hnum : -(B * observableEnvelopeSum L) ≤ -(manuscriptW0 cutoff L x) := by
      exact neg_le_neg hW'.2
    exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2 * ν)
  simpa [manuscriptPhi, manuscriptW0, coleHopfPhi, coleHopfScalar] using
    Real.exp_le_exp.mpr harg

theorem manuscriptPhi_upper_bound
    (L : WeightedObservable) {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    manuscriptPhi ν cutoff L x ≤ Real.exp ((B * observableEnvelopeSum L) / (2 * ν)) := by
  have hW := abs_manuscriptW0_le L hB hcutoff x
  have hW' := abs_le.mp hW
  have harg :
      -(manuscriptW0 cutoff L x) / (2 * ν) ≤ (B * observableEnvelopeSum L) / (2 * ν) := by
    have hnum : -(manuscriptW0 cutoff L x) ≤ B * observableEnvelopeSum L := by
      have := neg_le_neg hW'.1
      simpa using this
    exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2 * ν)
  simpa [manuscriptPhi, manuscriptW0, coleHopfPhi, coleHopfScalar] using
    Real.exp_le_exp.mpr harg

theorem manuscriptPhi_bounded
    (L : WeightedObservable) {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    Real.exp (-(B * observableEnvelopeSum L) / (2 * ν)) ≤ manuscriptPhi ν cutoff L x ∧
      manuscriptPhi ν cutoff L x ≤ Real.exp ((B * observableEnvelopeSum L) / (2 * ν)) := by
  exact ⟨manuscriptPhi_lower_bound L hν hB hcutoff x,
    manuscriptPhi_upper_bound L hν hB hcutoff x⟩

end ManuscriptChartDatum

end NavierStokes
end FluidDynamics
end Mettapedia
