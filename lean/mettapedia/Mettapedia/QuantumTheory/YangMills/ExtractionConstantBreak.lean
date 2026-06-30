import Mettapedia.QuantumTheory.YangMills.RGBootstrap

/-!
# Yang-Mills Extraction Constant Break

The manuscript's extended-extraction contraction uses the advertised numerical
audit `2224 * 2^-13 < 1`.  That arithmetic remains true when `2224` is supplied
as an input.  This file records the separate obstruction: the manuscript's own
displayed extraction-projection series at `r1 / r0 = 1/2` is already enormous
in the one-variable lower-bound scenario, so the corresponding `C₁` is not a
contraction constant at `dmax = 16`.

This is a route-step audit, not a Yang-Mills mass-gap theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Manuscript factor map from an extraction-projection norm bound to the RG
recursion constant at block factor `b = 2`, using `1.65 = 33/20`,
`Ccumulant = 3 b^4`, and `Crecomb = 14`. -/
def manuscriptC1FromCextract (Cextract : ℝ) : ℝ :=
  ((33 : ℝ) / 20) * (3 * (2 : ℝ) ^ 4) * 14 * Cextract

/-- The one-variable lower-bound value of the displayed extraction series
`sum_{d=0}^{16} (1/2)^(-d) = 2^17 - 1`. -/
def manuscriptExtractionSeriesLowerBound16 : ℝ :=
  (2 : ℝ) ^ 17 - 1

/-- The RG-recursion constant obtained from the displayed extraction series
lower bound at `dmax = 16`. -/
def manuscriptSeriesC1LowerBound16 : ℝ :=
  manuscriptC1FromCextract manuscriptExtractionSeriesLowerBound16

theorem manuscriptExtractionSeriesLowerBound16_eq :
    manuscriptExtractionSeriesLowerBound16 = 131071 := by
  norm_num [manuscriptExtractionSeriesLowerBound16]

theorem manuscriptExtractionSeriesLowerBound16_exceeds_asserted_two :
    (2 : ℝ) < manuscriptExtractionSeriesLowerBound16 := by
  norm_num [manuscriptExtractionSeriesLowerBound16]

theorem manuscriptSeriesC1LowerBound16_eq :
    manuscriptSeriesC1LowerBound16 = (726657624 : ℝ) / 5 := by
  norm_num [manuscriptSeriesC1LowerBound16, manuscriptC1FromCextract,
    manuscriptExtractionSeriesLowerBound16]

theorem manuscriptSeriesC1LowerBound16_exceeds_advertised :
    (2224 : ℝ) < manuscriptSeriesC1LowerBound16 := by
  norm_num [manuscriptSeriesC1LowerBound16, manuscriptC1FromCextract,
    manuscriptExtractionSeriesLowerBound16]

/-- At the manuscript's `b = 2, dmax = 16` endpoint, contraction forces the
constant below `2^(16-3) = 8192`. -/
theorem not_rgContraction_two_sixteen_of_constant_ge_8192
    {C : ℝ} (hC : (8192 : ℝ) ≤ C) :
    ¬ HasExtendedExtractionContraction C 2 16 := by
  intro h
  have hlt : C < (2 : ℝ) ^ (16 - 3) :=
    rgContraction_two_forces_constant_lt_pow_of_three_le
      (C := C) (dmax := 16) (by norm_num) h
  norm_num at hlt
  exact (not_lt_of_ge hC) hlt

theorem manuscriptSeriesC1LowerBound16_ge_threshold :
    (8192 : ℝ) ≤ manuscriptSeriesC1LowerBound16 := by
  norm_num [manuscriptSeriesC1LowerBound16, manuscriptC1FromCextract,
    manuscriptExtractionSeriesLowerBound16]

/-- Using the displayed extraction series lower-bound constant, the advertised
extended-extraction contraction certificate fails at `dmax = 16`. -/
theorem not_rgContraction_manuscriptSeriesC1LowerBound_two_sixteen :
    ¬ HasExtendedExtractionContraction manuscriptSeriesC1LowerBound16 2 16 := by
  exact
    not_rgContraction_two_sixteen_of_constant_ge_8192
      manuscriptSeriesC1LowerBound16_ge_threshold

theorem manuscriptSeriesGain_two_sixteen_eq :
    manuscriptSeriesC1LowerBound16 * irrelevantScale 2 16 =
      (90832203 : ℝ) / 5120 := by
  rw [irrelevantScale_two_sixteen]
  norm_num [manuscriptSeriesC1LowerBound16, manuscriptC1FromCextract,
    manuscriptExtractionSeriesLowerBound16]

theorem manuscriptSeriesGain_two_sixteen_gt_one :
    (1 : ℝ) < manuscriptSeriesC1LowerBound16 * irrelevantScale 2 16 := by
  rw [manuscriptSeriesGain_two_sixteen_eq]
  norm_num

/-- If the actual extraction norm is at least the one-variable displayed-series
lower bound, then the manuscript factor map cannot yield a contraction at
`b = 2, dmax = 16`. -/
theorem not_rgContraction_two_sixteen_of_manuscriptCextract_ge_seriesLowerBound
    {Cextract : ℝ}
    (hCextract : manuscriptExtractionSeriesLowerBound16 ≤ Cextract) :
    ¬ HasExtendedExtractionContraction (manuscriptC1FromCextract Cextract) 2 16 := by
  apply not_rgContraction_two_sixteen_of_constant_ge_8192
  have hbase :
      (8192 : ℝ) ≤ manuscriptC1FromCextract
        manuscriptExtractionSeriesLowerBound16 := by
    simpa [manuscriptSeriesC1LowerBound16] using
      manuscriptSeriesC1LowerBound16_ge_threshold
  have hmono :
      manuscriptC1FromCextract manuscriptExtractionSeriesLowerBound16 ≤
        manuscriptC1FromCextract Cextract := by
    unfold manuscriptC1FromCextract
    nlinarith [hCextract]
  exact le_trans hbase hmono

end YangMills
end QuantumTheory
end Mettapedia
