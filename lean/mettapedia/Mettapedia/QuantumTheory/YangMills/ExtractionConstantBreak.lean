import Mettapedia.QuantumTheory.YangMills.RGBootstrap

/-!
# Legacy Appendix-O extraction-ledger arithmetic

This file retains arithmetic for Appendix O's proposed factor ledger with the
numeral `Cextract = 2`.  It does **not** prove that numeral is an operator-norm
bound.  `ExtractionMajorant` proves that changing only the printed exponent
sign still leaves a binomial sum greater than two, while
`ExtendedExtractionTransfer` proves that the manuscript's range-only
projection definition cannot imply a uniform bound two.  The actual
source-adjudicated verdict is in `WilsonExtractionRecombinationConstant`.

Consequently every "upper bound" name below should be read as legacy naming
for a proposed ledger value, not as a theorem about the v14 Wilson RG map.  The
arithmetic implication remains useful once its analytic factors are supplied.

The only negative theorem retained here is a generic HYPOTHETICAL threshold:
if some unrelated future constant satisfies `C >= 8192`, then it cannot certify
the `b = 2, dmax = 16` contraction.  This theorem is not applied to Ben's
corrected Cauchy constant.
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

/-- The numeral assigned to the extraction factor in Appendix O.  No theorem in
this file proves it bounds the v14 extraction operator. -/
def benCauchyCextractUpperBound : ℝ :=
  2

/-- The resulting proposed `C1` value from the Appendix-O factor map. -/
def benCauchyC1UpperBound : ℝ :=
  manuscriptC1FromCextract benCauchyCextractUpperBound

theorem benCauchyC1UpperBound_eq :
    benCauchyC1UpperBound = (11088 : ℝ) / 5 := by
  norm_num [benCauchyC1UpperBound, benCauchyCextractUpperBound,
    manuscriptC1FromCextract]

theorem benCauchyC1UpperBound_nonneg :
    0 ≤ benCauchyC1UpperBound := by
  norm_num [benCauchyC1UpperBound, benCauchyCextractUpperBound,
    manuscriptC1FromCextract]

theorem benCauchyC1UpperBound_le_advertised :
    benCauchyC1UpperBound ≤ (2224 : ℝ) := by
  norm_num [benCauchyC1UpperBound, benCauchyCextractUpperBound,
    manuscriptC1FromCextract]

/-- At the manuscript's `b = 2, dmax = 16` endpoint, contraction forces the
constant below `2^(16-3) = 8192`. -/
theorem hypothetical_not_rgContraction_two_sixteen_of_constant_ge_8192
    {C : ℝ} (hC : (8192 : ℝ) ≤ C) :
    ¬ HasExtendedExtractionContraction C 2 16 := by
  intro h
  have hlt : C < (2 : ℝ) ^ (16 - 3) :=
    rgContraction_two_forces_constant_lt_pow_of_three_le
      (C := C) (dmax := 16) (by norm_num) h
  norm_num at hlt
  exact (not_lt_of_ge hC) hlt

/-- The Appendix-O proposed ledger value has one-step gain about `0.2707`, so
its arithmetic value is below `1`. -/
theorem benCauchyC1UpperBound_gain_two_sixteen_eq :
    benCauchyC1UpperBound * irrelevantScale 2 16 =
      (693 : ℝ) / 2560 := by
  rw [irrelevantScale_two_sixteen]
  norm_num [benCauchyC1UpperBound, benCauchyCextractUpperBound,
    manuscriptC1FromCextract]

theorem benCauchyC1UpperBound_gain_two_sixteen_lt_one :
    benCauchyC1UpperBound * irrelevantScale 2 16 < 1 := by
  rw [benCauchyC1UpperBound_gain_two_sixteen_eq]
  norm_num

/-- Conditional arithmetic only: the Appendix-O proposed ledger value meets
linear contraction at `b = 2, dmax = 16`. -/
theorem benCauchyC1UpperBound_contraction_two_sixteen :
    HasExtendedExtractionContraction benCauchyC1UpperBound 2 16 := by
  exact
    rgContraction_of_nonneg_le_2224_two_sixteen
      benCauchyC1UpperBound_nonneg
      benCauchyC1UpperBound_le_advertised

end YangMills
end QuantumTheory
end Mettapedia
