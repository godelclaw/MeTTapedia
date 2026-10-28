import Mettapedia.QuantumTheory.YangMills.RGBootstrap

/-!
# Yang-Mills Extraction Constant Erratum

The manuscript's extended-extraction contraction uses the advertised numerical
audit `2224 * 2^-13 < 1`.  That arithmetic remains true when `2224` is supplied
as an input, and it also remains true for the Cauchy-estimate bound
`Cextract <= 2`.

Erratum: the previous `ExtractionConstantBreak` audit read the displayed
extraction-projection ratio with the inverted exponent literally.  That made a
convergent Cauchy estimate look like a growing series and incorrectly produced
an extraction-constant refutation.  The corrected interpretation keeps the
extended-extraction contraction standing; the continuum Yang-Mills endpoint
is still open because the constructive-QFT/continuum gate has not been closed.

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

/-- The corrected Cauchy-estimate extraction bound used by the manuscript:
`Cextract <= 2`. -/
def benCauchyCextractUpperBound : ℝ :=
  2

/-- The resulting `C1` bound from the manuscript factor map. -/
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

/-- The corrected Cauchy-estimate constant has one-step gain about `0.2707`,
so it is below `1`. -/
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

/-- Therefore the corrected Cauchy-estimate bound certifies the advertised
extended-extraction contraction at `b = 2, dmax = 16`. -/
theorem benCauchyC1UpperBound_contraction_two_sixteen :
    HasExtendedExtractionContraction benCauchyC1UpperBound 2 16 := by
  exact
    rgContraction_of_nonneg_le_2224_two_sixteen
      benCauchyC1UpperBound_nonneg
      benCauchyC1UpperBound_le_advertised

end YangMills
end QuantumTheory
end Mettapedia
