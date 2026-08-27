import Mettapedia.QuantumTheory.YangMills.ExtractionMajorant

/-!
# Extraction majorant regression checks

Pins the three readings of the manuscript's displayed extraction sum (literal
fails, sign-corrected fails for `n ≥ 2`, weightless is the only `< 2`
reading) and the majorant-norm repair (truncation contractive, tail gains
`(r1/r0)^(D+1)`, RG-scaled tail bounded by `irrelevantScale`).  Axiom audits
are guarded so any future `sorry` or extra axiom fails the build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace ExtractionMajorantRegression

theorem literal_sum_never_le_two_regression {n : ℕ} (hn : 1 ≤ n) :
    ¬ literalExtractionOperatorSum n ≤ 2 :=
  not_literalExtractionOperatorSum_le_two hn

theorem literal_sum_one_index_regression :
    literalExtractionOperatorSum 1 = 3 :=
  literalExtractionOperatorSum_one

theorem literal_weightless_growth_regression :
    ∑ d ∈ Finset.range 17, 2 ^ d = 131071 :=
  literalWeightlessExtractionSum_eq

theorem sign_corrected_binomial_value_regression (n : ℕ) :
    ∑ d ∈ Finset.range (n + 1), (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d
      = ((3 : ℝ) / 2) ^ n :=
  signCorrectedExtractionSum_eq n

theorem sign_corrected_exceeds_two_regression {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) < signCorrectedTruncatedExtractionSum n :=
  two_lt_signCorrectedTruncatedExtractionSum hn

theorem weightless_geometric_lt_two_regression :
    ∑ d ∈ Finset.range 17, ((1 : ℝ) / 2) ^ d < 2 :=
  weightlessExtractionSum_lt_two

theorem majorant_truncation_contractive_regression
    {ι : Type} [Fintype ι] {r : ℝ} (hr : 0 ≤ r)
    (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) :
    majorantNorm r Δ (dimTruncate Δ D c) ≤ majorantNorm r Δ c :=
  majorantNorm_dimTruncate_le hr Δ D c

theorem majorant_tail_contraction_regression
    {ι : Type} [Fintype ι] (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ)
    {bN : ℕ} {r0 r1 : ℝ}
    (hb : 1 ≤ bN) (hr1 : 0 ≤ r1) (hr0 : 0 < r0) (hle : r1 ≤ r0) :
    majorantNorm r1 Δ (rgDimScale (bN : ℝ) Δ (dimTail Δ D c))
      ≤ irrelevantScale bN D
        * ((r1 / r0) ^ (D + 1) * majorantNorm r0 Δ c) :=
  majorant_irrelevant_tail_contraction_irrelevantScale Δ D c hb hr1 hr0 hle

/--
info: 'Mettapedia.QuantumTheory.YangMills.not_literalExtractionOperatorSum_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms not_literalExtractionOperatorSum_le_two

/--
info: 'Mettapedia.QuantumTheory.YangMills.signCorrectedExtractionSum_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signCorrectedExtractionSum_eq

/--
info: 'Mettapedia.QuantumTheory.YangMills.two_lt_signCorrectedTruncatedExtractionSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms two_lt_signCorrectedTruncatedExtractionSum

/--
info: 'Mettapedia.QuantumTheory.YangMills.weightlessExtractionSum_lt_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms weightlessExtractionSum_lt_two

/--
info: 'Mettapedia.QuantumTheory.YangMills.majorantNorm_dimTruncate_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms majorantNorm_dimTruncate_le

/--
info: 'Mettapedia.QuantumTheory.YangMills.majorant_irrelevant_tail_contraction_irrelevantScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms majorant_irrelevant_tail_contraction_irrelevantScale

end ExtractionMajorantRegression
end YangMills
end QuantumTheory
end Mettapedia
