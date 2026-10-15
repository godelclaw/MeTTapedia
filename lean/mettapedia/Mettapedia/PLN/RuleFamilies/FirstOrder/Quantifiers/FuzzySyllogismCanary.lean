import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.QuantifierWorkedExamples

/-!
# Chapter 11 Extended Fuzzy-Syllogism Canaries

This module adds:

1. A Zadeh-style quantified syllogism theorem family (`most ∘ most`, `few ∘ most`)
   using the multiplicative composition pattern already used in Chapter-11 examples.
2. QFM-oriented canaries:
   - monotonicity under pointwise profile increase,
   - conservativity-style invariance when the `nearOne` witness signature is unchanged.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers

section Generic

variable {U : Type*} [Fintype U]

/-- QFM-abstract syllogism transport from two fuzzy quantifier intervals. -/
theorem qfm_syllogism_interval
    (q : QFMCompose)
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    q.comp pAB.LPC pBC.LPC ≤
        q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ∧
      q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ≤
        q.comp pAB.UPC pBC.UPC :=
  qfm_compose_interval_of_fuzzyIntervals q pAB pBC profileAB profileBC hAB hBC

/-- QFM-abstract `MOST ∘ MOST` theorem. -/
theorem qfm_syllogism_most_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    q.comp mostParams.LPC mostParams.LPC ≤
        q.comp (nearOneFraction mostParams profileAB)
          (nearOneFraction mostParams profileBC) ∧
      q.comp (nearOneFraction mostParams profileAB)
          (nearOneFraction mostParams profileBC) ≤
        q.comp mostParams.UPC mostParams.UPC :=
  qfm_syllogism_interval q mostParams mostParams profileAB profileBC hAB hBC

/-- QFM-abstract `FEW ∘ MOST` theorem. -/
theorem qfm_syllogism_few_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    q.comp fewParams.LPC mostParams.LPC ≤
        q.comp (nearOneFraction fewParams profileAB)
          (nearOneFraction mostParams profileBC) ∧
      q.comp (nearOneFraction fewParams profileAB)
          (nearOneFraction mostParams profileBC) ≤
        q.comp fewParams.UPC mostParams.UPC :=
  qfm_syllogism_interval q fewParams mostParams profileAB profileBC hAB hBC

/-- Reusable selector bundle (`MOST ∘ MOST`) for any QFM operator. -/
noncomputable def qfm_selector_bundle_most_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    QFMSyllogismEnvelope :=
  qfm_compose_interval_bundle q mostParams mostParams profileAB profileBC hAB hBC

/-- Reusable selector bundle (`FEW ∘ MOST`) for any QFM operator. -/
noncomputable def qfm_selector_bundle_few_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    QFMSyllogismEnvelope :=
  qfm_compose_interval_bundle q fewParams mostParams profileAB profileBC hAB hBC

/-- Soundness projection for the selector bundle (`MOST ∘ MOST`). -/
theorem qfm_selector_bundle_most_most_sound
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    let B := qfm_selector_bundle_most_most q profileAB profileBC hAB hBC
    B.lower ≤ B.score ∧ B.score ≤ B.upper := by
  intro B
  exact ⟨B.lower_le_score, B.score_le_upper⟩

/-- Soundness projection for the selector bundle (`FEW ∘ MOST`). -/
theorem qfm_selector_bundle_few_most_sound
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    let B := qfm_selector_bundle_few_most q profileAB profileBC hAB hBC
    B.lower ≤ B.score ∧ B.score ≤ B.upper := by
  intro B
  exact ⟨B.lower_le_score, B.score_le_upper⟩

/-- Zadeh-style family: if both legs are `MOST`, the composed score is in `[0.49, 0.81]`. -/
theorem zadeh_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.49 : ℝ) ≤
        nearOneFraction mostParams profileAB *
          nearOneFraction mostParams profileBC ∧
      nearOneFraction mostParams profileAB *
          nearOneFraction mostParams profileBC ≤
        (0.81 : ℝ) := by
  have hProd :
      mostParams.LPC * mostParams.LPC ≤
          nearOneFraction mostParams profileAB *
            nearOneFraction mostParams profileBC ∧
        nearOneFraction mostParams profileAB *
            nearOneFraction mostParams profileBC ≤
          mostParams.UPC * mostParams.UPC := by
    simpa [qfmMul] using qfm_syllogism_most_most (q := qfmMul) profileAB profileBC hAB hBC
  have hL : mostParams.LPC * mostParams.LPC = (0.49 : ℝ) := by
    norm_num [mostParams]
  have hU : mostParams.UPC * mostParams.UPC = (0.81 : ℝ) := by
    norm_num [mostParams]
  constructor
  · simpa [hL] using hProd.1
  · simpa [hU] using hProd.2

/-- Zadeh-style family: if premise is `FEW` and rule-leg is `MOST`,
the composed score is in `[0.07, 0.27]`. -/
theorem zadeh_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.07 : ℝ) ≤
        nearOneFraction fewParams profileAB *
          nearOneFraction mostParams profileBC ∧
      nearOneFraction fewParams profileAB *
          nearOneFraction mostParams profileBC ≤
        (0.27 : ℝ) := by
  have hProd :
      fewParams.LPC * mostParams.LPC ≤
          nearOneFraction fewParams profileAB *
            nearOneFraction mostParams profileBC ∧
        nearOneFraction fewParams profileAB *
            nearOneFraction mostParams profileBC ≤
          fewParams.UPC * mostParams.UPC := by
    simpa [qfmMul] using qfm_syllogism_few_most (q := qfmMul) profileAB profileBC hAB hBC
  have hL : fewParams.LPC * mostParams.LPC = (0.07 : ℝ) := by
    norm_num [fewParams, mostParams]
  have hU : fewParams.UPC * mostParams.UPC = (0.27 : ℝ) := by
    norm_num [fewParams, mostParams]
  constructor
  · simpa [hL] using hProd.1
  · simpa [hU] using hProd.2

/-- `qfmMin` specialization of `MOST ∘ MOST`:
composed score stays in the same MOST interval. -/
theorem qfmMin_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.7 : ℝ) ≤
        min (nearOneFraction mostParams profileAB)
            (nearOneFraction mostParams profileBC) ∧
      min (nearOneFraction mostParams profileAB)
          (nearOneFraction mostParams profileBC) ≤
        (0.9 : ℝ) := by
  have h :
      min mostParams.LPC mostParams.LPC ≤
          min (nearOneFraction mostParams profileAB)
              (nearOneFraction mostParams profileBC) ∧
        min (nearOneFraction mostParams profileAB)
            (nearOneFraction mostParams profileBC) ≤
          min mostParams.UPC mostParams.UPC := by
    simpa [qfmMin] using qfm_syllogism_most_most (q := qfmMin) profileAB profileBC hAB hBC
  have hL : min mostParams.LPC mostParams.LPC = (0.7 : ℝ) := by
    norm_num [mostParams]
  have hU : min mostParams.UPC mostParams.UPC = (0.9 : ℝ) := by
    norm_num [mostParams]
  constructor
  · simpa [hL, mostParams] using h.1
  · simpa [hU, mostParams] using h.2

/-- `qfmMin` specialization of `FEW ∘ MOST`:
composed score stays in the FEW interval `[0.1,0.3]`. -/
theorem qfmMin_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.1 : ℝ) ≤
        min (nearOneFraction fewParams profileAB)
            (nearOneFraction mostParams profileBC) ∧
      min (nearOneFraction fewParams profileAB)
          (nearOneFraction mostParams profileBC) ≤
        (0.3 : ℝ) := by
  have h :
      min fewParams.LPC mostParams.LPC ≤
          min (nearOneFraction fewParams profileAB)
              (nearOneFraction mostParams profileBC) ∧
        min (nearOneFraction fewParams profileAB)
            (nearOneFraction mostParams profileBC) ≤
          min fewParams.UPC mostParams.UPC := by
    simpa [qfmMin] using qfm_syllogism_few_most (q := qfmMin) profileAB profileBC hAB hBC
  have hL : min fewParams.LPC mostParams.LPC = (0.1 : ℝ) := by
    norm_num [fewParams, mostParams]
  have hU : min fewParams.UPC mostParams.UPC = (0.3 : ℝ) := by
    norm_num [fewParams, mostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmLukasiewicz` specialization of `MOST ∘ MOST`. -/
theorem qfmLukasiewicz_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.4 : ℝ) ≤
        max 0 (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC - 1) ∧
      max 0 (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC - 1) ≤
        (0.8 : ℝ) := by
  have h :
      max 0 (mostParams.LPC + mostParams.LPC - 1) ≤
          max 0 (nearOneFraction mostParams profileAB +
            nearOneFraction mostParams profileBC - 1) ∧
        max 0 (nearOneFraction mostParams profileAB +
            nearOneFraction mostParams profileBC - 1) ≤
          max 0 (mostParams.UPC + mostParams.UPC - 1) := by
    simpa [qfmLukasiewicz] using
      qfm_syllogism_most_most (q := qfmLukasiewicz) profileAB profileBC hAB hBC
  have hL : max 0 (mostParams.LPC + mostParams.LPC - 1) = (0.4 : ℝ) := by
    norm_num [mostParams]
  have hU : max 0 (mostParams.UPC + mostParams.UPC - 1) = (0.8 : ℝ) := by
    norm_num [mostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmLukasiewicz` specialization of `FEW ∘ MOST`. -/
theorem qfmLukasiewicz_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0 : ℝ) ≤
        max 0 (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC - 1) ∧
      max 0 (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC - 1) ≤
        (0.2 : ℝ) := by
  have h :
      max 0 (fewParams.LPC + mostParams.LPC - 1) ≤
          max 0 (nearOneFraction fewParams profileAB +
            nearOneFraction mostParams profileBC - 1) ∧
        max 0 (nearOneFraction fewParams profileAB +
            nearOneFraction mostParams profileBC - 1) ≤
          max 0 (fewParams.UPC + mostParams.UPC - 1) := by
    simpa [qfmLukasiewicz] using
      qfm_syllogism_few_most (q := qfmLukasiewicz) profileAB profileBC hAB hBC
  have hL : max 0 (fewParams.LPC + mostParams.LPC - 1) = (0 : ℝ) := by
    norm_num [fewParams, mostParams]
  have hU : max 0 (fewParams.UPC + mostParams.UPC - 1) = (0.2 : ℝ) := by
    norm_num [fewParams, mostParams]
  constructor
  · calc
      (0 : ℝ) = max 0 (fewParams.LPC + mostParams.LPC - 1) := by simp [hL]
      _ ≤ max 0 (nearOneFraction fewParams profileAB +
            nearOneFraction mostParams profileBC - 1) := h.1
  · simpa [hU] using h.2

/-- `qfmProbSum` specialization of `MOST ∘ MOST`. -/
theorem qfmProbSum_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.91 : ℝ) ≤
        (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction mostParams profileAB * nearOneFraction mostParams profileBC) ∧
      (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction mostParams profileAB * nearOneFraction mostParams profileBC) ≤
        (0.99 : ℝ) := by
  have h :
      (mostParams.LPC + mostParams.LPC - mostParams.LPC * mostParams.LPC) ≤
          (nearOneFraction mostParams profileAB +
            nearOneFraction mostParams profileBC -
            nearOneFraction mostParams profileAB * nearOneFraction mostParams profileBC) ∧
        (nearOneFraction mostParams profileAB +
            nearOneFraction mostParams profileBC -
            nearOneFraction mostParams profileAB * nearOneFraction mostParams profileBC) ≤
          (mostParams.UPC + mostParams.UPC - mostParams.UPC * mostParams.UPC) := by
    simpa [qfmProbSum] using
      qfm_syllogism_most_most (q := qfmProbSum) profileAB profileBC hAB hBC
  have hL : (mostParams.LPC + mostParams.LPC - mostParams.LPC * mostParams.LPC) =
      (0.91 : ℝ) := by
    norm_num [mostParams]
  have hU : (mostParams.UPC + mostParams.UPC - mostParams.UPC * mostParams.UPC) =
      (0.99 : ℝ) := by
    norm_num [mostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmProbSum` specialization of `FEW ∘ MOST`. -/
theorem qfmProbSum_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.73 : ℝ) ≤
        (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction fewParams profileAB * nearOneFraction mostParams profileBC) ∧
      (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction fewParams profileAB * nearOneFraction mostParams profileBC) ≤
        (0.93 : ℝ) := by
  have h :
      (fewParams.LPC + mostParams.LPC - fewParams.LPC * mostParams.LPC) ≤
          (nearOneFraction fewParams profileAB +
            nearOneFraction mostParams profileBC -
            nearOneFraction fewParams profileAB * nearOneFraction mostParams profileBC) ∧
        (nearOneFraction fewParams profileAB +
            nearOneFraction mostParams profileBC -
            nearOneFraction fewParams profileAB * nearOneFraction mostParams profileBC) ≤
          (fewParams.UPC + mostParams.UPC - fewParams.UPC * mostParams.UPC) := by
    simpa [qfmProbSum] using
      qfm_syllogism_few_most (q := qfmProbSum) profileAB profileBC hAB hBC
  have hL :
      (fewParams.LPC + mostParams.LPC - fewParams.LPC * mostParams.LPC) = (0.73 : ℝ) := by
    norm_num [fewParams, mostParams]
  have hU :
      (fewParams.UPC + mostParams.UPC - fewParams.UPC * mostParams.UPC) = (0.93 : ℝ) := by
    norm_num [fewParams, mostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- Compact comparison block on common premises (`MOST ∘ MOST`) across QFM instances. -/
theorem qfm_instance_comparison_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds mostParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.49 : ℝ) ≤
        nearOneFraction mostParams profileAB *
          nearOneFraction mostParams profileBC ∧
      nearOneFraction mostParams profileAB *
          nearOneFraction mostParams profileBC ≤
        (0.81 : ℝ) ∧
      (0.7 : ℝ) ≤
        min (nearOneFraction mostParams profileAB)
            (nearOneFraction mostParams profileBC) ∧
      min (nearOneFraction mostParams profileAB)
          (nearOneFraction mostParams profileBC) ≤
        (0.9 : ℝ) ∧
      (0.4 : ℝ) ≤
        max 0 (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC - 1) ∧
      max 0 (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC - 1) ≤
        (0.8 : ℝ) ∧
      (0.91 : ℝ) ≤
        (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction mostParams profileAB * nearOneFraction mostParams profileBC) ∧
      (nearOneFraction mostParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction mostParams profileAB * nearOneFraction mostParams profileBC) ≤
        (0.99 : ℝ) := by
  have hMul := zadeh_syllogism_most_most profileAB profileBC hAB hBC
  have hMin := qfmMin_syllogism_most_most profileAB profileBC hAB hBC
  have hLuk := qfmLukasiewicz_syllogism_most_most profileAB profileBC hAB hBC
  have hProb := qfmProbSum_syllogism_most_most profileAB profileBC hAB hBC
  exact ⟨hMul.1, hMul.2, hMin.1, hMin.2, hLuk.1, hLuk.2, hProb.1, hProb.2⟩

/-- Compact comparison block on common premises (`FEW ∘ MOST`) across QFM instances. -/
theorem qfm_instance_comparison_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds fewParams profileAB)
    (hBC : fuzzyIntervalHolds mostParams profileBC) :
    (0.07 : ℝ) ≤
        nearOneFraction fewParams profileAB *
          nearOneFraction mostParams profileBC ∧
      nearOneFraction fewParams profileAB *
          nearOneFraction mostParams profileBC ≤
        (0.27 : ℝ) ∧
      (0.1 : ℝ) ≤
        min (nearOneFraction fewParams profileAB)
            (nearOneFraction mostParams profileBC) ∧
      min (nearOneFraction fewParams profileAB)
          (nearOneFraction mostParams profileBC) ≤
        (0.3 : ℝ) ∧
      (0 : ℝ) ≤
        max 0 (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC - 1) ∧
      max 0 (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC - 1) ≤
        (0.2 : ℝ) ∧
      (0.73 : ℝ) ≤
        (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction fewParams profileAB * nearOneFraction mostParams profileBC) ∧
      (nearOneFraction fewParams profileAB +
          nearOneFraction mostParams profileBC -
          nearOneFraction fewParams profileAB * nearOneFraction mostParams profileBC) ≤
        (0.93 : ℝ) := by
  have hMul := zadeh_syllogism_few_most profileAB profileBC hAB hBC
  have hMin := qfmMin_syllogism_few_most profileAB profileBC hAB hBC
  have hLuk := qfmLukasiewicz_syllogism_few_most profileAB profileBC hAB hBC
  have hProb := qfmProbSum_syllogism_few_most profileAB profileBC hAB hBC
  exact ⟨hMul.1, hMul.2, hMin.1, hMin.2, hLuk.1, hLuk.2, hProb.1, hProb.2⟩

end Generic

section FiniteCanaries

/-- Uniform high profile on `Fin 4`, used for monotonicity canaries. -/
def allHighFin4 : Fin 4 → ℝ := fun _ => 0.95

/-- Alternate profile with same `nearOne` signature as `threeHighOneLow` under MOST parameters. -/
def mostSignatureAlt : Fin 4 → ℝ := fun u => if u = 0 then 0.2 else 0.91

/-- QFM-style monotonicity canary:
pointwise increase in profile values cannot decrease near-one mass. -/
theorem canary_qfm_monotonicity_most :
    nearOneFraction mostParams threeHighOneLow ≤
      nearOneFraction mostParams allHighFin4 := by
  have hmono :
      fuzzyExistsScore mostParams threeHighOneLow ≤
        fuzzyExistsScore mostParams allHighFin4 := by
    exact fuzzyExistsScore_mono_of_pointwise
      (p := mostParams)
      (profile₁ := threeHighOneLow)
      (profile₂ := allHighFin4)
      (hle := by
        intro u
        fin_cases u <;> (simp [threeHighOneLow, allHighFin4]; try norm_num))
      (hub := by
        intro u
        simp [allHighFin4]
        norm_num)
  simpa [fuzzyExistsScore] using hmono

/-- Generic monotonicity schema instantiated on a finite profile pair. -/
theorem canary_qfm_forall_monotonicity_most :
    fuzzyForAllHolds mostParams threeHighOneLow →
      fuzzyForAllHolds mostParams allHighFin4 := by
  exact fuzzyForAllHolds_mono_of_pointwise
    (p := mostParams)
    (profile₁ := threeHighOneLow)
    (profile₂ := allHighFin4)
    (hle := by
      intro u
      fin_cases u <;> (simp [threeHighOneLow, allHighFin4]; try norm_num))
    (hub := by
      intro u
      simp [allHighFin4]
      norm_num)

/-- QFM-style conservativity canary:
if the `nearOne` signature is unchanged, interval truth is unchanged. -/
theorem canary_qfm_conservativity_same_nearOne_signature :
    nearOneFraction mostParams threeHighOneLow =
      nearOneFraction mostParams mostSignatureAlt ∧
      (fuzzyIntervalHolds mostParams threeHighOneLow ↔
        fuzzyIntervalHolds mostParams mostSignatureAlt) := by
  have hSig :
      ∀ u : Fin 4,
        nearOne mostParams (threeHighOneLow u) ↔ nearOne mostParams (mostSignatureAlt u) := by
    intro u
    fin_cases u <;> (simp [nearOne, threeHighOneLow, mostSignatureAlt, mostParams]; norm_num)
  have hA :
      nearOneFraction mostParams threeHighOneLow =
        nearOneFraction mostParams mostSignatureAlt := by
    exact nearOneFraction_eq_of_signatureEq mostParams threeHighOneLow mostSignatureAlt hSig
  constructor
  · exact hA
  · exact fuzzyIntervalHolds_iff_of_signatureEq mostParams threeHighOneLow mostSignatureAlt hSig

/-- Concrete `MOST ∘ MOST` fixture canary (3/4 composed with 3/4). -/
theorem canary_zadeh_most_most_fixture :
    (0.49 : ℝ) ≤
        nearOneFraction mostParams threeHighOneLow *
          nearOneFraction mostParams threeHighOneLow ∧
      nearOneFraction mostParams threeHighOneLow *
          nearOneFraction mostParams threeHighOneLow ≤
        (0.81 : ℝ) := by
  have hMost : fuzzyIntervalHolds mostParams threeHighOneLow := by
    unfold fuzzyIntervalHolds
    rw [canary_most_fraction_threeQuarters]
    norm_num [mostParams]
  exact zadeh_syllogism_most_most threeHighOneLow threeHighOneLow hMost hMost

/-- Concrete `FEW ∘ MOST` fixture canary (1/4 composed with 3/4). -/
theorem canary_zadeh_few_most_fixture :
    (0.07 : ℝ) ≤
        nearOneFraction fewParams oneHighThreeLow *
          nearOneFraction mostParams threeHighOneLow ∧
      nearOneFraction fewParams oneHighThreeLow *
          nearOneFraction mostParams threeHighOneLow ≤
        (0.27 : ℝ) := by
  have hFew : fuzzyIntervalHolds fewParams oneHighThreeLow := by
    unfold fuzzyIntervalHolds
    rw [canary_few_fraction_oneQuarter]
    norm_num [fewParams]
  have hMost : fuzzyIntervalHolds mostParams threeHighOneLow := by
    unfold fuzzyIntervalHolds
    rw [canary_most_fraction_threeQuarters]
    norm_num [mostParams]
  exact zadeh_syllogism_few_most oneHighThreeLow threeHighOneLow hFew hMost

end FiniteCanaries

end Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
