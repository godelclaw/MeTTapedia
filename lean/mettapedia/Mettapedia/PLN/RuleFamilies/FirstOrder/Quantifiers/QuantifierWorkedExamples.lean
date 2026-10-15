import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyITVBridge
import Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

/-!
# Chapter 11 Worked Examples (Canary Theorems)

This module provides theorem-level canaries aligned with the Chapter-11 narrative:

1. A "crooked lottery"-style case where only a minority are near-certain winners.
2. A fuzzy syllogism-style case where composed scores stay in a "many" interval.
3. Explicit non-equivalence witness for the Ch.11 rule-4 shape on an ITV-based path.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers

open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

/-- Shared ε=0.1 fixture with AFew-like interval `[0.4,0.6]` and strong `PCL=0.9`. -/
def aFewParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.6
  PCL := 0.9
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MANY-like interval `[0.4,0.95]`. -/
def manyParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.95
  PCL := 0.4
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- One high-probability witness, one low-probability witness. -/
def oneHighOneLow : Bool → ℝ :=
  fun b => if b then 0.95 else 0.05

/-- Both witnesses high. -/
def bothHigh : Bool → ℝ :=
  fun _ => 0.95

/-- Both witnesses low. -/
def bothLow : Bool → ℝ :=
  fun _ => 0.05

/-- Shared ε=0.1 fixture with MOST-like interval `[0.7,0.9]`. -/
def mostParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.7
  UPC := 0.9
  PCL := 0.7
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with FEW-like interval `[0.1,0.3]`. -/
def fewParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.1
  UPC := 0.3
  PCL := 0.1
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with ALMOST-ALL-like interval `[0.75,1.0]`. -/
def almostAllParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.75
  UPC := 1
  PCL := 0.75
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with ABOUT-HALF-like interval `[0.45,0.55]`. -/
def aboutHalfParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.45
  UPC := 0.55
  PCL := 0.45
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with PROBABLY-like interval `[0.66,0.85]`. -/
def probablyParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.66
  UPC := 0.85
  PCL := 0.66
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MAYBE/POSSIBLY-like interval `[0.3,0.7]`. -/
def maybeParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.3
  UPC := 0.7
  PCL := 0.3
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with ALMOST-NONE-like interval `[0.0,0.2]`. -/
def almostNoneParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0
  UPC := 0.2
  PCL := 0
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MANY-BUT-NOT-MOST interval `[0.4,0.69]`. -/
def manyNotMostParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.69
  PCL := 0.4
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Finite fixture with exactly 3 near-one witnesses out of 4. -/
def threeHighOneLow : Fin 4 → ℝ := fun u => if u = 0 then 0.05 else 0.95

/-- Finite fixture with exactly 1 near-one witness out of 4. -/
def oneHighThreeLow : Fin 4 → ℝ := fun u => if u = 0 then 0.95 else 0.05

/-- Finite-5 fixture with exactly 1 near-one witness out of 5. -/
def oneHighFourLowFin5 : Fin 5 → ℝ := fun u => if u = 0 then 0.95 else 0.05

/-- Finite-5 fixture with exactly 3 near-one witnesses out of 5. -/
def threeHighTwoLowFin5 : Fin 5 → ℝ :=
  fun u => if u = 0 ∨ u = 1 ∨ u = 2 then 0.95 else 0.05

/-- Crooked-lottery canary:
`AFew` holds while strict `ForAll` (via `PCL=0.9`) does not. -/
theorem canary_crookedLottery_afew_not_forall :
    fuzzyIntervalHolds aFewParams oneHighOneLow ∧
      ¬ fuzzyForAllHolds aFewParams oneHighOneLow := by
  have hfrac : nearOneFraction aFewParams oneHighOneLow = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne aFewParams (oneHighOneLow u)) =
          (fun u => u = true) := by
      funext u
      cases u <;> simp [nearOne, oneHighOneLow, aFewParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  constructor
  · unfold fuzzyIntervalHolds
    rw [hfrac]
    norm_num [aFewParams]
  · unfold fuzzyForAllHolds
    rw [hfrac]
    norm_num [aFewParams]

/-- Fuzzy-syllogism canary:
with "many women are beautiful" and "almost all beautiful bring happiness"
encoded as near-one fractions `1/2` and `1`, the composed score remains "many". -/
theorem canary_fuzzySyllogism_many :
    manyParams.LPC ≤
        nearOneFraction manyParams oneHighOneLow *
          nearOneFraction manyParams bothHigh ∧
      nearOneFraction manyParams oneHighOneLow *
          nearOneFraction manyParams bothHigh ≤
        manyParams.UPC := by
  have hWB : nearOneFraction manyParams oneHighOneLow = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne manyParams (oneHighOneLow u)) =
          (fun u => u = true) := by
      funext u
      cases u <;> simp [nearOne, oneHighOneLow, manyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hBH : nearOneFraction manyParams bothHigh = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne manyParams (bothHigh u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearOne, bothHigh, manyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  rw [hWB, hBH]
  norm_num [manyParams]

/-- Positive fixture: all-high profile satisfies strict fuzzy `ForAll` under AFew parameters. -/
theorem canary_allHigh_forall :
    fuzzyForAllHolds aFewParams bothHigh := by
  have hBH : nearOneFraction aFewParams bothHigh = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne aFewParams (bothHigh u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearOne, bothHigh, aFewParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  unfold fuzzyForAllHolds
  rw [hBH]
  norm_num [aFewParams]

/-- Negative fixture: all-low profile fails fuzzy `ThereExists` under AFew parameters. -/
theorem canary_allLow_not_thereExists :
    ¬ fuzzyThereExistsHolds aFewParams bothLow := by
  have hBZ : nearZeroFraction aFewParams bothLow = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearZero aFewParams (bothLow u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearZero, bothLow, aFewParams] <;> norm_num
    unfold nearZeroFraction
    simp [hpred, witnessFraction, witnessCount]
  unfold fuzzyThereExistsHolds
  rw [hBZ]
  norm_num [aFewParams]

/-- MOST fixture canary: expected near-one fraction is exactly `3/4`. -/
theorem canary_most_fraction_threeQuarters :
    nearOneFraction mostParams threeHighOneLow = (3 / 4 : ℝ) := by
  have hpred :
      (fun u : Fin 4 => nearOne mostParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
    funext u
    fin_cases u <;> simp [nearOne, threeHighOneLow, mostParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- FEW fixture canary: expected near-one fraction is exactly `1/4`. -/
theorem canary_few_fraction_oneQuarter :
    nearOneFraction fewParams oneHighThreeLow = (1 / 4 : ℝ) := by
  have hpred :
      (fun u : Fin 4 => nearOne fewParams (oneHighThreeLow u)) = (fun u => u = 0) := by
    funext u
    fin_cases u <;> simp [nearOne, oneHighThreeLow, fewParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- MOST positive + FEW negative on the same `3/4` fixture. -/
theorem canary_most_vs_few_split_on_threeQuarters :
    fuzzyIntervalHolds mostParams threeHighOneLow ∧
      ¬ fuzzyIntervalHolds fewParams threeHighOneLow := by
  have hfrac : nearOneFraction mostParams threeHighOneLow = (3 / 4 : ℝ) := by
    exact canary_most_fraction_threeQuarters
  constructor
  · unfold fuzzyIntervalHolds
    rw [hfrac]
    norm_num [mostParams]
  · unfold fuzzyIntervalHolds
    have hfracFew : nearOneFraction fewParams threeHighOneLow = (3 / 4 : ℝ) := by
      have hpred :
          (fun u : Fin 4 => nearOne fewParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
        funext u
        fin_cases u <;> simp [nearOne, threeHighOneLow, fewParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hfracFew]
    norm_num [fewParams]

/-- ALMOST-ALL fixture canary: expected near-one fraction is exactly `3/4`. -/
theorem canary_almostAll_fraction_threeQuarters :
    nearOneFraction almostAllParams threeHighOneLow = (3 / 4 : ℝ) := by
  have hpred :
      (fun u : Fin 4 => nearOne almostAllParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
    funext u
    fin_cases u <;> simp [nearOne, threeHighOneLow, almostAllParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- ALMOST-ALL positive canary on the `3/4` fixture. -/
theorem canary_almostAll_holds_on_threeQuarters :
    fuzzyIntervalHolds almostAllParams threeHighOneLow := by
  unfold fuzzyIntervalHolds
  rw [canary_almostAll_fraction_threeQuarters]
  norm_num [almostAllParams]

/-- ABOUT-HALF fixture canary: expected near-one fraction is exactly `1/2`. -/
theorem canary_aboutHalf_fraction_oneHalf :
    nearOneFraction aboutHalfParams oneHighOneLow = (1 / 2 : ℝ) := by
  have hpred :
      (fun u : Bool => nearOne aboutHalfParams (oneHighOneLow u)) = (fun u => u = true) := by
    funext u
    cases u <;> simp [nearOne, oneHighOneLow, aboutHalfParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- ABOUT-HALF split canary:
the `1/2` fixture is accepted while an all-high profile is rejected. -/
theorem canary_aboutHalf_positive_negative_split :
    fuzzyIntervalHolds aboutHalfParams oneHighOneLow ∧
      ¬ fuzzyIntervalHolds aboutHalfParams bothHigh := by
  constructor
  · unfold fuzzyIntervalHolds
    rw [canary_aboutHalf_fraction_oneHalf]
    norm_num [aboutHalfParams]
  · unfold fuzzyIntervalHolds
    have hAll : nearOneFraction aboutHalfParams bothHigh = (1 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne aboutHalfParams (bothHigh u)) = (fun _ => True) := by
        funext u
        cases u <;> simp [nearOne, bothHigh, aboutHalfParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hAll]
    norm_num [aboutHalfParams]

/-- PROBABLY positive + negative split:
`3/4` is accepted, while `1/2` is rejected. -/
theorem canary_probably_positive_negative_split :
    fuzzyIntervalHolds probablyParams threeHighOneLow ∧
      ¬ fuzzyIntervalHolds probablyParams oneHighOneLow := by
  constructor
  · unfold fuzzyIntervalHolds
    have hThreeQuarter : nearOneFraction probablyParams threeHighOneLow = (3 / 4 : ℝ) := by
      have hpred :
          (fun u : Fin 4 => nearOne probablyParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
        funext u
        fin_cases u <;> simp [nearOne, threeHighOneLow, probablyParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hThreeQuarter]
    norm_num [probablyParams]
  · unfold fuzzyIntervalHolds
    have hHalf : nearOneFraction probablyParams oneHighOneLow = (1 / 2 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne probablyParams (oneHighOneLow u)) = (fun u => u = true) := by
        funext u
        cases u <;> simp [nearOne, oneHighOneLow, probablyParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hHalf]
    norm_num [probablyParams]

/-- PROBABLY positive finite fixture:
`3/4` near-one mass is accepted by `[0.66,0.85]`. -/
theorem canary_probably_holds_on_threeQuarters :
    fuzzyIntervalHolds probablyParams threeHighOneLow :=
  (canary_probably_positive_negative_split).1

/-- PROBABLY negative finite fixture:
`1/2` near-one mass is rejected by `[0.66,0.85]`. -/
theorem canary_probably_rejects_oneHalf :
    ¬ fuzzyIntervalHolds probablyParams oneHighOneLow :=
  (canary_probably_positive_negative_split).2

/-- MAYBE/POSSIBLY positive + negative split:
`1/2` is accepted, while certainty (`1`) is rejected. -/
theorem canary_maybe_positive_negative_split :
    fuzzyIntervalHolds maybeParams oneHighOneLow ∧
      ¬ fuzzyIntervalHolds maybeParams bothHigh := by
  constructor
  · unfold fuzzyIntervalHolds
    have hHalf : nearOneFraction maybeParams oneHighOneLow = (1 / 2 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne maybeParams (oneHighOneLow u)) = (fun u => u = true) := by
        funext u
        cases u <;> simp [nearOne, oneHighOneLow, maybeParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hHalf]
    norm_num [maybeParams]
  · unfold fuzzyIntervalHolds
    have hAll : nearOneFraction maybeParams bothHigh = (1 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne maybeParams (bothHigh u)) = (fun _ => True) := by
        funext u
        cases u <;> simp [nearOne, bothHigh, maybeParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hAll]
    norm_num [maybeParams]

/-- MAYBE/POSSIBLY positive finite fixture:
`1/2` near-one mass is accepted by `[0.3,0.7]`. -/
theorem canary_maybe_holds_on_oneHalf :
    fuzzyIntervalHolds maybeParams oneHighOneLow :=
  (canary_maybe_positive_negative_split).1

/-- ALMOST-NONE fixture canary: expected near-one fraction is exactly `1/5`. -/
theorem canary_almostNone_fraction_oneFifth :
    nearOneFraction almostNoneParams oneHighFourLowFin5 = (1 / 5 : ℝ) := by
  have hpred :
      (fun u : Fin 5 => nearOne almostNoneParams (oneHighFourLowFin5 u)) = (fun u => u = 0) := by
    funext u
    fin_cases u <;> simp [nearOne, oneHighFourLowFin5, almostNoneParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- ALMOST-NONE positive canary on the finite-5 `1/5` fixture. -/
theorem canary_almostNone_holds_on_oneFifth :
    fuzzyIntervalHolds almostNoneParams oneHighFourLowFin5 := by
  unfold fuzzyIntervalHolds
  rw [canary_almostNone_fraction_oneFifth]
  norm_num [almostNoneParams]

/-- MANY-BUT-NOT-MOST fixture canary: expected near-one fraction is exactly `3/5`. -/
theorem canary_manyNotMost_fraction_threeFifths :
    nearOneFraction manyNotMostParams threeHighTwoLowFin5 = (3 / 5 : ℝ) := by
  have hpred :
      (fun u : Fin 5 => nearOne manyNotMostParams (threeHighTwoLowFin5 u)) =
        (fun u => u = 0 ∨ u = 1 ∨ u = 2) := by
    funext u
    fin_cases u <;> simp [nearOne, threeHighTwoLowFin5, manyNotMostParams] <;> norm_num
  have hcount : Fintype.card {u : Fin 5 // u = 0 ∨ u = 1 ∨ u = 2} = 3 := by
    decide
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount, hcount]

/-- MANY-BUT-NOT-MOST split canary:
the `3/5` fixture satisfies many-but-not-most, but not MOST. -/
theorem canary_manyNotMost_vs_most_split :
    fuzzyIntervalHolds manyNotMostParams threeHighTwoLowFin5 ∧
      ¬ fuzzyIntervalHolds mostParams threeHighTwoLowFin5 := by
  constructor
  · unfold fuzzyIntervalHolds
    rw [canary_manyNotMost_fraction_threeFifths]
    norm_num [manyNotMostParams]
  · unfold fuzzyIntervalHolds
    have hMostFrac : nearOneFraction mostParams threeHighTwoLowFin5 = (3 / 5 : ℝ) := by
      have hpred :
          (fun u : Fin 5 => nearOne mostParams (threeHighTwoLowFin5 u)) =
            (fun u => u = 0 ∨ u = 1 ∨ u = 2) := by
        funext u
        fin_cases u <;> simp [nearOne, threeHighTwoLowFin5, mostParams] <;> norm_num
      have hcount : Fintype.card {u : Fin 5 // u = 0 ∨ u = 1 ∨ u = 2} = 3 := by
        decide
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount, hcount]
    rw [hMostFrac]
    norm_num [mostParams]

/-- ITV fixtures for explicit rule-4 non-equivalence witness. -/
def itvHi : ITV where
  lower := 0.9
  upper := 1
  credibility := 0.8
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def itvLo : ITV where
  lower := 0
  upper := 0.2
  credibility := 0.8
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def itvG : ITV where
  lower := 0.55
  upper := 0.65
  credibility := 0.9
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

/-- ε=0.2 makes "near one" mean `x ≥ 0.8`. -/
def itvConjunctionSeparationParams : FuzzyQuantifierParams where
  ε := 0.2
  LPC := 0
  UPC := 1
  PCL := 0
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Profile induced by ITV midpoint strengths. -/
noncomputable def itvSeparationStrengthProfile : Bool → ℝ :=
  fun b => (if b then itvHi else itvLo).strength

/-- Concrete ITV-valued finite fixture used by coordinate bridge canaries. -/
def itvSeparationProfile : Bool → ITV :=
  fun b => if b then itvHi else itvLo

/-- Ch.11 Rule-4 non-equivalence witness on an ITV-based path:

`∃x (G ∧ F(x))` score is not equal to `G ∧ ∃x F(x)` score under proxy-threshold
aggregation. -/
theorem canary_existentialConjunction_not_equivalent_itvPath :
    fuzzyExistsScore itvConjunctionSeparationParams
      (conjoinProfile itvG.strength itvSeparationStrengthProfile)
      ≠
    min itvG.strength (fuzzyExistsScore itvConjunctionSeparationParams itvSeparationStrengthProfile) := by
  have hLeft :
      fuzzyExistsScore itvConjunctionSeparationParams (conjoinProfile itvG.strength itvSeparationStrengthProfile) = (0 : ℝ) := by
    unfold fuzzyExistsScore nearOneFraction witnessFraction witnessCount nearOne
    unfold conjoinProfile itvSeparationStrengthProfile itvConjunctionSeparationParams
    norm_num [ITV.strength, itvG, itvHi, itvLo]
  have hScore :
      fuzzyExistsScore itvConjunctionSeparationParams itvSeparationStrengthProfile = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne itvConjunctionSeparationParams (itvSeparationStrengthProfile u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvSeparationStrengthProfile, itvConjunctionSeparationParams, ITV.strength, itvHi, itvLo] <;> norm_num
    unfold fuzzyExistsScore nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hRight :
      min itvG.strength (fuzzyExistsScore itvConjunctionSeparationParams itvSeparationStrengthProfile) = (1 / 2 : ℝ) := by
    rw [hScore]
    norm_num [ITV.strength, itvG]
  rw [hLeft, hRight]
  norm_num

/-- ITV-coordinate bridge canary:
lower/upper fuzzy-interval truth transfers to strength-profile truth. -/
theorem canary_itv_strength_interval_of_lower_upper :
    fuzzyIntervalHolds manyParams (itvLowerProfile itvSeparationProfile) ∧
      fuzzyIntervalHolds manyParams (itvUpperProfile itvSeparationProfile) ∧
      fuzzyIntervalHolds manyParams (itvStrengthProfile itvSeparationProfile) := by
  have hLowerFrac : nearOneFraction manyParams (itvLowerProfile itvSeparationProfile) = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne manyParams ((itvLowerProfile itvSeparationProfile) u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvLowerProfile, itvSeparationProfile, itvHi, itvLo, manyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hUpperFrac : nearOneFraction manyParams (itvUpperProfile itvSeparationProfile) = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne manyParams ((itvUpperProfile itvSeparationProfile) u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvUpperProfile, itvSeparationProfile, itvHi, itvLo, manyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hLower : fuzzyIntervalHolds manyParams (itvLowerProfile itvSeparationProfile) := by
    unfold fuzzyIntervalHolds
    rw [hLowerFrac]
    norm_num [manyParams]
  have hUpper : fuzzyIntervalHolds manyParams (itvUpperProfile itvSeparationProfile) := by
    unfold fuzzyIntervalHolds
    rw [hUpperFrac]
    norm_num [manyParams]
  refine ⟨hLower, hUpper, ?_⟩
  exact fuzzyIntervalHolds_strength_of_lower_upper manyParams itvSeparationProfile hLower hUpper

/-! ### ITV Rule-Family Finite Fixture Corpus (Ch.11 core rules) -/

/-- MOST-style parameters with strict `PCL = 1` for universal-specification fixtures. -/
def mostPCL1Params : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.7
  UPC := 0.9
  PCL := 1
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Bool ITV fixture: all-high. -/
def itvAllHighBool : Bool → ITV := fun _ => itvHi

/-- Bool ITV fixture: all-low. -/
def itvAllLowBool : Bool → ITV := fun _ => itvLo

/-- Bool ITV fixture: one high witness, one low witness. -/
def itvMixedBool : Bool → ITV := fun b => if b then itvHi else itvLo

/-- ITV existential-generalization fixture:
one near-one witness implies strictly positive fuzzy existential score. -/
theorem canary_itv_existential_generalization_mixed :
    0 < fuzzyExistsScore aFewParams (itvStrengthProfile itvMixedBool) := by
  have hWitness : nearOne aFewParams ((itvStrengthProfile itvMixedBool) true) := by
    simp [nearOne, itvStrengthProfile, itvMixedBool, aFewParams, ITV.strength, itvHi]
    norm_num
  exact
    fuzzyExistsScore_pos_of_itvStrengthWitness
      aFewParams itvMixedBool true hWitness

/-- ITV universal-specification fixture (strict threshold):
on an all-high profile with `PCL = 1`, every instance is near-one. -/
theorem canary_itv_universal_specification_allHigh :
    nearOne mostPCL1Params ((itvStrengthProfile itvAllHighBool) false) := by
  have hPred :
      (fun u : Bool => nearOne mostPCL1Params ((itvStrengthProfile itvAllHighBool) u)) =
        (fun _ => True) := by
    funext u
    cases u <;>
      (simp [nearOne, itvStrengthProfile, itvAllHighBool, mostPCL1Params, ITV.strength, itvHi];
        norm_num)
  have hFrac : nearOneFraction mostPCL1Params (itvStrengthProfile itvAllHighBool) = (1 : ℝ) := by
    unfold nearOneFraction
    simp [hPred, witnessFraction, witnessCount]
  have hForAll : fuzzyForAllHolds mostPCL1Params (itvStrengthProfile itvAllHighBool) := by
    unfold fuzzyForAllHolds
    rw [hFrac]
    norm_num [mostPCL1Params]
  exact
    nearOne_itvStrength_of_fuzzyForAll_eq_one
      mostPCL1Params itvAllHighBool false hForAll rfl

/-- ITV exchange fixture on all-low profile:
the existential side is false, and the complemented near-one mass is exactly `1`. -/
theorem canary_itv_exchange_allLow_false :
    ¬ fuzzyThereExistsHolds aFewParams (itvStrengthProfile itvAllLowBool) ∧
      nearOneFraction aFewParams (itvStrengthComplementProfile itvAllLowBool) = (1 : ℝ) := by
  have hCompPred :
      (fun u : Bool =>
          nearOne aFewParams ((itvStrengthComplementProfile itvAllLowBool) u)) =
        (fun _ => True) := by
    funext u
    cases u <;>
      (simp [nearOne, itvStrengthComplementProfile, itvStrengthProfile, itvAllLowBool,
        aFewParams, ITV.strength, itvLo];
       norm_num)
  have hCompFrac :
      nearOneFraction aFewParams (itvStrengthComplementProfile itvAllLowBool) = (1 : ℝ) := by
    unfold nearOneFraction
    simp [hCompPred, witnessFraction, witnessCount]
  have hExch :
      fuzzyThereExistsHolds aFewParams (itvStrengthProfile itvAllLowBool) ↔
        aFewParams.PCL ≤
          1 - nearOneFraction aFewParams (itvStrengthComplementProfile itvAllLowBool) :=
    fuzzyThereExistsHolds_itvStrength_iff_exchange aFewParams itvAllLowBool
  have hRhsFalse :
      ¬ aFewParams.PCL ≤
          1 - nearOneFraction aFewParams (itvStrengthComplementProfile itvAllLowBool) := by
    rw [hCompFrac]
    norm_num [aFewParams]
  constructor
  · intro hThere
    exact hRhsFalse (hExch.mp hThere)
  · exact hCompFrac

/-- End-to-end finite fixture bundle for Ch.11 core rule-family on ITV path:
existential generalization, universal specification, and exchange behavior. -/
theorem canary_itv_rule_family_bundle_bool :
    (0 < fuzzyExistsScore aFewParams (itvStrengthProfile itvMixedBool)) ∧
      (nearOne mostPCL1Params ((itvStrengthProfile itvAllHighBool) false)) ∧
      (¬ fuzzyThereExistsHolds aFewParams (itvStrengthProfile itvAllLowBool)) := by
  refine ⟨canary_itv_existential_generalization_mixed, ?_, ?_⟩
  · exact canary_itv_universal_specification_allHigh
  · exact (canary_itv_exchange_allLow_false).1

end Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
