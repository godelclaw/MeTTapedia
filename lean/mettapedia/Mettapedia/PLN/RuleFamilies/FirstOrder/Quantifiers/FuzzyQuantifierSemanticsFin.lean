import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSemantics
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSemanticsInf

/-!
# Finite fuzzy quantifiers as the counting instance of the arbitrary-domain semantics

The finite Chapter-11 fuzzy quantifier semantics lives in
`FuzzyQuantifierSemantics` (`nearOneFraction`, `fuzzyExistsScore`,
`fuzzyForAllHolds`, ...).  This module proves that, for a profile bounded in
`[0,1]`, it is exactly the arbitrary-domain proxy-cut semantics of
`FuzzyQuantifierSemanticsInf` under the normalized counting capacity
(`nearOneMassInf_counting_eq_nearOneFraction` and its companions).
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers

open scoped unitInterval

/-- Finite Chapter-11 parameters viewed as arbitrary-domain fuzzy parameters. -/
def FuzzyQuantifierParams.toInf (p : FuzzyQuantifierParams) : FuzzyQuantifierParamsInf where
  ε := p.ε
  LPC := p.LPC
  UPC := p.UPC
  PCL := p.PCL
  hε := p.hε
  hLPC := p.hLPC
  hUPC := p.hUPC
  hPCL := p.hPCL
  hLPC_le_UPC := p.hLPC_le_UPC

/-- A bounded finite profile promoted into the arbitrary-domain fuzzy-profile type. -/
def boundedProfileFinToInf
    {U : Type*} (profile : U → ℝ) (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    FuzzyProfile U :=
  FuzzyProfile.ofFn profile hprofile

@[simp] theorem boundedProfileFinToInf_apply
    {U : Type*} (profile : U → ℝ) (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) (u : U) :
    ((boundedProfileFinToInf profile hprofile) u : ℝ) = profile u :=
  FuzzyProfile.ofFn_eval profile hprofile u

@[simp] theorem nearOneInf_toInf_iff
    (p : FuzzyQuantifierParams) (x : ℝ) :
    nearOneInf p.toInf x ↔ nearOne p x := by
  rfl

@[simp] theorem nearZeroInf_toInf_iff
    (p : FuzzyQuantifierParams) (x : ℝ) :
    nearZeroInf p.toInf x ↔ nearZero p x := by
  rfl

section CountingReduction

variable {U : Type*} [Fintype U] [MeasurableSpace U]

/-- Exact reduction of the arbitrary-domain near-one mass to the finite witness
fraction when the capacity is counting and the profile is bounded in `[0,1]`. -/
theorem nearOneMassInf_counting_eq_nearOneFraction
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    (nearOneMassInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) : ℝ) =
      nearOneFraction p profile := by
  classical
  unfold nearOneMassInf nearOneCutInf boundedProfileFinToInf
  unfold FuzzyCapacity.countingCapacity FuzzyCapacity.countingValue
  unfold nearOneFraction witnessFraction witnessCount
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · simp [h0, Fintype.card_subtype]

/-- Exact reduction of the arbitrary-domain near-zero mass to the finite witness
fraction when the capacity is counting and the profile is bounded in `[0,1]`. -/
theorem nearZeroMassInf_counting_eq_nearZeroFraction
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    (nearZeroMassInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) : ℝ) =
      nearZeroFraction p profile := by
  classical
  unfold nearZeroMassInf nearZeroCutInf boundedProfileFinToInf
  unfold FuzzyCapacity.countingCapacity FuzzyCapacity.countingValue
  unfold nearZeroFraction witnessFraction witnessCount
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · simp [h0, Fintype.card_subtype]

/-- Exact reduction of the infinitary existential score to the finite/counting score. -/
theorem fuzzyExistsScoreInf_counting_eq_fuzzyExistsScore
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    (fuzzyExistsScoreInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) : ℝ) =
      fuzzyExistsScore p profile := by
  exact nearOneMassInf_counting_eq_nearOneFraction p profile hprofile

/-- Exact reduction of interval truth under the counting capacity. -/
theorem fuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHolds
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    fuzzyIntervalHoldsInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) ↔
      fuzzyIntervalHolds p profile := by
  unfold fuzzyIntervalHoldsInf fuzzyIntervalHolds
  rw [nearOneMassInf_counting_eq_nearOneFraction p profile hprofile]
  simp [FuzzyQuantifierParams.toInf]

/-- Exact reduction of crisp-leaning universal truth under the counting capacity. -/
theorem fuzzyForAllHoldsInf_counting_iff_fuzzyForAllHolds
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    fuzzyForAllHoldsInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) ↔
      fuzzyForAllHolds p profile := by
  unfold fuzzyForAllHoldsInf fuzzyForAllHolds
  rw [nearOneMassInf_counting_eq_nearOneFraction p profile hprofile]
  simp [FuzzyQuantifierParams.toInf]

/-- Exact reduction of crisp-leaning existential truth under the counting capacity. -/
theorem fuzzyThereExistsHoldsInf_counting_iff_fuzzyThereExistsHolds
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    fuzzyThereExistsHoldsInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) ↔
      fuzzyThereExistsHolds p profile := by
  unfold fuzzyThereExistsHoldsInf fuzzyThereExistsHolds
  rw [nearZeroMassInf_counting_eq_nearZeroFraction p profile hprofile]
  simp [FuzzyQuantifierParams.toInf]

end CountingReduction

end Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
