import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CycleSeedCharacter
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Exact character of one relabeling-cycle family

For a positive cycle length, this module identifies literal local letters
around the cycle that satisfy the relabeling/hypercubic fixed equation with
one local seed fixed by the corresponding hypercubic power.  The product of
the one-step tensor signs is proved to be the tensor sign of that power.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CycleFamilyCharacter

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16LocalLetterCharacter
open SU2LatticeFDCensusNoGo

/-! ## Exact local-letter action and sign laws -/

@[simp] theorem ExactLocalFieldLetter.hypercubicAct_one
    {derivativeCount : ℕ}
    (letter : ExactLocalFieldLetter derivativeCount) :
    letter.hypercubicAct 1 = letter := by
  apply Prod.ext
  · exact planeAction_one letter.1
  · funext position
    rfl

theorem ExactLocalFieldLetter.hypercubicAct_mul
    (left right : Hypercubic4) {derivativeCount : ℕ}
    (letter : ExactLocalFieldLetter derivativeCount) :
    letter.hypercubicAct (left * right) =
      (letter.hypercubicAct right).hypercubicAct left := by
  apply Prod.ext
  · exact planeAction_compose left right letter.1
  · funext position
    rfl

@[simp] theorem ExactLocalFieldLetter.tensorSign_one
    {derivativeCount : ℕ}
    (letter : ExactLocalFieldLetter derivativeCount) :
    letter.tensorSign 1 = 1 := by
  simp [ExactLocalFieldLetter.tensorSign, hypercubic_one_def,
    planeTensorSign, planeReorderSign, OrientedPlane.ordered]

theorem ExactLocalFieldLetter.tensorSign_mul
    (left right : Hypercubic4) {derivativeCount : ℕ}
    (letter : ExactLocalFieldLetter derivativeCount) :
    letter.tensorSign (left * right) =
      letter.tensorSign right *
        (letter.hypercubicAct right).tensorSign left := by
  simp only [ExactLocalFieldLetter.tensorSign, hypercubic_mul_def,
    planeTensorSign_compose, Int.cast_mul,
    Hypercubic4.axisSign_compose, Finset.prod_mul_distrib,
    ExactLocalFieldLetter.hypercubicAct]
  ring_nf

theorem ExactLocalFieldLetter.tensorSign_pow_eq_prod
    (h : Hypercubic4) {derivativeCount : ℕ}
    (letter : ExactLocalFieldLetter derivativeCount) (exponent : ℕ) :
    letter.tensorSign (h ^ exponent) =
      ∏ step ∈ Finset.range exponent,
        (letter.hypercubicAct (h ^ step)).tensorSign h := by
  induction exponent with
  | zero =>
      simp only [pow_zero, ExactLocalFieldLetter.tensorSign_one,
        Finset.range_zero, Finset.prod_empty]
  | succ exponent inductionHypothesis =>
      rw [pow_succ', ExactLocalFieldLetter.tensorSign_mul,
        inductionHypothesis, Finset.prod_range_succ]

/-! ## Fixed families on one positive cycle -/

/-- Moving once around the relabeling cycle applies `h` to the local letter. -/
def IsExactTwistedCycleFamily (h : Hypercubic4)
    {cyclePredecessor derivativeCount : ℕ}
    (family : Fin (cyclePredecessor + 1) →
      ExactLocalFieldLetter derivativeCount) : Prop :=
  ∀ position,
    family (finRotate (cyclePredecessor + 1) position) =
      (family position).hypercubicAct h

abbrev FixedExactCycleFamily (h : Hypercubic4)
    (cyclePredecessor derivativeCount : ℕ) :=
  { family : Fin (cyclePredecessor + 1) →
      ExactLocalFieldLetter derivativeCount //
    IsExactTwistedCycleFamily h family }

abbrev FixedExactCycleSeed (h : Hypercubic4)
    (cyclePredecessor derivativeCount : ℕ) :=
  { letter : ExactLocalFieldLetter derivativeCount //
    letter.hypercubicAct (h ^ (cyclePredecessor + 1)) = letter }

def exactCycleFamilyOfSeed (h : Hypercubic4)
    {cyclePredecessor derivativeCount : ℕ}
    (seed : FixedExactCycleSeed h cyclePredecessor derivativeCount) :
    FixedExactCycleFamily h cyclePredecessor derivativeCount :=
  ⟨fun position => seed.1.hypercubicAct (h ^ position.1), by
    intro position
    by_cases lastPosition : position = Fin.last cyclePredecessor
    · subst position
      rw [finRotate_last]
      change seed.1.hypercubicAct (h ^ 0) =
        (seed.1.hypercubicAct (h ^ cyclePredecessor)).hypercubicAct h
      rw [pow_zero, ExactLocalFieldLetter.hypercubicAct_one,
        ← ExactLocalFieldLetter.hypercubicAct_mul, ← pow_succ', seed.2]
    · have beforeLast : position.1 < cyclePredecessor :=
        (Fin.lt_last_iff_ne_last.mpr lastPosition)
      rw [finRotate_of_lt beforeLast]
      change seed.1.hypercubicAct (h ^ (position.1 + 1)) =
        (seed.1.hypercubicAct (h ^ position.1)).hypercubicAct h
      rw [← ExactLocalFieldLetter.hypercubicAct_mul, ← pow_succ']⟩

theorem fixedExactCycleFamily_eq_seed_power
    (h : Hypercubic4) {cyclePredecessor derivativeCount : ℕ}
    (family : FixedExactCycleFamily h cyclePredecessor derivativeCount)
    (position : Fin (cyclePredecessor + 1)) :
    family.1 position =
      (family.1 0).hypercubicAct (h ^ position.1) := by
  have recurrence : ∀ (step : ℕ) (stepBound : step < cyclePredecessor + 1),
      family.1 ⟨step, stepBound⟩ =
        (family.1 0).hypercubicAct (h ^ step) := by
    intro step stepBound
    induction step with
    | zero =>
        rw [pow_zero, ExactLocalFieldLetter.hypercubicAct_one]
        exact congrArg family.1 (Fin.ext rfl)
    | succ step inductionHypothesis =>
        have beforeLast : step < cyclePredecessor := by omega
        have fixedStep := family.2 ⟨step, by omega⟩
        rw [finRotate_of_lt beforeLast] at fixedStep
        change family.1 ⟨step + 1, stepBound⟩ =
          (family.1 ⟨step, by omega⟩).hypercubicAct h at fixedStep
        rw [fixedStep, inductionHypothesis (by omega),
          ← ExactLocalFieldLetter.hypercubicAct_mul, ← pow_succ']
  exact recurrence position.1 position.2

def exactCycleSeedOfFamily (h : Hypercubic4)
    {cyclePredecessor derivativeCount : ℕ}
    (family : FixedExactCycleFamily h cyclePredecessor derivativeCount) :
    FixedExactCycleSeed h cyclePredecessor derivativeCount :=
  ⟨family.1 0, by
    have closingStep := family.2 (Fin.last cyclePredecessor)
    rw [finRotate_last] at closingStep
    rw [fixedExactCycleFamily_eq_seed_power h family
      (Fin.last cyclePredecessor)] at closingStep
    change family.1 0 =
      ((family.1 0).hypercubicAct (h ^ cyclePredecessor)).hypercubicAct h
      at closingStep
    rw [← ExactLocalFieldLetter.hypercubicAct_mul, ← pow_succ'] at closingStep
    exact closingStep.symm⟩

/-- A literal twisted family on one positive relabeling cycle is equivalent
to its seed fixed by the corresponding hypercubic power. -/
def fixedExactCycleFamilyEquivSeed (h : Hypercubic4)
    (cyclePredecessor derivativeCount : ℕ) :
    FixedExactCycleFamily h cyclePredecessor derivativeCount ≃
      FixedExactCycleSeed h cyclePredecessor derivativeCount where
  toFun := exactCycleSeedOfFamily h
  invFun := exactCycleFamilyOfSeed h
  left_inv := by
    intro family
    apply Subtype.ext
    funext position
    exact (fixedExactCycleFamily_eq_seed_power h family position).symm
  right_inv := by
    intro seed
    apply Subtype.ext
    exact ExactLocalFieldLetter.hypercubicAct_one seed.1

def exactCycleFamilyTensorSign (h : Hypercubic4)
    {cyclePredecessor derivativeCount : ℕ}
    (family : Fin (cyclePredecessor + 1) →
      ExactLocalFieldLetter derivativeCount) : ℚ :=
  ∏ position, (family position).tensorSign h

/-- The product of one-step signs around a fixed cycle is the sign of the
powered action on its seed. -/
theorem fixedExactCycleFamily_tensorSign
    (h : Hypercubic4) {cyclePredecessor derivativeCount : ℕ}
    (family : FixedExactCycleFamily h cyclePredecessor derivativeCount) :
    exactCycleFamilyTensorSign h family.1 =
      (family.1 0).tensorSign (h ^ (cyclePredecessor + 1)) := by
  unfold exactCycleFamilyTensorSign
  calc
    (∏ position : Fin (cyclePredecessor + 1),
        (family.1 position).tensorSign h) =
        ∏ position : Fin (cyclePredecessor + 1),
          ((family.1 0).hypercubicAct (h ^ position.1)).tensorSign h := by
      apply Finset.prod_congr rfl
      intro position _
      rw [fixedExactCycleFamily_eq_seed_power h family]
    _ = ∏ step ∈ Finset.range (cyclePredecessor + 1),
          ((family.1 0).hypercubicAct (h ^ step)).tensorSign h := by
      exact Fin.prod_univ_eq_prod_range
        (fun step : ℕ =>
          ((family.1 0).hypercubicAct (h ^ step)).tensorSign h)
        (cyclePredecessor + 1)
    _ = (family.1 0).tensorSign (h ^ (cyclePredecessor + 1)) :=
      (ExactLocalFieldLetter.tensorSign_pow_eq_prod h
        (family.1 0) (cyclePredecessor + 1)).symm

/-! ## Signed character identity for one cycle -/

def exactCycleFamilyCharacter (h : Hypercubic4)
    (cyclePredecessor derivativeCount : ℕ) : ℚ := by
  classical
  exact
    ∑ family : Fin (cyclePredecessor + 1) →
        ExactLocalFieldLetter derivativeCount,
      if IsExactTwistedCycleFamily h family then
        exactCycleFamilyTensorSign h family
      else 0

private theorem sum_if_eq_sum_fixedSubtype
    {Carrier : Type*} [Fintype Carrier]
    (fixed : Carrier → Prop) [DecidablePred fixed]
    (weight : Carrier → ℚ) :
    (∑ item : Carrier, if fixed item then weight item else 0) =
      ∑ item : {item // fixed item}, weight item.1 := by
  classical
  calc
    (∑ item : Carrier, if fixed item then weight item else 0) =
        ∑ item ∈ (Finset.univ.filter fixed), weight item := by
      exact (Finset.sum_filter fixed weight).symm
    _ = ∑ item : {item // fixed item}, weight item.1 := by
      exact Finset.sum_subtype _ (by simp) weight

/-- The literal signed character of a complete positive relabeling cycle is
the signed fixed-point character of one exact seed under `h` to the cycle
length. -/
theorem exactCycleFamilyCharacter_eq_exactLocalLetterCharacter
    (h : Hypercubic4) (cyclePredecessor derivativeCount : ℕ) :
    exactCycleFamilyCharacter h cyclePredecessor derivativeCount =
      exactLocalLetterCharacter (h ^ (cyclePredecessor + 1))
        derivativeCount := by
  classical
  unfold exactCycleFamilyCharacter exactLocalLetterCharacter
  rw [sum_if_eq_sum_fixedSubtype, sum_if_eq_sum_fixedSubtype]
  apply Fintype.sum_equiv
    (fixedExactCycleFamilyEquivSeed h cyclePredecessor derivativeCount)
  intro family
  exact fixedExactCycleFamily_tensorSign h family

end HypercubicDimension16CycleFamilyCharacter
end YangMills
end QuantumTheory
end Mettapedia
