import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FixedCycleFamilyCarrier
import Mathlib.Logic.Equiv.Prod

/-!
# Decorations on a concrete disjoint union of relabeling cycles

This module supplies a literal label type for a list of cycle lengths and
the block rotation on those labels.  Its signed decoration character is
defined before any conjugacy-class or centralizer calculation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CycleBlockDecoration

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16LocalLetterCharacter
open HypercubicDimension16CycleFamilyCharacter
open HypercubicDimension16FixedCycleFamilyCarrier

/-! ## Concrete block labels and rotation -/

/-- Recursive disjoint union of one finite label set per listed cycle. -/
def CycleBlockLabel : List ℕ → Type
  | [] => PEmpty
  | cycleLength :: rest => Fin cycleLength ⊕ CycleBlockLabel rest

@[reducible] def cycleBlockLabelFintype :
    (parts : List ℕ) → Fintype (CycleBlockLabel parts)
  | [] => by
      change Fintype PEmpty
      exact inferInstance
  | _ :: rest => by
      letI : Fintype (CycleBlockLabel rest) := cycleBlockLabelFintype rest
      change Fintype (Fin _ ⊕ CycleBlockLabel rest)
      exact inferInstance

@[reducible] instance (parts : List ℕ) :
    Fintype (CycleBlockLabel parts) := cycleBlockLabelFintype parts

@[reducible] def cycleBlockLabelDecidableEq :
    (parts : List ℕ) → DecidableEq (CycleBlockLabel parts)
  | [] => by
      change DecidableEq PEmpty
      exact inferInstance
  | _ :: rest => by
      letI : DecidableEq (CycleBlockLabel rest) :=
        cycleBlockLabelDecidableEq rest
      change DecidableEq (Fin _ ⊕ CycleBlockLabel rest)
      exact inferInstance

@[reducible] instance (parts : List ℕ) :
    DecidableEq (CycleBlockLabel parts) := cycleBlockLabelDecidableEq parts

/-- Rotation by one step independently on every displayed block. -/
def cycleBlockRotation :
    (parts : List ℕ) → Equiv.Perm (CycleBlockLabel parts)
  | [] => Equiv.refl _
  | cycleLength :: rest =>
      Equiv.Perm.sumCongr (finRotate cycleLength) (cycleBlockRotation rest)

@[simp] theorem cycleBlockRotation_cons_inl
    (cycleLength : ℕ) (rest : List ℕ) (position : Fin cycleLength) :
    cycleBlockRotation (cycleLength :: rest) (Sum.inl position) =
      Sum.inl (finRotate cycleLength position) :=
  rfl

@[simp] theorem cycleBlockRotation_cons_inr
    (cycleLength : ℕ) (rest : List ℕ)
    (label : CycleBlockLabel rest) :
    cycleBlockRotation (cycleLength :: rest) (Sum.inr label) =
      Sum.inr (cycleBlockRotation rest label) :=
  rfl

theorem card_cycleBlockLabel (parts : List ℕ) :
    Fintype.card (CycleBlockLabel parts) = parts.sum := by
  induction parts with
  | nil => simp [CycleBlockLabel]
  | cons cycleLength rest inductionHypothesis =>
      letI : Fintype (CycleBlockLabel rest) := cycleBlockLabelFintype rest
      change Fintype.card (Fin cycleLength ⊕ CycleBlockLabel rest) =
        cycleLength + rest.sum
      rw [Fintype.card_sum, Fintype.card_fin, inductionHypothesis]

/-! ## One positive block at a fixed derivative length -/

/-- Literal local letters of one positive block satisfying the one-step
rotation/hypercubic equation. -/
def IsBudgetedTwistedCycleFamily (h : Hypercubic4)
    {cyclePredecessor derivativeBudget : ℕ}
    (family : Fin (cyclePredecessor + 1) →
      LocalFieldLetter derivativeBudget) : Prop :=
  ∀ position,
    family (finRotate (cyclePredecessor + 1) position) =
      (family position).hypercubicAct h

abbrev FixedBudgetedCycleFamily (h : Hypercubic4)
    (cyclePredecessor derivativeBudget : ℕ) :=
  { family : Fin (cyclePredecessor + 1) →
      LocalFieldLetter derivativeBudget //
    IsBudgetedTwistedCycleFamily h family }

noncomputable instance fixedBudgetedCycleFamilyFintype
    (h : Hypercubic4) (cyclePredecessor derivativeBudget : ℕ) :
    Fintype (FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget) :=
  Fintype.ofFinite _

/-- The fixed-family fiber whose common derivative length is the displayed
budgeted count. -/
abbrev FixedBudgetedCycleFamilyFiber (h : Hypercubic4)
    (cyclePredecessor derivativeBudget : ℕ)
    (localDerivativeCount : Fin (derivativeBudget + 1)) :=
  { family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget //
    (family.1 0).derivativeCount.1 = localDerivativeCount.1 }

theorem fixedBudgetedCycleFamily_eq_seed_power
    (h : Hypercubic4) {cyclePredecessor derivativeBudget : ℕ}
    (family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget)
    (position : Fin (cyclePredecessor + 1)) :
    family.1 position =
      (family.1 0).hypercubicAct (h ^ position.1) := by
  have recurrence : ∀ (step : ℕ) (stepBound : step < cyclePredecessor + 1),
      family.1 ⟨step, stepBound⟩ =
        (family.1 0).hypercubicAct (h ^ step) := by
    intro step stepBound
    induction step with
    | zero =>
        rw [pow_zero, LocalFieldLetter.hypercubicAct_one]
        exact congrArg family.1 (Fin.ext rfl)
    | succ step inductionHypothesis =>
        have beforeLast : step < cyclePredecessor := by omega
        have fixedStep := family.2 ⟨step, by omega⟩
        rw [finRotate_of_lt beforeLast] at fixedStep
        change family.1 ⟨step + 1, stepBound⟩ =
          (family.1 ⟨step, by omega⟩).hypercubicAct h at fixedStep
        rw [fixedStep, inductionHypothesis (by omega),
          ← LocalFieldLetter.hypercubicAct_mul, ← pow_succ']
  exact recurrence position.1 position.2

theorem fixedBudgetedCycleFamily_derivativeCount_eq_zero
    (h : Hypercubic4) {cyclePredecessor derivativeBudget : ℕ}
    (family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget)
    (position : Fin (cyclePredecessor + 1)) :
    (family.1 position).derivativeCount =
      (family.1 0).derivativeCount := by
  rw [fixedBudgetedCycleFamily_eq_seed_power h family position]
  rfl

theorem fixedBudgetedCycleFamily_sum_derivativeCount
    (h : Hypercubic4) {cyclePredecessor derivativeBudget : ℕ}
    (family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget) :
    (∑ position, (family.1 position).derivativeCount.1) =
      (cyclePredecessor + 1) *
        (family.1 0).derivativeCount.1 := by
  calc
    (∑ position, (family.1 position).derivativeCount.1) =
        ∑ _position : Fin (cyclePredecessor + 1),
          (family.1 0).derivativeCount.1 := by
      apply Finset.sum_congr rfl
      intro position _
      exact congrArg Fin.val
        (fixedBudgetedCycleFamily_derivativeCount_eq_zero h family position)
    _ = (cyclePredecessor + 1) *
        (family.1 0).derivativeCount.1 := by simp

/-- Exact-length families and the corresponding fiber of the actual
budgeted local-letter carrier are equivalent cycle by cycle. -/
def fixedExactCycleFamilyEquivBudgetedFiber
    (h : Hypercubic4) (cyclePredecessor derivativeBudget : ℕ)
    (localDerivativeCount : Fin (derivativeBudget + 1)) :
    FixedExactCycleFamily h cyclePredecessor localDerivativeCount.1 ≃
      FixedBudgetedCycleFamilyFiber h cyclePredecessor derivativeBudget
        localDerivativeCount where
  toFun family :=
    ⟨⟨fun position =>
        (exactLocalFieldLetterEquivFiber derivativeBudget
          localDerivativeCount.1 (Nat.le_of_lt_succ localDerivativeCount.2)
          (family.1 position)).1,
      by
        intro position
        change
          ((exactLocalFieldLetterEquivFiber derivativeBudget
            localDerivativeCount.1
            (Nat.le_of_lt_succ localDerivativeCount.2))
            (family.1 (finRotate (cyclePredecessor + 1) position))).1 =
          (((exactLocalFieldLetterEquivFiber derivativeBudget
            localDerivativeCount.1
            (Nat.le_of_lt_succ localDerivativeCount.2))
            (family.1 position)).1).hypercubicAct h
        rw [family.2 position]
        exact (exactLocalFieldLetterEquivFiber_hypercubicAct h
          derivativeBudget localDerivativeCount.1
          (Nat.le_of_lt_succ localDerivativeCount.2)
          (family.1 position)).symm⟩,
      rfl⟩
  invFun family :=
    ⟨fun position =>
        (exactLocalFieldLetterEquivFiber derivativeBudget
          localDerivativeCount.1 (Nat.le_of_lt_succ localDerivativeCount.2)).symm
          ⟨family.1.1 position, by
            rw [fixedBudgetedCycleFamily_derivativeCount_eq_zero h
              family.1 position]
            exact family.2⟩,
      by
        intro position
        let fiberEquiv := exactLocalFieldLetterEquivFiber derivativeBudget
          localDerivativeCount.1
          (Nat.le_of_lt_succ localDerivativeCount.2)
        let atPosition : LocalFieldLetterFiber derivativeBudget
            localDerivativeCount.1 :=
          ⟨family.1.1 position, by
            rw [fixedBudgetedCycleFamily_derivativeCount_eq_zero h
              family.1 position]
            exact family.2⟩
        let atNext : LocalFieldLetterFiber derivativeBudget
            localDerivativeCount.1 :=
          ⟨family.1.1 (finRotate (cyclePredecessor + 1) position), by
            rw [fixedBudgetedCycleFamily_derivativeCount_eq_zero h
              family.1 (finRotate (cyclePredecessor + 1) position)]
            exact family.2⟩
        change fiberEquiv.symm atNext =
          (fiberEquiv.symm atPosition).hypercubicAct h
        apply fiberEquiv.injective
        rw [fiberEquiv.apply_symm_apply]
        apply Subtype.ext
        change atNext.1 =
          (fiberEquiv ((fiberEquiv.symm atPosition).hypercubicAct h)).1
        calc
          atNext.1 = (atPosition.1).hypercubicAct h :=
            family.1.2 position
          _ = (fiberEquiv (fiberEquiv.symm atPosition)).1.hypercubicAct h := by
            rw [fiberEquiv.apply_symm_apply]
          _ = (fiberEquiv
              ((fiberEquiv.symm atPosition).hypercubicAct h)).1 :=
            exactLocalFieldLetterEquivFiber_hypercubicAct h
              derivativeBudget localDerivativeCount.1
              (Nat.le_of_lt_succ localDerivativeCount.2)
              (fiberEquiv.symm atPosition)⟩
  left_inv := by
    intro family
    apply Subtype.ext
    funext position
    exact (exactLocalFieldLetterEquivFiber derivativeBudget
      localDerivativeCount.1
      (Nat.le_of_lt_succ localDerivativeCount.2)).left_inv
      (family.1 position)
  right_inv := by
    intro family
    apply Subtype.ext
    apply Subtype.ext
    funext position
    exact congrArg Subtype.val
      ((exactLocalFieldLetterEquivFiber derivativeBudget
        localDerivativeCount.1
        (Nat.le_of_lt_succ localDerivativeCount.2)).apply_symm_apply
        ⟨family.1.1 position, by
          rw [fixedBudgetedCycleFamily_derivativeCount_eq_zero h
            family.1 position]
          exact family.2⟩)

def budgetedCycleFamilyTensorSign (h : Hypercubic4)
    {cyclePredecessor derivativeBudget : ℕ}
    (family : Fin (cyclePredecessor + 1) →
      LocalFieldLetter derivativeBudget) : ℚ :=
  ∏ position, (family position).tensorSign h

theorem fixedExactCycleFamilyEquivBudgetedFiber_tensorSign
    (h : Hypercubic4) (cyclePredecessor derivativeBudget : ℕ)
    (localDerivativeCount : Fin (derivativeBudget + 1))
    (family : FixedExactCycleFamily h cyclePredecessor
      localDerivativeCount.1) :
    budgetedCycleFamilyTensorSign h
        (fixedExactCycleFamilyEquivBudgetedFiber h cyclePredecessor
          derivativeBudget localDerivativeCount family).1.1 =
      exactCycleFamilyTensorSign h family.1 := by
  unfold budgetedCycleFamilyTensorSign exactCycleFamilyTensorSign
  apply Finset.prod_congr rfl
  intro position _
  exact exactLocalFieldLetterEquivFiber_tensorSign h derivativeBudget
    localDerivativeCount.1 (Nat.le_of_lt_succ localDerivativeCount.2)
    (family.1 position)

noncomputable instance fixedBudgetedCycleFamilyFiberFintype
    (h : Hypercubic4) (cyclePredecessor derivativeBudget : ℕ)
    (localDerivativeCount : Fin (derivativeBudget + 1)) :
    Fintype (FixedBudgetedCycleFamilyFiber h cyclePredecessor
      derivativeBudget localDerivativeCount) :=
  Fintype.ofFinite _

/-- The signed sum on one actual budgeted fiber equals the already certified
exact-family character. -/
theorem fixedBudgetedCycleFamilyFiber_character
    (h : Hypercubic4) (cyclePredecessor derivativeBudget : ℕ)
    (localDerivativeCount : Fin (derivativeBudget + 1)) :
    (∑ family : FixedBudgetedCycleFamilyFiber h cyclePredecessor
        derivativeBudget localDerivativeCount,
      budgetedCycleFamilyTensorSign h family.1.1) =
      exactCycleFamilyCharacter h cyclePredecessor
        localDerivativeCount.1 := by
  classical
  rw [exactCycleFamilyCharacter_eq_fixedFamilySum]
  symm
  apply Fintype.sum_equiv
    (fixedExactCycleFamilyEquivBudgetedFiber h cyclePredecessor
      derivativeBudget localDerivativeCount)
  intro family
  exact (fixedExactCycleFamilyEquivBudgetedFiber_tensorSign h
    cyclePredecessor derivativeBudget localDerivativeCount family).symm

/-- Partition all fixed budgeted families by their common derivative count. -/
def budgetedCycleFamilySigmaFiberEquiv
    (h : Hypercubic4) (cyclePredecessor derivativeBudget : ℕ) :
    (Sigma fun localDerivativeCount : Fin (derivativeBudget + 1) =>
      FixedBudgetedCycleFamilyFiber h cyclePredecessor derivativeBudget
        localDerivativeCount) ≃
      FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget where
  toFun entry := entry.2.1
  invFun family :=
    ⟨(family.1 0).derivativeCount, ⟨family, rfl⟩⟩
  left_inv := by
    rintro ⟨localDerivativeCount, family⟩
    apply Sigma.subtype_ext
    · apply Fin.ext
      exact family.2
    · rfl
  right_inv := by
    intro family
    apply Subtype.ext
    rfl

/-- Grouping one-cycle families by their exact derivative length recovers
the already certified exact-family character in every fiber. -/
theorem fixedBudgetedCycleFamily_sum_by_derivativeCount
    (h : Hypercubic4) (cyclePredecessor derivativeBudget targetDegree : ℕ)
    (continuation : ℕ → ℚ) :
    (∑ family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget,
      if (cyclePredecessor + 1) *
          (family.1 0).derivativeCount.1 ≤ targetDegree then
        budgetedCycleFamilyTensorSign h family.1 *
          continuation ((family.1 0).derivativeCount.1)
      else 0) =
      ∑ localDerivativeCount : Fin (derivativeBudget + 1),
        if (cyclePredecessor + 1) * localDerivativeCount.1 ≤ targetDegree then
          exactCycleFamilyCharacter h cyclePredecessor
              localDerivativeCount.1 *
            continuation localDerivativeCount.1
        else 0 := by
  classical
  calc
    (∑ family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget,
      if (cyclePredecessor + 1) *
          (family.1 0).derivativeCount.1 ≤ targetDegree then
        budgetedCycleFamilyTensorSign h family.1 *
          continuation ((family.1 0).derivativeCount.1)
      else 0) =
      ∑ entry :
          (Sigma fun localDerivativeCount : Fin (derivativeBudget + 1) =>
            FixedBudgetedCycleFamilyFiber h cyclePredecessor derivativeBudget
              localDerivativeCount),
        if (cyclePredecessor + 1) * entry.1.1 ≤ targetDegree then
          budgetedCycleFamilyTensorSign h entry.2.1.1 *
            continuation entry.1.1
        else 0 := by
      apply Fintype.sum_equiv
        (budgetedCycleFamilySigmaFiberEquiv h cyclePredecessor
          derivativeBudget).symm
      intro family
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro localDerivativeCount _
      by_cases headBound : (cyclePredecessor + 1) *
          localDerivativeCount.1 ≤ targetDegree
      · simp only [if_pos headBound]
        rw [← Finset.sum_mul,
          fixedBudgetedCycleFamilyFiber_character]
      · simp [headBound]

/-- Counts admitted by an ambient budget and by the residual degree. -/
abbrev AdmissibleBudgetedDerivativeCount
    (derivativeBudget cycleLength targetDegree : ℕ) :=
  { count : Fin (derivativeBudget + 1) //
    cycleLength * count.1 ≤ targetDegree }

/-- When the ambient budget dominates the target degree, the admissible
budgeted counts are exactly the usual `0 .. target / cycleLength` range. -/
def admissibleBudgetedDerivativeCountEquivResidual
    (derivativeBudget cycleLength targetDegree : ℕ)
    (cyclePositive : 0 < cycleLength)
    (targetWithinBudget : targetDegree ≤ derivativeBudget) :
    AdmissibleBudgetedDerivativeCount derivativeBudget cycleLength
        targetDegree ≃
      Fin (targetDegree / cycleLength + 1) where
  toFun count :=
    ⟨count.1.1, Nat.lt_succ_iff.mpr <| by
      rw [Nat.le_div_iff_mul_le cyclePositive]
      simpa [mul_comm] using count.2⟩
  invFun count :=
    ⟨⟨count.1, by
        have countLe : count.1 ≤ targetDegree / cycleLength :=
          Nat.lt_succ_iff.mp count.2
        have quotientLe : targetDegree / cycleLength ≤ targetDegree :=
          Nat.div_le_self targetDegree cycleLength
        omega⟩,
      by
        have countLe : count.1 ≤ targetDegree / cycleLength :=
          Nat.lt_succ_iff.mp count.2
        rw [Nat.le_div_iff_mul_le cyclePositive] at countLe
        simpa [mul_comm] using countLe⟩
  left_inv := by
    intro count
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv := by
    intro count
    apply Fin.ext
    rfl

theorem sum_budgeted_count_if_admissible
    (derivativeBudget cycleLength targetDegree : ℕ)
    (cyclePositive : 0 < cycleLength)
    (targetWithinBudget : targetDegree ≤ derivativeBudget)
    (weight : ℕ → ℚ) :
    (∑ count : Fin (derivativeBudget + 1),
      if cycleLength * count.1 ≤ targetDegree then weight count.1 else 0) =
      ∑ count : Fin (targetDegree / cycleLength + 1), weight count.1 := by
  classical
  calc
    (∑ count : Fin (derivativeBudget + 1),
      if cycleLength * count.1 ≤ targetDegree then weight count.1 else 0) =
      ∑ count ∈ (Finset.univ.filter
          (fun count : Fin (derivativeBudget + 1) =>
            cycleLength * count.1 ≤ targetDegree)),
        weight count.1 := by
      exact (Finset.sum_filter _ _).symm
    _ = ∑ count : AdmissibleBudgetedDerivativeCount derivativeBudget
          cycleLength targetDegree, weight count.1.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ count : Fin (targetDegree / cycleLength + 1),
          weight count.1 := by
      apply Fintype.sum_equiv
        (admissibleBudgetedDerivativeCountEquivResidual derivativeBudget
          cycleLength targetDegree cyclePositive targetWithinBudget)
      intro count
      rfl

/-- The exact degree condition and pointwise relabeling/hypercubic fixed
equation, written on a total family rather than a subtype. -/
def IsTwistedIndexedDecoration
    {Label : Type*} [Fintype Label]
    (h : Hypercubic4) (rename : Equiv.Perm Label)
    (derivativeBudget targetDegree : ℕ)
    (letters : Label → LocalFieldLetter derivativeBudget) : Prop :=
  (∑ label, (letters label).derivativeCount.1) = targetDegree ∧
    ∀ label, letters (rename label) = (letters label).hypercubicAct h

/-- Literal fixed decorations on the displayed block rotation. -/
abbrev FixedCycleBlockDecoration (h : Hypercubic4)
    (parts : List ℕ) (derivativeBudget targetDegree : ℕ) :=
  { letters : CycleBlockLabel parts → LocalFieldLetter derivativeBudget //
    IsTwistedIndexedDecoration h (cycleBlockRotation parts)
      derivativeBudget targetDegree letters }

/-! ## A budget-stable recursive carrier -/

/-- Recursive fixed-cycle carrier which retains one ambient local-letter
budget.  The head count is restricted by the exact residual degree, while
the underlying letter type remains unchanged down the recursion. -/
def FixedBudgetedCycleCarrier (h : Hypercubic4) (derivativeBudget : ℕ) :
    List ℕ → ℕ → Type
  | [], targetDegree => PLift (targetDegree = 0)
  | 0 :: _, _ => PEmpty
  | (cyclePredecessor + 1) :: rest, targetDegree =>
      ULift
        (Sigma fun family :
          FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget =>
          PLift ((cyclePredecessor + 1) *
              (family.1 0).derivativeCount.1 ≤ targetDegree) ×
            FixedBudgetedCycleCarrier h derivativeBudget rest
              (targetDegree -
                (cyclePredecessor + 1) *
                  (family.1 0).derivativeCount.1))

@[reducible] noncomputable def fixedBudgetedCycleCarrierFintypeDef
    (h : Hypercubic4) (derivativeBudget : ℕ) :
    (parts : List ℕ) → (targetDegree : ℕ) →
      Fintype (FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree)
  | [], targetDegree => by
      change Fintype (PLift (targetDegree = 0))
      exact Fintype.ofFinite _
  | 0 :: _, _ => by
      change Fintype PEmpty
      exact inferInstance
  | (cyclePredecessor + 1) :: rest, targetDegree => by
      change Fintype
        (ULift
          (Sigma fun family :
            FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget =>
            PLift ((cyclePredecessor + 1) *
                (family.1 0).derivativeCount.1 ≤ targetDegree) ×
              FixedBudgetedCycleCarrier h derivativeBudget rest
                (targetDegree -
                  (cyclePredecessor + 1) *
                    (family.1 0).derivativeCount.1)))
      letI (family : FixedBudgetedCycleFamily h cyclePredecessor
          derivativeBudget) :
          Fintype (FixedBudgetedCycleCarrier h derivativeBudget rest
            (targetDegree -
              (cyclePredecessor + 1) *
                (family.1 0).derivativeCount.1)) :=
        fixedBudgetedCycleCarrierFintypeDef h derivativeBudget rest _
      exact inferInstance

@[reducible] noncomputable instance fixedBudgetedCycleCarrierFintype
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ) :
    Fintype (FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree) :=
  fixedBudgetedCycleCarrierFintypeDef h derivativeBudget parts targetDegree

def FixedBudgetedCycleCarrier.tensorSign (h : Hypercubic4)
    (derivativeBudget : ℕ) :
    (parts : List ℕ) → (targetDegree : ℕ) →
      FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree → ℚ
  | [], _, _ => 1
  | 0 :: _, _, carrier => nomatch carrier
  | (cyclePredecessor + 1) :: rest, targetDegree,
      ⟨⟨family, _, tail⟩⟩ =>
      budgetedCycleFamilyTensorSign h family.1 *
        FixedBudgetedCycleCarrier.tensorSign h derivativeBudget rest
          (targetDegree -
            (cyclePredecessor + 1) *
              (family.1 0).derivativeCount.1) tail

/-- Complete signed sum on the budget-stable recursive carrier. -/
def fixedBudgetedCycleCarrierCharacter (h : Hypercubic4)
    (derivativeBudget : ℕ) (parts : List ℕ) (targetDegree : ℕ) : ℚ :=
  ∑ carrier : FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree,
    carrier.tensorSign h derivativeBudget parts targetDegree

theorem fixedBudgetedCycleCarrierCharacter_nil
    (h : Hypercubic4) (derivativeBudget targetDegree : ℕ) :
    fixedBudgetedCycleCarrierCharacter h derivativeBudget [] targetDegree =
      if targetDegree = 0 then 1 else 0 := by
  classical
  by_cases targetZero : targetDegree = 0
  · subst targetDegree
    simp [fixedBudgetedCycleCarrierCharacter, FixedBudgetedCycleCarrier,
      FixedBudgetedCycleCarrier.tensorSign]
  · haveI : IsEmpty (PLift (targetDegree = 0)) :=
      ⟨fun witness => targetZero witness.down⟩
    simp [fixedBudgetedCycleCarrierCharacter, FixedBudgetedCycleCarrier,
      targetZero]

@[simp] theorem fixedBudgetedCycleCarrierCharacter_zero_cons
    (h : Hypercubic4) (derivativeBudget targetDegree : ℕ)
    (rest : List ℕ) :
    fixedBudgetedCycleCarrierCharacter h derivativeBudget (0 :: rest)
      targetDegree = 0 := by
  classical
  simp [fixedBudgetedCycleCarrierCharacter, FixedBudgetedCycleCarrier]

theorem fixedBudgetedCycleCarrierCharacter_cons_succ
    (h : Hypercubic4) (derivativeBudget cyclePredecessor targetDegree : ℕ)
    (rest : List ℕ) :
    fixedBudgetedCycleCarrierCharacter h derivativeBudget
        ((cyclePredecessor + 1) :: rest) targetDegree =
      ∑ family : FixedBudgetedCycleFamily h cyclePredecessor derivativeBudget,
        if (cyclePredecessor + 1) *
            (family.1 0).derivativeCount.1 ≤ targetDegree then
          budgetedCycleFamilyTensorSign h family.1 *
            fixedBudgetedCycleCarrierCharacter h derivativeBudget rest
              (targetDegree -
                (cyclePredecessor + 1) *
                  (family.1 0).derivativeCount.1)
        else 0 := by
  classical
  unfold fixedBudgetedCycleCarrierCharacter
  let decomposition :
      FixedBudgetedCycleCarrier h derivativeBudget
          ((cyclePredecessor + 1) :: rest) targetDegree ≃
        (Sigma fun family : FixedBudgetedCycleFamily h cyclePredecessor
            derivativeBudget =>
          PLift ((cyclePredecessor + 1) *
              (family.1 0).derivativeCount.1 ≤ targetDegree) ×
            FixedBudgetedCycleCarrier h derivativeBudget rest
              (targetDegree -
                (cyclePredecessor + 1) *
                  (family.1 0).derivativeCount.1)) :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (∑ carrier : FixedBudgetedCycleCarrier h derivativeBudget
          ((cyclePredecessor + 1) :: rest) targetDegree,
        carrier.tensorSign h derivativeBudget
          ((cyclePredecessor + 1) :: rest) targetDegree) =
      ∑ entry :
          (Sigma fun family : FixedBudgetedCycleFamily h cyclePredecessor
              derivativeBudget =>
            PLift ((cyclePredecessor + 1) *
                (family.1 0).derivativeCount.1 ≤ targetDegree) ×
              FixedBudgetedCycleCarrier h derivativeBudget rest
                (targetDegree -
                  (cyclePredecessor + 1) *
                    (family.1 0).derivativeCount.1)),
        budgetedCycleFamilyTensorSign h entry.1.1 *
          entry.2.2.tensorSign h derivativeBudget rest
            (targetDegree -
              (cyclePredecessor + 1) *
                (entry.1.1 0).derivativeCount.1) := by
      apply Fintype.sum_equiv decomposition
      rintro ⟨⟨family, proof, tail⟩⟩
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro family _
      by_cases headBound : (cyclePredecessor + 1) *
          (family.1 0).derivativeCount.1 ≤ targetDegree
      · letI : Unique (PLift ((cyclePredecessor + 1) *
            (family.1 0).derivativeCount.1 ≤ targetDegree)) :=
          { default := PLift.up headBound
            uniq := fun _ => Subsingleton.elim _ _ }
        rw [if_pos headBound, Fintype.sum_prod_type]
        simp only [Fintype.sum_unique]
        rw [← Finset.mul_sum]
      · letI : IsEmpty (PLift ((cyclePredecessor + 1) *
            (family.1 0).derivativeCount.1 ≤ targetDegree)) :=
          ⟨fun witness => headBound witness.down⟩
        rw [if_neg headBound, Fintype.sum_prod_type]
        simp

/-! ## Literal block decorations and the budget-stable carrier -/

def fixedCycleBlockDecorationToBudgetedCarrier (h : Hypercubic4)
    (derivativeBudget : ℕ) :
    (parts : List ℕ) → (targetDegree : ℕ) →
      (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) →
      FixedCycleBlockDecoration h parts derivativeBudget targetDegree →
        FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree
  | [], targetDegree, _, decoration =>
      PLift.up (by
        have totalDegree := decoration.2.1
        simp [CycleBlockLabel] at totalDegree
        exact totalDegree.symm)
  | 0 :: rest, _, positiveParts, _ =>
      False.elim (Nat.lt_irrefl 0 (positiveParts 0 (by simp)))
  | (cyclePredecessor + 1) :: rest, targetDegree,
      positiveParts, decoration => by
      let headFamily : FixedBudgetedCycleFamily h cyclePredecessor
          derivativeBudget :=
        ⟨fun position => decoration.1 (Sum.inl position), by
          intro position
          exact decoration.2.2 (Sum.inl position)⟩
      have totalSplit :
          (∑ position, (headFamily.1 position).derivativeCount.1) +
            ∑ label : CycleBlockLabel rest,
              (decoration.1 (Sum.inr label)).derivativeCount.1 =
            targetDegree := by
        have totalDegree := decoration.2.1
        change
          (∑ label : Fin (cyclePredecessor + 1) ⊕ CycleBlockLabel rest,
            (decoration.1 label).derivativeCount.1) = targetDegree
          at totalDegree
        rw [Fintype.sum_sum_type] at totalDegree
        exact totalDegree
      have headDegree :=
        fixedBudgetedCycleFamily_sum_derivativeCount h headFamily
      have headBound :
          (cyclePredecessor + 1) *
              (headFamily.1 0).derivativeCount.1 ≤
            targetDegree := by
        omega
      have tailDegree :
          (∑ label : CycleBlockLabel rest,
              (decoration.1 (Sum.inr label)).derivativeCount.1) =
            targetDegree -
              (cyclePredecessor + 1) *
                (headFamily.1 0).derivativeCount.1 := by
        omega
      let tailDecoration : FixedCycleBlockDecoration h rest derivativeBudget
          (targetDegree -
            (cyclePredecessor + 1) *
              (headFamily.1 0).derivativeCount.1) :=
        ⟨fun label => decoration.1 (Sum.inr label),
          ⟨tailDegree, fun label => decoration.2.2 (Sum.inr label)⟩⟩
      let tailCarrier :=
        fixedCycleBlockDecorationToBudgetedCarrier h derivativeBudget rest
          (targetDegree -
            (cyclePredecessor + 1) *
              (headFamily.1 0).derivativeCount.1)
          (fun laterCycle laterMembership =>
            positiveParts laterCycle (by simp [laterMembership]))
          tailDecoration
      exact ULift.up ⟨headFamily, PLift.up headBound, tailCarrier⟩

def fixedBudgetedCarrierToCycleBlockDecoration (h : Hypercubic4)
    (derivativeBudget : ℕ) :
    (parts : List ℕ) → (targetDegree : ℕ) →
      (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) →
      FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree →
        FixedCycleBlockDecoration h parts derivativeBudget targetDegree
  | [], targetDegree, _, carrier => by
      refine ⟨(fun label : CycleBlockLabel [] => nomatch label), ?_⟩
      constructor
      · change 0 = targetDegree
        exact carrier.down.symm
      · intro label
        nomatch label
  | 0 :: rest, _, _, carrier => nomatch carrier
  | (cyclePredecessor + 1) :: rest, targetDegree,
      positiveParts, ⟨⟨family, headBound, tail⟩⟩ => by
      let tailDecoration :=
        fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget rest
          (targetDegree -
            (cyclePredecessor + 1) *
              (family.1 0).derivativeCount.1)
          (fun laterCycle laterMembership =>
            positiveParts laterCycle (by simp [laterMembership])) tail
      refine ⟨Sum.elim family.1 tailDecoration.1, ?_⟩
      constructor
      · change
          (∑ label : Fin (cyclePredecessor + 1) ⊕ CycleBlockLabel rest,
            (Sum.elim family.1 tailDecoration.1 label).derivativeCount.1) =
              targetDegree
        rw [Fintype.sum_sum_type]
        change
          (∑ position, (family.1 position).derivativeCount.1) +
            (∑ label, (tailDecoration.1 label).derivativeCount.1) =
              targetDegree
        rw [fixedBudgetedCycleFamily_sum_derivativeCount h family,
          tailDecoration.2.1]
        exact Nat.add_sub_of_le headBound.down
      · intro label
        cases label with
        | inl position => exact family.2 position
        | inr tailLabel => exact tailDecoration.2.2 tailLabel

theorem fixedBudgetedCarrierToCycleBlockDecoration_after_to
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength)
    (decoration : FixedCycleBlockDecoration h parts derivativeBudget
      targetDegree) :
    fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget parts
        targetDegree positiveParts
        (fixedCycleBlockDecorationToBudgetedCarrier h derivativeBudget parts
          targetDegree positiveParts decoration) =
      decoration := by
  induction parts generalizing targetDegree with
  | nil =>
      apply Subtype.ext
      funext label
      nomatch label
  | cons cycleLength rest inductionHypothesis =>
      have cyclePositive := positiveParts cycleLength (by simp)
      obtain ⟨cyclePredecessor, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt cyclePositive)
      let headFamily : FixedBudgetedCycleFamily h cyclePredecessor
          derivativeBudget :=
        ⟨fun position => decoration.1 (Sum.inl position), by
          intro position
          exact decoration.2.2 (Sum.inl position)⟩
      have totalSplit :
          (∑ position, (headFamily.1 position).derivativeCount.1) +
            ∑ label : CycleBlockLabel rest,
              (decoration.1 (Sum.inr label)).derivativeCount.1 =
            targetDegree := by
        have totalDegree := decoration.2.1
        change
          (∑ label : Fin (cyclePredecessor + 1) ⊕ CycleBlockLabel rest,
            (decoration.1 label).derivativeCount.1) = targetDegree
          at totalDegree
        rw [Fintype.sum_sum_type] at totalDegree
        exact totalDegree
      have headDegree :=
        fixedBudgetedCycleFamily_sum_derivativeCount h headFamily
      have headBound :
          (cyclePredecessor + 1) *
              (headFamily.1 0).derivativeCount.1 ≤
            targetDegree := by
        omega
      have tailDegree :
          (∑ label : CycleBlockLabel rest,
              (decoration.1 (Sum.inr label)).derivativeCount.1) =
            targetDegree -
              (cyclePredecessor + 1) *
                (headFamily.1 0).derivativeCount.1 := by
        omega
      let tailDecoration : FixedCycleBlockDecoration h rest derivativeBudget
          (targetDegree -
            (cyclePredecessor + 1) *
              (headFamily.1 0).derivativeCount.1) :=
        ⟨fun label => decoration.1 (Sum.inr label),
          ⟨tailDegree, fun label => decoration.2.2 (Sum.inr label)⟩⟩
      have tailIdentity := inductionHypothesis
        (targetDegree -
          (cyclePredecessor + 1) *
            (headFamily.1 0).derivativeCount.1)
        (fun laterCycle laterMembership =>
          positiveParts laterCycle (by simp [laterMembership]))
        tailDecoration
      apply Subtype.ext
      funext label
      cases label with
      | inl position => rfl
      | inr tailLabel =>
          exact congrFun (congrArg Subtype.val tailIdentity) tailLabel

theorem fixedCycleBlockDecorationToBudgetedCarrier_after_from
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength)
    (carrier : FixedBudgetedCycleCarrier h derivativeBudget parts
      targetDegree) :
    fixedCycleBlockDecorationToBudgetedCarrier h derivativeBudget parts
        targetDegree positiveParts
        (fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget parts
          targetDegree positiveParts carrier) =
      carrier := by
  induction parts generalizing targetDegree with
  | nil =>
      rcases carrier with ⟨proof⟩
      rfl
  | cons cycleLength rest inductionHypothesis =>
      have cyclePositive := positiveParts cycleLength (by simp)
      obtain ⟨cyclePredecessor, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt cyclePositive)
      rcases carrier with ⟨⟨family, headBound, tail⟩⟩
      have tailIdentity := inductionHypothesis
        (targetDegree -
          (cyclePredecessor + 1) *
            (family.1 0).derivativeCount.1)
        (fun laterCycle laterMembership =>
          positiveParts laterCycle (by simp [laterMembership])) tail
      let tailDecoration :=
        fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget rest
          (targetDegree -
            (cyclePredecessor + 1) *
              (family.1 0).derivativeCount.1)
          (fun laterCycle laterMembership =>
            positiveParts laterCycle (by simp [laterMembership])) tail
      let recoveredFamily : FixedBudgetedCycleFamily h cyclePredecessor
          derivativeBudget :=
        ⟨fun position => family.1 position, family.2⟩
      change
        ULift.up
          (⟨recoveredFamily,
            (PLift.up _,
              fixedCycleBlockDecorationToBudgetedCarrier h derivativeBudget rest
                (targetDegree -
                  (cyclePredecessor + 1) *
                    (recoveredFamily.1 0).derivativeCount.1)
                _ tailDecoration)⟩ :
            Sigma fun fixedFamily : FixedBudgetedCycleFamily h
                cyclePredecessor derivativeBudget =>
              PLift ((cyclePredecessor + 1) *
                  (fixedFamily.1 0).derivativeCount.1 ≤ targetDegree) ×
                FixedBudgetedCycleCarrier h derivativeBudget rest
                  (targetDegree - (cyclePredecessor + 1) *
                    (fixedFamily.1 0).derivativeCount.1)) =
          ULift.up
            (⟨family, (headBound, tail)⟩ :
              Sigma fun fixedFamily : FixedBudgetedCycleFamily h
                  cyclePredecessor derivativeBudget =>
                PLift ((cyclePredecessor + 1) *
                    (fixedFamily.1 0).derivativeCount.1 ≤ targetDegree) ×
                  FixedBudgetedCycleCarrier h derivativeBudget rest
                    (targetDegree - (cyclePredecessor + 1) *
                      (fixedFamily.1 0).derivativeCount.1))
      apply ULift.ext
      have familyIdentity : recoveredFamily = family := by
        apply Subtype.ext
        rfl
      refine Sigma.ext familyIdentity ?_
      cases familyIdentity
      rw [heq_iff_eq]
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact tailIdentity

/-- Literal fixed block decorations and the recursive budget-stable carrier
are equivalent, not merely equinumerous. -/
def fixedCycleBlockDecorationEquivBudgetedCarrier
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    FixedCycleBlockDecoration h parts derivativeBudget targetDegree ≃
      FixedBudgetedCycleCarrier h derivativeBudget parts targetDegree where
  toFun := fixedCycleBlockDecorationToBudgetedCarrier h derivativeBudget
    parts targetDegree positiveParts
  invFun := fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget
    parts targetDegree positiveParts
  left_inv := fixedBudgetedCarrierToCycleBlockDecoration_after_to h
    derivativeBudget parts targetDegree positiveParts
  right_inv := fixedCycleBlockDecorationToBudgetedCarrier_after_from h
    derivativeBudget parts targetDegree positiveParts

theorem fixedBudgetedCarrierToCycleBlockDecoration_tensorSign
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength)
    (carrier : FixedBudgetedCycleCarrier h derivativeBudget parts
      targetDegree) :
    (∏ label,
      ((fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget parts
        targetDegree positiveParts carrier).1 label).tensorSign h) =
      carrier.tensorSign h derivativeBudget parts targetDegree := by
  induction parts generalizing targetDegree with
  | nil =>
      rcases carrier with ⟨proof⟩
      simp [fixedBudgetedCarrierToCycleBlockDecoration,
        FixedBudgetedCycleCarrier.tensorSign, CycleBlockLabel]
  | cons cycleLength rest inductionHypothesis =>
      have cyclePositive := positiveParts cycleLength (by simp)
      obtain ⟨cyclePredecessor, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt cyclePositive)
      rcases carrier with ⟨⟨family, headBound, tail⟩⟩
      have tailIdentity := inductionHypothesis
        (targetDegree -
          (cyclePredecessor + 1) *
            (family.1 0).derivativeCount.1)
        (fun laterCycle laterMembership =>
          positiveParts laterCycle (by simp [laterMembership])) tail
      change
        (∏ label : Fin (cyclePredecessor + 1) ⊕ CycleBlockLabel rest,
          ((fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget
            ((cyclePredecessor + 1) :: rest) targetDegree positiveParts
            (ULift.up ⟨family, (headBound, tail)⟩)).1 label).tensorSign h) = _
      rw [Fintype.prod_sum_type]
      change
        budgetedCycleFamilyTensorSign h family.1 *
          (∏ label : CycleBlockLabel rest,
            ((fixedBudgetedCarrierToCycleBlockDecoration h derivativeBudget
              rest
              (targetDegree -
                (cyclePredecessor + 1) *
                  (family.1 0).derivativeCount.1)
              _ tail).1 label).tensorSign h) = _
      rw [tailIdentity]
      rfl

/-- With an ambient budget at least the exact target degree, the
budget-stable carrier has exactly the same signed character as the dependent
exact-family carrier. -/
theorem fixedBudgetedCycleCarrierCharacter_eq_fixedCycleFamilyCharacter
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength)
    (targetWithinBudget : targetDegree ≤ derivativeBudget) :
    fixedBudgetedCycleCarrierCharacter h derivativeBudget parts targetDegree =
      fixedCycleFamilyCharacter h parts targetDegree := by
  induction parts generalizing targetDegree with
  | nil =>
      rw [fixedBudgetedCycleCarrierCharacter_nil,
        fixedCycleFamilyCharacter_nil]
  | cons cycleLength rest inductionHypothesis =>
      have cyclePositive := positiveParts cycleLength (by simp)
      obtain ⟨cyclePredecessor, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt cyclePositive)
      rw [fixedBudgetedCycleCarrierCharacter_cons_succ]
      rw [fixedBudgetedCycleFamily_sum_by_derivativeCount
        (continuation := fun localDerivativeCount =>
          fixedBudgetedCycleCarrierCharacter h derivativeBudget rest
            (targetDegree -
              (cyclePredecessor + 1) * localDerivativeCount))]
      rw [sum_budgeted_count_if_admissible derivativeBudget
        (cyclePredecessor + 1) targetDegree (by omega) targetWithinBudget
        (fun localDerivativeCount =>
          exactCycleFamilyCharacter h cyclePredecessor localDerivativeCount *
            fixedBudgetedCycleCarrierCharacter h derivativeBudget rest
              (targetDegree -
                (cyclePredecessor + 1) * localDerivativeCount))]
      rw [fixedCycleFamilyCharacter_cons_succ]
      apply Finset.sum_congr rfl
      intro localDerivativeCount _
      rw [inductionHypothesis]
      · intro laterCycle laterMembership
        exact positiveParts laterCycle (by simp [laterMembership])
      · exact le_trans (Nat.sub_le _ _) targetWithinBudget

/-! ## Signed fixed-decoration character on arbitrary finite labels -/

/-- Signed contribution of one indexed decoration, with a single named
decision procedure shared by all character decompositions. -/
def indexedDecorationWeight
    {Label : Type*} [Fintype Label]
    (h : Hypercubic4) (rename : Equiv.Perm Label)
    (derivativeBudget targetDegree : ℕ)
    (letters : Label → LocalFieldLetter derivativeBudget) : ℚ := by
  classical
  exact
    if IsTwistedIndexedDecoration h rename derivativeBudget targetDegree letters
    then ∏ label, (letters label).tensorSign h
    else 0

/-- Signed fixed-point sum of local-word decorations on an arbitrary finite
label type.  The derivative budget is separated from the exact target degree
so recursive block decompositions do not silently change the letter type. -/
def indexedDecorationCharacter
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (h : Hypercubic4) (rename : Equiv.Perm Label)
    (derivativeBudget targetDegree : ℕ) : ℚ := by
  classical
  exact
    ∑ letters : Label → LocalFieldLetter derivativeBudget,
      indexedDecorationWeight h rename derivativeBudget targetDegree letters

/-- Specialization to the displayed disjoint-cycle rotation. -/
def cycleBlockDecorationCharacter (h : Hypercubic4)
    (parts : List ℕ) (derivativeBudget targetDegree : ℕ) : ℚ :=
  indexedDecorationCharacter h (cycleBlockRotation parts)
    derivativeBudget targetDegree

noncomputable instance fixedCycleBlockDecorationFintype
    (h : Hypercubic4) (parts : List ℕ)
    (derivativeBudget targetDegree : ℕ) :
    Fintype (FixedCycleBlockDecoration h parts derivativeBudget targetDegree) :=
  Fintype.ofFinite _

theorem cycleBlockDecorationCharacter_eq_fixedSum
    (h : Hypercubic4) (parts : List ℕ)
    (derivativeBudget targetDegree : ℕ) :
    cycleBlockDecorationCharacter h parts derivativeBudget targetDegree =
      ∑ decoration : FixedCycleBlockDecoration h parts
          derivativeBudget targetDegree,
        ∏ label, (decoration.1 label).tensorSign h := by
  classical
  unfold cycleBlockDecorationCharacter indexedDecorationCharacter
    indexedDecorationWeight
  calc
    (∑ letters : CycleBlockLabel parts → LocalFieldLetter derivativeBudget,
        if IsTwistedIndexedDecoration h (cycleBlockRotation parts)
            derivativeBudget targetDegree letters then
          ∏ label, (letters label).tensorSign h
        else 0) =
      ∑ letters ∈ (Finset.univ.filter
          (IsTwistedIndexedDecoration h (cycleBlockRotation parts)
            derivativeBudget targetDegree)),
        ∏ label, (letters label).tensorSign h := by
      exact (Finset.sum_filter _ _).symm
    _ = ∑ decoration : FixedCycleBlockDecoration h parts
          derivativeBudget targetDegree,
        ∏ label, (decoration.1 label).tensorSign h := by
      exact Finset.sum_subtype _ (by simp) _

theorem cycleBlockDecorationCharacter_eq_budgetedCarrierCharacter
    (h : Hypercubic4) (derivativeBudget : ℕ)
    (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    cycleBlockDecorationCharacter h parts derivativeBudget targetDegree =
      fixedBudgetedCycleCarrierCharacter h derivativeBudget parts
        targetDegree := by
  classical
  rw [cycleBlockDecorationCharacter_eq_fixedSum]
  unfold fixedBudgetedCycleCarrierCharacter
  apply Fintype.sum_equiv
    (fixedCycleBlockDecorationEquivBudgetedCarrier h derivativeBudget parts
      targetDegree positiveParts)
  intro decoration
  have weightIdentity :=
    fixedBudgetedCarrierToCycleBlockDecoration_tensorSign h derivativeBudget
      parts targetDegree positiveParts
      (fixedCycleBlockDecorationToBudgetedCarrier h derivativeBudget parts
        targetDegree positiveParts decoration)
  rw [fixedBudgetedCarrierToCycleBlockDecoration_after_to] at weightIdentity
  exact weightIdentity

/-- The literal fixed-decoration character of the concrete disjoint-cycle
permutation is the recursive partition character. -/
theorem cycleBlockDecorationCharacter_eq_partitionDerivativeCharacter
    (h : Hypercubic4) (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    cycleBlockDecorationCharacter h parts targetDegree targetDegree =
      HypercubicDimension16CompressionCensus.partitionDerivativeCharacter
        h parts targetDegree := by
  rw [cycleBlockDecorationCharacter_eq_budgetedCarrierCharacter h
      targetDegree parts targetDegree positiveParts,
    fixedBudgetedCycleCarrierCharacter_eq_fixedCycleFamilyCharacter h
      targetDegree parts targetDegree positiveParts (le_refl _),
    fixedCycleFamilyCharacter_eq_partitionDerivativeCharacter h parts
      targetDegree positiveParts]

theorem cycleBlockDecorationCharacter_nil
    (h : Hypercubic4) (derivativeBudget targetDegree : ℕ) :
    cycleBlockDecorationCharacter h [] derivativeBudget targetDegree =
      if targetDegree = 0 then 1 else 0 := by
  classical
  by_cases targetZero : targetDegree = 0
  · subst targetDegree
    simp [cycleBlockDecorationCharacter, indexedDecorationCharacter,
      indexedDecorationWeight,
      IsTwistedIndexedDecoration, CycleBlockLabel, cycleBlockRotation]
  · have zeroTarget : ¬ 0 = targetDegree := fun equality =>
      targetZero equality.symm
    simp [cycleBlockDecorationCharacter, indexedDecorationCharacter,
      indexedDecorationWeight,
      IsTwistedIndexedDecoration, CycleBlockLabel, cycleBlockRotation,
      targetZero, zeroTarget]

end HypercubicDimension16CycleBlockDecoration
end YangMills
end QuantumTheory
end Mettapedia
