import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CycleFamilyCharacter

/-!
# Dependent fixed-family carrier over a positive cycle list

This module assembles the literal fixed family from each positive relabeling
cycle while preserving exact residual derivative degree.  Zero-length cycles
are explicitly uninhabited.  The resulting signed weight sum is proved equal
to the direct cycle-seed character for every positive list.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16FixedCycleFamilyCarrier

open V14HypercubicFDCensus
open HypercubicDimension16LocalLetterCharacter
open HypercubicDimension16CycleSeedCharacter
open HypercubicDimension16CycleFamilyCharacter

/-! ## Exact dependent carrier -/

/-- One literal fixed local-letter family per positive cycle, with exact
residual derivative bookkeeping. -/
def FixedCycleFamilyCarrier (h : Hypercubic4) : List ℕ → ℕ → Type
  | [], remainingDegree => PLift (remainingDegree = 0)
  | 0 :: _, _ => PEmpty
  | (cyclePredecessor + 1) :: rest, remainingDegree =>
      ULift
        (Sigma fun localDerivativeCount : Fin
          (remainingDegree / (cyclePredecessor + 1) + 1) =>
          FixedExactCycleFamily h cyclePredecessor
              localDerivativeCount.1 ×
            FixedCycleFamilyCarrier h rest
              (remainingDegree -
                (cyclePredecessor + 1) * localDerivativeCount.1))

@[reducible] noncomputable def fixedCycleFamilyCarrierFintypeDef
    (h : Hypercubic4) :
    (parts : List ℕ) → (remainingDegree : ℕ) →
      Fintype (FixedCycleFamilyCarrier h parts remainingDegree)
  | [], remainingDegree => by
      change Fintype (PLift (remainingDegree = 0))
      exact Fintype.ofFinite _
  | 0 :: _, _ => by
      change Fintype PEmpty
      exact inferInstance
  | (cyclePredecessor + 1) :: rest, remainingDegree => by
      change Fintype
        (ULift
          (Sigma fun localDerivativeCount : Fin
            (remainingDegree / (cyclePredecessor + 1) + 1) =>
            FixedExactCycleFamily h cyclePredecessor
                localDerivativeCount.1 ×
              FixedCycleFamilyCarrier h rest
                (remainingDegree -
                  (cyclePredecessor + 1) * localDerivativeCount.1)))
      letI (localDerivativeCount : Fin
          (remainingDegree / (cyclePredecessor + 1) + 1)) :
          Fintype (FixedCycleFamilyCarrier h rest
            (remainingDegree -
              (cyclePredecessor + 1) * localDerivativeCount.1)) :=
        fixedCycleFamilyCarrierFintypeDef h rest
          (remainingDegree -
            (cyclePredecessor + 1) * localDerivativeCount.1)
      letI (localDerivativeCount : Fin
          (remainingDegree / (cyclePredecessor + 1) + 1)) :
          Fintype (FixedExactCycleFamily h cyclePredecessor
            localDerivativeCount.1) :=
        Fintype.ofFinite _
      exact inferInstance

@[reducible] noncomputable instance fixedCycleFamilyCarrierFintype
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ) :
    Fintype (FixedCycleFamilyCarrier h parts remainingDegree) :=
  fixedCycleFamilyCarrierFintypeDef h parts remainingDegree

noncomputable instance fixedCycleFamilyCarrierDecidableEq
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ) :
    DecidableEq (FixedCycleFamilyCarrier h parts remainingDegree) :=
  Classical.decEq _

def FixedCycleFamilyCarrier.tensorSign (h : Hypercubic4) :
    (parts : List ℕ) → (remainingDegree : ℕ) →
      FixedCycleFamilyCarrier h parts remainingDegree → ℚ
  | [], _, _ => 1
  | 0 :: _, _, carrier => nomatch carrier
  | (cyclePredecessor + 1) :: rest, remainingDegree,
      ⟨⟨localDerivativeCount, family, tail⟩⟩ =>
      exactCycleFamilyTensorSign h family.1 *
        FixedCycleFamilyCarrier.tensorSign h rest
          (remainingDegree -
            (cyclePredecessor + 1) * localDerivativeCount.1) tail

/-- Direct signed weight sum on the complete fixed-family carrier. -/
def fixedCycleFamilyCharacter (h : Hypercubic4)
    (parts : List ℕ) (remainingDegree : ℕ) : ℚ :=
  ∑ carrier : FixedCycleFamilyCarrier h parts remainingDegree,
    carrier.tensorSign h parts remainingDegree

/-! ## Recursive factorization -/

theorem fixedCycleFamilyCharacter_nil (h : Hypercubic4)
    (remainingDegree : ℕ) :
    fixedCycleFamilyCharacter h [] remainingDegree =
      if remainingDegree = 0 then 1 else 0 := by
  classical
  by_cases zeroDegree : remainingDegree = 0
  · subst remainingDegree
    simp [fixedCycleFamilyCharacter, FixedCycleFamilyCarrier,
      FixedCycleFamilyCarrier.tensorSign]
  · haveI : IsEmpty (PLift (remainingDegree = 0)) :=
      ⟨fun witness => zeroDegree witness.down⟩
    simp [fixedCycleFamilyCharacter, FixedCycleFamilyCarrier, zeroDegree]

@[simp] theorem fixedCycleFamilyCharacter_zero_cons
    (h : Hypercubic4) (rest : List ℕ) (remainingDegree : ℕ) :
    fixedCycleFamilyCharacter h (0 :: rest) remainingDegree = 0 := by
  classical
  simp [fixedCycleFamilyCharacter, FixedCycleFamilyCarrier]

theorem fixedCycleFamilyCharacter_cons_succ
    (h : Hypercubic4) (cyclePredecessor : ℕ) (rest : List ℕ)
    (remainingDegree : ℕ) :
    fixedCycleFamilyCharacter h
        ((cyclePredecessor + 1) :: rest) remainingDegree =
      ∑ localDerivativeCount : Fin
          (remainingDegree / (cyclePredecessor + 1) + 1),
        exactCycleFamilyCharacter h cyclePredecessor
            localDerivativeCount.1 *
          fixedCycleFamilyCharacter h rest
            (remainingDegree -
              (cyclePredecessor + 1) * localDerivativeCount.1) := by
  classical
  unfold fixedCycleFamilyCharacter
  let decomposition :
      FixedCycleFamilyCarrier h
          ((cyclePredecessor + 1) :: rest) remainingDegree ≃
        (Sigma fun localDerivativeCount : Fin
          (remainingDegree / (cyclePredecessor + 1) + 1) =>
          FixedExactCycleFamily h cyclePredecessor
              localDerivativeCount.1 ×
            FixedCycleFamilyCarrier h rest
              (remainingDegree -
                (cyclePredecessor + 1) * localDerivativeCount.1)) :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (∑ carrier : FixedCycleFamilyCarrier h
          ((cyclePredecessor + 1) :: rest) remainingDegree,
        carrier.tensorSign h ((cyclePredecessor + 1) :: rest)
          remainingDegree) =
      ∑ entry :
          (Sigma fun localDerivativeCount : Fin
            (remainingDegree / (cyclePredecessor + 1) + 1) =>
            FixedExactCycleFamily h cyclePredecessor
                localDerivativeCount.1 ×
              FixedCycleFamilyCarrier h rest
                (remainingDegree -
                  (cyclePredecessor + 1) * localDerivativeCount.1)),
        exactCycleFamilyTensorSign h entry.2.1.1 *
          entry.2.2.tensorSign h rest
            (remainingDegree -
              (cyclePredecessor + 1) * entry.1.1) := by
      apply Fintype.sum_equiv decomposition
      rintro ⟨⟨localDerivativeCount, family, tail⟩⟩
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro localDerivativeCount _
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [← exactCycleFamilyCharacter_eq_fixedFamilySum]

/-! ## Exact comparison with the cycle-seed carrier -/

/-- On every list of positive cycle lengths, the literal fixed-family weight
sum is exactly the direct cycle-seed character. -/
theorem fixedCycleFamilyCharacter_eq_cycleSeedCharacter
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    fixedCycleFamilyCharacter h parts remainingDegree =
      cycleSeedCharacter h parts remainingDegree := by
  induction parts generalizing remainingDegree with
  | nil =>
      rw [fixedCycleFamilyCharacter_nil,
        cycleSeedCharacter_nil]
  | cons cycleLength rest inductionHypothesis =>
      have cyclePositive := positiveParts cycleLength (by simp)
      obtain ⟨cyclePredecessor, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt cyclePositive)
      rw [fixedCycleFamilyCharacter_cons_succ,
        cycleSeedCharacter_cons]
      apply Finset.sum_congr rfl
      intro localDerivativeCount _
      rw [exactCycleFamilyCharacter_eq_exactLocalLetterCharacter,
        inductionHypothesis]
      intro laterCycle laterMembership
      exact positiveParts laterCycle (by simp [laterMembership])

theorem fixedCycleFamilyCharacter_eq_partitionDerivativeCharacter
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    fixedCycleFamilyCharacter h parts remainingDegree =
      HypercubicDimension16CompressionCensus.partitionDerivativeCharacter
        h parts remainingDegree := by
  rw [fixedCycleFamilyCharacter_eq_cycleSeedCharacter
      h parts remainingDegree positiveParts,
    cycleSeedCharacter_eq_partitionDerivativeCharacter]

end HypercubicDimension16FixedCycleFamilyCarrier
end YangMills
end QuantumTheory
end Mettapedia
