import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LocalLetterCharacter

/-!
# Signed character of a list of relabeling-cycle seeds

For a list of positive cycle lengths and a prescribed total derivative
degree, this module constructs the literal dependent carrier of one exact
local field letter per cycle.  A cycle of length `r` carrying a local word of
length `k` consumes derivative degree `r * k` and is acted on by `h ^ r`.

The signed fixed-point sum of this carrier is proved to be the recursive
`partitionDerivativeCharacter`.  No field permutation, trace layout, or
conjugacy-class count is used at this stage.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CycleSeedCharacter

open V14HypercubicFDCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16LocalLetterCharacter

/-! ## The dependent carrier and its literal signed action -/

/-- Sequential cycle seeds with exact residual derivative bookkeeping.  The
base is inhabited exactly when no derivative degree remains. -/
def CycleSeedCarrier : List ℕ → ℕ → Type
  | [], remainingDegree => PLift (remainingDegree = 0)
  | cycleLength :: rest, remainingDegree =>
      ULift
        (Sigma fun localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1) =>
          ExactLocalFieldLetter localDerivativeCount.1 ×
            CycleSeedCarrier rest
              (remainingDegree - cycleLength * localDerivativeCount.1))

@[reducible] noncomputable def cycleSeedCarrierFintypeDef :
    (parts : List ℕ) → (remainingDegree : ℕ) →
      Fintype (CycleSeedCarrier parts remainingDegree)
  | [], remainingDegree => by
      change Fintype (PLift (remainingDegree = 0))
      exact Fintype.ofFinite _
  | cycleLength :: rest, remainingDegree => by
      change Fintype
        (ULift (Sigma fun localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1) =>
          ExactLocalFieldLetter localDerivativeCount.1 ×
            CycleSeedCarrier rest
              (remainingDegree - cycleLength * localDerivativeCount.1)))
      letI (localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1)) :
          Fintype (CycleSeedCarrier rest
            (remainingDegree - cycleLength * localDerivativeCount.1)) :=
        cycleSeedCarrierFintypeDef rest
          (remainingDegree - cycleLength * localDerivativeCount.1)
      exact inferInstance

@[reducible] noncomputable instance cycleSeedCarrierFintype
    (parts : List ℕ) (remainingDegree : ℕ) :
    Fintype (CycleSeedCarrier parts remainingDegree) :=
  cycleSeedCarrierFintypeDef parts remainingDegree

@[reducible] noncomputable def cycleSeedCarrierDecidableEqDef :
    (parts : List ℕ) → (remainingDegree : ℕ) →
      DecidableEq (CycleSeedCarrier parts remainingDegree)
  | [], remainingDegree => Classical.decEq _
  | cycleLength :: rest, remainingDegree => by
      change DecidableEq
        (ULift (Sigma fun localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1) =>
          ExactLocalFieldLetter localDerivativeCount.1 ×
            CycleSeedCarrier rest
              (remainingDegree - cycleLength * localDerivativeCount.1)))
      letI (localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1)) :
          DecidableEq (CycleSeedCarrier rest
            (remainingDegree - cycleLength * localDerivativeCount.1)) :=
        cycleSeedCarrierDecidableEqDef rest
          (remainingDegree - cycleLength * localDerivativeCount.1)
      exact inferInstance

@[reducible] noncomputable instance cycleSeedCarrierDecidableEq
    (parts : List ℕ) (remainingDegree : ℕ) :
    DecidableEq (CycleSeedCarrier parts remainingDegree) :=
  cycleSeedCarrierDecidableEqDef parts remainingDegree

def CycleSeedCarrier.hypercubicAct (h : Hypercubic4) :
    (parts : List ℕ) → (remainingDegree : ℕ) →
      CycleSeedCarrier parts remainingDegree →
        CycleSeedCarrier parts remainingDegree
  | [], _, seed => seed
  | cycleLength :: rest, remainingDegree,
      ⟨⟨localDerivativeCount, letter, tail⟩⟩ =>
      ⟨⟨localDerivativeCount,
        letter.hypercubicAct (h ^ cycleLength),
        CycleSeedCarrier.hypercubicAct h rest
          (remainingDegree - cycleLength * localDerivativeCount.1) tail⟩⟩

def CycleSeedCarrier.tensorSign (h : Hypercubic4) :
    (parts : List ℕ) → (remainingDegree : ℕ) →
      CycleSeedCarrier parts remainingDegree → ℚ
  | [], _, _ => 1
  | cycleLength :: rest, remainingDegree,
      ⟨⟨localDerivativeCount, letter, tail⟩⟩ =>
      letter.tensorSign (h ^ cycleLength) *
        CycleSeedCarrier.tensorSign h rest
          (remainingDegree - cycleLength * localDerivativeCount.1) tail

/-- Direct signed fixed-point sum on the complete cycle-seed carrier. -/
def cycleSeedCharacter (h : Hypercubic4)
    (parts : List ℕ) (remainingDegree : ℕ) : ℚ :=
  ∑ seed : CycleSeedCarrier parts remainingDegree,
    if seed.hypercubicAct h parts remainingDegree = seed then
      seed.tensorSign h parts remainingDegree
    else 0

/-! ## Generic product factorization -/

theorem signedFixedProductSum
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    [DecidableEq Left] [DecidableEq Right]
    (leftAct : Left → Left) (rightAct : Right → Right)
    (leftWeight : Left → ℚ) (rightWeight : Right → ℚ) :
    (∑ pair : Left × Right,
      if (leftAct pair.1, rightAct pair.2) = pair then
        leftWeight pair.1 * rightWeight pair.2
      else 0) =
      (∑ left : Left,
        if leftAct left = left then leftWeight left else 0) *
      (∑ right : Right,
        if rightAct right = right then rightWeight right else 0) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  simp_rw [show ∀ (left : Left) (right : Right),
      (if leftAct left = left ∧ rightAct right = right then
        leftWeight left * rightWeight right
      else 0) =
      (if leftAct left = left then leftWeight left else 0) *
        (if rightAct right = right then rightWeight right else 0) by
    intro left right
    by_cases hleft : leftAct left = left <;>
      by_cases hright : rightAct right = right <;>
      simp [hleft, hright]]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]

/-! ## Recursive character identity -/

private def cycleSeedCarrierConsDown
    (cycleLength : ℕ) (rest : List ℕ) (remainingDegree : ℕ) :
    CycleSeedCarrier (cycleLength :: rest) remainingDegree →
      (Sigma fun localDerivativeCount : Fin
        (remainingDegree / cycleLength + 1) =>
        ExactLocalFieldLetter localDerivativeCount.1 ×
          CycleSeedCarrier rest
            (remainingDegree - cycleLength * localDerivativeCount.1))
  | ⟨payload⟩ => payload

private theorem cycleSeedCarrier_cons_up_eq_iff
    (cycleLength : ℕ) (rest : List ℕ) (remainingDegree : ℕ)
    (localDerivativeCount : Fin
      (remainingDegree / cycleLength + 1))
    (left right : ExactLocalFieldLetter localDerivativeCount.1 ×
      CycleSeedCarrier rest
        (remainingDegree - cycleLength * localDerivativeCount.1)) :
    (show CycleSeedCarrier (cycleLength :: rest) remainingDegree from
      ULift.up ⟨localDerivativeCount, left⟩) =
        (show CycleSeedCarrier (cycleLength :: rest) remainingDegree from
          ULift.up ⟨localDerivativeCount, right⟩) ↔
      left = right := by
  constructor
  · intro fixed
    have payloadFixed := congrArg
      (cycleSeedCarrierConsDown cycleLength rest remainingDegree) fixed
    exact eq_of_heq (Sigma.mk.inj_iff.mp payloadFixed).2
  · intro fixed
    subst right
    rfl

theorem cycleSeedCharacter_cons
    (h : Hypercubic4) (cycleLength : ℕ) (rest : List ℕ)
    (remainingDegree : ℕ) :
    cycleSeedCharacter h (cycleLength :: rest) remainingDegree =
      ∑ localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1),
        exactLocalLetterCharacter (h ^ cycleLength)
            localDerivativeCount.1 *
          cycleSeedCharacter h rest
            (remainingDegree - cycleLength * localDerivativeCount.1) := by
  classical
  unfold cycleSeedCharacter
  let decomposition :
      CycleSeedCarrier (cycleLength :: rest) remainingDegree ≃
        (Sigma fun localDerivativeCount : Fin
          (remainingDegree / cycleLength + 1) =>
          ExactLocalFieldLetter localDerivativeCount.1 ×
            CycleSeedCarrier rest
              (remainingDegree - cycleLength * localDerivativeCount.1)) :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (∑ seed : CycleSeedCarrier (cycleLength :: rest) remainingDegree,
        if seed.hypercubicAct h (cycleLength :: rest) remainingDegree =
            seed then
          seed.tensorSign h (cycleLength :: rest) remainingDegree
        else 0) =
      ∑ entry :
          (Sigma fun localDerivativeCount : Fin
            (remainingDegree / cycleLength + 1) =>
            ExactLocalFieldLetter localDerivativeCount.1 ×
              CycleSeedCarrier rest
                (remainingDegree - cycleLength * localDerivativeCount.1)),
        if
              (⟨entry.1,
              (entry.2.1.hypercubicAct (h ^ cycleLength),
                entry.2.2.hypercubicAct h rest
                  (remainingDegree - cycleLength * entry.1.1))⟩ :
              (Sigma fun localDerivativeCount : Fin
                (remainingDegree / cycleLength + 1) =>
                ExactLocalFieldLetter localDerivativeCount.1 ×
                  CycleSeedCarrier rest
                    (remainingDegree - cycleLength *
                      localDerivativeCount.1))) = entry then
          entry.2.1.tensorSign (h ^ cycleLength) *
            entry.2.2.tensorSign h rest
              (remainingDegree - cycleLength * entry.1.1)
        else 0 := by
      apply Fintype.sum_equiv decomposition
      rintro ⟨⟨localDerivativeCount, letter, tail⟩⟩
      dsimp [decomposition, CycleSeedCarrier.hypercubicAct,
        CycleSeedCarrier.tensorSign]
      simp only [cycleSeedCarrier_cons_up_eq_iff, Sigma.mk.inj_iff,
        heq_eq_eq, true_and, Prod.mk.injEq]
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro localDerivativeCount _
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and,
          Prod.mk.injEq, exactLocalLetterCharacter, cycleSeedCharacter] using
        (signedFixedProductSum
          (ExactLocalFieldLetter.hypercubicAct (h ^ cycleLength))
          (CycleSeedCarrier.hypercubicAct h rest
            (remainingDegree - cycleLength * localDerivativeCount.1))
          (ExactLocalFieldLetter.tensorSign (h ^ cycleLength))
          (CycleSeedCarrier.tensorSign h rest
            (remainingDegree - cycleLength * localDerivativeCount.1)))

theorem cycleSeedCharacter_nil (h : Hypercubic4)
    (remainingDegree : ℕ) :
    cycleSeedCharacter h [] remainingDegree =
      if remainingDegree = 0 then 1 else 0 := by
  classical
  by_cases hzero : remainingDegree = 0
  · subst remainingDegree
    simp [cycleSeedCharacter, CycleSeedCarrier,
      CycleSeedCarrier.hypercubicAct, CycleSeedCarrier.tensorSign]
  · haveI : IsEmpty (PLift (remainingDegree = 0)) :=
      ⟨fun witness => hzero witness.down⟩
    simp [cycleSeedCharacter, CycleSeedCarrier, hzero]

/-- The literal cycle-seed character is exactly the existing recursive
partition derivative character. -/
theorem cycleSeedCharacter_eq_partitionDerivativeCharacter
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ) :
    cycleSeedCharacter h parts remainingDegree =
      partitionDerivativeCharacter h parts remainingDegree := by
  induction parts generalizing remainingDegree with
  | nil =>
      rw [cycleSeedCharacter_nil]
      rfl
  | cons cycleLength rest inductionHypothesis =>
      rw [cycleSeedCharacter_cons]
      simp only [partitionDerivativeCharacter]
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro localDerivativeCount membership
      simp only [Finset.mem_range] at membership
      simp only [dif_pos membership]
      rw [exactLocalLetterCharacter_eq_cycleLetterCharacter,
        inductionHypothesis]

end HypercubicDimension16CycleSeedCharacter
end YangMills
end QuantumTheory
end Mettapedia
