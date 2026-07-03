import Mettapedia.Computability.PNP.V13RealRungTwoBitJunta

/-!
# Regression canaries for PNP v13 real rung-two bit-junta observers
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

example (j m : Nat) :
    v13RealLinearBitJuntaEpsilon2 j m =
      (4 * (2 : Rat) ^ j) / ((2 : Rat) ^ m) :=
  rfl

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) :
    V13RealLinearBitJuntaBlocked observer A i₀ ↔
      ∀ w : F2Vec m,
        (∀ row : Fin m,
          row ∈ v13RealLinearBitJuntaRhsRows observer →
            A.toEquiv w row = 0) →
          w i₀ = 0 :=
  v13RealLinearBitJunta_blocked_iff_kernel observer A i₀

example {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j) :
    (v13RealLinearBitJuntaRhsRows observer).card ≤ j :=
  v13RealLinearBitJuntaRhsRows_card_le observer

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A ↔
      V13RealLinearRowsGenerateTarget A.val
        (v13RealLinearBitJuntaRhsBudgetedRowset observer).1 i₀ :=
  v13RealLinearNoTargetBitJunta_blockedMap_iff_rowsGenerateTarget
    i₀ observer A

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) :
    V13RealLinearParityObserverDeterminesTarget observer A i₀ ↔
      v13RealLinearParityObserverConstant observer A = 0 ∧
        V13RealLinearParityObserverRhsParityMatchesTarget
          observer A i₀ :=
  v13RealLinearParityObserver_determinesTarget_iff observer A i₀

example {m j : Nat}
    (hcount : V13RealLinearNoTargetBitJuntaBlockedCountingBound m j) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_blockedCounting hcount

example {m j : Nat}
    (hcount : V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m j) :
    V13RealLinearNoTargetBitJuntaBlockedCountingBound m j :=
  V13RealLinearNoTargetBitJuntaBlockedCountingBound_of_budgetedRowsetGeneration
    hcount

example {m j : Nat}
    (hcount : V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m j) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_budgetedRowsetGeneration hcount

example (m : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m 0 :=
  V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_zeroBudget m

example (m : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m 0 :=
  v13RealLinearNoTargetBitJuntaSuccessBound_zeroBudget m

example (m : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m 1 :=
  V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_oneBudget m

example (m : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m 1 :=
  v13RealLinearNoTargetBitJuntaSuccessBound_oneBudget m

example (m : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m 2 :=
  V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_twoBudget m

example (m : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m 2 :=
  v13RealLinearNoTargetBitJuntaSuccessBound_twoBudget m

example {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (coeff : V13RealLinearRowsTargetCoefficient A.val rows i₀) :
    2 ≤ (v13RealLinearRowCombinationSupport coeff.val).card :=
  v13RealLinearNoTargetRowsTargetCoefficient_support_card_two_le
    i₀ A coeff

example {m j : Nat} {i₀ : Fin m} {rows : V13RealLinearBudgetedRowset m j}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ coeff : V13RealLinearRowsTargetCoefficient A.val.val rows.1 i₀,
      2 ≤ (v13RealLinearRowCombinationSupport coeff.val).card :=
  v13RealLinearNoTargetBudgetedRowsetGeneratingMapSet_exists_twoSupport A

example {m : Nat} {rows : Finset (Fin m)} (A : V13F2LinearEquiv m)
    (i₀ : Fin m)
    (coeff : V13RealLinearRowsTargetCoefficient A rows i₀)
    (hsupport :
      (v13RealLinearRowCombinationSupport coeff.val).card = 2) :
    ∃ row₀ row₁ : {row : Fin m // row ∈ rows},
      row₀ ≠ row₁ ∧
        ∀ w : F2Vec m,
          A.toEquiv w row₀.val + A.toEquiv w row₁.val = w i₀ :=
  v13RealLinearRowsTargetCoefficient_twoSupport_exists_pair_sum_target
    A i₀ coeff hsupport

example {m : Nat} {i₀ : Fin m}
    {rows : V13RealLinearBudgetedRowset m 2}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ row₀ row₁ : {row : Fin m // row ∈ rows.1},
      row₀ ≠ row₁ ∧
        ∀ w : F2Vec m,
          A.val.val.toEquiv w row₀.val +
            A.val.val.toEquiv w row₁.val = w i₀ :=
  v13RealLinearNoTargetTwoBudgetGeneratingMapSet_exists_pair_sum_target A

example {m : Nat} (A : V13F2LinearEquiv m) (i₀ row₀ row₁ : Fin m)
    (hpair : ∀ w : F2Vec m,
      A.toEquiv w row₀ + A.toEquiv w row₁ = w i₀) :
    V13RealLinearRowFunctionalTargetCosetHit A
      ({row₀} : Finset (Fin m)) i₀ row₁ :=
  v13RealLinearRowFunctionalTargetCosetHit_of_pair_sum_target
    A i₀ row₀ row₁ hpair

example {m : Nat} {i₀ : Fin m}
    {rows : V13RealLinearBudgetedRowset m 2}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ row₀ row₁ : {row : Fin m // row ∈ rows.1},
      row₀ ≠ row₁ ∧ row₁.val ∉ ({row₀.val} : Finset (Fin m)) ∧
        V13RealLinearRowFunctionalTargetCosetHit A.val.val
          ({row₀.val} : Finset (Fin m)) i₀ row₁.val :=
  v13RealLinearNoTargetTwoBudgetGeneratingMapSet_exists_pair_cosetHit A

example {m : Nat} (row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁) :
    Fintype.card (V13RealLinearTwoRowZeroAt row₀ row₁) * 4 =
      2 ^ m :=
  v13RealLinearTwoRowZeroAt_card_mul_four row₀ row₁ hneq

example {m : Nat} (i₀ row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    4 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetFixedPairSumTargetMapSet_card_mul_two_pow_le_noTarget
    i₀ row₀ row₁ hneq

example {m : Nat} (i₀ : Fin m)
    (rows : V13RealLinearBudgetedRowset m 2) :
    Fintype.card
        (V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows) *
      2 ^ m ≤
    16 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetTwoBudgetPairSumWitnessSigma_card_mul_two_pow_le
    i₀ rows

example {m : Nat} (i₀ row₀ row₁ : Fin m)
    (hrow : row₁ ∉ ({row₀} : Finset (Fin m))) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    8 * Fintype.card (V13F2LinearEquiv m) :=
  v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_equiv
    i₀ row₀ row₁ hrow

end Mettapedia.Computability.PNP
