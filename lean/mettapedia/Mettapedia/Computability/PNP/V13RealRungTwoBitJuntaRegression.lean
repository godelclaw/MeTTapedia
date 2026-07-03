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

example (m j : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m j :=
  V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_allBudget m j

example (m j : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j :=
  v13RealLinearNoTargetBitJuntaSuccessBound_allBudget m j

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
    (coeff : V13RealLinearRowsTargetCoefficient A rows i₀) :
    ∀ w : F2Vec m,
      (v13RealLinearRowCombinationSupport coeff.val).sum
          (fun row => A.toEquiv w row.val) =
        w i₀ :=
  v13RealLinearRowsTargetCoefficient_support_sum_target A i₀ coeff

example {m j : Nat} {i₀ : Fin m} {rows : V13RealLinearBudgetedRowset m j}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ support : Finset {row : Fin m // row ∈ rows.1},
      2 ≤ support.card ∧ support.card ≤ j ∧
        ∀ w : F2Vec m,
          support.sum (fun row => A.val.val.toEquiv w row.val) = w i₀ :=
  v13RealLinearNoTargetBudgetedRowsetGeneratingMapSet_exists_support_sum_target
    A

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

example {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    (support : Finset {row : Fin m // row ∈ rows})
    (hsupport : 2 ≤ support.card) :
    Fintype.card
        (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support) *
      2 ^ m ≤
    4 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetFixedSupportSumTargetMapSet_card_mul_two_pow_le_noTarget
    i₀ support hsupport

example {m : Nat} {rows : Finset (Fin m)} {row : Fin m}
    (hrow : row ∉ rows) (support : Finset {r : Fin m // r ∈ rows}) :
    (v13RealLinearFreshFullSupport rows row support).card =
      support.card + 1 :=
  v13RealLinearFreshFullSupport_card hrow support

example {m : Nat} {i₀ : Fin m} {rows : Finset (Fin m)} {row : Fin m}
    (A : V13RealLinearNoTargetRowsMap m i₀) (hrow : row ∉ rows)
    (hhit :
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row) :
    ∃ support : Finset {r : Fin m // r ∈ rows},
      0 < support.card ∧
        ∀ w : F2Vec m,
          (v13RealLinearFreshFullSupport rows row support).sum
              (fun r => A.val.toEquiv w r.1) =
            w i₀ :=
  v13RealLinearNoTargetRows_freshRowFunctionalTargetCosetHit_exists_support_sum
    A hrow hhit

example {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∉ rows) :
    Fintype.card
        (V13RealLinearNoTargetFreshRowCosetHitSupportSigma i₀ rows row) *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetFreshRowCosetHitSupportSigma_card_mul_two_pow_le
    i₀ rows row hrow

example {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∉ rows) :
    Fintype.card
        {A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetFreshRowCosetHitMapSet_card_mul_two_pow_le
    i₀ rows row hrow

example {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∈ rows) :
    Fintype.card
        {A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetExistingRowCosetHitMapSet_card_mul_two_pow_le
    i₀ rows row hrow

example {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        {A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetFixedRowsetCosetHitMapSet_card_mul_two_pow_le
    i₀ rows row

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t rows row) *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_mul_two_pow_le_rows
    i₀ observer t rows row

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t rows row) *
      2 ^ m ≤
    4 * 2 ^ (t : Nat) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_mul_two_pow_le_step
    i₀ observer t rows row

example {m : Nat} (i₀ : Fin m)
    (rows : V13RealLinearBudgetedRowset m 2) :
    Fintype.card
        (V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows) *
      2 ^ m ≤
    16 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetTwoBudgetPairSumWitnessSigma_card_mul_two_pow_le
    i₀ rows

example {m j : Nat} (i₀ : Fin m)
    (rows : V13RealLinearBudgetedRowset m j) :
    Fintype.card
        (V13RealLinearNoTargetSupportSumWitnessSigma i₀ rows) *
      2 ^ m ≤
    4 * 2 ^ j *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetSupportSumWitnessSigma_card_mul_two_pow_le i₀ rows

example {m : Nat} (i₀ row₀ row₁ : Fin m)
    (hrow : row₁ ∉ ({row₀} : Finset (Fin m))) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    8 * Fintype.card (V13F2LinearEquiv m) :=
  v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_equiv
    i₀ row₀ row₁ hrow

example {m : Nat} (i₀ row₀ row₁ : Fin m)
    (hrow : row₁ ∉ ({row₀} : Finset (Fin m))) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    4 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) :=
  v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_noTarget
    i₀ row₀ row₁ hrow

end Mettapedia.Computability.PNP
