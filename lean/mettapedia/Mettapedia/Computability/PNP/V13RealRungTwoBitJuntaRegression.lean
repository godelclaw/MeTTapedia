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

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) :
    V13RealLinearParityObserverDeterminesTargetComplement observer A i₀ ↔
      v13RealLinearParityObserverConstant observer A = 1 ∧
        V13RealLinearParityObserverRhsParityMatchesTarget
          observer A i₀ :=
  v13RealLinearParityObserver_determinesTargetComplement_iff observer A i₀

example {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    Fintype.card (F2Vec m) =
      Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) +
        Fintype.card (V13RealLinearBitJuntaFixedIncorrect observer A i₀) :=
  v13RealLinearBitJuntaFixedWorld_card_eq_correct_add_incorrect
    observer A i₀

example {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearBitJuntaBlocked observer A i₀) :
    Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) * 2 =
      Fintype.card (F2Vec m) :=
  v13RealLinearBitJunta_fixed_correct_card_mul_two_eq_f2vec_card_of_not_blocked
    observer A i₀ hnot

example {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearBitJuntaBlocked observer A i₀) :
    v13RealLinearBitJuntaFixedSuccess observer A i₀ = (1 / 2 : Rat) :=
  v13RealLinearBitJunta_fixedSuccess_eq_half_of_not_blocked
    observer A i₀ hnot

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot : ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaFixedCorrect i₀ observer A) * 2 =
      Fintype.card (F2Vec m) :=
  v13RealLinearNoTargetBitJunta_fixed_correct_card_mul_two_eq_f2vec_card_of_not_blocked
    i₀ observer A hnot

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot : ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    v13RealLinearNoTargetBitJuntaFixedSuccess i₀ observer A =
      (1 / 2 : Rat) :=
  v13RealLinearNoTargetBitJunta_fixedSuccess_eq_half_of_not_blocked
    i₀ observer A hnot

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (x w : F2Vec m) :
    v13RealLinearParityObserverRhsParity observer A (f2AddVec x w) =
      v13RealLinearParityObserverRhsParity observer A x +
        v13RealLinearParityObserverRhsParity observer A w :=
  v13RealLinearParityObserver_rhsParity_add observer A x w

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) =
      Fintype.card
        (V13RealLinearBitJuntaFixedIncorrect observer.toBitJunta A i₀) :=
  v13RealLinearParityObserver_fixed_correct_card_eq_incorrect_card_of_not_rhsParityMatchesTarget
    observer A i₀ hnot

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) * 2 =
      Fintype.card (F2Vec m) :=
  v13RealLinearParityObserver_fixed_correct_card_mul_two_eq_f2vec_card_of_not_rhsParityMatchesTarget
    observer A i₀ hnot

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hdet : V13RealLinearParityObserverDeterminesTarget observer A i₀) :
    v13RealLinearParityObserverFixedSuccess observer A i₀ = 1 :=
  v13RealLinearParityObserver_fixedSuccess_eq_one_of_determinesTarget
    observer A i₀ hdet

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hcomp :
      V13RealLinearParityObserverDeterminesTargetComplement observer A i₀) :
    v13RealLinearParityObserverFixedSuccess observer A i₀ = 0 :=
  v13RealLinearParityObserver_fixedSuccess_eq_zero_of_determinesTargetComplement
    observer A i₀ hcomp

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀) :
    v13RealLinearParityObserverFixedSuccess observer A i₀ = (1 / 2 : Rat) :=
  v13RealLinearParityObserver_fixedSuccess_eq_half_of_not_rhsParityMatchesTarget
    observer A i₀ hnot

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (i₀ : Fin m) (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A.val i₀) :
    v13RealLinearNoTargetBitJuntaFixedSuccess i₀ observer.toBitJunta A =
      (1 / 2 : Rat) :=
  realLinearNoTargetParityObserver_fixedSuccess_eq_half_of_not_rhsParityMatchesTarget
    observer i₀ A hnot

example {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    (V13RealLinearParityObserverDeterminesTarget observer A i₀ ∧
        v13RealLinearParityObserverFixedSuccess observer A i₀ = 1) ∨
      (V13RealLinearParityObserverDeterminesTargetComplement observer A i₀ ∧
        v13RealLinearParityObserverFixedSuccess observer A i₀ = 0) ∨
      (¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀ ∧
        v13RealLinearParityObserverFixedSuccess observer A i₀ =
          (1 / 2 : Rat)) :=
  v13RealLinearParityObserver_fixedSuccess_trichotomy observer A i₀

example {m j : Nat}
    (hcount : V13RealLinearNoTargetBitJuntaBlockedCountingBound m j) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_blockedCounting hcount

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) * 2 ≤
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) +
        Fintype.card
          (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) :=
  v13RealLinearNoTargetBitJunta_correct_card_mul_two_le_world_card_add_blocked_card
    i₀ observer

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) *
      2 ^ m ≤
    4 * 2 ^ j *
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) :=
  realLinearNoTargetBitJuntaBlockedWorld_card_mul_two_pow_le_world
    i₀ observer

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

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    v13RealLinearNoTargetBitJuntaSuccess i₀ observer ≤
      (1 / 2 : Rat) + v13RealLinearBitJuntaEpsilon2 j m :=
  realLinearNoTargetBitJunta_success_le_half_add_epsilon2 i₀ observer

example {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hrows : rows.card ≤ 1) :
    ¬ V13RealLinearRowsGenerateTarget A.val rows i₀ :=
  v13RealLinearNoTargetRows_not_rowsGenerateTarget_of_rows_card_le_one
    i₀ A hrows

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

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) ≤
      ∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
              i₀ observer t rows row) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_le_sum_fixedPrefix
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_fixedPrefixPacking
    i₀ observer hpack

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t rows row) =
      ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
            i₀ observer t rows row transcript) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_eq_sum_transcripts
    i₀ observer t rows row

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound_iff_transcriptPacking
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcapacity :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound_of_activeFixedMapTranscriptCylinderCapacity
    i₀ observer hcapacity

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_fixedPrefixTranscriptPacking
    i₀ observer hpack

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_iff_fixedPrefixTranscriptPacking
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_fixedPrefixTranscriptPacking
    i₀ observer hpack

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcapacity :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_activeFixedMapTranscriptCylinderCapacity
    i₀ observer hcapacity

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcount :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_counting
    i₀ observer hcount

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_iff_counting
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (ht : (t : Nat) = 0) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) = 0 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_sum_eq_zero_of_zero_index
    i₀ observer t ht

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (ht : (t : Nat) = 0) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_zeroIndex
    i₀ observer t ht

example {m : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m 1) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_oneBudget
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
            i₀ observer t pref) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
    i₀ observer t

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t ≃
      (Σ rows : Finset (Fin m),
        Σ row : Fin m,
          Σ transcript : V13RealLinearRowsTranscriptSpace m rows,
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetEquivSigmaFixedPrefixTranscript
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
            Fintype.card
              (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
                i₀ observer t rows row transcript) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_fixedPrefixTranscript
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ activeIdx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
          i₀ observer t,
        2 ^ (m - activeIdx.1.rows.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_active_capacity
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixPacking
    i₀ observer hpack

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_iff_counting
    i₀ observer

example {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorToList
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput n) =
      v13RealLinearSequentialRowPrefixTranscriptOf observer publicInput n :=
  v13RealLinearSequentialPrefixTranscriptVectorOf_toList
    observer publicInput n

example {m n : Nat}
    (pref : V13RealLinearSequentialPrefixTranscriptVector m n) :
    (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤ n :=
  v13RealLinearSequentialPrefixTranscriptVectorRows_card_le pref

example {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorInit
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (n + 1)) =
      v13RealLinearSequentialPrefixTranscriptVectorOf observer
        publicInput n :=
  v13RealLinearSequentialPrefixTranscriptVectorOf_init
    observer publicInput n

example {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorLastRow
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (n + 1)) =
      observer.chooseRow
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n) :=
  v13RealLinearSequentialPrefixTranscriptVectorOf_lastRow
    observer publicInput n

example {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat)
    {entry : Fin m × V13RealLinearRowView m}
    (hentry :
      entry ∈
        v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n) :
    entry.2 = v13RealLinearRowView entry.1 publicInput :=
  v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
    observer publicInput n hentry

example {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (public₀ public₁ : V13RealLinearPublic m) (n : Nat)
    (hpref :
      v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n =
        v13RealLinearSequentialRowPrefixTranscriptOf observer public₁ n) :
    v13RealLinearRowsTranscript
        (v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
        public₀ =
      v13RealLinearRowsTranscript
        (v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
        public₁ :=
  v13RealLinearRowsTranscript_eq_of_sequentialPrefixTranscript_eq
    observer public₀ public₁ n hpref

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (transcript : V13RealLinearRowsTranscriptSpace m rows) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
        i₀ observer t rows row transcript ↪
      ({A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} ×
        V13RealLinearRowsUnreadAssignment m rows) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSetToMapTimesUnreadAssignment
    i₀ observer t rows row transcript

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (transcript : V13RealLinearRowsTranscriptSpace m rows) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
          i₀ observer t rows row transcript) *
      2 ^ m ≤
    4 *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_card_mul_two_pow_le_world
    i₀ observer t rows row transcript

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx ↪
      V13RealLinearRowsUnreadAssignment m idx.rows :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderToUnreadAssignment
    i₀ observer t idx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx) ≤
      2 ^ (m - idx.rows.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_card_le_capacity
    i₀ observer t idx

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsUnreadAssignment m activeIdx.1.rows ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t activeIdx.1 :=
  v13RealLinearRowsUnreadAssignmentToActiveNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m - activeIdx.1.rows.card) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t activeIdx.1) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_card
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t activeIdx.1) =
      2 ^ (m - activeIdx.1.rows.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_card_eq_capacity
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    activeIdx.1.rows.card ≤ (t : Nat) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_le_step
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    activeIdx.1.rows.Nonempty :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_nonempty
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    0 < activeIdx.1.rows.card :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_pos
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    0 < (t : Nat) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_step_pos
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsGenerateTarget activeIdx.1.A.val
      (insert activeIdx.1.row activeIdx.1.rows) i₀ :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rowsGenerateTarget
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    (insert activeIdx.1.row activeIdx.1.rows).card ≤ (t : Nat) + 1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_step_succ
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearBudgetedRowset m ((t : Nat) + 1) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedBudgetedRowset
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedBudgetedRowset
        i₀ observer t activeIdx) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedMap
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    (insert activeIdx.1.row activeIdx.1.rows).card ≤ q :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_budget
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearBudgetedRowset m q :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQMap
    i₀ observer t activeIdx

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
      i₀ observer t activeIdx.1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
    i₀ observer t activeIdx

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearSequentialPrefixTranscriptVector m ((t : Nat) + 1) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) =
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_rows_eq
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearSequentialPrefixTranscriptVectorInit
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx)) =
      activeIdx.1.rows :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_init_rows_eq
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    v13RealLinearSequentialPrefixTranscriptVectorLastRow
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) =
      activeIdx.1.row :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_lastRow_eq
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx₀ activeIdx₁ :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hA : activeIdx₀.1.A = activeIdx₁.1.A)
    (hpref :
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₀ =
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₁) :
    activeIdx₀ = activeIdx₁ :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex_eq_of_sameMap_generatedPrefix
    i₀ observer t activeIdx₀ activeIdx₁ hA hpref

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
        i₀ observer t A ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
        i₀ observer t A :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMapToGeneratedPrefixForMap
    i₀ observer t A

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
          i₀ observer t A) ≤
      2 ^ ((t : Nat) + 1) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap_card_le_rhsHistory
    i₀ observer t A

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsTranscriptSpace m
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedTranscript
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Type :=
  V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
    i₀ observer t activeIdx

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsUnreadAssignment m
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1 ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx :=
  v13RealLinearRowsUnreadAssignmentToActiveNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
          i₀ observer t activeIdx) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_capacity_le_card
    i₀ observer t activeIdx

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx ↪
      V13RealLinearRowsUnreadAssignment m
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToUnreadAssignment
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
          i₀ observer t activeIdx) =
      2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_card_eq_capacity
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
          i₀ observer t omega) ≤
      2 ^ ((t : Nat) + 1) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_card_le_rhsHistory
    i₀ observer t omega

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
          i₀ observer t omega) ≤
      1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_card_le_one
    i₀ observer t omega

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t activeIdx.1 :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∈ activeIdx.1.rows) :
    V13RealLinearRowsGenerateTarget activeIdx.1.A.val activeIdx.1.rows i₀ :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_existing_rowsGenerateTarget
    i₀ observer t activeIdx hrow

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∉ activeIdx.1.rows) :
    ¬ V13RealLinearRowsGenerateTarget activeIdx.1.A.val activeIdx.1.rows i₀ :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_fresh_not_rowsGenerateTarget
    i₀ observer t activeIdx hrow

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t)
    (cell :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx) :
    V13RealLinearRowTraceNewCapture idx.A.val i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
          (idx.A, cell.val))
        (t : Nat) ∨
      ∃ s : Fin (t : Nat),
        V13RealLinearRowTraceNewCapture idx.A.val i₀
          (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
            (idx.A, cell.val))
          s :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_newCapture_or_priorNewCapture
    i₀ observer t idx cell

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t)
    (cell :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx)
    (hrow : idx.row ∈ idx.rows) :
    ∃ s : Fin (t : Nat),
      V13RealLinearRowTraceNewCapture idx.A.val i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
          (idx.A, cell.val))
        s :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_existing_priorNewCapture
    i₀ observer t idx cell hrow

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∉ activeIdx.1.rows) :
    2 ≤ (insert activeIdx.1.row activeIdx.1.rows).card :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_fresh_insert_rows_card_two_le
    i₀ observer t activeIdx hrow

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∈ activeIdx.1.rows) :
    2 ≤ activeIdx.1.rows.card :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_existing_rows_card_two_le
    i₀ observer t activeIdx hrow

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ≤ (insert activeIdx.1.row activeIdx.1.rows).card :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_two_le
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ≤
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1.card :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset_card_two_le
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m - activeIdx.1.rows.card) ≤
      2 * 2 ^ (m - (insert activeIdx.1.row activeIdx.1.rows).card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_two_mul_insert_capacity
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m - activeIdx.1.rows.card) ≤
      2 *
        2 ^ (m -
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
            i₀ observer t activeIdx).1.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_two_mul_generatedQBudgetedRowset_capacity
    i₀ observer t activeIdx

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) ≤
      2 *
        ∑ activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
            i₀ observer t,
          2 ^ (m -
            (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
              i₀ observer t activeIdx).1.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_sum_capacity_le_two_mul_generatedQBudgetedRowset_capacity_sum
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t,
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx)) =
      ∑ activeIdx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
          i₀ observer t,
        2 ^ (m - activeIdx.1.rows.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_sum_card_eq_active_capacity
    i₀ observer t

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (Σ rows : Finset (Fin m),
      Σ row : Fin m,
        Σ transcript : V13RealLinearRowsTranscriptSpace m rows,
          V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
            i₀ observer t rows row transcript) ≃
      (Σ idx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
          m q i₀ observer t,
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptSigmaEquivFixedMapCylinderSigma
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript)) =
      ∑ idx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
          m q i₀ observer t,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
            i₀ observer t idx) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_fixedMapCylinder_sum_card
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript)) =
      ∑ activeIdx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
          i₀ observer t,
        2 ^ (m - activeIdx.1.rows.card) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_active_capacity
    i₀ observer t

noncomputable example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
        (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          pref) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSetToFixedPrefixWorldSet
    i₀ observer t pref

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) *
      2 ^ m ≤
    4 * 2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_rows
    i₀ observer t pref

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) *
      2 ^ m ≤
    4 * 2 ^ (t : Nat) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_step
    i₀ observer t pref

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref)) ≤
      ∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
              i₀ observer t rows row) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_sum_card_le_sum_fixedPrefix
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_fixedPrefixPacking
    i₀ observer hpack

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

example (n : Nat) :
    Fintype.card (V13RealLinearSequentialPrefixRhsHistory n) = 2 ^ n :=
  v13RealLinearSequentialPrefixRhsHistory_card n

example {m : Nat} {public₀ public₁ : V13RealLinearPublic m}
    {row : Fin m} (hA : public₀.A = public₁.A)
    (hrhs : public₀.b row = public₁.b row) :
    v13RealLinearRowView row public₀ =
      v13RealLinearRowView row public₁ :=
  v13RealLinearRowView_eq_of_A_eq_rhs_eq hA hrhs

example {m q : Nat}
    (observer : V13RealLinearSequentialRowObserver m q)
    {public₀ public₁ : V13RealLinearPublic m} (n : Nat)
    (hA : public₀.A = public₁.A)
    (hrhs :
      v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₀ n) =
        v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₁ n)) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer public₀ n =
      v13RealLinearSequentialPrefixTranscriptVectorOf observer public₁ n :=
  v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_A_eq_rhs
    observer n hA hrhs

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (cell :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx) :
    v13RealLinearSequentialPrefixTranscriptVectorRhs
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := cell.val, A := activeIdx.1.A.val } :
              V13RealLinearWorld m))
          ((t : Nat) + 1)) =
      v13RealLinearSequentialPrefixTranscriptVectorRhs
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_rhs_eq
    i₀ observer t activeIdx cell

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx₀ activeIdx₁ :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hA : activeIdx₀.1.A = activeIdx₁.1.A)
    (hrhs :
      v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx₀) =
        v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx₁)) :
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
        i₀ observer t activeIdx₀ =
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
        i₀ observer t activeIdx₁ :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_eq_of_sameMap_rhs
    i₀ observer t activeIdx₀ activeIdx₁ hA hrhs

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
          i₀ observer t A) ≤
      2 ^ ((t : Nat) + 1) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap_card_le_rhsHistory
    i₀ observer t A

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
          i₀ observer t) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence_card_le_worldSet
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card)) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) :=
  v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCell_capacity_sum_le_worldSet_card
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hprior :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge_of_noPrior
    i₀ observer hprior

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixWorldSet
          i₀ observer t pref)) =
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) :=
  v13RealLinearNoTargetSequentialPrefixWorldSet_sum_card_eq_world
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref) :
    v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∉
      v13RealLinearSequentialPrefixTranscriptVectorRows pref :=
  v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet_hitRow_not_mem
    i₀ observer t pref omega

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) *
      2 ^ m ≤
    (4 *
        2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) *
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixWorldSet
          i₀ observer t pref) :=
  v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_prefixWorldSet
    i₀ observer t pref

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitOrderedPrefixConditionedCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitOrderedPrefixConditionedCountingBound_unconditional
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceTrueFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet
            i₀ observer t pref) :=
  v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
    i₀ observer t

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitOrderedPrefixPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitOrderedPrefixPackingBound_unconditional
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitCountingBound_unconditional
    i₀ observer

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hconditioned :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_conditionedCounting
    i₀ observer hconditioned

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hconditioned :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixConditionedCounting
    i₀ observer hconditioned

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hconditioned :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_orderedPrefixConditionedCounting
    i₀ observer hconditioned

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hfresh :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_freshnessBridge
    i₀ observer hfresh

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hprior :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_noPriorBridge
    i₀ observer hprior

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hfresh :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_freshnessBridge
    i₀ observer hfresh

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hprior :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_noPriorBridge
    i₀ observer hprior

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hfresh :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_freshnessBridge
    i₀ observer hfresh

example {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hprior :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_noPriorBridge
    i₀ observer hprior

example {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearRowsGenerateTarget
      (v13RealLinearNoTargetRowShear i₀ hm)
      ({i₀, v13FinSpare i₀ hm} : Finset (Fin m)) i₀ :=
  v13RealLinearNoTargetRowShear_pairRowsGenerateTarget i₀ hm

example {m : Nat} (i₀ : Fin m) (hm : 4 < m) :
    ¬ V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
      i₀
      (v13RealLinearNoTargetRowShearGeneratedRereadObserver i₀
        (Nat.lt_trans (by norm_num : 1 < 4) hm)) :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_not_of_rowShear_generated_reread
    i₀ hm

#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_newCapture_or_priorNewCapture
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_existing_priorNewCapture
#print axioms v13RealLinearRowTraceCosetHit_get_not_mem_of_noPrior
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_not_mem_of_noPrior
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_cosetHit
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRowsGenerateTarget_of_nextRow_mem
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_priorCosetHit_of_nextRow_mem
#print axioms v13RealLinear_rowFunctionalTargetCosetHit_of_rowsGenerateTarget_of_mem
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSet_prefixRows_eq
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSet_nextRow_eq
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSetToOrderedPrefixHitOfNextRowMemOfPrefixRowsGenerateTarget
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSet_orderedPrefixHit_nonempty_of_nextRow_mem_of_prefixRowsGenerateTarget
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSet_rowsGenerateTarget_of_same_prefix
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSetToOrderedPrefixHitEmbeddingOfGeneratedRereadPrefix
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSet_card_le_orderedPrefixHitWorldSet_of_generated_reread_prefix
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge_not_of_generated_reread_prefix
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge_not_of_generated_reread_prefix
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge_of_noPrior
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_not_of_generated_reread_prefix_gap
#print axioms v13RealLinearNoTargetRowShear_pairRowsGenerateTarget
#print axioms v13RealLinearNoTargetRowShearGeneratedRereadObserver_prefixRows_two
#print axioms v13RealLinearNoTargetRowShearGeneratedRereadObserver_nextRow_two
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_not_of_rowShear_generated_reread
#print axioms v13RealLinearNoTargetSequentialPrefixWorldSet_sum_card_eq_world
#print axioms v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass_card_mul_two_pow_le_prefixMapClass
#print axioms v13RealLinearNoTargetSequentialPrefixHitMapClass_card_mul_two_pow_le_prefixMapClass
#print axioms v13RealLinearNoTargetSequentialPrefixMapClass_card_mul_unread_le_prefixWorldSet
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_le_hitMapClass_mul_unread
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_of_freshnessBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_of_noPriorBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_conditionedCounting
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixConditionedCounting
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_orderedPrefixConditionedCounting
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_freshnessBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_noPriorBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_freshnessBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_noPriorBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_freshnessBridge
#print axioms V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_noPriorBridge
#print axioms v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet_card_le_orderedPrefixWorldSet
#print axioms v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet_hitRow_not_mem
#print axioms v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_prefixWorldSet
#print axioms V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitOrderedPrefixConditionedCountingBound_unconditional
#print axioms v13RealLinearNoTargetSequentialTraceTrueFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
#print axioms V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitOrderedPrefixPackingBound_unconditional
#print axioms V13RealLinearNoTargetRowsSequentialTraceTrueFirstCosetHitCountingBound_unconditional
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_rows_eq
#print axioms v13RealLinearSequentialPrefixTranscriptVectorOf_init
#print axioms v13RealLinearSequentialPrefixTranscriptVectorOf_lastRow
#print axioms v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
#print axioms v13RealLinearRowsTranscript_eq_of_sequentialPrefixTranscript_eq
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_init_rows_eq
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_lastRow_eq
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex_eq_of_sameMap_generatedPrefix
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMapToGeneratedPrefixForMap
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap_card_le_rhsHistory
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_card_le_rhsHistory
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_card_le_one
#print axioms v13RealLinearSequentialPrefixRhsHistory_card
#print axioms v13RealLinearRowView_eq_of_A_eq_rhs_eq
#print axioms v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_A_eq_rhs
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_rhs_eq
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_eq_of_sameMap_rhs
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMapToRhsHistory
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap_card_le_rhsHistory
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderSigmaEquivWorldSet
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidenceToWorldSet
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence_card_le_worldSet
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCell_capacity_sum_le_worldSet_card
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_capacity_le_card
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_card_eq_capacity
#print axioms v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder

end Mettapedia.Computability.PNP
