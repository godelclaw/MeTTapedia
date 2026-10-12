import Mettapedia.GSLT.Dedukti.LeanMinusObservers
import Mettapedia.GSLT.Dedukti.LeanMinusRuleOrder

/-!
# Controls for the observer reading of the level translations

A positive and a negative example for each definition of
`LeanMinusLevelValues`, `LeanMinusCanonicity`, `LeanMinusPaperNormalForm`,
`LeanMinusObservers` and `LeanMinusRuleOrder`, and the controls that show which
hypotheses are used.

## Values and insertions

* `guardHolds_examples`, `sublevelEval_examples`, `setEval_examples`,
  `admissible_examples`.
* `leSub_unsound_unguarded`: the dominance test is not sound on the paper's
  code of a variable at `α = 0`; admissibility cannot be dropped from
  `leSub_sound`.  This is the mechanism of the lost distinction.
* `dropping_not_insertionSound`: an insertion that forgets the new sublevel is
  not sound.
* `addSubPaper_examples`: the paper's `Add` agrees with the corrected one where
  the rest of the set holds nothing dominated, and keeps a dominated element
  where it does.
* `normalSet_examples`, `paperSet_examples`, `unguardedSet_examples`: the three
  computed sets on the two witness pairs.  The paper's rules join `max 1 α`
  with `α` and separate the pair of the rule on `Add`; the corrected rules do
  the opposite; the empty guard alone joins both.
* `guardedPaperSet_examples`: the fourth computed set, the guard corrected
  alone.  It joins the pair of the rule on `Add` and separates another pair of
  equivalent levels, which the paper's rules join under the empty guard.
* `addTainted_examples`, `addFree_examples`, `bodyAddFreeTest_examples`.
* `transfer_needs_addFree`: from a term that mentions `Add`, the corrected
  theory reaches a term that the paper's theory does not reach.

## Canonical sets

* `strictComparison_examples`, `sublevelKey_examples`, `sortedGuard_examples`,
  `guardSorted_examples`, `guarded_examples`, `indicator_examples`,
  `setBound_examples`.
* `paperSet_not_canonical`: the set that the paper's rules compute for
  `max (succ α) (max 2 α)` is not canonical; it keeps a dominated sublevel.
  The sets of the corrected rules are canonical (`normalSet_canonical`,
  `unguardedSet_canonical`).
* `two_variable_examples`, `theorem2_two_variable_example`: the computed sets
  and Theorem 2 on levels in two variables, one equivalent pair that uses
  `imax` and one pair that is apart.

## Observers

* `report_examples`: the semantic report, the report of (a) and the report at
  the positive valuations on the witness pairs, by the fibres of the main
  module.
* One theorem for each observer, with a pair it identifies and a pair it
  separates: `semanticObserver_examples`, `paperObserver_examples`,
  `explicitObserver_examples`, `frozenObserver_examples`,
  `unguardedObserver_examples`, `guardedObserver_examples`,
  `positiveObserver_examples`.  The observer of (b) separates nothing
  (`polyObserver_examples`).
* `orderedCodeObserver_examples`, `orderedClass_examples`: with the rules tried
  in order, the paper's rules identify the levels `0` and `1`, and the
  corrected frozen rules keep `max 1 α` and `α` apart.
* `conversionClass_examples`, `termObserver_examples`, `positiveValuations_examples`,
  `levelSat_examples`, `equationSat_examples`, `levelsWhere_examples`.
* `variables_examples`, `variables_positive_examples`: the variables of a
  level; the pair that (a) identifies has one value at a valuation that is `0`
  away from its variables, and two values where its variable is `0`.
* `testTolerance_max_one_var_examples`: the weighted distance between
  `max 1 α` and `α` is `1` for one test at `α = 0` and `0` for one test at
  `α = 1`.

## Maps of theories

* `paperPairMap`: on the collection of `max 1 α` and `α` the paper's code is a
  map, since it identifies the two, and it is not hosting
  (`paperPairMap_not_hosting`).
* `paperClosedPairMap`: on the collection of the levels `0` and `1` the paper's
  code is a hosting map (`paperClosedPairMap_hosting`).  So the failure of (a)
  to host is a property of the collection, not of every use of the code.
* `polyMap_not_hosting`, `polyMap_singleton_hosting`: (b) on all levels is a
  map and is not hosting; on a collection of one level it is hosting.

## Typing

* `typingReport_examples`, `typedRewriting_examples`.
* `forgetTyping_empty_hosting`, `typing_invisible_in_pure_calculus`: in the
  calculus with beta alone, the inhabitants of every type in the empty context
  are hosted by the calculus as it runs, and every step out of a typed term is
  invisible to the typing observer.

## Rule order

* `checkAct_frozen_fallback_commutes`: on the frozen rules, at
  `v (frz 0) x`, selecting and instantiating `x` reach one term in both
  orders.
* `fires_examples`, `checkTheory_examples`.
* `frozenPair`, `frozenPair_commutes`: the instantiation and the fallback step
  on a frozen parameter are independent events, and their two routes are one
  trace.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus.ObserverControls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx subst)
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.Logic.HostingStyles (observer observer_indistinguishable observer_apart)
open Mettapedia.GSLT.Causality.EventConcurrency
open Mettapedia.GSLT.Dynamics.EffectTraceInterleaving (run)
open Mettapedia.Logic.Relation (Confluent IsNormal)
open Mettapedia.Logic.TheoryModel (SentenceWeighting testTolerance)

/-! ## Values of sublevels -/

/-- A guard holds where its variables are positive, and fails where one of
them is `0`. -/
theorem guardHolds_examples :
    guardHolds (fun _ => 1) [0, 3] = true ∧ guardHolds (fun index => index) [0, 3] = false := by
  decide

/-- `V {α} α 1` is `α + 1` where `α` is positive, and `0` where `α` is `0`. -/
theorem sublevelEval_examples :
    sublevelEval (fun _ => 2) (.var [0] 0 1) = 3 ∧ sublevelEval (fun _ => 0) (.var [0] 0 1) = 0 := by
  decide

/-- The value of a set is the maximum of the sublevels whose guards hold: `2`
for `{C ∅ 1, V {α} α 0}` at `α = 2`, and `0` for `{C {α} 5, V {α} α 3}` at
`α = 0`. -/
theorem setEval_examples :
    setEval (fun _ => 2) [.cst [] 1, .var [0] 0 0] = 2 ∧
      setEval (fun _ => 0) [.cst [0] 5, .var [0] 0 3] = 0 := by
  decide

/-- The corrected code of a variable is admissible where the variable is `0`;
the paper's code is not; and a constant `0` is admissible nowhere. -/
theorem admissible_examples :
    Admissible (fun _ => 0) (guardedLeaf 0) ∧ ¬ Admissible (fun _ => 0) (unguardedLeaf 0) ∧
      ¬ Admissible (fun _ => 1) (.cst [] 0) :=
  ⟨guardedLeaf_admissible _ 0,
    fun admissible => (unguardedLeaf_admissible_iff _ 0).mp admissible rfl,
    fun admissible => absurd (show 1 ≤ 0 from admissible) (by decide)⟩

/-- **The dominance test is not sound on the paper's code of a variable**:
`leS` puts `C ∅ 1` below `V ∅ α 0`, whose value at `α = 0` is smaller.  The
admissibility of the dominating sublevel cannot be dropped from
`leSub_sound`. -/
theorem leSub_unsound_unguarded :
    leSub (.cst [] 1) (unguardedLeaf 0) = true ∧
      ¬ sublevelEval (fun _ => 0) (.cst [] 1) ≤ sublevelEval (fun _ => 0) (unguardedLeaf 0) := by
  decide

/-- An insertion that forgets the new sublevel is not sound. -/
theorem dropping_not_insertionSound : ¬ InsertionSound (fun _ => 1) (fun _ set => set) := by
  intro sound
  have value := sound.value (sublevel := .cst [] 1) (set := []) (Nat.le_refl 1)
    (fun _ member => (by cases member))
  exact absurd value (by decide)

/-- The set of `imax`, with the corrected `Add`: nothing when the second set is
empty; and for `imax 1 α` the constant, guarded by `α`, is dominated by `α`. -/
theorem imaxSetWith_examples :
    imaxSetWith addSub [.cst [] 1] [] = [] ∧
      imaxSetWith addSub [.cst [] 1] [.var [0] 0 0] = [.var [0] 0 0] := by
  decide

/-- **The paper's `Add` against the corrected one**: they agree where the rest
of the set holds nothing dominated; where it does, the paper's rule keeps the
dominated `V ∅ α 0` beside `V ∅ α 1` and the corrected rule drops it. -/
theorem addSubPaper_examples :
    addSubPaper (.cst [] 2) [.cst [] 1] = addSub (.cst [] 2) [.cst [] 1] ∧
      addSubPaper (.var [] 0 1) [.cst [] 1, .var [] 0 0] = [.var [] 0 0, .var [] 0 1] ∧
      addSub (.var [] 0 1) [.cst [] 1, .var [] 0 0] = [.var [] 0 1] := by
  decide

/-- The nested insertion of the rule on `imax`, with the corrected `Add`, is
the existing one; with no guarding sublevel nothing is inserted. -/
theorem guardedSetWith_examples :
    guardedSetWith addSub [.cst [] 1] [.var [0] 0 0] [.var [0] 0 0] =
        guardedSet [.cst [] 1] [.var [0] 0 0] [.var [0] 0 0] ∧
      guardedSetWith addSub [.cst [] 1] [] [.var [0] 0 0] = [.var [0] 0 0] := by
  decide

/-- **The corrected rules**: the computed sets separate `max 1 α` from `α` and
join the pair of the rule on `Add`. -/
theorem normalSet_examples :
    normalSet maxOneVar ≠ normalSet alpha ∧ normalSet addPairLeft = normalSet addPairRight := by
  decide

/-- **The paper's own rules**: the computed sets join `max 1 α` with `α` and
separate the pair of the rule on `Add`.  The two defects, by computation. -/
theorem paperSet_examples :
    normalSetWith addSubPaper unguardedLeaf maxOneVar = normalSetWith addSubPaper unguardedLeaf alpha ∧
      normalSetWith addSubPaper unguardedLeaf addPairLeft ≠
        normalSetWith addSubPaper unguardedLeaf addPairRight := by
  decide

/-- **The empty guard alone**: with the rule on `Add` corrected, the computed
sets join both pairs, and they still separate the levels `0` and `1`. -/
theorem unguardedSet_examples :
    normalSetWith addSub unguardedLeaf maxOneVar = normalSetWith addSub unguardedLeaf alpha ∧
      normalSetWith addSub unguardedLeaf addPairLeft = normalSetWith addSub unguardedLeaf addPairRight ∧
      normalSetWith addSub unguardedLeaf .zero ≠ normalSetWith addSub unguardedLeaf (.succ .zero) := by
  decide

/-- **The guard corrected alone**: with the paper's `Add` and each variable in
its own guard, the computed sets join the pair of the rule on `Add` and
separate the equivalent levels `max 3 (max 1 (imax 2 α))` and `max 3 α`.  Under
the empty guard the paper's `Add` joins that second pair. -/
theorem guardedPaperSet_examples :
    normalSetWith addSubPaper guardedLeaf addPairLeft =
        normalSetWith addSubPaper guardedLeaf addPairRight ∧
      normalSetWith addSubPaper guardedLeaf guardPairLeft ≠
        normalSetWith addSubPaper guardedLeaf guardPairRight ∧
      normalSetWith addSubPaper unguardedLeaf guardPairLeft =
        normalSetWith addSubPaper unguardedLeaf guardPairRight := by
  decide

/-! ## Canonical sets -/

/-- The comparison of naturals is a strict order; a comparison that answers
"less" always is not. -/
theorem strictComparison_examples :
    StrictComparison cmpNat ∧ ¬ StrictComparison fun (_ _ : Nat) => Ordering.lt :=
  ⟨cmpNat_strict, fun strict => absurd (strict.irrefl 0) (by decide)⟩

/-- A constant comes before a variable, two constants on one guard are in the
order of their numbers, and the key of `C {α} 5` is its kind, its guard with a
terminator, and its number. -/
theorem sublevelKey_examples :
    cmpSub (.cst [0] 5) (.var [] 0 0) = .lt ∧ cmpSub (.cst [] 2) (.cst [] 1) = .gt ∧
      sublevelKey (.cst [0] 5) = [0, 1, 0, 5] := by
  decide

/-- A guard in increasing order is sorted; one out of order, or with a
repetition, is not. -/
theorem sortedGuard_examples : SortedGuard [0, 2] ∧ ¬ SortedGuard [2, 0] ∧ ¬ SortedGuard [1, 1] := by
  unfold SortedGuard
  decide

/-- The guard of the corrected code of a variable is sorted; a guard out of
order is not. -/
theorem guardSorted_examples : GuardSorted (guardedLeaf 0) ∧ ¬ GuardSorted (.cst [1, 0] 1) := by
  unfold GuardSorted SortedGuard
  decide

/-- The corrected code of a variable is a sublevel of the corrected code and
not of the paper's; the paper's code of a variable is the reverse. -/
theorem guarded_examples :
    Guarded (guardedLeaf 0) ∧ ¬ Guarded (unguardedLeaf 0) ∧ Unguarded (unguardedLeaf 0) ∧
      ¬ Unguarded (guardedLeaf 0) :=
  ⟨⟨List.pairwise_singleton _ _, List.mem_cons_self⟩, fun guarded => absurd guarded.2 List.not_mem_nil,
    rfl, fun unguarded => absurd (show [0] = [] from unguarded) (by decide)⟩

/-- The two valuations that test dominance: `1` on the support and `0` off it,
and the same with a chosen value at one variable. -/
theorem indicator_examples :
    indicator (fun index => index == 0) 0 = 1 ∧ indicator (fun index => index == 0) 1 = 0 ∧
      spike (fun _ => true) 2 7 2 = 7 ∧ spike (fun _ => true) 2 7 3 = 1 := by
  decide

/-- The bound of `{C ∅ 3, V ∅ α 4}` is `3 + 5`. -/
theorem setBound_examples :
    setBound [.cst [] 3, .var [] 0 4] = 8 ∧ sublevelBound (.var [] 0 4) = 5 := by
  decide

/-- **The set that the paper's rules compute for `max (succ α) (max 2 α)` is
not canonical**: it keeps `V ∅ α 0`, which is below `V ∅ α 1`. -/
theorem paperSet_not_canonical :
    ¬ Canonical Unguarded (normalSetWith addSubPaper unguardedLeaf addPairLeft) := fun canonical =>
  absurd (canonical.antichain (.var [] 0 0) (by decide) (.var [] 0 1) (by decide) (by decide))
    (by decide)

/-- **The computed sets on levels in two variables**: `max (imax α β) β` and
`imax α β` have one set, and `max α β` and `α` have two. -/
theorem two_variable_examples :
    normalSet (.max (.imax (.param 0) (.param 1)) (.param 1)) =
        normalSet (.imax (.param 0) (.param 1)) ∧
      normalSet (.max (.param 0) (.param 1)) ≠ normalSet (.param 0) := by
  decide

/-- **Theorem 2 on levels in two variables**: the codes of `max (imax α β) β`
and `imax α β` are convertible, and those of `max α β` and `α` are not. -/
theorem theorem2_two_variable_example :
    Conv leanTheoryExplicit (code (.max (.imax (.param 0) (.param 1)) (.param 1)))
        (code (.imax (.param 0) (.param 1))) ∧
      ¬ Conv leanTheoryExplicit (code (.max (.param 0) (.param 1))) (code (.param 0)) := by
  refine ⟨theorem3_all_levels fun valuation => ?_, fun convertible => ?_⟩
  · simp only [LeanLevel.eval]
    by_cases zero : valuation 1 = 0
    · simp [zero]
    · simp only [zero, if_false]
      omega
  · have atIdentity := theorem2_all_levels.mp convertible fun index => index
    simp [LeanLevel.eval] at atIdentity

/-! ## Reductions that reach the rule on `Add` -/

/-- `Add` is one of the constants on which the two level theories differ, or
that reach it; the comparison of naturals is not. -/
theorem addTainted_examples : "Add" ∈ addTainted ∧ "cmpN" ∉ addTainted := by
  decide

/-- A comparison keeps away from `Add`; a successor does not. -/
theorem addFree_examples : AddFree (ap "cmpN" [zeroN, zeroN]) ∧ ¬ AddFree (succ zero) := by
  decide

/-- A definition without `Add` passes the test; one that mentions it fails. -/
theorem bodyAddFreeTest_examples :
    bodyAddFreeTest (.defn "Fold" typ (ap "fold" [.con "S_code"])) = true ∧
      bodyAddFreeTest (.defn "X" typ (.con "Add")) = false := by
  decide

/-- **The hypothesis of the transfer is used**: from a term that mentions
`Add`, the corrected level theory reaches a term that the paper's level theory
does not reach.  The paper's rule keeps the dominated `V ∅ α 0`. -/
theorem transfer_needs_addFree :
    Reduces pureTheoryExplicit
        (ap "Add" [sublevelCode (.var [] 0 1), setCode [.cst [] 1, .var [] 0 0]])
        (setCode [.var [] 0 1]) ∧
      ¬ Reduces paperLevelTheory
        (ap "Add" [sublevelCode (.var [] 0 1), setCode [.cst [] 1, .var [] 0 0]])
        (setCode [.var [] 0 1]) := by
  refine ⟨Add_reduces (.var [] 0 1) [.cst [] 1, .var [] 0 0], fun reached => ?_⟩
  have kept : Reduces paperLevelTheory
      (ap "Add" [sublevelCode (.var [] 0 1), setCode [.cst [] 1, .var [] 0 0]])
      (setCode [.var [] 0 0, .var [] 0 1]) := paper_Add_reduces (.var [] 0 1) [.cst [] 1, .var [] 0 0]
  have headed : paperLevelTheory.Headed := paperLevelTheory_orthogonal.leftAlgebraic.headed
  have rigid : ∀ name ∈ setConstructors, ¬ paperLevelTheory.Defines name :=
    setConstructors_rigid (by decide +kernel)
  have normal (set : List Sublevel) : IsNormal (Step paperLevelTheory) (setCode set) :=
    normal_of_rigidConstants headed _ (setCode_flat set) fun name member =>
      rigid name (setCode_constants set name member)
  exact not_conv_of_normal paperLevelTheory_confluent (normal _) (normal _)
    (fun same => absurd (setCode_injective same) (by decide))
    (.trans _ _ _ (.symm _ _ reached.conv) kept.conv)

/-! ## The observers -/

/-- **The three reports on the witness pairs.**  The semantic report separates
`max 1 α` from `α` and joins the pair of the rule on `Add`; the report of (a)
does the reverse; the report at the positive valuations joins `max 1 α` with
`α` and separates the levels `0` and `1`. -/
theorem report_examples :
    semanticReport maxOneVar ≠ semanticReport alpha ∧
      semanticReport addPairLeft = semanticReport addPairRight ∧
      codeReport paperLevelTheory paperCode maxOneVar = codeReport paperLevelTheory paperCode alpha ∧
      codeReport paperLevelTheory paperCode addPairLeft ≠
        codeReport paperLevelTheory paperCode addPairRight ∧
      valuationReport positiveValuations maxOneVar = valuationReport positiveValuations alpha ∧
      valuationReport positiveValuations .zero ≠ valuationReport positiveValuations (.succ .zero) :=
  ⟨paperLostFiber.differentValue, paperAddedFiber.sameShadow, paperLostFiber.sameShadow,
    paperAddedFiber.differentValue, positiveLostFiber.sameShadow, fun same => by
      have atOne := valuationReport_eq_iff.mp same (fun _ => 1) fun _ => Nat.one_ne_zero
      simp [LeanLevel.eval] at atOne⟩

/-- The semantic observer identifies the pair of the rule on `Add` and
separates `max 1 α` from `α`. -/
theorem semanticObserver_examples :
    semanticObserver.Indistinguishable addPairLeft addPairRight ∧
      semanticObserver.Apart maxOneVar alpha :=
  ⟨semanticObserver_indistinguishable.mpr addPair_equiv,
    (observer_apart _ _ _).mpr fun same => maxOneVar_not_equiv (semanticReport_eq_iff.mp same)⟩

/-- What the checker of the theory with explicit level substitution tells
about terms: `zero` and its normal form are one class; `zero` and `succ zero`
are two. -/
theorem conversionClass_examples :
    conversionClass leanTheoryExplicit zero = conversionClass leanTheoryExplicit levelZero ∧
      conversionClass leanTheoryExplicit zero ≠ conversionClass leanTheoryExplicit (succ zero) :=
  ⟨conversionClass_eq_iff.mpr zero_reduces_explicit.conv,
    fun same => zero_succ_not_conv_explicit (conversionClass_eq_iff.mp same)⟩

/-- The checker's observer of the terms of that theory, on the same terms. -/
theorem termObserver_examples :
    (termObserver leanTheoryExplicit).Indistinguishable zero levelZero ∧
      (termObserver leanTheoryExplicit).Apart zero (succ zero) :=
  ⟨(observer_indistinguishable _ _ _).mpr conversionClass_examples.1,
    (observer_apart _ _ _).mpr conversionClass_examples.2⟩

/-- **(a)** identifies `max 1 α` with `α` and separates the pair of the rule on
`Add`: the reverse of the semantic observer on both pairs. -/
theorem paperObserver_examples :
    paperObserver.Indistinguishable maxOneVar alpha ∧ paperObserver.Apart addPairLeft addPairRight :=
  ⟨codeObserver_indistinguishable.mpr paperLevelTheory_max_one_var_reduces.conv,
    (observer_apart _ _ _).mpr fun same => paper_add_incomplete.2 (codeReport_eq_iff.mp same)⟩

/-- **(b)** identifies the levels `0` and `1`, and separates no two levels. -/
theorem polyObserver_examples (parameter : Nat → Term) :
    (polyObserver parameter).Indistinguishable .zero (.succ .zero) ∧
      ∀ first second : LeanLevel, ¬ (polyObserver parameter).Apart first second :=
  ⟨(poly_strictly_coarser_than_semantic parameter).2.2 _ _, fun first second =>
    (Tolerance.not_apart_iff_indistinguishable _ _ _).mpr
      ((poly_strictly_coarser_than_semantic parameter).2.2 first second)⟩

/-- **(c)** identifies the pair of the rule on `Add` and separates `max 1 α`
from `α`, as the semantic observer does. -/
theorem explicitObserver_examples :
    explicitObserver.Indistinguishable addPairLeft addPairRight ∧
      explicitObserver.Apart maxOneVar alpha :=
  ⟨codeObserver_indistinguishable.mpr explicit_joins_add_pair,
    (observer_apart _ _ _).mpr fun same => explicit_separates_max_one_var (codeReport_eq_iff.mp same)⟩

/-- **(d)** does the same. -/
theorem frozenObserver_examples :
    frozenObserver.Indistinguishable addPairLeft addPairRight ∧ frozenObserver.Apart maxOneVar alpha :=
  ⟨codeObserver_indistinguishable.mpr frozenCorrected_joins_add_pair,
    (observer_apart _ _ _).mpr fun same =>
      frozenCorrected_separates_max_one_var (codeReport_eq_iff.mp same)⟩

/-- The empty guard alone identifies `max 1 α` with `α` and separates the
levels `0` and `1`. -/
theorem unguardedObserver_examples :
    unguardedObserver.Indistinguishable maxOneVar alpha ∧ unguardedObserver.Apart .zero (.succ .zero) :=
  ⟨codeObserver_indistinguishable.mpr paperCode_max_one_var_conv_explicit,
    (observer_apart _ _ _).mpr fun same =>
      unguardedSet_examples.2.2 (conv_paperCode_explicit_iff.mp (codeReport_eq_iff.mp same))⟩

/-- The guard corrected alone identifies the pair of the rule on `Add` and
separates `max 1 α` from `α`, as the semantic observer does; it separates the
equivalent levels `max 3 (max 1 (imax 2 α))` and `max 3 α`. -/
theorem guardedObserver_examples :
    guardedObserver.Indistinguishable addPairLeft addPairRight ∧
      guardedObserver.Apart maxOneVar alpha ∧ guardedObserver.Apart guardPairLeft guardPairRight :=
  ⟨codeObserver_indistinguishable.mpr
      (conv_code_paperLevelTheory_iff.mpr guardedPaperSet_examples.1),
    (observer_apart _ _ _).mpr fun same =>
      maxOneVar_not_equiv (equiv_of_conv_code_paperLevelTheory (codeReport_eq_iff.mp same)),
    (observer_apart _ _ _).mpr guardedAddedFiber.differentValue⟩

/-- **The rules tried in order**: for the paper's rules every translation
identifies the levels `0` and `1`; for the corrected frozen rules, which do
not overlap, the frozen-parameter code keeps `max 1 α` and `α` apart. -/
theorem orderedCodeObserver_examples (translate : LeanLevel → Term) :
    (orderedCodeObserver leanSig leanRules translate).Indistinguishable .zero (.succ .zero) ∧
      (orderedCodeObserver frozenSig frozenRulesCorrected (paperLevel frzVar)).Apart
        maxOneVar alpha := by
  refine ⟨(observer_indistinguishable _ _ _).mpr
    (orderedClass_eq_iff.mpr (ordered_conv_collapses _ _)), ?_⟩
  rw [orderedCodeObserver_eq_of_orthogonal (signature := frozenSig) (rules := frozenRulesCorrected)
    frozenTheoryCorrected_orthogonal]
  exact frozenObserver_examples.2

/-- The classes of the two checkers on terms: one class for `zero` and
`succ zero` under the paper's rules, two classes for the frozen codes of
`max 1 α` and `α` under the corrected frozen rules. -/
theorem orderedClass_examples :
    orderedClass leanSig leanRules zero = orderedClass leanSig leanRules (succ zero) ∧
      orderedClass frozenSig frozenRulesCorrected (paperLevel frzVar maxOneVar) ≠
        orderedClass frozenSig frozenRulesCorrected (paperLevel frzVar alpha) :=
  ⟨orderedClass_eq_iff.mpr (ordered_conv_collapses _ _),
    (observer_apart _ _ _).mp (orderedCodeObserver_examples (paperLevel frzVar)).2⟩

/-- A valuation that is positive everywhere, and one that is not. -/
theorem positiveValuations_examples :
    (fun _ => 1 : Nat → Nat) ∈ positiveValuations ∧ (fun _ => 0 : Nat → Nat) ∉ positiveValuations :=
  ⟨fun _ => Nat.one_ne_zero, fun positive => positive 0 rfl⟩

/-- The observer of the positive valuations identifies `max 1 α` with `α` and
separates the levels `0` and `1`. -/
theorem positiveObserver_examples :
    (valuationObserver positiveValuations).Indistinguishable maxOneVar alpha ∧
      (valuationObserver positiveValuations).Apart .zero (.succ .zero) := by
  refine ⟨positive_indistinguishable_max_one_var, (observer_apart _ _ _).mpr fun same => ?_⟩
  have atOne := valuationReport_eq_iff.mp same (fun _ => 1) positiveValuations_examples.1
  simp [LeanLevel.eval] at atOne

/-- The only variable of `max 1 α` is `α`; a closed level has none. -/
theorem variables_examples :
    maxOneVar.variables = [0] ∧ (natLevel 2).variables = [] ∧ 1 ∉ maxOneVar.variables := by
  decide

/-- **What (a) loses is bounded by the variables of the two levels, and the
bound is used**: `max 1 α` and `α` have one value at the valuation that is `1`
at `α` and `0` at every other variable, which is not positive everywhere; and
they have two values where `α` is `0`. -/
theorem variables_positive_examples :
    maxOneVar.eval (fun index => if index = 0 then 1 else 0) =
        alpha.eval (fun index => if index = 0 then 1 else 0) ∧
      (fun index => if index = 0 then 1 else 0 : Nat → Nat) ∉ positiveValuations ∧
      maxOneVar.eval (fun _ => 0) ≠ alpha.eval (fun _ => 0) :=
  ⟨eval_eq_of_conv_paperCode_on_variables paperLevelTheory_max_one_var_reduces.conv (by decide),
    fun positive => positive 1 rfl, by decide⟩

/-- A value test that `α` satisfies, and one that it does not. -/
theorem levelSat_examples : levelSat alpha (fun _ => 3, 3) ∧ ¬ levelSat alpha (fun _ => 3, 4) := by
  simp [levelSat, alpha, LeanLevel.eval]

open Classical in
/-- **The weighted distance between `max 1 α` and `α`, on two weightings**: one
test of weight `1` at `α = 0` that asks for the value `0` puts the two levels
at distance `1`; one test at `α = 1` puts them at distance `0`. -/
theorem testTolerance_max_one_var_examples :
    (testTolerance levelSat (ν := ⟨{(fun _ => 0, 0)}, fun _ => 1, fun _ _ => one_pos⟩)
        (by simp [SentenceWeighting.mass])).distance maxOneVar alpha = 1 ∧
      (testTolerance levelSat (ν := ⟨{(fun _ => 1, 1)}, fun _ => 1, fun _ _ => one_pos⟩)
        (by simp [SentenceWeighting.mass])).distance maxOneVar alpha = 0 := by
  constructor
  · rw [testTolerance_distance_max_one_var]
    simp [SentenceWeighting.mass, Finset.filter_singleton]
  · rw [testTolerance_distance_max_one_var]
    simp [SentenceWeighting.mass, Finset.filter_singleton]

/-- The equation `max 1 α = α` holds where `α` is `1` and fails where `α` is
`0`. -/
theorem equationSat_examples :
    equationSat (fun _ => 1) (maxOneVar, alpha) ∧ ¬ equationSat (fun _ => 0) (maxOneVar, alpha) :=
  ⟨(maxOneVar_eval_eq_iff _).mpr Nat.one_ne_zero, fun same => (maxOneVar_eval_eq_iff _).mp same rfl⟩

/-! ## The translations as maps of theories -/

/-- The theory of all levels equates the pair of the rule on `Add`, keeps
`max 1 α` and `α` apart, and has no reduction. -/
theorem levelsWhere_examples :
    (levelsWhere fun _ => True).equations.r ⟨addPairLeft, trivial⟩ ⟨addPairRight, trivial⟩ ∧
      ¬ (levelsWhere fun _ => True).equations.r ⟨maxOneVar, trivial⟩ ⟨alpha, trivial⟩ ∧
      ∀ first second : (levelsWhere fun _ => True).Term,
        ¬ (levelsWhere fun _ => True).rewrites first second :=
  ⟨addPair_equiv, maxOneVar_not_equiv, fun _ _ step => step⟩

/-- **On the collection of `max 1 α` and `α`, the paper's code is a map**: it
identifies the two levels, which are apart, so it respects every equivalence
of the collection. -/
def paperPairMap :
    ContextMap (levelsWhere fun level => level = maxOneVar ∨ level = alpha).termsAlone
      (conversionTheory paperLevelTheory) :=
  translationMap paperLevelTheory _ paperCode fun first second keepFirst keepSecond _ => by
    rcases keepFirst with rfl | rfl <;> rcases keepSecond with rfl | rfl
    · exact .refl _
    · exact paperLevelTheory_max_one_var_reduces.conv
    · exact .symm _ _ paperLevelTheory_max_one_var_reduces.conv
    · exact .refl _

/-- **That map is not hosting.** -/
theorem paperPairMap_not_hosting : ¬ paperPairMap.Hosting :=
  paperCode_not_hosting (Or.inl rfl) (Or.inr rfl) paperPairMap fun _ => rfl

/-- On the collection of the levels `0` and `1`, the paper's code is a map. -/
def paperClosedPairMap :
    ContextMap (levelsWhere fun level => level = .zero ∨ level = .succ .zero).termsAlone
      (conversionTheory paperLevelTheory) :=
  translationMap paperLevelTheory _ paperCode fun first second keepFirst keepSecond equivalent => by
    rcases keepFirst with rfl | rfl <;> rcases keepSecond with rfl | rfl
    · exact .refl _
    · have atZero := equivalent fun _ => 0
      simp [LeanLevel.eval] at atZero
    · have atZero := equivalent fun _ => 0
      simp [LeanLevel.eval] at atZero
    · exact .refl _

/-- **On the levels `0` and `1` the paper's code is a hosting map**: its
normal forms keep the two apart. -/
theorem paperClosedPairMap_hosting : paperClosedPairMap.Hosting := by
  refine (translationMap_hosting_iff _ _ _ _).mpr fun first second keepFirst keepSecond convertible => ?_
  have same := conv_paperCode_iff.mp convertible
  rcases keepFirst with rfl | rfl <;> rcases keepSecond with rfl | rfl
  · exact fun _ => rfl
  · exact absurd same (by decide)
  · exact absurd same (by decide)
  · exact fun _ => rfl

/-- **(b) on all levels is a map and is not hosting.** -/
theorem polyMap_not_hosting (translate : LeanLevel → Term) :
    ¬ (polyMap (fun _ => True) translate).Hosting :=
  poly_not_hosting _ (first := .zero) (second := .succ .zero) trivial trivial fun equivalent => by
    have atZero := equivalent fun _ => 0
    simp [LeanLevel.eval] at atZero

/-- **(b) is hosting on a collection of one level**: nothing is apart there. -/
theorem polyMap_singleton_hosting (translate : LeanLevel → Term) :
    (polyMap (fun level => level = .zero) translate).Hosting :=
  (polyMap_hosting_iff _ _).mpr fun _ _ keepFirst keepSecond => by
    rw [keepFirst, keepSecond]
    exact fun _ => rfl

/-! ## Typing -/

/-- The typing observer of `ε |0| (Q x)` reports that `PUnit.rec Q h x` has the
type, and that `h` has not. -/
theorem typingReport_examples :
    typingReport leanTheoryExplicit punitContext punitRedexType punitRedex ∧
      ¬ typingReport leanTheoryExplicit punitContext punitRedexType (.var 1) :=
  ⟨punitRedex_typed, punitMinor_not_typed⟩

/-- The theory of the inhabitants of `ε |0| (Q x)` has the term
`PUnit.rec Q h x`, and has not its reduct `h`. -/
theorem typedRewriting_examples :
    (∃ source : (typedRewriting leanTheoryExplicit punitContext punitRedexType).Term,
        source.1 = punitRedex) ∧
      ¬ ∃ target : (typedRewriting leanTheoryExplicit punitContext punitRedexType).Term,
        target.1 = .var 1 :=
  ⟨⟨⟨punitRedex, punitRedex_typed⟩, rfl⟩, fun inhabitant => by
    obtain ⟨target, same⟩ := inhabitant
    exact punitMinor_not_typed (same ▸ target.2)⟩

/-- **In the calculus with beta alone, the inhabitants of every type in the
empty context are hosted by the calculus as it runs.** -/
theorem forgetTyping_empty_hosting (type : Term) : (forgetTyping Theory.empty [] type).Hosting :=
  (forgetTyping_hosting_iff _ _ _).mpr fun _ _ typed step =>
    typePreservation confluent_empty Theory.empty_headed Theory.empty_closedBodies
      (fun _ _ declared => by cases declared) (fun _ _ declared => by cases declared)
      (fun _ _ _ defined _ => by cases defined) (fun _ _ _ _ member => member.elim) .nil typed step

/-- **In the calculus with beta alone, every step out of a term typed in the
empty context is invisible to the typing observer.** -/
theorem typing_invisible_in_pure_calculus {type source target : Term}
    (typed : LambdaPiModulo Theory.empty [] source type) (step : Step Theory.empty source target) :
    (observer (typingReport Theory.empty [] type)).Indistinguishable source target :=
  (typing_indistinguishable_iff typed).mpr
    ((forgetTyping_hosting_iff _ _ _).mp (forgetTyping_empty_hosting type) _ _ typed step)

/-! ## Rule order -/

/-- **On the frozen rules, at `v (frz 0) x`, selecting and instantiating `x`
reach one term in both orders.** -/
theorem checkAct_frozen_fallback_commutes :
    run (checkAct frozenSig frozenRules 0 zeroN) (some (ap "v" [frzVar 0, .var 0]))
        [.select, .instantiate] = some (levelVariable zeroN) ∧
      run (checkAct frozenSig frozenRules 0 zeroN) (some (ap "v" [frzVar 0, .var 0]))
        [.instantiate, .select] = some (levelVariable zeroN) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- For the paper's rules the fallback fires at `v x 0`, and does not fire at
its instance `v (inst zero) 0`. -/
theorem fires_examples :
    Fires leanSig leanRules 0 (instOf zero) .select (ap "v" [.var 0, zeroN]) (levelVariable zeroN) ∧
      ¬ Fires leanSig leanRules 0 (instOf zero) .select (ap "v" [instOf zero, zeroN])
        (levelVariable zeroN) :=
  ⟨.select ordered_not_substitution_stable.1, fun fires => ordered_not_after_instantiation fires.ordered⟩

/-- The theory of the two events on the paper's rules has the fallback step at
`v x 0`, and has no step from `v (inst zero) 0` to the code of a variable. -/
theorem checkTheory_examples :
    (checkTheory leanSig leanRules 0 (instOf zero)).rewrites (ap "v" [.var 0, zeroN])
        (levelVariable zeroN) ∧
      ¬ (checkTheory leanSig leanRules 0 (instOf zero)).rewrites (ap "v" [instOf zero, zeroN])
        (levelVariable zeroN) := by
  refine ⟨?_, fun step => ?_⟩
  · exact show ∃ event, Fires leanSig leanRules 0 (instOf zero) event _ _ from
      ⟨.select, .select ordered_not_substitution_stable.1⟩
  · obtain ⟨event, fires⟩ := step
    cases event with
    | instantiate => exact absurd fires.substituted (by decide +kernel)
    | select => exact ordered_not_after_instantiation fires.ordered

/-- The fallback on a frozen parameter, as an ordered step: `v (frz 0) x`
steps to the code of the variable `x`. -/
theorem frozen_fallback_ordered :
    OrderedStep frozenSig frozenRules (ap "v" [frzVar 0, .var 0]) (levelVariable (.var 0)) :=
  (orderedStep_iff_of_orthogonal (signature := frozenSig) (rules := frozenRules)
    frozenTheory_orthogonal).mpr
    (stepOnce_sound frozenRules_linear (fun _ member => member) (by decide +kernel))

/-- **On the frozen rules, the instantiation of `x` and the fallback step at
`v (frz 0) x` are independent events.** -/
def frozenPair :
    (orthogonalConcurrency (signature := frozenSig) (rules := frozenRules) frozenTheory_orthogonal 0
      zeroN).Pair (ap "v" [frzVar 0, .var 0]) where
  first := instantiateAt frozenSig frozenRules 0 zeroN _
  second := selectAt 0 zeroN frozen_fallback_ordered
  independent := by
    change CheckEvent.instantiate ≠ CheckEvent.select
    decide

/-- **Their two routes are one trace**, and both end at the code of the
variable `0`. -/
theorem frozenPair_commutes :
    Trace.mk (T := (orthogonalConcurrency (signature := frozenSig) (rules := frozenRules)
        frozenTheory_orthogonal 0 zeroN).tiles) (frozenPair.route _) =
        Trace.mk (frozenPair.swapped _) ∧
      ((orthogonalConcurrency (signature := frozenSig) (rules := frozenRules) frozenTheory_orthogonal 0
        zeroN).residual frozenPair.independent).target = levelVariable zeroN :=
  ⟨Trace.mk_sound (.tile (T := (orthogonalConcurrency (signature := frozenSig) (rules := frozenRules)
      frozenTheory_orthogonal 0 zeroN).tiles) frozenPair), rfl⟩

#print axioms leSub_unsound_unguarded
#print axioms paperSet_not_canonical
#print axioms two_variable_examples
#print axioms theorem2_two_variable_example
#print axioms transfer_needs_addFree
#print axioms paperSet_examples
#print axioms guardedPaperSet_examples
#print axioms paperObserver_examples
#print axioms guardedObserver_examples
#print axioms orderedCodeObserver_examples
#print axioms explicitObserver_examples
#print axioms paperPairMap_not_hosting
#print axioms paperClosedPairMap_hosting
#print axioms report_examples
#print axioms typedRewriting_examples
#print axioms checkTheory_examples
#print axioms variables_positive_examples
#print axioms testTolerance_max_one_var_examples
#print axioms polyMap_not_hosting
#print axioms polyMap_singleton_hosting
#print axioms forgetTyping_empty_hosting
#print axioms typing_invisible_in_pure_calculus
#print axioms checkAct_frozen_fallback_commutes
#print axioms frozenPair_commutes

end Mettapedia.GSLT.Dedukti.LeanMinus.ObserverControls
