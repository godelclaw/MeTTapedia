import Mettapedia.Logic.Prolog.RuntimeControlRegression
import Mettapedia.Logic.Prolog.SourceRuntimeRegression
import Mettapedia.Logic.Prolog.ReaderDCGRegression

/-!
Executable side of the shared-runtime control differential.  The fixtures use
the canonical `Logic.Prolog.RuntimeControl` entrypoint; this driver only renders
their ordered answers for comparison with pinned SWI-Prolog.
-/

open Mettapedia.Logic.LP.RuntimeQueryRegression
open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.RuntimeControlRegression

set_option maxRecDepth 100000

def renderConstant : QConst -> String
  | .a => "a"
  | .b => "b"
  | .c => "c"

def renderAnswers (label : String) :
    Option (List QConst × Nat × Nat) -> IO Unit
  | some (answers, 0, 0) =>
      IO.println s!"{label}={String.intercalate "," (answers.map renderConstant)}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderStringAnswers (label : String) :
    Option (List String × Nat × Nat) -> IO Unit
  | some (answers, 0, 0) =>
      IO.println s!"{label}={String.intercalate "," answers}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderCount (label : String) : Option (Nat × Nat × Nat) -> IO Unit
  | some (count, 0, 0) => IO.println s!"{label}={count}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderIntegerAnswers (label : String) :
    Option (List Int × Nat × Nat) -> IO Unit
  | some (answers, 0, 0) =>
      IO.println s!"{label}={String.intercalate "," (answers.map toString)}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderRaisedAtom (label : String) :
    Option (String × Nat × Nat) -> IO Unit
  | some (name, 0, 0) => IO.println s!"{label}=raised({name})"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not raise"

def renderAtomBag (bag : List String) : String :=
  s!"[{String.intercalate "," bag}]"

def renderAtomBags (label : String) :
    Option (List (List String) × Nat × Nat) → IO Unit
  | some (bags, 0, 0) =>
      IO.println s!"{label}={String.intercalate ";" (bags.map renderAtomBag)}"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def renderBool (label : String) (value : Bool) : IO Unit :=
  IO.println s!"{label}={if value then 1 else 0}"

def main : IO Unit := do
  renderAnswers "source_order" (runTyped [] disjSourceOrder)
  renderAnswers "restore_before_right" (runTyped [] disjRestoresBeforeRight)
  renderAnswers "cut_prunes_right" (runTyped [] disjCutPrunesRight)
  renderAnswers "callee_cut_retains_caller"
    (runTyped calleeCutRetainsCallerDisjProgram calleeCutRetainsCallerDisj)
  renderAnswers "if_first_success" (runTyped [] hardIfFirstConditionSuccess)
  renderAnswers "if_then_failure" (runTyped [] hardIfThenFailureDoesNotRetry)
  renderAnswers "if_false_else" (runTyped [] hardIfFalseUsesElse)
  renderAnswers "if_condition_cut_else"
    (runTyped [] hardIfConditionCutPreservesElse)
  renderAnswers "if_then_cut_outer"
    (runTyped [] hardIfThenCutPrunesOuterDisj)
  renderAnswers "soft_if_condition_answers"
    (runTyped [] softIfKeepsConditionAnswers)
  renderAnswers "soft_if_then_retry"
    (runTyped [] softIfThenFailureRetriesCondition)
  renderAnswers "soft_if_false_else" (runTyped [] softIfFalseUsesElse)
  renderAnswers "soft_if_condition_cut_else"
    (runTyped [] softIfConditionCutPreservesElse)
  renderAnswers "soft_if_then_cut_outer"
    (runTyped [] softIfThenCutPrunesOuterDisj)
  renderAnswers "once_first" (runTyped [] onceKeepsFirstAnswer)
  renderAnswers "once_failure" (runTyped [] onceFailureHasNoAnswer)
  renderAnswers "once_cut_caller"
    (runTyped [] onceCutPreservesCallerDisj)
  renderAnswers "once_then_cut_outer"
    (runTyped [] onceThenCutPrunesCallerDisj)
  renderAnswers "once_restore_caller"
    (runTyped [] onceFailureRestoresCallerAlternative)
  renderStringAnswers "memberchk_first"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms
      Mettapedia.Logic.Prolog.ReaderDCGRegression.memberRegressionProgram
      Mettapedia.Logic.Prolog.ReaderDCGRegression.memberchkOrdinaryGoal)
  renderStringAnswers "memberchk_dynamic"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms
      Mettapedia.Logic.Prolog.ReaderDCGRegression.memberRegressionProgram
      Mettapedia.Logic.Prolog.ReaderDCGRegression.memberchkDynamicGoal)
  renderStringAnswers "memberchk_restores"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms
      Mettapedia.Logic.Prolog.ReaderDCGRegression.memberRegressionProgram
      Mettapedia.Logic.Prolog.ReaderDCGRegression.memberchkRestoredGoal)
  renderStringAnswers "meta_dynamic_disj"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.dynamicDisjunction)
  renderStringAnswers "meta_cut_retains_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaCutRetainsCaller)
  renderCount "call_three"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.binaryFactProgram
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.callThree)
  renderCount "heap_built_callable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.binaryFactProgram
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.heapBuiltCallable)
  renderCount "neg_rejects_success"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.negationRejectsSuccess)
  renderCount "neg_accepts_failure"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.negationAcceptsFailure)
  renderStringAnswers "neg_restores_trial_bindings"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.negationRestoresTrialBindings)
  renderStringAnswers "neg_cut_retains_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.negationCutRetainsCaller)
  renderCount "not_unify_distinct_atoms"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.distinctAtomsAreNotUnifiable)
  renderCount "not_unify_variable_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.variableAndAtomAreUnifiable)
  renderStringAnswers "not_unify_restores_trial_bindings"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.notUnifyRestoresTrialBindings)
  renderCount "meta_nonvar_bound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaNonvarBound)
  renderCount "meta_nonvar_variable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaNonvarVariable)
  renderCount "meta_forall_succeeds"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaForallSucceeds)
  renderCount "meta_forall_fails"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaForallFails)
  renderStringAnswers "meta_forall_restores_bindings"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaForallRestoresBindings)
  renderCount "term_atom_accepts_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomAcceptsAtom)
  renderCount "term_atom_rejects_integer"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomRejectsInteger)
  renderCount "term_atom_rejects_list_nil"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomRejectsListNil)
  renderCount "term_atomic_accepts_string"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomicAcceptsString)
  renderCount "term_atomic_rejects_compound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomicRejectsCompound)
  renderCount "term_compound_accepts_pair"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.compoundAcceptsPair)
  renderCount "term_compound_rejects_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.compoundRejectsAtom)
  renderCount "term_number_accepts_integer"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.numberAcceptsInteger)
  renderCount "term_number_accepts_float"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.numberAcceptsFloat)
  renderCount "term_number_rejects_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.numberRejectsAtom)
  renderCount "term_string_accepts_string"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.stringAcceptsString)
  renderCount "term_string_rejects_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.stringRejectsAtom)
  renderCount "term_meta_atom_accepts_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaAtomAcceptsAtom)
  renderCount "term_reference_atomic_not_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.referenceIsAtomicButNotAtom)
  renderCount "ground_nested_compound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.groundAcceptsCompound)
  renderCount "ground_unbound_variable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.groundRejectsVariable)
  renderCount "ground_nested_free_leaf"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.groundRejectsNestedVariable)
  renderCount "ground_rational_cycle"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.groundAcceptsRationalCompound)
  renderCount "ground_rational_free_leaf"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.groundRejectsRationalCompoundWithFreeLeaf)
  renderCount "is_list_finite"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.isListAcceptsFinite)
  renderCount "is_list_improper"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.isListRejectsImproper)
  renderCount "is_list_variable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.isListRejectsVariable)
  renderCount "is_list_rational_spine"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.isListRejectsRationalSpine)
  renderCount "is_list_cyclic_head"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.isListAcceptsCyclicHead)
  renderCount "atom_codes_forward"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomCodesForward)
  renderStringAnswers "atom_codes_reverse"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomCodesReverse
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderIntegerAnswers "atom_codes_binds_element"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomCodesBindsElement
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderCount "atom_codes_mismatch"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.atomCodesMismatch)
  renderCount "string_codes_forward"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.stringCodesForward)
  renderStringAnswers "string_codes_reverse"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runStringsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.stringCodesReverse
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderCount "code_type_space"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.codeTypeSpace)
  renderCount "code_type_newline_space"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.codeTypeNewlineSpace)
  renderCount "code_type_letter_not_space"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.codeTypeLetterNotSpace)
  renderCount "code_type_digit"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.codeTypeDigit)
  renderCount "code_type_letter_not_digit"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.codeTypeLetterNotDigit)
  renderCount "code_type_meta_space"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaCodeTypeSpace)
  renderCount "identity_same_variable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identitySameVariable)
  renderCount "identity_distinct_variables"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityDistinctVariables)
  renderCount "nonidentity_distinct_variables"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.nonIdentityDistinctVariables)
  renderCount "identity_separate_compounds"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identitySeparateCompounds)
  renderCount "identity_different_compounds"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityDifferentCompounds)
  renderCount "identity_variable_sharing"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityDistinguishesVariableSharing)
  renderCount "identity_equal_rational_cycles"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityEqualRationalCycles)
  renderCount "identity_different_rational_cycles"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityDifferentRationalCycles)
  renderStringAnswers "identity_failure_no_bind"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityFailureDoesNotBind)
  renderCount "identity_meta_same_variable"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaIdentitySameVariable)
  renderCount "identity_numeric_types"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityDistinguishesNumericTypes)
  renderCount "identity_equal_strings"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityEqualStrings)
  renderCount "identity_atom_zero_compound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.identityAtomNotZeroArityCompound)
  renderCount "nonidentity_different_compounds"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.nonIdentityDifferentCompounds)
  renderCount "univ_decompose_compound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univDecomposesCompound)
  renderCount "univ_construct_compound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univConstructsCompound)
  renderCount "univ_decompose_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univDecomposesAtom)
  renderCount "univ_construct_atom"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univConstructsAtom)
  renderCount "univ_decompose_integer"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univDecomposesInteger)
  renderCount "univ_construct_sharing"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univConstructionPreservesSharing)
  renderCount "univ_decompose_sharing"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.univDecompositionPreservesSharing)
  renderCount "univ_meta_construct"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaUnivConstructsCompound)
  renderIntegerAnswers "integer_addition"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerAddition
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderIntegerAnswers "integer_nested"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerNestedArithmetic
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderIntegerAnswers "integer_subtraction"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerSubtraction
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderIntegerAnswers "integer_mod_negative_dividend"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerModuloNegativeDividend
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderIntegerAnswers "integer_mod_negative_divisor"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerModuloNegativeDivisor
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderCount "integer_is_mismatch"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerIsMismatchFails)
  renderCount "integer_comparisons"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerComparisonsSucceed)
  renderStringAnswers "integer_comparison_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.integerComparisonFailureRetainsCaller)
  renderIntegerAnswers "integer_meta_addition"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runIntegersFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.metaIntegerAddition
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderStringAnswers "catch_ground"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.caughtGround)
  renderRaisedAtom "catch_throw_time_reject"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runRaisedAtom []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.throwTimeBoundCatcherRejects)
  renderRaisedAtom "catch_recovery_rethrow"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runRaisedAtom []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.recoveryRethrowEscapes)
  renderStringAnswers "catch_guard_cut_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.guardedCutRetainsCaller)
  renderStringAnswers "catch_recovery_cut_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.recoveryCutRetainsCaller)
  renderStringAnswers "catch_guard_answers"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.catchRetainsGuardedAnswers)
  renderRaisedAtom "catch_nested_throw_time_reject"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runRaisedAtom []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.nestedMismatchRetainsThrowTimeBinding)
  renderCount "catch_copy_separates_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.packetCopySeparatesCaller)
  renderCount "catch_copy_preserves_sharing"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.packetCopyPreservesSharing)
  renderCount "catch_copy_preserves_separation"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.packetCopyPreservesSeparation)
  renderCount "throw_variable_instantiation_error"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.throwVariableRaisesInstantiationError)
  renderAtomBags "findall_order_multiplicity"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallOrderMultiplicity
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_binding_isolation"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallIsolatesGeneratorBindings
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_empty"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallEmpty
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_cut_retains_caller"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallCutRetainsCaller
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderAtomBags "findall_exception_discards_partial"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomBagsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.findallExceptionDiscardsPartialBag
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.bagIdentity)
  renderBool "findall_copy_fresh_shared"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.copiedSolutionsAreFreshAndShared
  renderBool "findall_copy_separation"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.copiedSolutionPreservesSeparation
  renderStringAnswers "db_assertz_then_call"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertzThenCall)
  renderStringAnswers "db_failed_branch_persists"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.failedBranchAssertionPersists)
  renderStringAnswers "db_asserta_assertz_order"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertaAndAssertzOrder)
  renderCount "db_assertz_ref_bound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertzReferenceIsBound)
  renderCount "db_asserta_ref_bound"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertaReferenceIsBound)
  renderCount "db_assert_refs_distinct"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertedReferencesAreDistinct)
  renderCount "db_assert_ref_roundtrip"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.assertedReferenceRoundTrip)
  renderStringAnswers "db_retract_source_order"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractFactsInOrder)
  renderStringAnswers "db_retract_cut_prunes_later"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractCutPrunesLater)
  renderStringAnswers "db_retract_fact_skips_rule"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractFactSkipsRule)
  renderStringAnswers "db_retract_failed_branch_persists"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.failedBranchRetractionPersists)
  renderBool "db_retract_snapshot_no_drift"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractSnapshotDoesNotDrift
  renderStringAnswers "db_retract_snapshot_retains_erased"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtoms []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.retractSnapshotRetainsErasedCandidate)
  renderStringAnswers "db_clause_source_order"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseFactsInOrder
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderStringAnswers "db_clause_bound_reference"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseBoundReferenceSelectsOccurrence
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderStringAnswers "db_clause_rule_body"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseRuleBody
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.yIdentity)
  renderStringAnswers "db_clause_cut_prunes_later"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseCutPrunesLater
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderCount "db_clause_reference_roundtrip"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runCount []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseReferenceRoundTrip)
  renderStringAnswers "db_clause_snapshot_no_drift"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseSnapshotDoesNotDrift
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderStringAnswers "db_clause_snapshot_retains_erased"
    (Mettapedia.Logic.Prolog.SourceRuntimeRegression.runAtomsFor []
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.clauseSnapshotRetainsErasedCandidate
      Mettapedia.Logic.Prolog.SourceRuntimeRegression.xIdentity)
  renderBool "db_snapshot_no_drift"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.snapshotDoesNotDrift
  renderStringAnswers "db_snapshot_later_call"
    Mettapedia.Logic.Prolog.SourceRuntimeRegression.laterCallSeesAssertion
  renderBool "dcg_terminal_sharing"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.terminalSharingExecutes
  renderBool "dcg_braced_goal"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.bracedGoalExecutes
  renderBool "dcg_disjunction"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.disjunctionExecutes
  renderBool "dcg_string_terminal"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.stringTerminalExecutes
  renderBool "dcg_variable_list"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.variableListBodyExecutes
  renderBool "dcg_variable_list_sharing"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.variableListBodyPreservesSharing
  renderBool "dcg_variable_string"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.variableStringBodyExecutes
  renderBool "dcg_phrase_two"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.sourcePhraseTwoExecutes
  renderBool "dcg_phrase_three_rest"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.sourcePhraseThreeRetainsRest
  renderBool "dcg_variable_braced"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.variableBracedBodyExecutes
  renderBool "dcg_dynamic_cut_caller"
    Mettapedia.Logic.Prolog.ReaderDCGRegression.dynamicCutRetainsCallerClause
