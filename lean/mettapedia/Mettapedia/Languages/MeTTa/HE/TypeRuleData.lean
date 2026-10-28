import Mettapedia.Languages.MeTTa.HE.Spec.Type.RulePresentationCompleteness
import Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding

/-!
# Inspectable HE typing requests

These are ordinary atom data, read without evaluation. `|-` retains a space's
declaration occurrences and names the selected lookup and matching policies.
Policy names are references, not evidence that those policies are installed.
The codec does not turn a request into a derivation.

The source's unordered occurrence collection is represented by a list with
the same bag. Ordered queries, assignments, results and premises retain their
order. A renderer chooses an order only for that explicitly unordered field.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeRuleData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RulePresentation
open TypedApplyEncoding (bindingsData readBindings resultData readResult resultsData readResults)

def outcomeData : ApplicabilityOutcome → Atom
  | .success bindings => .expression [.symbol "HEApplies", bindingsData bindings]
  | .error error => .expression [.symbol "HEInapplicable", error]

def readOutcome : Atom → Option ApplicabilityOutcome
  | .expression [.symbol "HEApplies", bindings] => do return .success (← readBindings bindings)
  | .expression [.symbol "HEInapplicable", error] => some (.error error)
  | _ => none

@[simp] theorem readOutcome_outcomeData (outcome : ApplicabilityOutcome) :
    readOutcome (outcomeData outcome) = some outcome := by
  cases outcome <;> simp [readOutcome, outcomeData]

def judgmentData (bagOrder : Multiset Atom → List Atom) : Judgment → Atom
  | .annotations subject rows types =>
      .expression [.symbol "HEAnnotations", subject, .expression rows, .expression types]
  | .intrinsic value type => .expression [.symbol "HEIntrinsic", .grounded value, type]
  | .occurrences subject types => .expression [.symbol "HEOccurrences", subject, .expression (bagOrder types)]
  | .storage subject types => .expression [.symbol "HEStorageTypes", subject, .expression types]
  | .lookup before subject expected types =>
      .expression [.symbol "HELookup", bindingsData before, subject, expected, .expression types]
  | .typeOf subject type => .expression [.symbol ":", subject, type]
  | .matchTypes expected actual before after =>
      .expression [.symbol "HEMatchTypes", expected, actual, bindingsData before, bindingsData after]
  | .matching expected actual before after =>
      .expression [.symbol "HEPolicyMatch", expected, actual, bindingsData before, bindingsData after]
  | .typeAt before subject expected actual =>
      .expression [.symbol "HETypeAt", bindingsData before, subject, expected, actual]
  | .cast subject expected before result =>
      .expression [.symbol "HECast", subject, expected, bindingsData before, resultData result]
  | .castBatch subject expected before results =>
      .expression [.symbol "HECastBatch", subject, expected, bindingsData before, resultsData results]
  | .functionType type arguments result =>
      .expression [.symbol "HEFunctionType", type, .expression arguments, result]
  | .arguments arguments expected before after =>
      .expression [.symbol "HEArguments", .expression arguments, .expression expected,
        bindingsData before, bindingsData after]
  | .application expression type expected before after =>
      .expression [.symbol "HEApplication", expression, type, expected, bindingsData before, bindingsData after]
  | .applicability expression type expected before outcome =>
      .expression [.symbol "HEApplicability", expression, type, expected, bindingsData before, outcomeData outcome]

def readJudgment : Atom → Option Judgment
  | .expression [.symbol "HEAnnotations", subject, .expression rows, .expression types] =>
      some (.annotations subject rows types)
  | .expression [.symbol "HEIntrinsic", .grounded value, type] => some (.intrinsic value type)
  | .expression [.symbol "HEOccurrences", subject, .expression types] =>
      some (.occurrences subject (types : Multiset Atom))
  | .expression [.symbol "HEStorageTypes", subject, .expression types] => some (.storage subject types)
  | .expression [.symbol "HELookup", before, subject, expected, .expression types] => do
      return .lookup (← readBindings before) subject expected types
  | .expression [.symbol ":", subject, type] => some (.typeOf subject type)
  | .expression [.symbol "HEMatchTypes", expected, actual, before, after] => do
      return .matchTypes expected actual (← readBindings before) (← readBindings after)
  | .expression [.symbol "HEPolicyMatch", expected, actual, before, after] => do
      return .matching expected actual (← readBindings before) (← readBindings after)
  | .expression [.symbol "HETypeAt", before, subject, expected, actual] => do
      return .typeAt (← readBindings before) subject expected actual
  | .expression [.symbol "HECast", subject, expected, before, result] => do
      return .cast subject expected (← readBindings before) (← readResult result)
  | .expression [.symbol "HECastBatch", subject, expected, before, results] => do
      return .castBatch subject expected (← readBindings before) (← readResults results)
  | .expression [.symbol "HEFunctionType", type, .expression arguments, result] =>
      some (.functionType type arguments result)
  | .expression [.symbol "HEArguments", .expression arguments, .expression expected, before, after] => do
      return .arguments arguments expected (← readBindings before) (← readBindings after)
  | .expression [.symbol "HEApplication", expression, type, expected, before, after] => do
      return .application expression type expected (← readBindings before) (← readBindings after)
  | .expression [.symbol "HEApplicability", expression, type, expected, before, outcome] => do
      return .applicability expression type expected (← readBindings before) (← readOutcome outcome)
  | _ => none

theorem readJudgment_judgmentData (bagOrder : Multiset Atom → List Atom)
    (retained : ∀ bag, (bagOrder bag : Multiset Atom) = bag) (judgment : Judgment) :
    readJudgment (judgmentData bagOrder judgment) = some judgment := by
  cases judgment <;> simp [judgmentData, readJudgment, retained]

theorem judgmentData_injective (bagOrder : Multiset Atom → List Atom)
    (retained : ∀ bag, (bagOrder bag : Multiset Atom) = bag) :
    Function.Injective (judgmentData bagOrder) := by
  intro first second same
  have decoded := congrArg readJudgment same
  simpa only [readJudgment_judgmentData bagOrder retained, Option.some.injEq] using decoded

def sequentData (space : Space) (lookupName matchingName : String) (judgment : Atom) : Atom :=
  .expression [.symbol "|-",
    .expression [.symbol "HEContext", .expression space.atoms,
      .grounded (.string lookupName), .grounded (.string matchingName)], judgment]

def readSequent : Atom → Option (Space × String × String × Judgment)
  | .expression [.symbol "|-",
      .expression [.symbol "HEContext", .expression rows,
        .grounded (.string lookupName), .grounded (.string matchingName)], judgment] => do
      return (Space.ofList rows, lookupName, matchingName, ← readJudgment judgment)
  | _ => none

theorem readSequent_sequentData (bagOrder : Multiset Atom → List Atom)
    (retained : ∀ bag, (bagOrder bag : Multiset Atom) = bag)
    (space : Space) (lookupName matchingName : String) (judgment : Judgment) :
    readSequent (sequentData space lookupName matchingName (judgmentData bagOrder judgment)) =
      some (space, lookupName, matchingName, judgment) := by
  cases space
  simp [readSequent, sequentData, readJudgment_judgmentData bagOrder retained, Space.ofList]

/-- Inspecting an arbitrary classification request grants no theorem. -/
theorem variable_request_is_readable_but_unprovable :
    readJudgment (.expression [.symbol ":", .var "x", .symbol "Int"]) =
      some (.typeOf (.var "x") (.symbol "Int")) ∧
    ¬Nonempty (Tree Space.empty (rawTypeLookupRel Space.empty) TypeMatchRel
      (.typeOf (.var "x") (.symbol "Int"))) := by
  constructor
  · rfl
  · rintro ⟨tree⟩
    exact variable_not_int_type (sound tree)

theorem malformed_context_refused (judgment : Atom) :
    readSequent (.expression [.symbol "|-", .symbol "HEContext", judgment]) = none := rfl

/-- An ordered lookup has a different wire constructor from an occurrence bag. -/
theorem query_order_is_not_occurrence_bag (subject : Atom) (types : List Atom) :
    readJudgment (.expression [.symbol "HEStorageTypes", subject, .expression types]) ≠
      readJudgment (.expression [.symbol "HEOccurrences", subject, .expression types]) := by
  simp [readJudgment]

#print axioms readJudgment_judgmentData
#print axioms readSequent_sequentData
#print axioms variable_request_is_readable_but_unprovable

end Mettapedia.Languages.MeTTa.HE.TypeRuleData
