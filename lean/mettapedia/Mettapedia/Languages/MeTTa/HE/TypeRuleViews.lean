import Mettapedia.Languages.MeTTa.HE.TypeRuleData

/-!
# Inspectable local HE rules and their source guards

Every constructor of the independent reference rule presentation has a data
view. Premise occurrences and selection positions remain ordered. Guard
descriptions are requests, not proofs: the input source rule already carries
the actual local side conditions needed for its use. Its recursive premises
remain holes, supplied only when applying the rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeRuleData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RulePresentation
open TypedApplyEncoding (bindingsData index)

deriving instance DecidableEq for ApplicabilityOutcome
deriving instance DecidableEq for Judgment

variable {space : Space} {lookup : TypeLookupRel} {matching : Matching}
variable {premises : List Judgment} {goal : Judgment}

def ruleName : Rule space lookup matching premises goal → String
  | .annotationsNil .. => "annotations-nil"
  | .annotationsHit .. => "annotations-hit"
  | .annotationsSkip .. => "annotations-skip"
  | .intrinsicInt .. => "intrinsic-int"
  | .intrinsicBool .. => "intrinsic-bool"
  | .intrinsicString .. => "intrinsic-string"
  | .intrinsicCustom .. => "intrinsic-custom"
  | .occurrencesVariable .. => "occurrences-variable"
  | .occurrencesGrounded .. => "occurrences-grounded"
  | .occurrencesSymbol .. => "occurrences-symbol"
  | .occurrencesUnit .. => "occurrences-unit"
  | .occurrencesExpression .. => "occurrences-expression"
  | .storageVariable .. => "storage-variable"
  | .storageGroundedKnown .. => "storage-grounded-known"
  | .storageGroundedUndefined .. => "storage-grounded-undefined"
  | .storageSymbolKnown .. => "storage-symbol-known"
  | .storageSymbolUndefined .. => "storage-symbol-undefined"
  | .storageUnit .. => "storage-unit"
  | .storageExpressionKnown .. => "storage-expression-known"
  | .storageExpressionUndefined .. => "storage-expression-undefined"
  | .lookupQuery .. => "lookup-query"
  | .typeOf .. => "type-of"
  | .matchUndefinedLeft .. => "match-undefined-left"
  | .matchAtomLeft .. => "match-atom-left"
  | .matchUndefinedRight .. => "match-undefined-right"
  | .matchAtomRight .. => "match-atom-right"
  | .matchStructural .. => "match-structural"
  | .matchingPolicy .. => "matching-policy"
  | .typeAt .. => "type-at"
  | .castSuccess .. => "cast-success"
  | .castFailure .. => "cast-failure"
  | .castBatchSuccess .. => "cast-batch-success"
  | .castBatchFailure .. => "cast-batch-failure"
  | .functionType .. => "function-type"
  | .argumentsNil .. => "arguments-nil"
  | .argumentsCons .. => "arguments-cons"
  | .application .. => "application"
  | .applicable .. => "applicable"
  | .wrongArity .. => "wrong-arity"
  | .badArgument .. => "bad-argument"
  | .badReturn .. => "bad-return"

private def guard (name : String) (arguments : List Atom) : Atom :=
  .expression (.symbol name :: arguments)

/-- Policy guards name their policy in the surrounding sequent. No search
deadline or failed attempt is encoded as a no-match/no-success certificate. -/
def ruleGuards : Rule space lookup matching premises goal → List Atom
  | .annotationsSkip subject head _ _ _ => [guard "NotAnnotation" [subject, head]]
  | .storageGroundedKnown _ type _ => [guard "NotUndefined" [type]]
  | .storageSymbolKnown _ types _ | .storageExpressionKnown _ _ types _ =>
      [guard "Nonempty" [.expression types]]
  | .lookupQuery before subject expected types _ =>
      [guard "LookupPolicy" [bindingsData before, subject, expected, .expression types]]
  | .typeOf _ types position | .typeAt _ _ _ types position =>
      [guard "Occurrence" [index position.val, .expression types]]
  | .matchStructural expected actual before matched after _ _ _ _ _ _ =>
      [guard "OrdinaryType" [expected], guard "OrdinaryType" [actual],
       guard "StructuralMatch" [expected, actual, bindingsData matched],
       guard "Merge" [bindingsData before, bindingsData matched, bindingsData after]]
  | .matchingPolicy expected actual before after _ =>
      [guard "MatchingPolicy" [expected, actual, bindingsData before, bindingsData after]]
  | .castSuccess _ expected _ before _ earlier _ _ =>
      [guard "NoEarlierStructuralMatch" [expected, .expression earlier, bindingsData before]]
  | .castFailure _ expected before types position _ =>
      [guard "Occurrence" [index position.val, .expression types],
       guard "NoStructuralMatch" [expected, .expression types, bindingsData before]]
  | .castBatchSuccess _ expected _ before _ earlier _ _ =>
      [guard "NoEarlierPolicyMatch" [expected, .expression earlier, bindingsData before]]
  | .castBatchFailure _ expected before types _ =>
      [guard "NoPolicyMatch" [expected, .expression types, bindingsData before]]
  | .wrongArity _ _ _ _ arguments argumentTypes _ _ =>
      [guard "DifferentLengths" [.expression arguments, .expression argumentTypes]]
  | .badArgument operator functionType expected _ bad expectedArg actual
      beforeArgs afterArgs _ afterTypes before atBad _ _ _ =>
      [guard "EqualLengths" [.expression afterArgs, .expression afterTypes],
       guard "NoStructuralMatch" [expectedArg, .expression [actual], bindingsData atBad],
       guard "NoApplication" [.expression (operator :: (beforeArgs ++ bad :: afterArgs)),
         functionType, expected, bindingsData before]]
  | .badReturn operator functionType expected returnType arguments _ before intermediate _ _ =>
      [guard "NoStructuralMatch" [expected, .expression [returnType], bindingsData intermediate],
       guard "NoApplication" [.expression (operator :: arguments), functionType, expected, bindingsData before]]
  | _ => []

def ruleData (bagOrder : Multiset Atom → List Atom)
    (lookupName matchingName : String) (rule : Rule space lookup matching premises goal) : Atom :=
  .expression [.symbol "HEReferenceRule", .grounded (.string (ruleName rule)),
    .expression (premises.map (fun premise =>
      sequentData space lookupName matchingName (judgmentData bagOrder premise))),
    sequentData space lookupName matchingName (judgmentData bagOrder goal),
    .expression (ruleGuards rule)]

def readRuleData : Atom → Option (String × List (Space × String × String × Judgment) ×
    (Space × String × String × Judgment) × List Atom)
  | .expression [.symbol "HEReferenceRule", .grounded (.string name),
      .expression premises, conclusion, .expression guards] => do
      return (name, ← premises.mapM readSequent, ← readSequent conclusion, guards)
  | _ => none

private theorem read_sequents (bagOrder : Multiset Atom → List Atom)
    (retained : ∀ bag, (bagOrder bag : Multiset Atom) = bag)
    (space : Space) (lookupName matchingName : String) (premises : List Judgment) :
    (premises.map (fun premise => sequentData space lookupName matchingName
      (judgmentData bagOrder premise))).mapM readSequent =
      some (premises.map fun premise => (space, lookupName, matchingName, premise)) := by
  induction premises with
  | nil => rfl
  | cons premise rest ih => simp [readSequent_sequentData bagOrder retained, ih]

theorem readRuleData_ruleData (bagOrder : Multiset Atom → List Atom)
    (retained : ∀ bag, (bagOrder bag : Multiset Atom) = bag)
    (lookupName matchingName : String) (rule : Rule space lookup matching premises goal) :
    readRuleData (ruleData bagOrder lookupName matchingName rule) =
      some (ruleName rule, premises.map (fun premise => (space, lookupName, matchingName, premise)),
        (space, lookupName, matchingName, goal), ruleGuards rule) := by
  simp [readRuleData, ruleData, read_sequents bagOrder retained,
    readSequent_sequentData bagOrder retained]

/-- Equal candidate types at different positions remain different rule
views; the occurrence field is not inferred from equality of the types. -/
theorem duplicate_type_positions_distinct (bagOrder : Multiset Atom → List Atom)
    (lookupName matchingName : String) (subject type : Atom) :
    ruleData bagOrder lookupName matchingName
        (Rule.typeOf (space := space) (lookup := lookup) (matching := matching) subject [type, type] 0) ≠
      ruleData bagOrder lookupName matchingName
        (Rule.typeOf (space := space) (lookup := lookup) (matching := matching) subject [type, type] 1) := by
  simp [ruleData, ruleName, ruleGuards, guard, index]

#print axioms readRuleData_ruleData
#print axioms duplicate_type_positions_distinct

end Mettapedia.Languages.MeTTa.HE.TypeRuleData
