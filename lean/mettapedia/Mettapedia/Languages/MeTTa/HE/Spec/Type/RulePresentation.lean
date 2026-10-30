import Mettapedia.Languages.MeTTa.HE.Spec.Type
import Mettapedia.TypeTheory.JudgmentDerivation

/-!
# Rule data for the published HE typing reference

This presentation retains the source relations' declaration occurrences,
grounded types, ordered lookup policy, matching, casts and applicability.
Its trees use the shared `JudgmentDerivation` owner. Local rule data do not
contain proofs of their recursive typing premises. Lookup and custom matching
remain explicitly selected external relations; they are not pooled across
policies. Native whole-expression inference and its private alpha-renaming
packages remain with `Type.Presentation.Exact`.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.RulePresentation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.TypeTheory.JudgmentDerivation
open Spec.Match.Merge

abbrev Matching := Atom → Atom → Bindings → Bindings → Prop

/-- Each constructor is a request for one independently defined source
judgment. A request contains data, not evidence that it holds. -/
inductive Judgment where
  | annotations (subject : Atom) (rows types : List Atom)
  | intrinsic (value : GroundedValue) (type : Atom)
  | occurrences (subject : Atom) (types : Multiset Atom)
  | storage (subject : Atom) (types : List Atom)
  | lookup (before : Bindings) (subject expected : Atom) (types : List Atom)
  | typeOf (subject type : Atom)
  | matchTypes (expected actual : Atom) (before after : Bindings)
  | matching (expected actual : Atom) (before after : Bindings)
  | typeAt (before : Bindings) (subject expected actual : Atom)
  | cast (subject expected : Atom) (before : Bindings) (result : ResultPair)
  | castBatch (subject expected : Atom) (before : Bindings) (results : ResultSet)
  | functionType (type : Atom) (arguments : List Atom) (result : Atom)
  | arguments (arguments expected : List Atom) (before after : Bindings)
  | application (expression type expected : Atom) (before after : Bindings)
  | applicability (expression type expected : Atom) (before : Bindings)
      (outcome : ApplicabilityOutcome)

def Source (space : Space) (lookup : TypeLookupRel) (matching : Matching) : Judgment → Prop
  | .annotations subject rows types => AnnotationTypesRel subject rows types
  | .intrinsic value type => IntrinsicGroundedTypeRel value type
  | .occurrences subject types => TypeOccurrencesRel (space.atoms : Multiset Atom) subject types
  | .storage subject types => StorageTypesRel space subject types
  | .lookup before subject expected types => lookup before subject expected types
  | .typeOf subject type => TypeOfRel space subject type
  | .matchTypes expected actual before after => TypeMatchRel expected actual before after
  | .matching expected actual before after => matching expected actual before after
  | .typeAt before subject expected actual => TypeAtRel lookup before subject expected actual
  | .cast subject expected before result => TypeCastRel space subject expected before result lookup
  | .castBatch subject expected before results =>
      TypeCastBatchRel space subject expected before results lookup matching
  | .functionType type arguments result => FunctionTypeRel type arguments result
  | .arguments arguments expected before after =>
      ArgumentsApplicableRel space arguments expected before after lookup
  | .application expression type expected before after =>
      ApplicationSuccessRel space expression type expected before after lookup
  | .applicability expression type expected before outcome =>
      ApplicabilityRel space expression type expected before outcome lookup

/-- The ordered premise list is part of a rule, even when two requests agree.
Negative selection conditions refer to complete source relations, never to an
exhausted search. Primitive match/merge and policy queries stay explicit. -/
inductive Rule (space : Space) (lookup : TypeLookupRel) (matching : Matching) :
    List Judgment → Judgment → Type where
  | annotationsNil (subject : Atom) : Rule space lookup matching [] (.annotations subject [] [])
  | annotationsHit (subject type : Atom) (rows types : List Atom) :
      Rule space lookup matching [.annotations subject rows types]
        (.annotations subject (.expression [.symbol ":", subject, type] :: rows) (type :: types))
  | annotationsSkip (subject head : Atom) (rows types : List Atom)
      (different : ∀ type, head ≠ .expression [.symbol ":", subject, type]) :
      Rule space lookup matching [.annotations subject rows types]
        (.annotations subject (head :: rows) types)
  | intrinsicInt (value : Int) : Rule space lookup matching [] (.intrinsic (.int value) (.symbol "Number"))
  | intrinsicBool (value : Bool) : Rule space lookup matching [] (.intrinsic (.bool value) (.symbol "Bool"))
  | intrinsicString (value : String) : Rule space lookup matching [] (.intrinsic (.string value) (.symbol "String"))
  | intrinsicCustom (type payload : String) :
      Rule space lookup matching [] (.intrinsic (.custom type payload) (.symbol type))
  | occurrencesVariable (name : String) :
      Rule space lookup matching [] (.occurrences (.var name) {Atom.undefinedType})
  | occurrencesGrounded (value : GroundedValue) (type : Atom) :
      Rule space lookup matching [.intrinsic value type] (.occurrences (.grounded value) {type})
  | occurrencesSymbol (name : String) :
      Rule space lookup matching [] (.occurrences (.symbol name)
        (withUndefined (annotationOccurrences (space.atoms : Multiset Atom) (.symbol name))))
  | occurrencesUnit : Rule space lookup matching [] (.occurrences (.expression []) {Atom.undefinedType})
  | occurrencesExpression (head : Atom) (tail : List Atom) :
      Rule space lookup matching [] (.occurrences (.expression (head :: tail))
        (withUndefined (annotationOccurrences (space.atoms : Multiset Atom) (.expression (head :: tail)))))
  | storageVariable (name : String) :
      Rule space lookup matching [] (.storage (.var name) [Atom.undefinedType])
  | storageGroundedKnown (value : GroundedValue) (type : Atom) (known : type ≠ Atom.undefinedType) :
      Rule space lookup matching [.intrinsic value type] (.storage (.grounded value) [type])
  | storageGroundedUndefined (value : GroundedValue) :
      Rule space lookup matching [.intrinsic value Atom.undefinedType]
        (.storage (.grounded value) [Atom.undefinedType])
  | storageSymbolKnown (name : String) (types : List Atom) (nonempty : types ≠ []) :
      Rule space lookup matching [.annotations (.symbol name) space.atoms types]
        (.storage (.symbol name) types)
  | storageSymbolUndefined (name : String) :
      Rule space lookup matching [.annotations (.symbol name) space.atoms []]
        (.storage (.symbol name) [Atom.undefinedType])
  | storageUnit : Rule space lookup matching [] (.storage (.expression []) [Atom.undefinedType])
  | storageExpressionKnown (head : Atom) (tail types : List Atom) (nonempty : types ≠ []) :
      Rule space lookup matching [.annotations (.expression (head :: tail)) space.atoms types]
        (.storage (.expression (head :: tail)) types)
  | storageExpressionUndefined (head : Atom) (tail : List Atom) :
      Rule space lookup matching [.annotations (.expression (head :: tail)) space.atoms []]
        (.storage (.expression (head :: tail)) [Atom.undefinedType])
  | lookupQuery (before : Bindings) (subject expected : Atom) (types : List Atom)
      (queried : lookup before subject expected types) :
      Rule space lookup matching [] (.lookup before subject expected types)
  | typeOf (subject : Atom) (types : List Atom) (position : Fin types.length) :
      Rule space lookup matching [.storage subject types] (.typeOf subject types[position])
  | matchUndefinedLeft (actual : Atom) (before : Bindings) :
      Rule space lookup matching [] (.matchTypes Atom.undefinedType actual before before)
  | matchAtomLeft (actual : Atom) (before : Bindings) :
      Rule space lookup matching [] (.matchTypes Atom.atomType actual before before)
  | matchUndefinedRight (expected : Atom) (before : Bindings) :
      Rule space lookup matching [] (.matchTypes expected Atom.undefinedType before before)
  | matchAtomRight (expected : Atom) (before : Bindings) :
      Rule space lookup matching [] (.matchTypes expected Atom.atomType before before)
  | matchStructural (expected actual : Atom) (before matched after : Bindings)
      (leftDefined : expected ≠ Atom.undefinedType) (leftOrdinary : expected ≠ Atom.atomType)
      (rightDefined : actual ≠ Atom.undefinedType) (rightOrdinary : actual ≠ Atom.atomType)
      (matchProof : MatchRel equalityGroundedSemantic expected actual matched)
      (mergeProof : MergeRel equalityGroundedSemantic before matched after) :
      Rule space lookup matching [] (.matchTypes expected actual before after)
  | matchingPolicy (expected actual : Atom) (before after : Bindings)
      (accepted : matching expected actual before after) :
      Rule space lookup matching [] (.matching expected actual before after)
  | typeAt (before : Bindings) (subject expected : Atom) (types : List Atom) (position : Fin types.length) :
      Rule space lookup matching [.lookup before subject expected types]
        (.typeAt before subject expected types[position])
  | castSuccess (subject expected actual : Atom) (before after : Bindings) (earlier later : List Atom)
      (skipped : ∀ type ∈ earlier, ∀ candidate, ¬TypeMatchRel expected type before candidate) :
      Rule space lookup matching [.lookup before subject expected (earlier ++ actual :: later),
        .matchTypes expected actual before after] (.cast subject expected before (subject, after))
  | castFailure (subject expected : Atom) (before : Bindings) (types : List Atom)
      (position : Fin types.length)
      (failed : ∀ type ∈ types, ∀ candidate, ¬TypeMatchRel expected type before candidate) :
      Rule space lookup matching [.lookup before subject expected types]
        (.cast subject expected before (mkError subject (.badType expected types[position]), before))
  | castBatchSuccess (subject expected actual : Atom) (before after : Bindings) (earlier later : List Atom)
      (skipped : ∀ type ∈ earlier, ∀ candidate, ¬matching expected type before candidate) :
      Rule space lookup matching [.lookup before subject expected (earlier ++ actual :: later),
        .matching expected actual before after] (.castBatch subject expected before [(subject, after)])
  | castBatchFailure (subject expected : Atom) (before : Bindings) (types : List Atom)
      (failed : ∀ type ∈ types, ∀ candidate, ¬matching expected type before candidate) :
      Rule space lookup matching [.lookup before subject expected types]
        (.castBatch subject expected before
          (types.map fun actual => (mkError subject (.badType expected actual), before)))
  | functionType (arguments : List Atom) (result : Atom) :
      Rule space lookup matching []
        (.functionType (.expression (.symbol "->" :: (arguments ++ [result]))) arguments result)
  | argumentsNil (before : Bindings) : Rule space lookup matching [] (.arguments [] [] before before)
  | argumentsCons (argument expected actual : Atom) (arguments expectedTypes : List Atom)
      (before next after : Bindings) :
      Rule space lookup matching [.typeAt before argument expected actual,
        .matchTypes expected actual before next, .arguments arguments expectedTypes next after]
        (.arguments (argument :: arguments) (expected :: expectedTypes) before after)
  | application (operator functionType expected returnType : Atom)
      (arguments argumentTypes : List Atom) (before intermediate after : Bindings) :
      Rule space lookup matching [.functionType functionType argumentTypes returnType,
        .arguments arguments argumentTypes before intermediate,
        .matchTypes expected returnType intermediate after]
        (.application (.expression (operator :: arguments)) functionType expected before after)
  | applicable (expression functionType expected : Atom) (before after : Bindings) :
      Rule space lookup matching [.application expression functionType expected before after]
        (.applicability expression functionType expected before (.success after))
  | wrongArity (operator functionType expected returnType : Atom)
      (arguments argumentTypes : List Atom) (before : Bindings)
      (different : arguments.length ≠ argumentTypes.length) :
      Rule space lookup matching [.functionType functionType argumentTypes returnType]
        (.applicability (.expression (operator :: arguments)) functionType expected before
          (.error (mkError (.expression (operator :: arguments)) .incorrectNumberOfArguments)))
  | badArgument (operator functionType expected returnType bad expectedArg actual : Atom)
      (argumentsBefore argumentsAfter typesBefore typesAfter : List Atom) (before atBad : Bindings)
      (lengths : argumentsAfter.length = typesAfter.length)
      (badMatch : ∀ candidate, ¬TypeMatchRel expectedArg actual atBad candidate)
      (noSuccess : ∀ after, ¬ApplicationSuccessRel space
        (.expression (operator :: (argumentsBefore ++ bad :: argumentsAfter))) functionType expected
        before after lookup) :
      Rule space lookup matching [.functionType functionType (typesBefore ++ expectedArg :: typesAfter) returnType,
        .arguments argumentsBefore typesBefore before atBad, .typeAt atBad bad expectedArg actual]
        (.applicability (.expression (operator :: (argumentsBefore ++ bad :: argumentsAfter)))
          functionType expected before (.error (mkError
            (.expression (operator :: (argumentsBefore ++ bad :: argumentsAfter)))
            (.badArgType (argumentsBefore.length + 1) expectedArg actual))))
  | badReturn (operator functionType expected returnType : Atom)
      (arguments argumentTypes : List Atom) (before intermediate : Bindings)
      (badMatch : ∀ candidate, ¬TypeMatchRel expected returnType intermediate candidate)
      (noSuccess : ∀ after, ¬ApplicationSuccessRel space
        (.expression (operator :: arguments)) functionType expected before after lookup) :
      Rule space lookup matching [.functionType functionType argumentTypes returnType,
        .arguments arguments argumentTypes before intermediate]
        (.applicability (.expression (operator :: arguments)) functionType expected before
          (.error (mkError (.expression (operator :: arguments)) (.badType expected returnType))))

def signature (space : Space) (lookup : TypeLookupRel) (matching : Matching) : Signature where
  Judgment := Judgment
  Rule conclusion := Σ premises, Rule space lookup matching premises conclusion
  Premise rule := Fin rule.1.length
  hypothesis rule position := rule.1[position]

abbrev Tree (space : Space) (lookup : TypeLookupRel) (matching : Matching) (goal : Judgment) :=
  Derivation (signature space lookup matching) goal

theorem local_sound {space : Space} {lookup : TypeLookupRel} {matching : Matching}
    {premises : List Judgment} {goal : Judgment} (rule : Rule space lookup matching premises goal)
    (children : ∀ position : Fin premises.length, Source space lookup matching premises[position]) :
    Source space lookup matching goal := by
  cases rule with
  | annotationsNil => exact .nil
  | annotationsHit => exact .hit (children 0)
  | annotationsSkip _ _ _ _ different => exact .skip different (children 0)
  | intrinsicInt => exact .int _
  | intrinsicBool => exact .bool _
  | intrinsicString => exact .string _
  | intrinsicCustom => exact .custom _ _
  | occurrencesVariable => exact .variable _
  | occurrencesGrounded => exact .grounded (children 0)
  | occurrencesSymbol => exact .symbol _
  | occurrencesUnit => exact .unit
  | occurrencesExpression => exact .expression _ _
  | storageVariable => exact .variable _ _
  | storageGroundedKnown _ _ known => exact .groundedKnown (children 0) known
  | storageGroundedUndefined => exact .groundedUndefined (children 0)
  | storageSymbolKnown _ _ nonempty => exact .symbolKnown (children 0) nonempty
  | storageSymbolUndefined => exact .symbolUndefined (children 0)
  | storageUnit => exact .unit _
  | storageExpressionKnown _ _ _ nonempty => exact .expressionKnown (children 0) nonempty
  | storageExpressionUndefined => exact .expressionUndefined (children 0)
  | lookupQuery _ _ _ _ queried => exact queried
  | typeOf _ _ position => exact ⟨_, children 0, List.getElem_mem position.isLt⟩
  | matchUndefinedLeft => exact .undefinedLeft _ _
  | matchAtomLeft => exact .atomLeft _ _
  | matchUndefinedRight => exact .undefinedRight _ _
  | matchAtomRight => exact .atomRight _ _
  | matchStructural _ _ _ _ _ h1 h2 h3 h4 hm hg => exact .structural h1 h2 h3 h4 hm hg
  | matchingPolicy _ _ _ _ accepted => exact accepted
  | typeAt _ _ _ _ position => exact ⟨_, children 0, List.getElem_mem position.isLt⟩
  | castSuccess _ _ _ _ _ _ _ skipped => exact .success (children 0) rfl skipped (children 1)
  | castFailure _ _ _ _ position failed =>
      exact .failure (children 0) (List.getElem_mem position.isLt) failed
  | castBatchSuccess _ _ _ _ _ _ _ skipped => exact .success (children 0) rfl skipped (children 1)
  | castBatchFailure _ _ _ _ failed => exact .failure (children 0) failed
  | functionType => rfl
  | argumentsNil => exact .nil _
  | argumentsCons => exact .cons (children 0) (children 1) (children 2)
  | application => exact .mk rfl (children 0) (children 1) (children 2)
  | applicable => exact .success (children 0)
  | wrongArity _ _ _ _ _ _ _ different => exact .wrongArity rfl (children 0) different
  | badArgument _ _ _ _ _ _ _ _ _ _ _ _ _ lengths badMatch noSuccess =>
      exact .badArgument rfl (children 0) lengths (children 1) (children 2) badMatch noSuccess
  | badReturn _ _ _ _ _ _ _ _ badMatch noSuccess =>
      exact .badReturn rfl (children 0) (children 1) badMatch noSuccess

def sourceAlgebra (space : Space) (lookup : TypeLookupRel) (matching : Matching) :
    Algebra (signature space lookup matching) where
  Carrier goal := PLift (Source space lookup matching goal)
  conclude rule children := ⟨local_sound rule.2 (fun position => (children position).down)⟩

theorem sound {space : Space} {lookup : TypeLookupRel} {matching : Matching} {goal : Judgment}
    (tree : Tree space lookup matching goal) : Source space lookup matching goal :=
  (interpret (sourceAlgebra space lookup matching) tree).down

#print axioms sound

end Mettapedia.Languages.MeTTa.HE.Spec.Type.RulePresentation
