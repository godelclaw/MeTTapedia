import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionPublication

/-!
# Execution of the three source type-definition equations

The actual retained helper computes the abstraction/representation equation,
the representation retraction and its Boolean equality with the predicate.
Their operands execute before the shared equality constructor. Both returned
formulas then enter the actual publication tail with all live bindings intact.
This law starts after the helper's sequential declarations; logical admission
and execution of those preceding declarations are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionEquations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Effects (State)
open Representation (registeredOperatorAtom termAtom)
open TypeDefinitionFormation (command)

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:extend-type"))[0]'(by decide)

/-- The actual source after its sequential declaration construction. -/
def sourceBody : Atom :=
  match equation.body with
  | .expression [_, _, body] => body
  | _ => .symbol "None"

private def application (function argument : Atom) : Atom :=
  .expression [.symbol "HOL:App", function, argument]

private def firstCall : Atom := .expression [.symbol "hol-light:equation",
  application (.var "abs") (application (.var "rep") (.var "a")), .var "a"]
private def retractionCall : Atom := .expression [.symbol "hol-light:equation",
  application (.var "rep") (application (.var "abs") (.var "r")), .var "r"]
private def secondCall : Atom := .expression [.symbol "hol-light:equation",
  application (.var "predicate") (.var "r"), .var "retraction"]
private def secondCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "second"], TypeDefinitionPublication.sourceTail),
   (.var "malformed", .symbol "None")]
private def secondBody : Atom := .expression [.symbol "case", secondCall,
  .expression (secondCases.map fun row => .expression [row.1, row.2])]
private def firstCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .var "first"],
      .expression [.symbol "Some", .var "retraction"]], secondBody),
   (.var "malformed", .symbol "None")]

theorem source_body_shape : sourceBody = .expression [.symbol "case",
    .expression [firstCall, retractionCall],
    .expression (firstCases.map fun row => .expression [row.1, row.2])] := by decide

def abstractionTerm (abstraction : Const) (represented carrier : Ty) : DBTerm :=
  .const abstraction (.function represented carrier)
def representationTerm (representation : Const) (represented carrier : Ty) : DBTerm :=
  .const representation (.function carrier represented)
def carrierVariable (carrier : Ty) : DBTerm := .free ⟨Name.global "a", carrier⟩
def representationVariable (represented : Ty) : DBTerm := .free ⟨Name.global "r", represented⟩

def firstLaw (abstraction representation : Const) (represented carrier : Ty) : DBTerm :=
  CanonicalTerm.equalityDB carrier
    (.app (abstractionTerm abstraction represented carrier)
      (.app (representationTerm representation represented carrier) (carrierVariable carrier)))
    (carrierVariable carrier)

def retractionLaw (abstraction representation : Const) (represented carrier : Ty) : DBTerm :=
  CanonicalTerm.equalityDB represented
    (.app (representationTerm representation represented carrier)
      (.app (abstractionTerm abstraction represented carrier) (representationVariable represented)))
    (representationVariable represented)

def secondLaw (abstraction representation : Const) (represented carrier : Ty) (predicate : DBTerm) : DBTerm :=
  CanonicalTerm.equalityDB Ty.bool (.app predicate (representationVariable represented))
    (retractionLaw abstraction representation represented carrier)

/-- The formulas executed below are exactly the pointwise output of the
existing shared type-definition construction, including its orientation. -/
theorem pointwise_output_formulas (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) :
    let operator := TypeOp.mk request.typeName (.defined request.predicateSource request.typeVariables)
    let carrier := Ty.op operator (request.typeVariables.map Ty.var)
    let abstraction := Const.mk request.abstractionName (.abstraction operator)
    let representation := Const.mk request.representationName (.representation operator)
    let output := makePointwiseTypeOperatorDefinition request predicate witness application boolean
    output.abstractionRepresentationTheorem.sequent.concl.term =
      firstLaw abstraction representation witness.ty carrier ∧
    output.representationAbstractionTheorem.sequent.concl.term =
      secondLaw abstraction representation witness.ty carrier predicate.term := by
  have semantics := DefinitionAdapters.makePointwiseTypeOperatorDefinition_semantics
    request predicate witness application boolean
  simpa only [firstLaw, secondLaw, retractionLaw, abstractionTerm, representationTerm,
    carrierVariable, representationVariable] using ⟨semantics.2.2.2.1, semantics.2.2.2.2⟩

/-- Successful registered admission uses those same executed formulas.
The signature context and its admission checks remain the existing authority. -/
theorem admitted_output_formulas (context : DefinitionAdapters.TheoryContext)
    (witnesses : SignatureFormation.InstanceWitnesses) (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) (result : DefinitionAdapters.SourceTypeDefinitionResult)
    (accepted : DefinitionAdapters.admitSourceTypeInTheory context witnesses request = some result) :
    let operator := TypeOp.mk request.typeName (.defined request.predicateSource request.typeVariables)
    let carrier := Ty.op operator (request.typeVariables.map Ty.var)
    let abstraction := Const.mk request.abstractionName (.abstraction operator)
    let representation := Const.mk request.representationName (.representation operator)
    result.output.abstractionRepresentationTheorem.sequent.concl.term =
      firstLaw abstraction representation witness.ty carrier ∧
    result.output.representationAbstractionTheorem.sequent.concl.term =
      secondLaw abstraction representation witness.ty carrier predicate.term := by
  rw [(TypeDefinitionFormation.source_result_components context witnesses request predicate witness
    application boolean result accepted).2]
  exact pointwise_output_formulas request predicate witness application boolean

private theorem application_variable_certificate (bindings : Subst) (state : State)
    (constants : Const → Atom) (function argument : DBTerm) (functionKey argumentKey : String)
    (functionCaptured : applySubst bindings (.var functionKey) = termAtom registeredOperatorAtom constants [] function)
    (argumentCaptured : applySubst bindings (.var argumentKey) = termAtom registeredOperatorAtom constants [] argument) :
    BoundCalls.CorePath.PureReturns program bindings state
      (application (.var functionKey) (.var argumentKey)) state
      (termAtom registeredOperatorAtom constants [] (.app function argument)) := by
  unfold application termAtom
  apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state
    "HOL:App" _ _ _ _ (by decide) (by decide)
  · simpa only [functionCaptured] using BoundCalls.CorePath.variable_returns program bindings state functionKey
  · simpa only [argumentCaptured] using BoundCalls.CorePath.variable_returns program bindings state argumentKey

private theorem first_certificate (bindings : Subst) (state : State) (constants : Const → Atom)
    (abstraction representation : Const) (represented carrier : Ty)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (absCaptured : applySubst bindings (.var "abs") =
      termAtom registeredOperatorAtom constants [] (abstractionTerm abstraction represented carrier))
    (repCaptured : applySubst bindings (.var "rep") =
      termAtom registeredOperatorAtom constants [] (representationTerm representation represented carrier))
    (aCaptured : applySubst bindings (.var "a") =
      termAtom registeredOperatorAtom constants [] (carrierVariable carrier)) :
    BoundCalls.CorePath.PureReturns program bindings state firstCall state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants []
        (firstLaw abstraction representation represented carrier)]) := by
  unfold firstCall firstLaw
  refine Equality.authored_equation_computed_certificate constants bindings state [] _ _ carrier
    ?_ ?_ equalityIdentity _ _ ?_ ?_
  · simp [abstractionTerm, representationTerm, carrierVariable, DBTerm.inferType,
      Ty.function, Ty.destFunction?, TypeOp.function]
  · simp [carrierVariable, DBTerm.inferType]
  · simp only [application, termAtom]
    apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state
      "HOL:App" _ _ _ _ (by decide) (by decide)
    · simpa only [absCaptured, termAtom] using BoundCalls.CorePath.variable_returns program bindings state "abs"
    · simpa only [application, termAtom] using
        application_variable_certificate bindings state constants _ _ "rep" "a" repCaptured aCaptured
  · simpa only [aCaptured] using BoundCalls.CorePath.variable_returns program bindings state "a"

private theorem retraction_certificate (bindings : Subst) (state : State) (constants : Const → Atom)
    (abstraction representation : Const) (represented carrier : Ty)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (absCaptured : applySubst bindings (.var "abs") =
      termAtom registeredOperatorAtom constants [] (abstractionTerm abstraction represented carrier))
    (repCaptured : applySubst bindings (.var "rep") =
      termAtom registeredOperatorAtom constants [] (representationTerm representation represented carrier))
    (rCaptured : applySubst bindings (.var "r") =
      termAtom registeredOperatorAtom constants [] (representationVariable represented)) :
    BoundCalls.CorePath.PureReturns program bindings state retractionCall state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants []
        (retractionLaw abstraction representation represented carrier)]) := by
  unfold retractionCall retractionLaw
  refine Equality.authored_equation_computed_certificate constants bindings state [] _ _ represented
    ?_ ?_ equalityIdentity _ _ ?_ ?_
  · simp [abstractionTerm, representationTerm, representationVariable, DBTerm.inferType,
      Ty.function, Ty.destFunction?, TypeOp.function]
  · simp [representationVariable, DBTerm.inferType]
  · simp only [application, termAtom]
    apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state
      "HOL:App" _ _ _ _ (by decide) (by decide)
    · simpa only [repCaptured, termAtom] using BoundCalls.CorePath.variable_returns program bindings state "rep"
    · simpa only [application, termAtom] using
        application_variable_certificate bindings state constants _ _ "abs" "r" absCaptured rCaptured
  · simpa only [rCaptured] using BoundCalls.CorePath.variable_returns program bindings state "r"

/-- The actual three equation calls compute both pointwise laws, then publish
them. The intermediate retraction is constructed and typed, never supplied
as an assumed result or cached theorem. -/
theorem authored_equations_publish (operators declarations axioms key dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (constants : Const → Atom)
    (abstraction representation : Const) (represented carrier : Ty) (predicate : DBTerm)
    (predicateChecked : predicate.inferType [] = some (.function represented Ty.bool))
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (worldCaptured : applySubst bindings (.var "extended") =
      ProofLookup.sourceState operators declarations axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var "key") = key)
    (requestCaptured : applySubst bindings (.var "request") =
      command typeName abstractionName representationName premise)
    (dependenciesCaptured : applySubst bindings (.var "dependencies") = dependencies)
    (predicateCaptured : applySubst bindings (.var "predicate") = termAtom registeredOperatorAtom constants [] predicate)
    (absCaptured : applySubst bindings (.var "abs") =
      termAtom registeredOperatorAtom constants [] (abstractionTerm abstraction represented carrier))
    (repCaptured : applySubst bindings (.var "rep") =
      termAtom registeredOperatorAtom constants [] (representationTerm representation represented carrier))
    (aCaptured : applySubst bindings (.var "a") = termAtom registeredOperatorAtom constants [] (carrierVariable carrier))
    (rCaptured : applySubst bindings (.var "r") =
      termAtom registeredOperatorAtom constants [] (representationVariable represented))
    (fresh : ∀ name ∈ ["first", "retraction", "second", "withFirst"], Subst.lookup bindings name = none)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none) :
    BoundCalls.PureReturns program bindings state sourceBody state
      (TypeDefinitionPublication.finalResult operators declarations axioms key
        (termAtom registeredOperatorAtom constants [] (firstLaw abstraction representation represented carrier))
        (termAtom registeredOperatorAtom constants [] (secondLaw abstraction representation represented carrier predicate))
        dependencies typeName abstractionName representationName premise cache receipts) := by
  let first := termAtom registeredOperatorAtom constants [] (firstLaw abstraction representation represented carrier)
  let retraction := termAtom registeredOperatorAtom constants [] (retractionLaw abstraction representation represented carrier)
  let second := termAtom registeredOperatorAtom constants [] (secondLaw abstraction representation represented carrier predicate)
  let firstBound := ("retraction", retraction) :: ("first", first) :: bindings
  let secondBound := ("second", second) :: firstBound
  have firstFresh := fresh "first" (by simp)
  have retractionFresh := fresh "retraction" (by simp)
  have secondFresh := fresh "second" (by simp)
  have resultFresh := fresh "withFirst" (by simp)
  dsimp only [Subst.lookup] at firstFresh retractionFresh secondFresh
  rw [source_body_shape]
  apply BoundCalls.case_returns program bindings firstBound state state state _
    (.expression [.expression [.symbol "Some", first], .expression [.symbol "Some", retraction]])
    secondBody _ _ firstCases (Eval.read_cases_encoded firstCases)
  · apply BoundCalls.CorePath.extended
    apply BoundCalls.CorePath.expression_return program bindings state _ _
      (by intro head arguments; simp [firstCall]) rfl
    exact .cons (first_certificate bindings state constants abstraction representation represented carrier
      equalityIdentity absCaptured repCaptured aCaptured)
      (.cons (retraction_certificate bindings state constants abstraction representation represented carrier
        equalityIdentity absCaptured repCaptured rCaptured) .nil)
  · simp [firstCases, firstBound, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, firstFresh, retractionFresh]
  · unfold secondBody
    apply BoundCalls.case_returns program firstBound secondBound state state state secondCall
      (.expression [.symbol "Some", second]) TypeDefinitionPublication.sourceTail _ _ secondCases
      (Eval.read_cases_encoded secondCases)
    · apply BoundCalls.CorePath.extended
      unfold secondCall second secondLaw
      refine Equality.authored_equation_computed_certificate constants firstBound state [] _ _ Ty.bool
        ?_ ?_ equalityIdentity _ _ ?_ ?_
      · simp [DBTerm.inferType, predicateChecked, representationVariable, Ty.function, Ty.destFunction?, TypeOp.function]
      · exact Equality.equality_result_typed [] _ _ represented
          (by simp [abstractionTerm, representationTerm, representationVariable, DBTerm.inferType,
            Ty.function, Ty.destFunction?, TypeOp.function])
          (by simp [representationVariable, DBTerm.inferType])
      · apply application_variable_certificate firstBound state constants predicate _ "predicate" "r"
        · simpa [firstBound, applySubst, Subst.lookup] using predicateCaptured
        · simpa [firstBound, applySubst, Subst.lookup] using rCaptured
      · simpa [firstBound, retraction, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program firstBound state "retraction"
    · simp [secondCases, secondBound, firstBound, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, secondFresh]
    · apply TypeDefinitionPublication.authored_captured_tail_returns operators declarations axioms key
        first second dependencies typeName abstractionName representationName premise cache receipts secondBound state
      · simpa [secondBound, firstBound, applySubst, Subst.lookup] using worldCaptured
      · simpa [secondBound, firstBound, applySubst, Subst.lookup] using keyCaptured
      · simpa [secondBound, firstBound, applySubst, Subst.lookup] using requestCaptured
      · rfl
      · rfl
      · simpa [secondBound, firstBound, applySubst, Subst.lookup] using dependenciesCaptured
      · simpa [secondBound, firstBound, Subst.lookup] using resultFresh
      · exact receiptFresh
      · exact cacheFresh

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionEquations
