import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchemaPrimitives

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxErrors 8

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open WellSorted RestAwareTyping
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

private theorem option_type_equality (left right : Option TypeExpr) :
    (left == right) = decide (encodeOption typeTerm left = encodeOption typeTerm right) := by
  have typeInjective : Function.Injective typeTerm := by
    intro first second same
    simpa only [InferenceCettaWire.AuthoredRule.decodeType?_typeTerm,Option.some.injEq] using
      congrArg InferenceCettaWire.AuthoredRule.decodeType? same
  apply Bool.eq_iff_iff.mpr
  cases left <;> cases right <;>
    simp [encodeOption,typeInjective.eq_iff]

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads library.runtime program)

include agreement in
theorem has_returns (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (pattern : Pattern) :
    ∀ (bound : List TypeExpr) (expected : TypeExpr),
    PureReturns program [] host
      (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
        encoded (freeTerm free),encoded (encodeList typeTerm bound),
        encoded (encodePattern pattern),encoded (typeTerm expected)])
      host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound pattern expected)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro bound expected
      have looked := row_returns program agreement typeTerm host bound index
      simp only [checkSchemaHasType,option_type_equality]
      schema_eval using (agreement) [looked]
  | hfvar name =>
      intro bound expected
      have looked := binding_returns program agreement host name free
      simp only [checkSchemaHasType,option_type_equality]
      schema_eval using (agreement) [looked]
  | happly label arguments children =>
      intro bound expected
      have constructors := constructors_returns_of program agreement host language free bound label arguments expected
        (fun child member type => children child member bound type) language.terms
      schema_eval using (agreement) [constructors] unfolding [checkSchemaHasType]
  | hlambda binder body induction =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          have nested := induction (domain :: bound) codomain
          schema_eval using (agreement) [nested] unfolding [checkSchemaHasType,typeTerm]
      | base sort => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
      | multiBinder type => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
      | collection kind type => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
  | hmultiLambda arity binders body induction =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder type =>
              have extended := extend_returns program agreement host type bound arity
              have nested := induction (List.replicate arity type ++ bound) codomain
              schema_eval using (agreement) [extended,nested] unfolding [checkSchemaHasType,typeTerm]
          | base sort => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
          | arrow first second => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
          | collection kind type => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
      | base sort => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
      | multiBinder type => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
      | collection kind type => schema_eval using (agreement) unfolding [checkSchemaHasType,typeTerm]
  | hsubst body replacement bodyInduction replacementInduction =>
      intro bound expected
      have substitutions := substitutions_returns_of program agreement host language free bound body replacement expected
        (fun domain => bodyInduction (domain :: bound) expected)
        (fun domain => replacementInduction bound domain) language.types
      schema_eval using (agreement) [substitutions] unfolding [checkSchemaHasType]
  | hcollection kind elements rest children =>
      intro bound expected
      have authored := collections_returns_of program agreement host language free bound kind elements rest expected
        (fun child member type => children child member bound type) language.terms
      cases expected with
      | base sort => schema_eval using (agreement) [authored] unfolding [checkSchemaHasType,typeTerm]
      | arrow domain codomain => schema_eval using (agreement) [authored] unfolding [checkSchemaHasType,typeTerm]
      | multiBinder type => schema_eval using (agreement) [authored] unfolding [checkSchemaHasType,typeTerm]
      | collection actual elementType =>
          have elementsChecked := elements_returns_of program agreement host language free bound elementType elements
            (fun child member type => children child member bound type)
          have restChecked := rest_returns program agreement host free kind elementType rest
          have absent : ∀ row : GrammarRule,
              bareCollectionElementType? row kind (.collection actual elementType) = none := by
            intro row
            simp [bareCollectionElementType?]
          have canonical : checkSchemaHasType language (FreeTypeContext.ofList free) bound
              (.collection kind elements rest) (.collection actual elementType) =
              (actual == kind && checkSchemaElements language (FreeTypeContext.ofList free) bound elements elementType &&
                checkRestHasType (FreeTypeContext.ofList free) kind elementType rest) := by
            simp only [checkSchemaHasType,absent]
            rw [show language.terms.any (fun _ : GrammarRule => false) = false from
              List.any_eq_false.mpr (by intro row member; simp), Bool.or_false]
          rw [canonical]
          cases elementsResult : checkSchemaElements language (FreeTypeContext.ofList free) bound elements elementType <;>
            rw [elementsResult] at elementsChecked <;>
            cases restResult : checkRestHasType (FreeTypeContext.ofList free) kind elementType rest <;>
              rw [restResult] at restChecked <;>
              cases actual <;> cases kind <;>
                schema_eval using (agreement) [elementsChecked,restChecked] unfolding
                  [typeTerm,elementsResult,restResult,String.reduceEq]

#print axioms has_returns

/-- The actual native call, with all authored declarations and scope arguments. -/
def schemaCall (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Atom :=
  apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
    encoded (freeTerm free),encoded (encodeList typeTerm bound),
    encoded (encodePattern pattern),encoded (typeTerm expected)]

include agreement in
theorem has_sufficient_fuel (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) :
    ∃ fuel, Eval.run program fuel {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound pattern expected)] [] [] :=
  pure_returns_has_sufficient_fuel program [] host host _ _
    (has_returns program agreement host language free pattern bound expected)

include agreement in
theorem completed_iff (host after : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete after answers input output) ↔
      after = host ∧ answers = [Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound pattern expected)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] host host _ _
    (has_returns program agreement host language free pattern bound expected) after answers input output

include agreement in
theorem completed_true_iff (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) :
    (∃ fuel, Eval.run program fuel {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean true] [] []) ↔
      checkSchemaHasType language (FreeTypeContext.ofList free) bound pattern expected = true := by
  rw [completed_iff program agreement]
  constructor
  · intro ⟨_,answers,_,_⟩
    have same := (List.cons.inj answers).1
    change Atom.grounded (.bool true) = Atom.grounded (.bool
      (checkSchemaHasType language (FreeTypeContext.ofList free) bound pattern expected)) at same
    exact (OSLFCore.GroundedValue.bool.inj (Atom.grounded.inj same)).symm
  · intro accepted
    refine ⟨rfl,?_,rfl,rfl⟩
    rw [accepted]

include agreement in
theorem completed_true_source_typed (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (completed : ∃ fuel, Eval.run program fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
        .complete host [Effects.boolean true] [] []) :
    RestAwareTyping.HasType language (FreeTypeContext.ofList free) bound pattern expected :=
  checkSchemaHasType_sound ((completed_true_iff program agreement host language free bound pattern expected).mp completed)

#print axioms has_sufficient_fuel
#print axioms completed_iff
#print axioms completed_true_iff
#print axioms completed_true_source_typed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema
