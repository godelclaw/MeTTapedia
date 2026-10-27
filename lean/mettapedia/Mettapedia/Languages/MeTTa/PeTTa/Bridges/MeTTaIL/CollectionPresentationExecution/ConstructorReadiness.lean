import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping
import Mettapedia.GSLT.LanguageDef.BagEquationDecision

/-! The native constructor predicate computes the retained producer's row
readiness test. Membership and declaration ordinals stay in the producer's
scan; this test does not establish formation or equation admissibility. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxErrors 6

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open WellSorted
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern)
open Eval BridgeKit WireKit

syntax "ready_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| ready_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in proof_checked using proof_agreement; metta_eval [$facts,*] with proof_checked in proof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        PremiseOperationsExecution.RestSchema.sortsTerm,
        PremiseOperationsExecution.RestSchema.declarationsTerm,
        PremiseOperationsExecution.RestSchema.freeTerm,
        PremiseOperationsExecution.RestSchema.nil_matches_encoded_list,
        PremiseOperationsExecution.RestSchema.symbol_matches_application,
        encodeList, encodeOption, parameterTerm, typingDeclarationTerm, typeTerm,
        InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

def representationTerm : CollectionRepresentation → Term
  | .bare => .symbol "ConstructorBare"
  | .wrapped => .symbol "ConstructorWrapped"

theorem parameters_returns (host : Effects.State) (language : LanguageDef)
    (free schemaFree : List (String × TypeExpr)) (schemaBound bound : List TypeExpr)
    (schemas sources : List Pattern) (row : GrammarRule) :
    PureReturns runtime [] host
      (apply "gslt:collection-presentation:view-constructor-parameters"
        [encoded (PremiseOperationsExecution.RestSchema.sortsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.freeTerm free),
          encoded (PremiseOperationsExecution.RestSchema.freeTerm schemaFree),
          encoded (encodeList typeTerm schemaBound), encoded (encodeList typeTerm bound),
          encoded (encodeList encodePattern schemas), encoded (encodeList encodePattern sources),
          encoded (encodeList parameterTerm row.params), encoded (representationTerm row.collectionRepresentation)])
      host (Effects.boolean (!usesBareCollection? row &&
        checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources row.params &&
        RestAwareTyping.checkSchemaArguments language (FreeTypeContext.ofList schemaFree) schemaBound schemas row.params)) := by
  have arguments := arguments_returns host language free schemaFree schemaBound bound schemas sources row.params
  rcases row with ⟨actual,category,parameters,syntaxRows,evaluation,algebra,representation⟩
  cases representation with
  | wrapped =>
      ready_eval [arguments] unfolding [representationTerm,usesBareCollection?,GrammarRule.bareParams,Bool.and_assoc]
  | bare =>
      cases parameters with
      | nil =>
          ready_eval [arguments] unfolding [representationTerm,usesBareCollection?,GrammarRule.bareParams,Bool.and_assoc]
      | cons parameter later =>
          cases later with
          | cons second rest =>
              have ordinary : usesBareCollection?
                  (⟨actual,category,parameter :: second :: rest,syntaxRows,evaluation,algebra,.bare⟩ : GrammarRule) = false := by
                cases parameter with
                | simple name type => cases type <;> rfl
                | abstractionNamed binder name type => rfl
                | multiAbstractionNamed binders name type => rfl
              simp only [ordinary,Bool.not_false,Bool.true_and]
              ready_eval [arguments] unfolding [representationTerm,Bool.and_assoc]
          | nil =>
              cases parameter with
              | simple name type =>
                  cases type <;>
                    ready_eval [arguments] unfolding [representationTerm,usesBareCollection?,GrammarRule.bareParams,Bool.and_assoc]
              | abstractionNamed binder name type =>
                  ready_eval [arguments] unfolding [representationTerm,usesBareCollection?,GrammarRule.bareParams,Bool.and_assoc]
              | multiAbstractionNamed binders name type =>
                  ready_eval [arguments] unfolding [representationTerm,usesBareCollection?,GrammarRule.bareParams,Bool.and_assoc]

#print axioms parameters_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping
