import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorReadiness

/-! Constructor header checks compose with target/schema argument checking.
The observed Boolean is the actual retained producer's readiness predicate. -/

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
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Eval BridgeKit WireKit

private theorem beq_as_decide {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (first second : α) : (first == second) = decide (first = second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]

def readyCall (language : LanguageDef) (free schemaFree : List (String × TypeExpr))
    (schemaBound bound : List TypeExpr) (expected : TypeExpr) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) : Atom :=
  apply "gslt:collection-presentation:view-constructor-ready"
    [encoded (PremiseOperationsExecution.RestSchema.sortsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm free),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm schemaFree),
      encoded (encodeList typeTerm schemaBound), encoded (encodeList typeTerm bound),
      encoded (typeTerm expected), encoded (.string label),
      encoded (encodeList encodePattern schemas), encoded (encodeList encodePattern sources),
      encoded (typingDeclarationTerm row)]

syntax "header_eval" " [" term,* "]" " at_base " "(" term "," term ")"
  " unfolding" " [" term,* "]" : tactic
macro_rules
  | `(tactic| header_eval [$facts,*] at_base($expected,$category) unfolding [$extra,*]) => do
    let simps ← extra.getElems.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (ready_eval [$facts,*] unfolding [$extra,*]
       all_goals
         apply pure_if_returns _ _ _ _ (decide ($expected = TypeExpr.base $category)) _ _ _
         · apply PremiseOperationsExecution.RestSchema.base_comparison_returns runtime
           all_goals simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
             Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
             Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, Library.bind,
             typeTerm,encoded,CettaWireAtom.encode,CettaWireAtom.encodeMany,$simps,*]
         · simp only [decide_true,decide_false,↓reduceIte,$simps,*]
           metta_eval [$facts,*] with proof_checked in proof_agreement unfolding
             [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
              Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
              Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, Library.bind,
              encodeList,encodeOption,parameterTerm,typingDeclarationTerm,representationTerm,
              PremiseOperationsExecution.RestSchema.freeTerm,
              PremiseOperationsExecution.RestSchema.declarationsTerm,
              PremiseOperationsExecution.RestSchema.sortsTerm,typeTerm,
              InferenceCettaWire.encodeList,$extra,*]))

theorem ready_returns (host : Effects.State) (language : LanguageDef)
    (free schemaFree : List (String × TypeExpr)) (schemaBound bound : List TypeExpr)
    (expected : TypeExpr) (label : String) (schemas sources : List Pattern) (row : GrammarRule) :
    PureReturns runtime [] host (readyCall language free schemaFree schemaBound bound expected label schemas sources row)
      host (Effects.boolean (row.label == label && expected == .base row.category && !usesBareCollection? row &&
        checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources row.params &&
        RestAwareTyping.checkSchemaArguments language (FreeTypeContext.ofList schemaFree) schemaBound schemas row.params)) := by
  have parameters := parameters_returns host language free schemaFree schemaBound bound schemas sources row
  simp only [Bool.and_assoc] at parameters
  rcases row with ⟨actual,category,arguments,syntaxRows,evaluation,algebra,representation⟩
  cases representation <;>
    by_cases labelSame : actual = label <;>
      by_cases typeSame : expected = .base category <;>
        header_eval [parameters] at_base(expected,category)
          unfolding [readyCall,representationTerm,beq_as_decide,labelSame,typeSame,Bool.and_assoc]

/-- The original and virtual-group focuses retain their respective expected
types and binder contexts when handed to the native readiness operation. -/
theorem retained_ready_returns (host : Effects.State) (parameters : Retained.Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) :
    PureReturns runtime [] host
      (readyCall parameters.language free schemaFree schemaBound focus.bound
        (focus.expected parameters.category) label schemas sources row)
      host (Effects.boolean (Retained.constructorReady parameters schemaBound focus label schemas sources row)) := by
  simpa only [Retained.constructorReady,targetContext,schemaContext] using
    ready_returns host parameters.language free schemaFree schemaBound focus.bound
      (focus.expected parameters.category) label schemas sources row

#print axioms ready_returns
#print axioms retained_ready_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping
