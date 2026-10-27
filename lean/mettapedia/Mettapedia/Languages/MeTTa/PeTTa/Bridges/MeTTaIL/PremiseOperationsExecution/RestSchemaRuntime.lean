import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram

/-! Rest-aware schema typing in the shared scoped and interpreted runtimes.
The added source has fresh heads. Actual ordered equation/declaration checks
discharge the primitive program agreement used by the recursive proof. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit

/-- The existing scoped source followed by the rest-aware operation family. -/
def scopedRuntime : SpaceSemantics.Program := RuleExecutionProgram.scopedProgram.append source.program

/-- The existing interpreted source followed by the same operation family. -/
def interpretedRuntime : SpaceSemantics.Program :=
  RuleExecutionProgram.interpretedPremiseProgram.append source.program

private def rowFields (row : SpaceSemantics.Equation) := (row.head, row.arguments, row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields, Prod.mk.injEq, SpaceSemantics.Equation.mk.injEq] using same

theorem scoped_runtime_agreement : ProgramAgreementOn proofHeads library.runtime scopedRuntime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem interpreted_runtime_agreement : ProgramAgreementOn proofHeads library.runtime interpretedRuntime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

def previousHeads (head : String) : Bool := !head.startsWith "gslt:premise:schema-"

private theorem new_equations_fresh :
    source.program.equations.all (fun row => !previousHeads row.head) = true := by decide +kernel

private theorem new_declarations_fresh :
    source.program.declarations.all (fun row => !retainedCallDeclaration previousHeads row) = true := by
  decide +kernel

/-- Existing operation names retain their dispatch, argument demand and
ordered bodies when the schema family is loaded. -/
theorem previous_runtime_agreement :
    ProgramAgreementOn previousHeads RuleExecutionProgram.interpretedPremiseProgram interpretedRuntime := by
  apply appended_program_agreement
  · intro row member
    have fresh := List.all_eq_true.mp new_equations_fresh row member
    cases result : previousHeads row.head with
    | false => rfl
    | true => simp [result] at fresh
  · intro name types member
    have fresh := List.all_eq_true.mp new_declarations_fresh _ member
    cases result : previousHeads name with
    | false => rfl
    | true => simp [retainedCallDeclaration, result] at fresh

theorem interpreted_has_returns (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) :
    PureReturns interpretedRuntime [] host (schemaCall language free bound pattern expected) host
      (Effects.boolean (RestAwareTyping.checkSchemaHasType language
        (WellSorted.FreeTypeContext.ofList free) bound pattern expected)) :=
  has_returns interpretedRuntime interpreted_runtime_agreement host language free pattern bound expected

theorem interpreted_has_sufficient_fuel (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) :
    ∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean (RestAwareTyping.checkSchemaHasType language
        (WellSorted.FreeTypeContext.ofList free) bound pattern expected)] [] [] :=
  has_sufficient_fuel interpretedRuntime interpreted_runtime_agreement host language free bound pattern expected

theorem interpreted_completed_iff (host after : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete after answers input output) ↔
      after = host ∧ answers = [Effects.boolean (RestAwareTyping.checkSchemaHasType language
        (WellSorted.FreeTypeContext.ofList free) bound pattern expected)] ∧ input = [] ∧ output = [] :=
  completed_iff interpretedRuntime interpreted_runtime_agreement host after language free bound pattern expected
    answers input output

theorem interpreted_true_iff (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) :
    (∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean true] [] []) ↔
      RestAwareTyping.checkSchemaHasType language (WellSorted.FreeTypeContext.ofList free) bound pattern expected = true :=
  completed_true_iff interpretedRuntime interpreted_runtime_agreement host language free bound pattern expected

theorem interpreted_true_source_typed (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (completed : ∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean true] [] []) :
    RestAwareTyping.HasType language (WellSorted.FreeTypeContext.ofList free) bound pattern expected :=
  completed_true_source_typed interpretedRuntime interpreted_runtime_agreement host language free bound pattern expected completed

#print axioms scoped_runtime_agreement
#print axioms interpreted_runtime_agreement
#print axioms previous_runtime_agreement
#print axioms interpreted_has_returns
#print axioms interpreted_has_sufficient_fuel
#print axioms interpreted_completed_iff
#print axioms interpreted_true_iff
#print axioms interpreted_true_source_typed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema
