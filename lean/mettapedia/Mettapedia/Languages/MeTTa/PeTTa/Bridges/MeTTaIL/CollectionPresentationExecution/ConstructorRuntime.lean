import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorDecision

/-! Constructor readiness in the actual scoped and interpreted runtimes.
Fresh operation names retain the old program. Source typing additionally
requires the authored declaration membership kept by the retained scan. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open WellSorted
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Eval BridgeKit WireKit

def scopedRuntime : SpaceSemantics.Program :=
  PremiseOperationsExecution.RestSchema.scopedRuntime.append source.program

def interpretedRuntime : SpaceSemantics.Program :=
  PremiseOperationsExecution.RestSchema.interpretedRuntime.append source.program

private def rowFields (row : SpaceSemantics.Equation) := (row.head, row.arguments, row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields, Prod.mk.injEq, SpaceSemantics.Equation.mk.injEq] using same

theorem runtime_closed : ProgramClosed proofHeads runtime := by
  constructor
  · decide +kernel
  · intro row member supported
    have all : runtime.equations.all (fun row => !proofHeads row.head || codeWithin proofHeads row.body) = true := by
      decide +kernel
    have selected := List.all_eq_true.mp all row member
    simpa only [supported, Bool.not_true, Bool.false_or] using selected

theorem scoped_runtime_agreement : ProgramAgreementOn proofHeads runtime scopedRuntime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem interpreted_runtime_agreement : ProgramAgreementOn proofHeads runtime interpretedRuntime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

def previousHeads (head : String) : Bool := !head.startsWith "gslt:collection-presentation:view-constructor-"

theorem previous_runtime_agreement :
    ProgramAgreementOn previousHeads PremiseOperationsExecution.RestSchema.interpretedRuntime interpretedRuntime := by
  apply appended_program_agreement
  · intro row member
    have all : source.program.equations.all (fun row => !previousHeads row.head) = true := by decide +kernel
    have fresh := List.all_eq_true.mp all row member
    cases result : previousHeads row.head with
    | false => rfl
    | true => simp [result] at fresh
  · intro name types member
    have all : source.program.declarations.all (fun row => !retainedCallDeclaration previousHeads row) = true := by
      decide +kernel
    have fresh := List.all_eq_true.mp all _ member
    cases result : previousHeads name with
    | false => rfl
    | true => simp [retainedCallDeclaration,result] at fresh

private theorem ready_arguments_raw (index : Nat) (within : index < 11) :
    argumentIsRaw runtime "gslt:collection-presentation:view-constructor-ready" index = true := by
  interval_cases index <;> decide +kernel

variable (program : SpaceSemantics.Program) (agreement : ProgramAgreementOn proofHeads runtime program)

include agreement in
theorem ready_returns_in (host : Effects.State) (language : LanguageDef)
    (free schemaFree : List (String × TypeExpr)) (schemaBound bound : List TypeExpr)
    (expected : TypeExpr) (label : String) (schemas sources : List Pattern) (row : GrammarRule) :
    PureReturns program [] host (readyCall language free schemaFree schemaBound bound expected label schemas sources row)
      host (Effects.boolean (row.label == label && expected == .base row.category && !usesBareCollection? row &&
        checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources row.params &&
        RestAwareTyping.checkSchemaArguments language (FreeTypeContext.ofList schemaFree) schemaBound schemas row.params)) := by
  let values : List Atom :=
    [encoded (PremiseOperationsExecution.RestSchema.sortsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm free),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm schemaFree),
      encoded (encodeList typeTerm schemaBound), encoded (encodeList typeTerm bound),
      encoded (typeTerm expected), encoded (.string label),
      encoded (encodeList encodePattern schemas), encoded (encodeList encodePattern sources),
      encoded (typingDeclarationTerm row)]
  let names := ["sorts", "declarations", "free", "schemaFree", "schemaBound", "bound",
    "expected", "label", "schemas", "sources", "row"]
  let capturedCaller := Library.bind names values
  apply captured_call_in_extension runtime_closed agreement [] capturedCaller host host
    "gslt:collection-presentation:view-constructor-ready" values names _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro index argument selected
    apply Or.inl
    apply ready_arguments_raw index
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    simpa only [values,List.length_cons,List.length_nil] using bounded
  · simp [names,values,capturedCaller,Library.bind,applySubst,Subst.lookup,List.find?]
  · exact ready_returns host language free schemaFree schemaBound bound expected label schemas sources row

include agreement in
theorem retained_ready_returns_in (host : Effects.State) (parameters : Retained.Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) :
    PureReturns program [] host
      (readyCall parameters.language free schemaFree schemaBound focus.bound
        (focus.expected parameters.category) label schemas sources row)
      host (Effects.boolean (Retained.constructorReady parameters schemaBound focus label schemas sources row)) := by
  simpa only [Retained.constructorReady,targetContext,schemaContext] using
    ready_returns_in program agreement host parameters.language free schemaFree schemaBound focus.bound
      (focus.expected parameters.category) label schemas sources row

include agreement in
theorem retained_sufficient_fuel (host : Effects.State) (parameters : Retained.Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) :
    ∃ fuel, Eval.run program fuel
      {state := host, control := .evaluate [] (readyCall parameters.language free schemaFree schemaBound
        focus.bound (focus.expected parameters.category) label schemas sources row)} =
      .complete host [Effects.boolean (Retained.constructorReady parameters schemaBound focus label schemas sources row)] [] [] :=
  pure_returns_has_sufficient_fuel program [] host host _ _
    (retained_ready_returns_in program agreement host parameters free schemaFree targetContext schemaContext
      schemaBound focus label schemas sources row)

include agreement in
theorem retained_completed_iff (host after : Effects.State) (parameters : Retained.Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel
      {state := host, control := .evaluate [] (readyCall parameters.language free schemaFree schemaBound
        focus.bound (focus.expected parameters.category) label schemas sources row)} =
      .complete after answers input output) ↔
      after = host ∧ answers = [Effects.boolean (Retained.constructorReady parameters schemaBound focus label schemas sources row)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] host host _ _
    (retained_ready_returns_in program agreement host parameters free schemaFree targetContext schemaContext
      schemaBound focus label schemas sources row) after answers input output

include agreement in
theorem retained_completed_true_iff (host : Effects.State) (parameters : Retained.Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) :
    (∃ fuel, Eval.run program fuel
      {state := host, control := .evaluate [] (readyCall parameters.language free schemaFree schemaBound
        focus.bound (focus.expected parameters.category) label schemas sources row)} =
      .complete host [Effects.boolean true] [] []) ↔
      Retained.constructorReady parameters schemaBound focus label schemas sources row = true := by
  rw [retained_completed_iff program agreement host host parameters free schemaFree targetContext schemaContext]
  constructor
  · intro ⟨_,answers,_,_⟩
    have same := (List.cons.inj answers).1
    change Atom.grounded (.bool true) = Atom.grounded (.bool
      (Retained.constructorReady parameters schemaBound focus label schemas sources row)) at same
    exact (OSLFCore.GroundedValue.bool.inj (Atom.grounded.inj same)).symm
  · intro accepted
    refine ⟨rfl,?_,rfl,rfl⟩
    rw [accepted]

include agreement in
theorem retained_true_source_typed (host : Effects.State) (parameters : Retained.Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (row : GrammarRule) (member : row ∈ parameters.language.terms)
    (completed : ∃ fuel, Eval.run program fuel
      {state := host, control := .evaluate [] (readyCall parameters.language free schemaFree schemaBound
        focus.bound (focus.expected parameters.category) label schemas sources row)} =
      .complete host [Effects.boolean true] [] []) :
    WellSorted.HasType parameters.language parameters.free focus.bound
      (.apply label sources) (focus.expected parameters.category) ∧
    RestAwareTyping.HasType parameters.language parameters.schemaFree schemaBound
      (.apply label schemas) (focus.expected parameters.category) := by
  have ready := (retained_completed_true_iff program agreement host parameters free schemaFree targetContext
    schemaContext schemaBound focus label schemas sources row).mp completed
  simp only [Retained.constructorReady,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at ready
  obtain ⟨⟨⟨⟨sameLabel,sameType⟩,notBare⟩,targetArguments⟩,schemaArguments⟩ := ready
  have representation : ¬ UsesBareCollection row := by
    intro bare
    have positive := (usesBareCollection?_eq_true_iff row).mpr bare
    simp only [notBare,Bool.false_eq_true] at positive
  have targetTyped := checkArgumentsHaveTypes_sound_of (fun _ _ _ checked => checkHasType_sound checked) targetArguments
  have schemaTyped := RestAwareTyping.checkSchemaArguments_sound_of
    (fun _ _ _ checked => RestAwareTyping.checkSchemaHasType_sound checked) schemaArguments
  constructor
  · simpa only [sameLabel,← sameType] using WellSorted.HasType.constructor member representation targetTyped
  · simpa only [sameLabel,← sameType] using RestAwareTyping.HasType.constructor member representation schemaTyped

#print axioms runtime_closed
#print axioms scoped_runtime_agreement
#print axioms interpreted_runtime_agreement
#print axioms previous_runtime_agreement
#print axioms ready_returns_in
#print axioms retained_ready_returns_in
#print axioms retained_sufficient_fuel
#print axioms retained_completed_iff
#print axioms retained_completed_true_iff
#print axioms retained_true_source_typed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping
