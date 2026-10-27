import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorRuntime
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedWire

/-! One actual retained declaration scan: readiness creates a child query and
retains the remaining scan with its next ordinal and complete continuation. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxErrors 8

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedConstructors

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Retained RetainedWire
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_constructor_scan.metta"
    sha256 "e7a93e639248b11201ad8562941d116a5953582fdb36417e5166a27c6e33542c"

def proofLibrary : Library :=
  ⟨ConstructorTyping.proofLibrary.runtime, source.program, ["gslt:collection-presentation:view-scan-"]⟩

def runtime : SpaceSemantics.Program := ConstructorTyping.interpretedRuntime.append source.program

def proofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (proofLibrary.runtime.equations.map (·.head)).contains head

theorem checked : proofLibrary.check = true := by decide +kernel

private def rowFields (row : SpaceSemantics.Equation) := (row.head,row.arguments,row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields,Prod.mk.injEq,SpaceSemantics.Equation.mk.injEq] using same

theorem proof_agreement : ProgramAgreementOn proofHeads proofLibrary.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem constructor_agreement :
    ProgramAgreementOn ConstructorTyping.proofHeads ConstructorTyping.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

def previousHeads (head : String) : Bool := !head.startsWith "gslt:collection-presentation:view-scan-"

theorem previous_runtime_agreement :
    ProgramAgreementOn previousHeads ConstructorTyping.interpretedRuntime runtime := by
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

def rowProjectionTerm (row : GrammarRule) : Term :=
  .application "ConstructorScanRow" [typingDeclarationTerm row,encodeList parameterTerm row.params]

def focusTypingTerm (category : String) (focus : Focus) : Term :=
  .application "ViewFocusTyping" [encodeList typeTerm focus.bound,typeTerm (focus.expected category)]

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads proofLibrary.runtime program)

syntax "scan_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| scan_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in checked using $agreement; metta_eval [$facts,*] with checked in $agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?,
        encodeList,encodeOption,parameterTerm,typingDeclarationTerm,
        rowProjectionTerm,focusTypingTerm,focusTerm,taskTerm,frameTerm,queryTerm,continuationTerm,
        expansionTerm,Focus.bound,Focus.expected,
        ModuleAlgebra.NativeAuthoring.Wire.grammarRule,
        InferenceCettaWire.encodePattern,InferenceCettaWire.encodePatterns,
        InferenceCettaWire.encodeList,InferenceCettaWire.encodePatterns_eq_encodeList,$extra,*]))

include agreement in
@[metta_head "gslt:collection-presentation:view-scan-row"]
theorem row_returns (host : Effects.State) (row : GrammarRule) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-scan-row" [encoded (ModuleAlgebra.NativeAuthoring.Wire.grammarRule row)])
      host (encoded (rowProjectionTerm row)) := by
  rcases row with ⟨label,category,parameters,syntaxRows,evaluation,algebra,representation⟩
  cases representation <;> scan_eval using (agreement)

include agreement in
@[metta_head "gslt:collection-presentation:view-scan-focus"]
theorem focus_returns (host : Effects.State) (category : String) (focus : Focus) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-scan-focus" [encoded (.string category),encoded (focusTerm focus)])
      host (encoded (focusTypingTerm category focus)) := by
  cases focus <;> scan_eval using (agreement)

def scanCall (language : LanguageDef) (free schemaFree : List (String × TypeExpr))
    (category : String) (task : Task) : Atom :=
  apply "gslt:collection-presentation:view-scan-constructors"
    [encoded (PremiseOperationsExecution.RestSchema.sortsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm free),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm schemaFree),
      encoded (.string category),encoded (taskTerm task)]

include agreement in
theorem scan_returns
    (constructorAgreement : ProgramAgreementOn ConstructorTyping.proofHeads ConstructorTyping.runtime program)
    (host : Effects.State) (parameters : Parameters) (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = WellSorted.FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = WellSorted.FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (outer : Option OneHoleContext) (ordinal : Nat)
    (remaining : List GrammarRule) (next : Continuation .spelling) :
    PureReturns program [] host
      (scanCall parameters.language free schemaFree parameters.category
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next))
      host (encoded (expansionTerm (expand parameters
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)))) := by
  cases remaining with
  | nil => scan_eval using (agreement) unfolding [scanCall,expand]
  | cons row later =>
      have projected := row_returns program agreement host row
      have typedFocus := focus_returns program agreement host parameters.category focus
      have ready := ConstructorTyping.retained_ready_returns_in program constructorAgreement host parameters
        free schemaFree targetContext schemaContext schemaBound focus label schemas sources row
      cases result : constructorReady parameters schemaBound focus label schemas sources row <;>
        rw [result] at ready <;>
        scan_eval using (agreement) [projected,typedFocus,ready]
          unfolding [scanCall,expand,result,ConstructorTyping.readyCall,
            PremiseOperationsExecution.RestSchema.sortsTerm,
            PremiseOperationsExecution.RestSchema.declarationsTerm,
            PremiseOperationsExecution.RestSchema.freeTerm]

theorem native_scan_returns (host : Effects.State) (parameters : Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = WellSorted.FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = WellSorted.FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (outer : Option OneHoleContext) (ordinal : Nat)
    (remaining : List GrammarRule) (next : Continuation .spelling) :
    PureReturns runtime [] host
      (scanCall parameters.language free schemaFree parameters.category
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next))
      host (encoded (expansionTerm (expand parameters
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)))) :=
  scan_returns runtime proof_agreement constructor_agreement host parameters free schemaFree
    targetContext schemaContext schemaBound path focus label schemas sources outer ordinal remaining next

theorem native_scan_sufficient_fuel (host : Effects.State) (parameters : Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = WellSorted.FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = WellSorted.FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (outer : Option OneHoleContext) (ordinal : Nat)
    (remaining : List GrammarRule) (next : Continuation .spelling) :
    ∃ fuel, Eval.run runtime fuel
      {state := host, control := .evaluate [] (scanCall parameters.language free schemaFree parameters.category
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next))} =
      .complete host [encoded (expansionTerm (expand parameters
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)))] [] [] :=
  pure_returns_has_sufficient_fuel runtime [] host host _ _
    (native_scan_returns host parameters free schemaFree targetContext schemaContext
      schemaBound path focus label schemas sources outer ordinal remaining next)

theorem native_scan_completed_iff (host after : Effects.State) (parameters : Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = WellSorted.FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = WellSorted.FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (outer : Option OneHoleContext) (ordinal : Nat)
    (remaining : List GrammarRule) (next : Continuation .spelling) (answers input output : List Atom) :
    (∃ fuel, Eval.run runtime fuel
      {state := host, control := .evaluate [] (scanCall parameters.language free schemaFree parameters.category
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next))} =
      .complete after answers input output) ↔
      after = host ∧ answers = [encoded (expansionTerm (expand parameters
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] host host _ _
    (native_scan_returns host parameters free schemaFree targetContext schemaContext
      schemaBound path focus label schemas sources outer ordinal remaining next) after answers input output

#print axioms checked
#print axioms proof_agreement
#print axioms constructor_agreement
#print axioms previous_runtime_agreement
#print axioms row_returns
#print axioms focus_returns
#print axioms scan_returns
#print axioms native_scan_returns
#print axioms native_scan_sufficient_fuel
#print axioms native_scan_completed_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedConstructors
