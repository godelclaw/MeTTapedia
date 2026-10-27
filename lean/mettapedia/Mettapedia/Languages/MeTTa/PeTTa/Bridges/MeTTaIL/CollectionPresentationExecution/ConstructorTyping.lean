import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchemaRuntime
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution

/-! Native readiness of a retained presentation's constructor row. Each side
uses its actual scope and free context. Declaration membership and frame
construction remain the responsibility of the retained declaration scan. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval BridgeKit WireKit
open scoped ProgramQuotation


def source : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_constructor_typing.metta"
    sha256 "08d0375fddd10f90591d1a5bf8dccb7869582d274907063ec9fe88608fa3160b"

def base : SpaceSemantics.Program :=
  PremiseOperationsExecution.program.append PremiseOperationsExecution.RestSchema.source.program

def library : Library := ⟨base, source.program, ["gslt:collection-presentation:view-constructor-"]⟩

abbrev runtime : SpaceSemantics.Program := library.runtime

theorem checked : library.check = true := by decide +kernel

private def rowFields (row : SpaceSemantics.Equation) := (row.head, row.arguments, row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields, Prod.mk.injEq, SpaceSemantics.Equation.mk.injEq] using same

theorem schema_agreement :
    ProgramAgreementOn PremiseOperationsExecution.RestSchema.proofHeads
      PremiseOperationsExecution.RestSchema.library.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

def groundHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || head.startsWith "gslt:premise:type-" ||
    ["gslt:automata:binding", "gslt:rule:row-at", "gslt:premise:parameter-type",
      "gslt:premise:parameter-representation"].contains head

theorem ground_closed : ProgramClosed groundHeads PremiseOperationsExecution.program := by
  constructor
  · decide +kernel
  · intro row member supported
    have all : PremiseOperationsExecution.program.equations.all (fun row =>
        !groundHeads row.head || codeWithin groundHeads row.body) = true := by decide +kernel
    have selected := List.all_eq_true.mp all row member
    simpa only [supported, Bool.not_true, Bool.false_or] using selected

theorem ground_agreement :
    ProgramAgreementOn groundHeads PremiseOperationsExecution.program runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel


private def groundFragment : SpaceSemantics.Program where
  equations := PremiseOperationsExecution.program.equations.filter (fun row => groundHeads row.head)
  declarations := PremiseOperationsExecution.program.declarations.filter (retainedCallDeclaration groundHeads)

def proofLibrary : Library :=
  ⟨{equations := [], declarations := []},
    groundFragment.append (PremiseOperationsExecution.RestSchema.source.program.append source.program), ["gslt:"]⟩

def proofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (proofLibrary.runtime.equations.map (·.head)).contains head

theorem proof_checked : proofLibrary.check = true := by decide +kernel

theorem proof_agreement : ProgramAgreementOn proofHeads proofLibrary.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

private theorem freeContextTerm_eq (free : List (String × TypeExpr)) :
    PremiseOperationsExecution.DeclarationTyping.freeContextTerm free =
      PremiseOperationsExecution.RestSchema.freeTerm free := by
  simp only [PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
    MatchAutomataBindingExecution.payloadBindingsTerm, CettaWire.encodeList_map,
    PremiseOperationsExecution.RestSchema.freeTerm, Function.comp_def,
    MatchAutomataBindingExecution.payloadBindingTerm]

private theorem ground_arguments_raw (index : Nat) (within : index < 5) :
    argumentIsRaw PremiseOperationsExecution.program "gslt:premise:type-arguments" index = true := by
  interval_cases index <;> decide +kernel

theorem ground_arguments_returns (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (sources : List Pattern) (parameters : List TermParam) :
    PureReturns runtime [] host
      (apply "gslt:premise:type-arguments"
        [encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.freeTerm free), encoded (encodeList typeTerm bound),
          encoded (encodeList encodePattern sources), encoded (encodeList parameterTerm parameters)])
      host (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources parameters)) := by
  let values : List Atom :=
    [encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
      encoded (PremiseOperationsExecution.RestSchema.freeTerm free), encoded (encodeList typeTerm bound),
      encoded (encodeList encodePattern sources), encoded (encodeList parameterTerm parameters)]
  let names := ["nativeDeclarations", "nativeFree", "nativeBound", "nativeSources", "nativeParameters"]
  let capturedCaller := Library.bind names values
  have previous : PureReturns PremiseOperationsExecution.program [] host
      (apply "gslt:premise:type-arguments" values) host
      (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources parameters)) := by
    have old := PremiseOperationsExecution.DeclarationTyping.check_arguments_have_types_returns
      language free bound sources parameters host
    change PureReturns PremiseOperationsExecution.program [] host
      (apply "gslt:premise:type-arguments"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
          encoded (encodeList typeTerm bound), encoded (InferenceCettaWire.encodePatterns sources),
          encoded (encodeList parameterTerm parameters)]) host
      (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources parameters)) at old
    simpa only [values, PremiseOperationsExecution.RestSchema.declarationsTerm,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm, freeContextTerm_eq,
      InferenceCettaWire.encodePatterns_eq_encodeList] using old
  apply captured_call_in_extension ground_closed ground_agreement [] capturedCaller host host
    "gslt:premise:type-arguments" values names _ (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro index argument selected
    apply Or.inl
    apply ground_arguments_raw index
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    simpa only [values, List.length_cons, List.length_nil] using bounded
  · simp [names, values, capturedCaller, Library.bind, applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
  · exact previous

theorem schema_arguments_returns (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (schemas : List Pattern) (parameters : List TermParam) :
    PureReturns runtime [] host
      (apply "gslt:premise:schema-arguments"
        [encoded (PremiseOperationsExecution.RestSchema.sortsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.freeTerm free), encoded (encodeList typeTerm bound),
          encoded (encodeList encodePattern schemas), encoded (encodeList parameterTerm parameters)])
      host (Effects.boolean (RestAwareTyping.checkSchemaArguments language (FreeTypeContext.ofList free) bound schemas parameters)) :=
  PremiseOperationsExecution.RestSchema.arguments_returns_of runtime schema_agreement host language free bound schemas parameters
    (fun child _ expected => PremiseOperationsExecution.RestSchema.has_returns
      runtime schema_agreement host language free child bound expected)

syntax "ctor_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| ctor_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in proof_checked using proof_agreement; metta_eval [$facts,*] with proof_checked in proof_agreement unfolding
        [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          PremiseOperationsExecution.RestSchema.sortsTerm,
          PremiseOperationsExecution.RestSchema.declarationsTerm,
          PremiseOperationsExecution.RestSchema.freeTerm,
          encodeList, encodeOption, parameterTerm, typeTerm,
          InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

theorem arguments_returns (host : Effects.State) (language : LanguageDef)
    (free schemaFree : List (String × TypeExpr)) (schemaBound bound : List TypeExpr)
    (schemas sources : List Pattern) (parameters : List TermParam) :
    PureReturns runtime [] host
      (apply "gslt:collection-presentation:view-constructor-arguments"
        [encoded (PremiseOperationsExecution.RestSchema.sortsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.declarationsTerm language),
          encoded (PremiseOperationsExecution.RestSchema.freeTerm free),
          encoded (PremiseOperationsExecution.RestSchema.freeTerm schemaFree),
          encoded (encodeList typeTerm schemaBound), encoded (encodeList typeTerm bound),
          encoded (encodeList encodePattern schemas), encoded (encodeList encodePattern sources),
          encoded (encodeList parameterTerm parameters)])
      host (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources parameters &&
        RestAwareTyping.checkSchemaArguments language (FreeTypeContext.ofList schemaFree) schemaBound schemas parameters)) := by
  have ground := ground_arguments_returns host language free bound sources parameters
  have schema := schema_arguments_returns host language schemaFree schemaBound schemas parameters
  cases groundResult : checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound sources parameters <;>
    rw [groundResult] at ground <;>
    cases schemaResult : RestAwareTyping.checkSchemaArguments language (FreeTypeContext.ofList schemaFree) schemaBound schemas parameters <;>
      rw [schemaResult] at schema <;>
      ctor_eval [ground, schema] unfolding [groundResult, schemaResult]

#print axioms proof_checked
#print axioms proof_agreement
#print axioms ground_arguments_returns
#print axioms schema_arguments_returns
#print axioms arguments_returns

#print axioms checked
#print axioms schema_agreement
#print axioms ground_closed
#print axioms ground_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping
