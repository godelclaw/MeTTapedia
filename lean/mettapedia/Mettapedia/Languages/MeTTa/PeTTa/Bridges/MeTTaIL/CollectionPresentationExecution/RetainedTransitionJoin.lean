import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperations

/-! Composing the proved task expansions with the retained agenda/account
commit. These are cases of the existing producer step, using ordinary let
and the same native operations. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionJoin

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Retained RetainedWire
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

abbrev runtime := RetainedOperations.runtime

private def rowFields (row : SpaceSemantics.Equation) := (row.head,row.arguments,row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields,Prod.mk.injEq,SpaceSemantics.Equation.mk.injEq] using same

theorem scan_agreement :
    ProgramAgreementOn RetainedConstructors.proofHeads RetainedConstructors.proofLibrary.runtime runtime := by
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

def previousHeads (head : String) : Bool :=
  !(RetainedOperations.source.program.equations.map (·.head)).contains head

theorem previous_runtime_agreement :
    ProgramAgreementOn previousHeads RetainedConstructors.runtime runtime := by
  apply appended_program_agreement
  · intro row member
    have all : RetainedOperations.source.program.equations.all (fun row => !previousHeads row.head) = true := by
      decide +kernel
    have fresh := List.all_eq_true.mp all row member
    cases result : previousHeads row.head with
    | false => rfl
    | true => simp [result] at fresh
  · intro name types member
    have all : RetainedOperations.source.program.declarations.all
        (fun row => !retainedCallDeclaration previousHeads row) = true := by decide +kernel
    have fresh := List.all_eq_true.mp all _ member
    cases result : previousHeads name with
    | false => rfl
    | true => simp [retainedCallDeclaration,result] at fresh

def commitCall (pending : List Task) (answers : List Spelling) (expansionCode : Atom) : Atom :=
  apply "let" [.var "producerChange",expansionCode,
    apply "gslt:collection-presentation:view-commit"
      [encoded (encodeList taskTerm pending),encoded (encodeList spellingTerm answers),.var "producerChange"]]

/-- A source expansion proof composes with the actual commit operation. The
conclusion includes the complete old agenda and ordered answer prefix. -/
theorem commit_computes_of_expansion (host : Effects.State) (parameters : Parameters)
    (task : Task) (pending : List Task) (answers : List Spelling) (code : Atom)
    (expanded : PureReturns runtime [] host code host (encoded (expansionTerm (expand parameters task)))) :
    PureReturns runtime [] host (commitCall pending answers code) host
      (encoded (stateTerm (tick parameters ⟨task :: pending,answers⟩))) := by
  have committed := RetainedOperations.commit_returns runtime RetainedOperations.runtime_agreement host
    pending (expand parameters task).1 answers (expand parameters task).2
  unfold commitCall
  refine pure_let_returns runtime [] host "producerChange" code
    (encoded (expansionTerm (expand parameters task))) _ _ rfl expanded ?_
  metta_capture_agreed RetainedOperations.runtime_agreement from committed

theorem returned_step_returns (host : Effects.State) (parameters : Parameters)
    {kind : Kind} (value : Value kind) (next : Continuation kind)
    (pending : List Task) (answers : List Spelling) :
    PureReturns runtime [] host
      (commitCall pending answers (apply "gslt:collection-presentation:view-return"
        [encoded (valueTerm value),encoded (continuationTerm next)])) host
      (encoded (stateTerm (tick parameters ⟨.returned value next :: pending,answers⟩))) :=
  commit_computes_of_expansion host parameters _ pending answers _
    (RetainedOperations.return_returns runtime RetainedOperations.runtime_agreement host parameters value next)

theorem children_step_returns (host : Effects.State) (parameters : Parameters)
    (query : Query .children) (next : Continuation .children)
    (pending : List Task) (answers : List Spelling) :
    PureReturns runtime [] host
      (commitCall pending answers (apply "gslt:collection-presentation:view-children"
        [encoded (queryTerm query),encoded (continuationTerm next)])) host
      (encoded (stateTerm (tick parameters ⟨.request query next :: pending,answers⟩))) :=
  commit_computes_of_expansion host parameters _ pending answers _
    (RetainedOperations.children_returns runtime RetainedOperations.runtime_agreement host parameters query next)

theorem constructors_step_returns (host : Effects.State) (parameters : Parameters)
    (free schemaFree : List (String × TypeExpr))
    (targetContext : parameters.free = WellSorted.FreeTypeContext.ofList free)
    (schemaContext : parameters.schemaFree = WellSorted.FreeTypeContext.ofList schemaFree)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus) (label : String)
    (schemas sources : List Pattern) (outer : Option OneHoleContext) (ordinal : Nat)
    (remaining : List GrammarRule) (next : Continuation .spelling)
    (pending : List Task) (answers : List Spelling) :
    PureReturns runtime [] host
      (commitCall pending answers (RetainedConstructors.scanCall parameters.language free schemaFree parameters.category
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next))) host
      (encoded (stateTerm (tick parameters
        ⟨.constructors schemaBound path focus label schemas sources outer ordinal remaining next :: pending,answers⟩))) :=
  commit_computes_of_expansion host parameters _ pending answers _
    (RetainedConstructors.scan_returns runtime scan_agreement constructor_agreement host parameters free schemaFree
      targetContext schemaContext schemaBound path focus label schemas sources outer ordinal remaining next)

#print axioms scan_agreement
#print axioms constructor_agreement
#print axioms previous_runtime_agreement
#print axioms commit_computes_of_expansion
#print axioms returned_step_returns
#print axioms children_step_returns
#print axioms constructors_step_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionJoin
