import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance

/-! Native construction of allocation child requests. The caller supplies
ordered residuals; normalization and ordering are separate obligations. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxErrors 8

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildren

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained RetainedWire
open InferenceCettaWire.AuthoredRule (typeTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_allocation_children.metta"
    sha256 "43c5415f0ea012f4bc0b1bbbbc1e83d36526cb400ff34f5088c01249dc3f4465"

private def appendSource : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel)]

def library : Library :=
  ⟨{equations := [],declarations := []},
    (appendSource.append RetainedConstructors.proofLibrary.runtime).append source.program, ["gslt:"]⟩

def runtime : SpaceSemantics.Program := AllocationAdvance.runtime.append source.program

theorem checked : library.check = true := by decide +kernel

def proofHeads (head : String) : Bool :=
  RetainedConstructors.proofHeads head || head == "gslt:automata:append" ||
    head.startsWith "gslt:collection-presentation:view-allocation-child"

private def rowFields (row : SpaceSemantics.Equation) := (row.head,row.arguments,row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields,Prod.mk.injEq,SpaceSemantics.Equation.mk.injEq] using same

theorem focus_agreement :
    ProgramAgreementOn RetainedConstructors.proofHeads RetainedConstructors.proofLibrary.runtime
      library.runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem runtime_agreement : ProgramAgreementOn proofHeads library.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem focus_within (head : String) (supported : RetainedConstructors.proofHeads head = true) :
    proofHeads head = true := by simp [proofHeads,supported]

def ordered (allocation : List (List SourceOccurrence) × List SourceOccurrence) :
    List (List SourceOccurrence) × List SourceOccurrence :=
  (allocation.1,sortOccurrences allocation.2)

def call (head : String) (category : String) (schemaBound : List TypeExpr) (path : List Nat)
    (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (next : Continuation .spelling) (allocations : Term) : Atom :=
  apply head [encoded (.string category),encoded (encodeList typeTerm schemaBound),
    encoded (encodeList .natural path),encoded (focusTerm focus),encoded (encodeList encodePattern schemas),
    encoded (InferenceCettaWire.encodeRest rest),encoded (continuationTerm next),encoded allocations]

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads library.runtime program)

syntax "allocation_child_eval" " using " "(" term ")" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| allocation_child_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in checked using $agreement; metta_eval [$facts,*] with checked in $agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        call,ordered,allocationTasks,RetainedConstructors.focusTypingTerm,
        encodeList,encodeOption,taskTerm,queryTerm,continuationTerm,frameTerm,allocationTerm,
        InferenceCettaWire.encodeRest,RetainedOperations.nil_matches_encoded_list,$extra,*]))

include agreement in
@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ first second : List α,
    PureReturns program [] host
      (apply "gslt:automata:append" [encoded (encodeList element first),encoded (encodeList element second)])
      host (encoded (encodeList element (first ++ second)))
  | [],second => by allocation_child_eval using (agreement)
  | first :: later,second => by
      have following := append_returns element host later second
      allocation_child_eval using (agreement) [following]

include agreement in
/-- The native builder constructs exactly the existing producer's child
request from a caller-ordered allocation, including the complete parent. -/
@[metta_head "gslt:collection-presentation:view-allocation-child"]
theorem child_returns (host : Effects.State) (category : String) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (next : Continuation .spelling)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) :
    PureReturns program [] host
      (call "gslt:collection-presentation:view-allocation-child" category schemaBound path focus schemas rest next
        (allocationTerm (ordered (groups,residual)))) host
      (encoded (encodeList taskTerm (allocationTasks schemaBound path focus schemas rest next (groups,residual)))) := by
  have projected := RetainedConstructors.focus_returns program
    (agreement_trans focus_agreement (agreement_mono focus_within agreement)) host category focus
  cases rest with
  | none =>
      cases selected : sortOccurrences residual with
      | nil =>
          allocation_child_eval using (agreement) [projected] unfolding [selected]
          convert variable_returns program _ host "children" using 1
          simp [allocationTasks,selected,encoded,encodeList,encodeOption,
              taskTerm,queryTerm,continuationTerm,frameTerm,allocationTerm,
              CettaWireAtom.encode,CettaWireAtom.encodeMany,
              Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
              Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?]
          all_goals rfl
      | cons first later => allocation_child_eval using (agreement) [projected] unfolding [selected]
  | some name => allocation_child_eval using (agreement) [projected]

include agreement in
/-- Every allocation is processed in order, including rejected allocations;
the builder does not silently keep only the first successful child. -/
@[metta_head "gslt:collection-presentation:view-allocation-children"]
theorem children_returns (host : Effects.State) (category : String) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (next : Continuation .spelling) : ∀ allocations : List (List (List SourceOccurrence) × List SourceOccurrence),
    PureReturns program [] host
      (call "gslt:collection-presentation:view-allocation-children" category schemaBound path focus schemas rest next
        (encodeList allocationTerm (allocations.map ordered))) host
      (encoded (encodeList taskTerm (allocations.flatMap
        (allocationTasks schemaBound path focus schemas rest next))))
  | [] => by allocation_child_eval using (agreement)
  | first :: later => by
      have one := child_returns program agreement host category schemaBound path focus schemas rest next first.1 first.2
      have following := children_returns host category schemaBound path focus schemas rest next later
      have appended := append_returns program agreement taskTerm host
        (allocationTasks schemaBound path focus schemas rest next first)
        (later.flatMap (allocationTasks schemaBound path focus schemas rest next))
      allocation_child_eval using (agreement) [one,following,appended]

#print axioms checked
#print axioms focus_agreement
#print axioms runtime_agreement
#print axioms append_returns
#print axioms child_returns
#print axioms children_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildren
