import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionJoin
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_allocation_advance.metta"
    sha256 "7826e8010753344ea816abf6aa48276e5719f20c8a2182ad0fd7bad0d35df8a8"

def runtime : SpaceSemantics.Program := RetainedOperations.runtime.append source.program

private def completeSource : SpaceSemantics.Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program

private def inherited : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[120]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[134]'(by decide +kernel),
    completeSource.equations[12]'(by decide +kernel),completeSource.equations[26]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[120]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[134]'(by decide +kernel),
    completeSource.declarations[12]'(by decide +kernel),completeSource.declarations[26]'(by decide +kernel)]

/-- The physical primitive rows retain their actual relative order, followed
by the grouping and retained-operation source rows. -/
def library : Library :=
  ⟨{equations := [],declarations := []},
    ((inherited.append Grouping.source).append RetainedOperations.source.program).append source.program,
    ["gslt:"]⟩

theorem checked : library.check = true := by decide +kernel

def proofHeads (head : String) : Bool :=
  RetainedOperations.proofHeads head || Grouping.proofHeads head ||
    head == "gslt:automata:length" || head == "gslt:collection-presentation:view-allocation-advance"

private def rowFields (row : SpaceSemantics.Equation) := (row.head,row.arguments,row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields,Prod.mk.injEq,SpaceSemantics.Equation.mk.injEq] using same

theorem native_agreement :
    ProgramAgreementOn RetainedOperations.proofHeads RetainedOperations.library.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem grouping_agreement :
    ProgramAgreementOn Grouping.proofHeads Grouping.proofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem runtime_agreement : ProgramAgreementOn proofHeads library.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

theorem native_within (head : String) (supported : RetainedOperations.proofHeads head = true) :
    proofHeads head = true := by simp [proofHeads, supported]

theorem grouping_within (head : String) (supported : Grouping.proofHeads head = true) :
    proofHeads head = true := by simp [proofHeads, supported]

theorem group_work_encoding :
    Grouping.workTerm RetainedWire.occurrenceTerm = RetainedWire.workTerm := by
  funext work
  cases work <;> rfl

theorem group_allocation_encoding :
    Grouping.allocationTerm RetainedWire.occurrenceTerm = RetainedWire.allocationTerm := by
  funext allocation
  cases allocation
  rfl

theorem group_cursor_encoding :
    Grouping.stateTerm RetainedWire.occurrenceTerm = RetainedWire.cursorTerm := by
  funext cursor
  cases cursor
  simp only [Grouping.stateTerm, RetainedWire.cursorTerm, group_work_encoding, group_allocation_encoding]

def pendingTasks (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
    (schemas : List Pattern) (rest : Option String) (advanced : GroupedCursor.State)
    (next : Continuation .spelling) : List Task :=
  if GroupedCursor.complete advanced then [] else
    [.allocations schemaBound path focus schemas rest advanced advanced.answers.length (Nat.le_refl _) next]

def progressTerm (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
    (schemas : List Pattern) (rest : Option String) (cursor : GroupedCursor.State)
    (published : Nat) (next : Continuation .spelling) : Term :=
  let advanced := GroupedCursor.tick cursor
  .application "ViewAllocationProgress"
    [RetainedWire.cursorTerm advanced,
      encodeList RetainedWire.allocationTerm (advanced.answers.drop published),
      .natural advanced.answers.length,
      encodeList RetainedWire.taskTerm (pendingTasks schemaBound path focus schemas rest advanced next)]

def previousHeads (head : String) : Bool :=
  head != "gslt:collection-presentation:view-allocation-advance"

theorem previous_runtime_agreement :
    ProgramAgreementOn previousHeads RetainedOperations.runtime runtime := by
  apply appended_program_agreement
  · intro row member
    have all : source.program.equations.all (fun row => !previousHeads row.head) = true := by decide +kernel
    have fresh := List.all_eq_true.mp all row member
    cases result : previousHeads row.head <;> simp_all
  · intro name types member
    have all : source.program.declarations.all
        (fun row => !retainedCallDeclaration previousHeads row) = true := by decide +kernel
    have fresh := List.all_eq_true.mp all _ member
    cases result : previousHeads name with
    | false => rfl
    | true => simp [retainedCallDeclaration,result] at fresh

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads library.runtime program)

syntax "allocation_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| allocation_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in checked using $agreement; metta_eval [$facts,*] with checked in $agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        RetainedOperations.nil_matches_encoded_list, encodeList, encodeOption,
        RetainedWire.taskTerm, progressTerm, pendingTasks,
        InferenceCettaWire.encodeRest, $extra,*]))

include agreement in
@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ values : List α,
    PureReturns program [] host
      (apply "gslt:automata:length" [encoded (encodeList element values)]) host (number values.length)
  | [] => by allocation_eval using (agreement)
  | first :: later => by
      have rest := length_returns element host later
      rw [show (first :: later).length = 1 + later.length by simp [Nat.add_comm]]
      allocation_eval using (agreement) [rest]

include agreement in
/-- One actual grouped-cursor tick, its complete ordered fresh suffix, and the
single retained continuation. This phase leaves residual records unsorted. -/
@[metta_head "gslt:collection-presentation:view-allocation-advance"]
theorem advance_returns (host : Effects.State) (schemaBound : List TypeExpr) (path : List Nat)
    (focus : Focus) (schemas : List Pattern) (rest : Option String) (cursor : GroupedCursor.State)
    (published : Nat) (within : published ≤ cursor.answers.length) (next : Continuation .spelling) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-allocation-advance"
        [encoded (RetainedWire.taskTerm (.allocations schemaBound path focus schemas rest cursor published within next))])
      host (encoded (progressTerm schemaBound path focus schemas rest cursor published next)) := by
  have groupOps := agreement_trans grouping_agreement (agreement_mono grouping_within agreement)
  have nativeOps := agreement_trans native_agreement (agreement_mono native_within agreement)
  let advanced := GroupedCursor.tick cursor
  have ticked := Grouping.tick_returns program groupOps RetainedWire.occurrenceTerm host cursor
  rw [group_cursor_encoding] at ticked
  have answers := Grouping.answers_returns program groupOps RetainedWire.occurrenceTerm host advanced
  rw [group_cursor_encoding, group_allocation_encoding] at answers
  have completed := Grouping.complete_returns program groupOps RetainedWire.occurrenceTerm host advanced
  rw [group_cursor_encoding] at completed
  have fresh := RetainedOperations.drop_returns program nativeOps RetainedWire.allocationTerm host published advanced.answers
  have count := length_returns program agreement RetainedWire.allocationTerm host advanced.answers
  cases finished : GroupedCursor.complete advanced <;>
    rw [finished] at completed <;>
    allocation_eval using (agreement) [ticked, answers, fresh, count, completed]
      unfolding [progressTerm, pendingTasks, advanced, finished]

theorem native_advance_sufficient_fuel (host : Effects.State)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
    (schemas : List Pattern) (rest : Option String) (cursor : GroupedCursor.State)
    (published : Nat) (within : published ≤ cursor.answers.length) (next : Continuation .spelling) :
    ∃ fuel, Eval.run runtime fuel
      {state := host, control := .evaluate []
        (apply "gslt:collection-presentation:view-allocation-advance"
          [encoded (RetainedWire.taskTerm
            (.allocations schemaBound path focus schemas rest cursor published within next))])} =
      .complete host [encoded (progressTerm schemaBound path focus schemas rest cursor published next)] [] [] :=
  pure_returns_has_sufficient_fuel runtime [] host host _ _
    (advance_returns runtime runtime_agreement host schemaBound path focus schemas rest cursor published within next)

theorem native_advance_completed_iff (host after : Effects.State)
    (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
    (schemas : List Pattern) (rest : Option String) (cursor : GroupedCursor.State)
    (published : Nat) (within : published ≤ cursor.answers.length) (next : Continuation .spelling)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run runtime fuel
      {state := host, control := .evaluate []
        (apply "gslt:collection-presentation:view-allocation-advance"
          [encoded (RetainedWire.taskTerm
            (.allocations schemaBound path focus schemas rest cursor published within next))])} =
      .complete after answers input output) ↔
      after = host ∧ answers = [encoded (progressTerm schemaBound path focus schemas rest cursor published next)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] host host _ _
    (advance_returns runtime runtime_agreement host schemaBound path focus schemas rest cursor published within next)
    after answers input output

#print axioms checked
#print axioms native_agreement
#print axioms grouping_agreement
#print axioms runtime_agreement
#print axioms previous_runtime_agreement
#print axioms group_work_encoding
#print axioms group_allocation_encoding
#print axioms group_cursor_encoding
#print axioms length_returns
#print axioms advance_returns
#print axioms native_advance_sufficient_fuel
#print axioms native_advance_completed_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance
