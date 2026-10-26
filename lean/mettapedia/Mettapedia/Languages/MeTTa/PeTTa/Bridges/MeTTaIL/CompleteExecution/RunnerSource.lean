import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source

/-!
# The common runner on the selected native program

The physical runner is loaded once. Its bounded source view supplies body and
argument metadata; primitive execution facts move through the checked lower
program closure. Operational conclusions use the selected shared runtime.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit
open scoped ProgramQuotation

def runnerSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_runner.metta"
    sha256 "c7f97a840f35d77a9b41a121b4e3dc5ff30a50bac7241f25cde4e96b9544f21a"

/-- Explicit descriptor for the established complete-class search. -/
abbrev classSearchBackend : Atom := .symbol "ClassSearch"

/-- The runner uses the same selected program as the collection implementations. -/
def runnerLibrary : Library := CollectionOccurrenceSearchExecution.SelectedNativeSource.library

def runnerProofInheritedHeads : List String := ["gslt:laws:standard", "gslt:canon:canonical", "gslt:rule:scope-reflective-normalize", "gslt:canon:model-normal", "gslt:classes:begin", "gslt:classes:rounds", "gslt:collection-search:run-plan", "gslt:occurrence-search:run", "gslt:collection-search:resume-run", "gslt:occurrence-search:resume", "gslt:collection-search:publication", "gslt:occurrence-search:publication", "gslt:classes:entries-complete", "gslt:collection-search:status", "gslt:occurrence-search:status", "gslt:canon:canon", "gslt:occurrence-search:target", "gslt:automata:length", "gslt:complete:drop", "gslt:automata:append", "gslt:collection-machine:publication", "gslt:collection-backend:ordinary-target", "gslt:deep:nodes", "gslt:collection-backend:frame-begin", "gslt:premise:open-well-sorted", "gslt:collection-search:requests-for-source", "gslt:collection-plan:start", "gslt:collection-plan:complete", "gslt:collection-backend:state-begin", "gslt:collection-plan:resume", "gslt:collection-backend:state-run", "gslt:collection-backend:state-settled"]

private def runnerProofSource : Program := (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program

private def runnerOwns (head : String) : Bool :=
  ["gslt:search:", "gslt:runner:", "gslt:explore:", "gslt:collection-root:"].any (·.isPrefixOf head)

def runnerProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || runnerOwns head || runnerProofInheritedHeads.contains head

/-- The metadata inventory is derived from the actual runner bodies. -/
theorem runnerProofInheritedHeads_derived :
    ((runnerProofSource.equations.flatMap (fun row => sourceLiteralHeads row.body)).filter
      (fun head => head.startsWith "gslt:" && !runnerOwns head)).eraseDups =
        runnerProofInheritedHeads := by decide +kernel

theorem runnerProof_source_quote : runnerProofSource = runnerSource.program := by rfl

private def runnerScoped_equations_rows := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel), RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel), RuleExecutionProgram.scopedProgram.equations[146]'(by decide +kernel), RuleExecutionProgram.scopedProgram.equations[181]'(by decide +kernel)]

private theorem runnerScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨146, by decide +kernel⟩, ⟨181, by decide +kernel⟩] := by decide +kernel

private theorem runnerScoped_equations : RuleExecutionProgram.scopedProgram.equations.filter (fun row => runnerProofHeads row.head) = runnerScoped_equations_rows := by
  rw [source_filter_indices, runnerScoped_equations_indices]
  rfl

private def runnerScoped_declarations_rows := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel), RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel), RuleExecutionProgram.scopedProgram.declarations[146]'(by decide +kernel), RuleExecutionProgram.scopedProgram.declarations[181]'(by decide +kernel)]

private theorem runnerScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨146, by decide +kernel⟩, ⟨181, by decide +kernel⟩] := by decide +kernel

private theorem runnerScoped_declarations : RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerScoped_declarations_rows := by
  rw [source_filter_indices, runnerScoped_declarations_indices]
  rfl

private def runnerPart0_equations_rows : List Equation := []

private theorem runnerPart0_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart0_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart0_equations_rows := by
  rw [source_filter_indices, runnerPart0_equations_indices]
  rfl

private def runnerPart0_declarations_rows : List Atom := []

private theorem runnerPart0_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart0_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart0_declarations_rows := by
  rw [source_filter_indices, runnerPart0_declarations_indices]
  rfl

private def runnerPart1_equations_rows : List Equation := []

private theorem runnerPart1_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart1_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart1_equations_rows := by
  rw [source_filter_indices, runnerPart1_equations_indices]
  rfl

private def runnerPart1_declarations_rows : List Atom := []

private theorem runnerPart1_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart1_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart1_declarations_rows := by
  rw [source_filter_indices, runnerPart1_declarations_indices]
  rfl

private def runnerPart2_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations[12]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations[73]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations[80]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations[81]'(by decide +kernel)]

private theorem runnerPart2_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨12, by decide +kernel⟩, ⟨73, by decide +kernel⟩, ⟨80, by decide +kernel⟩, ⟨81, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart2_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart2_equations_rows := by
  rw [source_filter_indices, runnerPart2_equations_indices]
  rfl

private def runnerPart2_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations[12]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations[73]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations[80]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations[81]'(by decide +kernel)]

private theorem runnerPart2_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨12, by decide +kernel⟩, ⟨73, by decide +kernel⟩, ⟨80, by decide +kernel⟩, ⟨81, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart2_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart2_declarations_rows := by
  rw [source_filter_indices, runnerPart2_declarations_indices]
  rfl

private def runnerPart3_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.equations[10]'(by decide +kernel)]

private theorem runnerPart3_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.equations.get index)) =
      [⟨10, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart3_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart3_equations_rows := by
  rw [source_filter_indices, runnerPart3_equations_indices]
  rfl

private def runnerPart3_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.declarations[10]'(by decide +kernel)]

private theorem runnerPart3_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.declarations.get index)) =
      [⟨10, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart3_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart3_declarations_rows := by
  rw [source_filter_indices, runnerPart3_declarations_indices]
  rfl

private def runnerPart4_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations[17]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations[27]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations[29]'(by decide +kernel)]

private theorem runnerPart4_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations.get index)) =
      [⟨17, by decide +kernel⟩, ⟨27, by decide +kernel⟩, ⟨29, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart4_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart4_equations_rows := by
  rw [source_filter_indices, runnerPart4_equations_indices]
  rfl

private def runnerPart4_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations[17]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations[27]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations[29]'(by decide +kernel)]

private theorem runnerPart4_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations.get index)) =
      [⟨17, by decide +kernel⟩, ⟨27, by decide +kernel⟩, ⟨29, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart4_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart4_declarations_rows := by
  rw [source_filter_indices, runnerPart4_declarations_indices]
  rfl

private def runnerPart5_equations_rows : List Equation := []

private theorem runnerPart5_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart5_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart5_equations_rows := by
  rw [source_filter_indices, runnerPart5_equations_indices]
  rfl

private def runnerPart5_declarations_rows : List Atom := []

private theorem runnerPart5_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart5_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart5_declarations_rows := by
  rw [source_filter_indices, runnerPart5_declarations_indices]
  rfl

private def runnerPart6_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations[6]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations[9]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations[10]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations[11]'(by decide +kernel)]

private theorem runnerPart6_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations.get index)) =
      [⟨6, by decide +kernel⟩, ⟨9, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨11, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart6_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart6_equations_rows := by
  rw [source_filter_indices, runnerPart6_equations_indices]
  rfl

private def runnerPart6_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations[6]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations[9]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations[10]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations[11]'(by decide +kernel)]

private theorem runnerPart6_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations.get index)) =
      [⟨6, by decide +kernel⟩, ⟨9, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨11, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart6_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart6_declarations_rows := by
  rw [source_filter_indices, runnerPart6_declarations_indices]
  rfl

private def runnerPart7_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations[3]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations[18]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations[19]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations[21]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations[22]'(by decide +kernel)]

private theorem runnerPart7_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations.get index)) =
      [⟨3, by decide +kernel⟩, ⟨18, by decide +kernel⟩, ⟨19, by decide +kernel⟩, ⟨21, by decide +kernel⟩, ⟨22, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart7_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart7_equations_rows := by
  rw [source_filter_indices, runnerPart7_equations_indices]
  rfl

private def runnerPart7_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations[3]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations[18]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations[19]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations[21]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations[22]'(by decide +kernel)]

private theorem runnerPart7_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations.get index)) =
      [⟨3, by decide +kernel⟩, ⟨18, by decide +kernel⟩, ⟨19, by decide +kernel⟩, ⟨21, by decide +kernel⟩, ⟨22, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart7_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart7_declarations_rows := by
  rw [source_filter_indices, runnerPart7_declarations_indices]
  rfl

private def runnerPart8_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations[8]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations[15]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations[17]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations[19]'(by decide +kernel)]

private theorem runnerPart8_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨8, by decide +kernel⟩, ⟨15, by decide +kernel⟩, ⟨17, by decide +kernel⟩, ⟨19, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart8_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart8_equations_rows := by
  rw [source_filter_indices, runnerPart8_equations_indices]
  rfl

private def runnerPart8_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations[8]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations[15]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations[17]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations[19]'(by decide +kernel)]

private theorem runnerPart8_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨8, by decide +kernel⟩, ⟨15, by decide +kernel⟩, ⟨17, by decide +kernel⟩, ⟨19, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart8_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart8_declarations_rows := by
  rw [source_filter_indices, runnerPart8_declarations_indices]
  rfl

private def runnerPart9_equations_rows : List Equation := []

private theorem runnerPart9_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart9_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart9_equations_rows := by
  rw [source_filter_indices, runnerPart9_equations_indices]
  rfl

private def runnerPart9_declarations_rows : List Atom := []

private theorem runnerPart9_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart9_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart9_declarations_rows := by
  rw [source_filter_indices, runnerPart9_declarations_indices]
  rfl

private def runnerPart10_equations_rows : List Equation := []

private theorem runnerPart10_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart10_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart10_equations_rows := by
  rw [source_filter_indices, runnerPart10_equations_indices]
  rfl

private def runnerPart10_declarations_rows : List Atom := []

private theorem runnerPart10_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart10_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart10_declarations_rows := by
  rw [source_filter_indices, runnerPart10_declarations_indices]
  rfl

private def runnerPart11_equations_rows : List Equation := []

private theorem runnerPart11_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart11_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart11_equations_rows := by
  rw [source_filter_indices, runnerPart11_equations_indices]
  rfl

private def runnerPart11_declarations_rows : List Atom := []

private theorem runnerPart11_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart11_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart11_declarations_rows := by
  rw [source_filter_indices, runnerPart11_declarations_indices]
  rfl

private def runnerPart12_equations_rows : List Equation := []

private theorem runnerPart12_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart12_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart12_equations_rows := by
  rw [source_filter_indices, runnerPart12_equations_indices]
  rfl

private def runnerPart12_declarations_rows : List Atom := []

private theorem runnerPart12_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart12_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart12_declarations_rows := by
  rw [source_filter_indices, runnerPart12_declarations_indices]
  rfl

private def runnerPart13_equations_rows : List Equation := []

private theorem runnerPart13_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart13_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart13_equations_rows := by
  rw [source_filter_indices, runnerPart13_equations_indices]
  rfl

private def runnerPart13_declarations_rows : List Atom := []

private theorem runnerPart13_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart13_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart13_declarations_rows := by
  rw [source_filter_indices, runnerPart13_declarations_indices]
  rfl

private def runnerPart14_equations_rows : List Equation := []

private theorem runnerPart14_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart14_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart14_equations_rows := by
  rw [source_filter_indices, runnerPart14_equations_indices]
  rfl

private def runnerPart14_declarations_rows : List Atom := []

private theorem runnerPart14_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart14_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart14_declarations_rows := by
  rw [source_filter_indices, runnerPart14_declarations_indices]
  rfl

private def runnerPart15_equations_rows : List Equation := []

private theorem runnerPart15_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart15_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart15_equations_rows := by
  rw [source_filter_indices, runnerPart15_equations_indices]
  rfl

private def runnerPart15_declarations_rows : List Atom := []

private theorem runnerPart15_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart15_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart15_declarations_rows := by
  rw [source_filter_indices, runnerPart15_declarations_indices]
  rfl

private def runnerPart16_equations_rows : List Equation := []

private theorem runnerPart16_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart16_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart16_equations_rows := by
  rw [source_filter_indices, runnerPart16_equations_indices]
  rfl

private def runnerPart16_declarations_rows : List Atom := []

private theorem runnerPart16_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart16_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart16_declarations_rows := by
  rw [source_filter_indices, runnerPart16_declarations_indices]
  rfl

private def runnerPart17_equations_rows : List Equation := []

private theorem runnerPart17_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart17_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart17_equations_rows := by
  rw [source_filter_indices, runnerPart17_equations_indices]
  rfl

private def runnerPart17_declarations_rows : List Atom := []

private theorem runnerPart17_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart17_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart17_declarations_rows := by
  rw [source_filter_indices, runnerPart17_declarations_indices]
  rfl

private def runnerPart18_equations_rows : List Equation := []

private theorem runnerPart18_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart18_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart18_equations_rows := by
  rw [source_filter_indices, runnerPart18_equations_indices]
  rfl

private def runnerPart18_declarations_rows : List Atom := []

private theorem runnerPart18_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart18_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart18_declarations_rows := by
  rw [source_filter_indices, runnerPart18_declarations_indices]
  rfl

private def runnerPart19_equations_rows : List Equation := []

private theorem runnerPart19_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.equations.get index)) =
      [] := by decide +kernel

private theorem runnerPart19_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart19_equations_rows := by
  rw [source_filter_indices, runnerPart19_equations_indices]
  rfl

private def runnerPart19_declarations_rows : List Atom := []

private theorem runnerPart19_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.declarations.get index)) =
      [] := by decide +kernel

private theorem runnerPart19_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart19_declarations_rows := by
  rw [source_filter_indices, runnerPart19_declarations_indices]
  rfl

private def runnerPart20_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations[1]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations[5]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations[10]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations[11]'(by decide +kernel)]

private theorem runnerPart20_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨5, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨11, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart20_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart20_equations_rows := by
  rw [source_filter_indices, runnerPart20_equations_indices]
  rfl

private def runnerPart20_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations[1]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations[5]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations[10]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations[11]'(by decide +kernel)]

private theorem runnerPart20_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨5, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨11, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart20_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart20_declarations_rows := by
  rw [source_filter_indices, runnerPart20_declarations_indices]
  rfl

private def runnerPart21_equations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[1]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[2]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[3]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[4]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[5]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[6]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[7]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[8]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[9]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[10]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[11]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[12]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[13]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[14]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[15]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[16]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[17]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[18]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[19]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[20]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[21]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[22]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[23]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[24]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[25]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[26]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[27]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[28]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[29]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[30]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[31]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[32]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[33]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[34]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations[35]'(by decide +kernel)]

private theorem runnerPart21_equations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations.length).filter (fun index => (fun row => runnerProofHeads row.head) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩, ⟨5, by decide +kernel⟩, ⟨6, by decide +kernel⟩, ⟨7, by decide +kernel⟩, ⟨8, by decide +kernel⟩, ⟨9, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨11, by decide +kernel⟩, ⟨12, by decide +kernel⟩, ⟨13, by decide +kernel⟩, ⟨14, by decide +kernel⟩, ⟨15, by decide +kernel⟩, ⟨16, by decide +kernel⟩, ⟨17, by decide +kernel⟩, ⟨18, by decide +kernel⟩, ⟨19, by decide +kernel⟩, ⟨20, by decide +kernel⟩, ⟨21, by decide +kernel⟩, ⟨22, by decide +kernel⟩, ⟨23, by decide +kernel⟩, ⟨24, by decide +kernel⟩, ⟨25, by decide +kernel⟩, ⟨26, by decide +kernel⟩, ⟨27, by decide +kernel⟩, ⟨28, by decide +kernel⟩, ⟨29, by decide +kernel⟩, ⟨30, by decide +kernel⟩, ⟨31, by decide +kernel⟩, ⟨32, by decide +kernel⟩, ⟨33, by decide +kernel⟩, ⟨34, by decide +kernel⟩, ⟨35, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart21_equations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations.filter (fun row => runnerProofHeads row.head) = runnerPart21_equations_rows := by
  rw [source_filter_indices, runnerPart21_equations_indices]
  rfl

private def runnerPart21_declarations_rows := [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[0]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[1]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[2]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[3]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[4]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[5]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[6]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[7]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[8]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[9]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[10]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[11]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[12]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[13]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[14]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[15]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[16]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[17]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[18]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[19]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[20]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[21]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[22]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[23]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[24]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[25]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[26]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[27]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[28]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[29]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[30]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[31]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[32]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[33]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[34]'(by decide +kernel), (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations[35]'(by decide +kernel)]

private theorem runnerPart21_declarations_indices :
    (List.finRange (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations.length).filter (fun index => (retainedCallDeclaration runnerProofHeads) ((CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩, ⟨5, by decide +kernel⟩, ⟨6, by decide +kernel⟩, ⟨7, by decide +kernel⟩, ⟨8, by decide +kernel⟩, ⟨9, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨11, by decide +kernel⟩, ⟨12, by decide +kernel⟩, ⟨13, by decide +kernel⟩, ⟨14, by decide +kernel⟩, ⟨15, by decide +kernel⟩, ⟨16, by decide +kernel⟩, ⟨17, by decide +kernel⟩, ⟨18, by decide +kernel⟩, ⟨19, by decide +kernel⟩, ⟨20, by decide +kernel⟩, ⟨21, by decide +kernel⟩, ⟨22, by decide +kernel⟩, ⟨23, by decide +kernel⟩, ⟨24, by decide +kernel⟩, ⟨25, by decide +kernel⟩, ⟨26, by decide +kernel⟩, ⟨27, by decide +kernel⟩, ⟨28, by decide +kernel⟩, ⟨29, by decide +kernel⟩, ⟨30, by decide +kernel⟩, ⟨31, by decide +kernel⟩, ⟨32, by decide +kernel⟩, ⟨33, by decide +kernel⟩, ⟨34, by decide +kernel⟩, ⟨35, by decide +kernel⟩] := by decide +kernel

private theorem runnerPart21_declarations : (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations.filter (retainedCallDeclaration runnerProofHeads) = runnerPart21_declarations_rows := by
  rw [source_filter_indices, runnerPart21_declarations_indices]
  rfl

private def runnerMetadataBase : Program where
  equations := runnerScoped_equations_rows ++ runnerPart0_equations_rows ++ runnerPart1_equations_rows ++ runnerPart2_equations_rows ++ runnerPart3_equations_rows ++ runnerPart4_equations_rows ++ runnerPart5_equations_rows ++ runnerPart6_equations_rows ++ runnerPart7_equations_rows ++ runnerPart8_equations_rows ++ runnerPart9_equations_rows ++ runnerPart10_equations_rows ++ runnerPart11_equations_rows ++ runnerPart12_equations_rows ++ runnerPart13_equations_rows ++ runnerPart14_equations_rows ++ runnerPart15_equations_rows ++ runnerPart16_equations_rows ++ runnerPart17_equations_rows ++ runnerPart18_equations_rows ++ runnerPart19_equations_rows ++ runnerPart20_equations_rows
  declarations := runnerScoped_declarations_rows ++ runnerPart0_declarations_rows ++ runnerPart1_declarations_rows ++ runnerPart2_declarations_rows ++ runnerPart3_declarations_rows ++ runnerPart4_declarations_rows ++ runnerPart5_declarations_rows ++ runnerPart6_declarations_rows ++ runnerPart7_declarations_rows ++ runnerPart8_declarations_rows ++ runnerPart9_declarations_rows ++ runnerPart10_declarations_rows ++ runnerPart11_declarations_rows ++ runnerPart12_declarations_rows ++ runnerPart13_declarations_rows ++ runnerPart14_declarations_rows ++ runnerPart15_declarations_rows ++ runnerPart16_declarations_rows ++ runnerPart17_declarations_rows ++ runnerPart18_declarations_rows ++ runnerPart19_declarations_rows ++ runnerPart20_declarations_rows

def runnerProofLibrary : Library :=
  ⟨runnerMetadataBase, runnerProofSource, ["gslt:search:", "gslt:runner:", "gslt:explore:", "gslt:collection-root:"]⟩

theorem runnerProof_checked : runnerProofLibrary.check = true := by decide +kernel

private def runnerPhysicalProgram : Program :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.foldl (fun loaded part => loaded.append part.program) RuleExecutionProgram.scopedProgram

private theorem runnerSupport_equations :
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.flatMap (fun part => part.program.equations)) =
      (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.equations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.equations ++ [] := by rfl

private theorem runnerPart21_equations_whole : runnerPart21_equations_rows = runnerProofSource.equations := by rfl

theorem runnerProof_physical_equations : runnerProofLibrary.runtime.equations =
    runnerPhysicalProgram.equations.filter (fun row => runnerProofHeads row.head) := by
  rw [runnerPhysicalProgram, PhysicalSourceAgreement.fold_equations, runnerSupport_equations]
  simp only [List.filter_append, runnerScoped_equations, runnerPart0_equations, runnerPart1_equations, runnerPart2_equations, runnerPart3_equations, runnerPart4_equations, runnerPart5_equations, runnerPart6_equations, runnerPart7_equations, runnerPart8_equations, runnerPart9_equations, runnerPart10_equations, runnerPart11_equations, runnerPart12_equations, runnerPart13_equations, runnerPart14_equations, runnerPart15_equations, runnerPart16_equations, runnerPart17_equations, runnerPart18_equations, runnerPart19_equations, runnerPart20_equations, runnerPart21_equations, List.append_nil]
  change _ ++ runnerProofSource.equations = _
  simp only [runnerProofLibrary, runnerMetadataBase, runnerPart21_equations_whole, List.append_assoc]

private theorem runnerSupport_declarations :
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.flatMap (fun part => part.program.declarations)) =
      (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[0]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[2]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[3]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[4]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[5]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[6]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[7]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[9]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[10]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[11]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[12]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[14]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[15]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[16]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[17]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[18]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[19]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[20]'(by decide +kernel)).program.declarations ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[21]'(by decide +kernel)).program.declarations ++ [] := by rfl

private theorem runnerPart21_declarations_whole : runnerPart21_declarations_rows = runnerProofSource.declarations := by rfl

theorem runnerProof_physical_declarations : runnerProofLibrary.runtime.declarations =
    runnerPhysicalProgram.declarations.filter (retainedCallDeclaration runnerProofHeads) := by
  rw [runnerPhysicalProgram, PhysicalSourceAgreement.fold_declarations, runnerSupport_declarations]
  simp only [List.filter_append, runnerScoped_declarations, runnerPart0_declarations, runnerPart1_declarations, runnerPart2_declarations, runnerPart3_declarations, runnerPart4_declarations, runnerPart5_declarations, runnerPart6_declarations, runnerPart7_declarations, runnerPart8_declarations, runnerPart9_declarations, runnerPart10_declarations, runnerPart11_declarations, runnerPart12_declarations, runnerPart13_declarations, runnerPart14_declarations, runnerPart15_declarations, runnerPart16_declarations, runnerPart17_declarations, runnerPart18_declarations, runnerPart19_declarations, runnerPart20_declarations, runnerPart21_declarations, List.append_nil]
  change _ ++ runnerProofSource.declarations = _
  simp only [runnerProofLibrary, runnerMetadataBase, runnerPart21_declarations_whole, List.append_assoc]

theorem runnerProof_agreement : ProgramAgreementOn runnerProofHeads
    runnerProofLibrary.runtime runnerLibrary.runtime := by
  have physical : ProgramAgreementOn runnerProofHeads runnerProofLibrary.runtime runnerPhysicalProgram :=
    fragment_agreement _ _ runnerProof_physical_equations runnerProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical (agreement_mono (fun _ _ => rfl)
    CollectionOccurrenceSearchExecution.SelectedNativeSource.PhysicalAgreement.physical_selected_agreement)

theorem runner_checked : runnerLibrary.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

/-- Metadata for unchanged primitive heads, directed back to the lower program. -/
def runnerLowerProofHeads (head : String) : Bool :=
  runnerProofHeads head && CollectionOccurrenceSearchExecution.SelectedNativeSource.lowerHeads head

theorem runnerLowerProof_agreement : ProgramAgreementOn runnerLowerProofHeads
    runnerProofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram where
  dispatch head supported := by
    obtain ⟨present, unchanged⟩ := Bool.and_eq_true_iff.mp supported
    exact (runnerProof_agreement.dispatch head present).trans
      (CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement.dispatch head unchanged).symm
  demand head index supported := by
    obtain ⟨present, unchanged⟩ := Bool.and_eq_true_iff.mp supported
    exact (runnerProof_agreement.demand head index present).trans
      (CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement.demand head index unchanged).symm
  bodies head values supported := by
    obtain ⟨present, unchanged⟩ := Bool.and_eq_true_iff.mp supported
    exact (runnerProof_agreement.bodies head values present).trans
      (CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement.bodies head values unchanged).symm

syntax "runner_from_base% " "[" str,* "] " term:max (" using " term:max)? : term
macro_rules
  | `(runner_from_base% [$names,*] $fact $[using $agreement]?) => do
    let metadata := agreement.getD (← `(runnerLowerProof_agreement))
    `(BridgeKit.transport_call
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
      (by decide +kernel) (by decide)
      (by rw [← ($metadata).dispatch _ (by decide +kernel)]; decide +kernel)
      (by decide) [$names,*] (by decide) (by rfl)
      (by
        intro index bounded
        simp only [List.length_cons, List.length_nil] at bounded
        rw [← ($metadata).demand _ index (by decide +kernel)]
        interval_cases index <;> decide +kernel) $fact)

syntax "canonical_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(canonical_runner_lifted% [$names,*] $fact) => `(runner_from_base% [$names,*] $fact)

syntax "collection_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(collection_runner_lifted% [$names,*] $fact) => `(runner_from_base% [$names,*] $fact)

syntax "laws_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(laws_runner_lifted% [$names,*] $fact) => `(runner_from_base% [$names,*] $fact)

syntax "complete_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(complete_runner_lifted% [$names,*] $fact) => `(runner_from_base% [$names,*] $fact)

#print axioms runnerProofInheritedHeads_derived
#print axioms runnerProof_source_quote
#print axioms runnerProof_checked
#print axioms runnerProof_physical_equations
#print axioms runnerProof_physical_declarations
#print axioms runnerProof_agreement
#print axioms runnerLowerProof_agreement
#print axioms runner_checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
