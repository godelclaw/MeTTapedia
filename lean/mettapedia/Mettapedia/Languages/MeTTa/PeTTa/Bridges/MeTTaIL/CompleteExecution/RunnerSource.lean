import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionSource

/-!
# The runner, as a MeTTa source

`gslt_runner.metta` (whole runs, fair exploration and the explored transition graph, in
standard, canonical, reflective or model form) loads over the canonical forms and
the established collection search and retained occurrence operations. It is
quoted, pinned and checked as its own `BridgeKit.Library`, in the order the gate loads it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open scoped ProgramQuotation
open LibraryCheck

def runnerSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_runner.metta"
    sha256 "c7f97a840f35d77a9b41a121b4e3dc5ff30a50bac7241f25cde4e96b9544f21a"

/-- Explicit descriptor for the established complete-class search. -/
abbrev classSearchBackend : Mettapedia.Languages.MeTTa.OSLFCore.Atom := .symbol "ClassSearch"

/-- The shared runner over its certified search implementations. -/
def runnerLibrary : BridgeKit.Library :=
  ⟨CollectionOccurrenceSearchExecution.library.runtime, runnerSource.program,
    ["gslt:search:", "gslt:runner:", "gslt:explore:", "gslt:collection-root:"]⟩

set_option maxRecDepth 100000

open Eval BridgeKit

private theorem runner_scoped : keptBy runnerLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem runner_typed : keptBy runnerLibrary GeneralTypedSiteExecution.source.program = true := by
  decide +kernel
private theorem runner_descent : keptBy runnerLibrary descentSource.program = true := by decide +kernel
private theorem runner_complete : keptBy runnerLibrary completeSource.program = true := by decide +kernel
private theorem runner_laws : keptBy runnerLibrary lawsSource.program = true := by decide +kernel
private theorem runner_canonical : keptBy runnerLibrary canonicalSource.program = true := by decide +kernel
private theorem runner_selection :
    keptBy runnerLibrary CollectionSelectionExecution.source.program = true := by decide +kernel
private theorem runner_collection_machine :
    keptBy runnerLibrary ScopedCollectionExecution.source.program = true := by decide +kernel
private theorem runner_collection_search :
    keptBy runnerLibrary CollectionLoggedSearchExecution.source.program = true := by decide +kernel
private theorem runner_collection_backend :
    keptBy runnerLibrary CollectionMatcherBackendExecution.source.program = true := by decide +kernel

private theorem runner_recursive : keptBy runnerLibrary RecursiveCollectionExecution.source.program = true := by
  decide +kernel
private theorem runner_presentation : keptBy runnerLibrary CollectionPresentationExecution.source.program = true := by
  decide +kernel
private theorem runner_handoff : keptBy runnerLibrary RecursiveCollectionHandoffExecution.source.program = true := by
  decide +kernel
private theorem runner_continuation : keptBy runnerLibrary RecursiveCollectionContinuationExecution.source.program = true := by
  decide +kernel
private theorem runner_batch : keptBy runnerLibrary CollectionOccurrenceBatchExecution.source.program = true := by
  decide +kernel
private theorem runner_installation : keptBy runnerLibrary CollectionOccurrenceInstallationExecution.source.program = true := by
  decide +kernel
private theorem runner_matchers : keptBy runnerLibrary CollectionOccurrenceMatcherExecution.source.program = true := by
  decide +kernel
private theorem runner_collector : keptBy runnerLibrary CollectionOccurrenceCollectorExecution.source.program = true := by
  decide +kernel
private theorem runner_machine : keptBy runnerLibrary CollectionOccurrenceMachineExecution.source.program = true := by
  decide +kernel
private theorem runner_contexts : keptBy runnerLibrary CollectionContextExecution.source.program = true := by
  decide +kernel
private theorem runner_discovery : keptBy runnerLibrary CollectionOccurrenceDiscoveryExecution.source.program = true := by
  decide +kernel
private theorem runner_occurrences : keptBy runnerLibrary CollectionOccurrenceSearchExecution.source.program = true := by
  decide +kernel

theorem runner_checked : runnerLibrary.check = true := by
  refine check_of runnerLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy runnerLibrary (((((((((((((collectionBaseLibrary.runtime.append RecursiveCollectionExecution.source.program).append CollectionPresentationExecution.source.program).append RecursiveCollectionHandoffExecution.source.program).append RecursiveCollectionContinuationExecution.source.program).append CollectionOccurrenceBatchExecution.source.program).append CollectionOccurrenceInstallationExecution.source.program).append CollectionOccurrenceMatcherExecution.source.program).append CollectionOccurrenceCollectorExecution.source.program).append CollectionOccurrenceMachineExecution.source.program).append CollectionContextExecution.source.program).append CollectionOccurrenceDiscoveryExecution.source.program).append CollectionOccurrenceSearchExecution.source.program)) = true
  simp only [keptBy_append, runner_recursive, runner_presentation, runner_handoff, runner_continuation, runner_batch, runner_installation, runner_matchers, runner_collector, runner_machine, runner_contexts, runner_discovery, runner_occurrences, Bool.and_true]
  change keptBy runnerLibrary (((((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program |>.append completeSource.program).append
      lawsSource.program).append canonicalSource.program |>.append collectionSupportProgram) = true
  simp only [keptBy_append, runner_scoped, runner_typed, runner_descent, runner_complete, runner_laws,
    runner_canonical, collectionSupportProgram, runner_selection,
    runner_collection_machine, runner_collection_search, runner_collection_backend, Bool.and_true]
  decide

syntax "runner_from_base% " "[" str,* "] " term:max : term
macro_rules
  | `(runner_from_base% [$names,*] $fact) =>
    `(by
      have atRecursive := by metta_lift RecursiveCollectionExecution.checked [$names,*] $fact
      have atPresentation := by metta_lift CollectionPresentationExecution.checked [$names,*] atRecursive
      have atHandoff := by metta_lift RecursiveCollectionHandoffExecution.checked [$names,*] atPresentation
      have atRuntime := occurrence_from_preparation% [$names,*] atHandoff
      have atCollector := by metta_lift CollectionOccurrenceCollectorExecution.checked [$names,*] atRuntime
      have atMachine := by metta_lift CollectionOccurrenceMachineExecution.checked [$names,*] atCollector
      have atContexts := by metta_lift CollectionOccurrenceDiscoveryExecution.contexts_checked [$names,*] atMachine
      have atDiscovery := by metta_lift CollectionOccurrenceDiscoveryExecution.checked [$names,*] atContexts
      have atOccurrence := by metta_lift CollectionOccurrenceSearchExecution.checked [$names,*] atDiscovery
      metta_lift runner_checked [$names,*] atOccurrence)

/-- A canonical operation in the shared runtime. -/
syntax "canonical_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(canonical_runner_lifted% [$names,*] $fact) =>
      `(runner_from_base% [$names,*]
        (BridgeKit.Library.lift_call collection_base_checked (by decide +kernel)
          (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
          (by rfl) (by decide +kernel) $fact))

/-- A logged-search operation in the same shared runtime. -/
syntax "collection_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(collection_runner_lifted% [$names,*] $fact) =>
      `(runner_from_base% [$names,*]
        (BridgeKit.transport_call collection_retained_closed collection_base_agreement
          (by decide +kernel) (by decide) (by decide +kernel) (by decide)
          [$names,*] (by decide) (by rfl) (by decide +kernel) $fact))

syntax "laws_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(laws_runner_lifted% [$names,*] $fact) =>
      `(canonical_runner_lifted% [$names,*]
        (BridgeKit.Library.lift_call canonical_checked (by decide +kernel)
          (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
          (by rfl) (by decide +kernel) $fact))

syntax "complete_runner_lifted% " "[" str,* "] " term:max : term
macro_rules
  | `(complete_runner_lifted% [$names,*] $fact) =>
      `(laws_runner_lifted% [$names,*]
        (BridgeKit.Library.lift_call laws_checked (by decide +kernel)
          (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
          (by rfl) (by decide +kernel) $fact))

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
