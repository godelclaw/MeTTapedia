import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource

/-! # Pinned target tests over complete reflective class receipts -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open scoped ProgramQuotation
open MeTTaIL CompleteExecution LibraryCheck

def helperSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rho_native_queries.metta"
    sha256 "41ee1611d31187895a2c3340f8e4a05fe19f3a060c81833b12169d2a6caf9144"

def helperLibrary : BridgeKit.Library :=
  ⟨runnerLibrary.runtime, helperSource.program, ["rho:native:"]⟩

private theorem scoped_kept : keptBy helperLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem typed_kept : keptBy helperLibrary GeneralTypedSiteExecution.source.program = true := by decide +kernel
private theorem descent_kept : keptBy helperLibrary descentSource.program = true := by decide +kernel
private theorem complete_kept : keptBy helperLibrary completeSource.program = true := by decide +kernel
private theorem laws_kept : keptBy helperLibrary lawsSource.program = true := by decide +kernel
private theorem canonical_kept : keptBy helperLibrary canonicalSource.program = true := by decide +kernel
private theorem selection_kept :
    keptBy helperLibrary CollectionSelectionExecution.source.program = true := by decide +kernel
private theorem collection_machine_kept :
    keptBy helperLibrary ScopedCollectionExecution.source.program = true := by decide +kernel
private theorem collection_search_kept :
    keptBy helperLibrary CollectionLoggedSearchExecution.source.program = true := by decide +kernel
private theorem collection_backend_kept :
    keptBy helperLibrary CollectionMatcherBackendExecution.source.program = true := by decide +kernel
private theorem runner_kept : keptBy helperLibrary runnerSource.program = true := by decide +kernel

private theorem recursive_kept : keptBy helperLibrary RecursiveCollectionExecution.source.program = true := by
  decide +kernel
private theorem presentation_kept : keptBy helperLibrary CollectionPresentationExecution.source.program = true := by
  decide +kernel
private theorem handoff_kept : keptBy helperLibrary RecursiveCollectionHandoffExecution.source.program = true := by
  decide +kernel
private theorem continuation_kept : keptBy helperLibrary RecursiveCollectionContinuationExecution.source.program = true := by
  decide +kernel
private theorem batch_kept : keptBy helperLibrary CollectionOccurrenceBatchExecution.source.program = true := by
  decide +kernel
private theorem installation_kept : keptBy helperLibrary CollectionOccurrenceInstallationExecution.source.program = true := by
  decide +kernel
private theorem matchers_kept : keptBy helperLibrary CollectionOccurrenceMatcherExecution.source.program = true := by
  decide +kernel
private theorem collector_kept : keptBy helperLibrary CollectionOccurrenceCollectorExecution.source.program = true := by
  decide +kernel
private theorem machine_kept : keptBy helperLibrary CollectionOccurrenceMachineExecution.source.program = true := by
  decide +kernel
private theorem contexts_kept : keptBy helperLibrary CollectionContextExecution.source.program = true := by
  decide +kernel
private theorem discovery_kept : keptBy helperLibrary CollectionOccurrenceDiscoveryExecution.source.program = true := by
  decide +kernel
private theorem occurrences_kept : keptBy helperLibrary CollectionOccurrenceSearchExecution.source.program = true := by
  decide +kernel

theorem helpers_checked : helperLibrary.check = true := by
  refine check_of helperLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy helperLibrary ((((((((((((((collectionBaseLibrary.runtime.append RecursiveCollectionExecution.source.program).append CollectionPresentationExecution.source.program).append RecursiveCollectionHandoffExecution.source.program).append RecursiveCollectionContinuationExecution.source.program).append CollectionOccurrenceBatchExecution.source.program).append CollectionOccurrenceInstallationExecution.source.program).append CollectionOccurrenceMatcherExecution.source.program).append CollectionOccurrenceCollectorExecution.source.program).append CollectionOccurrenceMachineExecution.source.program).append CollectionContextExecution.source.program).append CollectionOccurrenceDiscoveryExecution.source.program).append CollectionOccurrenceSearchExecution.source.program).append runnerSource.program)) = true
  simp only [keptBy_append, recursive_kept, presentation_kept, handoff_kept, continuation_kept, batch_kept, installation_kept, matchers_kept, collector_kept, machine_kept, contexts_kept, discovery_kept, occurrences_kept, runner_kept, Bool.and_true]
  change keptBy helperLibrary (((((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program).append completeSource.program).append
      lawsSource.program |>.append canonicalSource.program |>.append collectionSupportProgram) = true
  simp only [keptBy_append, scoped_kept, typed_kept, descent_kept, complete_kept, laws_kept,
    canonical_kept, collectionSupportProgram, selection_kept, collection_machine_kept,
    collection_search_kept, collection_backend_kept, Bool.and_true]
  decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
