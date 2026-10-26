import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMatcherExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution

/-!
# One native runtime for retained collection occurrence execution

Continuation, batch and installation operations use the selected source directly.
The unchanged matching and preparation operations move to it through the checked
lower-program closure and ordered per-head agreement. Raw arguments remain captured
as data during that transport.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceRuntime

open SpaceSemantics Eval BridgeKit

abbrev runtime : Program := CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime

syntax "occurrence_from_matcher% " "[" str,* "] " term:max : term
macro_rules
  | `(occurrence_from_matcher% [$names,*] $fact) =>
    `(by
      have metadata := CollectionOccurrenceMatcherExecution.matcherProof_agreement
      simp only [CollectionOccurrenceMatcherExecution.library, RetainedMatchingWire.interpreted_runtime] at metadata
      have previous := $fact
      simp only [CollectionOccurrenceMatcherExecution.library, RetainedMatchingWire.interpreted_runtime] at previous
      exact BridgeKit.transport_call
        CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
        CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
        (by decide +kernel) (by decide)
        (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel)
        (by decide) [$names,*] (by decide) (by rfl)
        (by
          intro index bounded
          simp only [List.length_cons, List.length_nil] at bounded
          rw [← metadata.demand _ index (by decide +kernel)]
          interval_cases index <;> decide +kernel) previous)

syntax "occurrence_from_preparation% " "[" str,* "] " term:max : term
macro_rules
  | `(occurrence_from_preparation% [$names,*] $fact) =>
    `(by
      have metadata := RecursiveCollectionHandoffExecution.handoffProof_agreement
      simp only [RecursiveCollectionHandoffExecution.library, RetainedMatchingWire.interpreted_runtime] at metadata
      have previous := $fact
      simp only [RecursiveCollectionHandoffExecution.library, RetainedMatchingWire.interpreted_runtime] at previous
      exact BridgeKit.transport_call
        CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
        CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
        (by decide +kernel) (by decide)
        (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel)
        (by decide) [$names,*] (by decide) (by rfl)
        (by
          intro index bounded
          simp only [List.length_cons, List.length_nil] at bounded
          rw [← metadata.demand _ index (by decide +kernel)]
          interval_cases index <;> decide +kernel) previous)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceRuntime
