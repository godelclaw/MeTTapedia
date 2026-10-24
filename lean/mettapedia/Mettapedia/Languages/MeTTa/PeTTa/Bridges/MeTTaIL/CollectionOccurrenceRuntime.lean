import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMatcherExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution

/-!
# One native runtime for retained collection occurrence execution

Preparation, recursive matching and conditional publication were proved over
different source extensions. This assembly loads their existing source once.
Ordered body and argument-demand agreement transport the earlier execution
proofs to this runtime, without changing the runner or any matching operation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceRuntime

open SpaceSemantics Eval BridgeKit

private def equationData (equation : Equation) :
    String × List Mettapedia.Languages.MeTTa.OSLFCore.Atom × Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  (equation.head, equation.arguments, equation.body)

private theorem equationData_injective : Function.Injective equationData := by
  rintro ⟨firstHead, firstArguments, firstBody⟩ ⟨secondHead, secondArguments, secondBody⟩ same
  simp only [equationData, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl⟩
  rfl

def continuations : Library :=
  ⟨RecursiveCollectionHandoffExecution.library.runtime,
    RecursiveCollectionContinuationExecution.source.program, ["gslt:collection-continuation:"]⟩

theorem continuations_checked : continuations.check = true := by decide +kernel

def batches : Library :=
  ⟨continuations.runtime, CollectionOccurrenceBatchExecution.source.program, ["gslt:occurrence-batch:"]⟩

theorem batches_checked : batches.check = true := by decide +kernel

def installations : Library :=
  ⟨batches.runtime, CollectionOccurrenceInstallationExecution.source.program, ["gslt:occurrence-install:"]⟩

theorem installations_checked : installations.check = true := by decide +kernel

def matchers : Library :=
  ⟨installations.runtime, CollectionOccurrenceMatcherExecution.source.program, ["gslt:occurrence-matcher:"]⟩

theorem matchers_checked : matchers.check = true := by decide +kernel

abbrev runtime : Program := matchers.runtime

/-- The conditional-publication runtime does not call the additional
canonical, preparation or recursive-matching namespaces. -/
def publicationHeads (head : String) : Bool :=
  !(["gslt:laws:", "gslt:canon:", "gslt:collection-search:",
    "gslt:recursive-collection:", "gslt:collection-presentation:",
    "gslt:collection-handoff:", "gslt:occurrence-matcher:"].any (·.isPrefixOf head))

theorem publication_closed :
    ProgramClosed publicationHeads CollectionOccurrenceInstallationExecution.library.runtime := by
  apply closed_of_all _ _ (by decide +kernel)
  decide +kernel

theorem publication_agreement :
    ProgramAgreementOn publicationHeads CollectionOccurrenceInstallationExecution.library.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply (List.map_inj_right (fun _ _ same => equationData_injective same)).mp
    decide +kernel
  · decide +kernel

/-- The recursive matcher does not call the later ordinary-preparation or
conditional-publication operations. -/
def matcherHeads (head : String) : Bool :=
  !(["gslt:collection-presentation:", "gslt:collection-handoff:",
    "gslt:collection-continuation:", "gslt:occurrence-batch:",
    "gslt:occurrence-install:"].any (·.isPrefixOf head))

theorem matcher_closed :
    ProgramClosed matcherHeads CollectionOccurrenceMatcherExecution.library.runtime := by
  apply closed_of_all _ _ (by decide +kernel)
  decide +kernel

theorem matcher_agreement :
    ProgramAgreementOn matcherHeads CollectionOccurrenceMatcherExecution.library.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply (List.map_inj_right (fun _ _ same => equationData_injective same)).mp
    decide +kernel
  · decide +kernel

syntax "occurrence_from_publication% " "[" str,* "] " term:max : term
macro_rules
  | `(occurrence_from_publication% [$names,*] $fact) =>
    `(BridgeKit.transport_call publication_closed publication_agreement
      (by decide +kernel) (by decide) (by decide +kernel) (by decide)
      [$names,*] (by decide) (by rfl) (by decide +kernel) $fact)

syntax "occurrence_from_matcher% " "[" str,* "] " term:max : term
macro_rules
  | `(occurrence_from_matcher% [$names,*] $fact) =>
    `(BridgeKit.transport_call matcher_closed matcher_agreement
      (by decide +kernel) (by decide) (by decide +kernel) (by decide)
      [$names,*] (by decide) (by rfl) (by decide +kernel) $fact)

syntax "occurrence_from_preparation% " "[" str,* "] " term:max : term
macro_rules
  | `(occurrence_from_preparation% [$names,*] $fact) =>
    `(BridgeKit.Library.lift_call matchers_checked (by decide +kernel)
      (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
      (by rfl) (by decide +kernel)
      (BridgeKit.Library.lift_call installations_checked (by decide +kernel)
        (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
        (by rfl) (by decide +kernel)
        (BridgeKit.Library.lift_call batches_checked (by decide +kernel)
          (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
          (by rfl) (by decide +kernel)
          (BridgeKit.Library.lift_call continuations_checked (by decide +kernel)
            (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
            (by rfl) (by decide +kernel) $fact))))

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceRuntime
