import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core

/-!
# Collection source inventory in the common runtime

The four collection source artifacts are already included in the shared
interpreted program. This owner records their inventory and exposes the same
checked runtime without loading their clauses a second time.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)

/-- The allocator, machine, logged search and post-match source artifacts. -/
def collectionSupportProgram : Program :=
  (((RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide)).program.append
    (RuleExecutionProgram.interpretedPremiseSupportSources[6]'(by decide)).program).append
      (RuleExecutionProgram.interpretedPremiseSupportSources[7]'(by decide)).program).append
        (RuleExecutionProgram.interpretedPremiseSupportSources[8]'(by decide)).program

def collectionBaseLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

theorem collection_base_checked : collectionBaseLibrary.check = true :=
  RetainedMatchingWire.interpreted_checked

theorem collection_base_runtime : collectionBaseLibrary.runtime =
    RuleExecutionProgram.interpretedPremiseProgram := RetainedMatchingWire.interpreted_runtime

#print axioms collection_base_checked
#print axioms collection_base_runtime

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
