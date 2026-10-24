import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceInstallation

/-! # Native installation of fresh allocations into retained occurrence work -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionOccurrenceBatch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CollectionOccurrenceBatchExecution (frameTerm stateTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_install.metta"
    sha256 "d1892fde9b7cecf4f826095d08629fb0d65892dd0e7e1cedf4261ae601f18a85"

def library : BridgeKit.Library :=
  ⟨CollectionOccurrenceBatchExecution.library.runtime, source.program,
    ["gslt:occurrence-install:"]⟩

theorem checked : library.check = true := by decide +kernel

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State)
    (left right : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append"
        [encoded (encodeList encoder left), encoded (encodeList encoder right)])
      host (encoded (encodeList encoder (left ++ right))) := by
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked ["left", "right"]
      (CompleteExecution.complete_append_returns encoder host left right)
  have atBackend := by metta_lift CollectionMatcherBackendExecution.checked ["left", "right"] atBase
  have atContinuation := by
    metta_lift RecursiveCollectionContinuationExecution.checked ["left", "right"] atBackend
  have atBatch := by metta_lift CollectionOccurrenceBatchExecution.checked ["left", "right"] atContinuation
  metta_lift checked ["left", "right"] atBatch

@[metta_head "gslt:occurrence-install:append"]
theorem install_returns (host : Effects.State) {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}
    (allocations : List (Allocation plan bound expected sourcePattern))
    (batch : State plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-install:append"
        [encoded (encodeList frameTerm (allocations.map Frame.initial)), encoded (stateTerm batch)])
      host (encoded (stateTerm (batch.install allocations))) := by
  have joined := append_returns frameTerm host batch.frames (allocations.map Frame.initial)
  metta_call checked
  metta_eval [joined] with checked unfolding
    [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      State.install, stateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution
