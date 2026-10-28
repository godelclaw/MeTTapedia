import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-! The snapshot library is ordinary MeTTa loaded over the common runtime.
Its source is retained verbatim. Local execution lemmas concern that source,
not a second implementation of the loop. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_snapshot_closure.metta"
  sha256 "218414e7a7db53f0237aad266f2bda83e802bbd1b4b94365f4a73a7a6e69102d"

def library : Library := ⟨CompleteEmission.runtime,source.program,["gslt:snapshot:"]⟩
def runtime := library.runtime

theorem checked : library.check = true := by decide +kernel

def factsTerm (facts : List Pattern) : Term := encodeList InferenceCettaWire.encodePattern facts
def rowsTerm (relation : String) (facts : List Pattern) : Term :=
  encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm
    (facts.map fun fact => ⟨relation,[fact]⟩)

theorem rows_returns (state : State) (relation : String) : ∀ facts : List Pattern,
    PureReturns runtime [] state (apply "gslt:snapshot:rows" [encoded (.string relation),encoded (factsTerm facts)])
      state (encoded (rowsTerm relation facts)) := by
  intro facts
  induction facts with
  | nil =>
    metta_call checked
    metta_eval with checked unfolding [factsTerm,rowsTerm,PremiseOperationsExecution.GeneralExecution.providerRowTerm,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,InferenceCettaWire.encodePatterns]
  | cons fact rest ih =>
    metta_call checked
    metta_eval [ih] with checked unfolding [factsTerm,rowsTerm,PremiseOperationsExecution.GeneralExecution.providerRowTerm,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,InferenceCettaWire.encodePatterns]

#print axioms checked
#print axioms rows_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
