import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.LawsSource

/-! # Pinned target tests over complete reflective class receipts -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open scoped ProgramQuotation
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.LibraryCheck

def helperSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rho_native_queries.metta"
    sha256 "41ee1611d31187895a2c3340f8e4a05fe19f3a060c81833b12169d2a6caf9144"

def helperLibrary : BridgeKit.Library :=
  ⟨runnerLibrary.runtime, helperSource.program, ["rho:native:"]⟩

private theorem runner_kept : keptBy helperLibrary runnerLibrary.runtime = true := by
  decide +kernel

theorem helpers_checked : helperLibrary.check = true := by
  exact check_of helperLibrary (by decide +kernel) runner_kept
    (by decide +kernel) (by decide +kernel)

#print axioms helpers_checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
