import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource

/-! # Pinned target tests over complete reflective class receipts -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open scoped ProgramQuotation
open MeTTaIL CompleteExecution LibraryCheck

def helperSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rho_native_queries.metta"
    sha256 "f94da45dc7f3207de515d4b982931f2dc0ef168ec290fde26699c845e98679ad"

def helperLibrary : BridgeKit.Library :=
  ⟨runnerLibrary.runtime, helperSource.program, ["rho:native:"]⟩

private theorem scoped_kept : keptBy helperLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem typed_kept : keptBy helperLibrary GeneralTypedSiteExecution.source.program = true := by decide +kernel
private theorem descent_kept : keptBy helperLibrary descentSource.program = true := by decide +kernel
private theorem complete_kept : keptBy helperLibrary completeSource.program = true := by decide +kernel
private theorem laws_kept : keptBy helperLibrary lawsSource.program = true := by decide +kernel
private theorem canonical_kept : keptBy helperLibrary canonicalSource.program = true := by decide +kernel
private theorem runner_kept : keptBy helperLibrary runnerSource.program = true := by decide +kernel

theorem helpers_checked : helperLibrary.check = true := by
  refine check_of helperLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy helperLibrary ((((((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program).append completeSource.program).append
      lawsSource.program).append canonicalSource.program |>.append runnerSource.program) = true
  simp only [keptBy_append, scoped_kept, typed_kept, descent_kept, complete_kept, laws_kept,
    canonical_kept, runner_kept, Bool.and_true]
  decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
