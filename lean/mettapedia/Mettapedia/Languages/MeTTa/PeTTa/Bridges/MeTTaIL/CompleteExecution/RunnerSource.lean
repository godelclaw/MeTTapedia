import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CanonicalSource

/-!
# The runner, as a MeTTa source

`gslt_runner.metta` (whole runs, fair exploration and the explored transition graph, in
standard, canonical, reflective or model form) loads over the canonical forms (`CanonicalSource`). It is
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
    sha256 "789ec3c0ffd669b350153d43be8b259ad070231e20b08ee9e2ab3fb0ff50c0a2"

/-- The runner over the canonical forms. -/
def runnerLibrary : BridgeKit.Library :=
  ⟨canonicalLibrary.runtime, runnerSource.program, ["gslt:runner:", "gslt:explore:"]⟩

set_option maxRecDepth 100000

private theorem runner_scoped : keptBy runnerLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem runner_typed : keptBy runnerLibrary GeneralTypedSiteExecution.source.program = true := by
  decide +kernel
private theorem runner_descent : keptBy runnerLibrary descentSource.program = true := by decide +kernel
private theorem runner_complete : keptBy runnerLibrary completeSource.program = true := by decide +kernel
private theorem runner_laws : keptBy runnerLibrary lawsSource.program = true := by decide +kernel
private theorem runner_canonical : keptBy runnerLibrary canonicalSource.program = true := by decide +kernel

theorem runner_checked : runnerLibrary.check = true := by
  refine check_of runnerLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy runnerLibrary (((((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program |>.append completeSource.program).append
      lawsSource.program).append canonicalSource.program) = true
  simp only [keptBy_append, runner_scoped, runner_typed, runner_descent, runner_complete, runner_laws,
    runner_canonical, Bool.and_true]
  decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
