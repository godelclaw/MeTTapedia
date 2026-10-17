import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source

/-!
# The collection laws and the runner, as MeTTa sources

`gslt_collection_laws.metta` (the standard form of declared collection and scope-extrusion
laws) loads over the complete machine, and `gslt_runner.metta` (whole runs and fair exploration
in standard form) loads over both. Each file is quoted, pinned and checked as its own
`BridgeKit.Library`, in the order the gate loads them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open Eval (codeWithin)
open scoped ProgramQuotation

def lawsSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_collection_laws.metta"
    sha256 "24a3e67c782270ba3ac7633d38c91b76ec14b2d4bd37269f811776e64fd30212"

def runnerSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_runner.metta"
    sha256 "270fd4f93c1c9795e9313c6cda5b8542e6633aaae01896fd1ca849600cb69aea"

/-- The collection laws over the complete machine. -/
def lawsLibrary : BridgeKit.Library := ⟨completeLibrary.runtime, lawsSource.program, ["gslt:laws:"]⟩

/-- The runner over the collection laws. -/
def runnerLibrary : BridgeKit.Library :=
  ⟨lawsLibrary.runtime, runnerSource.program, ["gslt:runner:", "gslt:explore:"]⟩

/-! ## The checks, decided by the kernel file by file -/

set_option maxRecDepth 100000

/-- A program's bodies keep to the heads a library inherits. -/
private abbrev keptBy (L : BridgeKit.Library) (program : Program) : Bool :=
  program.equations.all fun equation => L.inherited equation.head && codeWithin L.inherited equation.body

private theorem keptBy_append (L : BridgeKit.Library) (first second : Program) :
    keptBy L (first.append second) = (keptBy L first && keptBy L second) := by
  simp [keptBy, SpaceSemantics.Program.append, List.all_append]

/-- A library's check, from its own source and its base file by file. -/
private theorem check_of (L : BridgeKit.Library) (binding : L.inherited "let" = true)
    (base : keptBy L L.base = true)
    (equations : (L.source.equations.all fun equation => L.owns equation.head) = true)
    (declarations : (L.source.declarations.all fun declaration =>
      (BridgeKit.arrowHead declaration).all L.owns) = true) : L.check = true := by
  simp only [BridgeKit.Library.check, Bool.and_eq_true]
  exact ⟨⟨⟨binding, base⟩, equations⟩, declarations⟩

private theorem laws_scoped : keptBy lawsLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem laws_typed : keptBy lawsLibrary GeneralTypedSiteExecution.source.program = true := by
  decide +kernel
private theorem laws_descent : keptBy lawsLibrary descentSource.program = true := by decide +kernel
private theorem laws_complete : keptBy lawsLibrary completeSource.program = true := by decide +kernel

theorem laws_checked : lawsLibrary.check = true := by
  refine check_of lawsLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy lawsLibrary (((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program |>.append completeSource.program) = true
  simp only [keptBy_append, laws_scoped, laws_typed, laws_descent, laws_complete, Bool.and_true]
  decide

private theorem runner_scoped : keptBy runnerLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem runner_typed : keptBy runnerLibrary GeneralTypedSiteExecution.source.program = true := by
  decide +kernel
private theorem runner_descent : keptBy runnerLibrary descentSource.program = true := by decide +kernel
private theorem runner_complete : keptBy runnerLibrary completeSource.program = true := by decide +kernel
private theorem runner_laws : keptBy runnerLibrary lawsSource.program = true := by decide +kernel

theorem runner_checked : runnerLibrary.check = true := by
  refine check_of runnerLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy runnerLibrary ((((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program |>.append completeSource.program).append
      lawsSource.program) = true
  simp only [keptBy_append, runner_scoped, runner_typed, runner_descent, runner_complete, runner_laws, Bool.and_true]
  decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
