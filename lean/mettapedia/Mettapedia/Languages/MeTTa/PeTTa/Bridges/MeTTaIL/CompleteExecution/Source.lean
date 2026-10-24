import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution.Program

/-!
# The complete machine's MeTTa sources

The scheduled descent machine (`gslt_descent_execution.metta`) and the complete machine
(`gslt_complete.metta`), quoted and pinned, loaded over the scoped execution library and the typed
sites, in the order the gate loads them. Each layer is a `BridgeKit.Library` whose check the kernel
decides once.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open Eval (codeWithin)
open scoped ProgramQuotation

def descentSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_descent_execution.metta"
    sha256 "81c5696a7a0243c5fcf8ef6dc95d2cfc02931180504d9147ad2dcc4d056c3e31"

def completeSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_complete.metta"
    sha256 "cb2a0d48692a75fc555f4a2276b99bda8b60e98782742a370f59589311ac3ed0"

/-- The empty program. -/
def emptyProgram : Program := ⟨[], [], [], [], []⟩

/-- The scoped execution library, alone: its heads are proved with the same kit. -/
def scopedLibrary : BridgeKit.Library := ⟨emptyProgram, RuleExecutionProgram.scopedProgram, ["gslt:"]⟩

/-- The typed sites over the scoped execution library. -/
def typedLibrary : BridgeKit.Library :=
  ⟨scopedLibrary.runtime, GeneralTypedSiteExecution.source.program, ["gslt:sites:"]⟩

/-- The descent machine over the typed sites. -/
def descentLibrary : BridgeKit.Library := ⟨typedLibrary.runtime, descentSource.program, ["gslt:descent:"]⟩

/-- The complete machine over the descent machine. -/
def completeLibrary : BridgeKit.Library := ⟨descentLibrary.runtime, completeSource.program,
    ["gslt:deep:", "gslt:step:", "gslt:complete:", "gslt:equations:", "gslt:classes:"]⟩

/-- Everything the gate loads for the complete machine. -/
abbrev runtime : Program := completeLibrary.runtime

/-! ## The checks, decided by the kernel file by file -/

set_option maxRecDepth 100000

theorem scoped_checked : scopedLibrary.check = true := by decide +kernel

theorem typed_checked : typedLibrary.check = true := by decide +kernel

theorem descent_checked : descentLibrary.check = true := by decide +kernel

/-- The complete machine's base bodies call none of its heads, file by file. -/
private abbrev baseKept (program : Program) : Bool :=
  program.equations.all fun equation =>
    completeLibrary.inherited equation.head && codeWithin completeLibrary.inherited equation.body

private theorem scoped_kept : baseKept RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem typed_kept : baseKept GeneralTypedSiteExecution.source.program = true := by decide +kernel
private theorem descent_kept : baseKept descentSource.program = true := by decide +kernel

private theorem complete_source_ready :
    completeLibrary.inherited "let" = true ∧
    (completeSource.program.equations.all fun equation => completeLibrary.owns equation.head) = true ∧
    (completeSource.program.declarations.all fun declaration =>
      (BridgeKit.arrowHead declaration).all completeLibrary.owns) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem complete_checked : completeLibrary.check = true := by
  obtain ⟨binding, equations, declarations⟩ := complete_source_ready
  have base : (completeLibrary.base.equations.all fun equation =>
      completeLibrary.inherited equation.head && codeWithin completeLibrary.inherited equation.body) = true := by
    change baseKept ((scopedLibrary.runtime.append GeneralTypedSiteExecution.source.program).append
      descentSource.program) = true
    have first := scoped_kept
    have second := typed_kept
    have third := descent_kept
    simp only [baseKept, scopedLibrary, emptyProgram, BridgeKit.Library.runtime, SpaceSemantics.Program.append,
      List.all_append, List.nil_append, Bool.and_eq_true] at first second third ⊢
    exact ⟨⟨first, second⟩, third⟩
  simp only [BridgeKit.Library.check, Bool.and_eq_true]
  exact ⟨⟨⟨binding, base⟩, equations⟩, declarations⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
