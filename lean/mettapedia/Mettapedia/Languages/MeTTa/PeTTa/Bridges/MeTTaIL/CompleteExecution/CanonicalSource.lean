import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.LawsSource

/-!
# Canonical forms, as a MeTTa source

`gslt_canonical.metta` (canonical forms sorted by a name table, and the standard form followed by
the canonical form) loads over the collection laws (`LawsSource`). It is quoted, pinned and
checked as its own `BridgeKit.Library`, in the order the gate loads it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open scoped ProgramQuotation
open LibraryCheck

def canonicalSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_canonical.metta"
    sha256 "43e88bc231cafbcf276cdd566d90a9160634f9582539c4832a6e37f55af8c9c5"

/-- Canonical forms over the collection laws. -/
def canonicalLibrary : BridgeKit.Library := ⟨lawsLibrary.runtime, canonicalSource.program, ["gslt:canon:"]⟩

set_option maxRecDepth 100000

private theorem canonical_scoped : keptBy canonicalLibrary RuleExecutionProgram.scopedProgram = true := by
  decide +kernel
private theorem canonical_typed : keptBy canonicalLibrary GeneralTypedSiteExecution.source.program = true := by
  decide +kernel
private theorem canonical_descent : keptBy canonicalLibrary descentSource.program = true := by decide +kernel
private theorem canonical_complete : keptBy canonicalLibrary completeSource.program = true := by decide +kernel
private theorem canonical_laws : keptBy canonicalLibrary lawsSource.program = true := by decide +kernel

theorem canonical_checked : canonicalLibrary.check = true := by
  refine check_of canonicalLibrary (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  change keptBy canonicalLibrary ((((emptyProgram.append RuleExecutionProgram.scopedProgram).append
    GeneralTypedSiteExecution.source.program).append descentSource.program |>.append completeSource.program).append
      lawsSource.program) = true
  simp only [keptBy_append, canonical_scoped, canonical_typed, canonical_descent, canonical_complete, canonical_laws,
    Bool.and_true]
  decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
