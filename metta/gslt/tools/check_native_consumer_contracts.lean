import Mettapedia.OSLF.NativeTypes.Consumers
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendControls

/-! Run the finite consumer controls and qualify complete native-query output. -/

open Mettapedia.OSLF.NativeTypes.Consumers

private def checkGroup (label : String) (checks : List (String × Bool)) : IO Unit := do
  for (name, accepted) in checks do
    if !accepted then throw (IO.userError (label ++ ": " ++ name))
  IO.println s!"{label}: {checks.length} controls passed"

open MM2Batch MM2BatchControls
  Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls
  Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls in
private def checkMM2 : IO Unit := do
  checkGroup "MM2 complete publication"
    [("one private answer stays unknown", decide
       (summary (check .sinkMajor .leaveInert joinSource target checkpoint100 0) = (.unknown, 100, 0))),
     ("all answers before exhaustion stay unknown", decide
       (summary (check .sinkMajor .leaveInert joinSource target checkpoint100 50) = (.unknown, 150, 0))),
     ("complete batch retains both origins", decide
       (summary (check .sinkMajor .leaveInert joinSource target checkpoint100 100) = (.proved, 177, 2))),
     ("stale snapshot", decide
       (summary (check .sinkMajor .leaveInert (.symbol "changed" :: joinSource) target checkpoint100 100) =
         (.refuted, 0, 0))),
     ("wrong target", decide
       (summary (check .sinkMajor .leaveInert joinSource [] checkpoint100 100) = (.refuted, 0, 0))),
     ("row-major target", decide
       (summary (check .rowMajor .leaveInert rowSource rowTarget rowCheckpoint 100) = (.proved, 30, 2))),
     ("sink-major target", decide
       (summary (check .sinkMajor .leaveInert rowSource sinkTarget rowCheckpoint 100) = (.proved, 30, 2))),
     ("row-major excludes sink-major target", decide
       (summary (check .rowMajor .leaveInert rowSource sinkTarget rowCheckpoint 100) = (.refuted, 0, 0))),
     ("sink-major excludes row-major target", decide
       (summary (check .sinkMajor .leaveInert rowSource rowTarget rowCheckpoint 100) = (.refuted, 0, 0)))]

def main (args : List String) : IO Unit := do
  checkGroup "Dependent typed-step contracts" DependentChecking.Controls.verdicts
  MM0Admission.Controls.run
  checkMM2
  checkGroup "MeTTa space source occurrences" MeTTaSpace.Controls.verdicts
  checkGroup "MeTTa space shared spatial checker" MeTTaSpaceSpatial.Controls.checks
  checkGroup "Authored append shared spatial checker"
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend.Controls.checks
  let store := PLNEvidence.Controls.store
  checkGroup "PLN identified evidence"
    [("disjoint", PLNEvidence.check store PLNEvidence.Controls.disjointRequest),
     ("shared support", !PLNEvidence.check store PLNEvidence.Controls.sharedRequest),
     ("repeated input", !PLNEvidence.check store PLNEvidence.Controls.repeatedRequest),
     ("malformed counts", !PLNEvidence.check store PLNEvidence.Controls.malformedRequest),
     ("reused origin", !PLNEvidence.check store PLNEvidence.Controls.reusedOriginRequest),
     ("absent input", !PLNEvidence.check store PLNEvidence.Controls.absentRequest),
     ("reverse parents", PLNEvidence.check store PLNEvidence.Controls.reverseRequest)]
  for path in args do
    let label := (System.FilePath.mk path).fileName.getD "output"
    IO.println s!"Qualifying runtime output: {label}"
    ExecutorQualification.Controls.checkOutput (← IO.FS.readFile path)
