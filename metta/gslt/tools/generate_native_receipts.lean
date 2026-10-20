import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls

def main (arguments : List String) : IO Unit := do
  let questions ← fixtures
  match arguments with
  | [output] => IO.FS.writeFile output (← generate questions)
  | [input, output] => IO.FS.writeFile output (← generateResume questions (← IO.FS.readFile input))
  | _ => throw (IO.userError "usage: generate_native_receipts.lean [FIRST_OUTPUT] OUTPUT.metta")
  IO.println s!"Generated {questions.length} native questions"
