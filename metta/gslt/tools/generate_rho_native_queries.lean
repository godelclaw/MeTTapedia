import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [modulePath, output] =>
    emitModule modulePath
    IO.FS.writeFile output (← generate)
  | ["resume", input, output] =>
    IO.FS.writeFile output (← generateResume (← IO.FS.readFile input))
  | _ => throw (IO.userError
    "usage: generate_rho_native_queries.lean MODULE.metta OUTPUT.metta | resume FIRST_OUTPUT OUTPUT.metta")
