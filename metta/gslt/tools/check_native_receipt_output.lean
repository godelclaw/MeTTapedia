import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls

def main (arguments : List String) : IO Unit := do
  let [output] := arguments
    | throw (IO.userError "usage: check_native_receipt_output.lean ENGINE_OUTPUT")
  let questions ← fixtures
  check questions (← IO.FS.readFile output)
