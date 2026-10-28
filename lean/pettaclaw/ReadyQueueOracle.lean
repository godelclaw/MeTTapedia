import ReadyQueue

/-! Streaming comparator for the native ready-order fixture. Its output is
computed from the same definitions used in the proved contract. This finite
differential check does not prove the C implementation for arbitrary inputs. -/

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut state : ReadyQueue.State := ⟨0, []⟩
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let parts := line.trimAscii.toString.splitOn " "
    let mut observation : ReadyQueue.Observation := ⟨0, none⟩
    match parts with
    | [command, argument] =>
      let some id := argument.toNat? | throw (IO.userError "invalid task")
      if command == "reset" then state := ⟨id, []⟩
      else
        let action ← match command with
          | "admit" => pure (ReadyQueue.Action.admit id)
          | "remove" => pure (ReadyQueue.Action.remove id)
          | "visit" => pure ReadyQueue.Action.visit
          | _ => throw (IO.userError "invalid operation")
        let result := ReadyQueue.step state action
        observation := result.1
        state := result.2
    | _ => throw (IO.userError "invalid command")
    let visited := observation.visited.map toString |>.getD "-1"
    output.putStrLn (String.intercalate " "
      ([toString observation.status, visited] ++ state.tasks.map toString))
