import Mettapedia.Logic.Prolog.SourceTermOrderRegression

open Mettapedia.Logic.Prolog.SourceTermOrderRegression

def main : IO Unit := do
  for (label, result) in differentialRows do
    match result with
    | some rendered => IO.println s!"{label}={rendered}"
    | none => throw <| IO.userError s!"{label}: canonical runtime did not answer"
