import Mettapedia.Logic.Prolog.SourceRuntimeRegression

/-!
Executable half of the known `throw(Variable)` divergence.  This is not part
of the matched control differential: it pins the current Lean behavior so the
boundary cannot disappear from reports merely because both sides stop being
run together.
-/

open Mettapedia.Logic.Prolog.SourceRuntimeRegression

def main : IO Unit :=
  match runCount [] throwVariableCurrentlyAccepted with
  | some (1, 0, 0) => IO.println "throw_variable=accepted"
  | _ => throw <| IO.userError "throw-variable boundary changed"
