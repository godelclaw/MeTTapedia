import Mettapedia.Logic.Prolog.ReaderProgram
import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.SourceRuntime

/-!
Load the pinned `spaces.pl` source through the canonical reader and execute
its real `add_sexp/2` clause through the shared Logic/LP/Prolog runtime.
-/

open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.SourceSignature

def testGoal : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "add_sexp"
      [atom "space", list [atom "rel", atom "a"]])
    (SourceSignature.call "space" [atom "rel", atom "a"])

def countAnswers : Nat -> Nat -> SourceRuntime.Session -> Option Nat
  | 0, _, _ => none
  | fuel + 1, count, session =>
      match SourceRuntime.pullSession 1024 session with
      | .open _ => none
      | .answer _ next => countAnswers fuel (count + 1) next
      | .terminal (.completed memory) _ =>
          if memory.heap.isEmpty && memory.trail.isEmpty then some count
          else none
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none

def main (arguments : List String) : IO Unit := do
  let [path] := arguments
    | throw <| IO.userError "usage: pinned_spaces_runtime <spaces.pl>"
  let source <- IO.FS.readFile path
  let loaded <- match ReaderProgram.loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults source with
    | .ok result => pure result
    | .error _ => throw <| IO.userError "strict source loading failed"
  let session <- match SourceRuntime.openEmpty loaded.program testGoal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "source runtime failed to open"
  match countAnswers 16 0 session with
  | some count => IO.println s!"spaces_add={count}"
  | none => throw <| IO.userError "source runtime did not close cleanly"
