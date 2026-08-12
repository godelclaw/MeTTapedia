import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderUnit
import Mettapedia.Logic.Prolog.SourceRuntimeRegression

/-! Execute the selected portable arm of pinned SWI `library(assoc)` through
the canonical source reader and shared Logic/LP/Prolog runtime. -/

open Mettapedia.Logic.Prolog
open SourceSignature

private def leaf (key value : String) : SourceSignature.Term :=
  compound "t" [atom key, atom value, atom "-", atom "t", atom "t"]

private def tree : SourceSignature.Term :=
  compound "t" [atom "m", atom "root", atom "-",
    leaf "a" "left", leaf "z" "right"]

private def answerIdentity : SourceSignature.Variable := {
  spelling := "Value"
  occurrence := 0
}

private def render (program : SourceSignature.Program)
    (label key : String) : IO Unit :=
  match SourceRuntimeRegression.runAtomsFor program
      (SourceSignature.call "get_assoc" [atom key, tree, var "Value" 0])
      answerIdentity with
  | some (answers, 0, 0) =>
      IO.println s!"{label}=[{String.intercalate "," answers}]"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError
        s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

def main (arguments : List String) : IO Unit := do
  let [assocPath] := arguments
    | throw <| IO.userError "usage: pinned_assoc_runtime <assoc.pl>"
  let source <- IO.FS.readFile assocPath
  let unit <- match ReaderUnit.loadConditionalSourceWith
      ReaderSWIProfile.pinnedPeTTaCondition
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults source with
    | .ok unit => pure unit
    | .error _ => throw <| IO.userError "conditional source loading failed"
  render unit.program "root" "m"
  render unit.program "left" "a"
  render unit.program "right" "z"
  render unit.program "missing" "x"
