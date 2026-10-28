import Mettapedia.Logic.Prolog.ReaderDCG
import Mettapedia.Logic.Prolog.ReaderSWIProfile

/-!
Executable coverage driver for every DCG rule in pinned PeTTa's parser files.
It reports expanded head indicators in source order; no alternative syntax or
runtime is introduced.
-/

open Mettapedia.Logic.Prolog

def checkForms (label : String) : Nat -> List ReaderSource.Form -> IO Nat
  | _, [] => pure 0
  | index, .dcg head body :: rest => do
      let clause <- match ReaderDCG.expand head body with
        | .ok clause => pure clause
        | .error _ => throw <| IO.userError s!"{label}: DCG expansion failed"
      IO.println s!"{label}:{index}={clause.head.symbol.name}/{clause.head.symbol.arity}"
      return (← checkForms label (index + 1) rest) + 1
  | index, _ :: rest => checkForms label index rest

def checkFile (label path : String) : IO Nat := do
  let source <- IO.FS.readFile path
  let loaded <- match ReaderLoader.loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults source with
    | .ok result => pure result
    | .error _ => throw <| IO.userError s!"{label}: source loading failed"
  checkForms label 0 loaded.forms

def main (arguments : List String) : IO Unit := do
  let [parserPath, fileReaderPath] := arguments
    | throw <| IO.userError
        "usage: pinned_dcg_expansion <parser.pl> <filereader.pl>"
  let parserCount <- checkFile "parser" parserPath
  let fileReaderCount <- checkFile "filereader" fileReaderPath
  IO.println s!"total={parserCount + fileReaderCount}"
