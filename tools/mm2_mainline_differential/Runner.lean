import Mettapedia.Languages.ProcessCalculi.MORK.MM2MainlineReference

/-!
Run MM2 programs through the mainline model.  The input file holds programs, each
introduced by a line `=== name`; the output repeats each header followed by the model's
printed final space, `FAULT name`, or `FUEL`.

Usage, from the Lean package root: `lake env lean --run <this file> <programs> <fuel>`.
-/

open Mettapedia.Languages.ProcessCalculi.MORK.Mainline.Reference

/-- Split a file into named programs. -/
def splitPrograms (text : String) : List (String × String) :=
  let step := fun (state : List (String × List String)) (line : String) =>
    if line.startsWith "=== " then (line.drop 4 |>.toString, []) :: state
    else
      match state with
      | [] => state
      | (name, lines) :: rest => (name, line :: lines) :: rest
  ((text.splitOn "\n").foldl step []).reverse.map fun (name, lines) =>
    (name, "\n".intercalate lines.reverse)

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path, fuel] =>
      let text ← IO.FS.readFile path
      for (name, program) in splitPrograms text do
        IO.println s!"=== {name}"
        IO.println (runProgram fuel.toNat! program)
      return 0
  | _ =>
      IO.eprintln "usage: Runner <programs> <fuel>"
      return 2
