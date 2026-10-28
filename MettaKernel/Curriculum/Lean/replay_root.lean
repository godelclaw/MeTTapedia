import Lean4Lean.Replay

/-!
External replay oracle for one elaborated declaration and its dependency closure.
Checks the closure in a fresh Lean4Lean environment, comparing each admission
with Lean's kernel. This executable is not a proof of checker soundness and
does not read or certify a separately serialized NDJSON/S-expression artifact.
-/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleName, rootName] := args
    | throw (IO.userError "expected module and declaration")
  let mod := moduleName.toName
  let root := rootName.toName
  initSearchPath (← findSysroot)
  let count ← Lean.withImportModules #[mod] {} (trustLevel := 0) fun env => do
    let some declaration := env.find? root
      | throw (IO.userError "requested declaration is absent")
    if declaration.isUnsafe || declaration.isPartial then
      throw (IO.userError "requested declaration is unsafe or partial")
    let context : Lean4Lean.Replay.Context :=
      { newConstants := env.constants.map₁, compare := true, checkQuot := false }
    let (count, checked) ← Lean4Lean.Replay.replay context (.empty mod) (some root)
    unless (checked.find? root).isSome do
      throw (IO.userError "requested declaration was not replayed")
    return count
  IO.println (Json.mkObj [("accepted", toJson count), ("root", toJson rootName),
    ("mode", toJson "fresh-dependency-closure-with-official-comparison")]).compress
  return 0
