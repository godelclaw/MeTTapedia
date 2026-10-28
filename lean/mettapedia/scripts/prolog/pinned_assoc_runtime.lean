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

private def valueIdentity : SourceSignature.Variable := {
  spelling := "Value"
  occurrence := 0
}

private def keyIdentity : SourceSignature.Variable := {
  spelling := "Key"
  occurrence := 0
}

private def listIdentity : SourceSignature.Variable := {
  spelling := "List"
  occurrence := 0
}

private def oldIdentity : SourceSignature.Variable := {
  spelling := "Old"
  occurrence := 0
}

private def seenIdentity : SourceSignature.Variable := {
  spelling := "Seen"
  occurrence := 0
}

private def renderAtoms (program : SourceSignature.Program) (label : String)
    (goal : SourceSignature.Goal)
    (identity : SourceSignature.Variable) : IO Unit :=
  match SourceRuntimeRegression.runAtomsFor program
      goal identity with
  | some (answers, 0, 0) =>
      IO.println s!"{label}=[{String.intercalate "," answers}]"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError
        s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

private def renderAtomBags (program : SourceSignature.Program) (label : String)
    (goal : SourceSignature.Goal)
    (identity : SourceSignature.Variable) : IO Unit :=
  match SourceRuntimeRegression.runAtomBagsFor program goal identity with
  | some (bags, 0, 0) =>
      let rendered := bags.map fun bag =>
        s!"[{String.intercalate "," bag}]"
      IO.println s!"{label}=[{String.intercalate "," rendered}]"
  | some (_, heapSize, trailSize) =>
      throw <| IO.userError
        s!"{label}: cleanup left heap={heapSize}, trail={trailSize}"
  | none => throw <| IO.userError s!"{label}: runtime did not close"

private def lookup (key : String) : SourceSignature.Goal :=
  SourceSignature.call "get_assoc" [atom key, tree, var "Value" 0]

private def updateLookup : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "get_assoc"
      [atom "a", tree, var "Old" 0, var "Updated" 0, atom "updated"])
    (SourceSignature.call "get_assoc"
      [atom "a", var "Updated" 0, var "Seen" 0])

private def insertedTree : SourceSignature.Term := var "Inserted" 0

private def insertLookup : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "put_assoc"
      [atom "x", tree, atom "middle", insertedTree])
    (SourceSignature.call "get_assoc"
      [atom "x", insertedTree, var "Seen" 0])

private def insertKeys : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "put_assoc"
      [atom "x", tree, atom "middle", insertedTree])
    (SourceSignature.call "assoc_to_keys"
      [insertedTree, var "List" 0])

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
  renderAtoms unit.program "root" (lookup "m") valueIdentity
  renderAtoms unit.program "left" (lookup "a") valueIdentity
  renderAtoms unit.program "right" (lookup "z") valueIdentity
  renderAtoms unit.program "missing" (lookup "x") valueIdentity
  renderAtomBags unit.program "keys"
    (SourceSignature.call "assoc_to_keys" [tree, var "List" 0]) listIdentity
  renderAtomBags unit.program "values"
    (SourceSignature.call "assoc_to_values" [tree, var "List" 0]) listIdentity
  renderAtoms unit.program "generated_keys"
    (SourceSignature.call "gen_assoc"
      [var "Key" 0, tree, var "GeneratedValue" 0]) keyIdentity
  renderAtoms unit.program "min_key"
    (SourceSignature.call "min_assoc"
      [tree, var "Key" 0, var "Value" 0]) keyIdentity
  renderAtoms unit.program "min_value"
    (SourceSignature.call "min_assoc"
      [tree, var "Key" 0, var "Value" 0]) valueIdentity
  renderAtoms unit.program "max_key"
    (SourceSignature.call "max_assoc"
      [tree, var "Key" 0, var "Value" 0]) keyIdentity
  renderAtoms unit.program "max_value"
    (SourceSignature.call "max_assoc"
      [tree, var "Key" 0, var "Value" 0]) valueIdentity
  renderAtoms unit.program "update_old" updateLookup oldIdentity
  renderAtoms unit.program "update_new" updateLookup seenIdentity
  renderAtoms unit.program "insert_lookup" insertLookup seenIdentity
  renderAtomBags unit.program "insert_keys" insertKeys listIdentity
