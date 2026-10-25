import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
import Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges
open Bridges.IndexedContainerTraversal Folding

private structure Case where
  label : String
  expression : Atom
  expected : Atom

private def suiteCases (bundles : Bool) : List Case :=
  if bundles then
    Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal.executionControls.map
      fun control => ⟨control.label, control.expression, control.expected⟩
  else Folding.executionControls.map fun control => ⟨control.label, control.expression, control.expected⟩

private def packetName (bundles : Bool) : String := if bundles then "BundlePacket" else "FoldPacket"

private def answers? (bundles : Bool) (fuel : Nat) (expression : Atom) : Option (List Atom) :=
  let program := if bundles then IndexedContainerTraversal.library.runtime else Folding.library.runtime
  match Eval.evaluate program fuel Effects.empty expression with
  | .complete _ values [] [] => some values
  | _ => none

private def render (atom : Atom) : IO String :=
  match ReadAfterRender.render? atom with
  | some text => pure text
  | none => throw (IO.userError "fold control has no faithful source spelling")

private def firstFuel (bundles : Bool) (expression : Atom) : Nat → Nat → Nat → Nat
  | _, low, 0 => low
  | 0, low, _ => low
  | steps + 1, low, width + 1 =>
      let middle := low + (width + 1) / 2
      if (answers? bundles middle expression).isSome then
        firstFuel bundles expression steps low ((width + 1) / 2)
      else
        firstFuel bundles expression steps (middle + 1) (low + width - middle)

private def renderPackets (bundles : Bool) (controls : List Case) : IO String := do
  let mut text := ""
  for control in controls do
    text := text ++ (← render (.expression [.symbol (packetName bundles),
      .grounded (.string control.label), .expression [control.expected]])) ++ "\n"
  return text

private def generate (directory : System.FilePath) (bundles : Bool) : IO Unit := do
  let mut commands := ""
  let mut costs : Array Lean.Json := #[]
  for control in suiteCases bundles do
    let expression ← render control.expression
    let fuel := firstFuel bundles control.expression 20 0 30000
    unless answers? bundles fuel control.expression == some [control.expected] do
      throw (IO.userError s!"complete model result differs: {control.label}")
    unless fuel == 0 || (answers? bundles (fuel - 1) control.expression).isNone do
      throw (IO.userError "fold source-machine fuel is not minimal")
    commands := commands ++ "!(let $packet (collapse " ++ expression ++
      ") (println! (" ++ packetName bundles ++ " " ++ reprStr control.label ++ " $packet)))\n"
    costs := costs.push (Lean.Json.mkObj [
      ("case", .str control.label), ("input_characters", Lean.toJson expression.length),
      ("source_machine_steps", Lean.toJson fuel)])
  IO.FS.createDirAll directory
  let sourceText := if bundles then IndexedContainerTraversal.source.text else
    Folding.source.text ++ "\n" ++ methodsSource.text
  IO.FS.writeFile (directory / (if bundles then "bundle.metta" else "fold.metta"))
    (sourceText ++ "\n" ++ commands)
  IO.FS.writeFile (directory / "source-costs.json") ((Lean.Json.arr costs).pretty ++ "\n")
  IO.FS.writeFile (directory / "expected-packets.out") (← renderPackets bundles (suiteCases bundles))
  if bundles then
    let controls := suiteCases true
    let alter (label : String) (expected : Atom) := controls.map fun control =>
      if control.label == label then { control with expected } else control
    let vector := Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal.Canonical.observations
    let [first, second] := vector | throw (IO.userError "Vector control is not two-position")
    let .application "InductionPosition" [element, _] := first
      | throw (IO.userError "malformed first Vector observation")
    let .application "InductionPosition" [_, otherWitness] := second
      | throw (IO.userError "malformed second Vector observation")
    let changedWitness := Mettapedia.GSLT.LanguageDef.CettaWire.Term.application
      "InductionPosition" [element, otherWitness]
    let some swapped := controls.find? (·.label == "list-proof-swap")
      | throw (IO.userError "missing List witness-order control")
    for (name, altered) in [
      ("missing-occurrence", alter "vector"
        (Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal.result vector.tail)),
      ("reordered", alter "list-proof-order" swapped.expected),
      ("changed-witness", alter "vector"
        (Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal.result
          [changedWitness, second]))] do
      IO.FS.writeFile (directory / ("mutation-" ++ name ++ ".out")) (← renderPackets true altered)
  IO.println s!"Emitted {(suiteCases bundles).length} {packetName bundles} controls from the proved source"

private def check (path : System.FilePath) (bundles : Bool) : IO Unit := do
  let text ← IO.FS.readFile path
  let mut seen : List String := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith ("(" ++ packetName bundles) then
      let .ok [.expression [.symbol head, .grounded (.string label), .expression answers]] :=
          SpaceSemantics.readSource line
        | throw (IO.userError "malformed fold packet")
      unless head == packetName bundles do throw (IO.userError "wrong packet kind")
      if seen.contains label then throw (IO.userError "duplicate fold packet")
      let some control := (suiteCases bundles).find? (·.label == label)
        | throw (IO.userError "unknown fold packet")
      unless answers == [control.expected] do
        throw (IO.userError s!"wrong complete fold result: {label}")
      seen := label :: seen
    else if line != "" && line != "()" && line != "[()]" && line != "[]" &&
        line != "true" && line != "True" then
      throw (IO.userError s!"unexpected fold output: {line}")
  unless seen.length == (suiteCases bundles).length do throw (IO.userError "missing fold packet")
  IO.println s!"Accepted {seen.length} exact recursive-fold packets"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["emit", directory] => generate directory false
  | ["check", path] => check path false
  | ["emit", directory, "bundle"] => generate directory true
  | ["check", path, "bundle"] => check path true
  | _ => throw (IO.userError "usage: qualify_inductive_fold.lean emit DIRECTORY [bundle] | check OUTPUT [bundle]")
