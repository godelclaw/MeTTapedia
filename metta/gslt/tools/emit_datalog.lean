import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

/-! Compile an explicitly selected shared-parser packet for ordinary source.
The emitter prepares rules and scalar operations; inference runs in MeTTa. -/

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.Datalog
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL Syntax

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def inputs (program : Program) (directory : System.FilePath) : IO (List GroundFact) := do
  let mut facts := []
  for statement in program.statements do
    if let .input name := statement then
      let some types := ProgramStatic.signature program name | throw (IO.userError "undeclared input")
      let text ← IO.FS.readFile (directory / (String.intercalate "." name ++ ".facts"))
      for line in text.splitOn "\n" do
        if !line.isEmpty then
          let fields := line.splitOn "\t"
          unless fields.length == types.length do throw (IO.userError "input field count mismatch")
          let values ← (fields.zip types).mapM fun (field,kind) => match kind with
            | .symbol => pure (.symbol field)
            | .number => match field.toInt? with
              | some value => pure (.number value) | none => throw (IO.userError "invalid signed input")
            | .unsigned => match field.toNat? with
              | some value => pure (.unsigned value) | none => throw (IO.userError "invalid unsigned input")
            | .floating => throw (IO.userError "floating inputs require a declared floating profile")
          facts := facts ++ [⟨name,values⟩]
  pure facts

def main (arguments : List String) : IO Unit := do
  let [sourcePath,packetPath,inputDirectory,outputPath,entry] := arguments
    | throw (IO.userError "expected source, selected packet, fact directory, output and entry name")
  let input ← IO.FS.readFile sourcePath
  let packet ← IO.FS.readFile packetPath
  let .ok [tree] := SpaceSemantics.readSource packet | throw (IO.userError "parser packet is malformed or ambiguous")
  let program ← match SouffleDatalog.Frontend.read input tree with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let seeds ← inputs program inputDirectory
  let prepared ← match Executable.prepare program seeds with
    | .ok prepared => pure prepared
    | .error reason => throw (IO.userError reason)
  let spec := ClosureMachine.spec prepared prepared.seedFacts
  let .ok _ := CompleteEmission.emitText? spec entry .classes
    | throw (IO.userError s!"GSLT execution admission refused: {reprStr spec.plan.obligations}")
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes [] (.base "DlStatement")).render
  let standard := (ClosureMachine.standardTerm prepared).render
  let source := CettaWire.Term.render (InferenceCettaWire.encodePattern (Executable.request prepared.vocabulary))
  let metadata := (ClosureMachine.metadataTerm prepared).render
  let static := (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows).render
  let facts := (encodeList InferenceCettaWire.encodePattern prepared.seedFacts).render
  let declarations := "(: " ++ entry ++ ":begin (-> %Undefined%))\n" ++
    "(= (" ++ entry ++ ":begin) (let* (($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++
    ")) ($source (quote " ++ source ++ ")) ($metadata (quote " ++ metadata ++ ")) ($static (quote " ++ static ++
    ")) ($facts (quote " ++ facts ++ "))) (gslt:snapshot:begin $plan $standard $source $metadata " ++ reprStr Query.factRelation ++ " $static $facts)))\n" ++
    "(: " ++ entry ++ ":run (-> Atom Atom %Undefined%))\n" ++
    "(= (" ++ entry ++ ":run $ticks $quantum) (let $initial (" ++ entry ++ ":begin) (gslt:snapshot:advance $initial $ticks $quantum)))\n" ++
    "(: " ++ entry ++ ":resume (-> Atom Atom Atom %Undefined%))\n" ++
    "(= (" ++ entry ++ ":resume $machine $ticks $quantum) (gslt:snapshot:advance $machine $ticks $quantum))\n"
  let sources := RuleExecutionProgram.scopedSource :: CollectionOccurrenceSearchExecution.SelectedNativeSource.sources
  IO.FS.writeFile outputPath (String.intercalate "\n" (sources.map (·.text)) ++ "\n" ++
    SnapshotClosureExecution.source.text ++ "\n" ++ declarations)
  let dictionary := Executable.dictionary prepared.vocabulary
  let decoded := CettaWire.encodeList (fun (name,value) => Term.application "Binding"
    [.string name,InferenceCettaWire.encodePattern value]) dictionary
  IO.FS.writeFile (outputPath ++ ".dictionary.metta") decoded.render
  IO.println s!"compiled ordinary Datalog: {program.statements.length} statements, {prepared.compiled.rewrites.length} rules, {seeds.length} input facts"
