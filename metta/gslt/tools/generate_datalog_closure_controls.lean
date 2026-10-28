import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureWire
import Mettapedia.Languages.Datalog.ClosureCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosurePlanExecution
import Lean.Data.Json.Printer

open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL Syntax

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace DatalogClosureControls

def reachability : Program := ⟨[
  .declaration ⟨["Edge"],[⟨"source",.symbol⟩,⟨"target",.symbol⟩]⟩,
  .input ["Edge"],
  .declaration ⟨["Reach"],[⟨"source",.symbol⟩,⟨"target",.symbol⟩]⟩,
  .rule ⟨⟨["Reach"],[.var "X",.var "Y"]⟩,[.atom ⟨["Edge"],[.var "X",.var "Y"]⟩]⟩,
  .rule ⟨⟨["Reach"],[.var "X",.var "Z"]⟩,
    [.atom ⟨["Reach"],[.var "X",.var "Y"]⟩,.atom ⟨["Edge"],[.var "Y",.var "Z"]⟩]⟩,
  .output ["Reach"]]⟩

def edge (a b : String) : GroundFact := ⟨["Edge"],[.symbol a,.symbol b]⟩
def suites : List (String × Program × List GroundFact) :=
  [("chain",reachability,[edge "a" "b",edge "b" "c",edge "c" "d"]),
   ("cycle",reachability,[edge "a" "b",edge "b" "c",edge "c" "a"]),
   ("diamond",reachability,[edge "a" "b",edge "b" "d",edge "a" "c",edge "c" "d"]),
   ("duplicates",reachability,[edge "a" "b",edge "a" "b",edge "b" "c"]),
   ("empty",reachability,[])]

def readInputs (program : Program) (directory : System.FilePath) : IO (List GroundFact) := do
  let mut facts := []
  for statement in program.statements do
    if let .input name := statement then
      let some types := ProgramStatic.signature program name
        | throw (IO.userError "undeclared input relation")
      let text ← IO.FS.readFile (directory / (String.intercalate "." name ++ ".facts"))
      for line in text.splitOn "\n" do
        if !line.isEmpty then
          let columns := line.splitOn "\t"
          unless columns.length == types.length do throw (IO.userError "input arity mismatch")
          let values ← (columns.zip types).mapM fun (column,type) => match type with
            | .symbol => pure (.symbol column)
            | .number => match column.toInt? with
              | some value => pure (.number value) | none => throw (IO.userError "invalid signed input")
            | .unsigned => match column.toNat? with
              | some value => pure (.unsigned value) | none => throw (IO.userError "invalid unsigned input")
            | .floating => throw (IO.userError "floating input needs a declared floating profile")
          facts := facts ++ [⟨name,values⟩]
  pure facts

def control (label : String) (prepared : Executable.Prepared) (ticks quantum : Nat)
    (expected : ClosureMachine.Machine prepared) : String :=
  let spec := ClosureMachine.spec prepared prepared.seedFacts
  let initial := ClosureMachine.begin prepared
  let first := if ticks == 0 then 0 else 1
  let remaining := ticks - first
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes [] (.base "DlStatement")).render
  let source := CettaWire.Term.render (InferenceCettaWire.encodePattern (Executable.request prepared.vocabulary))
  let static := (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows).render
  let facts := (encodeList InferenceCettaWire.encodePattern prepared.seedFacts).render
  "!(let* (($plan (quote " ++ plan ++ ")) ($standard (quote " ++ (ClosureMachine.standardTerm prepared).render ++
  ")) ($source (quote " ++ source ++ ")) ($metadata (quote " ++ (ClosureMachine.metadataTerm prepared).render ++
  ")) ($static (quote " ++ static ++ ")) ($facts (quote " ++ facts ++ "))" ++
  " ($initial (gslt:snapshot:begin $plan $standard $source $metadata " ++ reprStr Query.factRelation ++ " $static $facts))" ++
  " ($result (gslt:snapshot:advance $initial " ++ toString ticks ++ " " ++ toString quantum ++ "))" ++
  " ($partial (gslt:snapshot:advance $initial " ++ toString first ++ " " ++ toString quantum ++ "))" ++
  " ($resumed (gslt:snapshot:advance $partial " ++ toString remaining ++ " " ++ toString quantum ++ "))" ++
  " ($observed (gslt:snapshot:result $result)))" ++
  " (println! (DatalogClosureControl " ++ reprStr label ++
  " (== $initial (quote " ++ (ClosureMachine.machineTerm prepared initial).render ++ "))" ++
  " (== $result (quote " ++ (ClosureMachine.machineTerm prepared expected).render ++ "))" ++
  " (== $resumed (quote " ++ (ClosureMachine.machineTerm prepared expected).render ++ "))" ++
  " (== $observed (quote " ++ (ClosureMachine.resultTerm prepared expected).render ++ ")))))"

def providerControl (label : String) (prepared : Executable.Prepared) (facts : List Pattern) : String :=
  let plan := CompletePlanWire.planTerm (Executable.plan prepared prepared.seedFacts)
    (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")
  let expectedPlan := if ClosureMachine.closed prepared facts then
    some (CompletePlanWire.planTerm (Executable.plan prepared facts)
      (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")) else none
  let rows := SnapshotClosureExecution.rowsTerm Query.factRelation facts
  let candidate := Executable.snapshot prepared facts
  "!(let* (($plan (quote " ++ plan.render ++ ")) ($facts (quote " ++ (SnapshotClosureExecution.factsTerm facts).render ++
  ")) ($static (quote " ++ (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows).render ++
  ")) ($rows (gslt:snapshot:rows " ++ reprStr Query.factRelation ++ " $facts))" ++
  " ($all (gslt:automata:append $rows $static))" ++
  " ($installed (gslt:snapshot:plan $plan " ++ reprStr Query.factRelation ++ " $facts $static))" ++
  " ($declarations (quote " ++ (PremiseOperationsExecution.DeclarationTyping.declarationsTerm prepared.compiled.terms).render ++
  ")) ($free (quote " ++ (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (Executable.freeTypes prepared.vocabulary)).render ++
  ")) ($signatures (quote " ++ (encodeList PremiseOperationsExecution.GeneralExecution.signatureTerm candidate.provider.signatures).render ++
  ")) ($checked (gslt:snapshot:check-rows $declarations $free LNil $signatures $all)))" ++
  " (println! (DatalogClosureControl " ++ reprStr label ++
  " (== $installed (quote " ++ (encodeOption id expectedPlan).render ++ "))" ++
  " (== $rows (quote " ++ rows.render ++ "))" ++
  " (== $checked " ++ (if ClosureMachine.closed prepared facts then "True" else "False") ++ ")" ++
  " (== $plan (quote " ++ plan.render ++ ")))))"

def main (arguments : List String) : IO Unit := do
  let directory :: options := arguments | throw (IO.userError "expected output directory")
  unless options == [] || options == ["--acceptance"] do throw (IO.userError "unknown option")
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  let mut controls : List String := []
  let mut measurements : List Lean.Json := []
  let mut tests := suites
  if options == ["--acceptance"] then
    let examples := System.FilePath.mk "../../metta/gslt/module/gold/SouffleDatalog/examples"
    let graph ← readInputs ProgramStatic.Controls.cyclicGraph (examples / "cyclic_graph")
    let points ← readInputs ProgramStatic.Controls.pointsTo (examples / "points_to")
    tests := tests ++ [("cyclic-graph",ProgramStatic.Controls.cyclicGraph,graph),
      ("points-to",ProgramStatic.Controls.pointsTo,points)]
  for (label,program,seeds) in tests do
    let .ok prepared := Executable.prepare program seeds | throw (IO.userError s!"{label}: preparation failed")
    let spec := ClosureMachine.spec prepared prepared.seedFacts
    let .ok _ := CompleteEmission.emitText? spec ("datalog-closure-" ++ label) .classes
      | throw (IO.userError s!"{label}: compiler admission refused")
    IO.println s!"{label}: prepared, executing shared model"
    (← IO.getStdout).flush
    let ticks := if label == "cyclic-graph" || label == "points-to" then 100 else 20
    let quantum := if ticks == 100 then 10000 else 2000
    let machine := ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)
    unless machine.complete && machine.fault.isNone do throw (IO.userError s!"{label}: model has pending work or fault")
    let some facts := machine.facts.mapM (Executable.decodeFact? prepared)
      | throw (IO.userError s!"{label}: fact decoding failed")
    let some keys := machine.keys.mapM (ClosureMachine.decodeKey? prepared)
      | throw (IO.userError s!"{label}: key decoding failed")
    let oracle := Closure.run Executable.policy program 12 (Closure.initial seeds)
    unless facts.toFinset == oracle.facts.toFinset && keys.toFinset == oracle.keys.toFinset do
      throw (IO.userError s!"{label}: source closure disagrees: facts={facts.length}/{oracle.facts.length}, keys={keys.length}/{oracle.keys.length}")
    controls := controls ++ [control label prepared ticks quantum machine,
      control (label ++ "/pending") prepared 0 0 (ClosureMachine.begin prepared)]
    measurements := measurements ++ [Lean.Json.mkObj [("label",Lean.toJson label),("kind",Lean.toJson "closure"),
      ("rounds",Lean.toJson machine.round),("facts",Lean.toJson facts.length),("keys",Lean.toJson keys.length)]]
    IO.println s!"{label}: done, rounds={machine.round}, facts={facts.length}, keys={keys.length}"
    (← IO.getStdout).flush
  let .ok prepared := Executable.prepare reachability [edge "a" "b"]
    | throw (IO.userError "provider-control preparation failed")
  let wrongSort := Pattern.apply "GroundFact" [Executable.relationRef 0,
    .apply "GroundTuple" [Join.vector [Executable.relationRef 0]]]
  let providerCases : List (String × List Pattern) :=
    [("provider/empty",[]),("provider/valid",prepared.seedFacts),
     ("provider/duplicates",prepared.seedFacts ++ prepared.seedFacts),
     ("provider/unknown-free",[.fvar "not-in-the-free-context"]),
     ("provider/wrong-sort",[wrongSort]),("provider/wrong-constructor",[.apply "Undeclared" []])]
  for (label,facts) in providerCases do
    controls := controls ++ [providerControl label prepared facts]
    measurements := measurements ++ [Lean.Json.mkObj [("label",Lean.toJson label),
      ("kind",Lean.toJson "provider"),("facts",Lean.toJson facts.length),
      ("accepted",Lean.toJson (ClosureMachine.closed prepared facts))]]
  let sources := RuleExecutionProgram.scopedSource :: CollectionOccurrenceSearchExecution.SelectedNativeSource.sources
  IO.FS.writeFile (output / "runtime.metta") (String.intercalate "\n" (sources.map (·.text)))
  IO.FS.writeFile (output / "ir-profiles.metta") SnapshotClosureExecution.source.text
  IO.FS.writeFile (output / "runtime-digests.json")
    (Lean.Json.pretty (Lean.toJson ((sources.map (·.digest)) ++ [SnapshotClosureExecution.source.digest])) ++ "\n")
  IO.FS.writeFile (output / "controls.metta") (String.intercalate "\n" controls ++ "\n")
  IO.FS.writeFile (output / "measurements.json") (Lean.Json.pretty (Lean.toJson measurements) ++ "\n")

end DatalogClosureControls

def main := DatalogClosureControls.main
