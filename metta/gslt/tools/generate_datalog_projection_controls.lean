import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNativeControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionProgramControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassGraph
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
import Lean.Data.Json.Printer

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace GSLTDatalogProjectionControls

structure Profile where
  spec : CompleteEmission.Spec
  name : String
  ticks : Nat
  quantum : Nat
  rounds : Nat

def tupleProfile : Profile := ⟨Native.Controls.tupleSpec,"datalog-projection",3,1500,200⟩
def programProfile : Profile := ⟨Native.ProgramControls.spec,"datalog-program-projection",4,12000,600⟩
def trivia : Pattern := .apply "dl-src:trivia-empty" []
def integer : Pattern := .apply "dl-src:constant-integer" [.fvar "i"]
def symbol : Pattern := .apply "dl-src:constant-symbol" [.fvar "s"]
def floating : Pattern := .apply "dl-src:constant-float" [.fvar "f"]
def items : List Pattern → Pattern
  | [] => ConstantLists.empty
  | [literal] => ConstantLists.one literal trivia
  | literal :: rest => ConstantLists.more literal trivia trivia (items rest)

def tupleCases : List (String × Pattern × Option Pattern) :=
  [("empty",ConstantLists.call (items []),some (Reference.groundTuple [])),
   ("single",ConstantLists.call (items [integer]),some (Reference.groundTuple [.apply "IntegerValue" [.fvar "i"]])),
   ("duplicate",ConstantLists.call (items [integer,integer]),
      some (Reference.groundTuple [.apply "IntegerValue" [.fvar "i"],.apply "IntegerValue" [.fvar "i"]])),
   ("mixed",ConstantLists.call (items [integer,symbol,floating]),
      some (Reference.groundTuple [.apply "IntegerValue" [.fvar "i"],.apply "SymbolValue" [.fvar "s"],
        .apply "FloatValue" [.fvar "f"]])),
   ("malformed",ConstantLists.call (items [.apply "dl-src:constant-integer" []]),none)]

def programCases : List (String × Pattern × Option Pattern) :=
  let c := Native.ProgramControls.ordinaryCore
  [("program/empty",Program.call (Native.ProgramControls.sourceProgram []),some (Reference.program [])),
   ("program/ordinary-source",Program.call c,some (Reference.program [Native.ProgramControls.groundResult])),
   ("program/duplicates",Program.call
      (Native.ProgramControls.sourceProgram [Native.ProgramControls.factItem,Native.ProgramControls.factItem]),
      some (Reference.program [Native.ProgramControls.groundResult,Native.ProgramControls.groundResult])),
   ("program/grouped-clause",Program.call Native.ProgramControls.fullSource,some Native.ProgramControls.fullResult),
   ("program/malformed",Program.call (.apply "dl-src:program" [trivia]),none)]

def search (profile : Profile) :=
  Complete.Normalized.search profile.spec.plan profile.spec.bound profile.spec.expected profile.spec.mode

def begun (profile : Profile) (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.begin
  (search profile) (Complete.Normalized.commit profile.spec.plan profile.spec.mode source)
def paged (profile : Profile) (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.advance
  (search profile) profile.ticks profile.quantum (begun profile source)
def explorer (profile : Profile) (source : Pattern) := Complete.Settled.roundsUntilSettled (search profile) profile.rounds
  (Complete.Explore.begin (search profile) (Complete.Normalized.commit profile.spec.plan profile.spec.mode source))

def resumed (profile : Profile) (source : Pattern) :=
  let interrupted := Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search profile) 1 1 (begun profile source)
  Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search profile) profile.ticks profile.quantum interrupted

def control (profile : Profile) (label : String) (source : Pattern) : String :=
  let spec := profile.spec
  let expected := CompleteExecution.SearchWire.traceTerm (paged profile source)
  let explored := explorer profile source
  let states := encodeList InferenceCettaWire.encodePattern (explored.nodes.map (·.state))
  let edges := encodeList (CompleteExecution.SearchWire.edgeTerm CompleteExecution.classReceiptTerm)
    (Complete.Graph.edges (search profile) explored)
  let machine := CompleteExecution.classMachineTerm spec.plan (resumed profile source)
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected).render
  let standard := (StandardWire.commitTerm spec.plan spec.mode (table spec)).render
  let pat := CettaWire.Term.render (InferenceCettaWire.encodePattern source)
  "!(let* (($input (quote " ++ pat ++ "))" ++
    " ($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++ "))" ++
    " ($expected (quote " ++ expected.render ++ "))" ++
    " ($expected-states (quote " ++ states.render ++ "))" ++
    " ($expected-edges (quote " ++ edges.render ++ "))" ++
    " ($expected-machine (quote " ++ machine.render ++ "))" ++
    " ($trace (" ++ profile.name ++ ":run $input " ++ toString profile.ticks ++ " " ++ toString profile.quantum ++ "))" ++
    " ($states (" ++ profile.name ++ ":explore $input " ++ toString profile.rounds ++ "))" ++
    " ($edges (" ++ profile.name ++ ":edges $input " ++ toString profile.rounds ++ "))" ++
    " ($begun (" ++ profile.name ++ ":begin $input))" ++
    " ($interrupted (gslt:runner:advance ClassSearch $plan $standard 1 1 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard " ++ toString profile.ticks ++ " " ++
      toString profile.quantum ++ " $interrupted)))" ++
    " (println! (DatalogProjectionControl " ++ reprStr label ++
    " (== $trace $expected) (== $states $expected-states)" ++
    " (== $edges $expected-edges) (== $resumed $expected-machine))))"

mutual
  def depth : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ children | .collection _ children _ => 1 + depths children
    | .lambda _ body | .multiLambda _ _ body => 1 + depth body
    | .subst body replacement => 1 + max (depth body) (depth replacement)
  def depths : List Pattern → Nat
    | [] => 0
    | first :: rest => max (depth first) (depths rest)
end

def measurement (profile : Profile) (label : String) (source : Pattern) : Lean.Json :=
  let machine := paged profile source
  let explored := explorer profile source
  Lean.Json.mkObj [
    ("label",Lean.toJson label),("source_depth",Lean.toJson (depth source)),
    ("source_wire_bytes",Lean.toJson (CettaWire.Term.render (InferenceCettaWire.encodePattern source)).toUTF8.size),
    ("ticks",Lean.toJson profile.ticks),("quantum",Lean.toJson profile.quantum),
    ("explorer_rounds",Lean.toJson profile.rounds),("committed_receipts",Lean.toJson machine.receipts.length),
    ("explored_nodes",Lean.toJson explored.nodes.length),
    ("receipt_edges",Lean.toJson (Complete.Graph.edges (search profile) explored).length),
    ("phase",Lean.toJson (CompleteExecution.SearchWire.phaseSymbol machine.phase)),
    ("resumed_state_wire_bytes",Lean.toJson
      (CompleteExecution.classMachineTerm profile.spec.plan (resumed profile source)).render.toUTF8.size)]

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  IO.FS.createDirAll directory
  let mut texts : List String := []
  let mut rows : List String := []
  let mut measurements : List Lean.Json := []
  for (profile,suite) in [(tupleProfile,tupleCases),(programProfile,programCases)] do
    let .ok text := emitText? profile.spec profile.name .classes
      | throw (IO.userError s!"{profile.name}: refused by existing emitter")
    texts := texts ++ [text]
    for (label,source,expected) in suite do
      let machine := paged profile source
      match expected with
      | some result =>
        unless result ∈ machine.states do throw (IO.userError s!"{label}: expected result missing")
        if machine.receipts.isEmpty then throw (IO.userError s!"{label}: no completed firing")
        unless machine.phase == .done do throw (IO.userError s!"{label}: model retains unfinished work")
      | none =>
        unless machine.receipts.isEmpty do throw (IO.userError s!"{label}: invented a firing")
      IO.println s!"model {label}: receipts={machine.receipts.length}, phase={CompleteExecution.SearchWire.phaseSymbol machine.phase}"
      (← IO.getStdout).flush
      rows := rows ++ [control profile label source]
      measurements := measurements ++ [measurement profile label source]
  IO.FS.writeFile (System.FilePath.mk directory / "projector.metta") (String.intercalate "\n" texts)
  IO.FS.writeFile (System.FilePath.mk directory / "controls.metta") (String.intercalate "\n" rows ++ "\n")
  IO.FS.writeFile (System.FilePath.mk directory / "projection-measurements.json")
    ((Lean.toJson measurements).pretty ++ "\n")

end GSLTDatalogProjectionControls

def main := GSLTDatalogProjectionControls.main
