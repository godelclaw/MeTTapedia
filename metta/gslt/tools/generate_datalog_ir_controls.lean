import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRLookupNative
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoinNative
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQueryNative
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassSearch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
import Lean.Data.Json.Printer

/-! Independent IR lookup through the unchanged emitter, runner and explorer.
The expected fact membership is checked separately from the wire comparisons. -/

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open CompleteEmission

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace DatalogIRControls

structure Profile where
  spec : Spec
  name : String
  quantum : Nat
  rounds : Nat

def lookupProfile : Profile := ⟨Lookup.Native.spec,"datalog-ir-lookup",300,3000⟩
def joinProfile : Profile := ⟨Join.Native.spec,"datalog-ir-join",10000,10000⟩
def search (profile : Profile) := Complete.Normalized.search profile.spec.plan profile.spec.bound profile.spec.expected profile.spec.mode
def initial (profile : Profile) (source : Pattern) := Complete.Normalized.commit profile.spec.plan profile.spec.mode source
def begun (profile : Profile) (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.begin (search profile) (initial profile source)
def run (profile : Profile) (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search profile) 4 profile.quantum (begun profile source)
def explorer (profile : Profile) (source : Pattern) := Complete.Settled.roundsUntilSettled (search profile) profile.rounds
  (Complete.Explore.begin (search profile) (initial profile source))
def resumed (profile : Profile) (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search profile) 4 profile.quantum
  (Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search profile) 1 1 (begun profile source))

def cases : List (String × List Pattern) :=
  [("empty",[]),("one",[Lookup.Native.fact "a" "b"]),
   ("join-input",[Lookup.Native.fact "a" "b",Lookup.Native.fact "b" "c"]),
   ("duplicate-occurrences",[Lookup.Native.fact "a" "b",Lookup.Native.fact "b" "c",Lookup.Native.fact "a" "b"])]

def referenceSuites : List (Profile × List (String × Pattern × List Pattern)) :=
  [(lookupProfile,cases.map fun (label,facts) => ("lookup/" ++ label,Lookup.call facts,facts)),
   (joinProfile,
     [("join/shared-variable",Join.Native.request [Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "b" "c"],
         [Join.Native.fact "path" "a" "c"]),
      ("join/reuse-one-fact",Join.Native.request [Join.Native.fact "edge" "a" "a"],
         [Join.Native.fact "path" "a" "a"]),
      ("join/two-explanations",Join.Native.request
         [Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "b" "c",
          Join.Native.fact "edge" "a" "d",Join.Native.fact "edge" "d" "c"],
         [Join.Native.fact "path" "a" "c",Join.Native.fact "path" "a" "c"]),
      ("join/disagreeing-variable",Join.Native.request [Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "d" "c"],[]),
      ("join/wrong-relation",Join.Native.request [Join.Native.fact "edge" "a" "b",Join.Native.fact "path" "b" "c"],[]),
      ("join/empty",Join.Native.request [],[])])]

def queryCases : List (String × List Pattern × List Pattern) :=
  [("shared-variable",[Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "b" "c"],
      [Join.Native.fact "path" "a" "c"]),
   ("reused-fact",[Join.Native.fact "edge" "a" "a"],[Join.Native.fact "path" "a" "a"]),
   ("two-explanations",
      [Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "b" "c",
       Join.Native.fact "edge" "a" "d",Join.Native.fact "edge" "d" "c"],
      [Join.Native.fact "path" "a" "c",Join.Native.fact "path" "a" "c"]),
   ("disagreeing-variable",[Join.Native.fact "edge" "a" "b",Join.Native.fact "edge" "d" "c"],[]),
   ("wrong-relation",[Join.Native.fact "edge" "a" "b",Join.Native.fact "path" "b" "c"],[]),
   ("empty",[],[])]

def suites : List (Profile × List (String × Pattern × List Pattern)) :=
  referenceSuites ++ queryCases.map fun (label,known,wanted) =>
    (⟨Query.Native.spec known,"datalog-ir-query-" ++ label,3000,3000⟩,
      [("query/" ++ label,Query.Native.request,wanted)])

def machine (profile : Profile) (source : Pattern) := CompleteExecution.SearchWire.machineTerm
  (CompleteExecution.classStateTerm profile.spec.plan) CompleteExecution.classReceiptTerm (resumed profile source)

def control (profile : Profile) (label : String) (source : Pattern) : String :=
  let spec := profile.spec
  let name := profile.name
  let budget := "4 " ++ toString profile.quantum
  let rounds := toString profile.rounds
  let trace := CompleteExecution.SearchWire.traceTerm (run profile source)
  let graph := explorer profile source
  let states := encodeList InferenceCettaWire.encodePattern (graph.nodes.map (·.state))
  let edges := encodeList (CompleteExecution.SearchWire.edgeTerm CompleteExecution.classReceiptTerm)
    (Complete.Graph.edges (search profile) graph)
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected).render
  let standard := (StandardWire.commitTerm spec.plan spec.mode (table spec)).render
  "!(let* (($input (quote " ++ CettaWire.Term.render (InferenceCettaWire.encodePattern source) ++ "))" ++
    " ($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++ "))" ++
    " ($expected (quote " ++ trace.render ++ "))" ++
    " ($expected-states (quote " ++ states.render ++ "))" ++
    " ($expected-edges (quote " ++ edges.render ++ "))" ++
    " ($expected-machine (quote " ++ (machine profile source).render ++ "))" ++
    " ($trace (" ++ name ++ ":run $input " ++ budget ++ "))" ++
    " ($states (" ++ name ++ ":explore $input " ++ rounds ++ "))" ++
    " ($edges (" ++ name ++ ":edges $input " ++ rounds ++ "))" ++
    " ($begun (" ++ name ++ ":begin $input))" ++
    " ($interrupted (gslt:runner:advance ClassSearch $plan $standard 1 1 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard " ++ budget ++ " $interrupted)))" ++
    " (println! (DatalogIRControl " ++ reprStr label ++
    " (== $trace $expected) (== $states $expected-states)" ++
    " (== $edges $expected-edges) (== $resumed $expected-machine))))"

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  let mut texts : List String := []
  let mut controls : List String := []
  let mut measurements : List Lean.Json := []
  for (profile,tests) in suites do
    let .ok text := emitText? profile.spec profile.name .classes
      | throw (IO.userError s!"{profile.name}: existing emitter refused the profile")
    texts := texts ++ [text]
    for (label,source,wanted) in tests do
      let result := run profile source
      unless result.phase == .done do throw (IO.userError s!"{label}: unfinished runner")
      let graph := explorer profile source
      unless Complete.Settled.settled (search profile) graph do throw (IO.userError s!"{label}: unfinished exploration")
      let edges := Complete.Graph.edges (search profile) graph
      unless edges.length == wanted.length do throw (IO.userError s!"{label}: wrong receipt count ({edges.length}, expected {wanted.length})")
      unless wanted.all (fun fact => edges.any (fun edge => edge.2.2 == fact)) do
        throw (IO.userError s!"{label}: missing fact")
      unless edges.all (fun edge => wanted.contains edge.2.2) do
        throw (IO.userError s!"{label}: invented fact")
      controls := controls ++ [control profile label source]
      measurements := measurements ++ [Lean.Json.mkObj [
        ("label",Lean.toJson label),("expected_receipts",Lean.toJson wanted.length),
        ("receipt_edges",Lean.toJson edges.length),("nodes",Lean.toJson graph.nodes.length),
        ("settled_round",Lean.toJson graph.round),
        ("quantum",Lean.toJson profile.quantum),("round_budget",Lean.toJson profile.rounds),
        ("phase",Lean.toJson (CompleteExecution.SearchWire.phaseSymbol result.phase)),
        ("source_wire_bytes",Lean.toJson (CettaWire.Term.render (InferenceCettaWire.encodePattern source)).toUTF8.size)]]
      IO.println s!"{label}: {edges.length} receipts, settled at round {graph.round}"
  IO.FS.writeFile (output / "ir-profiles.metta") (String.intercalate "\n" texts)
  let sources := RuleExecutionProgram.scopedSource :: CollectionOccurrenceSearchExecution.SelectedNativeSource.sources
  IO.FS.writeFile (output / "runtime.metta") (String.intercalate "\n" (sources.map (·.text)))
  IO.FS.writeFile (output / "runtime-digests.json") (Lean.Json.pretty (Lean.toJson (sources.map (·.digest))) ++ "\n")
  IO.FS.writeFile (output / "controls.metta") (String.intercalate "\n" controls ++ "\n")
  IO.FS.writeFile (output / "measurements.json") (Lean.Json.pretty (Lean.toJson measurements) ++ "\n")

end DatalogIRControls

def main := DatalogIRControls.main
