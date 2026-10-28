import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogQueryKernel
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
/-! Ground-kernel controls through the shared emitter and finite provider.
The source reader and full receipt interpretation have separate contracts. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace DatalogKernelControls

def freeTypes : List (String × TypeExpr) :=
 [("a",.base "DlGroundAtomData"),("b",.base "DlGroundAtomData"),
  ("c",.base "DlGroundAtomData"),("id",.base "DlClauseOrdinal"),("env",.base "DlGrounding")]
def known : List Pattern := [.fvar "a", .fvar "b"]
def spec : Spec := ⟨QueryKernel.plan freeTypes known, [], .base "DlInference", .canonical⟩
example : spec.plan.obligations = [] := by decide_cbv

def pat (source : Pattern) := CettaWire.Term.render (InferenceCettaWire.encodePattern source)

def controlCases : List (String × Pattern) :=
  [("present", Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c")
      [.fvar "a", .fvar "b"] known),
   ("repeated", Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c")
      [.fvar "a", .fvar "a"] known),
   ("absent", Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c")
      [.fvar "c"] known),
   ("empty", Kernel.groundApplication (.fvar "id") (.fvar "env") (.fvar "c") [] known)]

def modelSearch := Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode

def begun (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.begin modelSearch
  (Complete.Normalized.commit spec.plan spec.mode source)

def paged (source : Pattern) (ticks quantum : Nat) :=
  Mettapedia.Machines.ResumableSearchRunner.Machine.advance modelSearch ticks quantum (begun source)

def explored (source : Pattern) (work : Nat) :=
  Complete.Explore.explore modelSearch (Complete.Normalized.commit spec.plan spec.mode source) work

def edgePairs (source : Pattern) (work : Nat) :=
  let explorer := Complete.Settled.roundsUntilSettled modelSearch work
    (Complete.Explore.begin modelSearch (Complete.Normalized.commit spec.plan spec.mode source))
  encodeList (fun edge => CettaWire.Term.application "Pair"
    [InferenceCettaWire.encodePattern edge.1, InferenceCettaWire.encodePattern edge.2.2])
    (Complete.Graph.edges modelSearch explorer)

def controls (label : String) (source : Pattern) : String :=
  let expected := CompleteExecution.SearchWire.traceTerm (paged source 2 500)
  let states := encodeList InferenceCettaWire.encodePattern ((explored source 100).nodes.map (·.state))
  let edges := edgePairs source 100
  let resumed := Mettapedia.Machines.ResumableSearchRunner.Machine.advance modelSearch 2 500
    (Mettapedia.Machines.ResumableSearchRunner.Machine.advance modelSearch 1 5 (begun source))
  let resumeTrace := CompleteExecution.SearchWire.traceTerm resumed
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected).render
  let standard := (StandardWire.commitTerm spec.plan spec.mode (table spec)).render
  "!(let* (($input (quote " ++ pat source ++ "))" ++
    " ($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++ "))" ++
    " ($expected (quote " ++ expected.render ++ "))" ++
    " ($expected-states (quote " ++ states.render ++ "))" ++
    " ($expected-edges (quote " ++ edges.render ++ "))" ++
    " ($expected-resume (quote " ++ resumeTrace.render ++ "))" ++
    " ($trace (datalog-query:run $input 2 500))" ++
    " ($states (datalog-query:explore $input 100))" ++
    " ($edges (datalog-query:edges $input 100))" ++
    " ($begun (datalog-query:begin $input))" ++
    " ($interrupted (gslt:runner:advance ClassSearch $plan $standard 1 5 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard 2 500 $interrupted))" ++
    " ($resumed-trace (gslt:runner:trace $resumed)))" ++
    " (println! (DatalogQueryKernelModelControl " ++ reprStr label ++
    " (== $trace $expected) (== $states $expected-states)" ++
    " (== (datalog-test:edge-pairs $edges) $expected-edges) (== $resumed-trace $expected-resume))))"

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  IO.FS.createDirAll directory
  for (label, source) in controlCases do
    let machine := paged source 2 500
    let nodes := (explored source 100).nodes.length
    if label != "absent" && (machine.receipts.isEmpty || nodes < 2) then
      throw (IO.userError s!"positive control {label} did not reach a firing within its declared budget")
    if label == "absent" && !machine.receipts.isEmpty then
      throw (IO.userError "missing-premise control invented a firing")
    IO.println s!"model {label}: receipts={machine.receipts.length}, nodes={nodes}"
  let .ok text := emitText? spec "datalog-query" .classes
    | throw (IO.userError "the query kernel was refused")
  IO.FS.writeFile (System.FilePath.mk directory / "query.metta") text
  IO.FS.writeFile (System.FilePath.mk directory / "controls.metta")
    ("(= (datalog-test:edge-pairs LNil) LNil)\n" ++
      "(= (datalog-test:edge-pairs (LCons (Edge $source $receipt $target) $rest)) (LCons (Pair $source $target) (datalog-test:edge-pairs $rest)))\n" ++
      String.intercalate "\n" (controlCases.map fun (label,source) => controls label source) ++ "\n")
end DatalogKernelControls

def main := DatalogKernelControls.main
