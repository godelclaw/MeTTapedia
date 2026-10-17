/-
Prints `tests/petta/gslt_complete_controls.metta`. Every expected readout is the Lean complete
machine's (`OSLF/MeTTaIL/Complete`).
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_complete_controls.lean`.
-/
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def render (term : Term) : String := Term.render term

def boolTerm (value : Bool) : Term := .symbol (if value then "True" else "False")

/-- The plan as MeTTa data, with its own list of free types: the free table on its declared
footprint (`Complete.Footprint.entriesOn_declared`), on which the bridge theorems are stated. -/
def planTerm (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (_source : Pattern) : Term :=
  CompletePlanWire.planTerm plan plan.snapshot.freeTypes bound expected

def assignment (value : ScopedRuleMatching.Assignment) : Term :=
  RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm value

def equationJobTerm (job : GeneralEquationJobs.Job) : Term :=
  .application "EquationJob" [.natural job.planPosition, AuthoredRule.rewriteTerm job.equation.rule,
    AuthoredRule.bindingSpecTerm job.equation.binding.spec, ScopedRuleJobReadoutExecution.siteTerm job.site]

def equationReceiptTerm (receipt : GeneralEquationJobs.Receipt) : Term :=
  .application "EquationReceipt" [equationJobTerm receipt.job,
    PremiseOperationsExecution.GeneralExecution.traceTerm receipt.matcherTrace, assignment receipt.captured,
    assignment receipt.completed, PremiseOperationsExecution.GeneralExecution.eventsTerm receipt.premiseHistory,
    encodePattern receipt.rawReduct, encodePattern receipt.target]

def conversionTerm : GeneralOccurrenceSemantics.Conversion → Term
  | .forward receipt => .application "ForwardConversion" [equationReceiptTerm receipt]
  | .reverse receipt => .application "ReverseConversion" [equationReceiptTerm receipt]

def classReceiptTerm (receipt : GeneralOccurrenceSemantics.Receipt) : Term :=
  .application "ClassReceipt" [encodePattern receipt.representative, CettaWire.encodeList conversionTerm receipt.conversions,
    ScopedRuleJobReadoutExecution.receiptTerm receipt.firing]

def predecessorControl (label : String) (plan : GeneralExecutionAdmission.Plan) (type : TypeExpr)
    (source target : Pattern) : String :=
  let expected := CettaWire.encodeList encodePattern (Complete.Predecessors.predecessors plan [] target)
  "!(let* (($p (quote " ++ render (planTerm plan [] type source) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern target) ++ "))\n" ++
  "        ($r (gslt:complete:predecessors $p $x)))\n" ++
  "  (println! (PredecessorControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def classControl (label : String) (plan : GeneralExecutionAdmission.Plan) (type : TypeExpr) (source : Pattern)
    (work : Nat) : String :=
  let state := Complete.Classes.rounds plan [] type work (Complete.Classes.begin plan [] type source)
  let expected := Term.application "ClassReadout"
    [CettaWire.encodeList encodePattern (state.reps.map (·.pattern)),
     CettaWire.encodeList classReceiptTerm state.log, boolTerm (Complete.Classes.complete plan state)]
  "!(let* (($p (quote " ++ render (planTerm plan [] type source) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern source) ++ "))\n" ++
  "        ($b (gslt:classes:begin $p $x))\n" ++
  "        ($s (gslt:classes:rounds $p " ++ toString work ++ " $b))\n" ++
  "        ($r (gslt:classes:readout $p $s)))\n" ++
  "  (println! (ClassControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def stepControl (label : String) (plan : GeneralExecutionAdmission.Plan) (type : TypeExpr) (source : Pattern)
    (work : Nat) : String :=
  let state := Complete.Step.rounds plan [] type work (Complete.Step.begin plan [] type source)
  let expected := Term.application "StepReadout"
    [CettaWire.encodeList ScopedRuleJobReadoutExecution.receiptTerm state.log,
     boolTerm (Complete.Step.status plan state == .complete)]
  "!(let* (($p (quote " ++ render (planTerm plan [] type source) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern source) ++ "))\n" ++
  "        ($b (gslt:step:begin $p $x))\n" ++
  "        ($s (gslt:step:rounds $p $x " ++ toString work ++ " $b))\n" ++
  "        ($r (gslt:step:readout $p $s)))\n" ++
  "  (println! (StepControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def limitControl (label : String) (plan : GeneralExecutionAdmission.Plan) (type : TypeExpr) (source : Pattern) : String :=
  let limits := (Complete.EquationJob.lanes plan [] type source).map fun lane =>
    match Complete.EquationJob.premisesBound plan lane.job lane.answer.assignment with
    | some limit => Term.application "Some" [.natural limit]
    | none => Term.symbol "None"
  "!(let* (($p (quote " ++ render (planTerm plan [] type source) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern source) ++ "))\n" ++
  "        ($l (gslt:equations:lanes $p $x))\n" ++
  "        ($r (gslt:equations:lane-limits $p $l)))\n" ++
  "  (println! (LimitControl " ++ reprStr label ++ " (== $r (quote " ++ render (CettaWire.encodeList id limits) ++ ")))))"

def term : TypeExpr := .base "Term"

def main : IO Unit := do
  IO.println "; Generated by tools/generate_complete_controls.lean. Expected readouts are the Lean complete machine's."
  for work in [0, 1, 40, 200, 600] do
    IO.println (stepControl s!"lambda-nested-{work}" Complete.Controls.lambdaPlan term
      StructuralDescent.Controls.nestedRedex work)
  for work in [100, 400, 1000] do
    IO.println (stepControl s!"lambda-two-steps-{work}" Complete.Controls.lambdaPlan term Complete.Controls.twoSteps work)
  for work in [100, 600] do
    IO.println (stepControl s!"letcase-nested-{work}" Complete.Controls.letCasePlan
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.computation StructuralDescent.Controls.LetCaseControls.nested work)
  for work in [50, 400] do
    IO.println (stepControl s!"partrec-{work}" StructuralDescent.Controls.partrecPlan (.base "Cfg")
      StructuralDescent.Controls.partrecStart work)

def guarded (allowed : List EquationFrontierBinderProfile.Token) : GeneralExecutionAdmission.Plan :=
  GeneralGuardedBinderExecution.plan allowed

def classes : IO Unit := do
  let source := GeneralGuardedBinderFrontierControls.source
  let exposed := GeneralGuardedBinderFrontierControls.exposed
  IO.println (predecessorControl "guarded-exposed" (guarded [.permit]) .proc source exposed)
  IO.println (predecessorControl "guarded-source" (guarded [.permit]) .proc source source)
  IO.println (limitControl "guarded-source-limits" (guarded [.permit]) .proc source)
  IO.println (limitControl "guarded-exposed-limits" (guarded [.permit]) .proc exposed)
  for work in [0, 1, 5, 20, 60, 400] do
    IO.println (classControl s!"guarded-permit-{work}" (guarded [.permit]) .proc source work)
  for work in [5, 400] do
    IO.println (classControl s!"guarded-none-{work}" (guarded []) .proc source work)
  for work in [100, 600] do
    IO.println (classControl s!"lambda-nested-classes-{work}" Complete.Controls.lambdaPlan term
      StructuralDescent.Controls.nestedRedex work)
  for work in [3, 30] do
    IO.println (classControl s!"branching-{work}" Complete.ClassesControls.branchingPlan (.base "T") (.apply "A" []) work)


open Mettapedia.Machines.ResumableSearchRunner in
def phaseTerm : Phase → Term
  | .running => .symbol "ClassRunning"
  | .done => .symbol "ClassDone"
  | .blocked => .symbol "ClassBlocked"

open Mettapedia.Machines.ResumableSearchRunner in
def runnerControl (label : String) (plan : GeneralExecutionAdmission.Plan) (type : TypeExpr) (source : Pattern)
    (ticks quantum : Nat) : String :=
  let search := Complete.Normalized.search plan [] type
  let machine := Machine.advance search ticks quantum (Machine.begin search (Complete.Normalized.standard plan source))
  let expected := Term.application "RunTrace" [phaseTerm machine.phase, CettaWire.encodeList encodePattern machine.states.reverse]
  "!(let* (($p (quote " ++ render (planTerm plan [] type source) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern source) ++ "))\n" ++
  "        ($s (quote " ++ render (StandardWire.standardTerm plan) ++ "))\n" ++
  "        ($b (gslt:runner:begin $p $s $x))\n" ++
  "        ($m (gslt:runner:advance $p $s " ++ toString ticks ++ " " ++ toString quantum ++ " $b))\n" ++
  "        ($r (gslt:runner:trace $m)))\n" ++
  "  (println! (RunnerControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def exploreControl (label : String) (plan : GeneralExecutionAdmission.Plan) (type : TypeExpr) (source : Pattern)
    (work : Nat) : String :=
  let explorer := Complete.Explore.explore (Complete.Normalized.search plan [] type)
    (Complete.Normalized.standard plan source) work
  let expected := CettaWire.encodeList encodePattern (explorer.nodes.map (·.state))
  "!(let* (($p (quote " ++ render (planTerm plan [] type source) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern source) ++ "))\n" ++
  "        ($s (quote " ++ render (StandardWire.standardTerm plan) ++ "))\n" ++
  "        ($b (gslt:explore:begin $p $s $x))\n" ++
  "        ($e (gslt:explore:rounds $p $s " ++ toString work ++ " $b))\n" ++
  "        ($r (gslt:explore:states $e)))\n" ++
  "  (println! (ExploreControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def runs : IO Unit := do
  for (ticks, quantum) in [(0, 10), (3, 10), (40, 50)] do
    IO.println (runnerControl s!"lambda-nested-run-{ticks}x{quantum}" Complete.Controls.lambdaPlan term
      StructuralDescent.Controls.nestedRedex ticks quantum)
  for ticks in [1, 10] do
    IO.println (runnerControl s!"guarded-permit-run-{ticks}" (guarded [.permit]) .proc
      GeneralGuardedBinderFrontierControls.source ticks 40)
  IO.println (runnerControl "guarded-none-run" (guarded []) .proc GeneralGuardedBinderFrontierControls.source 10 40)
  for ticks in [2, 20] do
    IO.println (runnerControl s!"branching-run-{ticks}" Complete.ClassesControls.branchingPlan (.base "T") (.apply "A" []) ticks 5)
  for work in [0, 3, 12] do
    IO.println (exploreControl s!"branching-explore-{work}" Complete.ClassesControls.branchingPlan (.base "T") (.apply "A" []) work)
  IO.println (exploreControl "guarded-permit-explore" (guarded [.permit]) .proc GeneralGuardedBinderFrontierControls.source 200)

/-- The variants of an equation side at an instance, as `Inversion.variants` lists them. -/
def variantControl (label : String) (schema target : Pattern) : String :=
  let expected := CettaWire.encodeList encodePattern (Complete.Inversion.variants schema target)
  "!(let* (($s (quote " ++ render (encodePattern schema) ++ "))\n" ++
  "        ($t (quote " ++ render (encodePattern target) ++ "))\n" ++
  "        ($r (gslt:complete:variants $s $t)))\n" ++
  "  (println! (VariantControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def twoElements (kind : CollType) (first second : Pattern) : Pattern := .collection kind [first, second] none

def variants : IO Unit := do
  let schema (kind : CollType) := twoElements kind (.fvar "x") (.fvar "y")
  let target (kind : CollType) := twoElements kind (.apply "A" []) (.apply "B" [])
  IO.println (variantControl "vector-keeps-order" (schema .vec) (target .vec))
  IO.println (variantControl "bag-every-order" (schema .hashBag) (target .hashBag))
  IO.println (variantControl "set-every-order" (schema .hashSet) (target .hashSet))
  IO.println (variantControl "lambda-erases-binder" (.lambda (some "x") (.bvar 0)) (.lambda (some "y") (.apply "A" [])))
  IO.println (variantControl "mismatch-erases" (.apply "F" [.fvar "x"]) (.lambda (some "y") (.bvar 0)))

/-- The standard form under declared laws, as `CollectionLaws.standardForm` computes it. -/
def lawsControl (label : String) (laws : List CollectionLaws.Laws) (extrusions : List CollectionLaws.Extrusion)
    (pattern : Pattern) : String :=
  let expected := encodePattern (CollectionLaws.standardForm laws extrusions pattern)
  "!(let* (($l (quote " ++ render (CettaWire.encodeList StandardWire.lawTerm laws) ++ "))\n" ++
  "        ($e (quote " ++ render (CettaWire.encodeList StandardWire.extrusionTerm extrusions) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern pattern) ++ "))\n" ++
  "        ($r (gslt:laws:standard $l $e $x)))\n" ++
  "  (println! (LawsControl " ++ reprStr label ++ " (== $r (quote " ++ render expected ++ ")))))"

def bag (items : List Pattern) : Pattern := .collection .hashBag items none

def laws : IO Unit := do
  let flat : List CollectionLaws.Laws := [⟨.hashBag, none⟩]
  let unit : List CollectionLaws.Laws := [⟨.hashBag, some "PZero"⟩]
  let restrict : List CollectionLaws.Extrusion := [⟨.hashBag, "PNew"⟩]
  let p := Pattern.fvar "p"
  let q := Pattern.fvar "q"
  let zero := Pattern.apply "PZero" []
  let new (body : Pattern) := Pattern.apply "PNew" [.lambda none body]
  IO.println (lawsControl "flatten-nested" flat [] (bag [p, bag [q, bag []]]))
  IO.println (lawsControl "drop-unit" unit [] (.apply "PAmb" [.fvar "n", bag [zero, p]]))
  IO.println (lawsControl "no-laws-identity" [] [] (bag [p, bag [q]]))
  IO.println (lawsControl "vector-untouched" flat [] (.collection .vec [p, .collection .vec [q] none] none))
  IO.println (lawsControl "rest-kept" flat [] (.collection .hashBag [p, bag [q]] (some "rest")))
  IO.println (lawsControl "extrude-one" flat restrict (bag [p, new (bag [.bvar 0, q])]))
  IO.println (lawsControl "extrude-two" flat restrict (bag [new (.bvar 0), new (bag [.bvar 0, p])]))
  IO.println (lawsControl "extrude-under-binder" flat restrict
    (.apply "PAmb" [.fvar "n", bag [new (.apply "PAmb" [.bvar 0, zero]), p]]))

#eval main
#eval classes
#eval runs
#eval variants
#eval laws
