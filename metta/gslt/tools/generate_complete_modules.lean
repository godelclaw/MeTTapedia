/-
Writes `tests/petta/emitted/complete_*.metta` with `CompleteEmission.emitText?` and prints
`tests/petta/gslt_complete_module_controls.metta`. Every expected readout is the Lean complete
machine's (`OSLF/MeTTaIL/Complete`).
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_complete_modules.lean`.
-/
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSharedOutputControls
import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.GSLT.LanguageDef.CollectionConsumerControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassGraph
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionRoot
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionOccurrence
import Mettapedia.GSLT.LanguageDef.CollectionOccurrenceAdmissionControls
import Mettapedia.GSLT.LanguageDef.CollectionInputGuardControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransportControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire (planTerm)

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

namespace CurrentAuthoredInputs
#module_file "../module/CollectionPetri.module"
example : CollectionPetri.module = _root_.CollectionPetri.module := by rfl
#module_file "../module/CollectionReachability.module"
example : CollectionReachability.module = _root_.CollectionReachability.module := by rfl
#module_file "../module/CollectionNestedGuardedPetri.module"
example : CollectionNestedGuardedPetri.module = _root_.CollectionNestedGuardedPetri.module := by rfl
#module_file "../module/CollectionNestedInputPetri.module"
example : CollectionNestedInputPetri.module = _root_.CollectionNestedInputPetri.module := by rfl
#module_file "../module/CollectionNestedOutputPetri.module"
example : CollectionNestedOutputPetri.module = _root_.CollectionNestedOutputPetri.module := by rfl
#module_file "../module/CollectionQuantifiedWorkflow.module"
example : CollectionQuantifiedWorkflow.module = _root_.CollectionQuantifiedWorkflow.module := by rfl
#module_file "../module/CollectionNestedControl.module"
example : CollectionNestedControl.module = _root_.CollectionNestedControl.module := by rfl
#module_file "../module/NamedReplacementControl.module"
example : NamedReplacementControl.module = _root_.NamedReplacementControl.module := by rfl
#module_file "../module/BinaryCollectionJoin.module"
example : BinaryCollectionJoin.module = _root_.BinaryCollectionJoin.module := by rfl
end CurrentAuthoredInputs
open Mettapedia.Machines.ResumableSearchRunner (Machine Phase)
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

namespace FreshCollectionModules
#module_file "../module/CollectionPetri.module"
#module_file "../module/CollectionReachability.module"
#module_file "../module/CollectionNestedGuardedPetri.module"
#module_file "../module/CollectionNestedInputPetri.module"
#module_file "../module/CollectionNestedOutputPetri.module"
#module_file "../module/CollectionQuantifiedWorkflow.module"
#module_file "../module/CollectionNestedControl.module"
#module_file "../module/NamedReplacementControl.module"
#module_file "../module/BinaryCollectionJoin.module"
end FreshCollectionModules

/-- Compare fresh text parsing/lowering with the snapshots imported by the
compiler consumers. This also detects stale objects after module-text edits. -/
def freshCoreMatches (loaded : Except ModuleSource.Error LanguageDef) (stored : LanguageDef) : Bool :=
  (loaded.toOption.bind fun language => language.toCore.toOption).map
    (fun core => reprStr core.language) == some (reprStr stored)

#guard freshCoreMatches FreshCollectionModules.CollectionPetri.language CollectionConsumers.petri
#guard freshCoreMatches FreshCollectionModules.CollectionReachability.language CollectionConsumers.reachability
#guard freshCoreMatches FreshCollectionModules.CollectionNestedGuardedPetri.language CollectionNestedConsumerControls.language
#guard freshCoreMatches FreshCollectionModules.CollectionNestedInputPetri.language CollectionInputGuardControls.language
#guard freshCoreMatches FreshCollectionModules.CollectionNestedOutputPetri.language CollectionQueryControls.language
#guard freshCoreMatches FreshCollectionModules.CollectionQuantifiedWorkflow.language CollectionQuantifierControls.language
#guard freshCoreMatches FreshCollectionModules.CollectionNestedControl.language CollectionSelection.ContextControls.language
#guard freshCoreMatches FreshCollectionModules.NamedReplacementControl.language ModuleSource.ReplacementTransportControls.language
#guard freshCoreMatches FreshCollectionModules.BinaryCollectionJoin.language ModuleSource.BinaryCollectionControls.language

def render (term : Term) : String := Term.render term
def pat (p : Pattern) : String := render (encodePattern p)

def search (spec : Spec) := Complete.Normalized.search spec.plan spec.bound spec.expected

def phaseTerm : Phase → Term
  | .running => .symbol "ClassRunning"
  | .done => .symbol "ClassDone"
  | .blocked => .symbol "ClassBlocked"

def traceText (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  let machine := Machine.advance (search spec) ticks quantum
    (Machine.begin (search spec) (Complete.Normalized.standard spec.plan source))
  render (.application "RunTrace" [phaseTerm machine.phase, CettaWire.encodeList encodePattern machine.states.reverse])

def statesText (spec : Spec) (source : Pattern) (work : Nat) : String :=
  render (CettaWire.encodeList encodePattern ((Complete.Explore.explore (search spec)
    (Complete.Normalized.standard spec.plan source) work).nodes.map (·.state)))

def runControl (label name : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let $t (" ++ name ++ ":run " ++ pat source ++ " " ++ toString ticks ++ " " ++ toString quantum ++ ")\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

def beginControl (label name : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let* (($m (" ++ name ++ ":begin " ++ pat source ++ "))\n" ++
  "        ($a (gslt:runner:advance ClassSearch " ++ render (planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected) ++
    " " ++ render (StandardWire.standardTerm spec.plan) ++ " " ++ toString ticks ++ " " ++ toString quantum ++ " $m))\n" ++
  "        ($t (gslt:runner:trace $a)))\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

def exploreControl (label name : String) (spec : Spec) (source : Pattern) (work : Nat) : String :=
  "!(let $s (" ++ name ++ ":explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $s (quote " ++ statesText spec source work ++ ")))))"

def edgesText (spec : Spec) (source : Pattern) (work : Nat) : String :=
  let explored := Complete.Settled.roundsUntilSettled (search spec) work
    (Complete.Explore.begin (search spec) (Complete.Normalized.standard spec.plan source))
  render (CettaWire.encodeList CompleteExecution.edgeTerm (Complete.Graph.edges (search spec) explored))

def edgesControl (label name : String) (spec : Spec) (source : Pattern) (work : Nat) : String :=
  "!(let $edges (" ++ name ++ ":edges " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $edges (quote " ++ edgesText spec source work ++ ")))))"

def emitTo (spec : Spec) (name : String) (path : String) (profile : SearchProfile spec := admittedProfile spec) : IO Unit := do
  match emitText? spec name profile with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError s!"refused: {name}")

def petriSpec : Spec := ⟨CollectionConsumers.petriPlan, [], .base "Marking", .canonical⟩
def graphSpec : Spec := ⟨CollectionConsumers.reachabilityPlan, [], .base "Graph", .canonical⟩
def producedSpec (permitted : Bool) : Spec :=
  ⟨CollectionConsumers.Controls.producedPetriPlan permitted, [], .base "Marking", .standard⟩

#guard match admittedProfile petriSpec with
  | .rootCollection _ _ _ => true
  | _ => false

def rootSearchModel (spec : Spec) (certificate : CollectionRootSearch.CoverageProfile spec.plan) :=
  CollectionRootSearch.search (profile := certificate.profile) spec.expected

def rootTraceText (spec : Spec) (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (source : Pattern) (ticks quantum : Nat) : String :=
  render (CompleteExecution.SearchWire.traceTerm
    (Machine.advance (rootSearchModel spec certificate) ticks quantum
      (Machine.begin (rootSearchModel spec certificate) (CanonicalBags.canon source))))

def rootStatesText (spec : Spec) (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (source : Pattern) (work : Nat) : String :=
  let explored := Complete.Settled.roundsUntilSettled (rootSearchModel spec certificate) work
    (Complete.Explore.begin (rootSearchModel spec certificate) (CanonicalBags.canon source))
  render (CettaWire.encodeList encodePattern (explored.nodes.map (·.state)))

def rootEdgesText (spec : Spec) (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (source : Pattern) (work : Nat) : String :=
  let explored := Complete.Settled.roundsUntilSettled (rootSearchModel spec certificate) work
    (Complete.Explore.begin (rootSearchModel spec certificate) (CanonicalBags.canon source))
  render (CettaWire.encodeList (CompleteExecution.SearchWire.edgeTerm CompleteExecution.RootCollection.receiptTerm)
    (Complete.Graph.edges (rootSearchModel spec certificate) explored))

def rootControl (label name entry : String) (source : Pattern) (arguments expected : String) : String :=
  "!(let $actual (" ++ name ++ ":" ++ entry ++ " " ++ pat source ++ " " ++ arguments ++ ")\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $actual (quote " ++ expected ++ ")))))"

def rootBeginControl (label name : String) (spec : Spec)
    (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let* (($machine (" ++ name ++ ":begin " ++ pat source ++ "))\n" ++
  "        ($paged (gslt:runner:advance " ++ render (CompleteExecution.RootCollection.backendTerm (table spec)) ++
  " " ++ render (planTerm spec.plan spec.plan.snapshot.freeTypes [] spec.expected) ++
  " " ++ render (StandardWire.commitTerm spec.plan spec.mode (table spec)) ++
  " " ++ toString ticks ++ " " ++ toString quantum ++ " $machine))\n" ++
  "        ($trace (gslt:runner:trace $paged)))\n" ++
  "  (println! (CompleteModuleControl " ++ reprStr label ++ " (== $trace (quote " ++
  rootTraceText spec certificate source ticks quantum ++ ")))))"

#guard match admittedProfile graphSpec with
  | .rootCollection _ _ _ => true
  | _ => false

#guard (match emit? graphSpec "graph" .classes with
  | .error (.obligations pending) => pending.contains .setDecomposition
  | _ => false)

def invalidFreeGraphSpec : Spec :=
  let snapshot := CollectionConsumers.snapshot CollectionConsumers.reachability
  let invalid := { snapshot with freeTypes := [("n", .base "Node"), ("n", .base "Node")] }
  { graphSpec with plan := GeneralExecutionAdmission.compile invalid CollectionConsumers.permissions }

#guard match admittedProfile invalidFreeGraphSpec with
  | .classes => true
  | _ => false

#guard match emit? invalidFreeGraphSpec "invalid-graph" with
  | .error (.obligations obligations) => obligations.contains .invalidFreeContext
  | _ => false

def lambdaSpec : Spec := ⟨Complete.Controls.lambdaPlan, [], .base "Term", .standard⟩
def guardedSpec : Spec := ⟨GeneralGuardedBinderExecution.plan [.permit], [], .proc, .standard⟩
def sealedSpec : Spec := ⟨GeneralGuardedBinderExecution.plan [], [], .proc, .standard⟩
def branchingSpec : Spec := ⟨Complete.ClassesControls.branchingPlan, [], .base "T", .standard⟩

def localQuantifierSpec (zeroRows : Nat := 1) (oneRow : Bool := true) : Spec :=
  ⟨CollectionQuantifierControls.plan zeroRows oneRow,
    [], .base "Term", .standard⟩

#guard match admittedProfile localQuantifierSpec with
  | .classes => true
  | _ => false

/-- Quantifier controls use the established ordinary profile. They do not
authorize quotient-aware quantification over bag or set presentations. -/
def localQuantifierControls : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  for (name, zeroRows, oneRow, nested, elements, expected) in [
      ("quantified_local", 1, true, false,
        [GeneralPremise.SharedOutputControls.zero, GeneralPremise.SharedOutputControls.one], 1),
      ("quantified_duplicate", 2, true, false,
        [GeneralPremise.SharedOutputControls.zero, GeneralPremise.SharedOutputControls.one], 2),
      ("quantified_missing", 1, false, false,
        [GeneralPremise.SharedOutputControls.zero, GeneralPremise.SharedOutputControls.one], 0),
      ("quantified_empty", 0, false, false, [], 1),
      ("quantified_nested", 2, true, true,
        [GeneralPremise.SharedOutputControls.zero, GeneralPremise.SharedOutputControls.one], 4)] do
    let spec := localQuantifierSpec zeroRows oneRow
    let source := CollectionQuantifierControls.source elements nested
    let model := search spec
    let run := model.run source 1000
    let explorer := Complete.Settled.roundsUntilSettled model 2000
      (Complete.Explore.begin model source)
    unless (model.publication run).length == expected do
      throw (IO.userError "Quantified module has an incorrect receipt count")
    unless model.status run == .complete && Complete.Settled.settled model explorer do
      throw (IO.userError "Quantified module did not complete and settle")
    unless (Complete.Graph.edges model explorer).length == expected do
      throw (IO.userError "Quantified module changed its complete receipt-bearing edges")
    emitTo spec name (dir ++ "complete_" ++ name ++ ".metta")
    IO.println (beginControl (name ++ "-begin-resume") name spec source 20 100)
    IO.println (runControl (name ++ "-run") name spec source 20 100)
    IO.println (exploreControl (name ++ "-explore") name spec source 2000)
    IO.println (edgesControl (name ++ "-edges") name spec source 2000)
/-- λ compiled without the structural-descent refinement: its only obligation is stratification. -/
def unstratifiedSpec : Spec :=
  ⟨GeneralExecutionAdmission.compile ⟨Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language, [],
    {signatures := [], rows := []}⟩ StructuralDescent.Controls.rootPermissions, [], .base "Term", .standard⟩

def refusal (name : String) : String :=
  match emitText? lambdaSpec name with
  | .error (.nameCollision _) => "refused-name-collision"
  | _ => "NOT-REFUSED"

def workflowSpec (permitted : Bool) (bound : List TypeExpr := []) : Spec :=
  ⟨CollectionNestedConsumerControls.plan permitted, bound, .base "Workspace", .canonical⟩

def contextSpec : Spec :=
  ⟨CollectionSelection.ContextControls.plan, [], .base "Proc", .canonical⟩

def collectionInputSpec (values : List Pattern) (copies : Nat := 1) : Spec :=
  ⟨CollectionInputGuardControls.plan values copies, [], .base "Workspace", .canonical⟩

def collectionQuerySpec (copies : Nat := 1) (inputs : List Pattern := [CollectionQueryControls.a, CollectionQueryControls.b])
    (witness : Pattern := CollectionQueryControls.b) : Spec :=
  ⟨CollectionQueryControls.plan copies inputs [CollectionQueryControls.a, CollectionQueryControls.a, CollectionQueryControls.b] witness,
    [], .base "Workspace", .canonical⟩

#guard match admittedProfile collectionQuerySpec with
  | .collectionOccurrence _ _ => true
  | _ => false

def namedReplacementSpec (expected : TypeExpr := .base "A") : Spec :=
  ⟨ModuleSource.ReplacementTransportControls.plan, [], expected, .canonical⟩

/-- The established native checker consumes the actual packed declaration
and lowered pattern. These are representation checks, not equation-profile
admission or operational-coverage certificates. -/
def binaryTypingControl (label : String) (language : LanguageDef)
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : String :=
  let context := [("x", .base "Item"), ("y", .base "Item"), ("z", .base "Item")]
  let declarations := PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms
  let free := PremiseOperationsExecution.DeclarationTyping.freeContextTerm context
  let bounds := PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound
  let answer := WellSorted.checkHasType language (WellSorted.FreeTypeContext.ofList context) bound pattern expected
  "!(let* (($declarations (quote " ++ render declarations ++ "))\n" ++
  "        ($free (quote " ++ render free ++ "))\n" ++
  "        ($bound (quote " ++ render bounds ++ "))\n" ++
  "        ($pattern (quote " ++ pat pattern ++ "))\n" ++
  "        ($expected (quote " ++ render (AuthoredRule.typeTerm expected) ++ "))\n" ++
  "        ($actual (gslt:premise:type-has $declarations $free $bound $pattern $expected)))\n" ++
  "  (println! (BinaryTypingControl " ++ reprStr label ++ " (== $actual " ++
    (if answer then "True" else "False") ++ "))))"

#guard match admittedProfile (namedReplacementSpec) with
  | .collectionOccurrence _ _ => true
  | _ => false

#guard match admittedProfile (collectionInputSpec [CollectionInputGuardControls.a, CollectionInputGuardControls.b]) with
  | .collectionOccurrence _ _ => true
  | _ => false
#guard match admittedProfile (collectionInputSpec [CollectionInputGuardControls.a, CollectionInputGuardControls.b] 2) with
  | .collectionOccurrence _ _ => true
  | _ => false
#guard match admittedProfile (collectionInputSpec [CollectionInputGuardControls.b, CollectionInputGuardControls.a]) with
  | .classes => true
  | _ => false

#guard match admittedProfile (workflowSpec true) with
  | .collectionOccurrence _ _ => true
  | _ => false
#guard match admittedProfile (workflowSpec false) with
  | .collectionOccurrence _ _ => true
  | _ => false
#guard match admittedProfile (workflowSpec true [.base "Place"]) with
  | .collectionOccurrence _ _ => true
  | _ => false
#guard match admittedProfile contextSpec with
  | .collectionOccurrence _ _ => true
  | _ => false
#guard (match emit? contextSpec "set-context-old-matcher" .classes with
  | .error (.obligations pending) => pending.contains .setDecomposition
  | _ => false)

def occurrenceTraceText (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  render (CompleteExecution.SearchWire.traceTerm
    (Machine.advance (occurrenceSearch spec) ticks quantum
      (Machine.begin (occurrenceSearch spec) (CanonicalBags.canon source))))

def occurrenceControls (label name : String) (spec : Spec) (source : Pattern)
    (ticks quantum work : Nat) : IO Unit := do
  let search := occurrenceSearch spec
  let final := Complete.Settled.roundsUntilSettled search work
    (Complete.Explore.begin search (CanonicalBags.canon source))
  let trace := occurrenceTraceText spec source ticks quantum
  let states := render (CettaWire.encodeList encodePattern (final.nodes.map (·.state)))
  let edges := render (CettaWire.encodeList
    (CompleteExecution.SearchWire.edgeTerm ScopedRuleJobReadoutExecution.receiptTerm)
    (Complete.Graph.edges search final))
  IO.println (rootControl (label ++ "-run") name "run" source
    (toString ticks ++ " " ++ toString quantum) trace)
  IO.println (rootControl (label ++ "-explore") name "explore" source (toString work) states)
  IO.println (rootControl (label ++ "-edges") name "edges" source (toString work) edges)
  IO.println ("!(let* (($machine (" ++ name ++ ":begin " ++ pat source ++ "))\n" ++
    "        ($paged (gslt:runner:advance " ++ render (CompleteExecution.CollectionOccurrence.backendTerm (table spec) 0) ++
    " " ++ render (planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected) ++
    " " ++ render (StandardWire.commitTerm spec.plan spec.mode (table spec)) ++
    " " ++ toString ticks ++ " " ++ toString quantum ++ " $machine))\n" ++
    "        ($trace (gslt:runner:trace $paged)))\n" ++
    "  (println! (CompleteModuleControl " ++ reprStr (label ++ "-begin-resume") ++
    " (== $trace (quote " ++ trace ++ ")))))")

def sourceAlgebraControl (label : String) (laws : List CollectionLaws.Laws) (pattern : Pattern) : String :=
  let lawsText := render (CettaWire.encodeList StandardWire.lawTerm laws)
  let expected := pat (CollectionLaws.normalize laws pattern)
  "!(let $normal (gslt:laws:normalize " ++ lawsText ++ " " ++ pat pattern ++ ")\n" ++
    "  (println! (SourceAlgebraControl " ++ reprStr label ++ " (== $normal (quote " ++ expected ++ ")))))"

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  emitTo petriSpec "petri" (dir ++ "complete_petri.metta")
  emitTo graphSpec "graph" (dir ++ "complete_graph.metta")
  emitTo (producedSpec true) "produced" (dir ++ "complete_produced.metta")
  emitTo (producedSpec false) "produced_empty" (dir ++ "complete_produced_empty.metta")
  emitTo lambdaSpec "lambda" (dir ++ "complete_lambda.metta")
  emitTo guardedSpec "guarded" (dir ++ "complete_guarded.metta")
  emitTo sealedSpec "sealed" (dir ++ "complete_sealed.metta")
  emitTo branchingSpec "branching" (dir ++ "complete_branching.metta")
  emitTo unstratifiedSpec "unstratified" (dir ++ "complete_unstratified.metta")
  emitTo (workflowSpec true) "workflow" (dir ++ "complete_workflow.metta")
  emitTo (workflowSpec false) "workflow_denied" (dir ++ "complete_workflow_denied.metta")
  emitTo (workflowSpec true [.base "Place"]) "workflow_ambient" (dir ++ "complete_workflow_ambient.metta")
  emitTo contextSpec "set_context" (dir ++ "complete_set_context.metta")
  emitTo (collectionInputSpec [CollectionInputGuardControls.a, CollectionInputGuardControls.b])
    "collection_input" (dir ++ "complete_collection_input.metta")
  emitTo (collectionInputSpec [CollectionInputGuardControls.a, CollectionInputGuardControls.b] 2)
    "collection_input_duplicates" (dir ++ "complete_collection_input_duplicates.metta")
  emitTo (collectionInputSpec [CollectionInputGuardControls.a])
    "collection_input_missing" (dir ++ "complete_collection_input_missing.metta")
  emitTo collectionQuerySpec "collection_query" (dir ++ "complete_collection_query.metta")
  emitTo (collectionQuerySpec 2) "collection_query_duplicates" (dir ++ "complete_collection_query_duplicates.metta")
  emitTo (collectionQuerySpec 0) "collection_query_missing" (dir ++ "complete_collection_query_missing.metta")
  emitTo (collectionQuerySpec 1 [CollectionQueryControls.a, CollectionQueryControls.b] CollectionQueryControls.a)
    "collection_query_wrong" (dir ++ "complete_collection_query_wrong.metta")
  emitTo namedReplacementSpec "named_replacement" (dir ++ "complete_named_replacement.metta")
  emitTo (namedReplacementSpec (.arrow (.base "A") (.base "A"))) "named_replacement_arrow"
    (dir ++ "complete_named_replacement_arrow.metta")
  IO.println "; Controls for complete-machine modules. Each module was written by"
  IO.println "; CompleteEmission.emitText?; every expected readout is the Lean complete machine's."
  localQuantifierControls
  let source := GeneralGuardedBinderFrontierControls.source
  IO.println (runControl "lambda-nested-run" "lambda" lambdaSpec StructuralDescent.Controls.nestedRedex 40 50)
  IO.println (runControl "lambda-two-steps-run" "lambda" lambdaSpec Complete.Controls.twoSteps 60 50)
  IO.println (beginControl "lambda-begin-then-pages" "lambda" lambdaSpec Complete.Controls.twoSteps 60 50)
  IO.println (runControl "guarded-run" "guarded" guardedSpec source 10 40)
  IO.println (exploreControl "guarded-explore" "guarded" guardedSpec source 200)
  IO.println (runControl "sealed-run" "sealed" sealedSpec source 10 40)
  IO.println (runControl "branching-run" "branching" branchingSpec (.apply "A" []) 20 5)
  IO.println (exploreControl "branching-explore" "branching" branchingSpec (.apply "A" []) 12)
  IO.println (runControl "unstratified-lambda-run" "unstratified" unstratifiedSpec Complete.Controls.twoSteps 60 50)
  let marking := CollectionConsumers.marking [CollectionConsumers.token "A", CollectionConsumers.token "B"]
  let duplicate := CollectionConsumers.marking
    [CollectionConsumers.token "A", CollectionConsumers.token "A", CollectionConsumers.token "B"]
  let petriCoverage := CollectionConsumers.Controls.RootControls.petriCoverage
  let graphCoverage := CollectionConsumers.Controls.RootControls.graphCoverage
  let duplicatePackets := (rootSearchModel petriSpec petriCoverage).publication
    ((rootSearchModel petriSpec petriCoverage).run (CanonicalBags.canon duplicate) 100)
  unless duplicatePackets.length == 2 do
    throw (IO.userError "Petri source occurrences were lost or multiplied")
  for packet in duplicatePackets do
    unless (CompleteExecution.RootCollection.decodeReceiptFor? petriSpec.plan petriCoverage.profile.collection
        (CanonicalBags.canon duplicate) (CompleteExecution.RootCollection.receiptTerm packet)).isSome do
      throw (IO.userError "A valid Petri packet did not decode")
    unless (CompleteExecution.RootCollection.decodeReceiptFor? petriSpec.plan petriCoverage.profile.collection
        (CollectionConsumers.marking [CollectionConsumers.token "A"])
        (CompleteExecution.RootCollection.receiptTerm packet)).isNone do
      throw (IO.userError "A packet from a different source was accepted by the decoder")
  IO.println (rootControl "petri-emitted-run" "petri" "run" marking "20 50" (rootTraceText petriSpec petriCoverage marking 20 50))
  IO.println (rootControl "petri-emitted-explore" "petri" "explore" marking "100" (rootStatesText petriSpec petriCoverage marking 100))
  IO.println (rootControl "petri-emitted-duplicate-run" "petri" "run" duplicate "20 50" (rootTraceText petriSpec petriCoverage duplicate 20 50))
  IO.println (rootControl "petri-emitted-duplicate-edges" "petri" "edges" duplicate "100" (rootEdgesText petriSpec petriCoverage duplicate 100))
  IO.println (rootBeginControl "petri-emitted-begin-resume" "petri" petriSpec petriCoverage marking 20 50)
  let graph := CollectionConsumers.graph [CollectionConsumers.edge "A" "B", CollectionConsumers.edge "B" "C"]
  let loop := CollectionConsumers.graph [CollectionConsumers.edge "A" "A"]
  let graphSearch := rootSearchModel graphSpec graphCoverage
  unless (graphSearch.publication (graphSearch.run (CanonicalBags.canon graph) 200)).length == 4 do
    throw (IO.userError "Graph residual origins were lost or multiplied")
  unless (graphSearch.publication (graphSearch.run (CanonicalBags.canon loop) 120)).length == 2 do
    throw (IO.userError "Graph reuse multiplied ordinary validation witnesses")
  let graphExplorer := Complete.Settled.roundsUntilSettled graphSearch 200
    (Complete.Explore.begin graphSearch (CanonicalBags.canon graph))
  unless Complete.Settled.settled graphSearch graphExplorer do
    throw (IO.userError "The graph consumer did not settle within its qualified observation")
  let closedGraph := CanonicalBags.canon (CollectionConsumers.graph
    [CollectionConsumers.edge "A" "B", CollectionConsumers.edge "B" "C", CollectionConsumers.edge "A" "C"])
  unless (graphExplorer.nodes.map (·.state)).contains closedGraph do
    throw (IO.userError "The graph consumer did not produce the transitive edge")
  IO.println (rootBeginControl "graph-emitted-begin-resume" "graph" graphSpec graphCoverage graph 20 100)
  IO.println (rootControl "graph-emitted-run" "graph" "run" graph "20 100" (rootTraceText graphSpec graphCoverage graph 20 100))
  IO.println (rootControl "graph-emitted-explore" "graph" "explore" graph "200" (rootStatesText graphSpec graphCoverage graph 200))
  IO.println (rootControl "graph-emitted-edges" "graph" "edges" graph "200" (rootEdgesText graphSpec graphCoverage graph 200))
  IO.println (rootControl "graph-emitted-reuse" "graph" "edges" loop "120" (rootEdgesText graphSpec graphCoverage loop 120))
  IO.println (rootControl "graph-emitted-wrong-kind" "graph" "run" marking "5 20"
    (rootTraceText graphSpec graphCoverage marking 5 20))
  IO.println (runControl "produced-premise-emitted-run" "produced" (producedSpec true) marking 5 100)
  IO.println (exploreControl "produced-premise-emitted-explore" "produced" (producedSpec true) marking 200)
  IO.println (edgesControl "produced-premise-emitted-edges" "produced" (producedSpec true) marking 200)
  IO.println (runControl "produced-premise-empty-provider" "produced_empty" (producedSpec false) marking 5 100)
  let workflow := CollectionNestedConsumerControls.source
  for permitted in [true, false] do
    let spec := workflowSpec permitted
    let search := occurrenceSearch spec
    let completed := search.publication (search.run (CanonicalBags.canon workflow) 200)
    unless completed.length == (if permitted then 2 else 0) do
      throw (IO.userError "Emitted workflow model lost token occurrences or bypassed its guard")
    occurrenceControls (s!"workflow-emitted-{permitted}")
      (if permitted then "workflow" else "workflow_denied") spec workflow 12 40 200
  occurrenceControls "workflow-emitted-missing" "workflow" (workflowSpec true)
    (CollectionNestedConsumerControls.boxed [CollectionNestedConsumerControls.token "B"]) 12 40 200
  let ambient := CollectionNestedConsumerControls.boxed
    [CollectionNestedConsumerControls.token "A", .bvar 0,
      CollectionNestedConsumerControls.token "A", CollectionNestedConsumerControls.token "B"]
  occurrenceControls "workflow-emitted-ambient" "workflow_ambient"
    (workflowSpec true [.base "Place"]) ambient 12 40 200
  let a := CollectionSelection.ContextControls.atom "A"
  let b := CollectionSelection.ContextControls.atom "B"
  let setOf := CollectionSelection.ContextControls.setOf
  occurrenceControls "set-emitted-both-residuals" "set_context" contextSpec (setOf [a]) 12 40 200
  occurrenceControls "set-emitted-collapse" "set_context" contextSpec (setOf [a, b]) 12 40 200
  occurrenceControls "set-emitted-nested-retention" "set_context" contextSpec (setOf [setOf [a]]) 12 40 200
  occurrenceControls "bag-emitted-distinct-origins" "set_context" contextSpec
    (CollectionSelection.ContextControls.bagOf [a, a]) 12 40 200
  for (label, name, spec) in [
      ("collection-input-emitted", "collection_input", collectionInputSpec [CollectionInputGuardControls.a, CollectionInputGuardControls.b]),
      ("collection-input-duplicate-provider-emitted", "collection_input_duplicates", collectionInputSpec [CollectionInputGuardControls.a, CollectionInputGuardControls.b] 2),
      ("collection-input-missing-emitted", "collection_input_missing", collectionInputSpec [CollectionInputGuardControls.a])] do
    occurrenceControls label name spec workflow 12 40 200
  for (label, name, spec) in [
      ("mixed-query-emitted", "collection_query", collectionQuerySpec),
      ("mixed-query-duplicate-provider-emitted", "collection_query_duplicates", collectionQuerySpec 2),
      ("mixed-query-missing-emitted", "collection_query_missing", collectionQuerySpec 0),
      ("mixed-query-wrong-witness-emitted", "collection_query_wrong",
        collectionQuerySpec 1 [CollectionQueryControls.a, CollectionQueryControls.b] CollectionQueryControls.a)] do
    occurrenceControls label name spec CollectionQueryControls.source 20 40 800
  let nestedReplacement := Pattern.apply "L" [.apply "B0" [], .apply "L" [.apply "B0" [], .apply "A0" []]]
  occurrenceControls "named-replacement-nested" "named_replacement" namedReplacementSpec nestedReplacement 12 40 200
  occurrenceControls "named-replacement-wrong-order" "named_replacement" namedReplacementSpec
    (.apply "L" [.apply "A0" [], .apply "B0" []]) 12 40 200
  occurrenceControls "named-replacement-binder" "named_replacement_arrow"
    (namedReplacementSpec (.arrow (.base "A") (.base "A")))
    (.lambda none (.apply "L" [.apply "B0" [], .bvar 0])) 12 40 200
  let bare := ModuleSource.BinaryCollectionControls.bareRow
  let wrapped := ModuleSource.BinaryCollectionControls.wrappedRow
  let target := ModuleSource.BinaryCollectionControls.target
  let lowered := ModuleSource.BinaryCollectionControls.lowered
  let item := ModuleSource.BinaryCollectionControls.item
  let nested := ModuleSource.BinaryCollectionControls.nested
  let binder := ModuleSource.BinaryCollectionControls.underBinder
  for (label, language, pattern, expected) in [
      ("binary-source-nested", ModuleSource.BinaryCollectionControls.source, nested, item),
      ("binary-bare-nested", target bare, lowered bare nested, item),
      ("binary-wrapped-nested", target wrapped, lowered wrapped nested, item),
      ("binary-bare-binder", target bare, lowered bare binder, .arrow item item),
      ("binary-wrapped-binder", target wrapped, lowered wrapped binder, .arrow item item),
      ("binary-wrapped-refuses-bare", target wrapped, lowered bare nested, item),
      ("binary-bare-refuses-wrapped", target bare, lowered wrapped nested, item),
      ("binary-wrong-kind", target wrapped,
        .apply "Word" [.collection .hashBag [.fvar "x", .fvar "y"] none], item),
      ("binary-wrong-result-sort", target bare, lowered bare nested, .base "Other"),
      ("binary-data-fibre", target bare, lowered bare nested, .collection .vec item)] do
    IO.println (binaryTypingControl label language [] pattern expected)
  let .ok binaryLanguage := FreshCollectionModules.BinaryCollectionJoin.language
    | throw (IO.userError "Authored binary algebra did not elaborate")
  let authoredLaws := CollectionLaws.declared binaryLanguage
  unless authoredLaws == [⟨.vec, some "One"⟩] do
    throw (IO.userError "Authored collection laws changed")
  let nestedWithUnit := ModuleSource.BinaryCollectionControls.nestedWithUnit
  for (label, laws, pattern) in [
      ("binary-authored-unit-normal", authoredLaws, lowered bare nestedWithUnit),
      ("binary-undeclared-flattening", [], lowered bare nested),
      ("binary-declared-unit-keeps-wrong-unit", authoredLaws,
        Pattern.collection .vec [.apply "Wrong" [], .fvar "x"] none),
      ("binary-other-kind-keeps-unit", authoredLaws,
        Pattern.collection .hashBag [.apply "One" []] none),
      ("binary-wrapped-declaration-keeps-nesting",
        CollectionLaws.declared (ModuleSource.declareAlgebras (target wrapped) ["Word"]),
        lowered wrapped nestedWithUnit),
      ("binary-distinct-wrapper-kept", authoredLaws,
        Pattern.apply "Other" [.collection .vec [.apply "One" [], .fvar "x"] none])] do
    IO.println (sourceAlgebraControl label laws pattern)
  IO.println ("; name collision with the runtime: " ++ refusal "gslt:runner" ++ ", " ++ refusal "gslt:explore")
  IO.println ("; unstratified plan's obligations: " ++ reprStr (repr unstratifiedSpec.plan.obligations).pretty ++
    ", pending after the complete machine: " ++ toString (pending unstratifiedSpec.plan).length)

#eval main
