import Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCollectionInputTransport
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution

/-!
# Whole-collection input guards and their representation boundary

The authored workflow's guard reads its captured residual bag. Equal provider
rows have separate indices, while the guarded rule retains each physical token
allocation. A noncanonical provider row is deliberately left unchanged and
separates structural query semantics from collection equality.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../metta/gslt/module/CollectionNestedInputPetri.module"
#module_file "../../../../../metta/gslt/module/CollectionNestedOutputPetri.module"
#module_file "../../../../../metta/gslt/module/CollectionQuantifiedWorkflow.module"

namespace Mettapedia.GSLT.LanguageDef.CollectionInputGuardControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching

def authored : LanguageDef := CollectionNestedInputPetri.language.toOption.getD (LanguageDef.empty "")

def language : LanguageDef :=
  (authored.toCore.toOption.map (·.language)).getD
    (LanguageDef.empty "")

#guard CollectionNestedInputPetri.language.isOk
#guard authored.toCore.isOk
#guard (language.rewrites.head?.bind fun rule => rule.typeContext.lookup "rest").isSome

def inputType : TypeExpr :=
  (language.rewrites.head?.bind fun rule => rule.typeContext.lookup "rest").getD (.base "Marking")

def a : Pattern := CollectionNestedConsumerControls.token "A"
def b : Pattern := CollectionNestedConsumerControls.token "B"
def bag (values : List Pattern) : Pattern := CollectionNestedConsumerControls.marking values

def provider (values : List Pattern) (copies : Nat := 1) : ProviderSnapshot :=
  { signatures := [⟨"inspect", [inputType], [.input]⟩],
    rows := List.replicate copies ⟨"inspect", [bag values]⟩ }

def plan (values : List Pattern) (copies : Nat := 1) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language, [], provider values copies⟩
    { sites := .all, includeDerivedEquations := false }

def environment (values : List Pattern) (copies : Nat := 1) : Environment :=
  GeneralPlanEnvironment.environment (plan values copies)

def context : Context :=
  match (plan [a, b]).rules.head? with
  | some declaration => ⟨0, declaration.rule, declaration.binding.spec, [], 0, 0⟩
  | none => ⟨0, { «name» := "", typeContext := [], premises := [], left := .fvar "", right := .fvar "" },
      { dependencies := [], occurrences := [] }, [], 0, 0⟩

#guard (plan [a, b]).rules.length == 1
#guard checkCanonicalProviderRows (provider [a, b])
#guard !checkCanonicalProviderRows (provider [b, a])
#guard checkCollectionInputGuards (provider [a, b]) context context.rule.premises
#guard !checkCollectionInputGuard (provider [a, b]) context
  (.relationQuery "inspect" [bag [.fvar "rest"]])
#guard !checkCollectionInputGuard { provider [a, b] with
    signatures := [⟨"inspect", [inputType], [.output]⟩] }
  context (.relationQuery "inspect" [.fvar "rest"])
#guard !checkCollectionInputGuard (provider [a, b]) context
  (.relationQuery "missing" [.fvar "rest"])

def search (values : List Pattern) (copies : Nat := 1) :=
  CollectionOccurrenceSearch.search (plan values copies) [] (.base "Workspace") 0

def query (captured : List Pattern) : Query.Request :=
  ⟨context, "inspect", [.fvar "rest"], [("rest", ⟨[], 0, bag captured⟩)]⟩

def queryAnswers (rowValues captured : List Pattern) (copies : Nat := 1) :=
  let request := query captured
  Query.run (environment rowValues copies) request 100 (Query.start (environment rowValues copies) request)

def controls : IO Unit := do
  let source := CollectionNestedConsumerControls.source
  for (values, copies, count) in [([a, b], 1, 2), ([a, b], 2, 4), ([a], 1, 0), ([b, a], 1, 0)] do
    let s := search values copies
    let zero := s.run source 0
    let whole := s.run source 200
    let resumed := s.resume (s.resume zero 73) 127
    let receipts := s.publication whole
    unless receipts.length == count do
      throw (IO.userError "Collection-valued guard changed allocation/provider occurrence counts")
    unless (s.publication resumed).map reprStr == receipts.map reprStr do
      throw (IO.userError "Resumption lost or repeated a collection-input guard receipt")
    unless receipts.all (fun receipt => CanonicalBags.canon receipt.target == CollectionNestedConsumerControls.expected) do
      throw (IO.userError "Collection-valued guard changed the outer workflow or conclusion")
  let direct := queryAnswers [b, a] [b, a]
  let normalized := queryAnswers [b, a] [a, b]
  unless direct.answers.length == 1 && normalized.answers.isEmpty do
    throw (IO.userError "Noncanonical provider row no longer separates structural input equality")
  let duplicated := queryAnswers [a, b] [a, b] 2
  unless duplicated.answers.map (·.rowIndex) == [0, 1] do
    throw (IO.userError "Repeated provider rows lost their original distinct indices")
  IO.println "CollectionInputGuardControls: guarded collections, provider indices, resumption and representation negative passed"

#eval controls

end Mettapedia.GSLT.LanguageDef.CollectionInputGuardControls

namespace Mettapedia.GSLT.LanguageDef.CollectionQueryControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching

def authored : LanguageDef := CollectionNestedOutputPetri.language.toOption.getD (LanguageDef.empty "")
def language : LanguageDef := (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")
def a : Pattern := CollectionNestedConsumerControls.token "A"
def b : Pattern := CollectionNestedConsumerControls.token "B"
def bag (values : List Pattern) : Pattern := CollectionNestedConsumerControls.marking values
def view (values : List Pattern) (witness : Pattern := b) : Pattern := .apply "View" [bag values, witness]

def provider (copies : Nat := 1) (inputValues : List Pattern := [a, b])
    (outputValues : List Pattern := [a, a, b]) (witness : Pattern := b) : ProviderSnapshot :=
  { signatures := [⟨"choose", [.base "Marking", .base "Marking"], [.input, .output]⟩],
    rows := List.replicate copies ⟨"choose", [view inputValues, view outputValues witness]⟩ }

def plan (copies : Nat := 1) (inputValues : List Pattern := [a, b])
    (outputValues : List Pattern := [a, a, b]) (witness : Pattern := b) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language, [], provider copies inputValues outputValues witness⟩
    { sites := .all, includeDerivedEquations := false }

def source : Pattern := CollectionNestedConsumerControls.source
def target (token : Pattern) : Pattern := CollectionNestedConsumerControls.boxed [token]
def search (copies : Nat := 1) (inputValues : List Pattern := [a, b])
    (outputValues : List Pattern := [a, a, b]) (witness : Pattern := b) :=
  CollectionOccurrenceSearch.search (plan copies inputValues outputValues witness) [] (.base "Workspace") 0

#guard CollectionNestedOutputPetri.language.isOk
#guard authored.toCore.isOk
#guard (plan).rules.length == 1
#guard CollectionOccurrenceMachine.checkGuardFragment (plan)
#guard checkCanonicalProviderRows (provider)
#guard !checkCanonicalProviderRows (provider 1 [b, a])
def noPremises : LanguageDef := { authored with
  «rewrites» := authored.rewrites.map fun rule => { rule with premises := [] } }
#guard !noPremises.toCore.isOk
#guard !CollectionOccurrenceAdmission.check (GeneralExecutionAdmission.compile
  ⟨language, [], { provider with signatures := [⟨"choose", [.base "Marking", .base "Marking"], [.input, .input]⟩] }⟩
    { sites := .all, includeDerivedEquations := false })

/-- Open output tails are declared at the collection type, independently
of the result sort of the collection's enclosing constructor. -/
theorem output_tail_type_checked :
    SchemaTyping.checkSchemaRest (fun _ => some (.collection .hashBag (.base "Place")))
        .hashBag (.base "Place") (some "remaining") = true ∧
      SchemaTyping.checkSchemaRest (fun _ => some (.base "Place"))
        .hashBag (.base "Place") (some "remaining") = false := by decide +kernel

def dependentValue : ContextualValue :=
  ⟨[.base "Place", .base "Place"], 0, .collection .hashBag [.bvar 0, .bvar 1] none⟩

theorem increasing_occurrence_read :
    instantiateValue? (CanonicalBags.canonValue dependentValue) 0 2 [.bvar 0, .bvar 1] =
      some (CanonicalBags.canon (.collection .hashBag [.bvar 0, .bvar 1] none)) := by
  exact CanonicalBags.instantiateValue?_canon
    (show variableSpine? 2 [.bvar 0, .bvar 1] = some [0, 1] from by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- A reversed occurrence substitution can unsort a canonical body. The
increasing-spine premise of exact canonical input reading is necessary. -/
theorem reversed_occurrence_is_not_a_canonical_read :
    instantiateValue? (CanonicalBags.canonValue dependentValue) 0 2 [.bvar 1, .bvar 0] ≠
      some (CanonicalBags.canon (.collection .hashBag [.bvar 1, .bvar 0] none)) := by
  cbv
  simp

def controls : IO Unit := do
  for (copies, inputs, outputs, witness, expected) in [
      (1, [a,b], [a,a,b], b, 6), (2, [a,b], [a,a,b], b, 12),
      (0, [a,b], [a,a,b], b, 0), (1, [a], [a,a,b], b, 0),
      (1, [a,b], [a,a,b], a, 0)] do
    let s := search copies inputs outputs witness
    let begun := s.run source 0
    let whole := s.run source 800
    let paused := s.resume begun 60
    let resumed := s.resume paused 740
    let receipts := s.publication whole
    if expected != 0 then
      unless decide (s.status paused = .pending) && (s.publication paused).length == 4 do
        throw (IO.userError "Mixed-query pause must retain pending work and four published receipts")
    unless decide (s.status whole = .complete) do
      throw (IO.userError "Mixed query did not finish within its observation budget")
    unless receipts.length == expected do
      throw (IO.userError s!"Mixed query changed allocation/provider multiplicity: {receipts.length} instead of {expected}")
    let withOrigins := CollectionOccurrenceSearch.publicationWithOrigins whole
    unless withOrigins.length == receipts.length &&
        (withOrigins.map (fun entry => reprStr entry.1)).eraseDups.length == receipts.length do
      throw (IO.userError "Mixed-query allocation origins were lost before receipt projection")
    unless (CollectionOccurrenceSearch.publicationWithOrigins resumed).map (fun entry => reprStr entry.1) ==
        withOrigins.map (fun entry => reprStr entry.1) do
      throw (IO.userError "Mixed-query resumption changed the allocation-origin account")
    unless (s.publication resumed).map reprStr == receipts.map reprStr do
      throw (IO.userError "Mixed-query resumption lost or repeated a receipt")
    unless receipts.all (fun receipt => CanonicalBags.canon receipt.target == target a ||
        CanonicalBags.canon receipt.target == target b) do
      throw (IO.userError "Mixed query changed the authored conclusion or outer context")
    if expected != 0 then
      unless (receipts.filter (fun receipt => CanonicalBags.canon receipt.target == target a)).length == 4 * copies do
        throw (IO.userError "Equal provider tokens lost their distinct ordinary output allocations")
      unless (receipts.filter (fun receipt => CanonicalBags.canon receipt.target == target b)).length == 2 * copies do
        throw (IO.userError "Provider output selection changed the B occurrences")
  IO.println "CollectionQueryControls: mixed modes, structured inputs/outputs, duplicate tokens, missing rows and pending-state resumption passed"

#eval controls

end Mettapedia.GSLT.LanguageDef.CollectionQueryControls

namespace Mettapedia.GSLT.LanguageDef.CollectionQuantifierControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching

def authored : LanguageDef := CollectionQuantifiedWorkflow.language.toOption.getD (LanguageDef.empty "")
def language : LanguageDef :=
  (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard CollectionQuantifiedWorkflow.language.isOk
#guard authored.toCore.isOk
#guard language.rewrites.length == 2
#guard language.rewrites[1]?.map (fun rule => rule.premises) ==
  some [.forAll "L" "element" (.forAll "L" "item"
    (.relationQuery "share" [.apply "Witness" [.fvar "Y"], .apply "Witness" [.fvar "item"]]))]
#guard (language.rewrites[1]?.bind (·.bindings)).any fun bindings =>
  bindings.dependencies.contains ("element", []) &&
    bindings.occurrences.contains ⟨"Y", .premise 0 2 0, [0], []⟩ &&
    bindings.occurrences.contains ⟨"item", .premise 0 2 1, [0], []⟩

def term : TypeExpr := .base "Term"
def zero : Pattern := .apply "Zero" []
def one : Pattern := .apply "Successor" [zero]
def witness (value : Pattern) : Pattern := .apply "Witness" [value]
def source (elements : List Pattern) (nested : Bool := false) : Pattern :=
  .apply (if nested then "NestedWrap" else "Wrap") [one, .collection .vec elements none]
def target : Pattern := .apply "Accept" [zero, one]

def provider (copies : Nat := 1) (lastRow : Bool := true) : ProviderSnapshot where
  signatures := [⟨"share", [term, term], [.output, .input]⟩]
  rows := List.replicate copies ⟨"share", [witness zero, witness zero]⟩ ++
    (if lastRow then [⟨"share", [witness one, witness one]⟩] else [])

def admission (copies : Nat := 1) (lastRow : Bool := true) :=
  GeneralExecutionTotalAdmission.compile ⟨language, [], provider copies lastRow⟩
    {equationIndices := some [], includeDerivedEquations := false}

def plan (copies : Nat := 1) (lastRow : Bool := true) := (admission copies lastRow).execution

/-- Local outputs and quantified parameters cannot become an outer result.
The core check rejects the dangling use before a plan can be emitted. -/
def escapingAuthored (metavariable : String) : LanguageDef :=
  {authored with «rewrites» := authored.rewrites.map fun rule =>
    {rule with right := .apply "Accept" [.fvar metavariable, .fvar "outer"]}}

#guard match (escapingAuthored "Y").toCore with
  | .error (.notCore _) => true
  | _ => false
#guard match (escapingAuthored "element").toCore with
  | .error (.notCore _) => true
  | _ => false

def relationEnvironment (copies : Nat := 1) (lastRow : Bool := true) : Engine.RelationEnv where
  tuples := fun relation _ =>
    ((provider copies lastRow).rows.filter (fun row => row.relation == relation)).map (·.values)

def rootReadout {env : Environment} {depth : Nat} {bound : List TypeExpr} {expected : TypeExpr}
    {input : Pattern} {index : Nat} :
    StructuralDescent.Scheduled.Result env (.root depth bound expected input index) → String
  | .root trace captured completed events output _ => reprStr (trace, captured, completed, events, output)

def rootTarget {env : Environment} {depth : Nat} {bound : List TypeExpr} {expected : TypeExpr}
    {input : Pattern} {index : Nat} :
    StructuralDescent.Scheduled.Result env (.root depth bound expected input index) → Pattern
  | .root _ _ _ _ output _ => output

def controls : IO Unit := do
  for (copies, lastRow, nested, elements, expected) in [
      (1, true, false, [zero, one], 1), (2, true, false, [zero, one], 2),
      (1, false, false, [zero, one], 0), (0, false, false, [], 1),
      (1, true, true, [zero, one], 1), (2, true, true, [zero, one], 4),
      (1, false, true, [zero, one], 0), (0, false, true, [], 1)] do
    unless (admission copies lastRow).complete do
      throw (IO.userError "The authored quantified workflow did not pass admission")
    let env := GeneralPlanEnvironment.environment (plan copies lastRow)
    let input := source elements nested
    let goal := StructuralDescent.Scheduled.Goal.root 1 [] term input (if nested then 1 else 0)
    let initial := StructuralDescent.Scheduled.start env goal
    let whole := StructuralDescent.Scheduled.run env goal 1000 initial
    let resumed := StructuralDescent.Scheduled.run env goal 940
      (StructuralDescent.Scheduled.run env goal 60 initial)
    let targets := whole.answers.map rootTarget
    let reference := ReferenceStep.stepsAt (relationEnvironment copies lastRow) language 1 input
    unless StructuralDescent.Scheduled.complete env goal whole && targets.length == expected &&
        targets == List.replicate expected target && targets == reference.map Prod.snd &&
        resumed.answers.map rootReadout == whole.answers.map rootReadout do
      throw (IO.userError "Authored quantification changed scope, source answers, completion or retained histories")
  IO.println "AuthoredQuantifierControls: recursive lowering, local outputs, nested histories, source agreement and resumption passed"

#eval controls

end Mettapedia.GSLT.LanguageDef.CollectionQuantifierControls
