import Mettapedia.OSLF.NativeTypes.Semantics.Operational
import Mettapedia.OSLF.NativeTypes.Modal.QuerySearch
import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Checking
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter

open Mettapedia.OSLF.Framework

/-!
# Readable outputs of the authored native-type generator

The presentation reads actual generated catalogues and selected vertices.
Query summaries retain the check result, the pending work and the ordered
physical receipt origins. A checked assignment is displayed separately from
membership in the complete dependent rely family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Display

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Rules
open ModalHypercube (HSort)

def renderCollection : CollType → String
  | .vec => "Vec"
  | .hashBag => "Bag"
  | .hashSet => "Set"

def renderType : TypeExpr → String
  | .base name => name
  | .arrow domain codomain => "(" ++ renderType domain ++ " -> " ++ renderType codomain ++ ")"
  | .multiBinder body => "Binder(" ++ renderType body ++ ")"
  | .collection kind element => renderCollection kind ++ "(" ++ renderType element ++ ")"

mutual
def renderPattern : Pattern → String
  | .bvar index => "#" ++ toString index
  | .fvar name => "$" ++ name
  | .apply constructor [] => constructor
  | .apply constructor arguments => constructor ++ "(" ++ renderPatterns arguments ++ ")"
  | .lambda name body => "lambda " ++ name.getD "_" ++ ". " ++ renderPattern body
  | .multiLambda count names body =>
      "lambda[" ++ toString count ++ "; " ++ String.intercalate ", " names ++ "]. " ++ renderPattern body
  | .subst body replacement => "subst(" ++ renderPattern body ++ ", " ++ renderPattern replacement ++ ")"
  | .collection kind elements rest =>
      renderCollection kind ++ "[" ++ renderPatterns elements ++
        (rest.map (fun name => " | $" ++ name)).getD "" ++ "]"

def renderPatterns : List Pattern → String
  | [] => ""
  | [term] => renderPattern term
  | term :: next :: rest => renderPattern term ++ ", " ++ renderPatterns (next :: rest)
end

def renderSort : HSort → String
  | .star => "*"
  | .box => "Box"

def renderPosition (position : List Nat) : String :=
  if position.isEmpty then "root" else String.intercalate "/" (position.map toString)

def renderTypes (types : List TypeExpr) : String :=
  "[" ++ String.intercalate ", " (types.map renderType) ++ "]"

def renderOptionSort : Option HSort → String
  | none => "unresolved"
  | some sort => renderSort sort

def renderAdmission : Option Bool → String
  | some true => "admitted"
  | some false => "rejected"
  | none => "unresolved"

def renderLawKind : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Kind → String
  | .equation => "E"
  | .rewrite => "R"

def renderConcreteStatus : Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers.CarrierStatus → String
  | .unclassifiedSource => "unclassified source carrier family"
  | .unsupportedRepresentation => "schematic source outside the concrete-object classifier"
  | .illSortedSource => "no typing in the concrete classifier's declared carrier pool"
  | .classified carriers => "classified " ++ renderTypes carriers

def renderProgramStatus : Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.ProgramCarrierStatus → String
  | .unclassifiedSource => "unclassified declared program carrier family"
  | .unsupportedSubstitution => "substitution source requires a checked typing annotation"
  | .noDeclaredProgramTyping => "no declared base-program typing"
  | .classified carriers => "classified " ++ renderTypes carriers

def shortDiagnostic (text : String) : String :=
  (text.replace "Mettapedia.OSLF.MeTTaIL." "").replace "\n" " "

def renderConnective : Mettapedia.OSLF.NativeTypes.Structural.Connective → String
  | .top => "top"
  | .bottom => "bottom"
  | .conjunction => "and"
  | .disjunction => "or"
  | .implication => "implies"
  | .negation => "not"
  | .structural => "structural"
  | .modal => "modal"

def connectives (generated : Generated) : List Mettapedia.OSLF.NativeTypes.Structural.Connective :=
  [.top, .bottom, .conjunction, .disjunction, .implication, .negation, .structural, .modal].filter
    generated.logicFragment.admits

/-- The operation catalogue is derived from exactly the source stream used
by the compiler, while keeping its executable authored ordering. -/
def operationNames (language : LanguageDef) : List Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Key :=
  (language.terms.map (fun declaration =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Key.constructor declaration.label declaration.params.length) ++
    language.equations.flatMap (fun equation =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.patternKeys equation.left ++ Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.patternKeys equation.right) ++
    language.rewrites.flatMap (fun rule =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.patternKeys rule.left ++ Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.patternKeys rule.right)).eraseDups

theorem operation_names_exact (language : LanguageDef) (key : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Key) :
    key ∈ operationNames language ↔ key ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.operationKeys language := by
  simp [operationNames, Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.operationKeys]

structure OperationView where
  name : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Key
  inputs : List HSort
  output : HSort
  deriving Repr, DecidableEq

def operationViews (generated : Generated) : List OperationView :=
  (operationNames generated.snapshot.language).attach.map fun entry =>
    let operation : (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature generated.snapshot.language).Operation :=
      ⟨entry.val, (operation_names_exact _ _).mp entry.property⟩
    {name := entry.val,
      inputs := List.ofFn fun input : Fin entry.val.arity =>
        generated.vertex.2 ⟨operation, ⟨input.val, Nat.lt_trans input.isLt (Nat.lt_succ_self _)⟩⟩,
      output := generated.vertex.2 ⟨operation, ⟨entry.val.arity, Nat.lt_succ_self _⟩⟩}

structure ModalView where
  index : Nat
  ordinal : Nat
  declaration : Nat
  rule : String
  position : List Nat
  bound : List TypeExpr
  programCarrier : TypeExpr
  focusBound : List TypeExpr
  focusCarrier : TypeExpr
  focus : Option Pattern
  rely : List (String × Option TypeExpr × Option HSort)
  matched : List String
  hidden : List String
  inputSorts : Option (List HSort)
  outputSort : Option HSort
  deriving Repr

def modalView (generated : Generated) (index : Nat) (schema : Schema generated.plan) : ModalView :=
  let assignment := schemaAssignment? generated schema
  let raw := generated.rawSites.find? fun site =>
    site.declaration == schema.declaration.declarationIndex && site.position == schema.position
  {index := index, ordinal := schema.ordinal,
    declaration := schema.declaration.declarationIndex,
    rule := schema.declaration.authored.name,
    position := schema.position, bound := schema.bound,
    programCarrier := schema.programCarrier,
    focusBound := schema.focusBound, focusCarrier := schema.focusCarrier,
    focus := RedexPosition.subtermAt schema.declaration.rule.left schema.position,
    rely := schema.relyNames.map fun name =>
      (name, Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree schema.declaration.rule name,
        assignment.bind fun computed => relySort? computed name),
    matched := schema.matchedNames,
    hidden := (raw.map Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site.hiddenNames).getD [],
    inputSorts := assignment.map Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.Assignment.inputs,
    outputSort := assignment.map Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.Assignment.output}

structure Catalogue where
  language : String
  carriers : List String
  selectedRules : List (Nat × String)
  selectedEquations : List (Nat × ScopedEquationExecution.Orientation × String)
  operationalSites : GeneralTypedSites.OperationalPermissions
  structural : List Mettapedia.OSLF.NativeTypes.Structural.Former
  modal : List ModalView
  operations : List OperationView
  rawSiteCount : Nat
  modalSlotCount : Nat
  operationSlotCount : Nat
  equationAdmission : Option Bool
  directedAdmission : Option Bool
  jointAdmission : Option Bool
  equationDiagnostics : List Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Diagnostic
  directedDiagnostics : List Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Diagnostic
  operationalObligations : List GeneralExecutionAdmission.Obligation
  sourceClassifications : List (Nat × Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers.CarrierStatus)
  programClassifications : List (Nat × Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.ProgramCarrierStatus)
  logic : List Mettapedia.OSLF.NativeTypes.Structural.Connective
  possibilityEnabled : Bool
  deriving Repr

def catalogue (generated : Generated) : Catalogue :=
  let operations := operationViews generated
  {language := generated.snapshot.language.name,
    carriers := generated.snapshot.language.typeNames,
    selectedRules := generated.plan.rules.map fun rule => (rule.declarationIndex, rule.authored.name),
    selectedEquations := generated.plan.equations.map fun equation =>
      (equation.declarationIndex, equation.direction, equation.authored.name),
    operationalSites := generated.plan.permissions.sites,
    structural := generated.structuralCatalogue,
    modal := generated.modalCatalogue.zipIdx.map fun (schema, index) => modalView generated index schema,
    operations := operations,
    rawSiteCount := generated.rawSites.length,
    modalSlotCount := ((Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language).map fun site =>
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.modalFamily generated.snapshot.language site).slotCount).sum,
    operationSlotCount := (operations.map fun operation => operation.inputs.length + 1).sum,
    equationAdmission := generated.equationAdmission,
    directedAdmission := generated.rewriteAdmission,
    jointAdmission := Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission generated,
    equationDiagnostics := (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedEquations generated).diagnostics,
    directedDiagnostics := (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedDirectedLaws generated).diagnostics,
    operationalObligations := generated.plan.obligations,
    sourceClassifications := generated.sourceCarrierStatuses,
    programClassifications := generated.programSourceCarrierStatuses,
    logic := connectives generated,
    possibilityEnabled := generated.logicFragment.core.possibility}

def renderOperationName : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Key → String
  | .constructor name arity => name ++ "/" ++ toString arity
  | .bound index => "bound#" ++ toString index
  | .binder name => "binder(" ++ name.getD "_" ++ ")"
  | .multiBinder count names =>
      "binder[" ++ toString count ++ "; " ++ String.intercalate ", " names ++ "]"
  | .substitution => "substitution"
  | .collection kind elements rest =>
      renderCollection kind ++ "[" ++ toString elements ++ (if rest then "; rest" else "") ++ "]"

def renderOperation (operation : OperationView) : String :=
  renderOperationName operation.name ++ ": (" ++
    String.intercalate ", " (operation.inputs.map renderSort) ++ ") -> " ++ renderSort operation.output

def renderStructural (former : Mettapedia.OSLF.NativeTypes.Structural.Former) : String :=
  "  S" ++ toString former.index ++ " " ++ former.declaration.label ++ "(" ++
    String.intercalate ", " (former.declaration.params.map fun parameter =>
      parameter.bodyName ++ ": " ++ renderType parameter.typeExpr ++
        (if parameter.binderNames.isEmpty then "" else
          " binds " ++ String.intercalate ", " parameter.binderNames)) ++ ") : " ++ former.declaration.category

def renderModal (entry : ModalView) : String :=
  "  M" ++ toString entry.index ++ " @ " ++ renderPosition entry.position ++
    " [decl " ++ toString entry.declaration ++ " " ++ entry.rule ++
    "; plan ordinal " ++ toString entry.ordinal ++ "] " ++
    renderType entry.focusCarrier ++ " -> " ++ renderType entry.programCarrier ++
    "; focus=" ++ (entry.focus.map renderPattern).getD "unresolved" ++
    "; focus-bound=" ++ renderTypes entry.focusBound ++ "\n" ++
    "    rely={" ++ String.intercalate ", " (entry.rely.map fun (name, carrier, sort) =>
      name ++ ": " ++ (carrier.map renderType).getD "unclassified" ++ " @ " ++ renderOptionSort sort) ++
    "}; matched={" ++ String.intercalate ", " entry.matched ++
    "}; hidden={" ++ String.intercalate ", " entry.hidden ++ "}; slots=" ++
    (entry.inputSorts.map (fun sorts => "(" ++ String.intercalate ", " (sorts.map renderSort) ++ ")")).getD
      "unresolved" ++ " -> " ++ renderOptionSort entry.outputSort

def renderDiagnostic : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Diagnostic → String
  | .conditionalPremises kind declaration premises =>
      renderLawKind kind ++ " #" ++ toString declaration ++ ": " ++ toString premises.length ++
        " ordered guard premises require a guarded interpretation"
  | .duplicateVariables kind declaration =>
      renderLawKind kind ++ " #" ++ toString declaration ++ ": duplicate context variable names"
  | .scopedDependencies kind declaration bindings =>
      renderLawKind kind ++ " #" ++ toString declaration ++ ": scoped dependency metadata " ++
        String.intercalate ", " (bindings.dependencies.map fun (name, dependencies) =>
          name ++ ": " ++ renderTypes dependencies)
  | .unencodedLeft kind declaration =>
      renderLawKind kind ++ " #" ++ toString declaration ++ ": left display law is not encoded"
  | .unencodedRight kind declaration =>
      renderLawKind kind ++ " #" ++ toString declaration ++ ": right display law is not encoded"

/-- Engine context permissions are displayed independently of the modal
schema positions generated from the authored rewrite's left-hand side. -/
def renderOperationalSites (permissions : GeneralTypedSites.OperationalPermissions) : String :=
  "root=" ++ toString permissions.enabled ++
    "; constructor arguments=" ++
    (if permissions.allConstructorArguments then "all" else
      "[" ++ String.intercalate ", " (permissions.constructorArguments.map fun (constructor, index) =>
        constructor ++ "/" ++ toString index) ++ "]") ++
    "; under lambda=" ++ toString permissions.underLambda ++
    "; under multi-lambda=" ++ toString permissions.underMultiLambda ++
    "; collections=[" ++ String.intercalate ", " (permissions.collectionKinds.map renderCollection) ++ "]"

def renderCatalogue (output : Catalogue) : String :=
  "Language: " ++ output.language ++ "\n" ++
  "Carriers: " ++ String.intercalate ", " output.carriers ++ "\n" ++
  "Logic: " ++ String.intercalate ", " (output.logic.map renderConnective) ++
    "; empty-context possibility=" ++ toString output.possibilityEnabled ++ "\n" ++
  "Operational rules: " ++ String.intercalate ", " (output.selectedRules.map fun (index, name) =>
      "#" ++ toString index ++ " " ++ name) ++
    "; equation directions=" ++ toString output.selectedEquations.length ++ "\n" ++
  "Operational contexts: " ++ renderOperationalSites output.operationalSites ++ "\n" ++
  "Source positions: " ++ toString output.rawSiteCount ++
    "; typed modal schemas: " ++ toString output.modal.length ++ "\n" ++
  "Cube: " ++ toString output.modalSlotCount ++ " modal slots + " ++
    toString output.operationSlotCount ++ " operation slots; 2^" ++
    toString (output.modalSlotCount + output.operationSlotCount) ++ " vertices\n" ++
  "Selected vertex (uniform partial code-formation interpretation): equations=" ++ renderAdmission output.equationAdmission ++
    "; directed laws=" ++ renderAdmission output.directedAdmission ++
    "; joint center=" ++ renderAdmission output.jointAdmission ++ "\n" ++
  "Structural formers:\n" ++ String.intercalate "\n" (output.structural.map renderStructural) ++ "\n" ++
  "Modal schemas (full rely-family contracts; former admission requires the equation gate):\n" ++
    String.intercalate "\n" (output.modal.map renderModal) ++ "\n" ++
  "Operation profiles: " ++ String.intercalate "; " (output.operations.map renderOperation) ++ "\n" ++
  "Program-source classification: " ++ String.intercalate "; " (output.programClassifications.map
    fun (index, status) => "#" ++ toString index ++ " " ++ renderProgramStatus status) ++ "\n" ++
  "Concrete-source classification: " ++ String.intercalate "; " (output.sourceClassifications.map
    fun (index, status) => "#" ++ toString index ++ " " ++ renderConcreteStatus status) ++ "\n" ++
  "Equation diagnostics: " ++ String.intercalate "; " (output.equationDiagnostics.map renderDiagnostic) ++ "\n" ++
  "Directed-law diagnostics: " ++ String.intercalate "; " (output.directedDiagnostics.map renderDiagnostic) ++ "\n" ++
  "Operational obligations: " ++ shortDiagnostic (reprStr output.operationalObligations)

structure ReceiptView where
  declaration : Nat
  rule : String
  ordinal : Nat
  position : List Nat
  focusBound : List TypeExpr
  representative : Pattern
  target : Pattern
  equationPath : List GeneralOccurrenceSemantics.Conversion
  matched : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  matcherChoices : List GeneralScopedMatchMachine.BagChoice
  premises : List GeneralPremise.Event
  authoredRHS : Pattern
  deriving Repr

def receiptView (receipt : GeneralOccurrenceSemantics.Receipt) : ReceiptView :=
  {declaration := receipt.firing.job.declaration.declarationIndex,
    rule := receipt.firing.job.declaration.authored.name,
    ordinal := receipt.firing.job.ordinal, position := receipt.firing.job.site.address,
    focusBound := receipt.firing.job.site.focusBound,
    representative := receipt.representative, target := receipt.target,
    equationPath := receipt.conversions,
    matched := receipt.firing.captured, completed := receipt.firing.completed,
    matcherChoices := receipt.firing.matcherTrace, premises := receipt.firing.premiseHistory,
    authoredRHS := receipt.firing.job.declaration.authored.right}

def renderAssignment (assignment : ScopedRuleMatching.Assignment) : String :=
  "{" ++ String.intercalate "; " (assignment.map fun (name, value) =>
    name ++ "[dependencies=" ++ renderTypes value.dependencies ++ "; ambient=" ++
      toString value.ambient ++ "]=" ++ renderPattern value.body) ++ "}"

def renderReceipt (receipt : ReceiptView) : String :=
  "  decl #" ++ toString receipt.declaration ++ " " ++ receipt.rule ++
    " @ " ++ renderPosition receipt.position ++ " bound=" ++ renderTypes receipt.focusBound ++
    " -> " ++ renderPattern receipt.target ++ "\n" ++
    "    primitive-events=1; equation-administration=" ++ toString receipt.equationPath.length ++
    "; ordered premises=" ++ toString receipt.premises.length ++
    "; matcher choices=" ++ shortDiagnostic (reprStr receipt.matcherChoices) ++ "\n" ++
    "    authored RHS=" ++ renderPattern receipt.authoredRHS ++
    "; scoped assignment=" ++ renderAssignment receipt.completed

inductive QueryScope where
  | outgoingPossibility
  | outgoingUniversal
  | structuralFormula
  | specifiedModalInstance
  deriving Repr, DecidableEq

def renderScope : QueryScope → String
  | .outgoingPossibility => "native outgoing possibility"
  | .outgoingUniversal => "native outgoing universal (not the incoming OSLF box)"
  | .structuralFormula => "structural/propositional formula"
  | .specifiedModalInstance => "specified modal instance (not full rely-family membership)"

def renderCheck : CheckResult → String
  | .decided true => "proved"
  | .decided false => "refuted"
  | .unknown => "unknown"
  | .refused connective => "refused: connective " ++ renderConnective connective
  | .illFormed (.unsupportedConnective connective) => "refused: connective " ++ renderConnective connective
  | .illFormed (.malformedJudgment expected) => "refused: malformed judgment at " ++ renderType expected
  | .refusedPossibility => "refused: empty-context possibility is disabled"
  | .rejectedCube => "refused: selected equational vertex is rejected"

def taskName {request : GeneralOccurrenceFrontier.Request} : GeneralOccurrenceFrontier.Task request → String
  | .visit _ => "visit representative"
  | .incoming _ _ => "scan incoming equation edges"
  | .universe => "derive finite universe"
  | .scanUniverse _ => "scan finite universe"
  | .equation _ => "equation matcher/premises"
  | .rule _ => "rule matcher/premises"

structure QueryView where
  scope : QueryScope
  source : Pattern
  result : CheckResult
  budget : Nat
  work : Nat
  receipts : List ReceiptView
  pending : List String
  obligations : List GeneralOccurrenceFrontier.Obligation
  sourceAdmitted : Bool
  coverageCertified : Bool
  equationAdmission : Option Bool
  selectedNativeReceipts : Option Nat := none
  deriving Repr

def queryView {generated : Generated} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (scope : QueryScope) (budget : Nat) (run : QueryRun generated bound expected source) : QueryView :=
  let request := generated.request bound expected source
  {scope := scope, source := source, result := run.result, budget := budget,
    work := run.state.work,
    receipts := run.state.answers.map fun answer => receiptView answer.val,
    pending := run.state.agenda.map taskName,
    obligations := run.state.unresolved,
    sourceAdmitted := sourceAdmission request,
    coverageCertified := GeneralOccurrenceFrontier.checkCertificate request run.state,
    equationAdmission := generated.equationAdmission}

/-- Selected native output is annotated from the actual receipt family.
Its length preserves duplicates and original order; it is not endpoint-only
support or a claim of complete outgoing coverage. -/
def nativeReceiptViews (request : GeneralOccurrenceFrontier.Request)
    (state : GeneralOccurrenceFrontier.State request) (test : Pattern → Bool) : List ReceiptView :=
  (Mettapedia.OSLF.NativeTypes.Semantics.Operational.answerOutputs request state test).map fun output => receiptView output.1.val

theorem native_receipt_views_sound {request : GeneralOccurrenceFrontier.Request}
    {state : GeneralOccurrenceFrontier.State request} {test : InvariantTest request} {view : ReceiptView}
    (member : view ∈ nativeReceiptViews request state test.accepts) :
    ∃ output ∈ Mettapedia.OSLF.NativeTypes.Semantics.Operational.answerOutputs request state test.accepts,
      view.declaration = output.1.val.firing.job.declaration.declarationIndex ∧
      view.position = output.1.val.firing.job.site.address ∧
      view.target = output.1.val.target ∧
      Mettapedia.OSLF.NativeTypes.Semantics.Operational.questionPredicate .possibility request test request.root := by
  obtain ⟨output, present, equal⟩ := List.mem_map.mp member
  subst view
  exact ⟨output, present, rfl, rfl, rfl, Mettapedia.OSLF.NativeTypes.Semantics.Operational.output_native_membership output⟩

theorem native_views_retain_all_origins (request : GeneralOccurrenceFrontier.Request)
    (state : GeneralOccurrenceFrontier.State request) (test : Pattern → Bool) :
    nativeReceiptViews request state test =
      (state.answers.filter (fun answer => test answer.val.target)).map (fun answer => receiptView answer.val) := by
  have retained := congrArg (List.map receiptView)
    (Mettapedia.OSLF.NativeTypes.Semantics.Operational.retained_origins_and_multiplicity request state test)
  simpa only [nativeReceiptViews, List.map_map, Function.comp_def] using retained

theorem native_views_preserve_occurrence_count (request : GeneralOccurrenceFrontier.Request)
    (state : GeneralOccurrenceFrontier.State request) :
    (nativeReceiptViews request state (fun _ => true)).length = state.answers.length := by
  rw [native_views_retain_all_origins]
  simp

def nativeQueryView {generated : Generated} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (kind : ModalQuery) (test : InvariantTest (generated.request bound expected source))
    (budget : Nat) (run : QueryRun generated bound expected source) : QueryView :=
  {queryView (match kind with | .possibility => .outgoingPossibility | .outgoingUniversal => .outgoingUniversal)
      budget run with
    selectedNativeReceipts := some (nativeReceiptViews (generated.request bound expected source)
      run.state test.accepts).length}

/-- User-facing execution consumes the actual generator and its independently
interpreted native question, then presents the same certified engine result. -/
def runNative (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (kind : ModalQuery) (test : InvariantTest (generated.request bound expected source))
    (budget : Nat) : QueryView :=
  nativeQueryView kind test budget (generated.searchModal bound expected source kind test budget)

/-- Explicit bounded frontier collection retains later origins after the
question becomes conclusive. It makes no coverage claim without the existing
certificate checker. Ordinary native queries stop after decisive evidence. -/
def collectNative (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (kind : ModalQuery) (test : InvariantTest (generated.request bound expected source))
    (budget : Nat) : QueryView :=
  nativeQueryView kind test budget (generated.checkModal bound expected source kind test budget)

theorem run_native_answer_exact {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound expected source)} {budget : Nat} {answer : Bool}
    (checked : (runNative generated bound expected source kind test budget).result = .decided answer) :
    answer = true ↔
      (GSLTTypeSynthesis.gsltOSLF (Mettapedia.OSLF.NativeTypes.Semantics.Operational.theory generated bound expected)).satisfies
        (generated.request bound expected source).root
        (Mettapedia.OSLF.NativeTypes.Semantics.Operational.questionType kind (generated.request bound expected source) test).pred :=
  Mettapedia.OSLF.NativeTypes.Generation.generated_search_answer_is_native_membership checked

def instanceView {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (budget : Nat) (run : ModalInstanceRun codes assignment term) : QueryView :=
  {scope := .specifiedModalInstance, source := run.request.source,
    result := run.result, budget := budget, work := run.sourceState.work + run.targetState.work,
    receipts := run.responses.map fun response => receiptView response.outcome.receipt,
    pending := run.sourceState.agenda.map taskName ++ run.targetState.agenda.map taskName,
    obligations := run.sourceState.unresolved ++ run.targetState.unresolved,
    sourceAdmitted := sourceAdmission run.request.sourceRequest && sourceAdmission run.request.targetRequest,
    coverageCertified := GeneralOccurrenceFrontier.checkCertificate run.request.sourceRequest run.sourceState &&
      GeneralOccurrenceFrontier.checkCertificate run.request.targetRequest run.targetState,
    equationAdmission := generated.equationAdmission,
    selectedNativeReceipts := some run.responses.length}

def unknownReasons (output : QueryView) : List String :=
  (if output.equationAdmission = none then ["selected equation-law admission is unresolved"] else []) ++
  (if !output.sourceAdmitted then ["the source/operational profile is not admitted"] else []) ++
  (if !output.pending.isEmpty then ["unfinished work: " ++ String.intercalate ", " output.pending] else []) ++
  (if !output.obligations.isEmpty then
    ["unresolved execution obligations: " ++ shortDiagnostic (reprStr output.obligations)] else []) ++
  (if !output.coverageCertified then ["exhaustive occurrence coverage is not certified"] else [])

def renderQuery (title : String) (output : QueryView) : String :=
  title ++ " [" ++ renderScope output.scope ++ "]\n" ++
  "  source: " ++ renderPattern output.source ++ "\n" ++
  "  result: " ++ renderCheck output.result ++ "; budget=" ++ toString output.budget ++
    "; work=" ++ toString output.work ++ "; source-admitted=" ++ toString output.sourceAdmitted ++
    "; exhaustive-coverage=" ++ toString output.coverageCertified ++ "\n" ++
  (if output.result = .unknown then
    "  reason: " ++ String.intercalate "; "
      (if (unknownReasons output).isEmpty then ["the query interpretation remains undecided"]
       else unknownReasons output) ++ "\n"
   else "") ++
  "  receipt count: " ++ toString output.receipts.length ++ "\n" ++
  (output.selectedNativeReceipts.map (fun count =>
    "  retained native answers/responses: " ++ toString count ++ "\n")).getD "" ++
  String.intercalate "\n" (output.receipts.map renderReceipt)

def renderInstanceIssue : ModalInstanceIssue → String
  | .unavailableFormer => "the generated modal former is not admitted"
  | .unavailableFilling => "the scoped assignment cannot fill the authored context"
  | .unavailableRightHandSide => "the scoped assignment cannot instantiate the authored RHS"
  | .noncanonicalSource => "the actual source has noncanonical binder metadata"
  | .noncanonicalTarget => "the specified RHS has noncanonical binder metadata"
  | .untypedFocus => "the focus does not have the generated carrier"
  | .unsupportedAssignment => "the scoped assignment is not admitted"

def renderInstanceError (title : String) (issue : ModalInstanceIssue) : String :=
  title ++ " [specified modal instance]\n  result: refused; reason: " ++ renderInstanceIssue issue

end Mettapedia.OSLF.NativeTypes.Semantics.Display
