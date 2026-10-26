import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Canonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionAccounting
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionNames
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff

/-!
# Recursive collection matcher source and execution

The native machine reuses scoped capture/task expansion and the existing
name-table canonical comparison. Its wire retains pending tasks and complete
nested allocation events. Source admission and the typed/premise handoff are
separate consumers of this component.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionMachine
open CanonicalBags CanonicalCompare CollectionSelection
open InferenceCettaWire (encodePattern encodeCollectionType encodeRest)
open RuleInstantiationExecution.GeneralExecution
open RuleInstantiationExecution.ScopedCapture (scopedAssignmentTerm)
open CollectionSelectionExecution (decisionTerm allocationTerm booleanTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_recursive_collection.metta"
    sha256 "e4ed176d2a640e0f98edca03c71ca922c0b5bae94697a50fad9cc2c3496a7628"

def library : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

def eventTerm (event : EquationalScopedReceipts.Event) : Term :=
  .application "CollectionEvent" [encodeList Term.natural event.path,
    encodeCollectionType event.kind, encodeList decisionTerm event.decisions]

private def decodeNatural? : Term → Option Nat
  | .natural index => some index
  | _ => none

def decodeDecision? : Term → Option CollectionSelection.Decision
  | .application "CollectionDecision" [.natural selected, .natural 0] => some ⟨selected, false⟩
  | .application "CollectionDecision" [.natural selected, .natural 1] => some ⟨selected, true⟩
  | _ => none

@[simp] theorem decodeDecision?_decisionTerm (decision : CollectionSelection.Decision) :
    decodeDecision? (CollectionSelectionExecution.decisionTerm decision) = some decision := by
  rcases decision with ⟨selected, retained⟩
  cases retained <;> rfl

def decodeEvent? : Term → Option EquationalScopedReceipts.Event
  | .application "CollectionEvent" [path, kind, decisions] => do
      pure ⟨← decodeList decodeNatural? path, ← InferenceCettaWire.decodeCollectionType kind,
        ← decodeList decodeDecision? decisions⟩
  | _ => none

@[simp] theorem decodeEvent?_eventTerm (event : EquationalScopedReceipts.Event) :
    decodeEvent? (eventTerm event) = some event := by
  rcases event with ⟨path, kind, decisions⟩
  have naturals : decodeList decodeNatural? (encodeList Term.natural path) = some path :=
    decodeList_encodeList decodeNatural? Term.natural (fun _ => rfl) path
  simp [eventTerm, decodeEvent?, decodeList_encodeList, naturals]

theorem eventTerm_injective : Function.Injective eventTerm := by
  intro first second same
  have decoded := congrArg decodeEvent? same
  simpa only [decodeEvent?_eventTerm, Option.some.injEq] using decoded

theorem decodeDecision?_invalid_retention (selected : Nat) :
    decodeDecision? (.application "CollectionDecision" [.natural selected, .natural 2]) = none := rfl

#print axioms decodeDecision?_decisionTerm
#print axioms decodeEvent?_eventTerm
#print axioms eventTerm_injective
#print axioms decodeDecision?_invalid_retention


def answerTerm (answer : Answer) : Term :=
  .application "RecursiveCollectionAnswer" [scopedAssignmentTerm answer.assignment,
    encodeList eventTerm answer.trace]

def workTerm (work : Work) : Term :=
  .application "RecursiveCollectionWork" [scopedAssignmentTerm work.assignment,
    encodeList matcherTaskTerm work.tasks, encodeList eventTerm work.trace]

def stateTerm (state : RecursiveCollectionMachine.State) : Term :=
  .application "RecursiveCollectionState" [encodeList workTerm state.agenda,
    encodeList answerTerm state.answers]

/-- A cached normalized request accompanies its retained allocation machine. -/
def canonicalStateTerm (machine : Request × RecursiveCollectionMachine.State) : Term :=
  .application "CanonicalMatchingState" [matcherRequestTerm machine.1, stateTerm machine.2]

/-- Premise frames read the same two-field answer wire for either matcher;
the allocation events remain the full recursive collection events. -/
def canonicalAnswerTerm (answer : RecursiveCollectionMachine.Answer) : Term :=
  .application "ScopedMatcherAnswer" [scopedAssignmentTerm answer.assignment,
    encodeList eventTerm answer.trace]


section RecursiveProofMetadata

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

private def recursiveProofSource : Program := (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program

theorem recursiveProof_source_quote : recursiveProofSource = source.program := by rfl

private def recursiveObservedInheritedHeads : List String :=
  ((recursiveProofSource.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(recursiveProofSource.equations.map (·.head)).contains head)).eraseDups

/-- Direct outward calls derived from the actual family bodies. -/
def recursiveProofInheritedHeads : List String := ["gslt:canon:sort", "gslt:canon:dedup-sorted", "gslt:automata:length", "gslt:automata:append", "gslt:rule:scope-matcher-expand", "gslt:collection:allocate", "gslt:canon:canon", "gslt:rule:row-at"]

theorem recursiveProofInheritedHeads_derived :
    recursiveObservedInheritedHeads = recursiveProofInheritedHeads := by decide +kernel

theorem recursiveProof_source_count : recursiveProofSource.equations.length = 18 := by decide +kernel

theorem recursiveProof_inherited_count : recursiveObservedInheritedHeads.length = 8 := by
  rw [recursiveProofInheritedHeads_derived]
  decide +kernel

private def recursiveScopedMetadataEquations : List SpaceSemantics.Equation :=
  [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[176]'(by decide +kernel)]

private def recursivePriorMetadataEquations : List SpaceSemantics.Equation :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.equations[16]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.equations[17]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.equations[19]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.equations[4]'(by decide +kernel)]

private def recursiveScopedMetadataDeclarations : List Atom :=
  [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[176]'(by decide +kernel)]

private def recursivePriorMetadataDeclarations : List Atom :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.declarations[16]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.declarations[17]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.declarations[19]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.declarations[4]'(by decide +kernel)]

private def recursiveMetadataBase : Program where
  equations := recursiveScopedMetadataEquations ++ recursivePriorMetadataEquations
  declarations := recursiveScopedMetadataDeclarations ++ recursivePriorMetadataDeclarations

/-- Bounded call and constructor metadata; execution remains in the shared Raw program. -/
def recursiveProofLibrary : Library := ⟨recursiveMetadataBase, recursiveProofSource, ["gslt:recursive-collection:"]⟩

def recursiveProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || recursiveProofLibrary.owns head || recursiveProofInheritedHeads.contains head

theorem recursiveProof_checked : recursiveProofLibrary.check = true := by decide +kernel

theorem recursiveProof_equation_count : recursiveProofLibrary.runtime.equations.length = 26 := by decide +kernel

private def recursivePriorSources := RuleExecutionProgram.interpretedPremiseSupportSources.take 10
private def recursiveLaterSources := RuleExecutionProgram.interpretedPremiseSupportSources.drop 11

private theorem recursiveScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => recursiveProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨65, by decide +kernel⟩, ⟨176, by decide +kernel⟩] := by decide +kernel

private theorem recursiveScoped_equations : RuleExecutionProgram.scopedProgram.equations.filter (fun row => recursiveProofHeads row.head) = recursiveScopedMetadataEquations := by
  rw [CompleteExecution.source_filter_indices, recursiveScoped_equations_indices]
  rfl

private theorem recursivePrior_equations_indices :
    (List.finRange (recursivePriorSources.flatMap (fun source => source.program.equations)).length).filter (fun index => (fun row => recursiveProofHeads row.head) ((recursivePriorSources.flatMap (fun source => source.program.equations)).get index)) =
      [⟨146, by decide +kernel⟩, ⟨147, by decide +kernel⟩, ⟨149, by decide +kernel⟩, ⟨164, by decide +kernel⟩] := by decide +kernel

private theorem recursivePrior_equations : (recursivePriorSources.flatMap (fun source => source.program.equations)).filter (fun row => recursiveProofHeads row.head) = recursivePriorMetadataEquations := by
  rw [CompleteExecution.source_filter_indices, recursivePrior_equations_indices]
  rfl

private theorem recursiveOwned_equations : recursiveProofSource.equations.filter (fun row => recursiveProofHeads row.head) = recursiveProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem recursiveLater_equations : (recursiveLaterSources.flatMap (fun source => source.program.equations)).filter (fun row => recursiveProofHeads row.head) = [] := by
  have checked : (recursiveLaterSources.flatMap (fun source => source.program.equations)).all (fun row => !((fun row => recursiveProofHeads row.head) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem recursiveSupport_equations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations) =
      (recursivePriorSources.flatMap (fun source => source.program.equations)) ++ recursiveProofSource.equations ++ (recursiveLaterSources.flatMap (fun source => source.program.equations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      recursivePriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)) :: recursiveLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem recursiveProof_physical_equations : recursiveProofLibrary.runtime.equations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter (fun row => recursiveProofHeads row.head) := by
  rw [CompleteExecution.PhysicalSourceAgreement.fold_equations, recursiveSupport_equations]
  simp only [List.filter_append, recursiveScoped_equations, recursivePrior_equations,
    recursiveOwned_equations, recursiveLater_equations, List.append_nil]
  change (recursiveScopedMetadataEquations ++ recursivePriorMetadataEquations) ++ recursiveProofSource.equations = _
  simp only [List.append_assoc]

private theorem recursiveScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration recursiveProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨65, by decide +kernel⟩, ⟨176, by decide +kernel⟩] := by decide +kernel

private theorem recursiveScoped_declarations : RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration recursiveProofHeads) = recursiveScopedMetadataDeclarations := by
  rw [CompleteExecution.source_filter_indices, recursiveScoped_declarations_indices]
  rfl

private theorem recursivePrior_declarations_indices :
    (List.finRange (recursivePriorSources.flatMap (fun source => source.program.declarations)).length).filter (fun index => (retainedCallDeclaration recursiveProofHeads) ((recursivePriorSources.flatMap (fun source => source.program.declarations)).get index)) =
      [⟨146, by decide +kernel⟩, ⟨147, by decide +kernel⟩, ⟨149, by decide +kernel⟩, ⟨164, by decide +kernel⟩] := by decide +kernel

private theorem recursivePrior_declarations : (recursivePriorSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration recursiveProofHeads) = recursivePriorMetadataDeclarations := by
  rw [CompleteExecution.source_filter_indices, recursivePrior_declarations_indices]
  rfl

private theorem recursiveOwned_declarations : recursiveProofSource.declarations.filter (retainedCallDeclaration recursiveProofHeads) = recursiveProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem recursiveLater_declarations : (recursiveLaterSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration recursiveProofHeads) = [] := by
  have checked : (recursiveLaterSources.flatMap (fun source => source.program.declarations)).all (fun row => !((retainedCallDeclaration recursiveProofHeads) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem recursiveSupport_declarations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations) =
      (recursivePriorSources.flatMap (fun source => source.program.declarations)) ++ recursiveProofSource.declarations ++ (recursiveLaterSources.flatMap (fun source => source.program.declarations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      recursivePriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)) :: recursiveLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem recursiveProof_physical_declarations : recursiveProofLibrary.runtime.declarations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter (retainedCallDeclaration recursiveProofHeads) := by
  rw [CompleteExecution.PhysicalSourceAgreement.fold_declarations, recursiveSupport_declarations]
  simp only [List.filter_append, recursiveScoped_declarations, recursivePrior_declarations,
    recursiveOwned_declarations, recursiveLater_declarations, List.append_nil]
  change (recursiveScopedMetadataDeclarations ++ recursivePriorMetadataDeclarations) ++ recursiveProofSource.declarations = _
  simp only [List.append_assoc]

theorem recursiveProof_agreement :
    ProgramAgreementOn recursiveProofHeads recursiveProofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram := by
  have physical : ProgramAgreementOn recursiveProofHeads recursiveProofLibrary.runtime
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram) :=
    fragment_agreement _ _ recursiveProof_physical_equations recursiveProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) CompleteExecution.PhysicalSourceAgreement.physical_interpreted_agreement)

/-- The metadata does not assert closure of inherited primitive bodies. -/
theorem recursiveProof_not_closed : ¬ ProgramClosed recursiveProofHeads recursiveProofLibrary.runtime := by
  intro closed
  let row := recursiveMetadataBase.equations[3]'(by decide +kernel)
  have member : row ∈ recursiveProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : recursiveProofHeads row.head = true := by decide +kernel
  have outside : codeWithin recursiveProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms recursiveProof_source_quote
#print axioms recursiveProofInheritedHeads_derived
#print axioms recursiveProof_source_count
#print axioms recursiveProof_inherited_count
#print axioms recursiveProof_checked
#print axioms recursiveProof_equation_count
#print axioms recursiveProof_agreement
#print axioms recursiveProof_not_closed

end RecursiveProofMetadata

syntax "recursive_collection_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| recursive_collection_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in recursiveProof_checked using recursiveProof_agreement; metta_eval [$facts,*] with recursiveProof_checked in recursiveProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CompleteExecution.pattern_symbol_unmatched, eventTerm, answerTerm, workTerm, stateTerm, encodeList, encodeOption,
        InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : Effects.State)
    (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact ScopedCollectionExecution.append_returns element state left right

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : Effects.State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  exact ScopedCollectionExecution.length_returns element state items

@[metta_head "gslt:collection:allocate"]
theorem allocate_returns {α : Type} (element : α → Term) (state : Effects.State)
    (idempotent : Bool) (count : Nat) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:allocate"
        [encoded (booleanTerm idempotent), number count, encoded (encodeList element items)])
      state (encoded (encodeList (allocationTerm element) (tracedAllocations idempotent count items))) := by
  exact ScopedCollectionExecution.allocate_returns element state idempotent count items

@[metta_head "gslt:canon:sort"]
theorem sort_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (items : List Pattern)
    (covered : ∀ item ∈ items, Covered names item) :
    PureReturns library.runtime [] state
      (apply "gslt:canon:sort" [encoded (encodeList Term.string names), encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (PatternLexOrder.sortLex items))) := by
  have sorted := CompleteExecution.sort_returns state names items covered
  rw [sortBy_eq_sortLex ordered covered] at sorted
  simp only [CompleteExecution.patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList] at sorted
  exact sorted

@[metta_head "gslt:canon:dedup-sorted"]
theorem dedup_returns (state : Effects.State) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:canon:dedup-sorted" [encoded (encodeList encodePattern (PatternLexOrder.sortLex items))])
      state (encoded (encodeList encodePattern (PatternLexOrder.sortLex items).dedup)) := by
  have unique := CompleteExecution.dedup_sorted_returns state (PatternLexOrder.sortLex items)
  rw [CompleteExecution.dedupSorted_eq_dedup (PatternLexOrder.sortLex_pairwise items)] at unique
  simp only [CompleteExecution.patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList] at unique
  exact unique

@[metta_head "gslt:recursive-collection:arrange"]
theorem arrange_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (kind : CollType) (items : List Pattern)
    (covered : ∀ item ∈ items, Covered names item) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:arrange" [encoded (encodeList Term.string names),
        encoded (encodeCollectionType kind), encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (arrange kind items))) := by
  cases kind with
  | vec => recursive_collection_eval unfolding [arrange, encodeCollectionType]
  | hashBag =>
    recursive_collection_eval [sort_returns state names ordered items covered]
      unfolding [arrange, encodeCollectionType]
  | hashSet =>
    recursive_collection_eval [sort_returns state names ordered items covered, dedup_returns state items]
      unfolding [arrange, encodeCollectionType]

@[metta_head "gslt:recursive-collection:inherit"]
theorem inherit_returns (state : Effects.State) : ∀ works : List GeneralScopedMatchMachine.Work,
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:inherit" [encoded (encodeList matcherWorkTerm works)])
      state (encoded (encodeList workTerm (works.map inheritWork)))
  | [] => by recursive_collection_eval
  | work :: tail => by
    recursive_collection_eval [inherit_returns state tail]
      unfolding [matcherWorkTerm, inheritWork, List.map_cons]

@[metta_head "gslt:recursive-collection:start"]
theorem start_returns (state : Effects.State) (request : Request) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:start" [encoded (matcherRequestTerm request)])
      state (encoded (stateTerm (start request))) := by
  simp only [RecursiveCollectionMachine.start, matcherRequestTerm, stateTerm]
  recursive_collection_eval

@[metta_head "gslt:recursive-collection:complete"]
theorem complete_returns (state : Effects.State) (machine : RecursiveCollectionMachine.State) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:complete" [encoded (stateTerm machine)])
      state (Effects.boolean (complete machine)) := by
  cases agenda : machine.agenda <;>
    simp only [RecursiveCollectionMachine.complete, agenda, List.isEmpty_nil, List.isEmpty_cons] <;>
    recursive_collection_eval unfolding [agenda]

@[metta_head "gslt:rule:scope-matcher-expand"]
theorem ordinary_expand_returns (state : Effects.State) (request : Request)
    (initial : ScopedRuleMatching.Assignment) (task : Task) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-matcher-expand" [encoded (matcherRequestTerm request),
        encoded (scopedAssignmentTerm initial), encoded (matcherTaskTerm task)])
      state (encoded (encodeList matcherWorkTerm
        (GeneralScopedMatchMachine.expand request initial task))) := by
  exact transport_call RuleInstantiationExecution.GeneralExecution.MachineTransport.program_closed
    ScopedCollectionExecution.machine_agreement
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["request", "assignment", "task"] (by decide) rfl (by decide +kernel)
    (matcher_expand_returns state request initial task)

@[metta_head "gslt:recursive-collection:ordinary"]
theorem ordinary_returns (state : Effects.State) (request : Request)
    (initial : ScopedRuleMatching.Assignment) (task : Task) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:ordinary" [encoded (matcherRequestTerm request),
        encoded (scopedAssignmentTerm initial), encoded (matcherTaskTerm task)])
      state (encoded (encodeList workTerm
        ((GeneralScopedMatchMachine.expand request initial task).map inheritWork))) := by
  recursive_collection_eval [ordinary_expand_returns state request initial task,
    inherit_returns state (GeneralScopedMatchMachine.expand request initial task)]

@[metta_head "gslt:recursive-collection:allocation"]
theorem allocation_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (path : List Nat) (depth : Nat)
    (initial : ScopedRuleMatching.Assignment) (kind : CollType)
    (schemas : List Pattern) (rest : Option String) (allocation : Allocation Pattern)
    (covered : ∀ item ∈ allocation.residual, Covered names item) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:allocation" [encoded (encodeList Term.string names),
        encoded (encodeList Term.natural path), number depth, encoded (scopedAssignmentTerm initial),
        encoded (encodeCollectionType kind), encoded (encodeList encodePattern schemas),
        encoded (encodeRest rest), encoded (allocationTerm encodePattern allocation)])
      state (encoded (encodeOption workTerm (allocationWork path depth initial kind schemas rest allocation))) := by
  cases rest with
  | none =>
    cases residual : arrange kind allocation.residual with
    | nil =>
      recursive_collection_eval [arrange_returns state names ordered kind allocation.residual covered]
        unfolding [allocationTerm, decisionTerm, booleanTerm, allocationWork, residual,
          matcherTaskTerm, encodeRest]
    | cons value tail =>
      recursive_collection_eval [arrange_returns state names ordered kind allocation.residual covered]
        unfolding [allocationTerm, decisionTerm, booleanTerm, allocationWork, residual,
          matcherTaskTerm, encodeRest]
  | some name =>
    recursive_collection_eval [arrange_returns state names ordered kind allocation.residual covered,
      length_returns encodePattern state schemas,
      append_returns Term.natural state path [schemas.length]]
      unfolding [allocationTerm, decisionTerm, booleanTerm, allocationWork, matcherTaskTerm, encodeRest]

@[metta_head "gslt:recursive-collection:allocations"]
theorem allocations_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (path : List Nat) (depth : Nat)
    (initial : ScopedRuleMatching.Assignment) (kind : CollType)
    (schemas : List Pattern) (rest : Option String) :
    ∀ allocations : List (Allocation Pattern),
    (∀ allocation ∈ allocations, ∀ item ∈ allocation.residual, Covered names item) →
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:allocations" [encoded (encodeList Term.string names),
        encoded (encodeList Term.natural path), number depth, encoded (scopedAssignmentTerm initial),
        encoded (encodeCollectionType kind), encoded (encodeList encodePattern schemas),
        encoded (encodeRest rest), encoded (encodeList (allocationTerm encodePattern) allocations)])
      state (encoded (encodeList workTerm
        (allocations.filterMap (allocationWork path depth initial kind schemas rest))))
  | [], _ => by recursive_collection_eval
  | allocation :: tail, covered => by
    have first := allocation_returns state names ordered path depth initial kind schemas rest allocation
      (covered allocation List.mem_cons_self)
    have later := allocations_returns state names ordered path depth initial kind schemas rest tail
      (fun other member => covered other (List.mem_cons_of_mem _ member))
    cases produced : allocationWork path depth initial kind schemas rest allocation with
    | none =>
      rw [produced] at first
      recursive_collection_eval [first, later] unfolding [List.filterMap_cons, produced]
    | some work =>
      rw [produced] at first
      recursive_collection_eval [first, later] unfolding [List.filterMap_cons, produced]

@[metta_head "gslt:recursive-collection:branches"]
theorem branches_returns (state : Effects.State) (tasks : List Task)
    (trace : List EquationalScopedReceipts.Event) : ∀ branches : List Work,
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:branches" [encoded (encodeList workTerm branches),
        encoded (encodeList matcherTaskTerm tasks), encoded (encodeList eventTerm trace)])
      state (encoded (encodeList workTerm
        (branches.map fun branch => ⟨branch.assignment, branch.tasks ++ tasks, trace ++ branch.trace⟩)))
  | [] => by recursive_collection_eval
  | branch :: tail => by
    recursive_collection_eval [branches_returns state tasks trace tail,
      append_returns matcherTaskTerm state branch.tasks tasks,
      append_returns eventTerm state trace branch.trace] unfolding [List.map_cons]

private theorem unordered_expand_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (initial : ScopedRuleMatching.Assignment)
    (path : List Nat) (depth : Nat) (kind : CollType) (schemas : List Pattern)
    (rest : Option String) (targets : List Pattern) (unordered : kind ≠ .vec)
    (covered : ∀ target ∈ targets, Covered names target) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:expand" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), encoded (scopedAssignmentTerm initial),
        encoded (matcherTaskTerm (.tree path depth (.collection kind schemas rest)
          (.collection kind targets none)))])
      state (encoded (encodeList workTerm (expand request initial
        (.tree path depth (.collection kind schemas rest) (.collection kind targets none))))) := by
  have allocatedCoverage :
      ∀ allocation ∈ tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets),
      ∀ item ∈ allocation.residual, Covered names item := by
    intro allocation generated item inside
    exact covered item ((arrange_mem _).mp ((tracedAllocations_residual_sublist generated).subset inside))
  have arranged := arrange_returns state names ordered kind targets covered
  have count := length_returns encodePattern state schemas
  have selected := allocate_returns encodePattern state (kind == .hashSet) schemas.length (arrange kind targets)
  have expanded := allocations_returns state names ordered path depth initial kind schemas rest
    (tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets)) allocatedCoverage
  cases kind with
  | vec => contradiction
  | hashBag | hashSet =>
    recursive_collection_eval [arranged, count, selected, expanded]
      unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm, encodePattern,
        encodeCollectionType, encodeRest, booleanTerm]

private theorem collection_pair_expand_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (initial : ScopedRuleMatching.Assignment)
    (path : List Nat) (depth : Nat) (kind actual : CollType) (schemas targets : List Pattern)
    (rest actualRest : Option String) (elements : ∀ target ∈ targets, Covered names target) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:expand" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), encoded (scopedAssignmentTerm initial),
        encoded (matcherTaskTerm (.tree path depth (.collection kind schemas rest)
          (.collection actual targets actualRest)))])
      state (encoded (encodeList workTerm (expand request initial
        (.tree path depth (.collection kind schemas rest) (.collection actual targets actualRest))))) := by
  have ordinary := ordinary_returns state request initial
    (.tree path depth (.collection kind schemas rest) (.collection actual targets actualRest))
  cases kind <;> cases actual <;> cases actualRest
  all_goals first
    | exact unordered_expand_returns state names ordered request initial path depth _ schemas rest targets
        (by decide) elements
    | recursive_collection_eval [ordinary]
        unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm, encodePattern,
          encodeCollectionType, encodeRest]

/-- Native expansion retains the exact pending scoped tasks and complete
allocation events. Table coverage is checked on the task's actual targets. -/
@[metta_head "gslt:recursive-collection:expand"]
theorem expand_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (initial : ScopedRuleMatching.Assignment)
    (task : Task) (covered : TaskCovered names task) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:expand" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), encoded (scopedAssignmentTerm initial),
        encoded (matcherTaskTerm task)])
      state (encoded (encodeList workTerm (expand request initial task))) := by
  have ordinary := ordinary_returns state request initial task
  cases task with
  | tree path depth schema target =>
    cases schema with
    | fvar name | bvar index | apply label schemas | lambda display body
    | multiLambda arity displays body | subst body replacement =>
      recursive_collection_eval [ordinary]
        unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm, encodePattern]
    | collection kind schemas rest =>
      cases target with
      | fvar name | bvar index | apply label targets | lambda display body
      | multiLambda arity displays body | subst body replacement =>
        recursive_collection_eval [ordinary]
          unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm, encodePattern]
      | collection actual targets actualRest =>
        have source := covered (.collection actual targets actualRest) (by simp [taskTargets])
        have elements : ∀ target ∈ targets, Covered names target :=
          covered_elements.mp (fun name named => source name (List.mem_append_left _ named))
        exact collection_pair_expand_returns state names ordered request initial path depth
          kind actual schemas targets rest actualRest elements
  | arguments path depth index schemas targets | restCapture path depth name kind targets =>
    recursive_collection_eval [ordinary] unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm]
  | bag | bagSelect =>
    recursive_collection_eval unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL CanonicalCompare RecursiveCollectionMachine

def canonicalCodec : MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution where
  choiceTerm := RecursiveCollectionExecution.eventTerm
  stateTerm := RecursiveCollectionExecution.canonicalStateTerm

theorem canonical_matcherAnswer (answer : RecursiveCollectionMachine.Answer) :
    matcherAnswerTerm canonicalCodec answer = RecursiveCollectionExecution.canonicalAnswerTerm answer := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.checked
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.eventTerm_injective
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.decodeDecision?_invalid_retention
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_source_quote
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProofInheritedHeads_derived
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_source_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_inherited_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_checked
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_equation_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.recursiveProof_not_closed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.append_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.length_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.allocate_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.sort_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.dedup_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.arrange_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.inherit_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.ordinary_expand_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.ordinary_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.allocation_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.allocations_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.branches_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.expand_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonicalStateTerm
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonicalAnswerTerm
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.canonicalCodec
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.canonical_matcherAnswer
