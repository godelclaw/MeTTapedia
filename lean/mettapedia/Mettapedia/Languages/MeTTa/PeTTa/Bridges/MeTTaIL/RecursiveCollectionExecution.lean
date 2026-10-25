import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Canonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionSource
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionAccounting
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionNames

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

def library : BridgeKit.Library :=
  ⟨CompleteExecution.collectionBaseLibrary.runtime, source.program,
    ["gslt:recursive-collection:"]⟩

set_option maxRecDepth 100000 in
theorem checked : library.check = true := by decide +kernel

def eventTerm (event : EquationalScopedReceipts.Event) : Term :=
  .application "CollectionEvent" [encodeList Term.natural event.path,
    encodeCollectionType event.kind, encodeList decisionTerm event.decisions]

def answerTerm (answer : Answer) : Term :=
  .application "RecursiveCollectionAnswer" [scopedAssignmentTerm answer.assignment,
    encodeList eventTerm answer.trace]

def workTerm (work : Work) : Term :=
  .application "RecursiveCollectionWork" [scopedAssignmentTerm work.assignment,
    encodeList matcherTaskTerm work.tasks, encodeList eventTerm work.trace]

def stateTerm (state : RecursiveCollectionMachine.State) : Term :=
  .application "RecursiveCollectionState" [encodeList workTerm state.agenda,
    encodeList answerTerm state.answers]

syntax "recursive_collection_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| recursive_collection_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CompleteExecution.pattern_symbol_unmatched, eventTerm, answerTerm, workTerm, stateTerm, encodeList, encodeOption,
        InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

syntax "recursive_from_logged% " "[" str,* "] " term:max : term
macro_rules
  | `(recursive_from_logged% [$names,*] $fact) =>
      `(BridgeKit.Library.lift_call checked (by decide +kernel)
        (by decide) (by decide +kernel) (by decide) [$names,*] (by decide)
        (by rfl) (by decide +kernel)
        (BridgeKit.transport_call CompleteExecution.collection_retained_closed
          CompleteExecution.collection_base_agreement
          (by decide +kernel) (by decide) (by decide +kernel) (by decide)
          [$names,*] (by decide) (by rfl) (by decide +kernel) $fact))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : Effects.State)
    (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact recursive_from_logged% ["left", "right"]
    (by metta_lift CollectionLoggedSearchExecution.checked ["left", "right"]
      (ScopedCollectionExecution.append_returns element state left right))

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : Effects.State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  exact recursive_from_logged% ["items"]
    (by metta_lift CollectionLoggedSearchExecution.checked ["items"]
      (ScopedCollectionExecution.length_returns element state items))

@[metta_head "gslt:collection:allocate"]
theorem allocate_returns {α : Type} (element : α → Term) (state : Effects.State)
    (idempotent : Bool) (count : Nat) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:allocate"
        [encoded (booleanTerm idempotent), number count, encoded (encodeList element items)])
      state (encoded (encodeList (allocationTerm element) (tracedAllocations idempotent count items))) := by
  exact recursive_from_logged% ["idempotent", "count", "items"]
    (by metta_lift CollectionLoggedSearchExecution.checked ["idempotent", "count", "items"]
      (ScopedCollectionExecution.allocate_returns element state idempotent count items))

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
  metta_lift checked ["names", "patterns"]
    (by metta_lift CompleteExecution.collection_base_checked ["names", "patterns"] sorted)

@[metta_head "gslt:canon:dedup-sorted"]
theorem dedup_returns (state : Effects.State) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:canon:dedup-sorted" [encoded (encodeList encodePattern (PatternLexOrder.sortLex items))])
      state (encoded (encodeList encodePattern (PatternLexOrder.sortLex items).dedup)) := by
  have unique := CompleteExecution.dedup_sorted_returns state (PatternLexOrder.sortLex items)
  rw [CompleteExecution.dedupSorted_eq_dedup (PatternLexOrder.sortLex_pairwise items)] at unique
  simp only [CompleteExecution.patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList] at unique
  metta_lift checked ["sorted"]
    (by metta_lift CompleteExecution.collection_base_checked ["sorted"] unique)

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
  exact recursive_from_logged% ["request", "assignment", "task"]
    (by metta_lift CollectionLoggedSearchExecution.checked ["request", "assignment", "task"]
      (by metta_lift ScopedCollectionExecution.checked ["request", "assignment", "task"]
        (by metta_lift CollectionSelectionExecution.checked ["request", "assignment", "task"]
          (transport_call RuleInstantiationExecution.GeneralExecution.MachineTransport.program_closed
            ScopedCollectionExecution.machine_agreement
            (by decide +kernel) (by decide) (by decide +kernel) (by decide)
            ["request", "assignment", "task"] (by decide) rfl (by decide +kernel)
            (matcher_expand_returns state request initial task)))))

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
        cases kind <;> cases actual <;> cases actualRest
        all_goals first
          | exact unordered_expand_returns state names ordered request initial path depth _ schemas rest targets
              (by decide) elements
          | recursive_collection_eval [ordinary]
              unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm, encodePattern,
                encodeCollectionType, encodeRest]
  | arguments path depth index schemas targets | restCapture path depth name kind targets =>
    recursive_collection_eval [ordinary] unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm]
  | bag | bagSelect =>
    recursive_collection_eval unfolding [RecursiveCollectionMachine.expand, matcherTaskTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution
