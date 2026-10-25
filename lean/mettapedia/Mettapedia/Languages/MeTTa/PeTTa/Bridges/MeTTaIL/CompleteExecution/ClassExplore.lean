import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchExplore
import Mettapedia.OSLF.MeTTaIL.Complete.Settled

/-!
# Fair exploration of every run modulo equations, in standard or canonical form

`gslt:explore:*` runs `Complete.Explore` over `Complete.Normalized.search`. Each round gives
every node one unit of work; the receipts its search newly publishes become children, which
start fresh searches at the committed forms of their targets, unless a node already has that
state. Every node's search is ready, so each round prints the model's explorer. In canonical
form, presentations that differ only by the order of an unordered collection are one state.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope Declared ClassReady)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open StandardWire (commitTerm TableFor)

variable (plan : GeneralExecutionAdmission.Plan)

/-- A node of the explorer modulo equations. -/
abbrev ClassNode := Node Pattern (Complete.Classes.State plan) GeneralOccurrenceSemantics.Receipt

/-- The explorer modulo equations. -/
abbrev ClassExplorer := Explorer Pattern (Complete.Classes.State plan) GeneralOccurrenceSemantics.Receipt

def nodeTerm (node : ClassNode plan) : Term :=
  .application "ExploreNode" [InferenceCettaWire.encodePattern node.state, encodeList classReceiptTerm node.receipts,
    encodeList InferenceCettaWire.encodePattern node.states, .natural node.born, classStateTerm plan node.run,
    .natural node.consumed]

def explorerTerm (explorer : ClassExplorer plan) : Term :=
  .application "Explorer" [.natural explorer.round, encodeList (nodeTerm plan) explorer.nodes]

def expandedTerm (expanded : List (ClassNode plan) × List (ClassNode plan)) : Term :=
  .application "Expanded" [encodeList (nodeTerm plan) expanded.1, encodeList (nodeTerm plan) expanded.2]

/-- One expanded node with its children. -/
def expandedNodeTerm (expanded : ClassNode plan × List (ClassNode plan)) : Term :=
  .application "Expanded" [nodeTerm plan expanded.1, encodeList (nodeTerm plan) expanded.2]

/-- The child of a published receipt. -/
def childNode (bound : List TypeExpr) (expected : TypeExpr) (mode : Complete.Normalized.Commit) (born : Nat)
    (receipts : List GeneralOccurrenceSemantics.Receipt) (states : List Pattern)
    (receipt : GeneralOccurrenceSemantics.Receipt) : ClassNode plan :=
  ⟨(Complete.Normalized.search plan bound expected mode).target receipt, receipt :: receipts,
    (Complete.Normalized.search plan bound expected mode).target receipt :: states, born,
    (Complete.Normalized.search plan bound expected mode).run
      ((Complete.Normalized.search plan bound expected mode).target receipt) 0, 0⟩

variable {plan}

/-- A node whose search is ready. -/
def NodeReady (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String) (node : ClassNode plan) :
    Prop :=
  SearchReady bound expected footprint node.run

theorem expand_ready {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) (mode : Complete.Normalized.Commit) (round : Nat) {node : ClassNode plan}
    (ready : NodeReady bound expected footprint node) :
    NodeReady bound expected footprint
        (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round node).1 ∧
      ∀ child ∈ (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round node).2,
        NodeReady bound expected footprint child := by
  have next := searchReady_rounds scope 1 ready
  refine ⟨next, ?_⟩
  intro child member
  simp only [Complete.Explore.expand, List.mem_map] at member
  obtain ⟨receipt, published, rfl⟩ := member
  exact searchReady_begin scope
    (Complete.Normalized.target_within plan bound expected receipt footprint
      (next.1.log receipt (List.mem_of_mem_drop published)) mode)

theorem step_ready {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) (mode : Complete.Normalized.Commit) {explorer : ClassExplorer plan}
    (ready : ∀ node ∈ explorer.nodes, NodeReady bound expected footprint node) :
    ∀ node ∈ (Complete.Explore.step (Complete.Normalized.search plan bound expected mode) explorer).nodes,
      NodeReady bound expected footprint node := by
  intro node member
  simp only [Complete.Explore.step, List.mem_append, List.mem_map] at member
  rcases member with ⟨pair, ⟨original, inside, rfl⟩, rfl⟩ | kept
  · exact (expand_ready scope mode _ (ready original inside)).1
  · obtain ⟨pair, listed, child⟩ := List.mem_flatMap.mp (Complete.Explore.fresh_subset _ _ node kept)
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp listed
    exact (expand_ready scope mode _ (ready original inside)).2 node child

theorem rounds_ready {bound : List TypeExpr} {expected : TypeExpr} {footprint : List String}
    (scope : Scope plan footprint) (mode : Complete.Normalized.Commit) :
    ∀ (work : Nat) (explorer : ClassExplorer plan), (∀ node ∈ explorer.nodes, NodeReady bound expected footprint node) →
      ∀ node ∈ (Complete.Settled.roundsUntilSettled (Complete.Normalized.search plan bound expected mode) work
        explorer).nodes, NodeReady bound expected footprint node
  | 0, _, ready => ready
  | work + 1, explorer, ready => by
    simp only [Complete.Settled.roundsUntilSettled]
    split
    · exact ready
    · exact rounds_ready scope mode work _ (step_ready scope mode ready)

variable (plan)

/-- **Exploration starts at the source's standard form.** -/
@[metta_head "gslt:explore:begin"]
theorem explore_begin_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (ready : CommitReady mode names source) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:begin" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
        patternValue source])
      state (encoded (explorerTerm plan
        (Complete.Explore.begin (Complete.Normalized.search plan bound expected mode)
          (Complete.Normalized.commit plan mode source)))) := by
  have standard := runner_standard_returns plan state mode names named source ready
  have started := search_run_zero_returns plan state table bound expected footprint tabled declared
    (Complete.Normalized.commit plan mode source)
    (Complete.Normalized.commit_within plan mode source footprint inside)
  runner_eval [standard, started]
    unfolding [explorerTerm, nodeTerm, Complete.Explore.begin, Complete.Normalized.search, Complete.Classes.search,
      classSearchBackend, Complete.Classes.rounds, encodeList, patternValue]

@[metta_head "gslt:explore:children"]
theorem explore_children_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (born : Nat) (receipts : List GeneralOccurrenceSemantics.Receipt)
    (states : List Pattern) : ∀ published : List GeneralOccurrenceSemantics.Receipt,
      (∀ receipt ∈ published, (∀ name ∈ receipt.target.freeFvarNames, name ∈ footprint) ∧
        Complete.Classes.Checked plan bound expected receipt.target) →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:explore:children" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
          number born, encoded (encodeList classReceiptTerm receipts),
          encoded (encodeList InferenceCettaWire.encodePattern states), encoded (encodeList classReceiptTerm published)])
        state (encoded (encodeList (nodeTerm plan)
          (published.map (childNode plan bound expected mode born receipts states))))
  | [], _ => by
    runner_eval unfolding [encodeList]
  | receipt :: rest, inside => by
    have target := search_target_returns plan state mode names named bound expected receipt
      (inside receipt (by simp)).2
    have fresh := search_run_zero_returns plan state table bound expected footprint tabled declared
      ((Complete.Normalized.search plan bound expected mode).target receipt)
      (Complete.Normalized.target_within plan bound expected receipt footprint (inside receipt (by simp)).1 mode)
    have later := explore_children_returns state mode names named table bound expected footprint tabled declared born
      receipts states rest (fun other member => inside other (by simp [member]))
    runner_eval [target, fresh, later]
      unfolding [encodeList, List.map_cons, childNode, nodeTerm, Complete.Normalized.search, Complete.Classes.search,
        classSearchBackend, Complete.Classes.rounds, patternValue]

@[metta_head "gslt:explore:expand"]
theorem explore_expand_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (round : Nat) (node : ClassNode plan)
    (ready : NodeReady bound expected footprint node) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:expand" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
        number round, encoded (nodeTerm plan node)])
      state (encoded (expandedNodeTerm plan
        (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round node))) := by
  obtain ⟨current, receipts, states, born, run, consumed⟩ := node
  have runReady : SearchReady bound expected footprint run := ready
  have nextReady := searchReady_rounds scope 1 runReady
  have resumed := search_resume_returns plan state table bound expected footprint tabled scope run runReady 1
  simp only [Complete.Classes.search] at resumed
  rcases hresumed : Complete.Classes.rounds plan bound expected 1 run with ⟨nextRound, reps, entries, log⟩
  rw [hresumed] at resumed nextReady
  have published := search_publication_returns plan state
    (⟨nextRound, reps, entries, log⟩ : Complete.Classes.State plan)
  have count := runner_lifted% ["items"] (complete_length_returns classReceiptTerm state log)
  have fresh := runner_lifted% ["count", "items"] (drop_list_returns classReceiptTerm state consumed log)
  have children := explore_children_returns plan state mode names named table bound expected footprint tabled
    scope.declared (round + 1) receipts states (log.drop consumed)
    (fun receipt member => ⟨nextReady.1.log receipt (List.mem_of_mem_drop member),
      nextReady.2 receipt (List.mem_of_mem_drop member)⟩)
  have shape : Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round
      ⟨current, receipts, states, born, run, consumed⟩ =
      (⟨current, receipts, states, born, ⟨nextRound, reps, entries, log⟩, log.length⟩,
        (log.drop consumed).map (childNode plan bound expected mode (round + 1) receipts states)) := by
    simp only [Complete.Explore.expand]
    rw [show (Complete.Normalized.search plan bound expected mode).resume run 1 = ⟨nextRound, reps, entries, log⟩
      from hresumed]
    rfl
  rw [shape]
  runner_eval [resumed, published, count, fresh, children]
    unfolding [classSearchBackend, nodeTerm, expandedNodeTerm, classStateTerm]

def expandedAllTerm (round : Nat) (bound : List TypeExpr) (expected : TypeExpr) (mode : Complete.Normalized.Commit)
    (nodes : List (ClassNode plan)) : Term :=
  expandedTerm plan
    ((nodes.map (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round)).map Prod.fst,
      (nodes.map (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round)).flatMap
        Prod.snd)

@[metta_head "gslt:explore:expand-all"]
theorem explore_expand_all_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (round : Nat) : ∀ nodes : List (ClassNode plan),
      (∀ node ∈ nodes, NodeReady bound expected footprint node) →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:explore:expand-all" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
          number round, encoded (encodeList (nodeTerm plan) nodes)])
        state (encoded (expandedAllTerm plan round bound expected mode nodes))
  | [], _ => by
    runner_eval unfolding [encodeList, expandedAllTerm, expandedTerm]
  | node :: rest, ready => by
    have head := explore_expand_returns plan state mode names named table bound expected footprint tabled scope round
      node (ready node (by simp))
    have tail := explore_expand_all_returns state mode names named table bound expected footprint tabled scope round
      rest (fun other member => ready other (by simp [member]))
    have joined := runner_lifted% ["left", "right"] (complete_append_returns (nodeTerm plan) state
      (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round node).2
      ((rest.map (Complete.Explore.expand (Complete.Normalized.search plan bound expected mode) round)).flatMap
        Prod.snd))
    runner_eval [head, tail, joined]
      unfolding [encodeList, expandedAllTerm, expandedTerm, expandedNodeTerm, List.map_cons, List.flatMap_cons]

@[metta_head "gslt:explore:node-states"]
theorem explore_node_states_returns (state : State) : ∀ nodes : List (ClassNode plan),
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:node-states" [encoded (encodeList (nodeTerm plan) nodes)])
      state (patternsValue (nodes.map (·.state)))
  | [] => by
    runner_eval unfolding [encodeList, patternsValue, InferenceCettaWire.encodePatterns]
  | node :: rest => by
    have later := explore_node_states_returns state rest
    runner_eval [later] unfolding [encodeList, nodeTerm, patternsValue, InferenceCettaWire.encodePatterns, List.map_cons]

/-- Membership of a state among seen states. -/
@[metta_head "gslt:explore:seen"]
theorem explore_seen_returns (state : State) (current : Pattern) : ∀ seen : List Pattern,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:seen" [encoded (InferenceCettaWire.encodePattern current), patternsValue seen])
      state (Effects.boolean (decide (current ∈ seen)))
  | [] => by
    runner_eval unfolding [patternsValue, InferenceCettaWire.encodePatterns]
  | other :: rest => by
    by_cases same : current = other
    · subst same
      runner_eval unfolding [patternsValue, InferenceCettaWire.encodePatterns, List.mem_cons, true_or, decide_true]
    · have later := explore_seen_returns state current rest
      have different : InferenceCettaWire.encodePattern current ≠ InferenceCettaWire.encodePattern other :=
        fun equal => same (InferenceCettaWire.encodePattern_injective equal)
      runner_eval [later] unfolding [patternsValue, InferenceCettaWire.encodePatterns, List.mem_cons, same, different]

/-- **The children with new states** (`Complete.Explore.fresh`). -/
@[metta_head "gslt:explore:fresh"]
theorem explore_fresh_returns (state : State) : ∀ (children : List (ClassNode plan)) (seen : List Pattern),
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:fresh" [patternsValue seen, encoded (encodeList (nodeTerm plan) children)])
      state (encoded (encodeList (nodeTerm plan) (Complete.Explore.fresh seen children)))
  | [], seen => by
    runner_eval unfolding [encodeList, Complete.Explore.fresh]
  | child :: rest, seen => by
    have test := explore_seen_returns state child.state seen
    by_cases known : child.state ∈ seen
    · have later := explore_fresh_returns state rest seen
      runner_eval [test, later] unfolding [encodeList, nodeTerm, Complete.Explore.fresh, known]
    · have later := explore_fresh_returns state rest (child.state :: seen)
      runner_eval [test, later]
        unfolding [encodeList, nodeTerm, Complete.Explore.fresh, known, patternsValue, InferenceCettaWire.encodePatterns]

@[metta_head "gslt:explore:step"]
theorem explore_step_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (explorer : ClassExplorer plan)
    (ready : ∀ node ∈ explorer.nodes, NodeReady bound expected footprint node) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:step" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
        encoded (explorerTerm plan explorer)])
      state (encoded (explorerTerm plan
        (Complete.Explore.step (Complete.Normalized.search plan bound expected mode) explorer))) := by
  exact SearchExplore.step_returns
    (classRealization plan mode names named table bound expected footprint tabled scope)
    state explorer ready

@[metta_head "gslt:explore:settled"]
theorem explore_settled_returns (state : State) (mode : Complete.Normalized.Commit) (table : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)
    (tabled : table = plan.snapshot.free.entriesOn footprint) :
    ∀ nodes : List (ClassNode plan), (∀ node ∈ nodes, NodeReady bound expected footprint node) →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:explore:settled" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (encodeList (nodeTerm plan) nodes)])
        state (Effects.boolean (nodes.all (Complete.Settled.nodeSettled (Complete.Normalized.search plan bound expected mode))))
  | [], _ => by
    runner_eval unfolding [encodeList]
  | ⟨current, receipts, states, born, ⟨round, reps, entries, log⟩, consumed⟩ :: rest, ready => by
    have runReady : ClassReady plan bound expected footprint ⟨round, reps, entries, log⟩ :=
      (ready ⟨current, receipts, states, born, ⟨round, reps, entries, log⟩, consumed⟩ List.mem_cons_self).1
    have licensed : ∀ entry ∈ entries, KeyLicensed plan bound expected entry.1 := fun entry member =>
      key_licensed_of_ready (runReady.entries entry member)
    have status := search_status_returns plan state table bound expected
      (⟨round, reps, entries, log⟩ : Complete.Classes.State plan) licensed
    have published := search_publication_returns plan state
      (⟨round, reps, entries, log⟩ : Complete.Classes.State plan)
    have count := runner_lifted% ["items"] (complete_length_returns classReceiptTerm state log)
    have later := explore_settled_returns state mode table bound expected footprint tabled rest
      (fun other member => ready other (by simp [member]))
    cases finished : entries.all fun entry => entry.2.complete
    · simp [Complete.Classes.search, Complete.Classes.status, Complete.Classes.complete,
        searchStatusAtom, finished] at status
      simp only [List.all_cons, Complete.Settled.nodeSettled, Complete.Normalized.search,
        Complete.Classes.search, Complete.Classes.status, Complete.Classes.complete, finished]
      runner_eval [status] unfolding [classSearchBackend, encodeList, nodeTerm, classStateTerm, List.all_cons,
        Complete.Settled.nodeSettled, Complete.Normalized.search, Complete.Classes.search, Complete.Classes.status,
        Complete.Classes.complete, searchStatusAtom, finished]
    · by_cases same : log.length = consumed
      · simp [Complete.Classes.search, Complete.Classes.status, Complete.Classes.complete,
          searchStatusAtom, finished] at status
        runner_eval [status, published, count, later]
          unfolding [classSearchBackend, encodeList, nodeTerm, classStateTerm, List.all_cons,
          Complete.Settled.nodeSettled, Complete.Normalized.search, Complete.Classes.search, Complete.Classes.status,
          Complete.Classes.complete, searchStatusAtom, finished, same]
      · have different : (consumed == log.length) = false := beq_false_of_ne fun equal => same equal.symm
        simp [Complete.Classes.search, Complete.Classes.status, Complete.Classes.complete,
          searchStatusAtom, finished] at status
        runner_eval [status, published, count]
          unfolding [classSearchBackend, encodeList, nodeTerm, classStateTerm, List.all_cons,
          Complete.Settled.nodeSettled, Complete.Normalized.search, Complete.Classes.search, Complete.Classes.status,
          Complete.Classes.complete, searchStatusAtom, finished, same, different, Bool.and_false, Bool.false_and]

/-- **Exploration stops once settled** (`Complete.Settled.roundsUntilSettled`). -/
@[metta_head "gslt:explore:rounds"]
theorem explore_rounds_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) :
    ∀ (work : Nat) (explorer : ClassExplorer plan), (∀ node ∈ explorer.nodes, NodeReady bound expected footprint node) →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:explore:rounds" [CompleteExecution.classSearchBackend, planValue plan table bound expected, encoded (commitTerm plan mode names),
          number work, encoded (explorerTerm plan explorer)])
        state (encoded (explorerTerm plan
          (Complete.Settled.roundsUntilSettled (Complete.Normalized.search plan bound expected mode) work explorer)))
  | work, explorer, ready => by
      exact SearchExplore.rounds_returns
        (classRealization plan mode names named table bound expected footprint tabled scope)
        state work explorer ready

/-- `work` rounds from the source are the model's exploration. -/
theorem iterate_begin (bound : List TypeExpr) (expected : TypeExpr) (mode : Complete.Normalized.Commit)
    (source : Pattern) : ∀ work,
    Nat.iterate (Complete.Explore.step (Complete.Normalized.search plan bound expected mode)) work
        (Complete.Explore.begin (Complete.Normalized.search plan bound expected mode) source) =
      Complete.Explore.explore (Complete.Normalized.search plan bound expected mode) source work
  | 0 => rfl
  | work + 1 => by
    rw [Function.iterate_succ_apply', iterate_begin bound expected mode source work]
    rfl

@[metta_head "gslt:explore:states"]
theorem explore_states_returns (state : State) (explorer : ClassExplorer plan) :
    PureReturns runnerLibrary.runtime [] state (apply "gslt:explore:states" [encoded (explorerTerm plan explorer)])
      state (patternsValue (explorer.nodes.map (·.state))) := by
  obtain ⟨round, nodes⟩ := explorer
  have listed := explore_node_states_returns plan state nodes
  runner_eval [listed] unfolding [explorerTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
