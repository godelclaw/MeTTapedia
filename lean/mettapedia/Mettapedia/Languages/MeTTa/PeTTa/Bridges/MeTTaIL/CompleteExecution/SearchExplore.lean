import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchRunner

/-!
# One native explorer for certified search realizations

The explorer implements `Complete.Explore` through the five search operations.
Search state and receipt representations remain opaque. Its readiness proof
uses the realization's closure laws; source-calculus successor coverage does
not follow from this computational correspondence alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchExplore

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Search Status)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open SearchRunner (Realization)

variable {Run Receipt : Type} {search : Search Pattern Run Receipt}

abbrev nodeTerm (realization : Realization search) :=
  SearchWire.nodeTerm realization.runTerm realization.receiptTerm
abbrev explorerTerm (realization : Realization search) :=
  SearchWire.explorerTerm realization.runTerm realization.receiptTerm
abbrev expandedTerm (realization : Realization search) :=
  SearchWire.expandedTerm realization.runTerm realization.receiptTerm
abbrev expandedNodeTerm (realization : Realization search) :=
  SearchWire.expandedNodeTerm realization.runTerm realization.receiptTerm

def NodeReady (realization : Realization search) (node : Node Pattern Run Receipt) : Prop :=
  realization.RunReady node.run

def Ready (realization : Realization search) (explorer : Explorer Pattern Run Receipt) : Prop :=
  ∀ node ∈ explorer.nodes, NodeReady realization node

def childNode (search : Search Pattern Run Receipt) (born : Nat) (receipts : List Receipt) (states : List Pattern)
    (receipt : Receipt) : Node Pattern Run Receipt :=
  ⟨search.target receipt, receipt :: receipts, search.target receipt :: states,
    born, search.run (search.target receipt) 0, 0⟩

theorem expand_ready (realization : Realization search) (round : Nat)
    (node : Node Pattern Run Receipt) (ready : NodeReady realization node) :
    NodeReady realization (Complete.Explore.expand search round node).1 ∧
      ∀ child ∈ (Complete.Explore.expand search round node).2, NodeReady realization child := by
  have next := realization.resume_ready node.run ready 1
  refine ⟨next, ?_⟩
  intro child member
  simp only [Complete.Explore.expand, List.mem_map] at member
  obtain ⟨receipt, published, rfl⟩ := member
  exact realization.run_ready _ (realization.target_ready receipt
    (realization.publication_ready _ next receipt (List.mem_of_mem_drop published))) 0

theorem step_ready (realization : Realization search) (explorer : Explorer Pattern Run Receipt)
    (ready : Ready realization explorer) : Ready realization (Complete.Explore.step search explorer) := by
  intro node member
  simp only [Complete.Explore.step, List.mem_append, List.mem_map] at member
  rcases member with ⟨pair, ⟨original, inside, rfl⟩, rfl⟩ | kept
  · exact (expand_ready realization _ original (ready original inside)).1
  · obtain ⟨pair, listed, child⟩ := List.mem_flatMap.mp (Complete.Explore.fresh_subset _ _ node kept)
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp listed
    exact (expand_ready realization _ original (ready original inside)).2 node child

syntax "search_explore_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| search_explore_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in runnerProof_checked using runnerProof_agreement
       metta_eval [$facts,*] with runnerProof_checked in runnerProof_agreement
         unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
           nodeTerm, explorerTerm, expandedTerm, expandedNodeTerm,
           SearchWire.nodeTerm, SearchWire.explorerTerm, SearchWire.expandedTerm,
           SearchWire.expandedNodeTerm, encodeList, $extra,*]))

theorem begin_returns (realization : Realization search) (state : Effects.State)
    (source start : Pattern) (ready : realization.SourceReady start)
    (prepared : PureReturns runnerLibrary.runtime [] state
      (apply "gslt:runner:standard" [realization.standard, patternValue source])
      state (patternValue start)) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:begin"
        [realization.backend, realization.plan, realization.standard, patternValue source])
      state (encoded (explorerTerm realization (Complete.Explore.begin search start))) := by
  have started := realization.run_returns state start ready 0
  search_explore_eval [prepared, started] unfolding [Complete.Explore.begin]

theorem children_returns (realization : Realization search) (state : Effects.State)
    (born : Nat) (receipts : List Receipt) (states : List Pattern) :
    ∀ published : List Receipt, (∀ receipt ∈ published, realization.ReceiptReady receipt) →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:children"
        [realization.backend, realization.plan, realization.standard, number born,
          encoded (encodeList realization.receiptTerm receipts),
          encoded (encodeList InferenceCettaWire.encodePattern states),
          encoded (encodeList realization.receiptTerm published)])
      state (encoded (encodeList (nodeTerm realization)
        (published.map (childNode search born receipts states))))
  | [], _ => by search_explore_eval
  | receipt :: rest, ready => by
      have receiptReady := ready receipt List.mem_cons_self
      have target := realization.target_returns state receipt receiptReady
      have fresh := realization.run_returns state (search.target receipt)
        (realization.target_ready receipt receiptReady) 0
      have later := children_returns realization state born receipts states rest
        (fun other member => ready other (by simp [member]))
      search_explore_eval [target, fresh, later] unfolding [List.map_cons, childNode]

theorem expand_returns (realization : Realization search) (state : Effects.State)
    (round : Nat) (node : Node Pattern Run Receipt) (ready : NodeReady realization node) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:expand"
        [realization.backend, realization.plan, realization.standard,
          number round, encoded (nodeTerm realization node)])
      state (encoded (expandedNodeTerm realization (Complete.Explore.expand search round node))) := by
  obtain ⟨current, receipts, states, born, run, consumed⟩ := node
  have nextReady := realization.resume_ready run ready 1
  have resumed := realization.resume_returns state run ready 1
  have published := realization.publication_returns state (search.resume run 1)
  have count := complete_runner_lifted% ["items"]
    (complete_length_returns realization.receiptTerm state (search.publication (search.resume run 1)))
  have fresh := complete_runner_lifted% ["count", "items"]
    (drop_list_returns realization.receiptTerm state consumed (search.publication (search.resume run 1)))
  have children := children_returns realization state (round + 1) receipts states
    ((search.publication (search.resume run 1)).drop consumed)
    (fun receipt member => realization.publication_ready _ nextReady receipt (List.mem_of_mem_drop member))
  search_explore_eval [resumed, published, count, fresh, children]
    unfolding [Complete.Explore.expand, childNode]

def expandedAllTerm (realization : Realization search) (round : Nat)
    (nodes : List (Node Pattern Run Receipt)) : Term :=
  expandedTerm realization
    ((nodes.map (Complete.Explore.expand search round)).map Prod.fst,
      (nodes.map (Complete.Explore.expand search round)).flatMap Prod.snd)

theorem expand_all_returns (realization : Realization search) (state : Effects.State)
    (round : Nat) : ∀ nodes : List (Node Pattern Run Receipt),
    (∀ node ∈ nodes, NodeReady realization node) →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:expand-all"
        [realization.backend, realization.plan, realization.standard, number round,
          encoded (encodeList (nodeTerm realization) nodes)])
      state (encoded (expandedAllTerm realization round nodes))
  | [], _ => by search_explore_eval unfolding [expandedAllTerm]
  | node :: rest, ready => by
      have head := expand_returns realization state round node (ready node List.mem_cons_self)
      have tail := expand_all_returns realization state round rest
        (fun other member => ready other (by simp [member]))
      have joined := complete_runner_lifted% ["left", "right"]
        (complete_append_returns (nodeTerm realization) state
          (Complete.Explore.expand search round node).2
          ((rest.map (Complete.Explore.expand search round)).flatMap Prod.snd))
      search_explore_eval [head, tail, joined]
        unfolding [expandedAllTerm, List.map_cons, List.flatMap_cons]

theorem node_states_returns (realization : Realization search) (state : Effects.State) :
    ∀ nodes : List (Node Pattern Run Receipt),
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:node-states" [encoded (encodeList (nodeTerm realization) nodes)])
      state (patternsValue (nodes.map (·.state)))
  | [] => by search_explore_eval unfolding [patternsValue, InferenceCettaWire.encodePatterns]
  | node :: rest => by
      have later := node_states_returns realization state rest
      search_explore_eval [later]
        unfolding [patternsValue, InferenceCettaWire.encodePatterns, List.map_cons]

theorem seen_returns (state : Effects.State) (current : Pattern) : ∀ seen : List Pattern,
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:seen" [patternValue current, patternsValue seen])
      state (Effects.boolean (decide (current ∈ seen)))
  | [] => by search_explore_eval unfolding [patternsValue, InferenceCettaWire.encodePatterns]
  | other :: rest => by
      by_cases same : current = other
      · subst same
        search_explore_eval
          unfolding [patternsValue, InferenceCettaWire.encodePatterns, List.mem_cons, true_or, decide_true]
      · have later := seen_returns state current rest
        have different : InferenceCettaWire.encodePattern current ≠ InferenceCettaWire.encodePattern other :=
          fun equal => same (InferenceCettaWire.encodePattern_injective equal)
        simp only [List.mem_cons, same, false_or]
        search_explore_eval [later]
          unfolding [patternsValue, InferenceCettaWire.encodePatterns, different]

theorem fresh_returns (realization : Realization search) (state : Effects.State) :
    ∀ (children : List (Node Pattern Run Receipt)) (seen : List Pattern),
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:fresh"
        [patternsValue seen, encoded (encodeList (nodeTerm realization) children)])
      state (encoded (encodeList (nodeTerm realization) (Complete.Explore.fresh seen children)))
  | [], seen => by search_explore_eval unfolding [Complete.Explore.fresh]
  | child :: rest, seen => by
      have test := seen_returns state child.state seen
      by_cases known : child.state ∈ seen
      · have later := fresh_returns realization state rest seen
        search_explore_eval [test, later] unfolding [Complete.Explore.fresh, known]
      · have later := fresh_returns realization state rest (child.state :: seen)
        search_explore_eval [test, later]
          unfolding [Complete.Explore.fresh, known, patternsValue, InferenceCettaWire.encodePatterns]

theorem step_returns (realization : Realization search) (state : Effects.State)
    (explorer : Explorer Pattern Run Receipt) (ready : Ready realization explorer) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:step"
        [realization.backend, realization.plan, realization.standard, encoded (explorerTerm realization explorer)])
      state (encoded (explorerTerm realization (Complete.Explore.step search explorer))) := by
  obtain ⟨round, nodes⟩ := explorer
  have expanded := expand_all_returns realization state round nodes ready
  have seen := node_states_returns realization state
    ((nodes.map (Complete.Explore.expand search round)).map Prod.fst)
  have kept := fresh_returns realization state
    ((nodes.map (Complete.Explore.expand search round)).flatMap Prod.snd)
    (((nodes.map (Complete.Explore.expand search round)).map Prod.fst).map (·.state))
  have all := complete_runner_lifted% ["left", "right"]
    (complete_append_returns (nodeTerm realization) state
      ((nodes.map (Complete.Explore.expand search round)).map Prod.fst)
      (Complete.Explore.fresh
        (((nodes.map (Complete.Explore.expand search round)).map Prod.fst).map (·.state))
        ((nodes.map (Complete.Explore.expand search round)).flatMap Prod.snd)))
  search_explore_eval [expanded, seen, kept, all] unfolding [expandedAllTerm, Complete.Explore.step]

theorem settled_returns (realization : Realization search) (state : Effects.State) :
    ∀ nodes : List (Node Pattern Run Receipt), (∀ node ∈ nodes, NodeReady realization node) →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:settled"
        [realization.backend, realization.plan, encoded (encodeList (nodeTerm realization) nodes)])
      state (Effects.boolean (nodes.all (Complete.Settled.nodeSettled search)))
  | [], _ => by search_explore_eval
  | ⟨current, receipts, states, born, run, consumed⟩ :: rest, ready => by
      have runReady := ready ⟨current, receipts, states, born, run, consumed⟩ List.mem_cons_self
      have status := realization.status_returns state run runReady
      have published := realization.publication_returns state run
      have count := complete_runner_lifted% ["items"]
        (complete_length_returns realization.receiptTerm state (search.publication run))
      have later := settled_returns realization state rest
        (fun other member => ready other (by simp [member]))
      cases finished : search.status run with
      | complete =>
          simp only [finished, SearchRunner.statusAtom] at status
          by_cases same : (search.publication run).length = consumed
          · simp only [List.all_cons, Complete.Settled.nodeSettled, finished, same,
              beq_self_eq_true, Bool.true_and]
            search_explore_eval [status, published, count, later] unfolding [same]
          · have different : (consumed == (search.publication run).length) = false :=
              beq_false_of_ne fun equal => same equal.symm
            search_explore_eval [status, published, count]
              unfolding [List.all_cons, Complete.Settled.nodeSettled, finished, same, different,
                Bool.and_false, Bool.false_and]
      | blocked =>
          simp only [finished, SearchRunner.statusAtom] at status
          simp only [List.all_cons, Complete.Settled.nodeSettled, finished]
          search_explore_eval [status]
      | pending =>
          simp only [finished, SearchRunner.statusAtom] at status
          simp only [List.all_cons, Complete.Settled.nodeSettled, finished]
          search_explore_eval [status]

theorem rounds_returns (realization : Realization search) (state : Effects.State) :
    ∀ (work : Nat) (explorer : Explorer Pattern Run Receipt), Ready realization explorer →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:rounds"
        [realization.backend, realization.plan, realization.standard,
          number work, encoded (explorerTerm realization explorer)])
      state (encoded (explorerTerm realization (Complete.Settled.roundsUntilSettled search work explorer)))
  | 0, explorer, _ => by search_explore_eval unfolding [Complete.Settled.roundsUntilSettled]
  | work + 1, ⟨round, nodes⟩, ready => by
      have settledFact := settled_returns realization state nodes ready
      cases settledNow : nodes.all (Complete.Settled.nodeSettled search)
      · have once := step_returns realization state ⟨round, nodes⟩ ready
        have later := rounds_returns realization state work
          (Complete.Explore.step search ⟨round, nodes⟩) (step_ready realization _ ready)
        search_explore_eval [settledFact, once, later]
          unfolding [Complete.Settled.roundsUntilSettled, Complete.Settled.settled, settledNow]
      · search_explore_eval [settledFact]
          unfolding [Complete.Settled.roundsUntilSettled, Complete.Settled.settled, settledNow]

theorem states_returns (realization : Realization search) (state : Effects.State)
    (explorer : Explorer Pattern Run Receipt) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:states" [encoded (explorerTerm realization explorer)])
      state (patternsValue (explorer.nodes.map (·.state))) := by
  obtain ⟨round, nodes⟩ := explorer
  have listed := node_states_returns realization state nodes
  search_explore_eval [listed]

theorem rounds_ready (realization : Realization search) (work : Nat)
    (explorer : Explorer Pattern Run Receipt) (ready : Ready realization explorer) :
    Ready realization (Complete.Settled.roundsUntilSettled search work explorer) := by
  induction work generalizing explorer with
  | zero => exact ready
  | succ work ih =>
      simp only [Complete.Settled.roundsUntilSettled]
      split
      · exact ready
      · exact ih _ (step_ready realization explorer ready)

theorem resumed_rounds_returns (realization : Realization search) (state : Effects.State)
    (first extra : Nat) (explorer : Explorer Pattern Run Receipt) (ready : Ready realization explorer) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:rounds"
        [realization.backend, realization.plan, realization.standard, number extra,
          encoded (explorerTerm realization (Complete.Settled.roundsUntilSettled search first explorer))])
      state (encoded (explorerTerm realization
        (Complete.Settled.roundsUntilSettled search (first + extra) explorer))) := by
  simpa only [Complete.Settled.roundsUntilSettled_add] using
    rounds_returns realization state extra (Complete.Settled.roundsUntilSettled search first explorer)
      (rounds_ready realization first explorer ready)

theorem settled_rounds_returns (realization : Realization search) (state : Effects.State)
    (extra : Nat) (explorer : Explorer Pattern Run Receipt) (ready : Ready realization explorer)
    (done : Complete.Settled.settled search explorer = true) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:rounds"
        [realization.backend, realization.plan, realization.standard, number extra,
          encoded (explorerTerm realization explorer)])
      state (encoded (explorerTerm realization explorer)) := by
  simpa only [Complete.Settled.roundsUntilSettled_of_settled (S := search) explorer done] using
    rounds_returns realization state extra explorer ready

#print axioms rounds_ready
#print axioms resumed_rounds_returns
#print axioms settled_rounds_returns


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchExplore
