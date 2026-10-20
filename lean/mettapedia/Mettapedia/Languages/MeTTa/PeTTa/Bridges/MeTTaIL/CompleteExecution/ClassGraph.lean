import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassExplore
import Mettapedia.OSLF.MeTTaIL.Complete.Graph

/-!
# The explored transition graph, in MeTTa

`gslt:explore:edges` reads an explorer's transitions (`Complete.Graph.edges`): every node's
published receipts, each with its committed target, as `(Edge state receipt target)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open StandardWire (commitTerm TableFor)

/-- A transition: its source state, its receipt and its target. -/
def edgeTerm (edge : Pattern × GeneralOccurrenceSemantics.Receipt × Pattern) : Term :=
  .application "Edge" [InferenceCettaWire.encodePattern edge.1, classReceiptTerm edge.2.1,
    InferenceCettaWire.encodePattern edge.2.2]

variable (plan : GeneralExecutionAdmission.Plan)

/-- The transitions of one state's receipts. -/
@[metta_head "gslt:explore:receipt-edges"]
theorem explore_receipt_edges_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (bound : List TypeExpr) (expected : TypeExpr)
    (current : Pattern) : ∀ receipts : List GeneralOccurrenceSemantics.Receipt,
      (∀ receipt ∈ receipts, Complete.Classes.Checked plan bound expected receipt.target) →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:explore:receipt-edges" [encoded (commitTerm plan mode names),
          encoded (InferenceCettaWire.encodePattern current), encoded (encodeList classReceiptTerm receipts)])
        state (encoded (encodeList edgeTerm (receipts.map fun receipt =>
          (current, receipt, (Complete.Normalized.search plan bound expected mode).target receipt))))
  | [], _ => by
    runner_eval unfolding [encodeList]
  | receipt :: rest, checked => by
    have target := runner_target_returns plan state mode names named bound expected receipt (checked receipt (by simp))
    have later := explore_receipt_edges_returns state mode names named bound expected current rest
      (fun other member => checked other (by simp [member]))
    runner_eval [target, later] unfolding [encodeList, List.map_cons, edgeTerm, patternValue]

/-- The transitions of a list of nodes. -/
@[metta_head "gslt:explore:node-edges"]
theorem explore_node_edges_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (bound : List TypeExpr) (expected : TypeExpr) :
    ∀ nodes : List (ClassNode plan), (∀ node ∈ nodes, Complete.Classes.LogChecked plan bound expected node.run) →
      PureReturns runnerLibrary.runtime [] state
        (apply "gslt:explore:node-edges" [encoded (commitTerm plan mode names),
          encoded (encodeList (nodeTerm plan) nodes)])
        state (encoded (encodeList edgeTerm
          (nodes.flatMap (Complete.Graph.nodeEdges (Complete.Normalized.search plan bound expected mode)))))
  | [], _ => by
    runner_eval unfolding [encodeList, List.flatMap_nil]
  | ⟨current, receipts, states, born, ⟨round, reps, entries, log⟩, consumed⟩ :: rest, checked => by
    have mine := explore_receipt_edges_returns plan state mode names named bound expected current log
      (checked ⟨current, receipts, states, born, ⟨round, reps, entries, log⟩, consumed⟩ (by simp))
    have later := explore_node_edges_returns state mode names named bound expected rest
      (fun other member => checked other (by simp [member]))
    have joined := runner_lifted% ["left", "right"] (complete_append_returns edgeTerm state
      (log.map fun receipt => (current, receipt, (Complete.Normalized.search plan bound expected mode).target receipt))
      (rest.flatMap (Complete.Graph.nodeEdges (Complete.Normalized.search plan bound expected mode))))
    have shape : (⟨current, receipts, states, born, ⟨round, reps, entries, log⟩, consumed⟩ :: rest :
          List (ClassNode plan)).flatMap (Complete.Graph.nodeEdges (Complete.Normalized.search plan bound expected mode)) =
        log.map (fun receipt => (current, receipt, (Complete.Normalized.search plan bound expected mode).target receipt)) ++
          rest.flatMap (Complete.Graph.nodeEdges (Complete.Normalized.search plan bound expected mode)) := rfl
    rw [shape]
    runner_eval [mine, later, joined] unfolding [encodeList, nodeTerm, classStateTerm]

/-- **The explored transition graph** (`Complete.Graph.edges`). -/
@[metta_head "gslt:explore:edges"]
theorem explore_edges_returns (state : State) (mode : Complete.Normalized.Commit) (names : List String)
    (named : TableFor plan names) (bound : List TypeExpr) (expected : TypeExpr)
    (explorer : ClassExplorer plan) (checked : ∀ node ∈ explorer.nodes, Complete.Classes.LogChecked plan bound expected node.run) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:edges" [encoded (commitTerm plan mode names), encoded (explorerTerm plan explorer)])
      state (encoded (encodeList edgeTerm
        (Complete.Graph.edges (Complete.Normalized.search plan bound expected mode) explorer))) := by
  obtain ⟨round, nodes⟩ := explorer
  have all := explore_node_edges_returns plan state mode names named bound expected nodes checked
  runner_eval [all] unfolding [explorerTerm, Complete.Graph.edges]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
