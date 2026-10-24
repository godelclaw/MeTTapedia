import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchExplore

/-!
# Native graph readout through the shared search algebra

Every published receipt is retained as an edge, including several receipts
with the same target. Target-state sharing in the explorer does not identify
their authored origins or remove their occurrences from the graph.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchGraph

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Search)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer)
open Eval BridgeKit WireKit
open SearchRunner (Realization)
open SearchExplore (nodeTerm explorerTerm)

variable {Run Receipt : Type} {search : Search Pattern Run Receipt}

theorem receipt_edges_returns (realization : Realization search) (state : Effects.State)
    (current : Pattern) : ∀ receipts : List Receipt,
    (∀ receipt ∈ receipts, realization.ReceiptReady receipt) →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:receipt-edges"
        [realization.backend, realization.standard, patternValue current,
          encoded (encodeList realization.receiptTerm receipts)])
      state (encoded (encodeList (SearchWire.edgeTerm realization.receiptTerm)
        (receipts.map fun receipt => (current, receipt, search.target receipt))))
  | [], _ => by search_explore_eval
  | receipt :: rest, ready => by
      have target := realization.target_returns state receipt (ready receipt List.mem_cons_self)
      have later := receipt_edges_returns realization state current rest
        (fun other member => ready other (by simp [member]))
      search_explore_eval [target, later] unfolding [List.map_cons, SearchWire.edgeTerm, patternValue]

theorem node_edges_returns (realization : Realization search) (state : Effects.State) :
    ∀ nodes : List (Node Pattern Run Receipt),
    (∀ node ∈ nodes, SearchExplore.NodeReady realization node) →
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:node-edges"
        [realization.backend, realization.standard, encoded (encodeList (nodeTerm realization) nodes)])
      state (encoded (encodeList (SearchWire.edgeTerm realization.receiptTerm)
        (nodes.flatMap (Complete.Graph.nodeEdges search))))
  | [], _ => by search_explore_eval unfolding [List.flatMap_nil]
  | ⟨current, receipts, states, born, run, consumed⟩ :: rest, ready => by
      have runReady := ready ⟨current, receipts, states, born, run, consumed⟩ List.mem_cons_self
      have published := realization.publication_returns state run
      have mine := receipt_edges_returns realization state current (search.publication run)
        (realization.publication_ready run runReady)
      have later := node_edges_returns realization state rest
        (fun other member => ready other (by simp [member]))
      have joined := complete_runner_lifted% ["left", "right"]
        (complete_append_returns (SearchWire.edgeTerm realization.receiptTerm) state
          ((search.publication run).map fun receipt => (current, receipt, search.target receipt))
          (rest.flatMap (Complete.Graph.nodeEdges search)))
      search_explore_eval [published, mine, later, joined]
        unfolding [List.flatMap_cons, Complete.Graph.nodeEdges]

theorem edges_returns (realization : Realization search) (state : Effects.State)
    (explorer : Explorer Pattern Run Receipt) (ready : SearchExplore.Ready realization explorer) :
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:explore:edges"
        [realization.backend, realization.standard, encoded (explorerTerm realization explorer)])
      state (encoded (encodeList (SearchWire.edgeTerm realization.receiptTerm)
        (Complete.Graph.edges search explorer))) := by
  obtain ⟨round, nodes⟩ := explorer
  have all := node_edges_returns realization state nodes ready
  search_explore_eval [all] unfolding [Complete.Graph.edges]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchGraph
