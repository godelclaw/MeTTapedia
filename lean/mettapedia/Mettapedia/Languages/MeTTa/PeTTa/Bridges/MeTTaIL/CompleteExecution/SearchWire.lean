import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.OSLF.MeTTaIL.Complete.Graph

/-!
# Search-independent runner and explorer data

Retained search states and receipts are encoded by their realization.  The
runner, explorer and graph envelopes do not inspect either representation.
The existing wire constructors are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Phase Machine)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer)

def phaseSymbol : Phase → String
  | .running => "ClassRunning"
  | .done => "ClassDone"
  | .blocked => "ClassBlocked"

variable {Run Receipt : Type}

def machineTerm (runTerm : Run → Term) (receiptTerm : Receipt → Term)
    (machine : Machine Pattern Run Receipt) : Term :=
  .application "ClassMachine" [.symbol (phaseSymbol machine.phase),
    InferenceCettaWire.encodePattern machine.state, runTerm machine.program,
    encodeList InferenceCettaWire.encodePattern machine.states,
    encodeList receiptTerm machine.receipts]

def traceTerm (machine : Machine Pattern Run Receipt) : Term :=
  .application "RunTrace" [.symbol (phaseSymbol machine.phase),
    encodeList InferenceCettaWire.encodePattern machine.states.reverse]

def nodeTerm (runTerm : Run → Term) (receiptTerm : Receipt → Term)
    (node : Node Pattern Run Receipt) : Term :=
  .application "ExploreNode"
    [InferenceCettaWire.encodePattern node.state, encodeList receiptTerm node.receipts,
      encodeList InferenceCettaWire.encodePattern node.states, .natural node.born,
      runTerm node.run, .natural node.consumed]

def explorerTerm (runTerm : Run → Term) (receiptTerm : Receipt → Term)
    (explorer : Explorer Pattern Run Receipt) : Term :=
  .application "Explorer" [.natural explorer.round,
    encodeList (nodeTerm runTerm receiptTerm) explorer.nodes]

def expandedTerm (runTerm : Run → Term) (receiptTerm : Receipt → Term)
    (expanded : List (Node Pattern Run Receipt) × List (Node Pattern Run Receipt)) : Term :=
  .application "Expanded" [encodeList (nodeTerm runTerm receiptTerm) expanded.1,
    encodeList (nodeTerm runTerm receiptTerm) expanded.2]

def expandedNodeTerm (runTerm : Run → Term) (receiptTerm : Receipt → Term)
    (expanded : Node Pattern Run Receipt × List (Node Pattern Run Receipt)) : Term :=
  .application "Expanded" [nodeTerm runTerm receiptTerm expanded.1,
    encodeList (nodeTerm runTerm receiptTerm) expanded.2]

def edgeTerm (receiptTerm : Receipt → Term) (edge : Pattern × Receipt × Pattern) : Term :=
  .application "Edge" [InferenceCettaWire.encodePattern edge.1,
    receiptTerm edge.2.1, InferenceCettaWire.encodePattern edge.2.2]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
