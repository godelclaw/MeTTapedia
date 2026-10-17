import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Lists

/-!
# Pattern sizes in the complete machine

`gslt:deep:nodes` and `gslt:deep:nodes-list` are `PatternTreeSize.nodes` and `listNodes`, the
measure the deepening search certifies against.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax PatternTreeSize
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

abbrev patternValue (pattern : Pattern) : Atom := encoded (encodePattern pattern)
abbrev patternsValue (patterns : List Pattern) : Atom := encoded (encodePatterns patterns)

@[metta_head "gslt:deep:nodes-list"]
theorem nodes_list_of (state : State) (patterns : List Pattern)
    (each : ∀ pattern ∈ patterns,
      PureReturns runtime [] state (apply "gslt:deep:nodes" [patternValue pattern]) state (number (nodes pattern))) :
    PureReturns runtime [] state (apply "gslt:deep:nodes-list" [patternsValue patterns]) state
      (number (listNodes patterns)) := by
  induction patterns with
  | nil =>
    metta_call complete_checked
    metta_eval unfolding [encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | cons pattern rest ih =>
    metta_call complete_checked
    metta_eval [each pattern (by simp), ih (fun other member => each other (by simp [member]))] with complete_checked
      unfolding [encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany]

/-- `gslt:deep:nodes` is `PatternTreeSize.nodes`. -/
@[metta_head "gslt:deep:nodes"]
theorem nodes_returns (state : State) (pattern : Pattern) :
    PureReturns runtime [] state (apply "gslt:deep:nodes" [patternValue pattern]) state (number (nodes pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    metta_call complete_checked
    metta_eval unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hfvar name =>
    metta_call complete_checked
    metta_eval unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | happly label arguments ih =>
    metta_call complete_checked
    metta_eval [nodes_list_of state arguments ih] with complete_checked
      unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hlambda binder body ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hmultiLambda arity binders body ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hsubst body replacement bodyIH replacementIH =>
    rw [show nodes (.subst body replacement) = 1 + (nodes body + nodes replacement) by simp only [nodes]; omega]
    metta_call complete_checked
    metta_eval [bodyIH, replacementIH] with complete_checked
      unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hcollection kind elements rest ih =>
    metta_call complete_checked
    metta_eval [nodes_list_of state elements ih] with complete_checked
      unfolding [encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
