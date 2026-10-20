import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Sizes
import Mettapedia.OSLF.MeTTaIL.Complete.Run
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesChecked
import Mettapedia.OSLF.MeTTaIL.Complete.Graph
import Mettapedia.OSLF.MeTTaIL.Complete.Termination
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentLower

/-!
# Display erasure and positions in the complete machine

`gslt:complete:erase` is `Pattern.eraseBinderMetadata`, `gslt:complete:binder-depth` is the
binder depth of a context, and `gslt:complete:decompositions` lists every position of a term,
context and focus, in the order of `Complete.Predecessors.decompositions`. The MeTTa lists the
positions under a constructor by wrapping the positions of each argument in one frame; `Frame`
names those frames.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax PatternTreeSize DerivedContexts
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

/-- A list of values of any encoding, as the list helpers read it. -/
theorem terms_map {α : Type} (encoder : α → Term) (items : List α) :
    encoded (CettaWire.encodeList encoder items) = terms (items.map encoder) := by
  simp only [terms, CettaWire.encodeList_map, Function.id_comp]

/-- `gslt:complete:drop` on a list of any encoding. -/
theorem drop_list_returns {α : Type} (encoder : α → Term) (state : State) (count : Nat) (items : List α) :
    PureReturns runtime [] state (apply "gslt:complete:drop" [number count, encoded (CettaWire.encodeList encoder items)]) state
      (encoded (CettaWire.encodeList encoder (items.drop count))) := by
  rw [terms_map, terms_map, List.map_drop]
  exact drop_returns state count (items.map encoder)

/-- `gslt:complete:take` is `List.take`. -/
@[metta_head "gslt:complete:take"]
theorem take_returns (state : State) : ∀ (count : Nat) (items : List Term),
    PureReturns runtime [] state (apply "gslt:complete:take" [number count, terms items]) state
      (terms (items.take count)) := by
  intro count
  induction count with
  | zero => intro items; metta_call complete_checked; metta_eval
  | succ count ih =>
    intro items
    metta_call complete_checked
    cases items <;> metta_eval [ih _] with complete_checked

theorem take_list_returns {α : Type} (encoder : α → Term) (state : State) (count : Nat) (items : List α) :
    PureReturns runtime [] state (apply "gslt:complete:take" [number count, encoded (CettaWire.encodeList encoder items)]) state
      (encoded (CettaWire.encodeList encoder (items.take count))) := by
  rw [terms_map, terms_map, List.map_take]
  exact take_returns state count (items.map encoder)

@[metta_head "gslt:complete:erase-list"]
theorem erase_list_of (state : State) (patterns : List Pattern)
    (each : ∀ pattern ∈ patterns,
      PureReturns runtime [] state (apply "gslt:complete:erase" [patternValue pattern]) state
        (patternValue pattern.eraseBinderMetadata)) :
    PureReturns runtime [] state (apply "gslt:complete:erase-list" [patternsValue patterns]) state
      (patternsValue (patterns.map Pattern.eraseBinderMetadata)) := by
  induction patterns with
  | nil =>
    metta_call complete_checked
    metta_eval unfolding [encodePatterns, patternsValue, patternValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | cons pattern rest ih =>
    metta_call complete_checked
    metta_eval [each pattern (by simp), ih (fun other member => each other (by simp [member]))] with complete_checked
      unfolding [encodePatterns, patternsValue, patternValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]

/-- `gslt:complete:erase` is `Pattern.eraseBinderMetadata`. -/
@[metta_head "gslt:complete:erase"]
theorem erase_returns (state : State) (pattern : Pattern) :
    PureReturns runtime [] state (apply "gslt:complete:erase" [patternValue pattern]) state
      (patternValue pattern.eraseBinderMetadata) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    metta_call complete_checked
    metta_eval unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hfvar name =>
    metta_call complete_checked
    metta_eval unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | happly label arguments ih =>
    metta_call complete_checked
    metta_eval [erase_list_of state arguments ih] with complete_checked
      unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hlambda binder body ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked
      unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, encodeBinder, CettaWireAtom.encode,
        CettaWireAtom.encodeMany]
  | hmultiLambda arity binders body ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked
      unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, InferenceCettaWire.encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany]
  | hsubst body replacement bodyIH replacementIH =>
    metta_call complete_checked
    metta_eval [bodyIH, replacementIH] with complete_checked
      unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | hcollection kind elements rest ih =>
    metta_call complete_checked
    metta_eval [erase_list_of state elements ih] with complete_checked
      unfolding [encodePattern, Pattern.eraseBinderMetadata, patternValue, patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany]

abbrev contextValue (context : OneHoleContext) : Atom := encoded (InferenceCettaWire.ContextObservation.contextTerm context)

/-- `gslt:complete:binder-depth` is `Predecessors.binderDepth`. -/
@[metta_head "gslt:complete:binder-depth"]
theorem binder_depth_returns (state : State) (context : OneHoleContext) :
    PureReturns runtime [] state (apply "gslt:complete:binder-depth" [contextValue context]) state
      (number (Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth context)) := by
  induction context with
  | hole =>
    metta_call complete_checked
    metta_eval unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm, Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth]
  | apply constructor before inner after ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm, Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth]
  | lambda binder inner ih =>
    rw [show Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth (.lambda binder inner) = 1 + Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth inner from rfl]
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm]
  | multiLambda arity binders inner ih =>
    rw [show Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth (.multiLambda arity binders inner) = arity + Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth inner from rfl]
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm]
  | substBody inner replacement ih =>
    rw [show Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth (.substBody inner replacement) = 1 + Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth inner from rfl]
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm]
  | substReplacement body inner ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm, Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth]
  | collection kind before inner after rest ih =>
    metta_call complete_checked
    metta_eval [ih] with complete_checked unfolding [contextValue, InferenceCettaWire.ContextObservation.contextTerm, Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.binderDepth]

/-- `gslt:automata:append`, in the complete machine's runtime. -/
theorem complete_append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns runtime [] state
      (apply "gslt:automata:append" [encoded (CettaWire.encodeList element left), encoded (CettaWire.encodeList element right)])
      state (encoded (CettaWire.encodeList element (left ++ right))) := by
  metta_lift complete_checked ["left", "right"] (descent_append_returns element state left right)

/-- `gslt:automata:length`, in the complete machine's runtime. -/
theorem complete_length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns runtime [] state (apply "gslt:automata:length" [encoded (CettaWire.encodeList element items)])
      state (number items.length) := by
  metta_lift complete_checked ["items"] (descent_length_returns element state items)

theorem take_patterns_returns (state : State) (count : Nat) (items : List Pattern) :
    PureReturns runtime [] state (apply "gslt:complete:take" [number count, patternsValue items]) state
      (patternsValue (items.take count)) := by
  simpa only [patternsValue, encodePatterns_eq_encodeList] using take_list_returns encodePattern state count items

theorem drop_patterns_returns (state : State) (count : Nat) (items : List Pattern) :
    PureReturns runtime [] state (apply "gslt:complete:drop" [number count, patternsValue items]) state
      (patternsValue (items.drop count)) := by
  simpa only [patternsValue, encodePatterns_eq_encodeList] using drop_list_returns encodePattern state count items

/-- The frame a position under a constructor is wrapped in. -/
inductive Frame where
  | app (constructor : String) (before after : List Pattern)
  | lambda (binder : Option String)
  | multiLambda (arity : Nat) (binders : List String)
  | substBody (replacement : Pattern)
  | substReplacement (body : Pattern)
  | collection (kind : CollType) (before after : List Pattern) (rest : Option String)

/-- The context one frame further out. -/
def Frame.wrap : Frame → OneHoleContext → OneHoleContext
  | .app constructor before after, inner => .apply constructor before inner after
  | .lambda binder, inner => .lambda binder inner
  | .multiLambda arity binders, inner => .multiLambda arity binders inner
  | .substBody replacement, inner => .substBody inner replacement
  | .substReplacement body, inner => .substReplacement body inner
  | .collection kind before after rest, inner => .collection kind before inner after rest

def frameTerm : Frame → Term
  | .app constructor before after => .application "AppFrame" [.string constructor, encodePatterns before,
      encodePatterns after]
  | .lambda binder => .application "LamFrame" [encodeBinder binder]
  | .multiLambda arity binders => .application "MultiLamFrame" [.natural arity, InferenceCettaWire.encodeList .string binders]
  | .substBody replacement => .application "SubstBodyFrame" [encodePattern replacement]
  | .substReplacement body => .application "SubstReplacementFrame" [encodePattern body]
  | .collection kind before after rest => .application "CollectionFrame" [encodeCollectionType kind,
      encodePatterns before, encodePatterns after, encodeRest rest]

def decompositionTerm (decomposition : OneHoleContext × Pattern) : Term :=
  .application "Decomposition" [ContextObservation.contextTerm decomposition.1, encodePattern decomposition.2]

abbrev decompositionsValue (decompositions : List (OneHoleContext × Pattern)) : Atom :=
  encoded (CettaWire.encodeList decompositionTerm decompositions)

/-- `gslt:complete:frame-context` puts a context in a frame. -/
@[metta_head "gslt:complete:frame-context"]
theorem frame_context_returns (state : State) (frame : Frame) (inner : OneHoleContext) :
    PureReturns runtime [] state (apply "gslt:complete:frame-context" [encoded (frameTerm frame), contextValue inner])
      state (contextValue (frame.wrap inner)) := by
  cases frame <;>
  · metta_call complete_checked
    metta_eval unfolding [frameTerm, Frame.wrap, contextValue, ContextObservation.contextTerm]

/-- `gslt:complete:wrap` puts every position's context in a frame. -/
@[metta_head "gslt:complete:wrap"]
theorem wrap_returns (state : State) (frame : Frame) : ∀ decompositions : List (OneHoleContext × Pattern),
    PureReturns runtime [] state (apply "gslt:complete:wrap" [encoded (frameTerm frame), decompositionsValue decompositions])
      state (decompositionsValue (decompositions.map fun decomposition => (frame.wrap decomposition.1, decomposition.2)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [decompositionsValue]
  | (inner, focus) :: rest => by
    metta_call complete_checked
    metta_eval [frame_context_returns state frame inner, wrap_returns state frame rest] with complete_checked
      unfolding [decompositionsValue, decompositionTerm, contextValue, patternValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
