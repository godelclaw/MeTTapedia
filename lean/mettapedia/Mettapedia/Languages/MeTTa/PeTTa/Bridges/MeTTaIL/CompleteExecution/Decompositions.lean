import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions

/-!
# Every position of a term, in the complete machine

`gslt:complete:decompositions` is `Complete.Predecessors.decompositions`. Under a constructor
or a collection the MeTTa walks the arguments with their index, taking the arguments before and
dropping those up to the current one; `argumentDecompositions` is that walk, and it equals the
indexed `flatMap` of the Lean definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

/-- Whether the arguments belong to a constructor or to a collection. -/
inductive ArgumentKind where
  | app
  | collection (kind : CollType) (rest : Option String)

def ArgumentKind.term : ArgumentKind → Term
  | .app => .symbol "AppKind"
  | .collection kind rest => .application "CollectionKind" [encodeCollectionType kind, encodeRest rest]

/-- The value the MeTTa passes as the head: the constructor's label, or the collection's kind. -/
def ArgumentKind.head (label : String) : ArgumentKind → Term
  | .app => .string label
  | .collection kind _ => encodeCollectionType kind

def ArgumentKind.frame (label : String) : ArgumentKind → List Pattern → List Pattern → Frame
  | .app, before, after => .app label before after
  | .collection kind rest, before, after => .collection kind before after rest

/-- The positions inside the arguments from `index` on. -/
def argumentDecompositions (label : String) (kind : ArgumentKind) (all : List Pattern) :
    List Pattern → Nat → List (OneHoleContext × Pattern)
  | [], _ => []
  | argument :: rest, index =>
      (Complete.Predecessors.decompositions argument).map
          (fun decomposition => ((kind.frame label (all.take index) (all.drop (index + 1))).wrap decomposition.1,
            decomposition.2)) ++
        argumentDecompositions label kind all rest (index + 1)

private theorem attach_zipIdx_flatMap {α β : Type} (items : List α) (body : α → Nat → List β) (start : Nat) :
    (items.attach.zipIdx start).flatMap (fun entry => body entry.1.1 entry.2) =
      (items.zipIdx start).flatMap (fun entry => body entry.1 entry.2) := by
  conv_rhs => rw [← List.attach_map_subtype_val items, List.zipIdx_map]
  rw [List.flatMap_map]
  rfl

private theorem zipIdx_flatMap_eq (label : String) (kind : ArgumentKind) (all : List Pattern) :
    ∀ (remaining : List Pattern) (start : Nat),
      (remaining.zipIdx start).flatMap (fun entry => (Complete.Predecessors.decompositions entry.1).map
          (fun decomposition => ((kind.frame label (all.take entry.2) (all.drop (entry.2 + 1))).wrap decomposition.1,
            decomposition.2))) =
        argumentDecompositions label kind all remaining start
  | [], _ => rfl
  | argument :: rest, start => by
    simp only [List.zipIdx_cons, List.flatMap_cons, argumentDecompositions]
    rw [zipIdx_flatMap_eq label kind all rest (start + 1)]

theorem decompositions_apply (label : String) (arguments : List Pattern) :
    Complete.Predecessors.decompositions (.apply label arguments) =
      (.hole, .apply label arguments) :: argumentDecompositions label .app arguments arguments 0 := by
  rw [Complete.Predecessors.decompositions]
  congr 1
  rw [← zipIdx_flatMap_eq label .app arguments arguments 0]
  exact attach_zipIdx_flatMap arguments (fun argument index =>
    (Complete.Predecessors.decompositions argument).map fun decomposition =>
      ((ArgumentKind.app.frame label (arguments.take index) (arguments.drop (index + 1))).wrap decomposition.1,
        decomposition.2)) 0

theorem decompositions_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    Complete.Predecessors.decompositions (.collection kind elements rest) =
      (.hole, .collection kind elements rest) ::
        argumentDecompositions "" (.collection kind rest) elements elements 0 := by
  rw [Complete.Predecessors.decompositions]
  congr 1
  rw [← zipIdx_flatMap_eq "" (.collection kind rest) elements elements 0]
  exact attach_zipIdx_flatMap elements (fun element index =>
    (Complete.Predecessors.decompositions element).map fun decomposition =>
      (((ArgumentKind.collection kind rest).frame "" (elements.take index) (elements.drop (index + 1))).wrap
        decomposition.1, decomposition.2)) 0

/-- What `gslt:complete:decompositions` returns on a term. -/
abbrev Decomposes (state : State) (pattern : Pattern) : Prop :=
  PureReturns runtime [] state (apply "gslt:complete:decompositions" [patternValue pattern]) state
    (decompositionsValue (Complete.Predecessors.decompositions pattern))

@[metta_head "gslt:complete:argument-decompositions"]
theorem argument_decompositions_returns (state : State) (label : String) (kind : ArgumentKind) (all : List Pattern)
    (each : ∀ argument ∈ all, Decomposes state argument) :
    ∀ (remaining : List Pattern) (index : Nat), (∀ argument ∈ remaining, argument ∈ all) →
      PureReturns runtime [] state
        (apply "gslt:complete:argument-decompositions" [encoded kind.term, encoded (kind.head label), patternsValue all,
          patternsValue remaining, number index])
        state (decompositionsValue (argumentDecompositions label kind all remaining index))
  | [], index, _ => by
    metta_call complete_checked
    metta_eval unfolding [patternsValue, encodePatterns, decompositionsValue, argumentDecompositions]
  | argument :: rest, index, within => by
    have inner := each argument (within argument (by simp))
    have later := argument_decompositions_returns state label kind all each rest (index + 1)
      (fun other member => within other (by simp [member]))
    have before := take_patterns_returns state index all
    have after := drop_patterns_returns state (index + 1) all
    have wrapped := wrap_returns state (kind.frame label (all.take index) (all.drop (index + 1)))
      (Complete.Predecessors.decompositions argument)
    have joined := complete_append_returns decompositionTerm state
      ((Complete.Predecessors.decompositions argument).map fun decomposition =>
        ((kind.frame label (all.take index) (all.drop (index + 1))).wrap decomposition.1, decomposition.2))
      (argumentDecompositions label kind all rest (index + 1))
    cases kind <;>
    · metta_call complete_checked
      metta_eval [inner, later, before, after, wrapped, joined] with complete_checked
        unfolding [patternsValue, encodePatterns, argumentDecompositions, ArgumentKind.term, ArgumentKind.head,
          ArgumentKind.frame, frameTerm, Decomposes]

/-- **`gslt:complete:decompositions` is `Predecessors.decompositions`.** -/
@[metta_head "gslt:complete:decompositions"]
theorem decompositions_returns (state : State) (pattern : Pattern) : Decomposes state pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    metta_call complete_checked
    metta_eval unfolding [encodePattern, patternValue, decompositionsValue, decompositionTerm,
      Complete.Predecessors.decompositions, ContextObservation.contextTerm]
  | hfvar name =>
    metta_call complete_checked
    metta_eval unfolding [encodePattern, patternValue, decompositionsValue, decompositionTerm,
      Complete.Predecessors.decompositions, ContextObservation.contextTerm]
  | happly label arguments ih =>
    unfold Decomposes
    rw [decompositions_apply]
    metta_call complete_checked
    metta_eval [argument_decompositions_returns state label .app arguments ih arguments 0 (fun _ member => member)]
      with complete_checked
      unfolding [encodePattern, patternValue, patternsValue, decompositionsValue, decompositionTerm,
        ContextObservation.contextTerm, ArgumentKind.term, ArgumentKind.head]
  | hlambda binder body ih =>
    unfold Decomposes
    rw [Complete.Predecessors.decompositions]
    metta_call complete_checked
    metta_eval [ih, wrap_returns state (.lambda binder) (Complete.Predecessors.decompositions body)] with complete_checked
      unfolding [encodePattern, patternValue, decompositionsValue, decompositionTerm,
        ContextObservation.contextTerm, frameTerm, Frame.wrap]
  | hmultiLambda arity binders body ih =>
    unfold Decomposes
    rw [Complete.Predecessors.decompositions]
    metta_call complete_checked
    metta_eval [ih, wrap_returns state (.multiLambda arity binders) (Complete.Predecessors.decompositions body)]
      with complete_checked
      unfolding [encodePattern, patternValue, decompositionsValue, decompositionTerm,
        ContextObservation.contextTerm, frameTerm, Frame.wrap]
  | hsubst body replacement bodyIH replacementIH =>
    unfold Decomposes
    rw [Complete.Predecessors.decompositions]
    have left := wrap_returns state (.substBody replacement) (Complete.Predecessors.decompositions body)
    have right := wrap_returns state (.substReplacement body) (Complete.Predecessors.decompositions replacement)
    have joined := complete_append_returns decompositionTerm state
      ((Complete.Predecessors.decompositions body).map fun decomposition =>
        ((Frame.substBody replacement).wrap decomposition.1, decomposition.2))
      ((Complete.Predecessors.decompositions replacement).map fun decomposition =>
        ((Frame.substReplacement body).wrap decomposition.1, decomposition.2))
    metta_call complete_checked
    metta_eval [bodyIH, replacementIH, left, right, joined] with complete_checked
      unfolding [encodePattern, patternValue, decompositionsValue, decompositionTerm,
        ContextObservation.contextTerm, frameTerm, Frame.wrap]
  | hcollection kind elements rest ih =>
    unfold Decomposes
    rw [decompositions_collection]
    metta_call complete_checked
    metta_eval [argument_decompositions_returns state "" (.collection kind rest) elements ih elements 0
        (fun _ member => member)]
      with complete_checked
      unfolding [encodePattern, patternValue, patternsValue, decompositionsValue, decompositionTerm,
        ContextObservation.contextTerm, ArgumentKind.term, ArgumentKind.head]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
