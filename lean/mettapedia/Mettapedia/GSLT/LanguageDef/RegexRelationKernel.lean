import Mettapedia.GSLT.LanguageDef.RegexRelationCursor

/-!
# Regular and intrinsic-observation occurrence profiles

The regular profile uses the existing tagged graph actions and point-simple
paths. The extended profile supplies atomic completed body observations from
the canonical intrinsic-call kernel and retains the entire capture-dependent
configuration in its cycle key. These are distinct declared path disciplines.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexRelationKernel

open Mettapedia.Computability.RegularLanguages
open RegexObservationTrace (ObservedAction)
open RegexDependentObservation
open RegexObservationKernel

def regularStep {State Class Assertion : Type} {length : Nat}
    (graph : State → RegexTaggedGraph.Node State Class Assertion Unit)
    (probe : OrderedGraphSearch.Probe Class Assertion length)
    (thread : RegexTaggedGraph.Thread State length) : ObservedAction (RegexTaggedGraph.Thread State length) :=
  match RegexSelectionCorrespondence.action graph probe thread with
  | .accept _ => .accept
  | .dead => .dead
  | .next target => .next target []
  | .branch left right => .branch left right

theorem regular_trace_iff {State Class Assertion : Type} {length : Nat}
    (graph : State → RegexTaggedGraph.Node State Class Assertion Unit)
    (probe : OrderedGraphSearch.Probe Class Assertion length)
    (eligible : RegexTaggedGraph.Thread State length → Bool)
    (first last : RegexTaggedGraph.Thread State length) (bits : List Bool)
    (points : List (OrderedGraphSearch.Point State length)) :
    RegexRelationEnumeration.Trace (regularStep graph probe) RegexTaggedGraph.Thread.point
        eligible first bits points last ↔
      RegexSelectionCorrespondence.Trace graph probe eligible first bits points last () := by
  constructor
  · intro trace
    induction trace with
    | @done first operation allowed =>
        cases actual : RegexSelectionCorrespondence.action graph probe first <;>
          simp [regularStep, actual] at operation
        rename_i tag
        cases tag
        exact .done actual allowed
    | @next first target leading bits points last operation trace ih =>
        cases actual : RegexSelectionCorrespondence.action graph probe first <;>
          simp only [regularStep, actual] at operation
        all_goals try cases operation
        exact .next actual ih
    | @left first left right bits points last operation trace ih =>
        cases actual : RegexSelectionCorrespondence.action graph probe first <;>
          simp only [regularStep, actual] at operation
        all_goals try cases operation
        exact .left actual ih
    | @right first left right bits points last operation trace ih =>
        cases actual : RegexSelectionCorrespondence.action graph probe first <;>
          simp only [regularStep, actual] at operation
        all_goals try cases operation
        exact .right actual ih
  · intro trace
    generalize terminal : () = tag at trace
    clear terminal
    induction trace with
    | done operation allowed => exact .done (by simp [regularStep, operation]) allowed
    | @next first target bits points last tag operation trace ih =>
        exact .next (first := first) (target := target) (leading := [])
          (by simp [regularStep, operation]) ih
    | @left first left right bits points last tag operation trace ih =>
        exact .left (first := first) (left := left) (right := right)
          (by simp [regularStep, operation]) ih
    | @right first left right bits points last tag operation trace ih =>
        exact .right (first := first) (left := left) (right := right)
          (by simp [regularStep, operation]) ih

def regularOccurrences {states : Nat} {Class Assertion : Type} {length : Nat}
    (graph : Fin states → RegexTaggedGraph.Node (Fin states) Class Assertion Unit)
    (probe : OrderedGraphSearch.Probe Class Assertion length)
    (eligible : RegexTaggedGraph.Thread (Fin states) length → Bool)
    (first : RegexTaggedGraph.Thread (Fin states) length) :=
  RegexRelationEnumeration.all (regularStep graph probe) RegexTaggedGraph.Thread.point eligible first

theorem regular_occurrences_exact {states : Nat} {Class Assertion : Type} {length : Nat}
    (graph : Fin states → RegexTaggedGraph.Node (Fin states) Class Assertion Unit)
    (probe : OrderedGraphSearch.Probe Class Assertion length)
    (eligible : RegexTaggedGraph.Thread (Fin states) length → Bool)
    (first : RegexTaggedGraph.Thread (Fin states) length)
    (occurrence : RegexRelationEnumeration.Occurrence (RegexTaggedGraph.Thread (Fin states) length)
      (OrderedGraphSearch.Point (Fin states) length)) :
    occurrence ∈ regularOccurrences graph probe eligible first ↔
      RegexSelectionCorrespondence.Trace graph probe eligible first occurrence.choices occurrence.points
        occurrence.value () ∧ occurrence.points.Nodup := by
  rw [regularOccurrences, RegexRelationEnumeration.all_exact, regular_trace_iff]

def intrinsicStep {states groups length : Nat} (interpretation : Interpretation) (input : Fin length → Nat)
    (direction : Direction) (code : Fin states → Instruction states groups)
    (certificate : Certificate code) (root : Fin states) :
    Licensed code length root → ObservedAction (Licensed code length root) :=
  fun configuration =>
    liftAction (controlAction interpretation input direction code root
      (fun entry _ => evaluate interpretation input code certificate entry) configuration)
      (control_targets interpretation input direction code root
        (fun entry _ => evaluate interpretation input code certificate entry) configuration)

theorem intrinsic_step_certificate_independent {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (first second : Certificate code) (root : Fin states) :
    intrinsicStep interpretation input direction code first root =
      intrinsicStep interpretation input direction code second root := by
  have recursive :
      (fun entry (_ : DirectBodyCall code entry root) => evaluate interpretation input code first entry) =
        (fun entry (_ : DirectBodyCall code entry root) => evaluate interpretation input code second entry) := by
    funext entry call
    exact certificate_independent interpretation input code first second entry
  exact congrArg (fun recurse => fun configuration : Licensed code length root =>
    liftAction (controlAction interpretation input direction code root recurse configuration)
      (control_targets interpretation input direction code root recurse configuration)) recursive

def intrinsicOccurrences {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (certificate : Certificate code) (root : Fin states)
    (eligible : Configuration states groups length → Bool)
    (position : Fin (length + 1)) (captures : Captures groups length) :=
  let initial : Licensed code length root := ⟨⟨root,position,captures⟩, .refl⟩
  RegexRelationEnumeration.all (intrinsicStep interpretation input direction code certificate root)
    Subtype.val (fun configuration => eligible configuration.val) initial

theorem intrinsic_occurrences_certificate_independent {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (first second : Certificate code) (root : Fin states)
    (eligible : Configuration states groups length → Bool)
    (position : Fin (length + 1)) (captures : Captures groups length) :
    intrinsicOccurrences interpretation input direction code first root eligible position captures =
      intrinsicOccurrences interpretation input direction code second root eligible position captures := by
  unfold intrinsicOccurrences
  rw [intrinsic_step_certificate_independent interpretation input direction code first second root]

end Mettapedia.GSLT.LanguageDef.RegexRelationKernel
