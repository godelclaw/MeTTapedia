import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalStream
import Mettapedia.OSLF.NativeTypes.Instances.Local.Backend
import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface

open Mettapedia.OSLF.Framework

/-!
# Suspended authored local occurrences as a native decision backend

The runtime advances the existing typed matcher and premise machine one
retained task at a time. Receipt transfer preserves its ordered origins.
The complete expansion forest appears only in the termination and coverage
proofs, rather than at the start of a budgeted experiment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling (Stream)
open Mettapedia.OSLF.NativeTypes.Decision.Machine (CursorBackend)
open Mettapedia.OSLF.NativeTypes.Instances.Local.Backend (request Source Receipt transport frontier completionBudget)

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

private theorem flatten_map {Item Result : Type} (transform : Item → Result)
    (stream : Stream Item) (ordinal : Nat) :
    (stream.mapIdx (fun item _ => transform item) ordinal).flatten = stream.flatten.map transform := by
  induction stream generalizing ordinal with
  | done => rfl
  | pause next ih => exact ih () ordinal
  | yield item next ih => exact congrArg (List.cons (transform item)) (ih () (ordinal + 1))

def tasks (equationFree : plan.equations = []) (source : Pattern) :
    Stream (Receipt plan bound type source) :=
  if checked : Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.sourceChecked plan bound type source = true then
    let typed : Source plan bound type source := checkOpenPatternWellSorted_sound checked
    (GeneralOccurrenceFrontier.LocalEquationFree.Suspended.stream
      (request plan bound type source) equationFree).mapIdx
      (fun receipt _ => transport plan bound type typed receipt)
  else .done

/-- The complete stream preserves the actual ordered occurrence archive;
matching targets are not merged. This is a list law, rather than merely
successor-set agreement. -/
theorem flatten_tasks (equationFree : plan.equations = []) (source : Pattern) :
    (tasks plan bound type equationFree source).flatten =
      frontier plan bound type (completionBudget plan bound type source) source := by
  unfold tasks Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.frontier
  split
  · rename_i checked
    dsimp only
    rw [flatten_map,
      (GeneralOccurrenceFrontier.LocalEquationFree.Suspended.stream_readouts
        (request plan bound type source) equationFree).1]
    rfl
  · rfl

/-- A valid source has an effective total stream bound, separately accounting
for actual engine tasks and for delivering the resulting receipts. The
budgeted runtime never reads this bound. -/
theorem tasks_work (equationFree : plan.equations = []) (source : Pattern)
    (typed : Source plan bound type source) :
    (tasks plan bound type equationFree source).workBound =
      completionBudget plan bound type source +
        (frontier plan bound type (completionBudget plan bound type source) source).length := by
  have checked : Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.sourceChecked plan bound type source = true :=
    checkOpenPatternWellSorted_complete typed
  simp only [tasks, checked, dite_true]
  have mapped : ∀ (Item Result : Type) (transform : Item → Result) (stream : Stream Item) (ordinal : Nat),
      (stream.mapIdx (fun item _ => transform item) ordinal).workBound = stream.workBound := by
    intro Item Result transform stream
    induction stream with
    | done => intro ordinal; rfl
    | pause next ih => intro ordinal; exact congrArg (1 + ·) (ih () ordinal)
    | yield item next ih => intro ordinal; exact congrArg (1 + ·) (ih () (ordinal + 1))
  rw [mapped, (GeneralOccurrenceFrontier.LocalEquationFree.Suspended.stream_readouts
    (request plan bound type source) equationFree).2]
  rw [frontier, dif_pos checked]
  simp only [List.length_map, completionBudget]

def cursorBackend
    (compiled : plan = GeneralExecutionAdmission.compile plan.snapshot plan.permissions)
    (foundation : plan.complete = true) (equationFree : plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric plan = true) :
    CursorBackend (GeneralOccurrenceSemantics.gslt plan bound type) (Source plan bound type) where
  Receipt := Receipt plan bound type
  target _ receipt := receipt.val.target
  tasks := tasks plan bound type equationFree
  sound _ receipt _ := GeneralOccurrenceSemantics.Receipt.semantic_step plan bound type receipt.property
  coverage source typed actual stepped := by
    have certified := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.closed_at_completion plan bound type
      compiled foundation equationFree generic source typed
    obtain ⟨receipt, listed, same⟩ := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.frontier_coverage plan bound type
      compiled foundation _ source certified actual stepped
    refine ⟨receipt, ?_, same⟩
    exact (congrArg (fun items => receipt ∈ items) (flatten_tasks plan bound type equationFree source)).mpr listed
  target_admitted _ _ receipt _ := GeneralOccurrenceSemantics.Receipt.target_sorted plan bound type receipt.property

end Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend
