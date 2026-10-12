import Mettapedia.Languages.C11.ValueSequencing
import Mettapedia.Languages.C11.SequencingData
import Mettapedia.Languages.C11.ScheduledObjects
import Mettapedia.Languages.C11.ObjectControls

/-!
# Sequencing, occurrence and retained-memory controls

The event shapes retain C11's scalar conflict distinctions. Undefined
controls are evaluated by the formal checker, not executed as native C.
The object plans exercise actual memory transitions and exact residuals;
they are already constructed primitive plans, not a complete C source
frontend or an authority to publish external effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.SequencingControls

open Sequencing ValueSequencing
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def checked {Index : Type} (component : Component Index Nat) : CheckResult Index :=
  let _ : DecidableEq Index := component.indexEq
  checkFamily component.enumeration [component.evaluation]

def place (object : Nat) : Component (Fin 1) Nat := leaf (.designate object)
def read (object : Nat) : Component (Fin 1 ⊕ Fin 1) Nat := unary (place object) (.readValue object)
def constant : Component (Fin 1) Nat := leaf .other
def post (object : Nat) := postUpdate (place object) object
def pre (object : Nat) := preUpdate (place object) object

theorem designation_is_not_stored_value_read : conflicts (.modify 3) (.designate 3) = false := rfl
theorem two_reads_do_not_conflict : conflicts (.readValue 3) (.readValue 3) = false := rfl
theorem write_read_conflicts : conflicts (.modify 3) (.readValue 3) = true := rfl
theorem read_write_conflicts : conflicts (.readValue 3) (.modify 3) = true := rfl
theorem distinct_objects_do_not_conflict : conflicts (.modify 3) (.readValue 4) = false := rfl

theorem ordinary_i_equals_i_plus_one : checked (assignment (place 0) (binary (read 0) constant) 0) = .safe := rfl
theorem ordinary_i_equals_i : checked (assignment (place 0) (read 0) 0) = .safe := rfl
theorem standalone_postincrement : checked (post 0) = .safe := rfl
theorem standalone_preincrement : checked (pre 0) = .safe := rfl
theorem postincrement_plus_same_read_is_undefined : checked (binary (post 0) (read 0)) ≠ .safe := by decide
theorem two_postincrements_same_object_are_undefined : checked (binary (post 0) (post 0)) ≠ .safe := by decide
theorem independent_postincrements_are_defined : checked (binary (post 0) (post 1)) = .safe := rfl
theorem assignment_of_postincrement_is_undefined : checked (assignment (place 0) (post 0) 0) ≠ .safe := by decide
def prefixPlusOne := binary (pre 0) constant
theorem assignment_of_preincrement_plus_one_is_undefined :
    checked (assignment (place 0) prefixPlusOne 0) ≠ .safe := by
  let component := assignment (place 0) prefixPlusOne 0
  let _ : DecidableEq _ := component.indexEq
  decide
theorem assignment_to_another_object_is_defined : checked (assignment (place 1) (post 0) 1) = .safe := rfl
theorem comma_orders_update_before_read : checked (sequencePoint (post 0) (read 0)) = .safe := rfl
theorem sequence_point_orders_two_updates : checked (sequencePoint (post 0) (post 0)) = .safe := rfl
theorem skipped_short_circuit_child_has_no_occurrences : checked (unary (post 0) .other) = .safe := rfl

def twoFunctionBodies := (post 0).evaluation.indeterminate (post 0).evaluation
def bodyEnumeration := (post 0).enumeration.sum (post 0).enumeration

theorem indeterminate_function_bodies_keep_both_orders : twoFunctionBodies.length = 2 := rfl
theorem indeterminate_function_bodies_are_defined : checkFamily bodyEnumeration twoFunctionBodies = .safe := rfl
theorem unsequenced_argument_updates_are_undefined :
    checkFamily bodyEnumeration [(post 0).evaluation.parallel (post 0).evaluation] ≠ .safe := by decide
theorem favorable_chosen_order_does_not_fix_an_allowed_conflict :
    checkFamily bodyEnumeration [
      (post 0).evaluation.sequence (post 0).evaluation,
      (post 0).evaluation.parallel (post 0).evaluation] ≠ .safe := by decide
theorem empty_alternatives_are_model_refusal : checkFamily (Enumeration.fin 0) ([] : List (Evaluation (Fin 0) Nat)) = .emptyAlternatives := rfl

def cycle : Order (Fin 2) := ⟨fun first second => decide (first ≠ second)⟩
def missingTransitiveEdge : Order (Fin 3) := ⟨fun first second => decide (first.val + 1 = second.val)⟩
def chain : Order (Fin 3) := ⟨fun first second => decide (first.val < second.val)⟩
def unconstrained : Order (Fin 3) := ⟨fun _ _ => false⟩

theorem cycle_is_invalid : cycle.check (.fin 2) = false := rfl
theorem complete_relation_is_required : missingTransitiveEdge.check (.fin 3) = false := rfl
theorem transitive_chain_is_valid : chain.check (.fin 3) = true := rfl
theorem irreflexivity_is_required : (Order.mk fun (_ _ : Fin 1) => true).check (.fin 1) = false := rfl
theorem chain_enables_only_first : SequencingSchedule.choices chain [0, 1, 2] = [0] := rfl
theorem next_occurrence_becomes_enabled : SequencingSchedule.choices chain [1, 2] = [1] := rfl
theorem unconstrained_order_offers_all_occurrences : SequencingSchedule.choices unconstrained [0, 1, 2] = [0, 1, 2] := rfl
theorem out_of_order_selection_is_refused : SequencingSchedule.select chain [0, 1, 2] 2 = none := rfl
theorem valid_selection_keeps_exact_tail : SequencingSchedule.select chain [0, 1, 2] 0 = some [1, 2] := rfl
theorem consumed_occurrence_cannot_be_selected_again : SequencingSchedule.select chain [1, 2] 0 = none := rfl
theorem schedule_does_not_rewrite_semantic_order :
    (binary (post 0) (read 0)).evaluation.order.before (.inl (.inl (.inr 0))) (.inl (.inr (.inr 0))) = false := rfl

def memory : ObjectStep.State Nat := ⟨[⟨7, ⟨true, [some 10, some 20, some 30]⟩⟩], []⟩

def plan : ScheduledObjects.Plan (Fin 2) Nat Nat where
  enumeration := .fin 2
  evaluation := ⟨⟨fun first second => decide (first.val < second.val)⟩,
    fun index => if index.val = 0 then .modify 7 else .readValue 7⟩
  request index := if index.val = 0 then .writeRepresentation ⟨7, 0⟩ [some 99] else .readRepresentation ⟨⟨7, 0⟩, 1⟩

def initial : ScheduledObjects.Configuration (Fin 2) Nat :=
  ⟨⟨[0, 1], memory⟩, [⟨0, .failure⟩, ⟨1, .failure⟩]⟩

def firstStep := ScheduledObjects.execute ObjectControls.difference64 plan .failure initial.state 0
def saved : ScheduledObjects.Configuration (Fin 2) Nat :=
  ⟨⟨[1], ⟨[⟨7, ⟨true, [some 99, some 20, some 30]⟩⟩, ⟨7, ⟨true, [some 10, some 20, some 30]⟩⟩], []⟩⟩,
    [⟨1, .failure⟩]⟩

theorem actual_store_is_executed : firstStep = some (.updated, saved.state) := rfl
theorem actual_read_uses_saved_store :
    ScheduledObjects.execute ObjectControls.difference64 plan .failure saved.state 1 =
      some (.representation [some 99], ⟨[], saved.state.memory⟩) := rfl
theorem resuming_cannot_execute_consumed_store :
    ScheduledObjects.execute ObjectControls.difference64 plan .failure saved.state 0 = none := rfl
theorem reading_before_store_is_not_a_permitted_selection :
    ScheduledObjects.execute ObjectControls.difference64 plan .failure initial.state 1 = none := rfl
theorem exhausted_driver_retains_memory_and_pending :
    ((ScheduledObjects.machine ObjectControls.difference64 plan).run 1 initial).2 = .exhausted saved := rfl
theorem first_prefix_has_one_receipt :
    (((ScheduledObjects.machine ObjectControls.difference64 plan).run 1 initial).1.map (fun receipt => receipt.index)) = [0] := rfl
theorem resumed_prefix_has_only_pending_receipt :
    (((ScheduledObjects.machine ObjectControls.difference64 plan).run 1 saved).1.map (fun receipt => receipt.index)) = [1] := rfl
theorem joined_receipts_preserve_occurrence_order :
    (((ScheduledObjects.machine ObjectControls.difference64 plan).run 2 initial).1.map (fun receipt => receipt.index)) = [0, 1] := rfl
theorem no_selection_suspends_with_complete_saved_state :
    ((ScheduledObjects.machine ObjectControls.difference64 plan).run 1 ⟨initial.state, []⟩).2 =
      .suspended ⟨[0]⟩ ⟨initial.state, []⟩ := rfl

def conflictingPlan : ScheduledObjects.Plan (Fin 2) Nat Nat :=
  { plan with evaluation := ⟨⟨fun _ _ => false⟩, plan.evaluation.access⟩ }

theorem conflicting_plan_has_no_memory_execution :
    ScheduledObjects.execute ObjectControls.difference64 conflictingPlan .failure initial.state 0 = none := rfl
theorem conflicting_plan_emits_no_receipts :
    ((ScheduledObjects.machine ObjectControls.difference64 conflictingPlan).run 3 initial).1 = [] := rfl

def raw : SequencingData.EvaluationData :=
  ⟨[[false, true], [false, false]], [.modify 7, .readValue 7]⟩

theorem represented_order_and_accesses_are_admitted : SequencingData.inspect 2 raw = some .safe := rfl
theorem missing_matrix_row_is_refused :
    SequencingData.inspect 2 { raw with matrix := [[false, true]] } = none := rfl
theorem excess_matrix_row_is_refused :
    SequencingData.inspect 2 { raw with matrix := raw.matrix ++ [[false, false]] } = none := rfl
theorem ragged_matrix_is_refused :
    SequencingData.inspect 2 { raw with matrix := [[false, true], [false]] } = none := rfl
theorem missing_access_occurrence_is_refused :
    SequencingData.inspect 2 { raw with accesses := [.modify 7] } = none := rfl
theorem extra_access_occurrence_is_refused :
    SequencingData.inspect 2 { raw with accesses := raw.accesses ++ [.other] } = none := rfl
theorem represented_self_edge_is_invalid_order :
    SequencingData.inspect 2 { raw with matrix := [[true, true], [false, false]] } = some (.invalidOrder 0) := rfl
theorem removing_sequencing_exposes_same_object_conflict :
    SequencingData.inspect 2 { raw with matrix := [[false, false], [false, false]] } =
      some (.unsequencedConflict 0 0 1) := rfl
theorem changing_object_identity_changes_conflict_judgment :
    SequencingData.inspect 2 { matrix := [[false, false], [false, false]], accesses := [.modify 7, .readValue 8] } =
      some .safe := rfl
theorem designation_occurrence_does_not_manufacture_read_conflict :
    SequencingData.inspect 2 { matrix := [[false, false], [false, false]], accesses := [.modify 7, .designate 7] } =
      some .safe := rfl

end Mettapedia.Languages.C11.SequencingControls
