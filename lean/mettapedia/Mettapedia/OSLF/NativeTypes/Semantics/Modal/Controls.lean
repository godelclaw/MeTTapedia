import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Root
import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Possibility
import Mettapedia.OSLF.NativeTypes.Modal.ContextControls
import Mettapedia.OSLF.MeTTaIL.GeneralRhoPaidControls

open Mettapedia.OSLF.Framework

/-!
# Native modal representative and origin controls

The Wrap context preserves the declared equation even when reduction
permissions remain root-only. Both focus representatives have implementations. A root-context control rejects an
unrelated specified contractum. Original rho COMM executions have equal
targets and different occurrence origins, retained in the native family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Semantics.Modal
open GSLTTypeSynthesis

namespace Context

open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples (carrier alpha beta done)
open Mettapedia.OSLF.NativeTypes.Modal.ContextControls (schema runtimePlan continuation wrap)

def alphaFamily : Family schema (fun _ _ => False) continuation alpha :=
  Mettapedia.OSLF.NativeTypes.Semantics.Modal.introduce Mettapedia.OSLF.NativeTypes.Modal.ContextControls.alphaEvidence

def betaFamily : Family schema (fun _ _ => False) continuation beta :=
  alphaFamily.rebase [.reverse Mettapedia.OSLF.NativeTypes.Modal.ContextControls.equationReceipt]
    (.back Mettapedia.OSLF.NativeTypes.Modal.ContextControls.equation_completed rfl (.nil alpha))

theorem beta_native_member : predicate schema (fun _ _ => False) continuation beta :=
  family_support_iff.mp ⟨betaFamily⟩

theorem beta_native_member_has_raw_implementation :
    predicate schema (fun _ _ => False) continuation beta ∧
      Inhabits schema (fun _ _ => False) continuation beta :=
  ⟨beta_native_member, Mettapedia.OSLF.NativeTypes.Modal.ContextControls.beta_inhabits⟩

theorem beta_family_retains_alpha :
    betaFamily.representative = alpha ∧
      betaFamily.implementation = Mettapedia.OSLF.NativeTypes.Modal.ContextControls.alphaEvidence ∧
      betaFamily.conversions.length = 1 := ⟨rfl, rfl, rfl⟩

theorem emptyRequest (anchor : ScopedRuleMatching.Assignment) :
    TypedRequest schema (fun _ _ => False) anchor [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have names : schema.relyNames = [] := by cbv
    intro name present
    rw [names] at present
    exact False.elim (List.not_mem_nil present)
  · exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
      fun _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
  · have names : schema.matchedNames = [] := by cbv
    intro name present
    rw [names] at present
    exact False.elim (List.not_mem_nil present)
  · have names : RedexPosition.fvarNames schema.declaration.rule.left ++
        RedexPosition.fvarNames schema.declaration.rule.right = [] := by cbv
    intro name present
    rw [names] at present
    exact False.elim (List.not_mem_nil present)

def betaRepresentativeResponse := betaFamily.response [] (emptyRequest betaFamily.implementation.anchor)

theorem beta_response_executes_retained_representative :
    betaRepresentativeResponse.source = wrap alpha ∧
      betaRepresentativeResponse.target = done ∧
      (gslt runtimePlan [] carrier).Step betaRepresentativeResponse.source betaRepresentativeResponse.target := by
  have readout := Family.response_readout betaFamily [] (emptyRequest betaFamily.implementation.anchor)
  have filled := Mettapedia.OSLF.NativeTypes.Modal.ContextControls.schema_fill [] alpha
  have rhs := Mettapedia.OSLF.NativeTypes.Modal.ContextControls.schema_rhs []
  exact ⟨Option.some.inj (readout.1.symm.trans filled),
    Option.some.inj (readout.2.1.symm.trans rhs), readout.2.2.1⟩

/-- The retained representative and the raw program both execute through
the authored equation lifted into their enclosing context. -/
theorem quotient_output_preserves_the_raw_program :
    predicate schema (fun _ _ => False) continuation beta ∧
      (gslt runtimePlan [] carrier).Step (wrap beta) done :=
  ⟨beta_native_member, Mettapedia.OSLF.NativeTypes.Modal.ContextControls.wrap_beta_steps_done⟩

end Context

theorem root_native_rejects_unrelated_rhs :
    ¬ predicate Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.schema (fun _ _ => False)
      Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.continuation Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other := by
  intro member
  have raw := (root_predicate_iff_inhabits Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.schema_position rfl rfl).mp member
  exact Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.corrected_modality_rejects_other raw

namespace Rho

open GeneralRho.PaidControls

def postcondition (duplicate : Bool) :
    EquationPredicate (gslt (request duplicate).plan (request duplicate).bound (request duplicate).expected) :=
  saturatePredicate _ (fun result => result = target duplicate)

def family (duplicate : Bool) (slot : Fin (count duplicate)) :
    PossibilityFamily (request duplicate).plan (request duplicate).bound (request duplicate).expected
      (postcondition duplicate) (request duplicate).root :=
  PossibilityFamily.introduce (occurrence duplicate slot)
    ⟨(occurrence duplicate slot).val.target, .refl _, occurrence_target duplicate slot⟩

theorem native_diamond_accepts_actual_COMM (duplicate : Bool) (slot : Fin (count duplicate)) :
    possibilityPredicate (request duplicate).plan (request duplicate).bound (request duplicate).expected
      (postcondition duplicate) (request duplicate).root :=
  possibility_family_support_iff.mp ⟨family duplicate slot⟩

theorem complete_target_readout (duplicate : Bool) (slot : Fin (count duplicate)) :
    (family duplicate slot).eliminate.1 = target duplicate :=
  occurrence_target duplicate slot

theorem equal_targets_distinct_native_receipts :
    (family true ⟨0, by decide⟩).eliminate.1 = (family true ⟨1, by decide⟩).eliminate.1 ∧
      family true ⟨0, by decide⟩ ≠ family true ⟨1, by decide⟩ := by
  refine ⟨(complete_target_readout true _).trans (complete_target_readout true _).symm, ?_⟩
  intro same
  exact distinct_duplicate_occurrences (congrArg Sigma.fst same)

theorem actual_distinct_matcher_origins :
    (family true ⟨0, by decide⟩).1.val.firing.matcherTrace = GeneralRho.firstInputTrace ∧
      (family true ⟨1, by decide⟩).1.val.firing.matcherTrace = GeneralRho.secondInputTrace :=
  duplicate_traces

theorem receipt_history_remains_one_event (duplicate : Bool) (slot : Fin (count duplicate)) :
    (GeneralOccurrenceNativeReceipts.history (request duplicate).plan (request duplicate).bound
      (request duplicate).expected (family duplicate slot).1).length = 1 :=
  GeneralOccurrenceNativeReceipts.primitive_count _ _ _ _

end Rho

end Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls
