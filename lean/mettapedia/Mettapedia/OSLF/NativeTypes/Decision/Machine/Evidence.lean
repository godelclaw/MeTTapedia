import Mettapedia.OSLF.NativeTypes.Decision.Machine.ModalTrace

open Mettapedia.OSLF.Framework

/-!
# Saved native receipts and complete modal coverage

The four modal polarities are joined to the actual computed state archive.
Witnesses and counterexamples retain their receipt origins and continuation
meanings. The complete polarities retain every operational receipt and cover
every actual successor through the backend's independently earned equations.
Query settlement alone is never used as a frontier coverage certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.GSLT GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling
open scoped List

universe u v w

theorem possibility_trace_evidence {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source)
    {seen : List (Observation backend)} {result : Outcome (denotation leaves (.possibility formula) source)}
    (trace : Trace (tasks backend leaves (.possibility formula) source sourceAdmitted []) seen result) :
    (result.answer = some true → ∃ receipt listed,
      (Observation.mk source receipt listed []) ∈ seen ∧
      denotation leaves formula (backend.target source receipt)) ∧
    (result.answer = some false → ∀ receipt listed,
      (Observation.mk source receipt listed []) ∈ seen ∧
      ¬ denotation leaves formula (backend.target source receipt)) := by
  rw [tasks] at trace
  cases trace with
  | paused tail =>
    obtain ⟨reply, modalTrace, result_eq⟩ := mapReply_trace _
      (fun reply => by cases reply <;> rfl) _ tail
    obtain ⟨positive, negative⟩ := existsTasks_trace _ _ _ _
      (fun receipt listed => tasks_complete backend leaves formula (backend.target source receipt)
        (backend.target_admitted source sourceAdmitted receipt listed) [0]) modalTrace
    constructor
    · intro read
      rw [result_eq] at read
      apply positive
      cases reply <;> exact read
    · intro read
      rw [result_eq] at read
      apply negative
      cases reply <;> exact read

theorem universal_trace_evidence {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source)
    {seen : List (Observation backend)} {result : Outcome (denotation leaves (.outgoingUniversal formula) source)}
    (trace : Trace (tasks backend leaves (.outgoingUniversal formula) source sourceAdmitted []) seen result) :
    (result.answer = some true → ∀ receipt listed,
      (Observation.mk source receipt listed []) ∈ seen ∧
      denotation leaves formula (backend.target source receipt)) ∧
    (result.answer = some false → ∃ receipt listed,
      (Observation.mk source receipt listed []) ∈ seen ∧
      ¬ denotation leaves formula (backend.target source receipt)) := by
  rw [tasks] at trace
  cases trace with
  | paused tail =>
    obtain ⟨reply, modalTrace, result_eq⟩ := mapReply_trace _
      (fun reply => by cases reply <;> rfl) _ tail
    obtain ⟨positive, negative⟩ := forallTasks_trace _ _ _ _
      (fun receipt listed => tasks_complete backend leaves formula (backend.target source receipt)
        (backend.target_admitted source sourceAdmitted receipt listed) [0]) modalTrace
    constructor
    · intro read
      rw [result_eq] at read
      apply positive
      cases reply <;> exact read
    · intro read
      rw [result_eq] at read
      apply negative
      cases reply <;> exact read

theorem positive_saved_receipt {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.possibility formula) source sourceAdmitted budget).outcome.answer = some true) :
    ∃ receipt listed,
      (Observation.mk source receipt listed []) ∈
        (run backend leaves (.possibility formula) source sourceAdmitted budget).observations ∧
      denotation leaves formula (backend.target source receipt) :=
  (possibility_trace_evidence backend leaves formula source sourceAdmitted
    (run_trace backend leaves (.possibility formula) source sourceAdmitted budget ⟨true, read⟩)).1 read

theorem negative_saved_counterreceipt {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).outcome.answer = some false) :
    ∃ receipt listed,
      (Observation.mk source receipt listed []) ∈
        (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).observations ∧
      ¬ denotation leaves formula (backend.target source receipt) :=
  (universal_trace_evidence backend leaves formula source sourceAdmitted
    (run_trace backend leaves (.outgoingUniversal formula) source sourceAdmitted budget ⟨false, read⟩)).2 read

theorem negative_possibility_saved_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.possibility formula) source sourceAdmitted budget).outcome.answer = some false) :
    ∀ receipt listed,
      (Observation.mk source receipt listed []) ∈
        (run backend leaves (.possibility formula) source sourceAdmitted budget).observations ∧
      ¬ denotation leaves formula (backend.target source receipt) :=
  (possibility_trace_evidence backend leaves formula source sourceAdmitted
    (run_trace backend leaves (.possibility formula) source sourceAdmitted budget ⟨false, read⟩)).2 read

theorem positive_universal_saved_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).outcome.answer = some true) :
    ∀ receipt listed,
      (Observation.mk source receipt listed []) ∈
        (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).observations ∧
      denotation leaves formula (backend.target source receipt) :=
  (universal_trace_evidence backend leaves formula source sourceAdmitted
    (run_trace backend leaves (.outgoingUniversal formula) source sourceAdmitted budget ⟨true, read⟩)).1 read

theorem negative_possibility_actual_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.possibility formula) source sourceAdmitted budget).outcome.answer = some false)
    (actual : system.Term) (step : system.Step source actual) :
    ∃ receipt listed,
      (Observation.mk source receipt listed []) ∈
        (run backend leaves (.possibility formula) source sourceAdmitted budget).observations ∧
      GSLT.Equiv system actual (backend.target source receipt) ∧ ¬ denotation leaves formula actual := by
  obtain ⟨receipt, listed, related⟩ := backend.coverage source sourceAdmitted actual step
  obtain ⟨saved, absent⟩ := negative_possibility_saved_coverage backend leaves formula
    source sourceAdmitted budget read receipt listed
  exact ⟨receipt, listed, saved, related, fun holds => absent ((denotation leaves formula).2 related |>.mp holds)⟩

theorem positive_universal_actual_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).outcome.answer = some true)
    (actual : system.Term) (step : system.Step source actual) :
    ∃ receipt listed,
      (Observation.mk source receipt listed []) ∈
        (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).observations ∧
      GSLT.Equiv system actual (backend.target source receipt) ∧ denotation leaves formula actual := by
  obtain ⟨receipt, listed, related⟩ := backend.coverage source sourceAdmitted actual step
  obtain ⟨saved, holds⟩ := positive_universal_saved_coverage backend leaves formula
    source sourceAdmitted budget read receipt listed
  exact ⟨receipt, listed, saved, related, ((denotation leaves formula).2 related).mpr holds⟩

/-- Complete absence retains all physical root origins in their original order. -/
theorem negative_possibility_ordered_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.possibility formula) source sourceAdmitted budget).outcome.answer = some false) :
    fullObservations (backend.tasks source) (fun receipt listed => Observation.mk source receipt listed []) <+
      (run backend leaves (.possibility formula) source sourceAdmitted budget).observations := by
  have trace := run_trace backend leaves (.possibility formula) source sourceAdmitted budget ⟨false, read⟩
  rw [tasks] at trace
  cases trace with
  | paused tail =>
    obtain ⟨reply, modalTrace, result_eq⟩ := mapReply_trace _
      (fun reply => by cases reply <;> rfl) _ tail
    apply existsTasks_ordered_coverage _ _ _ _
      (fun receipt listed => tasks_complete backend leaves formula (backend.target source receipt)
        (backend.target_admitted source sourceAdmitted receipt listed) [0]) modalTrace
    rw [result_eq] at read
    cases reply <;> exact read

/-- Universal truth retains all physical root origins, including duplicates. -/
theorem positive_universal_ordered_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (formula : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).outcome.answer = some true) :
    fullObservations (backend.tasks source) (fun receipt listed => Observation.mk source receipt listed []) <+
      (run backend leaves (.outgoingUniversal formula) source sourceAdmitted budget).observations := by
  have trace := run_trace backend leaves (.outgoingUniversal formula) source sourceAdmitted budget ⟨true, read⟩
  rw [tasks] at trace
  cases trace with
  | paused tail =>
    obtain ⟨reply, modalTrace, result_eq⟩ := mapReply_trace _
      (fun reply => by cases reply <;> rfl) _ tail
    apply forallTasks_ordered_coverage _ _ _ _
      (fun receipt listed => tasks_complete backend leaves formula (backend.target source receipt)
        (backend.target_admitted source sourceAdmitted receipt listed) [0]) modalTrace
    rw [result_eq] at read
    cases reply <;> exact read

end Mettapedia.OSLF.NativeTypes.Decision.Machine
