import Mettapedia.OSLF.NativeTypes.Runtime.Search
import Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence

/-!
# Public computed receipt certificates

Computed sessions retain their execution provenance through resumption.
Modal witnesses and counterexamples belong to the actual saved archive and
their continuations have the generated public meaning. Complete absence and
universal truth retain the whole physical receipt sequence, including order
and multiplicity. No law treats an arbitrary constructed running session as
an execution certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Evidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver Meaning Readout)
open Mettapedia.OSLF.NativeTypes.Decision.Machine (Observation fullObservations)
open scoped List

/-- Provenance from either public entrypoint, retained by exact resumption. -/
def Computed {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (session : Session driver runtime formula raw) : Prop :=
  (∃ budget, session = search driver runtime formula raw budget) ∨
    (∃ source budget, session = check driver runtime formula (source : driver.Decoded raw) budget)

theorem computed_search (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) (budget : Nat) :
    Computed (search driver runtime formula raw budget) := .inl ⟨budget, rfl⟩

theorem computed_check (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw) (budget : Nat) :
    Computed (check driver runtime formula source budget) := .inr ⟨source, budget, rfl⟩

theorem computed_start (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) : Computed (start driver runtime formula raw) := by
  refine .inl ⟨0, ?_⟩
  unfold search
  cases start driver runtime formula raw <;> rfl

theorem computed_resume {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (session : Session driver runtime formula raw)
    (computed : Computed session) (more : Nat) : Computed (resume more session) := by
  rcases computed with ⟨budget, rfl⟩ | ⟨source, budget, rfl⟩
  · exact .inl ⟨budget + more, (search_resume driver runtime formula raw budget more).symm⟩
  · exact .inr ⟨source, budget + more, (check_resume driver runtime formula source budget more).symm⟩

private theorem check_running (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw) (budget : Nat)
    (answer : Bool) (read : (check driver runtime formula source budget).readout = .judgment (.decided answer)) :
    check driver runtime formula source budget = .running source
      (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves
        formula source.val source.property.1 budget) ∧
    (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves
        formula source.val source.property.1 budget).outcome.answer = some answer := by
  cases refused : Mettapedia.OSLF.NativeTypes.Decision.Admission.firstRefusal
      driver.generated.logicFragment driver.leafAdmission formula with
  | some reason =>
    rw [check, startSource, refused] at read
    change (resume budget (Session.refusedFormula source reason)).readout = _ at read
    cases reason <;> cases read
  | none =>
    cases profile : driver.profileAdmission with
    | none =>
      rw [check, startSource, refused, profile] at read
      change (resume budget (Session.unresolvedCube source)).readout = _ at read
      cases read
    | some accepted =>
      cases accepted with
      | false =>
        rw [check, startSource, refused, profile] at read
        change (resume budget (Session.rejectedCube source)).readout = _ at read
        cases read
      | true =>
        have same : check driver runtime formula source budget = .running source
            (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves
              formula source.val source.property.1 budget) := by
          simp only [check, startSource, refused, profile, resume,
            Mettapedia.OSLF.NativeTypes.Decision.Machine.run]
        refine ⟨same, ?_⟩
        rw [same, running_readout] at read
        cases result : (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves
            formula source.val source.property.1 budget).outcome.answer with
        | none => rw [result] at read; cases read
        | some value =>
          rw [result] at read
          have equal : value = answer := by cases read; rfl
          exact congrArg some equal

private theorem computed_running {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (session : Session driver runtime formula raw)
    (computed : Computed session) (answer : Bool)
    (read : session.readout = .judgment (.decided answer)) :
    ∃ source budget, session = Session.running (runtime := runtime) (formula := formula)
      (source : driver.Decoded raw)
      (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves
        formula source.val source.property.1 budget) ∧
    (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves
        formula source.val source.property.1 budget).outcome.answer = some answer := by
  rcases computed with ⟨budget, rfl⟩ | ⟨source, budget, rfl⟩
  · cases decoded : driver.decode raw with
    | error reason =>
      simp only [search, start, decoded, resume] at read
      cases read
    | ok source =>
      have same : search driver runtime formula raw budget = check driver runtime formula source budget := by
        simp only [search, start, decoded, check]
      obtain ⟨machine, result⟩ := check_running driver runtime formula source budget answer (same ▸ read)
      exact ⟨source, budget, same.trans machine, result⟩
  · obtain ⟨machine, result⟩ := check_running driver runtime formula source budget answer read
    exact ⟨source, budget, machine, result⟩

private theorem target_meaning (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw)
    (receipt : runtime.cursor.Receipt source.val)
    (listed : receipt ∈ (runtime.cursor.tasks source.val).flatten) :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation runtime.leaves formula
      (runtime.cursor.target source.val receipt) ↔
      Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) :=
  runtime.meaning_at_decoded formula
    ⟨runtime.cursor.target source.val receipt,
      runtime.cursor.target_admitted source.val source.property.1 receipt listed, rfl⟩

theorem computed_positive_receipt {driver : Driver} {runtime : Engine driver}
    (formula : driver.Formula) {raw : Pattern}
    (session : Session driver runtime (.possibility formula) raw) (computed : Computed session)
    (read : session.readout = .judgment (.decided true)) :
    ∃ source : driver.Decoded raw, ∃ receipt listed,
      (Observation.mk source.val receipt listed []) ∈ session.observations ∧
      driver.system.Step source.val (runtime.cursor.target source.val receipt) ∧
      Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) := by
  obtain ⟨source, budget, same, result⟩ := computed_running session computed true read
  obtain ⟨receipt, listed, saved, holds⟩ := Mettapedia.OSLF.NativeTypes.Decision.Machine.positive_saved_receipt
    runtime.cursor runtime.leaves formula source.val source.property.1 budget result
  rw [same]
  exact ⟨source, receipt, listed, saved, runtime.cursor.sound _ _ listed,
    (target_meaning driver runtime formula source receipt listed).mp holds⟩

theorem computed_negative_counterreceipt {driver : Driver} {runtime : Engine driver}
    (formula : driver.Formula) {raw : Pattern}
    (session : Session driver runtime (.outgoingUniversal formula) raw) (computed : Computed session)
    (read : session.readout = .judgment (.decided false)) :
    ∃ source : driver.Decoded raw, ∃ receipt listed,
      (Observation.mk source.val receipt listed []) ∈ session.observations ∧
      driver.system.Step source.val (runtime.cursor.target source.val receipt) ∧
      ¬ Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) := by
  obtain ⟨source, budget, same, result⟩ := computed_running session computed false read
  obtain ⟨receipt, listed, saved, absent⟩ := Mettapedia.OSLF.NativeTypes.Decision.Machine.negative_saved_counterreceipt
    runtime.cursor runtime.leaves formula source.val source.property.1 budget result
  rw [same]
  exact ⟨source, receipt, listed, saved, runtime.cursor.sound _ _ listed,
    fun holds => absent ((target_meaning driver runtime formula source receipt listed).mpr holds)⟩

theorem computed_negative_coverage {driver : Driver} {runtime : Engine driver}
    (formula : driver.Formula) {raw : Pattern}
    (session : Session driver runtime (.possibility formula) raw) (computed : Computed session)
    (read : session.readout = .judgment (.decided false)) :
    ∃ source : driver.Decoded raw,
      fullObservations (runtime.cursor.tasks source.val)
        (fun receipt listed => Observation.mk source.val receipt listed []) <+ session.observations ∧
      ∀ receipt listed,
        (Observation.mk source.val receipt listed []) ∈ session.observations ∧
        ¬ Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) := by
  obtain ⟨source, budget, same, result⟩ := computed_running session computed false read
  rw [same]
  refine ⟨source, Mettapedia.OSLF.NativeTypes.Decision.Machine.negative_possibility_ordered_coverage
    runtime.cursor runtime.leaves formula source.val source.property.1 budget result, ?_⟩
  intro receipt listed
  obtain ⟨saved, absent⟩ := Mettapedia.OSLF.NativeTypes.Decision.Machine.negative_possibility_saved_coverage
    runtime.cursor runtime.leaves formula source.val source.property.1 budget result receipt listed
  exact ⟨saved, fun holds => absent ((target_meaning driver runtime formula source receipt listed).mpr holds)⟩

theorem computed_positive_coverage {driver : Driver} {runtime : Engine driver}
    (formula : driver.Formula) {raw : Pattern}
    (session : Session driver runtime (.outgoingUniversal formula) raw) (computed : Computed session)
    (read : session.readout = .judgment (.decided true)) :
    ∃ source : driver.Decoded raw,
      fullObservations (runtime.cursor.tasks source.val)
        (fun receipt listed => Observation.mk source.val receipt listed []) <+ session.observations ∧
      ∀ receipt listed,
        (Observation.mk source.val receipt listed []) ∈ session.observations ∧
        Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) := by
  obtain ⟨source, budget, same, result⟩ := computed_running session computed true read
  rw [same]
  refine ⟨source, Mettapedia.OSLF.NativeTypes.Decision.Machine.positive_universal_ordered_coverage
    runtime.cursor runtime.leaves formula source.val source.property.1 budget result, ?_⟩
  intro receipt listed
  obtain ⟨saved, holds⟩ := Mettapedia.OSLF.NativeTypes.Decision.Machine.positive_universal_saved_coverage
    runtime.cursor runtime.leaves formula source.val source.property.1 budget result receipt listed
  exact ⟨saved, (target_meaning driver runtime formula source receipt listed).mp holds⟩

theorem search_positive_receipt (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) (budget : Nat)
    (read : (search driver runtime (.possibility formula) raw budget).readout = .judgment (.decided true)) :
    ∃ source : driver.Decoded raw, ∃ receipt listed,
      (Observation.mk source.val receipt listed []) ∈
        (search driver runtime (.possibility formula) raw budget).observations ∧
      driver.system.Step source.val (runtime.cursor.target source.val receipt) ∧
      Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) :=
  computed_positive_receipt formula _ (computed_search driver runtime _ raw budget) read

theorem search_negative_counterreceipt (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) (budget : Nat)
    (read : (search driver runtime (.outgoingUniversal formula) raw budget).readout = .judgment (.decided false)) :
    ∃ source : driver.Decoded raw, ∃ receipt listed,
      (Observation.mk source.val receipt listed []) ∈
        (search driver runtime (.outgoingUniversal formula) raw budget).observations ∧
      driver.system.Step source.val (runtime.cursor.target source.val receipt) ∧
      ¬ Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) :=
  computed_negative_counterreceipt formula _ (computed_search driver runtime _ raw budget) read

theorem search_negative_coverage (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) (budget : Nat)
    (read : (search driver runtime (.possibility formula) raw budget).readout = .judgment (.decided false)) :
    ∃ source : driver.Decoded raw,
      fullObservations (runtime.cursor.tasks source.val)
        (fun receipt listed => Observation.mk source.val receipt listed []) <+
          (search driver runtime (.possibility formula) raw budget).observations ∧
      ∀ receipt listed,
        (Observation.mk source.val receipt listed []) ∈
          (search driver runtime (.possibility formula) raw budget).observations ∧
        ¬ Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) :=
  computed_negative_coverage formula _ (computed_search driver runtime _ raw budget) read

theorem search_positive_coverage (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) (budget : Nat)
    (read : (search driver runtime (.outgoingUniversal formula) raw budget).readout = .judgment (.decided true)) :
    ∃ source : driver.Decoded raw,
      fullObservations (runtime.cursor.tasks source.val)
        (fun receipt listed => Observation.mk source.val receipt listed []) <+
          (search driver runtime (.outgoingUniversal formula) raw budget).observations ∧
      ∀ receipt listed,
        (Observation.mk source.val receipt listed []) ∈
          (search driver runtime (.outgoingUniversal formula) raw budget).observations ∧
        Meaning driver formula (driver.render (runtime.cursor.target source.val receipt)) :=
  computed_positive_coverage formula _ (computed_search driver runtime _ raw budget) read

theorem check_positive_receipt (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw) (budget : Nat)
    (read : (check driver runtime (.possibility formula) source budget).readout = .judgment (.decided true)) :
    ∃ decoded : driver.Decoded raw, ∃ receipt listed,
      (Observation.mk decoded.val receipt listed []) ∈
        (check driver runtime (.possibility formula) source budget).observations ∧
      driver.system.Step decoded.val (runtime.cursor.target decoded.val receipt) ∧
      Meaning driver formula (driver.render (runtime.cursor.target decoded.val receipt)) :=
  computed_positive_receipt formula _ (computed_check driver runtime _ source budget) read

theorem check_negative_counterreceipt (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw) (budget : Nat)
    (read : (check driver runtime (.outgoingUniversal formula) source budget).readout = .judgment (.decided false)) :
    ∃ decoded : driver.Decoded raw, ∃ receipt listed,
      (Observation.mk decoded.val receipt listed []) ∈
        (check driver runtime (.outgoingUniversal formula) source budget).observations ∧
      driver.system.Step decoded.val (runtime.cursor.target decoded.val receipt) ∧
      ¬ Meaning driver formula (driver.render (runtime.cursor.target decoded.val receipt)) :=
  computed_negative_counterreceipt formula _ (computed_check driver runtime _ source budget) read

theorem check_negative_coverage (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw) (budget : Nat)
    (read : (check driver runtime (.possibility formula) source budget).readout = .judgment (.decided false)) :
    ∃ decoded : driver.Decoded raw,
      fullObservations (runtime.cursor.tasks decoded.val)
        (fun receipt listed => Observation.mk decoded.val receipt listed []) <+
          (check driver runtime (.possibility formula) source budget).observations ∧
      ∀ receipt listed,
        (Observation.mk decoded.val receipt listed []) ∈
          (check driver runtime (.possibility formula) source budget).observations ∧
        ¬ Meaning driver formula (driver.render (runtime.cursor.target decoded.val receipt)) :=
  computed_negative_coverage formula _ (computed_check driver runtime _ source budget) read

theorem check_positive_coverage (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) {raw : Pattern} (source : driver.Decoded raw) (budget : Nat)
    (read : (check driver runtime (.outgoingUniversal formula) source budget).readout = .judgment (.decided true)) :
    ∃ decoded : driver.Decoded raw,
      fullObservations (runtime.cursor.tasks decoded.val)
        (fun receipt listed => Observation.mk decoded.val receipt listed []) <+
          (check driver runtime (.outgoingUniversal formula) source budget).observations ∧
      ∀ receipt listed,
        (Observation.mk decoded.val receipt listed []) ∈
          (check driver runtime (.outgoingUniversal formula) source budget).observations ∧
        Meaning driver formula (driver.render (runtime.cursor.target decoded.val receipt)) :=
  computed_positive_coverage formula _ (computed_check driver runtime _ source budget) read

end Mettapedia.OSLF.NativeTypes.Runtime.Evidence
