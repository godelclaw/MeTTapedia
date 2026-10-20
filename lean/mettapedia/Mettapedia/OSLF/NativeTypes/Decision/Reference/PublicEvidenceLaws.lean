import Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence
import Mettapedia.OSLF.NativeTypes.Decision.Reference.EvidenceLaws

open Mettapedia.OSLF.Framework

/-!
# Evidence laws for the computed public entry point

Conclusive public readouts retain the actual first stopping horizon.
Existential witnesses and outgoing universal counterexamples belong to the
receipt view of that round and retain the continuation's native meaning.
Absence and universal truth establish closed coverage of every actual step.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidenceLaws

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Admission
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded Mettapedia.OSLF.NativeTypes.Decision.Reference.EvidenceLaws

theorem decided_admission (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) (answer : Bool)
    (read : (checkSource driver formula source budget).readout = .judgment (.decided answer)) :
    firstRefusal driver.generated.logicFragment driver.leafAdmission formula = none ∧
      driver.profileAdmission = some true := by
  unfold checkSource at read
  split at read
  · rename_i reason refused
    cases reason <;> cases read
  · rename_i formed
    split at read
    · cases read
    · cases read
    · rename_i permitted
      exact ⟨formed, permitted⟩

theorem computed_observed (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat)
    (formation : firstRefusal driver.generated.logicFragment driver.leafAdmission formula = none)
    (profile : driver.profileAdmission = some true) :
    checkSource driver formula source budget =
      .observed source ((firstRefusal_exact _ _ _).mp formation) profile
        (run driver.backend driver.tests formula source.val budget) := by
  unfold checkSource
  split
  · rename_i reason refused
    rw [formation] at refused
    cases refused
  · split
    · rename_i refused
      rw [profile] at refused
      cases refused
    · rename_i refused
      rw [profile] at refused
      cases refused
    · rfl

theorem decided_run (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) (answer : Bool)
    (read : (checkSource driver formula source budget).readout = .judgment (.decided answer)) :
    (run driver.backend driver.tests formula source.val budget).outcome.answer = some answer := by
  obtain ⟨formation, profile⟩ := decided_admission driver formula source budget answer read
  rw [computed_observed driver formula source budget formation profile] at read
  simp only [Report.readout, Report.result, Result.readout, Verdict.readout] at read
  cases found : (run driver.backend driver.tests formula source.val budget).outcome.answer with
  | none => simp [found] at read
  | some value =>
    have same : value = answer := by simpa [found] using read
    simp only [same]

theorem computed_frontier (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) (answer : Bool)
    (read : (checkSource driver formula source budget).readout = .judgment (.decided answer)) :
    (checkSource driver formula source budget).frontier =
      some ⟨source, frontierView driver.backend (run driver.backend driver.tests formula source.val budget)⟩ := by
  obtain ⟨formation, profile⟩ := decided_admission driver formula source budget answer read
  rw [computed_observed driver formula source budget formation profile]
  rfl

theorem computed_first_horizon (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) (answer : Bool)
    (read : (checkSource driver formula source budget).readout = .judgment (.decided answer)) :
    let horizon := (run driver.backend driver.tests formula source.val budget).horizon
    (checkSource driver formula source budget).horizon = some horizon ∧ horizon ≤ budget ∧
      (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.raw driver.backend driver.tests horizon formula source.val).answer = some answer ∧
      ∀ previous, 1 ≤ previous → previous < horizon →
        (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.raw driver.backend driver.tests previous formula source.val).answer = none := by
  obtain ⟨formation, profile⟩ := decided_admission driver formula source budget answer read
  have stopped := decided_run driver formula source budget answer read
  refine ⟨?_, run_horizon_le _ _ _ _ _, run_stopped_at_answer _ _ _ _ _ _ stopped, ?_⟩
  · rw [computed_observed driver formula source budget formation profile]
    rfl
  · intro previous positive earlier
    exact scan_prior_unknown _ 1 budget previous positive earlier

theorem positive_possibility_receipt (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat)
    (read : (checkSource driver (.possibility formula) source budget).readout = .judgment (.decided true)) :
    ∃ view : FrontierView driver.backend source.val,
      (checkSource driver (.possibility formula) source budget).frontier = some ⟨source, view⟩ ∧
        ∃ receipt, receipt ∈ view.receipts ∧ driver.system.Step source.val (driver.backend.target source.val receipt) ∧
          denotation driver.tests formula driver.backend.spatial.theory (driver.backend.target source.val receipt) := by
  refine ⟨frontierView driver.backend (run driver.backend driver.tests (.possibility formula) source.val budget),
    computed_frontier driver (.possibility formula) source budget true read, ?_⟩
  exact recorded_positive_receipt_evidence driver.backend driver.tests formula source.val budget
    (decided_run driver (.possibility formula) source budget true read)

theorem negative_universal_counterreceipt (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat)
    (read : (checkSource driver (.outgoingUniversal formula) source budget).readout = .judgment (.decided false)) :
    ∃ view : FrontierView driver.backend source.val,
      (checkSource driver (.outgoingUniversal formula) source budget).frontier = some ⟨source, view⟩ ∧
        ∃ receipt, receipt ∈ view.receipts ∧ driver.system.Step source.val (driver.backend.target source.val receipt) ∧
          ¬ denotation driver.tests formula driver.backend.spatial.theory (driver.backend.target source.val receipt) := by
  refine ⟨frontierView driver.backend (run driver.backend driver.tests (.outgoingUniversal formula) source.val budget),
    computed_frontier driver (.outgoingUniversal formula) source budget false read, ?_⟩
  exact recorded_negative_receipt_evidence driver.backend driver.tests formula source.val budget
    (decided_run driver (.outgoingUniversal formula) source budget false read)

theorem negative_possibility_closed_coverage (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat)
    (read : (checkSource driver (.possibility formula) source budget).readout = .judgment (.decided false)) :
    ∃ view : FrontierView driver.backend source.val,
      (checkSource driver (.possibility formula) source budget).frontier = some ⟨source, view⟩ ∧
        view.closed = true ∧ ∀ target, driver.system.Step source.val target →
          ∃ receipt, receipt ∈ view.receipts ∧ driver.system.Equiv target (driver.backend.target source.val receipt) := by
  have stopped := decided_run driver (.possibility formula) source budget false read
  refine ⟨frontierView driver.backend (run driver.backend driver.tests (.possibility formula) source.val budget),
    computed_frontier driver (.possibility formula) source budget false read,
    recorded_negative_possibility_closed _ _ _ _ _ stopped, ?_⟩
  exact recorded_negative_possibility_coverage _ _ _ _ _ stopped

theorem positive_universal_closed_coverage (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat)
    (read : (checkSource driver (.outgoingUniversal formula) source budget).readout = .judgment (.decided true)) :
    ∃ view : FrontierView driver.backend source.val,
      (checkSource driver (.outgoingUniversal formula) source budget).frontier = some ⟨source, view⟩ ∧
        view.closed = true ∧ ∀ target, driver.system.Step source.val target →
          ∃ receipt, receipt ∈ view.receipts ∧ driver.system.Equiv target (driver.backend.target source.val receipt) := by
  have stopped := decided_run driver (.outgoingUniversal formula) source budget true read
  refine ⟨frontierView driver.backend (run driver.backend driver.tests (.outgoingUniversal formula) source.val budget),
    computed_frontier driver (.outgoingUniversal formula) source budget true read,
    recorded_positive_universal_closed _ _ _ _ _ stopped, ?_⟩
  exact recorded_positive_universal_coverage _ _ _ _ _ stopped

end Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidenceLaws
