import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.RegisteredReplayComposition

/-!
# Composition and policy-sensitive reuse of source export programs

Programs retain the complete receiver state between segments: registered
declarations, theorem cache, source addresses and publication receipts.
Constant and type definitions therefore compose through their actual
admission operations. A policy comparison observes each explicitly requested
axiom; it preserves both acceptance and refusal, not merely accepted roots.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExportReplay

open Mettapedia.Languages.OpenTheory
open ProofExecution DefinitionAdapters

theorem replayFrom_append (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (first second : List Event) :
    replayFrom policy before (first ++ second) =
      (replayFrom policy before first).bind (fun middle => replayFrom policy middle second) := by
  induction first generalizing before with
  | nil => rfl
  | cons event rest ih =>
      cases checked : apply policy before event <;> simp [replayFrom, checked, ih]

theorem replayFrom_append_iff (policy : AxiomPolicy) [DecidablePred policy]
    (before after : State) (first second : List Event) :
    replayFrom policy before (first ++ second) = some after ↔
      ∃ middle, replayFrom policy before first = some middle ∧
        replayFrom policy middle second = some after := by
  rw [replayFrom_append]
  cases checked : replayFrom policy before first <;> simp

theorem replayFrom_receipts (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {events : List Event}
    (accepted : replayFrom policy before events = some after) :
    after.receipts.toList = before.receipts.toList ++ events := by
  induction events generalizing before with
  | nil => cases Option.some.inj accepted; simp
  | cons event rest ih =>
      cases first : apply policy before event with
      | none => simp [replayFrom, first] at accepted
      | some middle =>
          have later : replayFrom policy middle rest = some after := by
            simpa [replayFrom, first] using accepted
          rw [ih later, (apply_checked policy first).2.2.2.1]
          simp

/-- Observations include exact requested sequents. Merely retaining an
axiom label would not justify this reuse theorem. -/
def requestedAxioms (events : List Event) : List Sequent :=
  events.filterMap (fun event => event.command.requestedAxiom)

theorem apply_policy_congr (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (before : State) (event : Event)
    (agree : ∀ sequent, event.command.requestedAxiom = some sequent →
      (first sequent ↔ second sequent)) :
    apply first before event = apply second before event := by
  simp only [apply, Registered.Command.check_policy_congr first second event.command
    before.registered.context before.registered.cache agree]

theorem replayFrom_policy_congr (first second : AxiomPolicy)
    [DecidablePred first] [DecidablePred second] (before : State) (events : List Event)
    (agree : ∀ sequent ∈ requestedAxioms events, first sequent ↔ second sequent) :
    replayFrom first before events = replayFrom second before events := by
  induction events generalizing before with
  | nil => rfl
  | cons event rest ih =>
      have current : ∀ sequent, event.command.requestedAxiom = some sequent →
          (first sequent ↔ second sequent) := by
        intro sequent requested
        exact agree sequent (List.mem_filterMap.mpr ⟨event, List.mem_cons_self, requested⟩)
      have remaining : ∀ sequent ∈ requestedAxioms rest, first sequent ↔ second sequent := by
        intro sequent member
        obtain ⟨entry, included, requested⟩ := List.mem_filterMap.mp member
        exact agree sequent (List.mem_filterMap.mpr
          ⟨entry, List.mem_cons_of_mem _ included, requested⟩)
      simp only [replayFrom, apply_policy_congr first second before event current]
      cases apply second before event with
      | none => rfl
      | some middle => exact ih middle remaining

/-- A negative replay result has the same policy footprint as a positive
one. Reuse across an unrelated policy edit is a proved equality of checkers. -/
theorem refusal_reuse (first second : AxiomPolicy) [DecidablePred first] [DecidablePred second]
    (before : State) (events : List Event)
    (agree : ∀ sequent ∈ requestedAxioms events, first sequent ↔ second sequent)
    (refused : replayFrom first before events = none) :
    replayFrom second before events = none := by
  rw [← replayFrom_policy_congr first second before events agree]
  exact refused

theorem revoked_axiom_refused (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (event : Event) (sequent : Sequent)
    (requested : event.command.requestedAxiom = some sequent) (revoked : ¬ policy sequent) :
    apply policy before event = none := by
  cases accepted : apply policy before event with
  | none => rfl
  | some after =>
      obtain ⟨output, checked, _, _⟩ := (apply_checked policy accepted).2.2.2.2
      exact False.elim (revoked (Registered.requested_axiom_formed requested checked).1)

/-- The source root after composition is the exact checked theorem in the
extended theory, including its own dependency ledger. Neither the caller's
claim nor program metadata can supply a replacement theorem value. -/
theorem composed_root (policy : AxiomPolicy) [DecidablePred policy]
    {before middle after : State} {first second : List Event}
    (valid : Valid policy before)
    (firstChecked : replayFrom policy before first = some middle)
    (secondChecked : replayFrom policy middle second = some after)
    {id : Nat} {claim : Sequent} {theoremValue : Theorem}
    (found : root? after id claim = some theoremValue) :
    replayFrom policy before (first ++ second) = some after ∧
      Registered.replayFrom policy before.registered
        ((first ++ second).map Event.command) = some after.registered ∧
      TheoryDerives policy after.registered.context theoremValue ∧
      theoremValue.sequent = claim := by
  have combined : replayFrom policy before (first ++ second) = some after := by
    rw [replayFrom_append, firstChecked]
    exact secondChecked
  have authorized := replayFrom_preserves_derivations policy before _ after valid combined
  exact ⟨combined, replayFrom_registered policy before _ after combined,
    root_derivation policy authorized found⟩

#print axioms replayFrom_append_iff
#print axioms replayFrom_receipts
#print axioms replayFrom_policy_congr
#print axioms revoked_axiom_refused
#print axioms composed_root

end Mettapedia.Languages.HOLLight.ExportReplay
