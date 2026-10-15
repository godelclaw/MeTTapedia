import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderRunControls
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileCoverage

/-!
# Operational equation and provider settings affect actual execution

The equation-permission coordinate controls conversion enumeration while
leaving directed authored rules intact. Its independent semantics omits those
conversion generators when the coordinate is disabled. A finite provider
snapshot separately controls the conditional guards of both kinds of action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierSettingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open EquationFrontierBinderProfile EquationFrontierBinderSearch EquationFrontierBinderRunControls
open Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

def configuredModel (ambient : Nat) (allowed : List Token) (equationsEnabled : Bool) :=
  let authored := model ambient allowed
  { authored with equations := fun source =>
      if equationsEnabled then authored.equations source else ⟨[], []⟩ }

def configuredRun {ambient : Nat} (allowed : List Token) (equationsEnabled : Bool)
    (fuel : Nat) (source : State ambient) :=
  run (configuredModel ambient allowed equationsEnabled) fuel (initial source.pattern)

def Equation (allowed : List Token) (equationsEnabled : Bool) {ambient : Nat}
    (source target : State ambient) : Prop :=
  equationsEnabled = true ∧ EquationEdge allowed source target

def Step {ambient : Nat} (allowed : List Token) (equationsEnabled : Bool) :
    State ambient → State ambient → Prop :=
  Mettapedia.OSLF.Framework.FiniteEquationCoverage.ModuloStep
    (Equation allowed equationsEnabled) (Enabled allowed) Event.target

theorem disabled_conversion_is_identity {ambient : Nat} (allowed : List Token)
    (source target : State ambient)
    (conversion : Relation.EqvGen (Equation allowed false) source target) : source = target := by
  induction conversion with
  | rel before after impossible => simp [Equation] at impossible
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem disabled_equations_block_hidden_firing {ambient : Nat} (allowed : List Token)
    (index : Fin (ambient + 1)) :
    ¬ ∃ target, Step allowed false (tucked index) target := by
  rintro ⟨target, representative, event, before, firing, _⟩
  have equal := disabled_conversion_is_identity allowed (tucked index) representative before
  subst representative
  cases firing

theorem enabled_equations_admit_hidden_firing {ambient : Nat}
    (index : Fin (ambient + 1)) :
    Step [.permit] true (tucked index) (finished index) := by
  refine ⟨exposed index, ⟨⟨0, 0⟩, finished index⟩, ?_, ?_, .refl _⟩
  · exact .rel _ _ ⟨rfl, .extrusion index .permit (by simp)⟩
  · exact .consume index .permit 0 0 (by rfl)

theorem equation_setting_changes_actual_frontier {ambient : Nat}
    (index : Fin (ambient + 1)) :
    (configuredRun [.permit] false 1 (tucked index)).receipts = [] ∧
      quiescent (configuredRun [.permit] false 1 (tucked index)) = true ∧
      (configuredRun [.permit] true 2 (tucked index)).receipts =
        [firedReceipt index 0, firedReceipt index 1] := by
  have emptyFirings := (firing_batches index).1
  have enabled : configuredModel ambient [.permit] true = model ambient [.permit] := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [configuredRun, run, tick, initial, configuredModel, emptyFirings,
      readouts, discoveries, obligations]
  · simp [configuredRun, run, tick, initial, configuredModel, emptyFirings,
      readouts, discoveries, obligations, quiescent]
  · simp only [configuredRun, enabled]
    exact congrArg Snapshot.receipts (run_two index)

theorem empty_provider_batches {ambient : Nat} (state : State ambient) :
    (model ambient []).equations state.pattern = ⟨[], []⟩ ∧
      (model ambient []).firings state.pattern = ⟨[], []⟩ := by
  change AuthoredEquationOccurrenceSearch.equationBatch _ _ _ _ _ _ = _ ∧
    AuthoredEquationOccurrenceSearch.firingBatch _ _ _ _ _ _ = _
  simp [equationBatch_family, firingBatch_family, expectedEquationReceipts,
    expectedRuleReceipts, expectedReceipts]

theorem provider_setting_changes_actual_frontier {ambient : Nat}
    (index : Fin (ambient + 1)) :
    (execute [] 1 (tucked index)).receipts = [] ∧
      status [] 1 (tucked index) = .certificateChecked ∧
      (execute [.permit] 2 (tucked index)).receipts.length = 2 := by
  have equations := (empty_provider_batches (tucked index)).1
  have firings := (empty_provider_batches (tucked index)).2
  have quiet : quiescent (execute [] 1 (tucked index)) = true := by
    simp [execute, run, tick, initial, equations, firings, discoveries,
      readouts, obligations, quiescent]
  refine ⟨?_, (checked_status_iff_quiescent [] (tucked index) 1).mpr quiet, ?_⟩
  · simp [execute, run, tick, initial, equations, firings, discoveries, readouts, obligations]
  · simp [run_two, completed]

theorem empty_provider_no_semantic_step {ambient : Nat} (source : State ambient) :
    ¬ ∃ target, EquationFrontierBinderProfile.Step [] source target := by
  rintro ⟨target, representative, event, _, firing, _⟩
  rcases event with ⟨⟨declaration, row⟩, endpoint⟩
  change Firing [] representative ⟨declaration, row⟩ endpoint at firing
  cases firing with
  | consume _ _ _ row impossible => simp at impossible

end Mettapedia.OSLF.MeTTaIL.EquationFrontierSettingControls
