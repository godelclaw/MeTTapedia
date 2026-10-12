import Mettapedia.OSLF.Framework.MetabolicPaidLearner
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicStackInternalization

/-!
# Acquired physical credits funding an interventional learner

The concrete consumer offers an ordered source cost stack whose cells carry
singleton signatures. The faithful signature codec retains their ground
atoms. Acquisition transfers the entire stack without burning a cell;
commands, delivery and inspection then consume it through the coupled
structural protocol. Silent experiments leave the version space unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.MetabolicPaidControls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory
open Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
open Mettapedia.CognitiveArchitecture.Consciousness.PaidWorkspaceExperiments
open Mettapedia.OSLF.Framework.MetabolicPaidTrace
open Mettapedia.OSLF.Framework.MetabolicPaidLearner
open Mettapedia.GSLT.Causality Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.OSLF.Framework.FiniteAssayLearner
open Cost

/-- Every cell is a valid nonempty source signature, including atom zero. -/
def credits (atom : Nat) : Nat → CostStack Nat
  | 0 => .empty
  | count + 1 => .cons {atom} (credits atom count)

theorem credits_supported (atom count : Nat) : (credits atom count).RuntimeSupported := by
  induction count with
  | zero => trivial
  | succ count inductionHypothesis =>
      exact ⟨by simp [CostSig.RuntimeValid], inductionHypothesis⟩

def units (atom count : Nat) : Stack (CostSig Nat) :=
  Cost.Metabolic.StackInternalization.stack (credits atom count)

theorem units_size (atom count : Nat) : (units atom count).size = count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (units atom count).size + 1 = count + 1
      exact congrArg (fun amount => amount + 1) inductionHypothesis

theorem units_heads (atom count : Nat) :
    (units atom count).heads = List.replicate count ({atom} : CostSig Nat) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change {atom} :: (units atom count).heads = _
      rw [inductionHypothesis]
      rfl

def encoding : Encoding (CostSig Nat) := Cost.Metabolic.StackInternalization.signatureEncoding

/-- The offered resource and payer are computation-owned; the claimant
is an admitted external context. The full annotation is retained. -/
def acquisitionOrigins (prime : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : Origin :=
  if prime = Canonical.canonicalize claimant then .context else .computation

def workspaceReceipt (mode : Mode) (atom count : Nat) :=
  executeMetabolic encoding (initial mode) separatingQuestion (units atom count)
    10 20 30 [] acquisitionOrigins 100

theorem workspace_source_distinct (mode : Mode) (atom count : Nat) :
    Distinct (sourceFor encoding (initial mode) separatingQuestion (units atom count)
      10 20 30 [] acquisitionOrigins 100) :=
  annotate_distinct _ _ _

theorem full_charge_entries (mode : Mode) :
    (experimentPath (execute (initial mode) separatingQuestion 7 10 20 30)).charges = [1, 1, 0, 2, 3] := by
  cases mode <;> decide +kernel

theorem short_charge_entries (mode : Mode) :
    (experimentPath (execute (initial mode) separatingQuestion 6 10 20 30)).charges = [1, 1, 0, 2] := by
  cases mode <;> decide +kernel

theorem funded_actual_answer (mode : Mode) (atom : Nat) :
    (workspaceReceipt mode atom 7).answers =
      {(10, ComplementaryAssay.verdictOf (observation (initial mode) separatingQuestion),
        30, observation (initial mode) separatingQuestion)} := by
  change (execute (initial mode) separatingQuestion (units atom 7).size 10 20 30).responses = _
  rw [units_size, execute_responses, if_pos (by decide : separatingQuestion.commands.length + 2 + 3 ≤ 7)]

theorem complete_physical_price (mode : Mode) (atom : Nat) :
    (workspaceReceipt mode atom 7).experiment.spent = 7 ∧
      (workspaceReceipt mode atom 7).coupling.finalStack.size = 0 ∧
      (workspaceReceipt mode atom 7).execution.length = 15 := by
  have paid : (workspaceReceipt mode atom 7).experiment.spent = 7 := by
    change (execute (initial mode) separatingQuestion (units atom 7).size 10 20 30).spent = 7
    rw [units_size]
    exact (funded_separating_ledger mode).1
  have conserved := (workspaceReceipt mode atom 7).resource_ledger
  have cells := units_size atom 7
  refine ⟨paid, by omega, ?_⟩
  rw [AcquiredExperiment.execution_length, paid]

theorem acquired_claims_are_distinct (mode : Mode) (atom count : Nat) :
    (workspaceReceipt mode atom count).execution.claimedKeys.Nodup :=
  (workspaceReceipt mode atom count).no_repeated_claim (workspace_source_distinct mode atom count)

theorem connected_intervention_learns (atom : Nat) :
    (workspaceReceipt .connected atom 7).revision candidates = {.connected} := by
  change revised (initial .connected) separatingQuestion (units atom 7).size 10 20 30 = _
  rw [units_size]
  exact connected_funded_separates

theorem shadow_intervention_learns (atom : Nat) :
    (workspaceReceipt .shadow atom 7).revision candidates = {.shadow} := by
  change revised (initial .shadow) separatingQuestion (units atom 7).size 10 20 30 = _
  rw [units_size]
  exact shadow_funded_separates

theorem one_cell_short_is_silent (mode : Mode) (atom : Nat) :
    (workspaceReceipt mode atom 6).answers = 0 :=
  (workspaceReceipt mode atom 6).underfunded_silent (by rw [units_size]; decide)

theorem one_cell_short_keeps_candidates (mode : Mode) (atom : Nat) :
    (workspaceReceipt mode atom 6).revision candidates = candidates :=
  (workspaceReceipt mode atom 6).silence_preserves_candidates
    (by rw [units_size]; decide) candidates

theorem short_execution_retains_resource (mode : Mode) (atom : Nat) :
    (workspaceReceipt mode atom 6).experiment.spent = 4 ∧
      (workspaceReceipt mode atom 6).coupling.finalStack.size = 2 ∧
      (workspaceReceipt mode atom 6).execution.length = 9 := by
  have remaining : (workspaceReceipt mode atom 6).experiment.remaining = 2 := by
    change (execute (initial mode) separatingQuestion (units atom 6).size 10 20 30).assay.remaining = 2
    rw [units_size]
    have delivered := one_unit_short_delivery_only mode
    change (GSLT.Causality.ResourceInteraction.rightPart
      (execute (initial mode) separatingQuestion 6 10 20 30).assay.endpoint).card = 2
    rw [delivered]
    simp [AssayProbeDelivery.paidReceived, GSLT.Causality.ResourceInteraction.rightPart_marking,
      ComplementaryAssay.purse]
  have conserved := (workspaceReceipt mode atom 6).experiment.ledger
  have cells := units_size atom 6
  have paid : (workspaceReceipt mode atom 6).experiment.spent = 4 := by omega
  refine ⟨paid, (workspaceReceipt mode atom 6).current_resource.2.trans remaining, ?_⟩
  rw [AcquiredExperiment.execution_length, paid]

theorem empty_acquired_stack_is_silent (mode : Mode) (atom : Nat) :
    (workspaceReceipt mode atom 0).answers = 0 ∧
      (workspaceReceipt mode atom 0).revision candidates = candidates ∧
      (workspaceReceipt mode atom 0).execution.length = 1 := by
  have silence := (workspaceReceipt mode atom 0).underfunded_silent (by rw [units_size]; decide)
  refine ⟨silence, (workspaceReceipt mode atom 0).silence_preserves_candidates
    (by rw [units_size]; decide) candidates, ?_⟩
  have conserved := (workspaceReceipt mode atom 0).resource_ledger
  have cells := units_size atom 0
  have paid : (workspaceReceipt mode atom 0).experiment.spent = 0 := by omega
  rw [AcquiredExperiment.execution_length, paid]

theorem correct_candidate_survives (mode : Mode) (atom count : Nat) :
    mode ∈ (workspaceReceipt mode atom count).revision candidates :=
  (workspaceReceipt mode atom count).correct_candidate_survives mode

theorem distinct_source_atoms_keep_equal_answers (mode : Mode) :
    (workspaceReceipt mode 0 7).answers = (workspaceReceipt mode 1 7).answers ∧
      (units 0 7).heads ≠ (units 1 7).heads := by
  constructor
  · rw [funded_actual_answer, funded_actual_answer]
  · rw [units_heads, units_heads]
    decide +kernel

/-- An exhausted physical purse cannot admit any positive-charge event,
even if a Boolean observation can be described mathematically. -/
theorem exhausted_stack_cannot_pay {question : Question} {before after : Marking}
    (event : Event question before after) (positive : 0 < event.charge)
    (future : Nat) (record : List (CostSig Nat)) (source : Configuration) :
    IsEmpty (CoupledEvent encoding event .empty future record source) := by
  refine ⟨fun coupling => ?_⟩
  have affordable := coupling.affordable
  change event.charge ≤ 0 at affordable
  omega

end Mettapedia.OSLF.Framework.MetabolicPaidControls
