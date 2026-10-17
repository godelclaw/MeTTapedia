import Mettapedia.Languages.Megalodon.RuleObservation
import Mettapedia.Languages.Megalodon.BudgetIndependent

/-!
# Resumable checking with distinct resource outcomes

This worker reads the same borrowed rows as the shared cursor. Its accepted
transition is exactly the shared transition; it additionally distinguishes
bad row structure, failed inference and unfinished normalization. Every stop
retains both the checked prefix and the entire unfinished suffix, without a
runtime journal. A normalization bound counts reference passes, while the row
bound counts attempted rows; neither is a bound on all native instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ObservedCursor
open MathdataKernel BorrowedProofCursor
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

inductive StepResult where
  | accepted (state : State Judgment)
  | refused
  | malformed
  | exhausted
  deriving DecidableEq

def StepResult.erase : StepResult → Option (State Judgment)
  | .accepted state => some state
  | _ => none

def observeStep {Origin : Type} (environment : Environment) (fuel : Nat)
    (store : Store Judgment Witness Origin) (state : State Judgment) (source : NodeId) : StepResult :=
  if state.revision ≠ store.revision then .malformed else
    if (indexAt state.checked source).isSome then .malformed else
      match store.read source with
      | none => .malformed
      | some node => match premiseValues state node.parents with
          | none => .malformed
          | some values => match RuleObservation.observe environment fuel node.request node.conclusion with
              | .refused => .refused
              | .exhausted => .exhausted
              | .requirements expected => if expected = values then
                  .accepted ⟨state.revision, (source, state.cache.size) :: state.checked,
                    state.cache.push node.conclusion⟩ else .refused

theorem observeStep_erases {Origin : Type} (environment : Environment) (fuel : Nat)
    (store : Store Judgment Witness Origin) (state : State Judgment) (source : NodeId) :
    (observeStep environment fuel store state source).erase =
      step (BorrowedProofCursor.interface environment fuel) store state source := by
  unfold observeStep step
  split
  · rfl
  · split
    · rfl
    · cases read : store.read source with
      | none => rfl
      | some node =>
          dsimp only
          cases parents : premiseValues state node.parents with
          | none => rfl
          | some values =>
              have agrees := RuleObservation.observe_erases environment fuel node.request node.conclusion
              cases observedRule : RuleObservation.observe environment fuel node.request node.conclusion with
              | refused | exhausted =>
                  simp only [observedRule, RuleObservation.Outcome.erase] at agrees
                  simp [BorrowedProofCursor.interface, ← agrees, StepResult.erase]
              | requirements expected =>
                  simp only [observedRule, RuleObservation.Outcome.erase] at agrees
                  by_cases same : expected = values <;>
                    simp [BorrowedProofCursor.interface, ← agrees, same, StepResult.erase]

theorem accepted_iff {Origin : Type} (environment : Environment) (fuel : Nat)
    (store : Store Judgment Witness Origin) (state next : State Judgment) (source : NodeId) :
    observeStep environment fuel store state source = .accepted next ↔
      step (BorrowedProofCursor.interface environment fuel) store state source = some next := by
  rw [← observeStep_erases]
  cases observeStep environment fuel store state source <;> simp [StepResult.erase]

def Valid (environment : Environment) (state : State Judgment) : Prop :=
  ∀ judgment ∈ state.cache, Derives (BudgetIndependent.UnboundedRules environment) judgment

theorem start_valid {Origin : Type} (environment : Environment) (store : Store Judgment Witness Origin) :
    Valid environment (start store) := by simp [Valid, start]

theorem step_valid {Origin : Type} {environment : Environment} {fuel : Nat}
    {store : Store Judgment Witness Origin} {state next : State Judgment} {source : NodeId}
    (prior : Valid environment state)
    (accepted : step (BorrowedProofCursor.interface environment fuel) store state source = some next) :
    Valid environment next := by
  obtain ⟨node, parents, _, _, replayed, _, _, shape⟩ :=
    step_correspondence (BorrowedProofCursor.interface environment fuel) store state next source accepted
  obtain ⟨values, found, ruleChecked, _⟩ := (Node.replay_eq_some_iff
    (BorrowedProofCursor.interface environment fuel) state.cache next.cache _).mp replayed
  have derived : Derives (BudgetIndependent.UnboundedRules environment) node.conclusion :=
    .node values node.conclusion
      ⟨fuel, (BorrowedProofCursor.interface environment fuel).sound _ _ _ ruleChecked⟩
      (fun premise member => prior premise (lookupPremises_mem state.cache found premise member))
  intro judgment member
  rw [shape, Array.mem_push] at member
  rcases member with previous | rfl
  · exact prior judgment previous
  · exact derived

inductive Status where
  | finished
  | paused
  | refused
  | malformed
  | exhausted
  deriving DecidableEq, Repr

structure Report where
  status : Status
  checkpoint : State Judgment
  pending : List NodeId
  deriving DecidableEq

def walk {Origin : Type} (environment : Environment) (fuel : Nat)
    (store : Store Judgment Witness Origin) : Nat → State Judgment → List NodeId → Report
  | _, state, [] => ⟨.finished, state, []⟩
  | 0, state, source :: rest => ⟨.paused, state, source :: rest⟩
  | rows + 1, state, source :: rest => match observeStep environment fuel store state source with
      | .accepted next => walk environment fuel store rows next rest
      | .refused => ⟨.refused, state, source :: rest⟩
      | .malformed => ⟨.malformed, state, source :: rest⟩
      | .exhausted => ⟨.exhausted, state, source :: rest⟩

/-- Every stop has a genuine accepted prefix, with the suffix kept intact.
The existential prefix is proof data, not a mandatory production journal. -/
theorem walk_partition {Origin : Type} (environment : Environment) (fuel : Nat)
    (store : Store Judgment Witness Origin) (rows : Nat) (state : State Judgment) (schedule : List NodeId) :
    let result := walk environment fuel store rows state schedule
    ∃ priorSteps, schedule = priorSteps ++ result.pending ∧ priorSteps.length ≤ rows ∧
      run (BorrowedProofCursor.interface environment fuel) store state priorSteps = some result.checkpoint := by
  induction rows generalizing state schedule with
  | zero =>
      cases schedule <;> exact ⟨[], rfl, Nat.zero_le _, rfl⟩
  | succ rows ih =>
      cases schedule with
      | nil => exact ⟨[], rfl, Nat.zero_le _, rfl⟩
      | cons source rest =>
          cases observed : observeStep environment fuel store state source with
          | accepted next =>
              obtain ⟨priorSteps, partition, fits, replayed⟩ := ih next rest
              have first := (accepted_iff environment fuel store state next source).mp observed
              refine ⟨source :: priorSteps, ?_, ?_, ?_⟩
              · simpa only [walk, observed, List.cons_append] using congrArg (List.cons source) partition
              · simpa only [List.length_cons] using Nat.succ_le_succ fits
              · simpa [walk, observed, run, first] using replayed
          | refused | malformed | exhausted =>
              exact ⟨[], by simp [walk, observed], Nat.zero_le _, by simp [walk, observed, run]⟩

theorem run_valid {Origin : Type} {environment : Environment} {fuel : Nat}
    {store : Store Judgment Witness Origin} {state final : State Judgment} {schedule : List NodeId}
    (prior : Valid environment state)
    (accepted : run (BorrowedProofCursor.interface environment fuel) store state schedule = some final) :
    Valid environment final := by
  induction schedule generalizing state with
  | nil => cases Option.some.inj accepted; exact prior
  | cons source rest ih =>
      cases first : step (BorrowedProofCursor.interface environment fuel) store state source with
      | none => simp [run, first] at accepted
      | some next => exact ih (step_valid prior first) (by simpa [run, first] using accepted)

theorem walk_valid {Origin : Type} (environment : Environment) (fuel : Nat)
    (store : Store Judgment Witness Origin) (rows : Nat) (state : State Judgment) (schedule : List NodeId)
    (prior : Valid environment state) :
    Valid environment (walk environment fuel store rows state schedule).checkpoint := by
  obtain ⟨_, _, _, accepted⟩ := walk_partition environment fuel store rows state schedule
  exact run_valid prior accepted

/-- Retrying can change either bound. Previously established judgments remain
valid in the same selected environment. -/
theorem retry_valid {Origin : Type} (environment : Environment) (firstFuel nextFuel firstRows nextRows : Nat)
    (store : Store Judgment Witness Origin) (state : State Judgment) (schedule : List NodeId)
    (prior : Valid environment state) :
    let first := walk environment firstFuel store firstRows state schedule
    Valid environment (walk environment nextFuel store nextRows first.checkpoint first.pending).checkpoint :=
  walk_valid environment nextFuel store nextRows _ _ (walk_valid environment firstFuel store firstRows _ _ prior)

theorem retained_root_original {environment : Environment} {state : State Judgment} {source : NodeId}
    {judgment : Judgment} (valid : Valid environment state) (found : rootAt state source = some judgment) :
    ∃ fuel proof, inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition := by
  unfold rootAt at found
  cases address : indexAt state.checked source with
  | none => simp [address] at found
  | some index =>
      have entry : state.cache[index]? = some judgment := by simpa [address] using found
      exact (BudgetIndependent.original_iff environment judgment).mp
        (valid judgment (Array.mem_of_getElem? entry))

theorem exhausted_keeps_failed_row {Origin : Type} (environment : Environment) (fuel rows : Nat)
    (store : Store Judgment Witness Origin) (state : State Judgment) (source : NodeId) (rest : List NodeId)
    (exhausted : observeStep environment fuel store state source = .exhausted) :
    walk environment fuel store (rows + 1) state (source :: rest) =
      ⟨.exhausted, state, source :: rest⟩ := by simp [walk, exhausted]

theorem finished_has_no_suffix {Origin : Type} (environment : Environment) (fuel rows : Nat)
    (store : Store Judgment Witness Origin) (state : State Judgment) (schedule : List NodeId)
    (finished : (walk environment fuel store rows state schedule).status = .finished) :
    (walk environment fuel store rows state schedule).pending = [] := by
  induction rows generalizing state schedule with
  | zero => cases schedule <;> simp_all [walk]
  | succ rows ih =>
      cases schedule with
      | nil => rfl
      | cons source rest =>
          cases observed : observeStep environment fuel store state source <;>
            simp only [walk, observed] at finished ⊢
          · exact ih _ _ finished
          all_goals cases finished

end Mettapedia.Languages.Megalodon.ObservedCursor
