import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceBackward
import Mettapedia.Machines.BranchLocalNeed.RepresentationRelation
import Mettapedia.Machines.BranchLocalNeed.SharedContinuationInstance
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceStrict

/-!
# Adequacy on the ordered-system layer

The reference machine is an ordered system (`NeedRepresentation.needSystem`),
whose frontier runner is the machine's own. Adequacy therefore reads directly on
that layer (`ordered_answers`).

A lockstep ordered simulation between the specification and the machine does not
exist: the specification has no transition relation, and the machine spends a
varying number of transitions per alternative (`Controls.machine_partial`). The
source relation is stated at halted frontiers, which is the boundary at which
complete observations are compared. Unfinished shared configurations separately
read back to exact depth-first reference prefixes, with bounded administrative
overhead and no termination premise.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference
open Mettapedia.GSLT.Distinction

/-- The reference machine of an observed program as an ordered system. -/
abbrev orderedMachine (P : Program) : OrderedSystem MMachine :=
  NeedRepresentation.needSystem (machineSpec (observed P))

/-- **Adequacy on the ordered system.** From some fuel on, the halted frontier of
the observation of `M` presents the specified outcomes, one by one. -/
theorem ordered_answers {P : Program} {M : Comp} {L : List Result} (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ OutcomeRel L
        (((orderedMachine P).runFrontier fuel [initialMachine (observe M)]).filterMap
          haltedOutcome) := by
  obtain ⟨N, hN⟩ := (adequacy P M).1 L h
  refine ⟨N, fun fuel hfuel => ?_⟩
  rw [NeedRepresentation.needSystem_runFrontier]
  exact (hN fuel hfuel).2

/-- Ordered-system adequacy also retains the event sequence of every answer. -/
theorem ordered_observations {P : Program} {M : Comp} {L : List Result}
    (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ ObservationRel L
        (((orderedMachine P).runFrontier fuel [initialMachine (observe M)]).filterMap
          haltedObservation) := by
  obtain ⟨N, hN⟩ := observations_forward h
  refine ⟨N, fun fuel hfuel => ?_⟩
  rw [NeedRepresentation.needSystem_runFrontier]
  exact hN fuel hfuel

/-! ## Shared return continuations

The shared-continuation adapter can erase or retain causal receipts. The outcome
laws cover both modes; recorded readback additionally preserves the reference
worlds and effect histories. The independent source semantics is unchanged.
-/

/-- The authored computation starts in the existing shared-return machine with
its empty branch world and the same local control as the reference machine. -/
def sharedInitialTask (M : Comp) (keepReceipts : Bool := false) :
    NeedContinuation.NeedTask (Comp × MEnv) MLocal MResume MRule MVal Empty MFault Nat :=
  ⟨⟨NeedExecution.projectWorld keepReceipts initialWorld, {}⟩, .run (enter (observe M) []), []⟩

def sharedInitial (M : Comp) (keepReceipts : Bool := false) :
    NeedContinuation.NeedState (Comp × MEnv) MLocal MResume MRule MVal Empty MFault Nat :=
  ⟨[sharedInitialTask M keepReceipts], []⟩

@[simp] theorem sharedInitialTask_decodes (M : Comp) (keepReceipts : Bool := false) :
    NeedContinuation.taskMachine (sharedInitialTask M keepReceipts) =
      NeedExecution.projectMachine keepReceipts (initialMachine (observe M)) := rfl

/-- The complete ordered outcome observer of the shared representation. -/
def sharedAnswers (P : Program) (steps : Nat) (M : Comp) (keepReceipts : Bool := false) : List MOutcome :=
  ((SharedContinuation.step
    (NeedContinuation.program (machineSpec (observed P))))^[steps]
      (sharedInitial M keepReceipts)).emitted.map Prod.snd

def SharedFinished (P : Program) (M : Comp) (steps : Nat) (keepReceipts : Bool := false) : Prop :=
  ((SharedContinuation.step
    (NeedContinuation.program (machineSpec (observed P))))^[steps]
      (sharedInitial M keepReceipts)).frontier = []

/-- Readback includes unfinished tasks as well as published answers. It
refuses a frontier whose receipt history was erased. -/
def sharedReadback (P : Program) (steps : Nat) (M : Comp)
    (keepReceipts : Bool := true) : Option (List MMachine) :=
  (NeedContinuation.machines
    ((SharedContinuation.step (NeedContinuation.program (machineSpec (observed P))))^[steps]
      (sharedInitial M keepReceipts))).mapM NeedExecution.CoreMachine.readback?

/-- The recorded observer reads the retained execution, not a replay of the
producer. Missing histories are not reported as empty event sequences. -/
def sharedObservations (P : Program) (steps : Nat) (M : Comp)
    (keepReceipts : Bool := true) : Option (List (MOutcome × List Nat)) :=
  (sharedReadback P steps M keepReceipts).map (List.filterMap haltedObservation)

/-- Every recorded shared pause is a genuine depth-first reference prefix.
An active pause has at most one pending administrative claim beyond twice
its reference expansion count. No termination assumption is used. -/
theorem shared_readback_prefix (P : Program) (M : Comp) (steps : Nat) :
    ∃ count ≤ steps,
      (¬ SharedFinished P M steps true → steps ≤ 2 * count + 1) ∧
      sharedReadback P steps M =
        some (((orderedMachine P).expandFirst)^[count] [initialMachine (observe M)]) := by
  exact NeedContinuation.recorded_prefix_of_program (machineSpec (observed P))
    steps (sharedInitial M true)
    (NeedContinuation.settled_single (sharedInitialTask M true) rfl)
    [initialMachine (observe M)] rfl

/-- Conversely, each finite depth-first reference prefix is realized with
its complete causal graph by the existing shared-continuation program. -/
theorem shared_recorded_prefix_realization (P : Program) (M : Comp) (count : Nat) :
    ∃ steps ≤ 2 * count,
      sharedReadback P steps M =
        some (((orderedMachine P).expandFirst)^[count] [initialMachine (observe M)]) := by
  obtain ⟨steps, bound, _, readback⟩ :=
    NeedContinuation.program_of_recorded_prefix (machineSpec (observed P))
      count (sharedInitial M true)
      (NeedContinuation.settled_single (sharedInitialTask M true) rfl)
      [initialMachine (observe M)] rfl
  exact ⟨steps, bound, readback⟩

/-- Pausing and resuming the checked arena reads back to the complete rich
prefix of the authored computation, with no reconstruction by producer replay. -/
theorem shared_arena_resumption_readback (P : Program) (M : Comp) (first second : Nat) :
    let core := SharedContinuation.sharedCore
      (NeedContinuation.program (machineSpec (observed P)))
    let earlier := MachineCore.runSlice core first
      (SharedContinuation.encode (sharedInitial M true))
    let later := MachineCore.runSlice core second earlier.1
    ∃ count ≤ earlier.2 + later.2,
      (NeedContinuation.machines later.1.1.decode).mapM NeedExecution.CoreMachine.readback? =
        some (((orderedMachine P).expandFirst)^[count] [initialMachine (observe M)]) := by
  apply NeedContinuation.shared_resumption_recorded_prefix (machineSpec (observed P))
    first second (SharedContinuation.encode (sharedInitial M true))
  · rw [SharedContinuation.decode_encode]
    exact NeedContinuation.settled_single (sharedInitialTask M true) rfl
  · rw [SharedContinuation.decode_encode]
    rfl

/-- Erasure preserves completion as well as answers. Receipt storage is not
part of the halt test, even when an authored computation emits events. -/
theorem halted_iff_execution_halted (P : Program) (M : Comp) (fuel : Nat)
    (keepReceipts : Bool := false) :
    Halted P M fuel ↔
      (NeedExecution.runFrontier (machineSpec (observed P)) fuel
        [NeedExecution.projectMachine keepReceipts (initialMachine (observe M))]).all
          NeedExecution.isHalted = true := by
  rw [show [NeedExecution.projectMachine keepReceipts (initialMachine (observe M))] =
    [initialMachine (observe M)].map (NeedExecution.projectMachine keepReceipts) from rfl,
    ← NeedExecution.project_runFrontier_commutes]
  simp only [List.all_map, Function.comp_def, NeedExecution.isHalted_project,
    List.all_eq_true, Halted]

/-- Every finite specified observation is realized by the shared-return
program, in order and with multiplicity, under its outcome-only observer. -/
theorem shared_answers_forward {P : Program} {M : Comp} {L : List Result}
    (source : Observes P M L) (keepReceipts : Bool := false) :
    ∃ steps, SharedFinished P M steps keepReceipts ∧
      List.Forall₂ OutcomeRel L (sharedAnswers P steps M keepReceipts) := by
  obtain ⟨fuel, complete⟩ := (adequacy P M).1 L source
  obtain ⟨steps, done, answers⟩ := NeedContinuation.program_of_answers
    (machineSpec (observed P)) (sharedInitialTask M keepReceipts) rfl fuel
    (by simpa only [sharedInitialTask_decodes M keepReceipts] using
      (halted_iff_execution_halted P M fuel keepReceipts).mp (complete fuel le_rfl).1)
  refine ⟨steps, done, ?_⟩
  change List.Forall₂ OutcomeRel L
    (((SharedContinuation.step
      (NeedContinuation.program (machineSpec (observed P))))^[steps]
        ⟨[sharedInitialTask M keepReceipts], []⟩).emitted.map Prod.snd)
  rw [answers, sharedInitialTask_decodes M keepReceipts, NeedExecution.project_answers_commute]
  exact (complete fuel le_rfl).2

/-- A completed shared run determines a completed rich reference run. The
claim uses the independent projection theorem, not a new evaluation. -/
theorem shared_finished_halted {P : Program} {M : Comp} {steps : Nat} {keepReceipts : Bool}
    (done : SharedFinished P M steps keepReceipts) : Halted P M steps := by
  apply (halted_iff_execution_halted P M steps keepReceipts).mpr
  have exactRun := NeedContinuation.runFrontier_eq_of_program
    (machineSpec (observed P)) steps (sharedInitial M keepReceipts)
    (NeedContinuation.settled_single (sharedInitialTask M keepReceipts) rfl) done
  have initial : NeedContinuation.machines (sharedInitial M keepReceipts) =
      [NeedExecution.projectMachine keepReceipts (initialMachine (observe M))] := rfl
  rw [initial] at exactRun
  rw [exactRun]
  unfold SharedFinished at done
  simp [NeedContinuation.machines, done, NeedContinuation.answerMachine,
    NeedExecution.isHalted]

/-- Every completed shared run has a source derivation. No invented answer or
multiplicity is admitted by changing the return-stack representation. -/
theorem shared_answers_backward {P : Program} {M : Comp} {steps : Nat} {keepReceipts : Bool}
    (done : SharedFinished P M steps keepReceipts) :
    ∃ L, Observes P M L ∧ List.Forall₂ OutcomeRel L (sharedAnswers P steps M keepReceipts) := by
  obtain ⟨L, source, answers⟩ := answers_backward (shared_finished_halted done)
  refine ⟨L, source, ?_⟩
  have same := NeedContinuation.answers_eq_of_program
    (machineSpec (observed P)) (sharedInitialTask M keepReceipts) rfl steps done
  rw [sharedInitialTask_decodes M keepReceipts, NeedExecution.project_answers_commute] at same
  change machineAnswers P steps M = sharedAnswers P steps M keepReceipts at same
  rw [← same]
  exact answers

/-- A completed recorded shared execution reads back to exactly the rich
reference frontier: receipt identities and parents survive along with the
heap, control, branch path and work account. -/
theorem shared_finished_readback {P : Program} {M : Comp} {steps : Nat}
    (done : SharedFinished P M steps true) :
    sharedReadback P steps M =
      some (NeedReference.runFrontier (machineSpec (observed P)) steps
        [initialMachine (observe M)]) := by
  have exactRun := NeedContinuation.runFrontier_eq_of_program
    (machineSpec (observed P)) steps (sharedInitial M true)
    (NeedContinuation.settled_single (sharedInitialTask M true) rfl) done
  unfold sharedReadback
  rw [← exactRun]
  exact NeedExecution.recording_runFrontier_readback
    (machineSpec (observed P)) steps [initialMachine (observe M)]

theorem shared_finished_observations {P : Program} {M : Comp} {steps : Nat}
    (done : SharedFinished P M steps true) :
    sharedObservations P steps M = some (machineObservations P steps M) := by
  simp only [sharedObservations, shared_finished_readback done, Option.map_some,
    machineObservations]

/-- Recorded shared executions have source derivations with exactly their
ordered outcomes and per-branch effect histories. -/
theorem shared_observations_backward {P : Program} {M : Comp} {steps : Nat}
    (done : SharedFinished P M steps true) :
    ∃ L observations, Observes P M L ∧ sharedObservations P steps M = some observations ∧
      List.Forall₂ ObservationRel L observations := by
  obtain ⟨L, source, related⟩ := observations_backward (shared_finished_halted done)
  exact ⟨L, machineObservations P steps M, source, shared_finished_observations done, related⟩

/-- Every finite source observation is realized with its effect history by
recording in the same shared-return machine. -/
theorem shared_observations_forward {P : Program} {M : Comp} {L : List Result}
    (source : Observes P M L) :
    ∃ steps observations, SharedFinished P M steps true ∧
      sharedObservations P steps M = some observations ∧
      List.Forall₂ ObservationRel L observations := by
  obtain ⟨steps, done, _⟩ := shared_answers_forward source true
  obtain ⟨other, observations, otherSource, readback, related⟩ :=
    shared_observations_backward done
  have equal : L = other := Derives.deterministic source otherSource
  exact ⟨steps, observations, done, readback, equal ▸ related⟩

/-- One completed consumer preparation and repeated preparation have the
same source observations in the recorded shared machine. Each actual run
retains its own receipt graph; administrative steps and graph identities need
not coincide between the two representations. -/
theorem shared_normalized_observations {P : Program}
    (reserved : ∀ rule ∈ P, rule.head ≠ normHead) {M : Comp} {L : List Result}
    (source : Observes P M L) :
    (∃ steps observations, SharedFinished P M steps true ∧
      sharedObservations P steps M = some observations ∧
      List.Forall₂ ObservationRel L observations) ∧
    (∃ steps observations, SharedFinished P (normalized M) steps true ∧
      sharedObservations P steps (normalized M) = some observations ∧
      List.Forall₂ ObservationRel L observations) :=
  ⟨shared_observations_forward source,
    shared_observations_forward ((observes_normalized_iff P reserved M L).mpr source)⟩

/-- Finite source observations and finished shared-return executions coincide.
The source need not terminate: the equivalence also rules out a spurious
completed shared run when there is no finite source derivation. -/
theorem observes_iff_shared_finishes (P : Program) (M : Comp)
    (keepReceipts : Bool := false) :
    (∃ L, Observes P M L) ↔ ∃ steps, SharedFinished P M steps keepReceipts := by
  constructor
  · rintro ⟨L, source⟩
    obtain ⟨steps, done, -⟩ := shared_answers_forward source keepReceipts
    exact ⟨steps, done⟩
  · rintro ⟨steps, done⟩
    obtain ⟨L, source, -⟩ := shared_answers_backward done
    exact ⟨L, source⟩

/-- Repeated consumer preparation creates no new completed run and loses no
existing completion, in either receipt mode. No termination assumption is
needed to exclude a spurious completion of the prepared computation. -/
theorem shared_normalization_completion_iff (P : Program)
    (reserved : ∀ rule ∈ P, rule.head ≠ normHead) (M : Comp) (keepReceipts : Bool := false) :
    (∃ steps, SharedFinished P (normalized M) steps keepReceipts) ↔
      ∃ steps, SharedFinished P M steps keepReceipts := by
  rw [← observes_iff_shared_finishes P (normalized M) keepReceipts,
    ← observes_iff_shared_finishes P M keepReceipts]
  constructor
  · rintro ⟨results, source⟩
    exact ⟨results, (observes_normalized_iff P reserved M results).mp source⟩
  · rintro ⟨results, source⟩
    exact ⟨results, (observes_normalized_iff P reserved M results).mpr source⟩

/-- The arena implementation with checked frame roots realizes exactly the
finite source observations at the ordered-outcome boundary. Frame sharing
changes the representation, while receipt erasure limits the observer.
Neither direction assumes that every authored computation terminates. -/
theorem shared_arena_adequacy (P : Program) (M : Comp)
    (keepReceipts : Bool := false) :
    (∀ L, Observes P M L → ∃ steps,
      ((SharedContinuation.checkedStep
        (NeedContinuation.program (machineSpec (observed P))))^[steps]
          (SharedContinuation.encode (sharedInitial M keepReceipts))).1.frontier = [] ∧
      List.Forall₂ OutcomeRel L
        (((SharedContinuation.checkedStep
          (NeedContinuation.program (machineSpec (observed P))))^[steps]
            (SharedContinuation.encode (sharedInitial M keepReceipts))).1.emitted.map
              Prod.snd)) ∧
    (∀ steps,
      ((SharedContinuation.checkedStep
        (NeedContinuation.program (machineSpec (observed P))))^[steps]
          (SharedContinuation.encode (sharedInitial M keepReceipts))).1.frontier = [] →
      ∃ L, Observes P M L ∧ List.Forall₂ OutcomeRel L
        (((SharedContinuation.checkedStep
          (NeedContinuation.program (machineSpec (observed P))))^[steps]
            (SharedContinuation.encode (sharedInitial M keepReceipts))).1.emitted.map
              Prod.snd)) := by
  have decoded (steps : Nat) := NeedContinuation.decode_checkedStep_iterate
    (NeedContinuation.program (machineSpec (observed P)))
    (SharedContinuation.encode (sharedInitial M keepReceipts)) steps
  simp only [SharedContinuation.decode_encode] at decoded
  have finished (steps : Nat) :
      ((SharedContinuation.checkedStep
        (NeedContinuation.program (machineSpec (observed P))))^[steps]
          (SharedContinuation.encode (sharedInitial M keepReceipts))).1.frontier = [] ↔
      SharedFinished P M steps keepReceipts := by
    unfold SharedFinished
    rw [← decoded steps]
    simp only [SharedContinuation.ArenaState.decode, List.map_eq_nil_iff]
  constructor
  · intro L source
    obtain ⟨steps, done, answers⟩ := shared_answers_forward source keepReceipts
    refine ⟨steps, (finished steps).mpr done, ?_⟩
    simpa only [sharedAnswers, ← decoded steps,
      SharedContinuation.ArenaState.decode] using answers
  · intro steps done
    obtain ⟨L, source, answers⟩ := shared_answers_backward ((finished steps).mp done)
    refine ⟨L, source, ?_⟩
    simpa only [sharedAnswers, ← decoded steps,
      SharedContinuation.ArenaState.decode] using answers

/-- Checked arena execution has the same recorded readback as shared-return
execution. In particular, arena frame sharing cannot erase causal histories. -/
theorem shared_arena_readback (P : Program) (M : Comp) (steps : Nat) :
    (NeedContinuation.machines
      ((SharedContinuation.checkedStep
        (NeedContinuation.program (machineSpec (observed P))))^[steps]
          (SharedContinuation.encode (sharedInitial M true))).1.decode).mapM
            NeedExecution.CoreMachine.readback? = sharedReadback P steps M := by
  rw [NeedContinuation.decode_checkedStep_iterate, SharedContinuation.decode_encode]
  rfl

/-- Both directions of source adequacy, now observed through the checked arena
with retained effects as well as ordered answers. -/
theorem shared_arena_observation_adequacy (P : Program) (M : Comp) :
    let state := fun steps => (SharedContinuation.checkedStep
      (NeedContinuation.program (machineSpec (observed P))))^[steps]
        (SharedContinuation.encode (sharedInitial M true))
    let observation := fun steps =>
      ((NeedContinuation.machines (state steps).1.decode).mapM
        NeedExecution.CoreMachine.readback?).map (List.filterMap haltedObservation)
    (∀ L, Observes P M L → ∃ steps observations,
      (state steps).1.frontier = [] ∧ observation steps = some observations ∧
        List.Forall₂ ObservationRel L observations) ∧
    (∀ steps, (state steps).1.frontier = [] → ∃ L observations,
      Observes P M L ∧ observation steps = some observations ∧
        List.Forall₂ ObservationRel L observations) := by
  dsimp only
  have decoded (steps : Nat) := NeedContinuation.decode_checkedStep_iterate
    (NeedContinuation.program (machineSpec (observed P)))
    (SharedContinuation.encode (sharedInitial M true)) steps
  simp only [SharedContinuation.decode_encode] at decoded
  have finished (steps : Nat) :
      ((SharedContinuation.checkedStep
        (NeedContinuation.program (machineSpec (observed P))))^[steps]
          (SharedContinuation.encode (sharedInitial M true))).1.frontier = [] ↔
      SharedFinished P M steps true := by
    unfold SharedFinished
    rw [← decoded steps]
    simp only [SharedContinuation.ArenaState.decode, List.map_eq_nil_iff]
  simp only [shared_arena_readback]
  constructor
  · intro L source
    obtain ⟨steps, observations, done, readback, related⟩ := shared_observations_forward source
    exact ⟨steps, observations, (finished steps).mpr done, readback, related⟩
  · intro steps done
    exact shared_observations_backward ((finished steps).mp done)

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
