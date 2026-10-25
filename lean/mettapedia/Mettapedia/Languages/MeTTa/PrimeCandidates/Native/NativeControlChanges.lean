import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeRouteDemand
import Mettapedia.Machines.BranchLocalNeed.SharedContinuationInstance
import Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching
import Mettapedia.GSLT.Core.ConsumerGenerations

/-!
# Native continuation transfer and goal revision

The shared-return representation is instantiated with the authored equation
evaluator, its actual bound cells, branch worlds and resume tokens. A transfer
changes storage without rebuilding the call or forgetting its emitted prefix.

Goal revision rechecks retained witnesses. Detached pure collection consumers
carry generation ownership; revoking an obsolete generation preserves source
production and the newly admitted consumer. It is a cancellation contract,
not a scheduling permutation or a certificate for the new goal.

Bounded shared-arena slices use the common `MachineCore.runSlice` contract.
Their readout retains native Need worlds, work accounts, pending update/resume
frames and emitted occurrences. Shared-program dispatch counts remain distinct
from Need transitions, and neither count certifies a compiled implementation.
Recording mode additionally recovers the complete rich reference prefix at
every pause and resumption, including the causal graph of each branch.

The native shared producer also feeds the common owned occurrence log. Its
representation comparison retains pending returns, source context, consumer
positions and public roots. Capture services and native owner validity are
separate realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeControlChanges

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines
open Mettapedia.GSLT.Core
open BranchingTemporal
open InferenceControl (WorkOccurrence)
open NativeEquationNeed

abbrev NativeTask := NeedContinuation.NeedTask Origin Local Resume Rule Atom Empty String Empty
abbrev NativeState := NeedContinuation.NeedState Origin Local Resume Rule Atom Empty String Empty
abbrev NativeContext := NeedContinuation.Context Origin Rule Atom Empty String Empty

def initialTask (term : Atom) (keepReceipts : Bool := false) : NativeTask :=
  let source := NeedExecution.projectMachine keepReceipts (initial term)
  ⟨⟨source.world, source.work⟩, .force rootCell, []⟩

def initialState (term : Atom) (keepReceipts : Bool := false) : NativeState :=
  ⟨[initialTask term keepReceipts], []⟩

/-- The shared program starts from the independently constructed native Need
machine; its heap contains the authored root expression, rather than answers. -/
theorem initial_decodes (term : Atom) (keepReceipts : Bool := false) :
    NeedContinuation.machines (initialState term keepReceipts) =
      [NeedExecution.projectMachine keepReceipts (initial term)] := rfl

/-- Recording the authored-equation evaluator retains its complete rich
prefix through a checked arena pause: bindings, cells, branch paths, work and
causal graph. This remains a Lean evaluator theorem, not a C realization proof. -/
theorem native_recorded_partial_readback (equations : Program) (term : Atom) (fuel : Nat) :
    ∃ count ≤ (MachineCore.runSlice
        (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
        fuel (SharedContinuation.encode (initialState term true))).2,
      (NeedContinuation.machines (MachineCore.runSlice
        (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
        fuel (SharedContinuation.encode (initialState term true))).1.1.decode).mapM
          NeedExecution.CoreMachine.readback? =
        some (((NeedRepresentation.needSystem (specification equations)).expandFirst)^[count]
          [initial term]) := by
  apply NeedContinuation.shared_slice_recorded_prefix (specification equations) fuel
    (SharedContinuation.encode (initialState term true))
  · rw [SharedContinuation.decode_encode]
    exact NeedContinuation.settled_single (initialTask term true) rfl
  · rw [SharedContinuation.decode_encode]
    rfl

/-- The recorded authored equation run resumes its retained cells and causal
history, even when the pause falls between lookup and claim. -/
theorem native_recorded_resumption_readback
    (equations : Program) (term : Atom) (first second : Nat) :
    let core := SharedContinuation.sharedCore
      (NeedContinuation.program (specification equations))
    let earlier := MachineCore.runSlice core first
      (SharedContinuation.encode (initialState term true))
    let later := MachineCore.runSlice core second earlier.1
    ∃ count ≤ earlier.2 + later.2,
      (NeedContinuation.machines later.1.1.decode).mapM NeedExecution.CoreMachine.readback? =
        some (((NeedRepresentation.needSystem (specification equations)).expandFirst)^[count]
          [initial term]) := by
  apply NeedContinuation.shared_resumption_recorded_prefix (specification equations)
    first second (SharedContinuation.encode (initialState term true))
  · rw [SharedContinuation.decode_encode]
    exact NeedContinuation.settled_single (initialTask term true) rfl
  · rw [SharedContinuation.decode_encode]
    rfl

/-- A bounded authored-equation run decodes to a genuine prefix of the
independent Need evaluator. No completion premise discards its pending cells,
selected worlds, remaining rows or receiving frames. -/
theorem native_partial_prefix (equations : Program) (term : Atom) (fuel : Nat) :
    ∃ count ≤ (MachineCore.runSlice
        (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
        fuel (SharedContinuation.encode (initialState term))).2,
      NeedContinuation.machines (MachineCore.runSlice
        (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
        fuel (SharedContinuation.encode (initialState term))).1.1.decode =
        (NeedContinuation.expandFirst (specification equations))^[count]
          [NeedExecution.eraseMachine (initial term)] := by
  have settled : NeedContinuation.Settled (initialState term) :=
    NeedContinuation.settled_single (initialTask term) rfl
  simpa only [SharedContinuation.decode_encode, initial_decodes] using
    NeedContinuation.shared_slice_prefix (specification equations) fuel
      (SharedContinuation.encode (initialState term))
      (by rwa [SharedContinuation.decode_encode])

/-- Resumption continues the same authored equation execution even if a slice
ends between lookup and claim. Both slices retain their actual charges. -/
theorem native_resumption_prefix (equations : Program) (term : Atom) (first second : Nat) :
    let core := SharedContinuation.sharedCore
      (NeedContinuation.program (specification equations))
    let earlier := MachineCore.runSlice core first (SharedContinuation.encode (initialState term))
    let later := MachineCore.runSlice core second earlier.1
    ∃ count ≤ earlier.2 + later.2,
      NeedContinuation.machines later.1.1.decode =
        (NeedContinuation.expandFirst (specification equations))^[count]
          [NeedExecution.eraseMachine (initial term)] := by
  have settled : NeedContinuation.Settled (initialState term) :=
    NeedContinuation.settled_single (initialTask term) rfl
  simpa only [SharedContinuation.decode_encode, initial_decodes] using
    NeedContinuation.shared_resumption_prefix (specification equations) first second
      (SharedContinuation.encode (initialState term))
      (by rwa [SharedContinuation.decode_encode])

/-- As long as authored execution is still pending, shared administration
cannot outrun genuine Need progress by more than one unfinished claim. This
bound does not assume that the source term terminates. -/
theorem native_active_prefix_progress (equations : Program) (term : Atom) (steps : Nat)
    (active : ((SharedContinuation.step
      (NeedContinuation.program (specification equations)))^[steps]
        (initialState term)).frontier ≠ []) :
    ∃ count ≤ steps, steps ≤ 2 * count + 1 ∧
      NeedContinuation.machines ((SharedContinuation.step
        (NeedContinuation.program (specification equations)))^[steps] (initialState term)) =
        (NeedContinuation.expandFirst (specification equations))^[count]
          [NeedExecution.eraseMachine (initial term)] := by
  obtain ⟨count, bound, progress, decoded⟩ :=
    NeedContinuation.prefix_of_program (specification equations) steps (initialState term)
      (NeedContinuation.settled_single (initialTask term) rfl)
  exact ⟨count, bound, progress active, by simpa only [initial_decodes] using decoded⟩

/-- A native Need force may need a separate shared dispatch quantum. Both
representations retain the same physical alternatives and return obligations. -/
theorem native_shared_step (equations : Program) (task : NativeTask)
    (pending : List NativeTask) (published : List (NativeContext × Outcome))
    (settled : task.control.isClaim = false) :
    ∃ emitted fresh,
      (SharedContinuation.step (NeedContinuation.program (specification equations)))^[
          NeedContinuation.cost (specification equations) task] ⟨task :: pending, published⟩ =
        ⟨fresh ++ pending, published ++ emitted⟩ ∧
      (∀ next ∈ fresh, next.control.isClaim = false) ∧
      emitted.map NeedContinuation.answerMachine ++ fresh.map NeedContinuation.taskMachine =
        NeedExecution.step (specification equations) (NeedContinuation.taskMachine task) :=
  NeedContinuation.step_exact (specification equations) task pending published settled

theorem native_shared_quantum_bound (equations : Program) (task : NativeTask) :
    0 < NeedContinuation.cost (specification equations) task ∧
      NeedContinuation.cost (specification equations) task ≤ 2 :=
  NeedContinuation.cost_pos_le_two (specification equations) task

/-- The boundary can be reached with any captured environment, return stack,
branch state and prefix. The residual, rather than the original query, moves. -/
theorem transfer_retains_native_state (equations : Program) (before after : Nat)
    (state : NativeState) :
    Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats
      (SharedContinuation.step (NeedContinuation.program (specification equations))) after
      (Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats
        (SharedContinuation.checkedStep (NeedContinuation.program (specification equations)))
        before (SharedContinuation.encode state)).1.decode =
      Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats
        (SharedContinuation.step (NeedContinuation.program (specification equations)))
        (before + after) state :=
  Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching.split_execution_exact
    (NeedContinuation.program (specification equations)) before after state

/-- Administrative transfer resumes the captured native configuration, with
exact prefix, residual and performed shared-dispatch count. It does not reload
the authored call, and an exhausted slice budget does not mean a final state. -/
theorem transfer_retains_native_slice (equations : Program) (before after : Nat)
    (state : NativeState) :
    (let earlier := MachineCore.runSlice
        (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
        before (SharedContinuation.encode state)
     let later := MachineCore.runSlice
        (SharedContinuation.referenceCore (NeedContinuation.program (specification equations)))
        after earlier.1.1.decode
     (later.1, earlier.2 + later.2)) =
      MachineCore.runSlice
        (SharedContinuation.referenceCore (NeedContinuation.program (specification equations)))
        (before + after) state :=
  SharedContinuation.slice_transfer_exact
    (NeedContinuation.program (specification equations)) before after state

/-- A captured native Need context uses at most one additional shared return
node per performed dispatch. No factor of the number of alternatives appears. -/
theorem native_shared_slice_node_bounds (equations : Program) (fuel : Nat)
    (state : NativeState) :
    (SharedContinuation.encode state).1.arena.length ≤
        (MachineCore.runSlice
          (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
          fuel (SharedContinuation.encode state)).1.1.arena.length ∧
      (MachineCore.runSlice
          (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
          fuel (SharedContinuation.encode state)).1.1.arena.length ≤
        (SharedContinuation.encode state).1.arena.length +
          (MachineCore.runSlice
            (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
            fuel (SharedContinuation.encode state)).2 :=
  SharedContinuation.slice_node_bounds
    (NeedContinuation.program (specification equations)) fuel (SharedContinuation.encode state)

abbrev NativeSharedState := SharedContinuation.CheckedState NativeContext
  (NeedContinuation.Mode Origin Local Atom Empty String) (NeedReference.Frame Resume) Outcome


/-- The detached paid endpoint embeds in the original native frontier without
advancing later alternatives or rebuilding its retained return arena. This is
an exclusive-frontier law, separate from concurrent owner scheduling. -/
theorem native_frontier_paid_handoff_exact (equations : Program) (fuel : Nat)
    (state : NativeSharedState)
    (later : List (SharedContinuation.RootTask NativeContext
      (NeedContinuation.Mode Origin Local Atom Empty String)))
    (bounded : ∀ task ∈ later, task.root ≤ state.1.arena.length) :
    let detached := MachineCore.runSlice
      (SharedContinuation.sharedCore (NeedContinuation.program (specification equations))) fuel state
    let joined := MachineCore.runSlice
      (SharedContinuation.sharedCore (NeedContinuation.program (specification equations))) detached.2
      (SharedContinuation.appendCheckedFrontier state later bounded)
    joined.1.1 = detached.1.1.appendFrontier later ∧ joined.2 = detached.2 :=
  SharedContinuation.shared_slice_append_paid_arena
    (NeedContinuation.program (specification equations)) fuel state later bounded

/-- An externally held native return task keeps its world, work context and
frame payloads across the exclusively advanced slice. Service authority and
actual native owner validity remain separate realization obligations. -/
theorem native_held_return_exact (equations : Program) (fuel : Nat)
    (state : NativeSharedState)
    (task : SharedContinuation.RootTask NativeContext
      (NeedContinuation.Mode Origin Local Atom Empty String))
    (bounded : task.root ≤ state.1.arena.length) :
    task.decode (MachineCore.runSlice
      (SharedContinuation.sharedCore (NeedContinuation.program (specification equations)))
      fuel state).1.1.arena = task.decode state.1.arena :=
  SharedContinuation.slice_held_task_exact
    (NeedContinuation.program (specification equations)) fuel state task bounded

abbrev NativeReturn := NativeContext × Outcome

abbrev NativeReturnConfiguration (Stored SourceContext Output : Type) (clients : Nat) :=
  Cursor.ProducerOccurrenceLog.Configuration NativeSharedState NativeReturn
    Stored SourceContext Output Empty Empty clients

/-- This is the authored equation/Need instance of the common producer
composition, including unfinished producer worlds and publication obligations.
The separate source-context predicate is checked without granting it native
service authority merely from its Boolean result. -/
theorem native_owned_producer_run {Stored SourceContext Output : Type} {clients : Nat}
    (equations : Program) (capture : NativeReturn → Option Stored) (capacity : Stored → Bool)
    (compatible : SourceContext → Bool) (ticks : Nat)
    (state : NativeReturnConfiguration Stored SourceContext Output clients) :
    Cursor.ProducerOccurrenceLog.run
        (SharedContinuation.referenceProducerStep (NeedContinuation.program (specification equations)))
        capture capacity compatible ticks
        (Cursor.ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode) state) =
      ((Cursor.ProducerOccurrenceLog.run
          (SharedContinuation.sharedProducerStep (NeedContinuation.program (specification equations)))
          capture capacity compatible ticks state).1,
        Cursor.ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode)
          (Cursor.ProducerOccurrenceLog.run
            (SharedContinuation.sharedProducerStep (NeedContinuation.program (specification equations)))
            capture capacity compatible ticks state).2) :=
  SharedContinuation.producer_run_exact (NeedContinuation.program (specification equations))
    capture capacity compatible ticks state

theorem native_owned_producer_delivery {Stored SourceContext Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output] (compatible : SourceContext → Bool)
    (state : NativeReturnConfiguration Stored SourceContext Output clients)
    (client : Fin clients) (output : Output) :
    Cursor.ProducerOccurrenceLog.deliver compatible
        (Cursor.ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode) state) client output =
      ((Cursor.ProducerOccurrenceLog.deliver compatible state client output).1,
        Cursor.ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode)
          (Cursor.ProducerOccurrenceLog.deliver compatible state client output).2) :=
  SharedContinuation.producer_delivery_exact compatible state client output

abbrev NativeOccurrence := WorkOccurrence NativeMachine

def reprioritize {Memory : Type} (order : Scheduler NativeOccurrence)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) :=
  { state with search := { state.search with frontier := order.reorder state.search.frontier } }

theorem priority_retains_source_account {Memory : Type} (equations : Program) (depth : Nat)
    (order : Scheduler NativeOccurrence)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) :
    FiniteSearchCertificate.account (occurrenceSystem equations) depth
      (reprioritize order state).search =
        FiniteSearchCertificate.account (occurrenceSystem equations) depth state.search :=
  FiniteSearchCertificate.reorder_account (occurrenceSystem equations) depth state.search.events
    (order.reorder state.search.frontier) state.search.frontier
    (order.reorder_complete state.search.frontier)

def witnesses {Memory : Type}
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) : List Atom :=
  state.search.events.filterMap fun event => match event.value.1 with
    | .value value => some value
    | _ => none

def assess {Memory : Type} (goal : List Atom → Bool)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) : Bool :=
  goal (witnesses state)

theorem priority_retains_witnesses {Memory : Type} (order : Scheduler NativeOccurrence)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory) :
    witnesses (reprioritize order state) = witnesses state := rfl

abbrev JointWork := ResumableJointSelection.Work Atom
abbrev OwnedWork := ConsumerGenerations.Task NativeOccurrence JointWork

def collectionConsumer (goals : Nat → List Atom → Bool) (generation : Nat) :=
  ResumableJointSelection.system (goals generation)

/-- Revocation projects to the surviving current-generation computation. It
cannot inherit an obsolete success or manufacture source steps. -/
theorem detached_consumers_after_revision (equations : Program)
    (goals : Nat → List Atom → Bool) (old current : Nat) (different : old ≠ current)
    (pending : List OwnedWork) (next : NativeOccurrence ⊕ JointWork) :
    Generated (ConsumerGenerations.system (occurrenceSystem equations)
        (collectionConsumer goals)) (ConsumerGenerations.revoke old pending)
      (ConsumerGenerations.embed current next) ↔
    Generated (ConsumerGenerations.currentSystem (occurrenceSystem equations)
        (collectionConsumer goals current))
      (pending.filterMap (ConsumerGenerations.current? current)) next :=
  ConsumerGenerations.generated_after_revocation (occurrenceSystem equations)
    (collectionConsumer goals) old current different pending next

theorem revision_retains_native_occurrences (old : Nat) (pending : List OwnedWork) :
    (ConsumerGenerations.revoke old pending).filterMap ConsumerGenerations.source? =
      pending.filterMap ConsumerGenerations.source? :=
  ConsumerGenerations.source_preserved old pending

/-- Goal replacement creates one new collection root from the retained native
answers and revokes old pure consumer work. Source producers are retained. -/
def reviseConsumer {Memory : Type} (old current requested : Nat)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory)
    (pending : List OwnedWork) : List OwnedWork :=
  .consumer current (ResumableJointSelection.initial requested (witnesses state)) ::
    ConsumerGenerations.revoke old pending

theorem revised_consumer_retains_source {Memory : Type} (old current requested : Nat)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory)
    (pending : List OwnedWork) :
    (reviseConsumer old current requested state pending).filterMap ConsumerGenerations.source? =
      pending.filterMap ConsumerGenerations.source? := by
  simpa [reviseConsumer, List.filterMap_cons, ConsumerGenerations.source?] using
    revision_retains_native_occurrences old pending

theorem revised_consumer_root {Memory : Type} (old current requested : Nat)
    (state : InferenceControl.Snapshot NativeOccurrence (Outcome × List Nat) Memory)
    (pending : List OwnedWork) :
    ConsumerGenerations.Task.consumer current
      (ResumableJointSelection.initial requested (witnesses state)) ∈
        reviseConsumer old current requested state pending := List.mem_cons_self

namespace Controls

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- Pausing at the initial claim preserves the authored root exactly. Resuming
the recorded evaluator produces the two correlated pairs and two retained causal
graphs; the empty initial history is not substituted for either completed one. -/
theorem recorded_claim_resume_keeps_choice_histories :
    let query := NativeEquationNeed.Controls.call "twice" [NativeEquationNeed.Controls.call "coin"]
    let core := SharedContinuation.sharedCore
      (NeedContinuation.program (specification NativeEquationNeed.Controls.program))
    let earlier := MachineCore.runSlice core 1
      (SharedContinuation.encode (initialState query true))
    let later := MachineCore.runSlice core 100 earlier.1
    earlier.2 = 1 ∧
      (NeedContinuation.machines earlier.1.1.decode).mapM NeedExecution.CoreMachine.readback? =
        some [initial query] ∧
      ((NeedContinuation.machines later.1.1.decode).mapM NeedExecution.CoreMachine.readback?).map
        (List.filterMap NeedReference.haltedOutcome) =
          some [.value (NativeEquationNeed.Controls.call "Pair"
            [NativeEquationNeed.Controls.integer 0, NativeEquationNeed.Controls.integer 0]),
            .value (NativeEquationNeed.Controls.call "Pair"
            [NativeEquationNeed.Controls.integer 1, NativeEquationNeed.Controls.integer 1])] ∧
      ((NeedContinuation.machines later.1.1.decode).mapM NeedExecution.CoreMachine.readback?).map
        (List.map fun machine => machine.world.receipts.nodes.isEmpty) = some [false, false] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide +kernel

example : NeedContinuation.cost (specification NativeEquationNeed.Controls.program)
    (initialTask (NativeEquationNeed.Controls.call "twice"
      [NativeEquationNeed.Controls.call "coin"])) = 2 := by decide +kernel

def ownedChoiceStart : NativeReturnConfiguration Atom Nat Nat 1 :=
  Cursor.ProducerOccurrenceLog.initial
    (SharedContinuation.encode (initialState (NativeEquationNeed.Controls.call "twice"
      [NativeEquationNeed.Controls.call "coin"]))) 0 4

def captureValue (row : NativeReturn) : Option Atom :=
  match row.2 with
  | .value value => some value
  | _ => none

def ownedChoiceRun (ticks : Nat) :=
  Cursor.ProducerOccurrenceLog.run
    (SharedContinuation.sharedProducerStep
      (NeedContinuation.program (specification NativeEquationNeed.Controls.program)))
    captureValue (fun _ => true) (fun _ => true) ticks ownedChoiceStart

/-- The actual authored choice is allocated once per branch world; its two
demands agree. The producer/log adapter does not turn them into four choices. -/
theorem owned_producer_retains_native_call_time_choice :
    (ownedChoiceRun 100).2.delivery.log.rows =
      [NativeEquationNeed.Controls.call "Pair" [NativeEquationNeed.Controls.integer 0,
        NativeEquationNeed.Controls.integer 0],
       NativeEquationNeed.Controls.call "Pair" [NativeEquationNeed.Controls.integer 1,
        NativeEquationNeed.Controls.integer 1]] ∧
      (ownedChoiceRun 100).2.delivery.log.completed = true := by decide +kernel

/-- Existing answers satisfy the old occurrence goal but fail the revised
coverage goal. Reordering them supplies no missing final obligation. -/
example :
    let retained := execute NativeRouteDemand.program (NativeRouteDemand.query 4) 7 3000
    assess (DemandExecution.atLeast 7) retained = true ∧
      assess NativeRouteDemand.coversAll retained = false ∧
      witnesses (reprioritize Scheduler.reverseBreadthFirst retained) = witnesses retained :=
  by decide +kernel

def pending : List OwnedWork :=
  [.source (NativeRouteDemand.root 4),
   .consumer 0 (ResumableJointSelection.initial 7 NativeRouteDemand.allRoutes),
   .source (NativeRouteDemand.root 4),
   .consumer 1 (ResumableJointSelection.initial 7 NativeRouteDemand.allRoutes)]

example : (ConsumerGenerations.revoke 0 pending).filterMap ConsumerGenerations.source? =
    [NativeRouteDemand.root 4, NativeRouteDemand.root 4] := rfl

example : (ConsumerGenerations.receipt 0 pending).length = 1 := rfl

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeControlChanges
