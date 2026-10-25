import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.BranchLocalNeed.ExecutionMachine

/-!
# A conservative candidate for language-local Need transitions

The reference machine and its action interface remain unchanged. An explicit
extension may intercept a running local control with one silent local step;
all other controls and unhandled local states use the actual reference step.
The silent step preserves the complete world and outer stack, and charges one
transition with no heap, receipt or allocation work.

Disabling interception preserves arbitrary reference specifications, ordered
bounded frontiers and answers exactly. This candidate supplies neither a new
source language nor termination of repeated administrative transitions. It is
not a change to reference's default evaluator. In particular, an ordinary local
transition is not represented by a fabricated effect or fresh Need allocation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedLocalSteps

open NeedReference

/-- A reference specification plus an explicit, optional local-control step.
Only running local controls are eligible for interception. -/
structure Extension
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*) where
  reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect
  localStep : Local → Option Local

section Core

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

def ofReference
    (reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Extension Origin Local Resume Rule Value StableFault RetryableFault Effect :=
  ⟨reference, fun _ => none⟩

/-- One candidate transition; protocol states are delegated unchanged. -/
def step
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  match machine.control with
  | .run state stack =>
      match extension.localStep state with
      | some next => [finished machine machine.world (.run next stack) 0 0 0 0]
      | none => NeedReference.step extension.reference machine
  | _ => NeedReference.step extension.reference machine

def advance
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  match step extension machine with
  | [] => [machine]
  | next => next

/-- The same ordered-frontier policy as the reference driver, with the
candidate one-step operation. An unfinished state is retained, not refuted. -/
def runFrontier
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat → List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) →
      List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
  | 0, states => states
  | fuel + 1, states =>
      if states.all isHalted then states
      else runFrontier extension fuel (states.flatMap (advance extension))

def answers
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Produced Value StableFault RetryableFault) :=
  (runFrontier extension fuel [machine]).filterMap haltedOutcome

/-- The existing receipt-policy executor handles protocol operations. Only a
language-local control transition is intercepted, just as in the reference
extension; it neither allocates a cell nor fabricates a receipt. -/
def coreStep
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault
      RetryableFault Effect) :
    List (NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault
      RetryableFault Effect) :=
  match machine.control with
  | .run state stack =>
      match extension.localStep state with
      | some next => [{
          world := machine.world
          control := .run next stack
          work := machine.work.bump 0 0 0 0 }]
      | none => NeedExecution.step extension.reference machine
  | _ => NeedExecution.step extension.reference machine

/-- Local interception and the independently implemented protocol executor
commute with receipt selection. This is a one-step list equality, preserving
the position and multiplicity of every alternative, not a whole-run premise. -/
theorem project_local_step (keepReceipts : Bool)
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (step extension machine).map (NeedExecution.projectMachine keepReceipts) =
      coreStep extension (NeedExecution.projectMachine keepReceipts machine) := by
  cases control : machine.control with
  | run state stack =>
      cases selected : extension.localStep state with
      | none =>
          simpa only [step, coreStep, NeedExecution.projectMachine, control, selected] using
            NeedExecution.project_step_commutes extension.reference machine
      | some next =>
          simp only [step, coreStep, NeedExecution.projectMachine, control, selected,
            List.map_cons, List.map_nil, finished]
  | force cell stack =>
      simpa only [step, coreStep, NeedExecution.projectMachine, control] using
        NeedExecution.project_step_commutes extension.reference machine
  | returned outcome stack =>
      simpa only [step, coreStep, NeedExecution.projectMachine, control] using
        NeedExecution.project_step_commutes extension.reference machine
  | halted outcome =>
      simpa only [step, coreStep, NeedExecution.projectMachine, control] using
        NeedExecution.project_step_commutes extension.reference machine

/-- No projected successor can be invented by local interception or by the
receipt-policy executor. Equal-valued alternatives still have their original
list occurrences in `project_local_step`. -/
theorem core_step_lifts (keepReceipts : Bool)
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {next : NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault
      RetryableFault Effect}
    (member : next ∈ coreStep extension (NeedExecution.projectMachine keepReceipts machine)) :
    ∃ rich ∈ step extension machine, NeedExecution.projectMachine keepReceipts rich = next := by
  rw [← project_local_step keepReceipts extension machine] at member
  exact List.mem_map.mp member

variable
  (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
  (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)

theorem step_local {state next : Local} {stack : List (Frame Resume)}
    (control : machine.control = .run state stack)
    (selected : extension.localStep state = some next) :
    step extension machine =
      [finished machine machine.world (.run next stack) 0 0 0 0] := by
  simp only [step, control, selected]

theorem step_unhandled {state : Local} {stack : List (Frame Resume)}
    (control : machine.control = .run state stack)
    (unhandled : extension.localStep state = none) :
    step extension machine = NeedReference.step extension.reference machine := by
  simp only [step, control, unhandled]

theorem step_force {cell : CellId} {stack : List (Frame Resume)}
    (control : machine.control = .force cell stack) :
    step extension machine = NeedReference.step extension.reference machine := by
  simp only [step, control]

theorem step_returned {outcome : Produced Value StableFault RetryableFault}
    {stack : List (Frame Resume)} (control : machine.control = .returned outcome stack) :
    step extension machine = NeedReference.step extension.reference machine := by
  simp only [step, control]

theorem step_halted {outcome : Produced Value StableFault RetryableFault}
    (control : machine.control = .halted outcome) : step extension machine = [] := by
  simp only [step, control, NeedReference.step]

/-- A silent successor retains the entire world, not just its native answer
or heap; ownership, paths and causal receipt data are all unchanged. -/
theorem local_successor_exact {state next : Local} {stack : List (Frame Resume)}
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (control : machine.control = .run state stack)
    (selected : extension.localStep state = some next)
    (member : successor ∈ step extension machine) :
    successor.world = machine.world ∧ successor.control = .run next stack ∧
      successor.work = machine.work.bump 0 0 0 0 := by
  rw [step_local extension machine control selected, List.mem_singleton] at member
  subst successor
  exact ⟨rfl, rfl, rfl⟩

theorem local_successor_work {state next : Local} {stack : List (Frame Resume)}
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (control : machine.control = .run state stack)
    (selected : extension.localStep state = some next)
    (member : successor ∈ step extension machine) :
    successor.work.transitions = machine.work.transitions + 1 ∧
    successor.work.heapLookups = machine.work.heapLookups ∧
    successor.work.heapUpdates = machine.work.heapUpdates ∧
    successor.work.receiptAppends = machine.work.receiptAppends ∧
    successor.work.allocations = machine.work.allocations := by
  rw [(local_successor_exact extension machine control selected member).2.2]
  simp only [Work.bump, Nat.add_zero, and_self]

/-- Every successor is either a world-preserving local step or an actual
reference successor. This is also the transfer boundary for heap invariants. -/
theorem successor_world_eq_or_reference
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : successor ∈ step extension machine) :
    successor.world = machine.world ∨
      successor ∈ NeedReference.step extension.reference machine := by
  cases control : machine.control with
  | run state stack =>
      cases selected : extension.localStep state with
      | none => exact Or.inr (by simpa only [step, control, selected] using member)
      | some next =>
          exact Or.inl (local_successor_exact extension machine control selected member).1
  | force cell stack => exact Or.inr (by simpa only [step, control] using member)
  | returned outcome stack => exact Or.inr (by simpa only [step, control] using member)
  | halted outcome => exact Or.inr (by simpa only [step, control] using member)

theorem step_receipts_valid
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (valid : machine.world.receipts.Valid) (present : next ∈ step extension machine) :
    next.world.receipts.Valid := by
  rcases successor_world_eq_or_reference extension machine present with same | reference
  · simpa only [same] using valid
  · exact NeedReference.step_receipts_valid extension.reference machine next valid reference

theorem step_preserves_completed
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : successor ∈ step extension machine)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (lookup : machine.world.heap.lookup cell = some record)
    (completed : NeedCacheLaws.Cache.Completed record.cache) :
    successor.world.heap.lookup cell = some record := by
  rcases successor_world_eq_or_reference extension machine member with same | reference
  · simpa only [same] using lookup
  · exact NeedCacheLaws.step_preserves_completed extension.reference machine successor
      reference lookup completed

/-- Completion roles inspect the preserved heap and control. They remain
available when the implementation's causal recording coordinate is absent. -/
theorem project_completed_observation (keepReceipts : Bool) :
    NeedCacheLaws.completedObservation? machine.world.heap machine.control =
      NeedCacheLaws.completedObservation?
        (NeedExecution.projectMachine keepReceipts machine).world.heap
        (NeedExecution.projectMachine keepReceipts machine).control := rfl

/-- A completed-cache observation can never be an intercepted local step.
It is an actual force or owner-matched commit of the reference protocol. -/
theorem completed_observation_reference
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {observed : NeedCacheLaws.CompletedObservation Value StableFault RetryableFault}
    (classified : NeedCacheLaws.completedObservation? machine.world.heap machine.control = some observed)
    (member : successor ∈ step extension machine) :
    successor ∈ NeedReference.step extension.reference machine := by
  cases control : machine.control with
  | run state stack => simp [NeedCacheLaws.completedObservation?, control] at classified
  | halted outcome => simp [NeedCacheLaws.completedObservation?, control] at classified
  | force cell stack => simpa only [step, control] using member
  | returned outcome stack => simpa only [step, control] using member

/-- The common observation describes the receipt actually appended by this
extended source step. The statement is about the existing graph transition;
it does not infer production from an arbitrary supplied trace. -/
theorem completed_observation_step
    {successor : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {observed : NeedCacheLaws.CompletedObservation Value StableFault RetryableFault}
    (classified : NeedCacheLaws.completedObservation? machine.world.heap machine.control = some observed)
    (member : successor ∈ step extension machine) :
    let receipt := NeedCacheLaws.completedReceipt machine observed.kind observed.cell observed.outcome
    successor.world.receipts.nodes =
      ⟨receipt.id, machine.world.receipts.roots, .observe observed.cell observed.outcome⟩ ::
        machine.world.receipts.nodes ∧
      successor.world.receipts.roots = [receipt.id] ∧
      successor.world.receipts.nextSerial = machine.world.receipts.nextSerial + 1 := by
  exact NeedCacheLaws.completedReceipt?_step_receipt extension.reference
    (by simp only [NeedCacheLaws.completedReceipt?, classified, Option.map_some])
    (completed_observation_reference extension machine classified member)

/-- Source firing metadata is read from the actual suspended producer's
ordered alternatives. A cache delivery, running local step or unsuccessful
force contributes no source firing. -/
def firingChoices
    (reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (heap : Heap Origin Value StableFault)
    (control : Control Local Resume Value StableFault RetryableFault) : List (CellId × Rule) :=
  match control with
  | .force cell _ => match heap.lookup cell with
    | some ⟨origin, .suspended⟩ => (reference.alternatives origin).map (fun row => (cell, row.1))
    | _ => []
  | _ => []

/-- The same reader works on the real implementation heap/control, even
when it has no causal receipt graph. No history is synthesized by this map. -/
theorem project_firing_choices (keepReceipts : Bool) :
    firingChoices extension.reference machine.world.heap machine.control =
      firingChoices extension.reference
        (NeedExecution.projectMachine keepReceipts machine).world.heap
        (NeedExecution.projectMachine keepReceipts machine).control := rfl

def receiptRule {Origin Rule Value StableFault RetryableFault Effect : Type*}
    (node : ReceiptNode Origin Rule Value StableFault RetryableFault Effect) : Option (CellId × Rule) :=
  match node.payload with
  | .chooseRule cell rule => some (cell, rule)
  | _ => none

private theorem branch_firing_choices
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (index : Nat) (alternatives : List (Rule × Local)) :
    (branchAlternatives machine base cell record owner stack index alternatives).filterMap
      (fun successor => successor.world.receipts.nodes.head?.bind receiptRule) =
      alternatives.map (fun row => (cell, row.1)) := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons row rest ih =>
      simp only [branchAlternatives, List.filterMap_cons, List.map_cons, finished,
        recorded, World.record, ReceiptGraph.append, List.head?_cons, Option.bind_some,
        receiptRule, ih]

/-- Ordered firing metadata agrees with the actual new choice receipts
produced by a suspended-cell force. This includes the empty-alternative
retry case; it does not mistake that case for a successful empty answer. -/
theorem firing_choices_are_recorded
    {cell : CellId} {stack : List (Frame Resume)} {origin : Origin}
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell = some ⟨origin, .suspended⟩) :
    (step extension machine).filterMap
      (fun successor => successor.world.receipts.nodes.head?.bind receiptRule) =
      firingChoices extension.reference machine.world.heap machine.control := by
  cases alternatives : extension.reference.alternatives origin with
  | nil =>
      simp only [step, control, NeedReference.step, suspended, alternatives, firingChoices,
        List.map_nil, List.filterMap_cons, List.filterMap_nil, retryMachine, finished,
        recorded, World.record, ReceiptGraph.append, List.head?_cons, Option.bind_some, receiptRule]
  | cons row rest =>
      simp only [step, control, NeedReference.step, suspended, alternatives, firingChoices]
      exact branch_firing_choices machine _ _ _ _ _ _ _

theorem force_cached_value_step {cell : CellId} {stack : List (Frame Resume)}
    {origin : Origin} {value : Value}
    (control : machine.control = .force cell stack)
    (lookup : machine.world.heap.lookup cell = some ⟨origin, .value value⟩) :
    step extension machine =
      [finished machine (recorded machine.world (.observe cell (.value value)))
        (.returned (.value value) stack) 1 0 1 0] := by
  rw [step_force extension machine control]
  exact NeedCacheLaws.force_cached_value_step extension.reference machine control lookup

variable (reference : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

@[simp] theorem step_ofReference :
    step (ofReference reference) machine = NeedReference.step reference machine := by
  cases control : machine.control <;> simp only [step, control, ofReference]

@[simp] theorem advance_ofReference :
    advance (ofReference reference) machine = NeedReference.advance reference machine := by
  cases result : NeedReference.step reference machine <;>
    simp only [advance, step_ofReference, NeedReference.advance, result]

/-- Exact list equality preserves ordering, multiplicity, unfinished controls,
worlds and work for every reference specification, not merely one example. -/
@[simp] theorem runFrontier_ofReference (fuel : Nat)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    runFrontier (ofReference reference) fuel states =
      NeedReference.runFrontier reference fuel states := by
  induction fuel generalizing states with
  | zero => rfl
  | succ fuel ih =>
      have sameAdvance : advance (ofReference reference) = NeedReference.advance reference :=
        funext (fun state => advance_ofReference state reference)
      simp only [runFrontier, NeedReference.runFrontier, sameAdvance, ih]

@[simp] theorem answers_ofReference (fuel : Nat) :
    answers (ofReference reference) fuel machine = NeedReference.answers reference fuel machine := by
  simp only [answers, NeedReference.answers, runFrontier_ofReference]

end Core

namespace Examples

abbrev ExampleMachine := Machine Unit Nat Unit Unit Nat Unit Unit Unit
abbrev ExampleExtension := Extension Unit Nat Unit Unit Nat Unit Unit Unit

def world : World Unit Unit Nat Unit Unit Unit :=
  ⟨0, [], Heap.empty, ReceiptGraph.empty, 0, 0⟩

def reference : Spec Unit Nat Unit Unit Nat Unit Unit Unit where
  alternatives := fun _ => [((), 0)]
  action := fun state => .done (.value state)
  afterDemand := fun _ _ => 0
  afterAllocation := fun _ _ => 0

/-- Two actual silent controls, followed by the unchanged return protocol. -/
def candidate : ExampleExtension where
  reference := reference
  localStep := fun state => if state < 2 then some (state + 1) else none

def initial : ExampleMachine := ⟨world, .run 0 [], {}⟩

theorem silent_controls_reach_answer : answers candidate 4 initial = [.value 2] := by
  decide

theorem reference_answer_is_different : NeedReference.answers reference 4 initial = [.value 0] := by
  decide

/-- Exhausted fuel leaves a real running control, not a false outcome. -/
theorem unfinished_frontier :
    (runFrontier candidate 2 [initial]).map (fun machine => machine.control) = [.run 2 []] := by
  rfl

theorem unfinished_has_no_answer_yet : answers candidate 2 initial = [] := by
  decide

theorem silent_frontier_world :
    (runFrontier candidate 2 [initial]).map (fun machine => machine.world) = [world] := by
  rfl

theorem silent_frontier_work :
    (runFrontier candidate 2 [initial]).map (fun machine => machine.work) =
      [⟨2, 0, 0, 0, 0⟩] := by
  decide

def performReference : Spec Unit Nat Unit Unit Nat Unit Unit Unit :=
  { reference with action := fun _ => .perform () 1 }

def allocateReference : Spec Unit Nat Unit Unit Nat Unit Unit Unit :=
  { reference with action := fun _ => .allocate () (), afterAllocation := fun _ _ => 1 }

/-- These observations retain actual receipt creation and fresh-cell state. -/
def retainedObservation (machine : ExampleMachine) : Nat × Nat :=
  (machine.world.receipts.nodes.length, machine.world.nextCell)

theorem silent_observation : (step candidate initial).map retainedObservation = [(0, 0)] := by
  decide

theorem perform_observation :
    (NeedReference.step performReference initial).map retainedObservation = [(1, 0)] := by
  decide

theorem allocation_observation :
    (NeedReference.step allocateReference initial).map retainedObservation = [(1, 1)] := by
  decide

theorem silent_not_perform :
    (step candidate initial).map retainedObservation ≠
      (NeedReference.step performReference initial).map retainedObservation := by
  rw [silent_observation, perform_observation]
  decide

theorem silent_not_allocate :
    (step candidate initial).map retainedObservation ≠
      (NeedReference.step allocateReference initial).map retainedObservation := by
  rw [silent_observation, allocation_observation]
  decide

end Examples

#print axioms local_successor_exact
#print axioms local_successor_work
#print axioms step_preserves_completed
#print axioms force_cached_value_step
#print axioms runFrontier_ofReference
#print axioms answers_ofReference
#print axioms Examples.silent_controls_reach_answer
#print axioms Examples.unfinished_frontier
#print axioms Examples.silent_not_perform
#print axioms Examples.silent_not_allocate

end Mettapedia.Machines.BranchLocalNeed.NeedLocalSteps
