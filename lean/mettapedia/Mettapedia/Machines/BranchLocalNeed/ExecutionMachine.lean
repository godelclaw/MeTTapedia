import Mettapedia.Machines.BranchLocalNeed.ReferenceSemantics

/-!
# Reference Need execution with optional causal receipts

One execution machine supports both receipt erasure and recording. Cell identity,
branch worlds, alternative multiplicity, cache states, retry behavior, control
frames and work counters are preserved in both modes. Recording additionally
retains the causal graph, including receipt identities and parent edges.

`project_step_commutes` and `project_runFrontier_commutes` relate the independently
defined execution transitions to the rich reference semantics. Their list
equalities preserve order and duplicate occurrences. `step_commutes` is the
answer-only specialization; `recording_runFrontier_readback` recovers the complete
rich frontier, including unfinished configurations, in recording mode.

Erased receipt storage cannot be read back as an empty history. An answer-only
interpreter or compiled tier may omit storage only under an observer that does
not demand those histories. The semantic work account still counts the receipt
operations; these laws make no claim about the physical cost of recording.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedExecution

open NeedReference

/-- Branch world with an explicit receipt-retention choice. -/
structure CoreWorld
    (Origin Rule Value StableFault RetryableFault Effect : Type*) where
  lineage : LineageId
  path : WorldPath
  heap : Heap Origin Value StableFault
  nextCell : Nat
  nextEvaluator : EvaluatorId
  receipts : Option (ReceiptGraph Origin Rule Value StableFault RetryableFault Effect) := none

namespace CoreWorld

variable {Origin Rule Value StableFault RetryableFault Effect : Type*}

/-- Recording is selected by the world. An erased world stays erased; a
recording world appends the same identified node as the rich reference. -/
def record (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect :=
  { world with receipts := world.receipts.map fun graph => (graph.append world.path payload).1 }

def fork
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect :=
  { world with path := world.path ++ [branch] }

def setKnownCache
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect :=
  { world with heap := world.heap.setKnownCache cell record state }

def freshCell
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (generation : Nat) : CellId :=
  { lineage := world.lineage
    birth := world.path
    slot := world.nextCell
    generation := generation }

def allocate?
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (origin : Origin) (generation : Nat := 0) :
    Option
      (CoreWorld Origin Rule Value StableFault RetryableFault Effect ×
        CellId) :=
  let cell := world.freshCell generation
  match world.heap.allocate? cell origin with
  | none => none
  | some heap =>
      some (({ world with heap := heap, nextCell := world.nextCell + 1 }).record
        (.allocate cell origin), cell)

end CoreWorld

def projectWorld (keepReceipts : Bool)
    {Origin Rule Value StableFault RetryableFault Effect : Type*}
    (world : World Origin Rule Value StableFault RetryableFault Effect) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect where
  lineage := world.lineage
  path := world.path
  heap := world.heap
  nextCell := world.nextCell
  nextEvaluator := world.nextEvaluator
  receipts := if keepReceipts then some world.receipts else none

abbrev eraseWorld := @projectWorld false

structure CoreMachine
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*)
    where
  world : CoreWorld Origin Rule Value StableFault RetryableFault Effect
  control : Control Local Resume Value StableFault RetryableFault
  work : Work := {}

def projectMachine (keepReceipts : Bool)
    {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
      Effect where
  world := projectWorld keepReceipts machine.world
  control := machine.control
  work := machine.work

abbrev eraseMachine := @projectMachine false

/-- Readback is available exactly when the world retained its causal graph.
An erased history is not an empty history. -/
def CoreWorld.readback?
    {Origin Rule Value StableFault RetryableFault Effect : Type*}
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect) :
    Option (World Origin Rule Value StableFault RetryableFault Effect) :=
  world.receipts.map fun receipts =>
    { lineage := world.lineage, path := world.path, heap := world.heap
      nextCell := world.nextCell, nextEvaluator := world.nextEvaluator, receipts := receipts }

def CoreMachine.readback?
    {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
    (machine : CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Option (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  machine.world.readback?.map fun world =>
    { world := world, control := machine.control, work := machine.work }

@[simp] theorem readback_projectWorld
    {Origin Rule Value StableFault RetryableFault Effect : Type*}
    (world : World Origin Rule Value StableFault RetryableFault Effect) :
    (projectWorld true world).readback? = some world := rfl

@[simp] theorem readback_projectMachine
    {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (projectMachine true machine).readback? = some machine := rfl

@[simp] theorem readback_erasedMachine
    {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (eraseMachine machine).readback? = none := rfl

section ProjectionLaws

variable {keepReceipts : Bool}

variable {Origin Rule Value StableFault RetryableFault Effect : Type*}

@[simp] theorem projectWorld_fork
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) :
    (projectWorld keepReceipts) (world.fork branch) = ((projectWorld keepReceipts) world).fork branch :=
  rfl

@[simp] theorem projectWorld_setKnownCache
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    (projectWorld keepReceipts) (world.setKnownCache cell record state) =
      ((projectWorld keepReceipts) world).setKnownCache cell record state :=
  rfl

@[simp] theorem projectWorld_record
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    (projectWorld keepReceipts) (world.record payload).1 =
      ((projectWorld keepReceipts) world).record payload := by
  cases keepReceipts <;> rfl

@[simp] theorem projectWorld_freshCell
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (generation : Nat) :
    ((projectWorld keepReceipts) world).freshCell generation = world.freshCell generation :=
  rfl

theorem projectWorld_allocate?
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (origin : Origin) (generation : Nat := 0) :
    (world.allocate? origin generation).map
        (fun result => ((projectWorld keepReceipts) result.1, result.2)) =
      ((projectWorld keepReceipts) world).allocate? origin generation := by
  simp only [World.allocate?, CoreWorld.allocate?, projectWorld_freshCell]
  split <;> cases keepReceipts <;>
    simp_all [World.record, ReceiptGraph.append, projectWorld, CoreWorld.record]

end ProjectionLaws

section Dynamics

variable {keepReceipts : Bool}

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

private def finished
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world :
      CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
      Effect :=
  { world := world
    control := control
    work := machine.work.bump lookups updates receipts allocations }

private def retryMachine
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world :
      CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates priorReceipts allocations : Nat) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
      Effect :=
  finished machine (world.record (.retry cell reason)) (.returned (.retryableFault reason) stack)
    lookups updates (priorReceipts + 1) allocations

@[simp] theorem project_finished
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    (projectMachine keepReceipts)
        (NeedReference.finished machine world control
          lookups updates receipts allocations) =
      finished ((projectMachine keepReceipts) machine) ((projectWorld keepReceipts) world) control
        lookups updates receipts allocations := by
  cases keepReceipts <;> rfl

@[simp] theorem project_recorded
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    (projectWorld keepReceipts) (NeedReference.recorded world payload) =
      ((projectWorld keepReceipts) world).record payload := by
  cases keepReceipts <;> rfl

@[simp] theorem project_retryMachine
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates priorReceipts allocations : Nat) :
    (projectMachine keepReceipts)
        (NeedReference.retryMachine machine world cell reason stack
          lookups updates priorReceipts allocations) =
      retryMachine ((projectMachine keepReceipts) machine) ((projectWorld keepReceipts) world) cell reason stack
        lookups updates priorReceipts allocations := by
  cases keepReceipts <;> rfl

def branchAlternatives
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (base : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume)) :
    Nat → List (Rule × Local) →
      List
        (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)
  | _, [] => []
  | index, (rule, state) :: rest =>
      let world :=
        (base.fork index).setKnownCache cell record (.evaluating owner)
      let world := (world.record (.evaluate cell owner)).record (.chooseRule cell rule)
      finished machine world
          (.run state (.commit cell owner :: stack))
          1 1 2 0 ::
        branchAlternatives machine base cell record owner stack
          (index + 1) rest

/-- Independently defined execution transition. Receipt operations are counted
in `Work` in both modes; the world selects whether their nodes are retained. -/
def step
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    List
      (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :=
  match machine.control with
  | .halted _ => []
  | .force cell stack =>
      match machine.world.heap.lookup cell with
      | none =>
          [retryMachine machine machine.world cell (.outOfScope cell) stack
            1 0 0 0]
      | some record =>
          match record.cache with
          | .value value =>
              let outcome : Produced Value StableFault RetryableFault :=
                .value value
              [finished machine (machine.world.record (.observe cell outcome)) (.returned outcome stack)
                1 0 1 0]
          | .stableFault fault =>
              let outcome : Produced Value StableFault RetryableFault :=
                .stableFault fault
              [finished machine (machine.world.record (.observe cell outcome)) (.returned outcome stack)
                1 0 1 0]
          | .evaluating _ =>
              [retryMachine machine machine.world cell (.blackhole cell) stack
                1 0 0 0]
          | .suspended =>
              let owner := machine.world.nextEvaluator
              let base := { machine.world with nextEvaluator := owner + 1 }
              match spec.alternatives record.origin with
              | [] =>
                  [retryMachine machine (base.record (.evaluate cell owner)) cell (.noRule cell) stack
                    1 0 1 0]
              | alternatives =>
                  branchAlternatives machine base cell record owner stack
                    0 alternatives
  | .run state stack =>
      match spec.action state with
      | .done outcome =>
          [finished machine machine.world (.returned outcome stack) 0 0 0 0]
      | .demand cell resume =>
          [finished machine machine.world
            (.force cell (.resume resume :: stack)) 0 0 0 0]
      | .allocate origin resume =>
          let candidate := machine.world.freshCell 0
          match machine.world.allocate? origin with
          | none =>
              [retryMachine machine machine.world candidate
                (.allocationCollision candidate) stack 1 0 0 0]
          | some (world, cell) =>
              [finished machine world
                (.run (spec.afterAllocation resume cell) stack)
                1 1 1 1]
      | .resample source resume =>
          match machine.world.heap.lookup source with
          | none =>
              [retryMachine machine machine.world source (.outOfScope source)
                stack 1 0 0 0]
          | some sourceRecord =>
              let candidate :=
                machine.world.freshCell (source.generation + 1)
              match machine.world.allocate? sourceRecord.origin
                  (source.generation + 1) with
              | none =>
                  [retryMachine machine machine.world candidate
                    (.allocationCollision candidate) stack 2 0 0 0]
              | some (world, fresh) =>
                  [finished machine (world.record (.resample source fresh))
                    (.run (spec.afterAllocation resume fresh) stack)
                    2 1 2 1]
      | .perform effect next =>
          [finished machine (machine.world.record (.effect effect)) (.run next stack) 0 0 1 0]
  | .returned outcome stack =>
      match stack with
      | [] =>
          [finished machine machine.world (.halted outcome) 0 0 0 0]
      | .resume token :: rest =>
          [finished machine machine.world
            (.run (spec.afterDemand token outcome) rest) 0 0 0 0]
      | .commit cell owner :: rest =>
          match machine.world.heap.lookup cell with
          | none =>
              [retryMachine machine machine.world cell (.outOfScope cell)
                rest 1 0 0 0]
          | some record =>
              match record.cache with
              | .evaluating actual =>
                  if _hOwner : actual = owner then
                    let state : Cache Value StableFault :=
                      match outcome with
                      | .value value => .value value
                      | .stableFault fault => .stableFault fault
                      | .retryableFault _ => .suspended
                    let world :=
                      machine.world.setKnownCache cell record state
                    match outcome with
                    | .retryableFault reason =>
                        [retryMachine machine world cell reason rest 1 1 0 0]
                    | _ =>
                        [finished machine (world.record (.observe cell outcome)) (.returned outcome rest)
                          1 1 1 0]
                  else
                    [retryMachine machine machine.world cell
                      (.ownershipLost cell owner actual) rest 1 0 0 0]
              | _ =>
                  [retryMachine machine machine.world cell
                    (.ownershipLost cell owner 0) rest 1 0 0 0]

private theorem project_branchAlternatives
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume))
    (index : Nat) (alternatives : List (Rule × Local)) :
    (NeedReference.branchAlternatives machine base cell record owner
        stack index alternatives).map (projectMachine keepReceipts) =
      branchAlternatives ((projectMachine keepReceipts) machine) ((projectWorld keepReceipts) base) cell record
        owner stack index alternatives := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨rule, state⟩
      simp only [NeedReference.branchAlternatives, branchAlternatives,
        List.map_cons, List.cons.injEq]
      constructor
      · cases keepReceipts <;> rfl
      · exact ih (index + 1)

/-- Exact one-step commuting square.  This is stronger than reachability
soundness: list order and duplicate alternatives are preserved. -/
theorem project_step_commutes
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (NeedReference.step spec machine).map (projectMachine keepReceipts) =
      step spec ((projectMachine keepReceipts) machine) := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome =>
      cases keepReceipts <;> rfl
  | force cell stack =>
      simp only [NeedReference.step, step, projectMachine, projectWorld]
      generalize hLookup : world.heap.lookup cell = lookup
      cases lookup with
      | none =>
          simp only [List.map_cons, List.map_nil, project_retryMachine]
          cases keepReceipts <;> rfl
      | some record =>
          simp only
          cases hCache : record.cache with
          | suspended =>
              simp only
              generalize hAlternatives :
                spec.alternatives record.origin = alternatives
              cases alternatives with
              | nil =>
                  simp only
                  simp only [List.map_cons, List.map_nil,
                    project_retryMachine, project_recorded]
                  cases keepReceipts <;> rfl
              | cons head tail =>
                  simp only
                  simpa only [projectMachine, projectWorld] using
                    project_branchAlternatives
                      (Machine.mk world (.force cell stack) work)
                      { world with
                        nextEvaluator := world.nextEvaluator + 1 }
                      cell record world.nextEvaluator stack 0 (head :: tail)
          | evaluating owner =>
              simp only
              simp only [List.map_cons, List.map_nil, project_retryMachine]
              cases keepReceipts <;> rfl
          | value value =>
              simp only
              simp only [List.map_cons, List.map_nil, project_finished,
                project_recorded]
              cases keepReceipts <;> rfl
          | stableFault fault =>
              simp only
              simp only [List.map_cons, List.map_nil, project_finished,
                project_recorded]
              cases keepReceipts <;> rfl
  | run state stack =>
      simp only [NeedReference.step, step, projectMachine, projectWorld]
      generalize hAction : spec.action state = action
      cases action with
      | done outcome =>
          simp only [List.map_cons, List.map_nil, project_finished]
          cases keepReceipts <;> rfl
      | demand cell resume =>
          simp only [List.map_cons, List.map_nil, project_finished]
          cases keepReceipts <;> rfl
      | allocate origin resume =>
          simp only
          generalize hAllocation :
            world.allocate? origin = allocation
          have hErase := projectWorld_allocate? (keepReceipts := keepReceipts) world origin
          cases allocation with
          | none =>
              simp only
              simp only [hAllocation, Option.map_none] at hErase
              simp only [projectWorld] at hErase
              simp only [List.map_cons, List.map_nil, project_retryMachine]
              rw [← hErase]
              cases keepReceipts <;> rfl
          | some result =>
              rcases result with ⟨nextWorld, nextCell⟩
              simp only
              simp only [hAllocation, Option.map_some] at hErase
              simp only [projectWorld] at hErase
              simp only [List.map_cons, List.map_nil, project_finished]
              rw [← hErase]
              cases keepReceipts <;> rfl
      | resample source resume =>
          simp only
          generalize hSource :
            world.heap.lookup source = sourceLookup
          cases sourceLookup with
          | none =>
              simp only
              simp only [List.map_cons, List.map_nil, project_retryMachine]
              cases keepReceipts <;> rfl
          | some sourceRecord =>
              simp only
              generalize hAllocation :
                world.allocate? sourceRecord.origin
                  (source.generation + 1) = allocation
              have hErase := projectWorld_allocate? (keepReceipts := keepReceipts) world sourceRecord.origin
                (source.generation + 1)
              cases allocation with
              | none =>
                  simp only
                  simp only [hAllocation, Option.map_none] at hErase
                  simp only [projectWorld] at hErase
                  simp only [List.map_cons, List.map_nil,
                    project_retryMachine]
                  rw [← hErase]
                  cases keepReceipts <;> rfl
              | some result =>
                  rcases result with ⟨nextWorld, nextCell⟩
                  simp only
                  simp only [hAllocation, Option.map_some] at hErase
                  simp only [projectWorld] at hErase
                  simp only [List.map_cons, List.map_nil, project_finished]
                  rw [← hErase]
                  cases keepReceipts <;> rfl
      | perform effect next =>
          simp only [List.map_cons, List.map_nil, project_finished,
            project_recorded]
          cases keepReceipts <;> rfl
  | returned outcome stack =>
      simp only [NeedReference.step, step, projectMachine, projectWorld]
      cases stack with
      | nil =>
          simp only [List.map_cons, List.map_nil, project_finished]
          cases keepReceipts <;> rfl
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [List.map_cons, List.map_nil, project_finished]
              cases keepReceipts <;> rfl
          | commit cell owner =>
              generalize hLookup :
                world.heap.lookup cell = lookup
              cases lookup with
              | none =>
                  simp only [hLookup, List.map_cons, List.map_nil,
                    project_retryMachine]
                  cases keepReceipts <;> rfl
              | some record =>
                  simp only [hLookup]
                  cases hCache : record.cache with
                  | suspended =>
                      simp only
                      simp only [List.map_cons, List.map_nil,
                        project_retryMachine]
                      cases keepReceipts <;> rfl
                  | value value =>
                      simp only
                      simp only [List.map_cons, List.map_nil,
                        project_retryMachine]
                      cases keepReceipts <;> rfl
                  | stableFault fault =>
                      simp only
                      simp only [List.map_cons, List.map_nil,
                        project_retryMachine]
                      cases keepReceipts <;> rfl
                  | evaluating actual =>
                      simp only
                      by_cases hOwner : actual = owner
                      · simp only [hOwner]
                        cases outcome with
                        | value value =>
                            cases keepReceipts <;> rfl
                        | stableFault fault =>
                            cases keepReceipts <;> rfl
                        | retryableFault reason =>
                            cases keepReceipts <;> rfl
                      · simp only [hOwner]
                        cases keepReceipts <;> rfl

/-- A halted core state remains in a bounded frontier. -/
def advance
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    List
      (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :=
  match step spec machine with
  | [] => [machine]
  | next => next

def isHalted
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    Bool :=
  match machine.control with
  | .halted _ => true
  | _ => false

def runFrontier
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat →
      List
        (CoreMachine Origin Local Resume Rule Value StableFault
          RetryableFault Effect) →
      List
        (CoreMachine Origin Local Resume Rule Value StableFault
          RetryableFault Effect)
  | 0, states => states
  | fuel + 1, states =>
      if states.all isHalted then
        states
      else
        runFrontier spec fuel (states.flatMap (advance spec))

def haltedOutcome
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    Option (Produced Value StableFault RetryableFault) :=
  match machine.control with
  | .halted outcome => some outcome
  | _ => none

def answers
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    List (Produced Value StableFault RetryableFault) :=
  (runFrontier spec fuel [machine]).filterMap haltedOutcome

@[simp] theorem isHalted_project
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    isHalted ((projectMachine keepReceipts) machine) =
      NeedReference.isHalted machine := by
  rcases machine with ⟨world, control, work⟩
  cases control <;> rfl

@[simp] theorem haltedOutcome_project
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    haltedOutcome ((projectMachine keepReceipts) machine) =
      NeedReference.haltedOutcome machine := by
  rcases machine with ⟨world, control, work⟩
  cases control <;> rfl

/-- Projection commutes with keeping a halted state in the frontier. -/
theorem project_advance_commutes
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    (NeedReference.advance spec machine).map (projectMachine keepReceipts) =
      advance spec ((projectMachine keepReceipts) machine) := by
  unfold NeedReference.advance advance
  rw [← project_step_commutes]
  cases NeedReference.step spec machine <;> rfl

private theorem flatMap_project_advance_commutes
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (states :
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)) :
    (states.flatMap (NeedReference.advance spec)).map (projectMachine keepReceipts) =
      (states.map (projectMachine keepReceipts)).flatMap (advance spec) := by
  induction states with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        project_advance_commutes, ih]

private theorem all_isHalted_project
    (states :
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)) :
    (states.map (projectMachine keepReceipts)).all isHalted =
      states.all NeedReference.isHalted := by
  induction states with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.all_cons, isHalted_project, ih]

/-- Exact bounded-run correspondence.  The theorem preserves frontier order,
world multiplicity, duplicate alternatives, cache state, and work counters. -/
theorem project_runFrontier_commutes
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (states :
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)) :
    (NeedReference.runFrontier spec fuel states).map (projectMachine keepReceipts) =
      runFrontier spec fuel (states.map (projectMachine keepReceipts)) := by
  induction fuel generalizing states with
  | zero => rfl
  | succ fuel ih =>
      simp only [NeedReference.runFrontier, runFrontier]
      rw [all_isHalted_project]
      split
      · rfl
      · rw [← flatMap_project_advance_commutes]
        exact ih (states.flatMap (NeedReference.advance spec))

/-- Recording preserves the entire bounded frontier, including unfinished
configurations, causal graphs, branch paths and exact work accounts. -/
theorem recording_runFrontier_readback
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (runFrontier spec fuel (states.map (projectMachine true))).mapM CoreMachine.readback? =
      some (NeedReference.runFrontier spec fuel states) := by
  rw [← project_runFrontier_commutes]
  generalize NeedReference.runFrontier spec fuel states = final
  induction final with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem filterMap_haltedOutcome_project
    (states :
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)) :
    (states.map (projectMachine keepReceipts)).filterMap haltedOutcome =
      states.filterMap NeedReference.haltedOutcome := by
  induction states with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.filterMap_cons, haltedOutcome_project, ih]

/-- Both receipt modes preserve the ordered bounded answer list. -/
theorem project_answers_commute
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    answers spec fuel ((projectMachine keepReceipts) machine) =
      NeedReference.answers spec fuel machine := by
  unfold answers NeedReference.answers
  change
    (runFrontier spec fuel ([machine].map (projectMachine keepReceipts))).filterMap
        haltedOutcome =
      (NeedReference.runFrontier spec fuel [machine]).filterMap
        NeedReference.haltedOutcome
  rw [← project_runFrontier_commutes]
  exact filterMap_haltedOutcome_project
    (NeedReference.runFrontier spec fuel [machine])

/-- Receipt retention refines what can be inspected, while leaving the bounded
answer observer unchanged. This is not a physical-cost comparison. -/
theorem recording_answers_eq_erased
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    answers spec fuel (projectMachine true machine) = answers spec fuel (eraseMachine machine) := by
  rw [project_answers_commute, project_answers_commute]

@[simp] theorem isHalted_erase
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    isHalted (eraseMachine machine) = NeedReference.isHalted machine :=
  isHalted_project machine

@[simp] theorem haltedOutcome_erase
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    haltedOutcome (eraseMachine machine) = NeedReference.haltedOutcome machine :=
  haltedOutcome_project machine

/-- The answer-only specialization keeps the original public contract. -/
theorem step_commutes
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (NeedReference.step spec machine).map eraseMachine = step spec (eraseMachine machine) :=
  project_step_commutes spec machine

theorem advance_commutes
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (NeedReference.advance spec machine).map eraseMachine = advance spec (eraseMachine machine) :=
  project_advance_commutes spec machine

theorem runFrontier_commutes
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (NeedReference.runFrontier spec fuel states).map eraseMachine =
      runFrontier spec fuel (states.map eraseMachine) :=
  project_runFrontier_commutes spec fuel states

theorem answers_commute
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    answers spec fuel (eraseMachine machine) = NeedReference.answers spec fuel machine :=
  project_answers_commute spec fuel machine

/-- Forward simulation from the rich reference machine. -/
theorem rich_step_sound
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (hNext : next ∈ NeedReference.step spec machine) :
    eraseMachine next ∈ step spec (eraseMachine machine) := by
  rw [← step_commutes spec machine]
  exact List.mem_map.mpr ⟨next, hNext, rfl⟩

/-- Backward lifting: every answer-only successor is the erasure of a rich
successor.  Thus the execution machine cannot invent an unreceipted branch. -/
theorem core_step_lifts
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {next :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (hNext : next ∈ step spec (eraseMachine machine)) :
    ∃ richNext ∈ NeedReference.step spec machine,
      eraseMachine richNext = next := by
  rw [← step_commutes spec machine] at hNext
  rcases List.mem_map.mp hNext with ⟨richNext, hRich, hErase⟩
  exact ⟨richNext, hRich, hErase⟩

end Dynamics

end Mettapedia.Machines.BranchLocalNeed.NeedExecution
