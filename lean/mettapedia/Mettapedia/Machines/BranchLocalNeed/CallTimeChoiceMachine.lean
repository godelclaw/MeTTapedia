import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mettapedia.Machines.BranchLocalNeed.ReturningRuns

/-!
# The core calculus on the reference Need machine

This module instantiates the unchanged reference machine `NeedReference` with
the core calculus of `CallTimeChoiceSpec`. Cells are the machine's own cells
(`CellId`): a cell's origin is a computation with its environment.

* A memoized suspension `need m` allocates a cell with origin `m`; forcing it
  is the machine's `demand`, which branches over the origin's alternatives the
  first time and reads the cache afterwards, in that branch only.
* An ordinary suspension `delay m` allocates a cell that is never demanded;
  forcing it is the machine's `resample`, which allocates a fresh cell of the
  next generation with the same origin and demands that one.
* Sequencing and calls allocate a private cell for the computation and demand
  it, so that the machine's resume frames carry the continuation.
* The alternatives of an origin are its first-level choices: the two sides of
  `choose`, the candidate equations of `call`, the selected equation of
  `callRule`, and otherwise the computation itself.
* `emit` is the machine's `perform`; the event goes into the receipt graph.
* `quote m` allocates a cell with origin `m` and returns the code value naming
  it; activating a code value is the machine's `resample` of that cell, so
  every activation runs the quoted computation afresh.
* A primitive is applied to the values it is given.

No machine rule is added or changed: every transition is
`NeedReference.step (machineSpec P)`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference

/-- Values on the machine: cells are machine cells. -/
abbrev MVal := Val CellId
abbrev MEnv := List MVal

/-- Domain failures of the instance. `fail` is the source language's failure;
`invalid` marks a continuation applied to an outcome it does not expect. -/
inductive MFault where
  | fail
  | invalid
  deriving DecidableEq, Repr

/-- Rule labels recorded in receipts. -/
inductive MRule where
  | builtin
  | left
  | right
  | equation
  deriving DecidableEq, Repr

/-- Resume tokens: the continuation data of a frame. -/
inductive MResume where
  | seqAlloc (rest : Comp) (env : MEnv)
  | seqRet (rest : Comp) (env : MEnv)
  | needAlloc (body : Comp) (env : MEnv)
  | delayAlloc (body : Comp) (env : MEnv)
  | forceRet
  | resampleAlloc
  | callAlloc
  | callRet
  | quoteAlloc
  deriving DecidableEq, Repr

abbrev MOutcome := Produced MVal Empty MFault

/-- Local states: each exposes exactly one machine action. -/
inductive MLocal where
  | output (outcome : MOutcome)
  | alloc (origin : Comp × MEnv) (k : MResume)
  | demand (cell : CellId) (k : MResume)
  | resample (cell : CellId) (k : MResume)
  | emit (event : Nat) (next : MLocal)
  deriving DecidableEq, Repr

/-- Force a value: demand a memoized cell, resample an ordinary one, or return
a weak head normal form. -/
def forceLocal : MVal → MLocal
  | .need c => .demand c .forceRet
  | .thunk c => .resample c .resampleAlloc
  | .sym c => .output (.value (.sym c))
  | .app f x => .output (.value (.app f x))
  | .code c => .output (.value (.code c))

/-- Execute a value as code: a code value is run afresh by resampling its cell;
any other value is left as the residual `unquoteHead v`. -/
def runLocal : MVal → MLocal
  | .code c => .resample c .resampleAlloc
  | .sym c => .output (.value (.app (.sym unquoteHead) (.sym c)))
  | .app f x => .output (.value (.app (.sym unquoteHead) (.app f x)))
  | .need c => .output (.value (.app (.sym unquoteHead) (.need c)))
  | .thunk c => .output (.value (.app (.sym unquoteHead) (.thunk c)))

/-- The machine outcome of a primitive application. -/
def primLocal (op : Prim) (vs : List MVal) : MLocal :=
  match op.apply vs with
  | some v => .output (.value v)
  | none => .output (.retryableFault (.domain .fail))

/-- Enter a computation: matching is decided here; every other construct
becomes a machine action. -/
def enter : Comp → MEnv → MLocal
  | .ret v, ρ => .output (.value (v.eval ρ))
  | .seq m n, ρ => .alloc (m, ρ) (.seqAlloc n ρ)
  | .need m n, ρ => .alloc (m, ρ) (.needAlloc n ρ)
  | .delay m n, ρ => .alloc (m, ρ) (.delayAlloc n ρ)
  | .force v, ρ => forceLocal (v.eval ρ)
  | .caseCon v c k hit miss, ρ =>
      match (v.eval ρ).matchCon c k with
      | some args => enter hit (args ++ ρ)
      | none => enter miss ρ
  | .caseApp v hit miss, ρ =>
      match (v.eval ρ).matchApp with
      | some (f, x) => enter hit (f :: x :: ρ)
      | none => enter miss ρ
  | .call f args, ρ => .alloc (.call f args, ρ) .callAlloc
  | .callRule i args, ρ => .alloc (.callRule i args, ρ) .callAlloc
  | .choose m n, ρ => .alloc (.choose m n, ρ) .callAlloc
  | .fail, _ => .output (.retryableFault (.domain .fail))
  | .emit e m, ρ => .emit e (enter m ρ)
  | .quote m, ρ => .alloc (m, ρ) .quoteAlloc
  | .run v, ρ => runLocal (v.eval ρ)
  | .prim op args, ρ => primLocal op (args.map (·.eval ρ))

def action : MLocal → Action (Comp × MEnv) MLocal MResume MVal Empty MFault Nat
  | .output o => .done o
  | .alloc o k => .allocate o k
  | .demand c k => .demand c k
  | .resample c k => .resample c k
  | .emit e next => .perform e next

def afterDemand : MResume → MOutcome → MLocal
  | .seqRet n ρ, .value w => enter n (w :: ρ)
  | .seqRet _ _, o => .output o
  | .forceRet, .value w => forceLocal w
  | .forceRet, o => .output o
  | .callRet, o => .output o
  | _, _ => .output (.retryableFault (.domain .invalid))

def afterAllocation : MResume → CellId → MLocal
  | .seqAlloc n ρ, c => .demand c (.seqRet n ρ)
  | .needAlloc n ρ, c => enter n (.need c :: ρ)
  | .delayAlloc n ρ, c => enter n (.thunk c :: ρ)
  | .resampleAlloc, c => .demand c .forceRet
  | .callAlloc, c => .demand c .callRet
  | .quoteAlloc, c => .output (.value (.code c))
  | _, _ => .output (.retryableFault (.domain .invalid))

/-- The first-level alternatives of an origin. -/
def alternatives (P : Program) : Comp × MEnv → List (MRule × MLocal)
  | (.choose m n, ρ) => [(.left, enter m ρ), (.right, enter n ρ)]
  | (.call f args, ρ) =>
      (candidates P f args.length).map fun r => (.equation, enter r.body (args.map (·.eval ρ)))
  | (.callRule i args, ρ) =>
      match P[i]? with
      | some r =>
          if r.arity = args.length then [(.equation, enter r.body (args.map (·.eval ρ)))]
          else []
      | none => []
  | (.ret v, ρ) => [(.builtin, enter (.ret v) ρ)]
  | (.seq m n, ρ) => [(.builtin, enter (.seq m n) ρ)]
  | (.need m n, ρ) => [(.builtin, enter (.need m n) ρ)]
  | (.delay m n, ρ) => [(.builtin, enter (.delay m n) ρ)]
  | (.force v, ρ) => [(.builtin, enter (.force v) ρ)]
  | (.caseCon v c k hit miss, ρ) => [(.builtin, enter (.caseCon v c k hit miss) ρ)]
  | (.caseApp v hit miss, ρ) => [(.builtin, enter (.caseApp v hit miss) ρ)]
  | (.fail, ρ) => [(.builtin, enter .fail ρ)]
  | (.emit e m, ρ) => [(.builtin, enter (.emit e m) ρ)]
  | (.quote m, ρ) => [(.builtin, enter (.quote m) ρ)]
  | (.run v, ρ) => [(.builtin, enter (.run v) ρ)]
  | (.prim op args, ρ) => [(.builtin, enter (.prim op args) ρ)]

/-- The instance of the reference machine. -/
def machineSpec (P : Program) :
    Spec (Comp × MEnv) MLocal MResume MRule MVal Empty MFault Nat where
  alternatives := alternatives P
  action := action
  afterDemand := afterDemand
  afterAllocation := afterAllocation

abbrev MWorld := World (Comp × MEnv) MRule MVal Empty MFault Nat
abbrev MMachine := Machine (Comp × MEnv) MLocal MResume MRule MVal Empty MFault Nat

def initialWorld : MWorld where
  lineage := 0
  path := []
  heap := Heap.empty
  receipts := ReceiptGraph.empty
  nextCell := 0
  nextEvaluator := 0

/-- Run a closed computation from the empty heap. -/
def initialMachine (M : Comp) : MMachine where
  world := initialWorld
  control := .run (enter M []) []

/-- The machine's answers for the observation of a closed computation. -/
def machineAnswers (P : Program) (fuel : Nat) (M : Comp) : List MOutcome :=
  answers (machineSpec (observed P)) fuel (initialMachine (observe M))

/-- Machine values of a machine answer list. -/
def machineValues (os : List MOutcome) : List MVal :=
  os.filterMap fun o =>
    match o with
    | .value w => some w
    | _ => none

/-- A completed outcome together with the branch's chronological emissions. -/
def haltedObservation (machine : MMachine) : Option (MOutcome × List Nat) :=
  (haltedOutcome machine).map fun outcome => (outcome, machine.world.receipts.effects)

/-- Observe the same frontier as `machineAnswers`, retaining each answer's
emitted events. Pending branches are not reported as completed observations. -/
def machineObservations (P : Program) (fuel : Nat) (M : Comp) :
    List (MOutcome × List Nat) :=
  (runFrontier (machineSpec (observed P)) fuel [initialMachine (observe M)]).filterMap
    haltedObservation

/-- Forgetting emitted events recovers the existing answer observer. -/
theorem machineObservations_erase (P : Program) (fuel : Nat) (M : Comp) :
    (machineObservations P fuel M).map Prod.fst = machineAnswers P fuel M := by
  unfold machineObservations machineAnswers answers
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro machine _
  simp [haltedObservation, Function.comp_def]

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
