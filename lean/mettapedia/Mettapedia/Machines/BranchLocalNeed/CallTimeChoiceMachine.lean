import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mettapedia.Machines.BranchLocalNeed.ReturningRuns
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.BranchLocalNeed.AllocationBound
import Mettapedia.Machines.BranchLocalNeed.Representation

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

/-! ## Captured references of active controls and saved continuations -/

/-- Only the environment-bearing continuation forms capture value references. -/
def MResume.referencesSatisfy (p : CellId → Prop) : MResume → Prop
  | .seqAlloc _ env | .seqRet _ env | .needAlloc _ env | .delayAlloc _ env =>
      EnvReferencesSatisfy p env
  | _ => True

def MLocal.referencesSatisfy (p : CellId → Prop) : MLocal → Prop
  | .output (.value value) => value.referencesSatisfy p
  | .output _ => True
  | .alloc origin token => EnvReferencesSatisfy p origin.2 ∧ token.referencesSatisfy p
  | .demand cell token | .resample cell token => p cell ∧ token.referencesSatisfy p
  | .emit _ next => next.referencesSatisfy p

theorem MResume.referencesSatisfy_mono {p q : CellId → Prop}
    (grows : ∀ c, p c → q c) {token : MResume} (valid : token.referencesSatisfy p) :
    token.referencesSatisfy q := by
  cases token <;> first | exact valid.mono grows | trivial

theorem MLocal.referencesSatisfy_mono {p q : CellId → Prop}
    (grows : ∀ c, p c → q c) {state : MLocal} (valid : state.referencesSatisfy p) :
    state.referencesSatisfy q := by
  induction state with
  | output result =>
      cases result with
      | value v => exact v.referencesSatisfy_mono grows valid
      | stableFault => trivial
      | retryableFault => trivial
  | alloc origin token => exact ⟨valid.1.mono grows, token.referencesSatisfy_mono grows valid.2⟩
  | demand c token | resample c token =>
      exact ⟨grows c valid.1, token.referencesSatisfy_mono grows valid.2⟩
  | emit event next ih => exact ih valid

theorem forceLocal_referencesSatisfy {p : CellId → Prop} {value : MVal}
    (valid : value.referencesSatisfy p) : (forceLocal value).referencesSatisfy p := by
  cases value <;> simp_all [forceLocal, MLocal.referencesSatisfy, MResume.referencesSatisfy,
    Val.referencesSatisfy]

theorem runLocal_referencesSatisfy {p : CellId → Prop} {value : MVal}
    (valid : value.referencesSatisfy p) : (runLocal value).referencesSatisfy p := by
  cases value <;> simp_all [runLocal, MLocal.referencesSatisfy, MResume.referencesSatisfy,
    Val.referencesSatisfy]

theorem primLocal_referencesSatisfy (p : CellId → Prop) (op : Prim) (values : List MVal) :
    (primLocal op values).referencesSatisfy p := by
  cases op
  cases values with
  | nil => trivial
  | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second tail =>
          cases tail <;> simp [primLocal, Prim.apply, MLocal.referencesSatisfy, Val.referencesSatisfy]

/-- Entering arbitrary nested syntax cannot manufacture a cell reference.
Constructor destructuring reuses the common value-reference lemmas. -/
theorem enter_referencesSatisfy {p : CellId → Prop} (code : Comp) {env : MEnv}
    (valid : EnvReferencesSatisfy p env) : (enter code env).referencesSatisfy p := by
  induction code generalizing env with
  | ret value => exact value.eval_referencesSatisfy valid
  | seq first rest _ _ => exact ⟨valid, valid⟩
  | need producer body _ _ => exact ⟨valid, valid⟩
  | delay producer body _ _ => exact ⟨valid, valid⟩
  | force value => exact forceLocal_referencesSatisfy (value.eval_referencesSatisfy valid)
  | caseCon value name arity hit miss ihHit ihMiss =>
      simp only [enter]
      cases matched : (value.eval env).matchCon name arity with
      | none => exact ihMiss valid
      | some fields =>
          exact ihHit
            ((Val.matchCon_referencesSatisfy (value.eval_referencesSatisfy valid) matched).append valid)
  | caseApp value hit miss ihHit ihMiss =>
      simp only [enter]
      cases matched : (value.eval env).matchApp with
      | none => exact ihMiss valid
      | some pair =>
          rcases pair with ⟨head, argument⟩
          have fields := Val.matchApp_referencesSatisfy (value.eval_referencesSatisfy valid) matched
          exact ihHit (EnvReferencesSatisfy.cons fields.1 (EnvReferencesSatisfy.cons fields.2 valid))
  | call function args => exact ⟨valid, True.intro⟩
  | callRule rule args => exact ⟨valid, True.intro⟩
  | choose first second _ _ => exact ⟨valid, True.intro⟩
  | fail => trivial
  | emit event body ih => exact ih valid
  | quote body _ => exact ⟨valid, True.intro⟩
  | run value => exact runLocal_referencesSatisfy (value.eval_referencesSatisfy valid)
  | prim op args => exact primLocal_referencesSatisfy p op _

theorem afterDemand_referencesSatisfy {p : CellId → Prop} {token : MResume} {result : MOutcome}
    (saved : token.referencesSatisfy p)
    (returned : match result with | .value v => v.referencesSatisfy p | _ => True) :
    (afterDemand token result).referencesSatisfy p := by
  cases token with
  | seqRet code env =>
      cases result with
      | value v => exact enter_referencesSatisfy code (EnvReferencesSatisfy.cons returned saved)
      | stableFault => trivial
      | retryableFault => trivial
  | forceRet =>
      cases result with
      | value v => exact forceLocal_referencesSatisfy returned
      | stableFault => trivial
      | retryableFault => trivial
  | callRet => cases result <;> exact returned
  | seqAlloc | needAlloc | delayAlloc | resampleAlloc | callAlloc | quoteAlloc => trivial

theorem afterAllocation_referencesSatisfy {p : CellId → Prop} {token : MResume} {cell : CellId}
    (saved : token.referencesSatisfy p) (allocated : p cell) :
    (afterAllocation token cell).referencesSatisfy p := by
  cases token with
  | seqAlloc code env => exact ⟨allocated, saved⟩
  | needAlloc code env => exact enter_referencesSatisfy code (EnvReferencesSatisfy.cons allocated saved)
  | delayAlloc code env => exact enter_referencesSatisfy code (EnvReferencesSatisfy.cons allocated saved)
  | resampleAlloc | callAlloc => exact ⟨allocated, True.intro⟩
  | quoteAlloc => exact allocated
  | seqRet | forceRet | callRet => trivial

theorem alternatives_referencesSatisfy (P : Program) {p : CellId → Prop} {origin : Comp × MEnv}
    (captured : EnvReferencesSatisfy p origin.2) {rule : MRule} {state : MLocal}
    (member : (rule, state) ∈ alternatives P origin) : state.referencesSatisfy p := by
  rcases origin with ⟨code, env⟩
  cases code with
  | choose first second =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact enter_referencesSatisfy first captured
      · cases List.mem_singleton.mp member
        exact enter_referencesSatisfy second captured
  | call function args =>
      obtain ⟨candidate, _, equal⟩ := List.mem_map.mp member
      cases equal
      exact enter_referencesSatisfy _ (VExp.evalList_referencesSatisfy captured args)
  | callRule index args =>
      simp only [alternatives] at member
      cases selected : P[index]? with
      | none => simp [selected] at member
      | some equation =>
          simp only [selected] at member
          split at member
          · cases List.mem_singleton.mp member
            exact enter_referencesSatisfy _ (VExp.evalList_referencesSatisfy captured args)
          · simp at member
  | ret | seq | need | delay | force | caseCon | caseApp | fail | emit | quote | run | prim =>
      simp only [alternatives, List.mem_singleton] at member
      cases member
      exact enter_referencesSatisfy _ captured

/-- Strong references captured by a continuation token. -/
def MResume.referenceSet : MResume → Finset CellId
  | .seqAlloc _ env | .seqRet _ env | .needAlloc _ env | .delayAlloc _ env => envReferenceSet env
  | _ => ∅

theorem MResume.referencesSatisfy_iff_referenceSet (p : CellId → Prop) (token : MResume) :
    token.referencesSatisfy p ↔ ∀ cell ∈ token.referenceSet, p cell := by
  cases token <;> simp [MResume.referencesSatisfy, MResume.referenceSet,
    EnvReferencesSatisfy_iff_referenceSet]

/-- The active local state's captured origins, outcomes and saved token. -/
def MLocal.referenceSet : MLocal → Finset CellId
  | .output (.value value) => value.referenceSet
  | .output _ => ∅
  | .alloc origin token => envReferenceSet origin.2 ∪ token.referenceSet
  | .demand cell token | .resample cell token => insert cell token.referenceSet
  | .emit _ next => next.referenceSet

theorem MLocal.referencesSatisfy_iff_referenceSet (p : CellId → Prop) (state : MLocal) :
    state.referencesSatisfy p ↔ ∀ cell ∈ state.referenceSet, p cell := by
  induction state with
  | output result =>
      cases result <;> simp [MLocal.referencesSatisfy, MLocal.referenceSet,
        Val.referencesSatisfy_iff_referenceSet]
  | alloc origin token =>
      simp [MLocal.referencesSatisfy, MLocal.referenceSet, EnvReferencesSatisfy_iff_referenceSet,
        MResume.referencesSatisfy_iff_referenceSet, or_imp, forall_and]
  | demand cell token | resample cell token =>
      simp [MLocal.referencesSatisfy, MLocal.referenceSet,
        MResume.referencesSatisfy_iff_referenceSet, or_imp, forall_and]
  | emit event next ih => exact ih

/-- A constructed instance of the general reference discipline. It checks
language operations for every domain, without assuming a machine invariant. -/
def machineReferenceDiscipline (P : Program) : NeedCacheLaws.ReferenceDiscipline (machineSpec P) where
  origin p source := EnvReferencesSatisfy p source.2
  localState := MLocal.referencesSatisfy
  resume := MResume.referencesSatisfy
  value p v := v.referencesSatisfy p
  origin_mono := by
    intro p q grows source valid
    exact valid.mono grows
  local_mono := MLocal.referencesSatisfy_mono
  resume_mono := MResume.referencesSatisfy_mono
  value_mono := Val.referencesSatisfy_mono
  alternatives := by
    intro p source rule state captured member
    exact alternatives_referencesSatisfy P (p := p) (origin := source)
      (rule := rule) (state := state) captured member
  action := by
    intro p state valid
    cases state with
    | output result => cases result <;> exact valid
    | alloc | demand | resample | emit => exact valid
  afterDemand := by
    intro p token result saved returned
    cases result with
    | value v => exact afterDemand_referencesSatisfy saved returned
    | stableFault fault => exact fault.elim
    | retryableFault reason => exact afterDemand_referencesSatisfy saved True.intro
  afterAllocation := by
    intro p token cell saved allocated
    exact afterAllocation_referencesSatisfy saved allocated

/-- The language's validated finite inventories instantiate the shared
heap and continuation assembly. The stored payload keeps all source roles. -/
def machineReferenceInventory (P : Program) :
    NeedCacheLaws.ReferenceInventory (machineReferenceDiscipline P) where
  origin source := envReferenceSet source.2
  localState := MLocal.referenceSet
  resume := MResume.referenceSet
  value := Val.referenceSet
  origin_exact := by
    intro p source
    exact EnvReferencesSatisfy_iff_referenceSet p source.2
  local_exact := MLocal.referencesSatisfy_iff_referenceSet
  resume_exact := MResume.referencesSatisfy_iff_referenceSet
  value_exact := Val.referencesSatisfy_iff_referenceSet

/-- Run a closed computation from the empty heap. -/
def initialMachine (M : Comp) : MMachine where
  world := initialWorld
  control := .run (enter M []) []

/-- Every bounded point of a closed computation has an exact ordered
full-cell history image. Pending controls, effects and duplicates survive
the round trip; reconstruction itself does not execute any producer. -/
theorem runFrontier_fullHistory_readback (P : Program) (code : Comp) (fuel : Nat) :
    ∃ views,
      (runFrontier (machineSpec P) fuel [initialMachine code]).mapM
        Machine.fullHistoryView? = some views ∧
      views.mapM Machine.ofFullHistoryView? =
        some (runFrontier (machineSpec P) fuel [initialMachine code]) := by
  apply Machine.runFrontier_fullHistory_frontier_readback
  intro machine member
  simp only [List.mem_singleton] at member
  subst machine
  exact ⟨Heap.empty_recorded, Heap.empty_historyEncodable⟩

theorem initialMachine_referencesClosed (P : Program) (code : Comp) :
    (machineReferenceDiscipline P).machineClosed (initialMachine code) := by
  constructor
  · intro cell record lookup
    simp [initialMachine, initialWorld, Heap.empty, Heap.lookup] at lookup
  · change MLocal.referencesSatisfy (NeedCacheLaws.heapLive (Heap.empty : Heap (Comp × MEnv) MVal Empty))
        (enter code []) ∧
        (machineReferenceDiscipline P).stack (NeedCacheLaws.heapLive Heap.empty) []
    exact ⟨enter_referencesSatisfy code (env := []) (by intro value member; cases member),
      by intro frame member; cases member⟩

/-- Every paused frontier of a closed program retains all captured, cached,
active and continuation references in each branch's own world. -/
theorem runFrontier_referencesClosed (P : Program) (code : Comp) (fuel : Nat) {machine : MMachine}
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code]) :
    (machineReferenceDiscipline P).machineClosed machine := by
  apply (machineReferenceDiscipline P).runFrontier_closed fuel (member := member)
  intro initial selected
  cases List.mem_singleton.mp selected
  exact initialMachine_referencesClosed P code

/-- Every real frontier retains an exact finite heap history. -/
theorem runFrontier_heapRecorded (P : Program) (code : Comp) (fuel : Nat) {machine : MMachine}
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code]) :
    machine.world.heap.Recorded := by
  apply NeedFrontierLaws.runFrontier_preserves (machineSpec P)
    (fun candidate => candidate.world.heap.Recorded) (fuel := fuel) (member := member)
  · intro before after valid stepped
    exact step_heap_recorded (machineSpec P) before after valid stepped
  · intro initial selected
    cases List.mem_singleton.mp selected
    exact Heap.empty_recorded

/-- The independently recorded allocation receipts and heap history agree
at every actual frontier, including pauses and inherited sibling prefixes. -/
theorem runFrontier_allocationReceiptsExact (P : Program) (code : Comp) (fuel : Nat)
    {machine : MMachine}
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code]) :
    machine.world.AllocationReceiptsExact := by
  apply NeedFrontierLaws.runFrontier_preserves (machineSpec P)
    (fun candidate => candidate.world.AllocationReceiptsExact) (fuel := fuel) (member := member)
  · intro before after valid stepped
    exact step_allocationReceiptsExact (machineSpec P) before after valid stepped
  · intro initial selected
    cases List.mem_singleton.mp selected
    rfl

theorem runFrontier_slotBound (P : Program) (code : Comp) (fuel : Nat) {machine : MMachine}
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code]) :
    NeedAllocationBound.SlotBound machine.world := by
  apply NeedFrontierLaws.runFrontier_preserves (machineSpec P)
    (fun candidate => NeedAllocationBound.SlotBound candidate.world) (fuel := fuel) (member := member)
  · intro before after bounded stepped
    exact NeedAllocationBound.step_slotBound (machineSpec P) before after bounded stepped
  · intro initial selected
    cases List.mem_singleton.mp selected
    exact NeedAllocationBound.SlotBound.of_empty _ rfl

/-- A collected actual frontier uses the common operational root census.
Receipt-target inspection requires its stronger archive retention policy. -/
def collectedFrontierMachine {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) : MMachine :=
  (machineReferenceInventory P).collectMachine owner machine
    (runFrontier_heapRecorded P code fuel member)
    (runFrontier_referencesClosed P code fuel member) weight

theorem collectedFrontierMachine_valid {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    let collected := collectedFrontierMachine owner P code fuel machine member weight
    collected.world.heap.Recorded ∧
      (machineReferenceDiscipline P).machineClosed collected ∧
      NeedAllocationBound.SlotBound collected.world :=
  ⟨(machineReferenceInventory P).collectMachine_recorded owner machine
      (runFrontier_heapRecorded P code fuel member)
      (runFrontier_referencesClosed P code fuel member) weight,
    (machineReferenceInventory P).collectMachine_closed owner machine
      (runFrontier_heapRecorded P code fuel member)
      (runFrontier_referencesClosed P code fuel member) weight,
    NeedAllocationBound.collectMachine_slotBound (machineReferenceInventory P) owner machine
      (runFrontier_heapRecorded P code fuel member)
      (runFrontier_referencesClosed P code fuel member) weight
      (runFrontier_slotBound P code fuel member)⟩

/-- The common finite resource heap is constructed for an arbitrary paused
frontier of the actual instance. It preserves complete captured origins and
cache payloads; its outgoing edges are the validated language inventory. -/
def frontierResourceHeap (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    Mettapedia.Machines.ResourceOwnership.Heap CellId (CellRecord (Comp × MEnv) MVal Empty) :=
  (machineReferenceInventory P).resourceHeap machine.world.heap
    (runFrontier_heapRecorded P code fuel member)
    (runFrontier_referencesClosed P code fuel member).1 weight

/-- Roots captured by the current control and continuation exist in the same
frontier's resource heap. No validity premise is supplied by the caller. -/
theorem frontier_controlRoots_valid {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    Mettapedia.Machines.ResourceOwnership.ValidRoots
      (frontierResourceHeap P code fuel machine member weight)
      ((machineReferenceInventory P).controlRoots owner machine.control) :=
  (machineReferenceInventory P).controlRoots_valid owner machine
    (runFrontier_heapRecorded P code fuel member)
    (runFrontier_referencesClosed P code fuel member) weight

/-- The existing executable resource census agrees with inductive reachability
for every actual frontier, including captured code and suspended fields. -/
theorem frontier_cell_census_exact {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) (cell : CellId) :
    cell ∈ Mettapedia.Machines.ResourceOwnership.census
        (frontierResourceHeap P code fuel machine member weight)
        ((machineReferenceInventory P).controlRoots owner machine.control) ↔
      Mettapedia.Machines.ResourceOwnership.Live
        (frontierResourceHeap P code fuel machine member weight)
        ((machineReferenceInventory P).controlRoots owner machine.control) cell :=
  (machineReferenceInventory P).control_census_exact owner machine
    (runFrontier_heapRecorded P code fuel member)
    (runFrontier_referencesClosed P code fuel member) weight cell

/-- Following every allocation receipt to its current cell requires the full
recorded heap. The root set is read from receipt nodes, independently of the
heap allocation census, and their equality is earned by actual transitions. -/
theorem frontier_allocationRoots_eq_snapshotRoots {Owner : Type*} [DecidableEq Owner]
    (owner : Owner) (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    machine.world.receipts.allocationRoots owner =
      (frontierResourceHeap P code fuel machine member weight).snapshotRoots owner := by
  change machine.world.receipts.allocationCells.image (fun cell => (owner, cell)) =
    machine.world.heap.allocated.image (fun cell => (owner, cell))
  rw [runFrontier_allocationReceiptsExact P code fuel member]

theorem frontier_allocationRoots_valid {Owner : Type*} [DecidableEq Owner]
    (owner : Owner) (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    Mettapedia.Machines.ResourceOwnership.ValidRoots
      (frontierResourceHeap P code fuel machine member weight)
      (machine.world.receipts.allocationRoots owner) := by
  rw [frontier_allocationRoots_eq_snapshotRoots owner P code fuel machine member weight]
  exact Mettapedia.Machines.ResourceOwnership.Heap.snapshotRoots_valid _ owner

theorem frontier_allocation_census {Owner : Type*} [DecidableEq Owner]
    (owner : Owner) (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    Mettapedia.Machines.ResourceOwnership.census
      (frontierResourceHeap P code fuel machine member weight)
      (machine.world.receipts.allocationRoots owner) = machine.world.heap.allocated := by
  rw [frontier_allocationRoots_eq_snapshotRoots owner P code fuel machine member weight]
  exact Mettapedia.Machines.ResourceOwnership.census_snapshotRoots _ owner

/-- Collection under the archive's allocation-target observer preserves every
complete resource lookup, not merely the current answer or continuation. -/
theorem frontier_allocation_lookup_preserved {Owner : Type*} [DecidableEq Owner]
    (owner : Owner) (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) :
    (Mettapedia.Machines.ResourceOwnership.collect
      (frontierResourceHeap P code fuel machine member weight)
      (machine.world.receipts.allocationRoots owner)).lookup =
        (frontierResourceHeap P code fuel machine member weight).lookup := by
  rw [frontier_allocationRoots_eq_snapshotRoots owner P code fuel machine member weight]
  funext cell
  exact Mettapedia.Machines.ResourceOwnership.lookup_collect_snapshotRoots _ owner cell

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

/-- Arbitrary actual pauses resume after collection with exactly the same
ordered completed outcomes and chronological emissions at every budget. -/
theorem collectedFrontierMachine_resume_eq {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) (more : Nat) :
    (runFrontier (machineSpec P) more [machine]).map haltedObservation =
      (runFrontier (machineSpec P) more
        [collectedFrontierMachine owner P code fuel machine member weight]).map haltedObservation := by
  have pairs := NeedAllocationBound.collectMachine_runFrontier (machineReferenceInventory P) owner
    machine (runFrontier_heapRecorded P code fuel member)
    (runFrontier_referencesClosed P code fuel member) weight
    (runFrontier_slotBound P code fuel member) more
  change List.Forall₂ (fun source target => ∃ domain,
    NeedAllocationBound.MachineAgreement (machineReferenceDiscipline P) domain source target)
    (runFrontier (machineSpec P) more [machine])
    (runFrontier (machineSpec P) more
      [collectedFrontierMachine owner P code fuel machine member weight]) at pairs
  generalize sourceFrontier : runFrontier (machineSpec P) more [machine] = sources at pairs ⊢
  generalize targetFrontier : runFrontier (machineSpec P) more
    [collectedFrontierMachine owner P code fuel machine member weight] = targets at pairs ⊢
  clear sourceFrontier targetFrontier
  induction pairs with
  | nil => rfl
  | @cons source target sources targets related _ ih =>
    obtain ⟨domain, same⟩ := related
    simp only [List.map_cons, haltedObservation, haltedOutcome,
      same.control, same.worlds.worlds.receipts, ih]

/-- The stronger paused-control observer also keeps the complete receipt
graph and semantic work, rather than only finished values and emissions. -/
theorem collectedFrontierMachine_resume_configurations
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (P : Program) (code : Comp) (fuel : Nat) (machine : MMachine)
    (member : machine ∈ runFrontier (machineSpec P) fuel [initialMachine code])
    (weight : CellRecord (Comp × MEnv) MVal Empty → Nat) (more : Nat) :
    (runFrontier (machineSpec P) more [machine]).map (fun result =>
      (result.control, result.world.receipts, result.work)) =
    (runFrontier (machineSpec P) more
      [collectedFrontierMachine owner P code fuel machine member weight]).map (fun result =>
        (result.control, result.world.receipts, result.work)) :=
  NeedAllocationBound.collectMachine_frontier_observations (machineReferenceInventory P) owner
    machine (runFrontier_heapRecorded P code fuel member)
    (runFrontier_referencesClosed P code fuel member) weight
    (runFrontier_slotBound P code fuel member) more

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
