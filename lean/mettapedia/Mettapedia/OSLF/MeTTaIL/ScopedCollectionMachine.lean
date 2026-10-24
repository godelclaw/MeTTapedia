import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching
import Mettapedia.OSLF.MeTTaIL.CollectionSelectionTrace
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified

/-!
# Equational collection jobs on the shared scoped machine

Each finite allocation supplies ordinary argument and rest-capture tasks to the
existing resumable engine. The allocation's index/retention history is kept
beside the engine's nested occurrence trace. Resuming never reruns completed
captures or discards either history.

The initial finite allocation enumeration is eager. Fuel counts shared-engine
ticks per allocation, not the cost of constructing the allocation list.
Nested matching retains the existing scoped argument semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection

structure Request where
  rule : RewriteRule
  spec : RuleBindingSpec
  ambient : Nat
  site : RulePatternSite
  path : List Nat
  depth : Nat
  index : Nat
  initial : Assignment
  schemas : List Pattern
  rest : Option String
  kind : CollType
  targets : List Pattern
  deriving Repr

def Request.machine (request : Request) : GeneralScopedMatchMachine.Request :=
  { rule := request.rule, spec := request.spec, ambient := request.ambient
    site := request.site, path := request.path, depth := request.depth
    initial := request.initial
    schema := .collection request.kind request.schemas request.rest
    target := .collection request.kind request.targets none }

def Request.allocations (request : Request) : List (Allocation Pattern) :=
  tracedAllocations (request.kind == .hashSet) request.schemas.length request.targets

def allocationState (request : Request) (allocation : Allocation Pattern) : GeneralScopedMatchMachine.State :=
  let arguments := GeneralScopedMatchMachine.Task.arguments request.path request.depth request.index
    request.schemas allocation.values
  let residual := arrange request.kind allocation.residual
  match request.rest with
  | none =>
      if residual.isEmpty then
        { agenda := [⟨request.initial, [arguments], []⟩] }
      else { agenda := [] }
  | some name =>
      { agenda := [⟨request.initial,
          [arguments, .restCapture (request.path ++ [request.index + request.schemas.length])
            request.depth name request.kind residual], []⟩] }

structure Job where
  allocation : Allocation Pattern
  state : GeneralScopedMatchMachine.State
  deriving Repr

abbrev State := List Job

structure Receipt where
  allocation : Allocation Pattern
  matching : GeneralScopedMatchMachine.Answer
  deriving Repr

structure FiringReceipt where
  source : Receipt
  target : Pattern
  deriving Repr

def start (request : Request) : State :=
  request.allocations.map fun allocation => ⟨allocation, allocationState request allocation⟩

def resume (request : Request) (fuel : Nat) (state : State) : State :=
  state.map fun job => { job with state := GeneralScopedMatchMachine.run request.machine fuel job.state }

def complete (state : State) : Bool := state.all fun job => GeneralScopedMatchMachine.complete job.state

def publication (state : State) : List Receipt :=
  state.flatMap fun job => job.state.answers.map fun answer => ⟨job.allocation, answer⟩

def firing? (request : Request) (receipt : Receipt) : Option FiringReceipt := do
  let target ← reduct? request.rule request.spec request.ambient receipt.matching.assignment
  pure ⟨receipt, target⟩

def firings (request : Request) (state : State) : List FiringReceipt :=
  (publication state).filterMap (firing? request)

theorem firing?_target {request : Request} {receipt : Receipt} {firing : FiringReceipt}
    (made : firing? request receipt = some firing) :
    reduct? request.rule request.spec request.ambient receipt.matching.assignment =
      some firing.target := by
  unfold firing? at made
  cases reduced : reduct? request.rule request.spec request.ambient
      receipt.matching.assignment with
  | none => simp [reduced] at made
  | some target =>
      simp [reduced] at made
      cases made
      exact rfl

theorem firing?_source {request : Request} {receipt : Receipt} {firing : FiringReceipt}
    (made : firing? request receipt = some firing) : firing.source = receipt := by
  unfold firing? at made
  cases reduced : reduct? request.rule request.spec request.ambient
      receipt.matching.assignment with
  | none => simp [reduced] at made
  | some target =>
      simp [reduced] at made
      cases made
      rfl

theorem firings_source {request : Request} {state : State} {firing : FiringReceipt}
    (member : firing ∈ firings request state) : firing.source ∈ publication state := by
  obtain ⟨receipt, inside, made⟩ := List.mem_filterMap.mp member
  unfold firing? at made
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at made
  obtain ⟨target, _, made⟩ := made
  cases made
  exact inside

theorem resume_add (request : Request) (first extra : Nat) (state : State) :
    resume request (first + extra) state = resume request extra (resume request first state) := by
  simp only [resume, List.map_map, Function.comp_def, GeneralScopedMatchMachine.run_add]

theorem resume_zero (request : Request) (state : State) : resume request 0 state = state := by
  induction state with
  | nil => rfl
  | cons job jobs ih =>
      cases job
      simpa only [resume, List.map_cons, GeneralScopedMatchMachine.run] using congrArg (List.cons _) ih

def meanings (request : Request) (state : State) : List Assignment :=
  state.flatMap fun job => GeneralScopedMatchMachine.OrderedProjection.stateAssignments request.machine job.state

theorem resume_meanings (request : Request) (fuel : Nat) (state : State) :
    meanings request (resume request fuel state) = meanings request state := by
  simp only [meanings, resume, List.flatMap_map,
    GeneralScopedMatchMachine.OrderedProjection.run_assignments]

theorem allocation_meanings (request : Request) (allocation : Allocation Pattern) :
    GeneralScopedMatchMachine.OrderedProjection.stateAssignments request.machine (allocationState request allocation) =
      (matchArgsAt request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.index request.schemas allocation.values).flatMap
        fun middle => ScopedCollectionMatching.finish request.rule request.spec
          request.ambient request.site request.path request.depth
          (request.index + request.schemas.length) request.rest request.kind middle
          (arrange request.kind allocation.residual) := by
  cases rest : request.rest with
  | none =>
      by_cases empty : (arrange request.kind allocation.residual).isEmpty = true
      · simp [allocationState, rest, empty, GeneralScopedMatchMachine.OrderedProjection.stateAssignments,
          GeneralScopedMatchMachine.OrderedProjection.workAssignments, GeneralScopedMatchMachine.OrderedProjection.tasksAssignments,
          GeneralScopedMatchMachine.OrderedProjection.taskAssignments, Request.machine,
          ScopedCollectionMatching.finish]
      · simp [allocationState, rest, empty, GeneralScopedMatchMachine.OrderedProjection.stateAssignments,
          ScopedCollectionMatching.finish]
  | some name =>
      simp [allocationState, rest, GeneralScopedMatchMachine.OrderedProjection.stateAssignments,
        GeneralScopedMatchMachine.OrderedProjection.workAssignments, GeneralScopedMatchMachine.OrderedProjection.tasksAssignments,
        GeneralScopedMatchMachine.OrderedProjection.taskAssignments, Request.machine,
        ScopedCollectionMatching.finish]

theorem start_meanings (request : Request) :
    meanings request (start request) =
      ScopedCollectionMatching.run request.rule request.spec request.ambient request.site
        request.path request.depth request.index request.initial request.schemas request.rest
        request.kind request.targets := by
  simp only [meanings, start, List.flatMap_map, allocation_meanings]
  have erased := tracedAllocations_erase (request.kind == .hashSet)
    request.schemas.length request.targets
  have mapped := congrArg
    (List.flatMap fun pair : List Pattern × List Pattern =>
      (matchArgsAt request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.index request.schemas pair.1).flatMap
        fun middle => ScopedCollectionMatching.finish request.rule request.spec
          request.ambient request.site request.path request.depth
          (request.index + request.schemas.length) request.rest request.kind middle
          (arrange request.kind pair.2)) erased
  simpa only [List.flatMap_map, Function.comp_def, Allocation.erase,
    Request.allocations, ScopedCollectionMatching.run, kindAllocations] using mapped

theorem complete_meanings (request : Request) (state : State)
    (finished : complete state = true) :
    meanings request state = (publication state).map (·.matching.assignment) := by
  simp only [meanings, publication, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro job member
  exact GeneralScopedMatchMachine.OrderedProjection.complete_assignments request.machine job.state
    (List.all_eq_true.mp finished job member)

/-- Completed shared-machine tasks return the exact ordered assignment list
of the equational collection matcher, including repeated bag occurrences. -/
theorem completed_assignments (request : Request) (fuel : Nat)
    (finished : complete (resume request fuel (start request)) = true) :
    (publication (resume request fuel (start request))).map (·.matching.assignment) =
      ScopedCollectionMatching.run request.rule request.spec request.ambient request.site
        request.path request.depth request.index request.initial request.schemas request.rest
        request.kind request.targets := by
  rw [← complete_meanings request _ finished, resume_meanings, start_meanings]

theorem completed_exact (request : Request) (fuel : Nat)
    (finished : complete (resume request fuel (start request)) = true)
    (unordered : request.kind ≠ .vec)
    (distinct : request.kind = .hashSet → request.targets.Nodup)
    (final : Assignment) :
    (∃ receipt ∈ publication (resume request fuel (start request)),
      receipt.matching.assignment = final) ↔
      ScopedCollectionMatching.Matches request.rule request.spec request.ambient
        request.site request.path request.depth request.index request.initial
        request.schemas request.rest request.kind request.targets final := by
  rw [← ScopedCollectionMatching.run_exact _ _ _ _ _ _ _ _ _ _ _ unordered distinct,
    ← completed_assignments request fuel finished]
  exact List.mem_map.symm

theorem complete_resume (request : Request) (state : State)
    (finished : complete state = true) (fuel : Nat) :
    resume request fuel state = state := by
  induction state with
  | nil => rfl
  | cons job jobs ih =>
      have done := List.all_eq_true.mp finished job List.mem_cons_self
      have tail := ih (List.all_eq_true.mpr fun item member =>
        List.all_eq_true.mp finished item (List.mem_cons_of_mem job member))
      cases job
      simp only [resume, List.map_cons, GeneralScopedMatchMachine.run_complete done]
      exact congrArg (List.cons _) tail

/-- Every finite batch eventually settles. The bound is mathematical; callers
retain the explicit pending state when their selected budget is smaller. -/
theorem eventually_complete (request : Request) (state : State) :
    ∃ fuel, complete (resume request fuel state) = true := by
  induction state with
  | nil => exact ⟨0, rfl⟩
  | cons job jobs ih =>
      obtain ⟨first, headFinished⟩ :=
        GeneralScopedMatchMachine.finiteDrain request.machine job.state
      obtain ⟨later, tailFinished⟩ := ih
      refine ⟨first + later, ?_⟩
      change (GeneralScopedMatchMachine.complete
        (GeneralScopedMatchMachine.run request.machine (first + later) job.state) &&
          complete (resume request (first + later) jobs)) = true
      rw [GeneralScopedMatchMachine.run_add,
        GeneralScopedMatchMachine.run_complete headFinished, headFinished]
      simp only [Bool.true_and]
      rw [Nat.add_comm first later, resume_add, complete_resume request _ tailFinished]
      exact tailFinished

theorem run_accepts (request : GeneralScopedMatchMachine.Request) (fuel : Nat)
    (state : GeneralScopedMatchMachine.State) (answer : GeneralScopedMatchMachine.Answer) :
    GeneralScopedMatchMachine.StateAccepts request
      (GeneralScopedMatchMachine.run request fuel state) answer ↔
      GeneralScopedMatchMachine.StateAccepts request state answer := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      exact (ih _).trans (GeneralScopedMatchMachine.tick_accepts_iff request state answer)

/-- Independent traced task evidence for the chosen allocation. This retains
the original engine's occurrence paths, binder captures and ordered history. -/
def Valid (request : Request) (receipt : Receipt) : Prop :=
  receipt.allocation.decisions.length = request.schemas.length ∧
  replay (request.kind == .hashSet) request.targets receipt.allocation.decisions =
    some receipt.allocation.erase ∧
  GeneralScopedMatchMachine.StateAccepts request.machine
    (allocationState request receipt.allocation) receipt.matching

def FiringValid (request : Request) (firing : FiringReceipt) : Prop :=
  Valid request firing.source ∧
    reduct? request.rule request.spec request.ambient firing.source.matching.assignment =
      some firing.target

theorem publication_mem (request : Request) (fuel : Nat) (receipt : Receipt) :
    receipt ∈ publication (resume request fuel (start request)) ↔
      receipt.allocation ∈ request.allocations ∧
      receipt.matching ∈
        (GeneralScopedMatchMachine.run request.machine fuel
          (allocationState request receipt.allocation)).answers := by
  simp only [publication, resume, start, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨job, ⟨original, ⟨allocation, member, rfl⟩, rfl⟩, matching, emitted, same⟩
    subst receipt
    exact ⟨member, emitted⟩
  · rintro ⟨member, emitted⟩
    refine ⟨⟨receipt.allocation, GeneralScopedMatchMachine.run request.machine fuel
      (allocationState request receipt.allocation)⟩, ?_, receipt.matching, emitted, ?_⟩
    · exact ⟨_, ⟨_, member, rfl⟩, rfl⟩
    · cases receipt
      rfl

theorem publication_sound (request : Request) (fuel : Nat) {receipt : Receipt}
    (member : receipt ∈ publication (resume request fuel (start request))) :
    Valid request receipt := by
  obtain ⟨allocated, emitted⟩ := (publication_mem request fuel receipt).mp member
  refine ⟨?_, tracedAllocations_replay allocated, ?_⟩
  · exact tracedAllocations_length allocated
  · exact (run_accepts request.machine fuel _ _).mp (.inl emitted)

theorem publication_exact (request : Request) (fuel : Nat)
    (finished : complete (resume request fuel (start request)) = true) (receipt : Receipt) :
    receipt ∈ publication (resume request fuel (start request)) ↔ Valid request receipt := by
  refine ⟨publication_sound request fuel, ?_⟩
  rintro ⟨length, replayed, valid⟩
  have allocated : receipt.allocation ∈ request.allocations := by
    have recovered := replay_complete replayed
    simpa only [Request.allocations, length, Allocation.erase] using recovered
  apply (publication_mem request fuel receipt).mpr
  refine ⟨allocated, ?_⟩
  have done : GeneralScopedMatchMachine.complete
      (GeneralScopedMatchMachine.run request.machine fuel
        (allocationState request receipt.allocation)) = true := by
    apply List.all_eq_true.mp finished
      ⟨receipt.allocation, GeneralScopedMatchMachine.run request.machine fuel
        (allocationState request receipt.allocation)⟩
    simp only [resume, start, List.mem_map]
    exact ⟨_, ⟨_, allocated, rfl⟩, rfl⟩
  have reached := (run_accepts request.machine fuel _ _).mpr valid
  have empty := List.isEmpty_iff.mp done
  simpa only [GeneralScopedMatchMachine.StateAccepts, empty, List.not_mem_nil,
    false_and, exists_false, or_false] using reached

theorem firings_sound (request : Request) (fuel : Nat) {firing : FiringReceipt}
    (member : firing ∈ firings request (resume request fuel (start request))) :
    FiringValid request firing := by
  obtain ⟨receipt, published, made⟩ := List.mem_filterMap.mp member
  have source := firing?_source made
  subst receipt
  exact ⟨publication_sound request fuel published, firing?_target made⟩

theorem firings_exact (request : Request) (fuel : Nat)
    (finished : complete (resume request fuel (start request)) = true)
    (firing : FiringReceipt) :
    firing ∈ firings request (resume request fuel (start request)) ↔
      FiringValid request firing := by
  constructor
  · exact firings_sound request fuel
  · rintro ⟨valid, reduced⟩
    apply List.mem_filterMap.mpr
    refine ⟨firing.source, (publication_exact request fuel finished firing.source).mpr valid, ?_⟩
    cases firing
    simp [firing?, reduced]

/-- Completed execution has the exact source successor list, including repeated
occurrences. The right side uses the independently specified collection
matcher, followed by the authored reduct operation. -/
theorem completed_targets (request : Request) (fuel : Nat)
    (finished : complete (resume request fuel (start request)) = true) :
    (firings request (resume request fuel (start request))).map (·.target) =
      (ScopedCollectionMatching.run request.rule request.spec request.ambient
        request.site request.path request.depth request.index request.initial
        request.schemas request.rest request.kind request.targets).filterMap
        (reduct? request.rule request.spec request.ambient) := by
  rw [← completed_assignments request fuel finished]
  simp only [firings, List.map_filterMap, List.filterMap_map]
  apply List.filterMap_congr
  intro receipt _
  simp only [firing?, Function.comp_def]
  cases reduct? request.rule request.spec request.ambient receipt.matching.assignment <;> rfl

/-- At a complete frontier the actual targets agree in both directions with
collection equality, scoped captures, and the authored reduct. -/
theorem completed_target_iff (request : Request) (fuel : Nat)
    (finished : complete (resume request fuel (start request)) = true)
    (unordered : request.kind ≠ .vec)
    (distinct : request.kind = .hashSet → request.targets.Nodup) (target : Pattern) :
    (∃ firing ∈ firings request (resume request fuel (start request)), firing.target = target) ↔
      ∃ assignment,
        ScopedCollectionMatching.Matches request.rule request.spec request.ambient
          request.site request.path request.depth request.index request.initial
          request.schemas request.rest request.kind request.targets assignment ∧
        reduct? request.rule request.spec request.ambient assignment = some target := by
  rw [← List.mem_map, completed_targets request fuel finished, List.mem_filterMap]
  simp only [ScopedCollectionMatching.run_exact _ _ _ _ _ _ _ _ _ _ _ unordered distinct]

/-- Every finite request reaches exact source coverage; the work bound is
obtained from the real retained matcher, not a fuel assumption. -/
theorem eventually_source_exact (request : Request) :
    ∃ fuel, complete (resume request fuel (start request)) = true ∧
      (firings request (resume request fuel (start request))).map (·.target) =
        (ScopedCollectionMatching.run request.rule request.spec request.ambient
          request.site request.path request.depth request.index request.initial
          request.schemas request.rest request.kind request.targets).filterMap
          (reduct? request.rule request.spec request.ambient) := by
  obtain ⟨fuel, finished⟩ := eventually_complete request (start request)
  exact ⟨fuel, finished, completed_targets request fuel finished⟩

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
