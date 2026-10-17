import Mettapedia.Machines.BranchLocalNeed.CacheLaws

/-!
# Fresh allocation and protected Need heap simulation

Every occupied cell slot lies strictly below the world's next allocation
slot. Empty heaps satisfy this invariant, and every actual reference-machine
successor preserves it, for arbitrary language specifications and generations.
Consequently a world reached from an empty heap can allocate its next cell;
this is a property of the allocator and machine, not a caller-supplied
freshness assumption.

The invariant concerns current heap entries. It neither licenses arbitrary
cache replacement nor asserts logical typing, termination or effect rollback.

Protected world and machine agreements tolerate differences outside the
operational reference domain. Their primitive and instruction laws preserve
complete protected records, control, receipts, work and fresh identities.
The constructed source collector supplies the agreement, and the ordered
frontier theorem proves resumption equivalence at every finite budget.
Observers that dereference discarded receipt targets or inspect heap update
history require stronger retention; physical collection cost is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedAllocationBound

open NeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

/-- The next allocation slot is strictly greater than every occupied slot. -/
def SlotBound (world : World Origin Rule Value StableFault RetryableFault Effect) : Prop :=
  ∀ cell record, world.heap.lookup cell = some record → cell.slot < world.nextCell

namespace SlotBound

theorem of_empty (world : World Origin Rule Value StableFault RetryableFault Effect)
    (empty : world.heap = Heap.empty) : SlotBound world := by
  intro cell record present
  rw [empty, Heap.empty_lookup] at present
  cases present

theorem recorded {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    SlotBound (NeedReference.recorded world payload) := bounded

/-- Removing entries preserves the allocation counter's bound. Collection
does not recycle identities which may occur in retained code or receipts. -/
theorem restrict {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (kept : Finset CellId) (recorded : world.heap.Recorded) :
    SlotBound { world with heap := world.heap.restrict kept } := by
  intro cell record present
  change (world.heap.restrict kept).lookup cell = some record at present
  rw [Heap.lookup_restrict _ _ recorded] at present
  split at present
  · exact bounded cell record present
  · cases present

theorem fork {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (branch : Nat) : SlotBound (world.fork branch) := bounded

theorem setKnownCache {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) {cell : CellId}
    {record : CellRecord Origin Value StableFault}
    (present : world.heap.lookup cell = some record) (state : Cache Value StableFault) :
    SlotBound (world.setKnownCache cell record state) := by
  intro other found lookup
  change other.slot < world.nextCell
  by_cases equal : other = cell
  · subst other
    exact bounded cell record present
  · change (world.heap.setKnownCache cell record state).lookup other = some found at lookup
    rw [Heap.setKnownCache_preserves_other world.heap record state equal] at lookup
    exact bounded other found lookup

/-- Allocation increments the counter after inserting exactly its old slot. -/
theorem allocate {world next : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) {origin : Origin} {generation : Nat} {cell : CellId}
    (allocated : world.allocate? origin generation = some (next, cell)) : SlotBound next := by
  intro other record present
  rw [World.allocate?_nextCell allocated]
  by_cases equal : other = cell
  · subst other
    rw [World.allocate?_fresh_cell allocated]
    exact Nat.lt_succ_self world.nextCell
  · rw [World.allocate?_preserves_other allocated equal] at present
    exact Nat.lt_trans (bounded other record present) (Nat.lt_succ_self world.nextCell)

/-- No generation at the next slot can already be occupied. -/
theorem fresh_absent {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (generation : Nat) :
    world.heap.lookup (world.freshCell generation) = none := by
  cases present : world.heap.lookup (world.freshCell generation) with
  | none => rfl
  | some record =>
      have impossible := bounded _ record present
      exact (Nat.lt_irrefl world.nextCell impossible).elim

/-- The actual executable allocator succeeds at the actual fresh identity,
including the generations used for explicit resampling. -/
theorem allocate_succeeds {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (origin : Origin) (generation : Nat) :
    ∃ next, world.allocate? origin generation = some (next, world.freshCell generation) := by
  have absent := bounded.fresh_absent generation
  simp only [World.allocate?, Heap.allocate?, absent]
  exact ⟨_, rfl⟩

theorem allocation_not_none {world : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound world) (origin : Origin) (generation : Nat) :
    world.allocate? origin generation ≠ none := by
  obtain ⟨next, allocated⟩ := bounded.allocate_succeeds origin generation
  rw [allocated]
  intro impossible
  cases impossible

end SlotBound

/-- Worlds may differ outside a selected reference domain. Complete records
inside it, allocator identity, evaluator ownership and receipt data agree.
Heap update histories are intentionally absent from this relation. -/
structure WorldAgreement (domain : CellId → Prop)
    (left right : World Origin Rule Value StableFault RetryableFault Effect) : Prop where
  lineage : left.lineage = right.lineage
  path : left.path = right.path
  nextCell : left.nextCell = right.nextCell
  nextEvaluator : left.nextEvaluator = right.nextEvaluator
  receipts : left.receipts = right.receipts
  lookup : ∀ cell, domain cell → left.heap.lookup cell = right.heap.lookup cell

namespace WorldAgreement

variable {domain : CellId → Prop}
    {left right : World Origin Rule Value StableFault RetryableFault Effect}

theorem symm (same : WorldAgreement domain left right) :
    WorldAgreement domain right left :=
  ⟨same.lineage.symm, same.path.symm, same.nextCell.symm, same.nextEvaluator.symm,
    same.receipts.symm, fun cell retained => (same.lookup cell retained).symm⟩

theorem narrow (same : WorldAgreement domain left right) {smaller : CellId → Prop}
    (subset : ∀ cell, smaller cell → domain cell) : WorldAgreement smaller left right :=
  ⟨same.lineage, same.path, same.nextCell, same.nextEvaluator, same.receipts,
    fun cell retained => same.lookup cell (subset cell retained)⟩

theorem restrict (world : World Origin Rule Value StableFault RetryableFault Effect)
    (kept : Finset CellId) (recorded : world.heap.Recorded) :
    WorldAgreement (fun cell => cell ∈ kept) world
      { world with heap := world.heap.restrict kept } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro cell retained
  rw [Heap.lookup_restrict _ _ recorded, if_pos retained]

theorem fresh_eq (same : WorldAgreement domain left right) (generation : Nat) :
    left.freshCell generation = right.freshCell generation := by
  simp only [World.freshCell, same.lineage, same.path, same.nextCell]

theorem fork (same : WorldAgreement domain left right) (index : Nat) :
    WorldAgreement domain (left.fork index) (right.fork index) :=
  ⟨same.lineage, congrArg (fun path => path ++ [index]) same.path,
    same.nextCell, same.nextEvaluator, same.receipts, same.lookup⟩

theorem recorded (same : WorldAgreement domain left right)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    WorldAgreement domain (NeedReference.recorded left payload)
      (NeedReference.recorded right payload) := by
  refine ⟨same.lineage, same.path, same.nextCell, same.nextEvaluator, ?_, same.lookup⟩
  change (left.receipts.append left.path payload).1 = (right.receipts.append right.path payload).1
  rw [same.receipts, same.path]

theorem advanceEvaluator (same : WorldAgreement domain left right) :
    WorldAgreement domain { left with nextEvaluator := left.nextEvaluator + 1 }
      { right with nextEvaluator := right.nextEvaluator + 1 } :=
  ⟨same.lineage, same.path, same.nextCell, congrArg (fun n => n + 1) same.nextEvaluator,
    same.receipts, same.lookup⟩

theorem setKnownCache (same : WorldAgreement domain left right) (cell : CellId)
    (record : CellRecord Origin Value StableFault) (state : Cache Value StableFault) :
    WorldAgreement domain (left.setKnownCache cell record state)
      (right.setKnownCache cell record state) := by
  refine ⟨same.lineage, same.path, same.nextCell, same.nextEvaluator, same.receipts, ?_⟩
  intro queried retained
  by_cases equal : queried = cell
  · subst queried
    simp only [World.setKnownCache, Heap.setKnownCache_lookup_same]
  · change (left.heap.setKnownCache cell record state).lookup queried =
      (right.heap.setKnownCache cell record state).lookup queried
    rw [Heap.setKnownCache_preserves_other _ _ _ equal,
      Heap.setKnownCache_preserves_other _ _ _ equal]
    exact same.lookup queried retained

/-- After allocation, both worlds extend the reference domain by the same
fresh identity. Existing records remain paired and the new record is equal. -/
theorem allocate (same : WorldAgreement domain left right)
    {leftNext rightNext : World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (leftSuccess : left.allocate? origin generation = some (leftNext, cell))
    (rightSuccess : right.allocate? origin generation = some (rightNext, cell)) :
    WorldAgreement (fun queried => domain queried ∨ queried = cell) leftNext rightNext := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [World.allocate?_lineage leftSuccess, World.allocate?_lineage rightSuccess]
    exact same.lineage
  · rw [(World.allocate?_metadata leftSuccess).1, (World.allocate?_metadata rightSuccess).1]
    exact same.path
  · rw [World.allocate?_nextCell leftSuccess, World.allocate?_nextCell rightSuccess]
    exact congrArg (fun n => n + 1) same.nextCell
  · rw [(World.allocate?_metadata leftSuccess).2.1, (World.allocate?_metadata rightSuccess).2.1]
    exact same.nextEvaluator
  · rw [(World.allocate?_metadata leftSuccess).2.2, (World.allocate?_metadata rightSuccess).2.2,
      same.receipts, same.path]
  · intro queried retained
    by_cases equal : queried = cell
    · subst queried
      rw [World.allocate?_lookup_same leftSuccess, World.allocate?_lookup_same rightSuccess]
    · rw [World.allocate?_preserves_other leftSuccess equal,
        World.allocate?_preserves_other rightSuccess equal]
      exact same.lookup queried (retained.resolve_right equal)

/-- Reachable allocator bounds construct the paired allocation; success in
the collected world is not supplied as an assumed simulation premise. -/
theorem allocate_match (same : WorldAgreement domain left right)
    (leftBounded : SlotBound left) (rightBounded : SlotBound right)
    (origin : Origin) (generation : Nat) :
    ∃ leftNext rightNext,
      left.allocate? origin generation = some (leftNext, left.freshCell generation) ∧
      right.allocate? origin generation = some (rightNext, left.freshCell generation) ∧
      WorldAgreement (fun queried => domain queried ∨ queried = left.freshCell generation)
        leftNext rightNext := by
  obtain ⟨leftNext, leftSuccess⟩ := leftBounded.allocate_succeeds origin generation
  obtain ⟨rightNext, rightSuccess⟩ := rightBounded.allocate_succeeds origin generation
  rw [← same.fresh_eq generation] at rightSuccess
  exact ⟨leftNext, rightNext, leftSuccess, rightSuccess, same.allocate leftSuccess rightSuccess⟩

end WorldAgreement

/-- Every protected cell exists, and all operational references in its
origin and cache remain within the same protected domain. -/
def ProtectedWorld
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (discipline : NeedCacheLaws.ReferenceDiscipline spec) (domain : CellId → Prop)
    (world : World Origin Rule Value StableFault RetryableFault Effect) : Prop :=
  ∀ cell, domain cell → ∃ record, world.heap.lookup cell = some record ∧
    discipline.origin domain record.origin ∧ discipline.cache domain record.cache

namespace ProtectedWorld

variable {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec} {domain : CellId → Prop}
    {world : World Origin Rule Value StableFault RetryableFault Effect}

theorem recorded (closed : ProtectedWorld discipline domain world)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    ProtectedWorld discipline domain (NeedReference.recorded world payload) := closed

theorem fork (closed : ProtectedWorld discipline domain world) (index : Nat) :
    ProtectedWorld discipline domain (world.fork index) := closed

theorem advanceEvaluator (closed : ProtectedWorld discipline domain world) :
    ProtectedWorld discipline domain { world with nextEvaluator := world.nextEvaluator + 1 } := closed

theorem setKnownCache (closed : ProtectedWorld discipline domain world)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (retained : domain cell) (found : world.heap.lookup cell = some record)
    {state : Cache Value StableFault} (ready : discipline.cache domain state) :
    ProtectedWorld discipline domain (world.setKnownCache cell record state) := by
  intro queried protectedCell
  obtain ⟨original, lookup, origin, cache⟩ := closed queried protectedCell
  by_cases equal : queried = cell
  · subst queried
    obtain ⟨owned, ownedLookup, ownedOrigin, _⟩ := closed cell retained
    rw [found, Option.some.injEq] at ownedLookup
    subst owned
    exact ⟨{ record with cache := state }, Heap.setKnownCache_lookup_same _ _ _ _, ownedOrigin, ready⟩
  · exact ⟨original, by
      change (world.heap.setKnownCache cell record state).lookup queried = some original
      rw [Heap.setKnownCache_preserves_other _ _ _ equal]
      exact lookup, origin, cache⟩

theorem allocate (closed : ProtectedWorld discipline domain world)
    {next : World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (captured : discipline.origin domain origin)
    (success : world.allocate? origin generation = some (next, cell)) :
    ProtectedWorld discipline (fun queried => domain queried ∨ queried = cell) next := by
  intro queried protectedCell
  have grows : ∀ c, domain c → domain c ∨ c = cell := fun _ retained => Or.inl retained
  by_cases equal : queried = cell
  · subst queried
    exact ⟨⟨origin, .suspended⟩, World.allocate?_lookup_same success,
      discipline.origin_mono grows captured, True.intro⟩
  · obtain ⟨record, lookup, capturedOrigin, cache⟩ := closed queried (protectedCell.resolve_right equal)
    exact ⟨record, by rw [World.allocate?_preserves_other success equal]; exact lookup,
      discipline.origin_mono grows capturedOrigin, discipline.cache_mono grows cache⟩

end ProtectedWorld

/-- A heap-relative agreement with the closure and allocator obligations
needed by actual instructions. These are state properties, not assumed steps. -/
structure ProtectedWorldAgreement
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (discipline : NeedCacheLaws.ReferenceDiscipline spec) (domain : CellId → Prop)
    (left right : World Origin Rule Value StableFault RetryableFault Effect) : Prop where
  worlds : WorldAgreement domain left right
  leftBounded : SlotBound left
  rightBounded : SlotBound right
  closed : ProtectedWorld discipline domain left

namespace ProtectedWorldAgreement

variable {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec} {domain : CellId → Prop}
    {left right : World Origin Rule Value StableFault RetryableFault Effect}

theorem symm (same : ProtectedWorldAgreement discipline domain left right) :
    ProtectedWorldAgreement discipline domain right left := by
  refine ⟨same.worlds.symm, same.rightBounded, same.leftBounded, ?_⟩
  intro cell retained
  obtain ⟨record, found, origin, cache⟩ := same.closed cell retained
  exact ⟨record, by rw [← same.worlds.lookup cell retained]; exact found, origin, cache⟩

theorem recorded (same : ProtectedWorldAgreement discipline domain left right)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    ProtectedWorldAgreement discipline domain (NeedReference.recorded left payload)
      (NeedReference.recorded right payload) :=
  ⟨same.worlds.recorded payload, same.leftBounded.recorded payload,
    same.rightBounded.recorded payload, same.closed.recorded payload⟩

theorem fork (same : ProtectedWorldAgreement discipline domain left right) (index : Nat) :
    ProtectedWorldAgreement discipline domain (left.fork index) (right.fork index) :=
  ⟨same.worlds.fork index, same.leftBounded.fork index, same.rightBounded.fork index,
    same.closed.fork index⟩

theorem advanceEvaluator (same : ProtectedWorldAgreement discipline domain left right) :
    ProtectedWorldAgreement discipline domain { left with nextEvaluator := left.nextEvaluator + 1 }
      { right with nextEvaluator := right.nextEvaluator + 1 } :=
  ⟨same.worlds.advanceEvaluator, same.leftBounded, same.rightBounded, same.closed.advanceEvaluator⟩

theorem setKnownCache (same : ProtectedWorldAgreement discipline domain left right)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (retained : domain cell) (found : left.heap.lookup cell = some record)
    {state : Cache Value StableFault} (ready : discipline.cache domain state) :
    ProtectedWorldAgreement discipline domain (left.setKnownCache cell record state)
      (right.setKnownCache cell record state) :=
  ⟨same.worlds.setKnownCache cell record state,
    same.leftBounded.setKnownCache found state,
    same.rightBounded.setKnownCache (by rw [← same.worlds.lookup cell retained]; exact found) state,
    same.closed.setKnownCache retained found ready⟩

theorem allocate_match (same : ProtectedWorldAgreement discipline domain left right)
    (origin : Origin) (generation : Nat) (captured : discipline.origin domain origin) :
    ∃ leftNext rightNext,
      left.allocate? origin generation = some (leftNext, left.freshCell generation) ∧
      right.allocate? origin generation = some (rightNext, left.freshCell generation) ∧
      ProtectedWorldAgreement discipline
        (fun queried => domain queried ∨ queried = left.freshCell generation) leftNext rightNext := by
  obtain ⟨leftNext, rightNext, leftSuccess, rightSuccess, worlds⟩ :=
    same.worlds.allocate_match same.leftBounded same.rightBounded origin generation
  exact ⟨leftNext, rightNext, leftSuccess, rightSuccess,
    worlds, same.leftBounded.allocate leftSuccess, same.rightBounded.allocate rightSuccess,
    same.closed.allocate captured leftSuccess⟩

end ProtectedWorldAgreement

/-- Protected machines agree on the full control and semantic work account.
Closure refers to a selected domain rather than all allocated garbage. -/
structure MachineAgreement
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (discipline : NeedCacheLaws.ReferenceDiscipline spec) (domain : CellId → Prop)
    (left right : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) : Prop where
  worlds : ProtectedWorldAgreement discipline domain left.world right.world
  control : left.control = right.control
  work : left.work = right.work
  roots : discipline.control domain left.control

namespace MachineAgreement

variable {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec} {domain : CellId → Prop}
    {left right : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}

theorem symm (same : MachineAgreement discipline domain left right) :
    MachineAgreement discipline domain right left :=
  ⟨same.worlds.symm, same.control.symm, same.work.symm, by rw [← same.control]; exact same.roots⟩

theorem finished (same : MachineAgreement discipline domain left right)
    {extended : CellId → Prop}
    {leftWorld rightWorld : World Origin Rule Value StableFault RetryableFault Effect}
    (worlds : ProtectedWorldAgreement discipline extended leftWorld rightWorld)
    (control : Control Local Resume Value StableFault RetryableFault)
    (roots : discipline.control extended control) (lookups updates receipts allocations : Nat) :
    MachineAgreement discipline extended
      (NeedReference.finished left leftWorld control lookups updates receipts allocations)
      (NeedReference.finished right rightWorld control lookups updates receipts allocations) :=
  ⟨worlds, rfl, congrArg (fun work => work.bump lookups updates receipts allocations) same.work, roots⟩

/-- Every local action produces a positionwise paired successor list.
Allocation and resampling extend the protected domain with the fresh cell. -/
theorem step_run (same : MachineAgreement discipline domain left right)
    {state : Local} {saved : List (Frame Resume)}
    (running : left.control = .run state saved) :
    List.Forall₂ (fun source target => ∃ extended,
      MachineAgreement discipline extended source target) (step spec left) (step spec right) := by
  have rightRunning : right.control = .run state saved := same.control.symm.trans running
  have roots := same.roots
  rw [running] at roots
  rcases roots with ⟨localRoots, savedRoots⟩
  have exposed := discipline.action localRoots
  cases action : spec.action state with
  | done result =>
    have returned : discipline.outcome domain result := by
      cases result with
      | value value => simpa only [action, NeedCacheLaws.ReferenceDiscipline.outcome] using exposed
      | stableFault | retryableFault => trivial
    simp only [step, running, rightRunning, action]
    exact .cons ⟨domain, same.finished same.worlds (.returned result saved)
      ⟨returned, savedRoots⟩ 0 0 0 0⟩ .nil
  | demand cell token =>
    simp only [action] at exposed
    simp only [step, running, rightRunning, action]
    exact .cons ⟨domain, same.finished same.worlds (.force cell (.resume token :: saved))
      ⟨exposed.1, discipline.stack_cons.mpr ⟨exposed.2, savedRoots⟩⟩ 0 0 0 0⟩ .nil
  | perform event following =>
    simp only [action] at exposed
    simp only [step, running, rightRunning, action]
    exact .cons ⟨domain, same.finished (same.worlds.recorded (.effect event))
      (.run following saved) ⟨exposed, savedRoots⟩ 0 0 1 0⟩ .nil
  | allocate origin token =>
    simp only [action] at exposed
    obtain ⟨sourceNext, targetNext, sourceSuccess, targetSuccess, worlds⟩ :=
      same.worlds.allocate_match origin 0 exposed.1
    let extended := fun cell => domain cell ∨ cell = left.world.freshCell 0
    have grows : ∀ cell, domain cell → extended cell := fun _ retained => Or.inl retained
    have newRoots : discipline.control extended
        (.run (spec.afterAllocation token (left.world.freshCell 0)) saved) :=
      ⟨discipline.afterAllocation (discipline.resume_mono grows exposed.2) (Or.inr rfl),
        discipline.stack_mono grows savedRoots⟩
    simp only [step, running, rightRunning, action, sourceSuccess, targetSuccess]
    exact .cons ⟨extended, same.finished worlds _ newRoots 1 1 1 1⟩ .nil
  | resample cell token =>
    simp only [action] at exposed
    obtain ⟨record, found, origin, _⟩ := same.worlds.closed cell exposed.1
    have targetFound : right.world.heap.lookup cell = some record := by
      rw [← same.worlds.worlds.lookup cell exposed.1]
      exact found
    obtain ⟨sourceNext, targetNext, sourceSuccess, targetSuccess, worlds⟩ :=
      same.worlds.allocate_match record.origin (cell.generation + 1) origin
    let fresh := left.world.freshCell (cell.generation + 1)
    let extended := fun queried => domain queried ∨ queried = fresh
    have grows : ∀ queried, domain queried → extended queried := fun _ retained => Or.inl retained
    have newRoots : discipline.control extended (.run (spec.afterAllocation token fresh) saved) :=
      ⟨discipline.afterAllocation (discipline.resume_mono grows exposed.2) (Or.inr rfl),
        discipline.stack_mono grows savedRoots⟩
    simp only [step, running, rightRunning, action, found, targetFound, sourceSuccess, targetSuccess]
    exact .cons ⟨extended, same.finished (worlds.recorded (.resample cell fresh)) _
      newRoots 2 1 2 1⟩ .nil

theorem branchAlternatives_pair (same : MachineAgreement discipline domain left right)
    {sourceBase targetBase : World Origin Rule Value StableFault RetryableFault Effect}
    (worlds : ProtectedWorldAgreement discipline domain sourceBase targetBase)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (retained : domain cell) (found : sourceBase.heap.lookup cell = some record)
    (owner : EvaluatorId) (saved : List (Frame Resume))
    (savedRoots : discipline.stack domain saved) (start : Nat) (choices : List (Rule × Local))
    (locals : ∀ pair ∈ choices, discipline.localState domain pair.2) :
    List.Forall₂ (fun source target => ∃ extended, MachineAgreement discipline extended source target)
      (branchAlternatives left sourceBase cell record owner saved start choices)
      (branchAlternatives right targetBase cell record owner saved start choices) := by
  induction choices generalizing start with
  | nil => exact .nil
  | cons head tail ih =>
    simp only [branchAlternatives]
    have marked := ((worlds.fork start).setKnownCache retained found
      (state := .evaluating owner) True.intro).recorded (.evaluate cell owner)
    have chosen := marked.recorded (.chooseRule cell head.1)
    exact .cons ⟨domain, same.finished chosen (.run head.2 (.commit cell owner :: saved))
      ⟨locals head (by simp), discipline.stack_cons.mpr ⟨retained, savedRoots⟩⟩ 1 1 2 0⟩
      (ih (start + 1) (fun pair member => locals pair (List.mem_cons_of_mem _ member)))

/-- First force, cached delivery and black-hole retry preserve the paired
occurrences. Alternative positions and duplicate rules remain distinct. -/
theorem step_force (same : MachineAgreement discipline domain left right)
    {cell : CellId} {saved : List (Frame Resume)}
    (forcing : left.control = .force cell saved) :
    List.Forall₂ (fun source target => ∃ extended,
      MachineAgreement discipline extended source target) (step spec left) (step spec right) := by
  have rightForcing : right.control = .force cell saved := same.control.symm.trans forcing
  have roots := same.roots
  rw [forcing] at roots
  rcases roots with ⟨retained, savedRoots⟩
  obtain ⟨record, found, captured, ready⟩ := same.worlds.closed cell retained
  have targetFound : right.world.heap.lookup cell = some record := by
    rw [← same.worlds.worlds.lookup cell retained]
    exact found
  cases cache : record.cache with
  | value value =>
    simp only [step, forcing, rightForcing, found, targetFound, cache]
    have valueRoots : discipline.outcome domain (.value value) := by
      simpa only [NeedCacheLaws.ReferenceDiscipline.cache, NeedCacheLaws.ReferenceDiscipline.outcome,
        cache] using ready
    exact .cons ⟨domain, same.finished (same.worlds.recorded (.observe cell (.value value)))
      (.returned (.value value) saved) ⟨valueRoots, savedRoots⟩ 1 0 1 0⟩ .nil
  | stableFault fault =>
    simp only [step, forcing, rightForcing, found, targetFound, cache]
    exact .cons ⟨domain, same.finished (same.worlds.recorded (.observe cell (.stableFault fault)))
      (.returned (.stableFault fault) saved) ⟨True.intro, savedRoots⟩ 1 0 1 0⟩ .nil
  | evaluating owner =>
    simp only [step, forcing, rightForcing, found, targetFound, cache, retryMachine]
    exact .cons ⟨domain, same.finished (same.worlds.recorded (.retry cell (.blackhole cell)))
      (.returned (.retryableFault (.blackhole cell)) saved) ⟨True.intro, savedRoots⟩ 1 0 1 0⟩ .nil
  | suspended =>
    have advanced := same.worlds.advanceEvaluator
    rw [← same.worlds.worlds.nextEvaluator] at advanced
    cases choices : spec.alternatives record.origin with
    | nil =>
      simp only [step, forcing, rightForcing, found, targetFound, cache, choices, retryMachine]
      rw [← same.worlds.worlds.nextEvaluator]
      exact .cons ⟨domain, same.finished
        ((advanced.recorded (.evaluate cell left.world.nextEvaluator)).recorded
          (.retry cell (.noRule cell)))
        (.returned (.retryableFault (.noRule cell)) saved) ⟨True.intro, savedRoots⟩ 1 0 2 0⟩ .nil
    | cons head tail =>
      simp only [step, forcing, rightForcing, found, targetFound, cache, choices]
      rw [← same.worlds.worlds.nextEvaluator]
      apply same.branchAlternatives_pair advanced cell record retained found
        left.world.nextEvaluator saved savedRoots 0 (head :: tail)
      intro pair member
      exact discipline.alternatives captured (by rwa [choices])

/-- Returning through a continuation, committing under its owner, and
ownership-loss retries all preserve positionwise successor agreement. -/
theorem step_returned (same : MachineAgreement discipline domain left right)
    {result : Produced Value StableFault RetryableFault} {saved : List (Frame Resume)}
    (returning : left.control = .returned result saved) :
    List.Forall₂ (fun source target => ∃ extended,
      MachineAgreement discipline extended source target) (step spec left) (step spec right) := by
  have rightReturning : right.control = .returned result saved := same.control.symm.trans returning
  have roots := same.roots
  rw [returning] at roots
  rcases roots with ⟨returnedRoots, savedRoots⟩
  cases saved with
  | nil =>
    simp only [step, returning, rightReturning]
    exact .cons ⟨domain, same.finished same.worlds (.halted result) returnedRoots 0 0 0 0⟩ .nil
  | cons frame rest =>
    rcases discipline.stack_cons.mp savedRoots with ⟨frameRoots, restRoots⟩
    cases frame with
    | resume token =>
      simp only [step, returning, rightReturning]
      exact .cons ⟨domain, same.finished same.worlds (.run (spec.afterDemand token result) rest)
        ⟨discipline.afterDemand frameRoots returnedRoots, restRoots⟩ 0 0 0 0⟩ .nil
    | commit cell owner =>
      obtain ⟨record, found, _, _⟩ := same.worlds.closed cell frameRoots
      have targetFound : right.world.heap.lookup cell = some record := by
        rw [← same.worlds.worlds.lookup cell frameRoots]
        exact found
      cases cache : record.cache with
      | evaluating actual =>
        by_cases owned : actual = owner
        · cases result with
          | value value =>
            have ready : discipline.cache domain (.value value) := returnedRoots
            have committed := (same.worlds.setKnownCache frameRoots found ready).recorded
              (.observe cell (.value value))
            simp only [step, returning, rightReturning, found, targetFound, cache, owned, ↓reduceDIte]
            exact .cons ⟨domain, same.finished committed (.returned (.value value) rest)
              ⟨returnedRoots, restRoots⟩ 1 1 1 0⟩ .nil
          | stableFault fault =>
            have committed := (same.worlds.setKnownCache frameRoots found
              (state := .stableFault fault) True.intro).recorded (.observe cell (.stableFault fault))
            simp only [step, returning, rightReturning, found, targetFound, cache, owned, ↓reduceDIte]
            exact .cons ⟨domain, same.finished committed (.returned (.stableFault fault) rest)
              ⟨True.intro, restRoots⟩ 1 1 1 0⟩ .nil
          | retryableFault reason =>
            have reset := (same.worlds.setKnownCache frameRoots found
              (state := .suspended) True.intro).recorded (.retry cell reason)
            simp only [step, returning, rightReturning, found, targetFound, cache, owned,
              ↓reduceDIte, retryMachine]
            exact .cons ⟨domain, same.finished reset (.returned (.retryableFault reason) rest)
              ⟨True.intro, restRoots⟩ 1 1 1 0⟩ .nil
        · simp only [step, returning, rightReturning, found, targetFound, cache, owned,
            ↓reduceDIte, retryMachine]
          exact .cons ⟨domain, same.finished
            (same.worlds.recorded (.retry cell (.ownershipLost cell owner actual)))
            (.returned (.retryableFault (.ownershipLost cell owner actual)) rest)
            ⟨True.intro, restRoots⟩ 1 0 1 0⟩ .nil
      | suspended | value _ | stableFault _ =>
        simp only [step, returning, rightReturning, found, targetFound, cache, retryMachine]
        exact .cons ⟨domain, same.finished
          (same.worlds.recorded (.retry cell (.ownershipLost cell owner 0)))
          (.returned (.retryableFault (.ownershipLost cell owner 0)) rest)
          ⟨True.intro, restRoots⟩ 1 0 1 0⟩ .nil

/-- The unchanged machine's complete ordered transition lists are paired.
Every successor supplies its own protected domain for the next transition. -/
theorem step (same : MachineAgreement discipline domain left right) :
    List.Forall₂ (fun source target => ∃ extended,
      MachineAgreement discipline extended source target) (NeedReference.step spec left)
        (NeedReference.step spec right) := by
  cases control : left.control with
  | force cell saved => exact same.step_force control
  | run state saved => exact same.step_run control
  | returned result saved => exact same.step_returned control
  | halted result =>
    have targetControl := same.control.symm.trans control
    simp only [NeedReference.step, control, targetControl]
    exact .nil

theorem isHalted_eq (same : MachineAgreement discipline domain left right) :
    isHalted left = isHalted right := by
  simp only [isHalted, ← same.control]

theorem advance (same : MachineAgreement discipline domain left right) :
    List.Forall₂ (fun source target => ∃ extended, MachineAgreement discipline extended source target)
      (NeedReference.advance spec left) (NeedReference.advance spec right) := by
  cases halted : isHalted left with
  | false =>
    rw [NeedFrontierLaws.advance_running spec left halted,
      NeedFrontierLaws.advance_running spec right (same.isHalted_eq ▸ halted)]
    exact same.step
  | true =>
    rw [NeedFrontierLaws.advance_halted spec left halted,
      NeedFrontierLaws.advance_halted spec right (same.isHalted_eq ▸ halted)]
    exact .cons ⟨domain, same⟩ .nil

/-- Full bounded frontiers agree positionwise, retaining pauses, halted
states, duplicate outcomes, receipts and the semantic work account. -/
theorem runFrontier {sources targets : List
    (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (pairs : List.Forall₂ (fun source target => ∃ domain,
      MachineAgreement discipline domain source target) sources targets) (fuel : Nat) :
    List.Forall₂ (fun source target => ∃ domain, MachineAgreement discipline domain source target)
      (NeedReference.runFrontier spec fuel sources) (NeedReference.runFrontier spec fuel targets) := by
  induction fuel generalizing sources targets with
  | zero => exact pairs
  | succ fuel ih =>
    have haltEq : sources.all isHalted = targets.all isHalted := by
      induction pairs with
      | nil => rfl
      | @cons source target sources targets related _ ih =>
        obtain ⟨domain, same⟩ := related
        simp only [List.all_cons, same.isHalted_eq, ih]
    simp only [NeedReference.runFrontier, haltEq]
    split
    · exact pairs
    · apply ih
      apply List.rel_flatMap pairs
      intro source target related
      obtain ⟨domain, same⟩ := related
      exact same.advance

end MachineAgreement

/-- The existing world-preservation interface discharges allocation safety
from its primitive operations, without repeating the instruction analysis. -/
theorem slotBoundWorldInvariant : WorldInstructionInvariant
    (fun world : World Origin Rule Value StableFault RetryableFault Effect => SlotBound world) := {
  fork _ index bounded := bounded.fork index
  nextEvaluator _ bounded := bounded
  record _ payload bounded _ := bounded.recorded payload
  cache _ _ _ state bounded present := bounded.setKnownCache present state
  allocate _ _ _ _ _ bounded success := bounded.allocate success
}

/-- Every occurrence in a first-force branch retains the slot bound. -/
theorem branchAlternatives_slotBound
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {base : World Origin Rule Value StableFault RetryableFault Effect}
    (bounded : SlotBound base) (cell : CellId) (record : CellRecord Origin Value StableFault)
    (present : base.heap.lookup cell = some record) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (start : Nat) (alternatives : List (Rule × Local))
    {candidate : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : candidate ∈ branchAlternatives machine base cell record owner stack start alternatives) :
    SlotBound candidate.world :=
  branchAlternatives_preserves_world slotBoundWorldInvariant machine base bounded
    cell record present owner stack start alternatives candidate member

/-- Every successor of the existing machine retains the fresh-slot invariant. -/
theorem step_slotBound
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (bounded : SlotBound machine.world) (member : next ∈ step spec machine) :
    SlotBound next.world :=
  step_preserves_world slotBoundWorldInvariant spec machine next bounded member

/-- The constructed source collector retains the allocation counter and
therefore cannot make an old cell identity available for reuse. -/
theorem collectMachine_slotBound {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) (bounded : SlotBound machine.world) :
    SlotBound (inventory.collectMachine owner machine recorded closed weight).world :=
  bounded.restrict _ recorded

/-- The actual collector constructs the heap-relative agreement; a matching
session or counter without protected lookups is insufficient. -/
theorem collectMachine_worldAgreement
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) :
    WorldAgreement (fun cell => cell ∈ Mettapedia.Machines.ResourceOwnership.census
      (inventory.resourceHeap machine.world.heap recorded closed.1 weight)
      (inventory.controlRoots owner machine.control)) machine.world
      (inventory.collectMachine owner machine recorded closed weight).world :=
  WorldAgreement.restrict machine.world _ recorded

/-- All simulation obligations are constructed from the actual collector's
census, reference closure and retained counter. No transition relation is
assumed between the source and collected machines. -/
theorem collectMachine_machineAgreement
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) (bounded : SlotBound machine.world) :
    MachineAgreement discipline
      (fun cell => cell ∈ Mettapedia.Machines.ResourceOwnership.census
        (inventory.resourceHeap machine.world.heap recorded closed.1 weight)
        (inventory.controlRoots owner machine.control)) machine
      (inventory.collectMachine owner machine recorded closed weight) := by
  let kept := Mettapedia.Machines.ResourceOwnership.census
    (inventory.resourceHeap machine.world.heap recorded closed.1 weight)
    (inventory.controlRoots owner machine.control)
  let collected := inventory.collectMachine owner machine recorded closed weight
  have collectedClosed := inventory.collectMachine_closed owner machine recorded closed weight
  have grows : ∀ cell, NeedCacheLaws.heapLive collected.world.heap cell → cell ∈ kept := by
    intro cell live
    obtain ⟨record, found⟩ := live
    change (machine.world.heap.restrict kept).lookup cell = some record at found
    rw [Heap.lookup_restrict _ _ recorded] at found
    split at found
    next member => exact member
    next _ => cases found
  have protectedHeap : ProtectedWorld discipline (fun cell => cell ∈ kept) machine.world := by
    intro cell retained
    have live := (Mettapedia.Machines.ResourceOwnership.mem_census_iff_live _ _
      (inventory.controlRoots_valid owner machine recorded closed weight) cell).mp retained
    have allocated := Mettapedia.Machines.ResourceOwnership.live_allocated _ _ live
    obtain ⟨record, found⟩ := (machine.world.heap.allocated_iff_lookup recorded cell).mp allocated
    have collectedFound : collected.world.heap.lookup cell = some record := by
      change (machine.world.heap.restrict kept).lookup cell = some record
      rw [Heap.lookup_restrict _ _ recorded, if_pos retained]
      exact found
    have captured := collectedClosed.1 cell record collectedFound
    exact ⟨record, found, discipline.origin_mono grows captured.1, discipline.cache_mono grows captured.2⟩
  refine ⟨⟨collectMachine_worldAgreement inventory owner machine recorded closed weight,
    bounded, collectMachine_slotBound inventory owner machine recorded closed weight bounded,
    protectedHeap⟩, rfl, rfl, ?_⟩
  exact discipline.control_mono grows collectedClosed.2

/-- Every future bounded frontier of the collected machine is paired with
the uncollected frontier, in order and with occurrence multiplicity intact. -/
theorem collectMachine_runFrontier
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) (bounded : SlotBound machine.world)
    (fuel : Nat) :
    List.Forall₂ (fun source target => ∃ domain, MachineAgreement discipline domain source target)
      (NeedReference.runFrontier spec fuel [machine])
      (NeedReference.runFrontier spec fuel
        [inventory.collectMachine owner machine recorded closed weight]) := by
  apply MachineAgreement.runFrontier
  exact .cons ⟨_, collectMachine_machineAgreement inventory owner machine recorded closed weight bounded⟩ .nil

/-- Control, complete receipts and semantic work agree after every budget.
This observer does not dereference receipt targets or inspect heap history. -/
theorem collectMachine_frontier_observations
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) (bounded : SlotBound machine.world)
    (fuel : Nat) :
    (NeedReference.runFrontier spec fuel [machine]).map (fun result =>
      (result.control, result.world.receipts, result.work)) =
    (NeedReference.runFrontier spec fuel
      [inventory.collectMachine owner machine recorded closed weight]).map (fun result =>
        (result.control, result.world.receipts, result.work)) := by
  have pairs := collectMachine_runFrontier inventory owner machine recorded closed weight bounded fuel
  generalize sourceFrontier : NeedReference.runFrontier spec fuel [machine] = sources at pairs ⊢
  generalize targetFrontier : NeedReference.runFrontier spec fuel
    [inventory.collectMachine owner machine recorded closed weight] = targets at pairs ⊢
  clear sourceFrontier targetFrontier
  induction pairs with
  | nil => rfl
  | @cons source target sources targets related _ ih =>
    obtain ⟨domain, same⟩ := related
    simp only [List.map_cons, same.control, same.worlds.worlds.receipts, same.work, ih]

/-- Source and collected worlds allocate the same identity and retain equal
protected records afterward. Both successful allocations are constructed. -/
theorem collectMachine_allocation_match
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) (bounded : SlotBound machine.world)
    (origin : Origin) (generation : Nat) :
    let collected := inventory.collectMachine owner machine recorded closed weight
    let kept := Mettapedia.Machines.ResourceOwnership.census
      (inventory.resourceHeap machine.world.heap recorded closed.1 weight)
      (inventory.controlRoots owner machine.control)
    ∃ sourceNext collectedNext,
      machine.world.allocate? origin generation = some (sourceNext, machine.world.freshCell generation) ∧
      collected.world.allocate? origin generation = some (collectedNext, machine.world.freshCell generation) ∧
      WorldAgreement (fun cell => cell ∈ kept ∨ cell = machine.world.freshCell generation)
        sourceNext collectedNext :=
  (collectMachine_worldAgreement inventory owner machine recorded closed weight).allocate_match
    bounded (collectMachine_slotBound inventory owner machine recorded closed weight bounded)
    origin generation

theorem collectMachine_allocate_succeeds
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {discipline : NeedCacheLaws.ReferenceDiscipline spec}
    (inventory : NeedCacheLaws.ReferenceInventory discipline)
    {Owner : Type*} [DecidableEq Owner] (owner : Owner)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (recorded : machine.world.heap.Recorded) (closed : discipline.machineClosed machine)
    (weight : CellRecord Origin Value StableFault → Nat) (bounded : SlotBound machine.world)
    (origin : Origin) (generation : Nat) :
    ∃ next, (inventory.collectMachine owner machine recorded closed weight).world.allocate?
      origin generation = some (next, machine.world.freshCell generation) :=
  (collectMachine_slotBound inventory owner machine recorded closed weight bounded).allocate_succeeds
    origin generation

theorem steps_slotBound
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) (bounded : SlotBound initial.world) :
    SlotBound final.world := by
  induction execution with
  | refl => exact bounded
  | cons successor _ ih =>
      exact ih (step_slotBound spec _ _ bounded (successor.mem spec))

/-- Every world reached from an empty heap has a fresh next allocation slot,
regardless of the source language, selected branch or resampling generation. -/
theorem reachable_allocate_succeeds
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) (empty : initial.world.heap = Heap.empty)
    (origin : Origin) (generation : Nat) :
    ∃ next, final.world.allocate? origin generation =
      some (next, final.world.freshCell generation) :=
  (steps_slotBound spec execution (SlotBound.of_empty initial.world empty)).allocate_succeeds
    origin generation

theorem reachable_allocation_not_none
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) (empty : initial.world.heap = Heap.empty)
    (origin : Origin) (generation : Nat) : final.world.allocate? origin generation ≠ none :=
  (steps_slotBound spec execution (SlotBound.of_empty initial.world empty)).allocation_not_none
    origin generation

/-- An arbitrary supplied heap can violate the bound: an occupied next slot
is not a valid initial state for the reachable-freshness theorem. -/
theorem occupied_next_slot_not_bounded
    {world : World Origin Rule Value StableFault RetryableFault Effect}
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (present : world.heap.lookup cell = some record) (slot : cell.slot = world.nextCell) :
    ¬ SlotBound world := by
  intro bounded
  have impossible := bounded cell record present
  rw [slot] at impossible
  exact Nat.lt_irrefl world.nextCell impossible

/-- The allocator remains fail-closed on malformed externally supplied
worlds. The invariant proves this branch unreachable; it does not delete it. -/
theorem occupied_fresh_allocation_fails
    {world : World Origin Rule Value StableFault RetryableFault Effect}
    {record : CellRecord Origin Value StableFault} {generation : Nat}
    (present : world.heap.lookup (world.freshCell generation) = some record) (origin : Origin) :
    world.allocate? origin generation = none := by
  simp only [World.allocate?, Heap.allocate?, present]

#print axioms SlotBound.of_empty
#print axioms SlotBound.allocate
#print axioms SlotBound.fresh_absent
#print axioms SlotBound.allocate_succeeds
#print axioms step_slotBound
#print axioms steps_slotBound
#print axioms reachable_allocate_succeeds
#print axioms reachable_allocation_not_none
#print axioms occupied_next_slot_not_bounded
#print axioms occupied_fresh_allocation_fails

end Mettapedia.Machines.BranchLocalNeed.NeedAllocationBound
