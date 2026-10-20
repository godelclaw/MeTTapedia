import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalSemantics
import Mettapedia.TypeTheory.ContextualCBPVNeed

/-!
# Scoped need in the contextual effect model

`ScopedNeedComputation.Code` binds suspension references with `letNeed` and
reads them with `force`; its natural semantics (`ScopedNeedNaturalSemantics`)
keeps a branch-local heap of owned cells.  This module reads the same code in
the free computation `Program` of the contextual model.  The state is a store
of memo caches, one per allocated cell, and a demand is the cell handler of
`ContextualCBPVNeed` (`Demand.cell`) for many cells: a cached value or stable
fault is served again; a pending cell runs its producer, which the reference
carries, and caches the outcome, except a retryable one, which leaves the
cell pending.  As in the natural semantics, `letNeed`, `sequence` and
`choose` each allocate a cell, and a cell whose source is a choice selects
one alternative when it is first demanded.

* `reading`: the program of the code and the program of its cell's producer;
* `demand_cached`, `demand_pending`, `alloc_run`: the steps of a run;
* `StoreAgrees`, `RefAgrees`: a store and its references against a heap;
* `eval_sound`, `force_sound`: every natural derivation from a heap that
  agrees with a store has its outcome among the worlds of the reading, which
  end in a store that agrees with the derivation's final heap.

The agreement holds for every derivation whose outcome is not a retryable
fault the machine raises itself (`MachineRetry`: a blackhole, a missing or
out-of-scope cell, lost ownership, an allocation collision).  Retryable
outcomes are never caught, so this excludes them everywhere in the derivation;
a retryable fault of a primitive is allowed.  The heap's named cells must be
allocated (`RefAgrees`); nothing else is assumed of the supplied heap.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.ScopedNeed

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ScopedNeedComputation (Code)
open ScopedNeedMachine (Closure ValueBody NeedBody NeedWorld)
open ScopedNeedNaturalSemantics (Eval Force Selection enterWorld finalize retryResult pairOutcome)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-- The outcome of a computation: a native value, a stable fault or a
retryable one. -/
abbrev Outcome (Head StableFault NativeFault : Type) (m : Nat) :=
  ScopedNeedMachine.Outcome Head StableFault NativeFault m

/-- One memo cache per allocated cell, in allocation order; `none` is pending. -/
abbrev Store (Head StableFault NativeFault : Type) (m : Nat) :=
  List (Option (Outcome Head StableFault NativeFault m))

/-- Computations over the store, answering outcomes, requesting effects. -/
abbrev Run (Head Effect StableFault NativeFault : Type) (m : Nat) :=
  Program (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect

/-- A suspension reference: its cell's position in the store and its producer. -/
abbrev Ref (Head Effect StableFault NativeFault : Type) (m : Nat) :=
  Nat × Run Head Effect StableFault NativeFault m

/-- Append a pending cell and continue with its position. -/
def alloc (next : Nat → Run Head Effect StableFault NativeFault m) :
    Run Head Effect StableFault NativeFault m :=
  .read fun store => .write (store ++ [none]) (next store.length)

/-- Cache an outcome in a cell unless it is retryable. -/
def settle (cell : Nat) : Outcome Head StableFault NativeFault m →
    Run Head Effect StableFault NativeFault m
  | .retryableFault reason => .pure (.retryableFault reason)
  | .value value =>
      .read fun store => .write (store.set cell (some (.value value))) (.pure (.value value))
  | .stableFault fault =>
      .read fun store => .write (store.set cell (some (.stableFault fault))) (.pure (.stableFault fault))

/-- Force a cell: serve its cache, or run its producer once and settle. -/
def demand (cell : Nat) (producer : Run Head Effect StableFault NativeFault m) :
    Run Head Effect StableFault NativeFault m :=
  .read fun store =>
    match store.getD cell none with
    | some outcome => .pure outcome
    | none => producer.bind (settle cell)

/-- A native value continues; a fault ends the computation. -/
def onValue (next : Tm Head m → Run Head Effect StableFault NativeFault m) :
    Outcome Head StableFault NativeFault m → Run Head Effect StableFault NativeFault m
  | .value value => next value
  | .stableFault fault => .pure (.stableFault fault)
  | .retryableFault reason => .pure (.retryableFault reason)

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

/-- The reading of scoped code under native values and references: the
program of the code, and the program its cell runs when first demanded (a
choice selects one alternative; any other code runs itself). -/
def reading : {n k : Nat} → Code Head Operation Effect n k → Sub Head n m →
    (Fin k → Ref Head Effect StableFault NativeFault m) →
      Run Head Effect StableFault NativeFault m × Run Head Effect StableFault NativeFault m
  | _, _, .returnValue term, values, _ =>
      (.pure (.value (subst values term)), .pure (.value (subst values term)))
  | _, _, .call operation argument, values, _ =>
      (.pure (ScopedNeedMachine.liftOutcome (primitive operation (subst values argument))),
       .pure (ScopedNeedMachine.liftOutcome (primitive operation (subst values argument))))
  | _, _, .emit effect next, values, needs =>
      (.intent effect (reading next values needs).1, .intent effect (reading next values needs).1)
  | _, _, .choose left right, values, needs =>
      (alloc fun cell => demand cell (.choose (reading left values needs).1 (reading right values needs).1),
       .choose (reading left values needs).1 (reading right values needs).1)
  | _, _, .sequence first body, values, needs =>
      (alloc fun cell => (demand cell (reading first values needs).2).bind
          (onValue fun value => (reading body (Fin.cases value values) needs).1),
       alloc fun cell => (demand cell (reading first values needs).2).bind
          (onValue fun value => (reading body (Fin.cases value values) needs).1))
  | _, _, .sequenceSigma first body, values, needs =>
      (alloc fun cell => (demand cell (reading first values needs).2).bind
          (onValue fun value =>
            Program.map (pairOutcome value) (reading body (Fin.cases value values) needs).1),
       alloc fun cell => (demand cell (reading first values needs).2).bind
          (onValue fun value =>
            Program.map (pairOutcome value) (reading body (Fin.cases value values) needs).1))
  | _, _, .letNeed suspended body, values, needs =>
      (alloc fun cell =>
          (reading body values (Fin.cases (cell, (reading suspended values needs).2) needs)).1,
       alloc fun cell =>
          (reading body values (Fin.cases (cell, (reading suspended values needs).2) needs)).1)
  | _, _, .force reference, _, needs =>
      (demand (needs reference).1 (needs reference).2, demand (needs reference).1 (needs reference).2)

/-- The answers of closed code from the empty store. -/
def answers (code : Code Head Operation Effect 0 0) (values : Sub Head 0 m) :
    List (Outcome Head StableFault NativeFault m) :=
  (runWorlds (reading primitive code values Fin.elim0).1 []).map WorldResult.answer

/-- Only a choice's cell differs from the code: it selects an alternative. -/
theorem reading_snd_of_not_choose {n k : Nat} (code : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → Ref Head Effect StableFault NativeFault m)
    (notChoice : ∀ left right, code ≠ .choose left right) :
    (reading primitive code values needs).2 = (reading primitive code values needs).1 := by
  cases code with
  | choose left right => exact absurd rfl (notChoice left right)
  | _ => rfl

/-! ## The steps of a run -/

theorem alloc_run (next : Nat → Run Head Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace) :
    runWorldsAt (alloc next) store branch = runWorldsAt (next store.length) (store ++ [none]) branch :=
  rfl

theorem demand_cached (cell : Nat) (producer : Run Head Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    (outcome : Outcome Head StableFault NativeFault m)
    (cached : store.getD cell none = some outcome) :
    runWorldsAt (demand cell producer) store branch =
      [{ branch := branch, answer := outcome, state := store, intents := [] }] := by
  unfold demand
  simp only [runWorldsAt]
  rw [cached]
  rfl

theorem demand_pending (cell : Nat) (producer : Run Head Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    (pending : store.getD cell none = none) :
    runWorldsAt (demand cell producer) store branch =
      runWorldsAt (producer.bind (settle cell)) store branch := by
  unfold demand
  simp only [runWorldsAt]
  rw [pending]

theorem mem_bind {Answer Other : Type}
    {program : Program (Store Head StableFault NativeFault m) Answer Effect}
    {next : Answer → Program (Store Head StableFault NativeFault m) Other Effect}
    {store : Store Head StableFault NativeFault m} {branch : BranchTrace}
    {first : WorldResult (Store Head StableFault NativeFault m) Answer Effect}
    {second : WorldResult (Store Head StableFault NativeFault m) Other Effect}
    (firstMem : first ∈ runWorldsAt program store branch)
    (secondMem : second ∈ runWorldsAt (next first.answer) first.state first.branch) :
    WorldResult.prependIntents first.intents second ∈ runWorldsAt (program.bind next) store branch := by
  rw [runWorldsAt_bind]
  exact List.mem_flatMap.mpr ⟨first, firstMem, List.mem_map.mpr ⟨second, secondMem, rfl⟩⟩

/-! ## Heap operations -/

section Heaps

variable {Origin Value Fault : Type}

theorem lookup_setKnownCache (heap : Heap Origin Value Fault) (cell other : CellId)
    (record : CellRecord Origin Value Fault) (state : Cache Value Fault) :
    (heap.setKnownCache cell record state).lookup other =
      if other = cell then some { record with cache := state } else heap.lookup other := by
  simp only [Heap.setKnownCache, Heap.lookup, Function.update_apply]

end Heaps

section Worlds

variable {world next : NeedWorld Head Operation Effect StableFault NativeFault m}

theorem allocate_fresh {origin : Closure Head Operation Effect m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) :
    world.heap.lookup cell = none ∧
      next.heap.lookup cell = some ⟨origin, .suspended⟩ ∧
      ∀ other, other ≠ cell → next.heap.lookup other = world.heap.lookup other := by
  unfold World.allocate? at allocated
  dsimp only at allocated
  split at allocated
  · contradiction
  · rename_i heap allocatedHeap
    cases allocated
    unfold Heap.allocate? at allocatedHeap
    split at allocatedHeap
    · contradiction
    · rename_i absent
      cases allocatedHeap
      refine ⟨absent, ?_, ?_⟩
      · simp [World.record, Heap.lookup]
      · intro other different
        simp [World.record, Heap.lookup, different]

theorem enterWorld_lookup (cell other : CellId) (origin : Closure Head Operation Effect m)
    (position : Nat) (rule : ScopedNeedMachine.Rule) :
    (enterWorld world cell origin position rule).heap.lookup other =
      if other = cell then some ⟨origin, .evaluating world.nextEvaluator⟩
      else world.heap.lookup other := by
  simp only [enterWorld, World.record, World.setKnownCache, World.fork]
  rw [lookup_setKnownCache]

end Worlds

/-! ## Agreement of a store with a heap -/

/-- A cache of the heap and a cache of the store agree.  A cell being
evaluated is pending in the store. -/
inductive CacheAgrees : Cache (Tm Head m) StableFault → Option (Outcome Head StableFault NativeFault m) →
    Prop where
  | suspended : CacheAgrees .suspended none
  | evaluating (owner : EvaluatorId) : CacheAgrees (.evaluating owner) none
  | value (value : Tm Head m) : CacheAgrees (.value value) (some (.value value))
  | stableFault (fault : StableFault) : CacheAgrees (.stableFault fault) (some (.stableFault fault))

/-- The store's cells are distinct cells of the heap, in allocation order, and
their caches agree. -/
structure StoreAgrees (cells : List CellId)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) : Prop where
  length : cells.length = store.length
  distinct : cells.Nodup
  caches : ∀ index cell, cells[index]? = some cell →
    ∃ record, world.heap.lookup cell = some record ∧ CacheAgrees record.cache (store.getD index none)

/-- A heap that keeps every cell of another, with its origin. -/
def Extends (world next : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  ∀ cell origin cache, world.heap.lookup cell = some ⟨origin, cache⟩ →
    ∃ cache', next.heap.lookup cell = some ⟨origin, cache'⟩

/-- A reference names a cell of the store whose producer is the reading of the
cell's origin, under references that agree in turn. -/
inductive RefAgrees (cells : List CellId) (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    CellId → Ref Head Effect StableFault NativeFault m → Prop where
  | intro {cell : CellId} (index : Nat) (located : cells[index]? = some cell)
      (origin : Closure Head Operation Effect m) (cache : Cache (Tm Head m) StableFault)
      (refs : Fin origin.k → Ref Head Effect StableFault NativeFault m)
      (record : world.heap.lookup cell = some ⟨origin, cache⟩)
      (children : ∀ j, RefAgrees cells world (origin.needs j) (refs j)) :
      RefAgrees cells world cell (index, (reading primitive origin.code origin.values refs).2)

/-- A retryable fault the machine raises itself, not one a primitive reports. -/
def MachineRetry : Outcome Head StableFault NativeFault m → Prop
  | .retryableFault (.domain _) => False
  | .retryableFault _ => True
  | _ => False

theorem Extends.refl (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Extends world world :=
  fun _ _ cache present => ⟨cache, present⟩

theorem Extends.trans {world middle next : NeedWorld Head Operation Effect StableFault NativeFault m}
    (first : Extends world middle) (second : Extends middle next) : Extends world next := by
  intro cell origin cache present
  obtain ⟨cache', present'⟩ := first cell origin cache present
  exact second cell origin cache' present'

theorem Extends.of_heap {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    (same : next.heap = world.heap) : Extends world next := by
  intro cell origin cache present
  exact ⟨cache, by rw [same]; exact present⟩

theorem prefix_getElem? {cells cells' : List CellId} (isPrefix : cells <+: cells')
    {index : Nat} {cell : CellId} (located : cells[index]? = some cell) : cells'[index]? = some cell := by
  obtain ⟨tail, rfl⟩ := isPrefix
  have bound : index < cells.length := (List.getElem?_eq_some_iff.mp located).1
  rw [List.getElem?_append_left bound]
  exact located

theorem RefAgrees.mono {cells cells' : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {ref : Ref Head Effect StableFault NativeFault m}
    (agrees : RefAgrees primitive cells world cell ref) (isPrefix : cells <+: cells')
    (extends' : Extends world next) : RefAgrees primitive cells' next cell ref := by
  induction agrees with
  | intro index located origin cache refs record _ childrenIH =>
      obtain ⟨cache', record'⟩ := extends' _ origin cache record
      exact .intro index (prefix_getElem? isPrefix located) origin cache' refs record' childrenIH

theorem StoreAgrees.of_heap {cells : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : Store Head StableFault NativeFault m}
    (agrees : StoreAgrees cells world store) (same : next.heap = world.heap) :
    StoreAgrees cells next store :=
  ⟨agrees.length, agrees.distinct, fun index cell located => by
    rw [same]; exact agrees.caches index cell located⟩

theorem StoreAgrees.cached {cells : List CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : Store Head StableFault NativeFault m}
    (agrees : StoreAgrees cells world store) {index : Nat} {cell : CellId}
    (located : cells[index]? = some cell) {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (present : world.heap.lookup cell = some record) :
    CacheAgrees record.cache (store.getD index none) := by
  obtain ⟨record', present', agreesCache⟩ := agrees.caches index cell located
  rw [present] at present'
  cases present'
  exact agreesCache

theorem nodup_index_unique {cells : List CellId} (distinct : cells.Nodup)
    {first second : Nat} {cell : CellId}
    (firstLocated : cells[first]? = some cell) (secondLocated : cells[second]? = some cell) :
    first = second := by
  obtain ⟨firstBound, firstEq⟩ := List.getElem?_eq_some_iff.mp firstLocated
  obtain ⟨secondBound, secondEq⟩ := List.getElem?_eq_some_iff.mp secondLocated
  exact (distinct.getElem_inj_iff).mp (firstEq.trans secondEq.symm)

theorem StoreAgrees.alloc {cells : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : Store Head StableFault NativeFault m} {origin : Closure Head Operation Effect m}
    {cell : CellId} (agrees : StoreAgrees cells world store)
    (allocated : world.allocate? origin = some (next, cell)) :
    StoreAgrees (cells ++ [cell]) next (store ++ [none]) := by
  obtain ⟨absent, present, others⟩ := allocate_fresh allocated
  have notIn : cell ∉ cells := by
    intro member
    obtain ⟨index, bound, located⟩ := List.getElem_of_mem member
    obtain ⟨record, found, _⟩ := agrees.caches index cell (List.getElem?_eq_some_iff.mpr ⟨bound, located⟩)
    rw [absent] at found
    cases found
  refine ⟨by simp [agrees.length], List.nodup_append.mpr ⟨agrees.distinct, List.nodup_singleton cell,
    fun a member b memberB => by
      simp only [List.mem_singleton] at memberB
      subst memberB
      intro equal
      exact notIn (equal ▸ member)⟩, ?_⟩
  intro index other located
  by_cases bound : index < cells.length
  · rw [List.getElem?_append_left bound] at located
    have different : other ≠ cell := by
      intro equal
      subst equal
      exact notIn (List.mem_of_getElem? located)
    obtain ⟨record, found, agreesCache⟩ := agrees.caches index other located
    refine ⟨record, by rw [others other different]; exact found, ?_⟩
    have storeBound : index < store.length := agrees.length ▸ bound
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left storeBound] using agreesCache
  · have atEnd : index = cells.length := by
      have := (List.getElem?_eq_some_iff.mp located).1
      simp at this
      omega
    subst atEnd
    simp at located
    subst located
    refine ⟨⟨origin, .suspended⟩, present, ?_⟩
    have : (store ++ [none]).getD cells.length none = none := by
      rw [agrees.length]
      simp [List.getD_eq_getElem?_getD]
    rw [this]
    exact .suspended

theorem StoreAgrees.enter {cells : List CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : Store Head StableFault NativeFault m} (agrees : StoreAgrees cells world store)
    {cell : CellId} {origin : Closure Head Operation Effect m}
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (position : Nat) (rule : ScopedNeedMachine.Rule) :
    StoreAgrees cells (enterWorld world cell origin position rule) store := by
  refine ⟨agrees.length, agrees.distinct, ?_⟩
  intro index other located
  rw [enterWorld_lookup]
  by_cases same : other = cell
  · subst same
    have pending := agrees.cached located present
    rw [if_pos rfl]
    refine ⟨_, rfl, ?_⟩
    generalize store.getD index none = entry at pending ⊢
    cases pending
    exact .evaluating _
  · rw [if_neg same]
    exact agrees.caches index other located

/-- Replacing one cell's cache, and the store's entry for it, keeps agreement. -/
theorem StoreAgrees.replace {cells : List CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store store' : Store Head StableFault NativeFault m} (agrees : StoreAgrees cells world store)
    {index : Nat} {cell : CellId} (located : cells[index]? = some cell)
    {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (state : Cache (Tm Head m) StableFault)
    (sameLength : store'.length = store.length)
    (replaced : CacheAgrees state (store'.getD index none))
    (kept : ∀ other, other ≠ index → store'.getD other none = store.getD other none) :
    StoreAgrees cells (world.setKnownCache cell record state) store' := by
  refine ⟨agrees.length.trans sameLength.symm, agrees.distinct, ?_⟩
  intro other otherCell otherLocated
  simp only [World.setKnownCache]
  rw [lookup_setKnownCache]
  by_cases same : otherCell = cell
  · subst same
    have equal := nodup_index_unique agrees.distinct otherLocated located
    subst equal
    rw [if_pos rfl]
    exact ⟨_, rfl, replaced⟩
  · rw [if_neg same]
    have different : other ≠ index := by
      intro equal
      subst equal
      rw [located] at otherLocated
      cases otherLocated
      exact same rfl
    rw [kept other different]
    exact agrees.caches other otherCell otherLocated

theorem Extends.alloc {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) : Extends world next := by
  obtain ⟨absent, _, others⟩ := allocate_fresh allocated
  intro other origin' cache present
  have different : other ≠ cell := by
    intro equal
    subst equal
    rw [absent] at present
    cases present
  exact ⟨cache, by rw [others other different]; exact present⟩

theorem Extends.setKnownCache {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (present : world.heap.lookup cell = some record) (state : Cache (Tm Head m) StableFault) :
    Extends world (world.setKnownCache cell record state) := by
  intro other origin cache found
  simp only [World.setKnownCache]
  rw [lookup_setKnownCache]
  by_cases same : other = cell
  · subst same
    rw [present] at found
    cases found
    exact ⟨state, by rw [if_pos rfl]⟩
  · exact ⟨cache, by rw [if_neg same]; exact found⟩

theorem Extends.enter {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m}
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (position : Nat) (rule : ScopedNeedMachine.Rule) :
    Extends world (enterWorld world cell origin position rule) := by
  intro other origin' cache found
  rw [enterWorld_lookup]
  by_cases same : other = cell
  · subst same
    rw [present] at found
    cases found
    exact ⟨_, by rw [if_pos rfl]⟩
  · exact ⟨cache, by rw [if_neg same]; exact found⟩

/-! ## Settling a cell -/

/-- The store after settling a cell. -/
def settled (cell : Nat) : Outcome Head StableFault NativeFault m →
    Store Head StableFault NativeFault m → Store Head StableFault NativeFault m
  | .value value, store => store.set cell (some (.value value))
  | .stableFault fault, store => store.set cell (some (.stableFault fault))
  | .retryableFault _, store => store

/-- The cache a finalized cell keeps. -/
def cacheOf : Outcome Head StableFault NativeFault m → Cache (Tm Head m) StableFault
  | .value value => .value value
  | .stableFault fault => .stableFault fault
  | .retryableFault _ => .suspended

theorem settle_run (cell : Nat) (outcome : Outcome Head StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace) :
    runWorldsAt (settle (Effect := Effect) cell outcome) store branch =
      [{ branch := branch, answer := outcome, state := settled cell outcome store, intents := [] }] := by
  cases outcome <;> rfl

theorem settled_length (cell : Nat) (outcome : Outcome Head StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) :
    (settled cell outcome store).length = store.length := by
  cases outcome <;> simp [settled]

theorem settled_other (cell other : Nat) (different : other ≠ cell)
    (outcome : Outcome Head StableFault NativeFault m) (store : Store Head StableFault NativeFault m) :
    (settled cell outcome store).getD other none = store.getD other none := by
  cases outcome <;> simp [settled, List.getD_eq_getElem?_getD, Ne.symm different]

theorem settled_agrees (cell : Nat) (outcome : Outcome Head StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (bound : cell < store.length)
    (pending : store.getD cell none = none) :
    CacheAgrees (cacheOf outcome) ((settled cell outcome store).getD cell none) := by
  cases outcome with
  | value value =>
      simp only [settled, cacheOf, List.getD_eq_getElem?_getD, List.getElem?_set_self bound]
      exact .value value
  | stableFault fault =>
      simp only [settled, cacheOf, List.getD_eq_getElem?_getD, List.getElem?_set_self bound]
      exact .stableFault fault
  | retryableFault reason =>
      simp only [settled, cacheOf]
      rw [pending]
      exact .suspended

/-- A finalization that the machine does not refuse found the cell evaluated
by this owner, answers the body's outcome and caches it. -/
theorem finalize_owned {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {owner : EvaluatorId} {outcome : Outcome Head StableFault NativeFault m}
    (notRetry : ¬ MachineRetry (finalize world cell owner outcome).1) :
    ∃ record, world.heap.lookup cell = some record ∧ record.cache = .evaluating owner ∧
      (finalize world cell owner outcome).1 = outcome ∧
      (finalize world cell owner outcome).2.heap =
        (world.setKnownCache cell record (cacheOf outcome)).heap := by
  unfold finalize at notRetry ⊢
  split at notRetry
  · simp [retryResult, MachineRetry] at notRetry
  · rename_i record found
    split at notRetry
    · rename_i actual evaluating
      by_cases owned : actual = owner
      · subst owned
        refine ⟨record, by rw [found], evaluating, ?_, ?_⟩
        · simp only [if_true]
          cases outcome <;> rfl
        · simp only [if_true]
          cases outcome <;> rfl
      · simp [retryResult, MachineRetry, owned] at notRetry
    · simp [retryResult, MachineRetry] at notRetry

theorem not_machineRetry_of_pair {first : Tm Head m} {outcome : Outcome Head StableFault NativeFault m}
    (notRetry : ¬ MachineRetry (pairOutcome first outcome)) : ¬ MachineRetry outcome := by
  cases outcome <;> simp_all [pairOutcome, MachineRetry]

/-! ## Soundness -/

/-- A world of the run answers the outcome and ends in a store that agrees
with the final heap; the heap keeps every cell it had. -/
abbrev Witnessed (cells : List CellId)
    (world final : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (program : Run Head Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace) : Prop :=
  ∃ (cells' : List CellId)
    (result : WorldResult (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect),
    cells <+: cells' ∧ StoreAgrees cells' final result.state ∧ Extends world final ∧
      result ∈ runWorldsAt program store branch ∧ result.answer = outcome

theorem located_last {cells : List CellId} {store : Store Head StableFault NativeFault m}
    (length : cells.length = store.length) (cell : CellId) :
    (cells ++ [cell])[store.length]? = some cell := by
  rw [← length]
  simp

/-- The reference of a cell that was just allocated for an origin. -/
theorem RefAgrees.fresh {cells : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : Store Head StableFault NativeFault m} (agrees : StoreAgrees cells world store)
    {n k : Nat} {code : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {refs : Fin k → Ref Head Effect StableFault NativeFault m}
    (refsAgree : ∀ j, RefAgrees primitive cells world (needs j) (refs j)) {cell : CellId}
    (allocated : world.allocate? ⟨n, k, code, values, needs⟩ = some (next, cell)) :
    RefAgrees primitive (cells ++ [cell]) next cell
      (store.length, (reading primitive code values refs).2) :=
  .intro store.length (located_last agrees.length cell) ⟨n, k, code, values, needs⟩ .suspended refs
    (allocate_fresh allocated).2.1
    (fun j => (refsAgree j).mono primitive (List.prefix_append _ _) (Extends.alloc allocated))

theorem CacheAgrees.none_of_suspended {entry : Option (Outcome Head StableFault NativeFault m)}
    (agrees : CacheAgrees (Head := Head) .suspended entry) : entry = none := by
  cases agrees; rfl

theorem CacheAgrees.none_of_evaluating {entry : Option (Outcome Head StableFault NativeFault m)}
    {owner : EvaluatorId} (agrees : CacheAgrees (Head := Head) (.evaluating owner) entry) : entry = none := by
  cases agrees; rfl

theorem CacheAgrees.of_value {entry : Option (Outcome Head StableFault NativeFault m)}
    {value : Tm Head m} (agrees : CacheAgrees (StableFault := StableFault) (.value value) entry) :
    entry = some (.value value) := by
  cases agrees; rfl

theorem CacheAgrees.of_stableFault {entry : Option (Outcome Head StableFault NativeFault m)}
    {fault : StableFault} (agrees : CacheAgrees (Head := Head) (.stableFault fault) entry) :
    entry = some (.stableFault fault) := by
  cases agrees; rfl

/-! ## Selected occurrences -/

/-- The references of a selected occurrence: those of its origin. -/
def selectionRefs {origin selected : Closure Head Operation Effect m} {position : Nat}
    {rule : ScopedNeedMachine.Rule} :
    Selection origin position rule selected →
      (Fin origin.k → Ref Head Effect StableFault NativeFault m) →
        Fin selected.k → Ref Head Effect StableFault NativeFault m
  | .entry _, refs => refs
  | .left _ _ _ _, refs => refs
  | .right _ _ _ _, refs => refs

/-- The branch trace of a selected occurrence: an alternative of a choice
records its side. -/
def selectionBranch {origin selected : Closure Head Operation Effect m} {position : Nat}
    {rule : ScopedNeedMachine.Rule} :
    Selection origin position rule selected → BranchTrace → BranchTrace
  | .entry _, branch => branch
  | .left _ _ _ _, branch => false :: branch
  | .right _ _ _ _, branch => true :: branch

theorem selection_refsAgree {cells : List CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin selected : Closure Head Operation Effect m} {position : Nat} {rule : ScopedNeedMachine.Rule}
    (selection : Selection origin position rule selected)
    (refs : Fin origin.k → Ref Head Effect StableFault NativeFault m)
    (agree : ∀ j, RefAgrees primitive cells world (origin.needs j) (refs j)) :
    ∀ j, RefAgrees primitive cells world (selected.needs j) (selectionRefs selection refs j) := by
  cases selection <;> exact agree

theorem selection_mem {origin selected : Closure Head Operation Effect m} {position : Nat}
    {rule : ScopedNeedMachine.Rule} (selection : Selection origin position rule selected)
    (refs : Fin origin.k → Ref Head Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    {result : WorldResult (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect}
    (member : result ∈ runWorldsAt
      (reading primitive selected.code selected.values (selectionRefs selection refs)).1 store
        (selectionBranch selection branch)) :
    result ∈ runWorldsAt (reading primitive origin.code origin.values refs).2 store branch := by
  cases selection with
  | entry notChoice =>
      rw [reading_snd_of_not_choose primitive _ _ _ notChoice]
      exact member
  | left l r values needs =>
      simp only [reading, runWorldsAt]
      exact List.mem_append_left _ member
  | right l r values needs =>
      simp only [reading, runWorldsAt]
      exact List.mem_append_right _ member

mutual

/-- **Every natural evaluation is witnessed by the reading.** -/
theorem eval_sound : {closure : Closure Head Operation Effect m} →
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} →
    {outcome : Outcome Head StableFault NativeFault m} →
    Eval primitive closure world outcome final → ¬ MachineRetry outcome →
    (cells : List CellId) → (store : Store Head StableFault NativeFault m) →
    (refs : Fin closure.k → Ref Head Effect StableFault NativeFault m) → (branch : BranchTrace) →
    StoreAgrees cells world store →
    (∀ j, RefAgrees primitive cells world (closure.needs j) (refs j)) →
    Witnessed cells world final outcome (reading primitive closure.code closure.values refs).1 store branch
  | _, _, _, _, .returnValue term values _ _, _, cells, store, _, branch, agrees, _ =>
      ⟨cells, ⟨branch, .value (subst values term), store, []⟩, List.prefix_refl _, agrees,
        Extends.refl _, by simp [reading, runWorldsAt], rfl⟩
  | _, _, _, _, .call operation argument values _ _, _, cells, store, _, branch, agrees, _ =>
      ⟨cells, ⟨branch, ScopedNeedMachine.liftOutcome (primitive operation (subst values argument)), store, []⟩,
        List.prefix_refl _, agrees, Extends.refl _, by simp [reading, runWorldsAt], rfl⟩
  | _, _, _, _, .emit effect nextDerivation, notRetry, cells, store, refs, branch, agrees, refsAgree => by
      obtain ⟨cells', result, isPrefix, agrees', extends', member, answer⟩ :=
        eval_sound nextDerivation notRetry cells store refs branch (agrees.of_heap rfl)
          (fun j => (refsAgree j).mono primitive (List.prefix_refl _) (Extends.of_heap rfl))
      refine ⟨cells', { result with intents := effect :: result.intents }, isPrefix, agrees',
        (Extends.of_heap rfl).trans extends', ?_, answer⟩
      simp only [reading, runWorldsAt]
      exact List.mem_map.mpr ⟨result, member, rfl⟩
  | _, _, _, _, .force reference forceDerivation, notRetry, cells, store, refs, branch, agrees, refsAgree =>
      force_sound forceDerivation notRetry cells store (refs reference) branch agrees (refsAgree reference)
  | _, _, _, _, .sequenceValue allocated forceDerivation bodyDerivation, notRetry, cells, store, refs, branch,
      agrees, refsAgree => by
      have agrees₁ := agrees.alloc allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation (by simp [MachineRetry]) _ _ _ branch agrees₁
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      obtain ⟨cells₃, second, prefix₃, agrees₃, extends₃, secondMember, secondAnswer⟩ :=
        eval_sound bodyDerivation notRetry cells₂ first.state refs first.branch agrees₂
          (fun j => (refsAgree j).mono primitive ((List.prefix_append _ _).trans prefix₂)
            ((Extends.alloc allocated).trans extends₂))
      refine ⟨cells₃, WorldResult.prependIntents first.intents second,
        ((List.prefix_append _ _).trans prefix₂).trans prefix₃, agrees₃,
        (Extends.alloc allocated).trans (extends₂.trans extends₃), ?_, secondAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      exact secondMember
  | _, _, _, _, .sequenceStable _ allocated forceDerivation, notRetry, cells, store, refs, branch,
      agrees, refsAgree => by
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation notRetry _ _ _ branch (agrees.alloc allocated)
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Extends.alloc allocated).trans extends₂, ?_,
        firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .sequenceRetry _ allocated forceDerivation, notRetry, cells, store, refs, branch,
      agrees, refsAgree => by
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation notRetry _ _ _ branch (agrees.alloc allocated)
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Extends.alloc allocated).trans extends₂, ?_,
        firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .sequenceSigmaValue (value := value) allocated forceDerivation bodyDerivation, notRetry, cells,
      store, refs, branch, agrees, refsAgree => by
      have agrees₁ := agrees.alloc allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation (by simp [MachineRetry]) _ _ _ branch agrees₁
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      obtain ⟨cells₃, second, prefix₃, agrees₃, extends₃, secondMember, secondAnswer⟩ :=
        eval_sound bodyDerivation (not_machineRetry_of_pair notRetry) cells₂ first.state refs first.branch
          agrees₂ (fun j => (refsAgree j).mono primitive ((List.prefix_append _ _).trans prefix₂)
            ((Extends.alloc allocated).trans extends₂))
      refine ⟨cells₃,
        WorldResult.prependIntents first.intents (WorldResult.mapAnswer (pairOutcome value) second),
        ((List.prefix_append _ _).trans prefix₂).trans prefix₃, agrees₃,
        (Extends.alloc allocated).trans (extends₂.trans extends₃), ?_, ?_⟩
      · simp only [reading]
        rw [alloc_run]
        refine mem_bind firstMember ?_
        rw [firstAnswer]
        simp only [onValue]
        rw [runWorldsAt_map]
        exact List.mem_map.mpr ⟨second, secondMember, rfl⟩
      · simp [WorldResult.prependIntents, WorldResult.mapAnswer, secondAnswer]
  | _, _, _, _, .sequenceSigmaStable _ allocated forceDerivation, notRetry, cells, store, refs, branch,
      agrees, refsAgree => by
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation notRetry _ _ _ branch (agrees.alloc allocated)
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Extends.alloc allocated).trans extends₂, ?_,
        firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .sequenceSigmaRetry _ allocated forceDerivation, notRetry, cells, store, refs, branch,
      agrees, refsAgree => by
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation notRetry _ _ _ branch (agrees.alloc allocated)
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Extends.alloc allocated).trans extends₂, ?_,
        firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .choose left right allocated forceDerivation, notRetry, cells, store, refs, branch,
      agrees, refsAgree => by
      obtain ⟨cells₂, first, prefix₂, agrees₂, extends₂, firstMember, firstAnswer⟩ :=
        force_sound forceDerivation notRetry _ _ _ branch (agrees.alloc allocated)
          (RefAgrees.fresh primitive agrees refsAgree allocated)
      refine ⟨cells₂, first, (List.prefix_append _ _).trans prefix₂, agrees₂,
        (Extends.alloc allocated).trans extends₂, ?_, firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      exact firstMember
  | _, _, _, _, .letNeed (suspended := suspended) (values := values) allocated bodyDerivation, notRetry, cells,
      store, refs, branch, agrees, refsAgree => by
      have agrees₁ := agrees.alloc allocated
      obtain ⟨cells₂, result, prefix₂, agrees₂, extends₂, member, answer⟩ :=
        eval_sound bodyDerivation notRetry _ _
          (Fin.cases (store.length, (reading primitive suspended values refs).2) refs) branch agrees₁ (by
          intro j
          refine Fin.cases ?_ (fun j' => ?_) j
          · exact RefAgrees.fresh primitive agrees refsAgree allocated
          · exact (refsAgree j').mono primitive (List.prefix_append _ _) (Extends.alloc allocated))
      refine ⟨cells₂, result, (List.prefix_append _ _).trans prefix₂, agrees₂,
        (Extends.alloc allocated).trans extends₂, ?_, answer⟩
      simp only [reading]
      rw [alloc_run]
      exact member
  | _, _, _, _, .sequenceAllocationFailure _ _, notRetry, _, _, _, _, _, _ =>
      absurd (by simp [retryResult, MachineRetry]) notRetry
  | _, _, _, _, .sequenceSigmaAllocationFailure _ _, notRetry, _, _, _, _, _, _ =>
      absurd (by simp [retryResult, MachineRetry]) notRetry
  | _, _, _, _, .chooseAllocationFailure _ _ _, notRetry, _, _, _, _, _, _ =>
      absurd (by simp [retryResult, MachineRetry]) notRetry
  | _, _, _, _, .letNeedAllocationFailure _ _, notRetry, _, _, _, _, _, _ =>
      absurd (by simp [retryResult, MachineRetry]) notRetry

/-- **Every natural force is witnessed by the demand of its reference.** -/
theorem force_sound : {cell : CellId} →
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} →
    {outcome : Outcome Head StableFault NativeFault m} →
    Force primitive cell world outcome final → ¬ MachineRetry outcome →
    (cells : List CellId) → (store : Store Head StableFault NativeFault m) →
    (ref : Ref Head Effect StableFault NativeFault m) → (branch : BranchTrace) →
    StoreAgrees cells world store → RefAgrees primitive cells world cell ref →
    Witnessed cells world final outcome (demand ref.1 ref.2) store branch
  | _, _, _, _, .cachedValue present, _, cells, store, _, branch, agrees,
      .intro index located _ _ _ _ _ => by
      have cached := (agrees.cached located present).of_value
      exact ⟨cells, ⟨branch, _, store, []⟩, List.prefix_refl _, agrees.of_heap rfl, Extends.of_heap rfl,
        by rw [demand_cached _ _ store branch _ cached]; exact List.mem_singleton_self _, rfl⟩
  | _, _, _, _, .cachedStable present, _, cells, store, _, branch, agrees,
      .intro index located _ _ _ _ _ => by
      have cached := (agrees.cached located present).of_stableFault
      exact ⟨cells, ⟨branch, _, store, []⟩, List.prefix_refl _, agrees.of_heap rfl, Extends.of_heap rfl,
        by rw [demand_cached _ _ store branch _ cached]; exact List.mem_singleton_self _, rfl⟩
  | _, _, _, _, .missing _, notRetry, _, _, _, _, _, _ =>
      absurd (by simp [MachineRetry]) notRetry
  | _, _, _, _, .evaluating _, notRetry, _, _, _, _, _, _ =>
      absurd (by simp [MachineRetry]) notRetry
  | cell, world, _, _, .suspended (origin := origin) (position := position) (rule := rule)
      (bodyFinal := bodyFinal) (bodyOutcome := bodyOutcome) present selection bodyDerivation,
      notRetry, cells, store, _, branch, agrees,
      .intro index located origin' cache refs record children => by
      rw [present] at record
      cases record
      have pending := (agrees.cached located present).none_of_suspended
      obtain ⟨found, foundPresent, owned, outcomeEq, heapEq⟩ := finalize_owned notRetry
      have bodyNotRetry : ¬ MachineRetry bodyOutcome := outcomeEq ▸ notRetry
      have agreesEnter := agrees.enter present position rule
      have childrenEnter := fun j => (children j).mono primitive (List.prefix_refl _)
        (Extends.enter present position rule)
      obtain ⟨cells₁, first, isPrefix, agrees₁, extends₁, selectedMember, answer⟩ :=
        eval_sound bodyDerivation bodyNotRetry cells store (selectionRefs selection refs)
          (selectionBranch selection branch) agreesEnter
          (selection_refsAgree primitive selection refs childrenEnter)
      have member := selection_mem primitive selection refs store branch selectedMember
      have located₁ := prefix_getElem? isPrefix located
      have pending₁ : first.state.getD index none = none := by
        have := agrees₁.cached located₁ foundPresent
        rw [owned] at this
        exact this.none_of_evaluating
      have bound : index < first.state.length := by
        rw [← agrees₁.length]
        exact (List.getElem?_eq_some_iff.mp located₁).1
      refine ⟨cells₁,
        WorldResult.prependIntents first.intents
          ⟨first.branch, bodyOutcome, settled index bodyOutcome first.state, []⟩,
        isPrefix, ?_, ?_, ?_, outcomeEq.symm⟩
      · refine StoreAgrees.of_heap ?_ heapEq
        exact agrees₁.replace (record := found) located₁ (cacheOf bodyOutcome) (settled_length _ _ _)
          (settled_agrees index bodyOutcome first.state bound pending₁)
          (fun other different => settled_other index other different _ _)
      · exact (Extends.enter present position rule).trans
          (extends₁.trans ((Extends.setKnownCache foundPresent _).trans (Extends.of_heap heapEq)))
      · rw [demand_pending _ _ store branch pending]
        refine mem_bind member ?_
        rw [answer, settle_run]
        exact List.mem_singleton_self _

end

/-- **Closed code: every natural outcome is an answer of the reading.**  From
any world, a derivation of closed code whose outcome is not a machine-owned
retry answers that outcome in some world of the reading from the empty store. -/
theorem closed_sound {code : Code Head Operation Effect 0 0} {values : Sub Head 0 m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (derivation : Eval primitive ⟨0, 0, code, values, Fin.elim0⟩ world outcome final)
    (notRetry : ¬ MachineRetry outcome) :
    outcome ∈ answers (Effect := Effect) primitive code values := by
  obtain ⟨_, result, _, _, _, member, answer⟩ :=
    eval_sound primitive derivation notRetry [] [] Fin.elim0 [] ⟨rfl, List.nodup_nil, by simp⟩
      (fun j => j.elim0)
  exact List.mem_map.mpr ⟨result, member, answer⟩

#print axioms eval_sound
#print axioms force_sound
#print axioms closed_sound

end Mettapedia.TypeTheory.ContextualCBPV.ScopedNeed
