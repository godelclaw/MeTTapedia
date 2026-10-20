import Mettapedia.TypeTheory.ContextualCBPVPolarizedValues

/-!
# Need cells inside the higher-order agreement

`ContextualCBPVPolarizedValues` reads PolarizedNeed's value layer at its
shapes and proves, by a logical relation, that every natural outcome of a
computation without need cells is an answer of the reading.  This module
adds the need cells.

A need cell is shared: its first demand runs its producer and caches the
answer, and later demands read the cache.  So the relation now runs from a
store that agrees with the heap and ends in a store that agrees with the
final heap (`StoreAgrees`).  Each store position is tracked (`Tracked`):
either a need cell with its origin, whose cache must agree with the store's
entry, or a cell of sequencing or choice, which nothing reads again.  The
relation (`RelValue`, `GoodFrom`, `Good`) is a Kripke relation over the
tracked positions, and a value stays related when more cells are tracked.  A
reference is related to its cell (`RelRef`) when every derivation of a
selected occurrence of the cell's origin is good for the reference's
producer.  `letNeed` establishes this for the cell it allocates, by the
fundamental lemma on its suspended computation; `forceNeed` uses it, through
the cached entry or through the producer (`forced_need`).

**Choices between functions.**  A choice's cell caches the function its
alternative answers, and the function is applied only after the cell is
finalized, from a heap that the alternative's own derivation never reaches.
So at a function shape the relation reads every application from any world
alike but at cells of sequencing or choice (`Similar`, `NonNeed`), which
nothing reads again: agreement with the store survives such a change
(`StoreAgrees.similar`), and so does goodness (`GoodFrom.similar`).  The
force of a choice's cell is then good at every shape (`forced_selected`).

**The result** (`sound`).  Take a closed native returner, evaluated from any
world.  Every natural outcome other than a retry the machine raises itself is
an answer of the reading.  This covers need cells, first-class thunks, value
and native lambdas, packages, sequencing, and choice at every shape.
`Examples.sharedInThunk_natural` and `Examples.sharedInThunk_no_mixed` apply
it to a need cell that a thunk captures and forces twice, and
`Examples.needChoice_natural` to a choice between functions, one of which
forces a need cell.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.PolarizedNeedCells

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open PolarizedValues
open PolarizedValues.Shaped
open PolarizedNeedMachine (RuntimeValue)
open PolarizedNeedNaturalSemantics (Eval Force Selection)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-! ## Tracked positions and store agreement -/

/-- The cell of each store position, with its origin when it is a need cell. -/
abbrev Tracked (Head Operation Effect : Type) (m : Nat) :=
  List (CellId × Option (PolarizedNeedMachine.Closure Head Operation Effect m))

/-- The cache of a need cell and its store entry agree.  A cell being
evaluated is pending in the store. -/
inductive CacheAgrees :
    Cache (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault →
      Option (ScopedNeed.Outcome Head StableFault NativeFault m) → Prop where
  | suspended : CacheAgrees .suspended none
  | evaluating (owner : EvaluatorId) : CacheAgrees (.evaluating owner) none
  | value (term : Tm Head m) : CacheAgrees (.value (.returned (.native term))) (some (.value term))
  | stableFault (fault : StableFault) : CacheAgrees (.stableFault fault) (some (.stableFault fault))

/-- The store has a position for every tracked cell, the cells are distinct
cells of the heap, and a need cell keeps its origin and a cache that agrees
with its entry. -/
structure StoreAgrees (tracked : Tracked Head Operation Effect m)
    (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (store : ScopedNeed.Store Head StableFault NativeFault m) : Prop where
  length : tracked.length = store.length
  distinct : (tracked.map Prod.fst).Nodup
  present : ∀ (index : Nat) (cell : CellId) (kind : Option (PolarizedNeedMachine.Closure Head Operation Effect m)),
    tracked[index]? = some (cell, kind) → ∃ record, world.heap.lookup cell = some record
  caches : ∀ (index : Nat) (cell : CellId) (origin : PolarizedNeedMachine.Closure Head Operation Effect m),
    tracked[index]? = some (cell, some origin) →
      ∃ cache, world.heap.lookup cell = some ⟨origin, cache⟩ ∧ CacheAgrees cache (store.getD index none)

theorem StoreAgrees.of_heap {tracked : Tracked Head Operation Effect m}
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : ScopedNeed.Store Head StableFault NativeFault m} (agrees : StoreAgrees tracked world store)
    (same : next.heap = world.heap) : StoreAgrees tracked next store :=
  ⟨agrees.length, agrees.distinct, fun index cell kind located => by rw [same]; exact agrees.present index cell kind located,
    fun index cell origin located => by rw [same]; exact agrees.caches index cell origin located⟩

/-- The empty store agrees with every heap. -/
theorem StoreAgrees.empty (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m) :
    StoreAgrees ([] : Tracked Head Operation Effect m) world ([] : ScopedNeed.Store Head StableFault NativeFault m) :=
  ⟨rfl, List.nodup_nil, fun _ _ _ located => by simp at located, fun _ _ _ located => by simp at located⟩

/-- Allocation adds a fresh suspended cell and changes no other. -/
theorem allocate_spec {Origin Rule Value StableFault' RetryableFault Effect' : Type}
    {world next : World Origin Rule Value StableFault' RetryableFault Effect'} {origin : Origin} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) :
    world.heap.lookup cell = none ∧ next.heap.lookup cell = some ⟨origin, .suspended⟩ ∧
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

theorem prefix_getElem {α : Type} {list list' : List α} (isPrefix : list <+: list') {index : Nat} {entry : α}
    (located : list[index]? = some entry) : list'[index]? = some entry := by
  obtain ⟨tail, rfl⟩ := isPrefix
  have bound : index < list.length := (List.getElem?_eq_some_iff.mp located).1
  rw [List.getElem?_append_left bound]
  exact located

theorem getElem?_append_tracked {tracked : Tracked Head Operation Effect m}
    {entry : CellId × Option (PolarizedNeedMachine.Closure Head Operation Effect m)} {index : Nat}
    {found : CellId × Option (PolarizedNeedMachine.Closure Head Operation Effect m)}
    (located : (tracked ++ [entry])[index]? = some found) :
    tracked[index]? = some found ∨ (index = tracked.length ∧ found = entry) := by
  by_cases inside : index < tracked.length
  · left; rw [List.getElem?_append_left inside] at located; exact located
  · right
    have atLeast : tracked.length ≤ index := Nat.le_of_not_lt inside
    rw [List.getElem?_append_right atLeast] at located
    cases difference : index - tracked.length with
    | zero =>
        rw [difference] at located
        simp at located
        exact ⟨by omega, located.symm⟩
    | succ _ => rw [difference] at located; simp at located

/-- Allocation extends the agreement by the new cell, pending in the store. -/
theorem StoreAgrees.alloc {tracked : Tracked Head Operation Effect m}
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : ScopedNeed.Store Head StableFault NativeFault m} (agrees : StoreAgrees tracked world store)
    {origin : PolarizedNeedMachine.Closure Head Operation Effect m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) (need : Bool) :
    StoreAgrees (tracked ++ [(cell, if need then some origin else none)]) next (store ++ [none]) := by
  obtain ⟨absent, present, others⟩ := allocate_spec allocated
  have different : ∀ (index : Nat) (other : CellId) (kind : Option (PolarizedNeedMachine.Closure Head Operation Effect m)),
      tracked[index]? = some (other, kind) → other ≠ cell := by
    intro index other kind located equal
    subst equal
    obtain ⟨_, found⟩ := agrees.present index other kind located
    rw [absent] at found
    cases found
  refine ⟨by simp only [List.length_append, List.length_singleton, agrees.length], ?_, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨agrees.distinct, List.nodup_singleton _, ?_⟩
    intro other otherMember fresh freshMember
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at freshMember
    subst freshMember
    obtain ⟨⟨other', kind⟩, member, rfl⟩ := List.mem_map.mp otherMember
    obtain ⟨index, located⟩ := List.getElem?_of_mem member
    exact different index other' kind located
  · intro index other kind located
    rcases getElem?_append_tracked located with old | ⟨_, equal⟩
    · rw [others other (different index other kind old)]
      exact agrees.present index other kind old
    · cases equal
      exact ⟨_, present⟩
  · intro index other origin' located
    rcases getElem?_append_tracked located with old | ⟨atEnd, equal⟩
    · obtain ⟨cache, found, cacheAgrees⟩ := agrees.caches index other origin' old
      have bound : index < store.length := by
        rw [← agrees.length]; exact (List.getElem?_eq_some_iff.mp old).1
      refine ⟨cache, by rw [others other (different index other _ old)]; exact found, ?_⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left bound]
      simpa only [List.getD_eq_getElem?_getD] using cacheAgrees
    · cases need with
      | false => simp at equal
      | true =>
          simp only [if_true, Prod.mk.injEq, Option.some.injEq] at equal
          obtain ⟨rfl, rfl⟩ := equal
          refine ⟨.suspended, present, ?_⟩
          rw [atEnd, agrees.length]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some]
          exact .suspended

theorem tracked_index_unique {tracked : Tracked Head Operation Effect m} (distinct : (tracked.map Prod.fst).Nodup)
    {index index' : Nat} {cell : CellId} {kind kind' : Option (PolarizedNeedMachine.Closure Head Operation Effect m)}
    (first : tracked[index]? = some (cell, kind)) (second : tracked[index']? = some (cell, kind')) :
    index = index' := by
  have bound : index < (tracked.map Prod.fst).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp first).1
  refine (List.getElem?_inj bound distinct).mp ?_
  rw [List.getElem?_map, List.getElem?_map, first, second]
  rfl

theorem enterWorld_lookup (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell other : CellId) (origin : PolarizedNeedMachine.Closure Head Operation Effect m) (position : Nat)
    (rule : PolarizedNeedMachine.Rule) :
    (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).heap.lookup other =
      if other = cell then some ⟨origin, .evaluating world.nextEvaluator⟩ else world.heap.lookup other := by
  simp only [PolarizedNeedNaturalSemantics.enterWorld, World.record, World.setKnownCache, World.fork]
  rw [ScopedNeed.lookup_setKnownCache]

/-- Entering a suspended cell keeps the agreement: the cell is pending in the
store either way. -/
theorem StoreAgrees.enter {tracked : Tracked Head Operation Effect m}
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : ScopedNeed.Store Head StableFault NativeFault m} (agrees : StoreAgrees tracked world store)
    {cell : CellId} {origin : PolarizedNeedMachine.Closure Head Operation Effect m}
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩) (position : Nat) (rule : PolarizedNeedMachine.Rule) :
    StoreAgrees tracked (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) store := by
  refine ⟨agrees.length, agrees.distinct, ?_, ?_⟩
  · intro index other kind located
    rw [enterWorld_lookup]
    by_cases same : other = cell
    · rw [if_pos same]; exact ⟨_, rfl⟩
    · rw [if_neg same]; exact agrees.present index other kind located
  · intro index other origin' located
    obtain ⟨cache, found, cacheAgrees⟩ := agrees.caches index other origin' located
    rw [enterWorld_lookup]
    by_cases same : other = cell
    · subst same
      rw [present] at found
      cases found
      rw [if_pos rfl]
      refine ⟨_, rfl, ?_⟩
      generalize store.getD index none = entry at cacheAgrees ⊢
      cases cacheAgrees
      exact .evaluating _
    · rw [if_neg same]; exact ⟨cache, found, cacheAgrees⟩

/-- The cache a finalized cell keeps. -/
def cacheOf : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
    Cache (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault
  | .value answer => .value answer
  | .stableFault fault => .stableFault fault
  | .retryableFault _ => .suspended

/-- Finalization raises a retry of the machine, or the cell's owner caches the
producer's outcome and answers it. -/
theorem finalize_cases (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (owner : EvaluatorId)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    MachineRaised (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).1 ∨
      ∃ origin, world.heap.lookup cell = some ⟨origin, .evaluating owner⟩ ∧
        (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).1 = outcome ∧
        (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2.heap =
          world.heap.setKnownCache cell ⟨origin, .evaluating owner⟩ (cacheOf outcome) := by
  unfold PolarizedNeedNaturalSemantics.finalize
  split
  · left; simp [PolarizedNeedNaturalSemantics.retryResult, MachineRaised]
  · rename_i record found
    split
    · rename_i actual evaluating
      by_cases owned : actual = owner
      · subst owned
        right
        refine ⟨record.origin, ?_, ?_, ?_⟩
        · rw [found]; cases record; simp_all
        · simp only [if_true]; cases outcome <;> rfl
        · simp only [if_true]
          cases record
          simp only at evaluating
          subst evaluating
          cases outcome <;> rfl
      · left; simp [PolarizedNeedNaturalSemantics.retryResult, MachineRaised, owned]
    · left; simp [PolarizedNeedNaturalSemantics.retryResult, MachineRaised]

/-- Replacing one cell's cache, and the store's entries at its position, keeps
the agreement. -/
theorem StoreAgrees.replace {tracked : Tracked Head Operation Effect m}
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {store store' : ScopedNeed.Store Head StableFault NativeFault m} (agrees : StoreAgrees tracked world store)
    {index : Nat} {cell : CellId} {kind : Option (PolarizedNeedMachine.Closure Head Operation Effect m)}
    (located : tracked[index]? = some (cell, kind))
    {record : CellRecord (PolarizedNeedMachine.Closure Head Operation Effect m)
      (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault}
    (state : Cache (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault)
    (heap : next.heap = world.heap.setKnownCache cell record state)
    (length : store'.length = store.length)
    (others : ∀ other, other ≠ index → store'.getD other none = store.getD other none)
    (entry : ∀ origin, kind = some origin → record.origin = origin ∧ CacheAgrees state (store'.getD index none)) :
    StoreAgrees tracked next store' := by
  refine ⟨agrees.length.trans length.symm, agrees.distinct, ?_, ?_⟩
  · intro index' other kind' located'
    rw [heap, ScopedNeed.lookup_setKnownCache]
    by_cases same : other = cell
    · rw [if_pos same]; exact ⟨_, rfl⟩
    · rw [if_neg same]; exact agrees.present index' other kind' located'
  · intro index' other origin' located'
    rw [heap, ScopedNeed.lookup_setKnownCache]
    by_cases same : other = cell
    · subst same
      have sameIndex := tracked_index_unique agrees.distinct located located'
      subst sameIndex
      rw [located] at located'
      cases located'
      obtain ⟨originEq, cacheAgrees⟩ := entry origin' rfl
      rw [if_pos rfl]
      refine ⟨state, ?_, cacheAgrees⟩
      rw [← originEq]
    · rw [if_neg same]
      have different : index' ≠ index := by
        intro equal; subst equal; rw [located] at located'; cases located'; exact same rfl
      obtain ⟨cache, found, cacheAgrees⟩ := agrees.caches index' other origin' located'
      exact ⟨cache, found, by rw [others index' different]; exact cacheAgrees⟩

/-! ## Worlds alike but at cells of sequencing or choice -/

/-- A cell tracked as a cell of sequencing or choice, which nothing reads
again. -/
def NonNeed (tracked : Tracked Head Operation Effect m) (cell : CellId) : Prop :=
  ∃ index : Nat, tracked[index]? = some (cell, (none : Option (PolarizedNeedMachine.Closure Head Operation Effect m)))

theorem NonNeed.mono {tracked tracked' : Tracked Head Operation Effect m} (isPrefix : tracked <+: tracked')
    {cell : CellId} (nonNeed : NonNeed tracked cell) : NonNeed tracked' cell := by
  obtain ⟨index, located⟩ := nonNeed
  exact ⟨index, prefix_getElem isPrefix located⟩

/-- Two worlds alike but at some cells, which both hold. -/
structure Similar (cells : List CellId)
    (world world' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m) : Prop where
  same : ∀ cell, cell ∉ cells → world'.heap.lookup cell = world.heap.lookup cell
  held : ∀ cell ∈ cells, (∃ record, world.heap.lookup cell = some record) ∧
    ∃ record, world'.heap.lookup cell = some record

theorem Similar.refl (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m) :
    Similar [] world world :=
  ⟨fun _ _ => rfl, fun _ member => nomatch member⟩

theorem Similar.trans {cells cells' : List CellId}
    {world middle final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (first : Similar cells world middle) (second : Similar cells' middle final) :
    Similar (cells ++ cells') world final := by
  refine ⟨fun cell outside => ?_, fun cell member => ?_⟩
  · have outsideFirst : cell ∉ cells := fun member => outside (List.mem_append_left _ member)
    have outsideSecond : cell ∉ cells' := fun member => outside (List.mem_append_right _ member)
    rw [second.same cell outsideSecond, first.same cell outsideFirst]
  · by_cases inSecond : cell ∈ cells'
    · by_cases inFirst : cell ∈ cells
      · exact ⟨(first.held cell inFirst).1, (second.held cell inSecond).2⟩
      · refine ⟨?_, (second.held cell inSecond).2⟩
        rw [← first.same cell inFirst]
        exact (second.held cell inSecond).1
    · have inFirst : cell ∈ cells := by
        rcases List.mem_append.mp member with inFirst | inSecond'
        · exact inFirst
        · exact absurd inSecond' inSecond
      refine ⟨(first.held cell inFirst).1, ?_⟩
      rw [second.same cell inSecond]
      exact (first.held cell inFirst).2

/-- **Agreement survives a change at cells of sequencing or choice.** -/
theorem StoreAgrees.similar {tracked : Tracked Head Operation Effect m}
    {world world' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : ScopedNeed.Store Head StableFault NativeFault m} (agrees : StoreAgrees tracked world store)
    {cells : List CellId} (similar : Similar cells world world') (nonNeed : ∀ cell ∈ cells, NonNeed tracked cell) :
    StoreAgrees tracked world' store := by
  refine ⟨agrees.length, agrees.distinct, fun index cell kind located => ?_, fun index cell origin located => ?_⟩
  · by_cases member : cell ∈ cells
    · exact (similar.held cell member).2
    · rw [similar.same cell member]
      exact agrees.present index cell kind located
  · have outside : cell ∉ cells := by
      intro member
      obtain ⟨index', located'⟩ := nonNeed cell member
      have sameIndex := tracked_index_unique agrees.distinct located located'
      subst sameIndex
      rw [located] at located'
      cases located'
    rw [similar.same cell outside]
    exact agrees.caches index cell origin located

/-- Finalizing a cell changes no other. -/
theorem finalize_similar (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) {origin : PolarizedNeedMachine.Closure Head Operation Effect m} {owner : EvaluatorId}
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m)
    (owned : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩)
    (heap : (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2.heap =
      world.heap.setKnownCache cell ⟨origin, .evaluating owner⟩ (cacheOf outcome)) :
    Similar [cell] world (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2 := by
  refine ⟨fun other outside => ?_, fun other member => ?_⟩
  · have different : other ≠ cell := fun equal => outside (equal ▸ List.mem_singleton_self _)
    rw [heap, ScopedNeed.lookup_setKnownCache, if_neg different]
  · rw [List.mem_singleton] at member
    subst member
    refine ⟨⟨_, owned⟩, ⟨origin, cacheOf outcome⟩, ?_⟩
    rw [heap, ScopedNeed.lookup_setKnownCache, if_pos rfl]

/-! ## The relation -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

mutual
  /-- A run-time value and a value of the reading agree at a shape, for the
  tracked positions. -/
  def RelValue : (shape : VShape) → Tracked Head Operation Effect m → RuntimeValue Head Operation Effect m →
      SemValue Head Effect StableFault NativeFault m shape → Prop
    | .native, _, value, semantic => value = .native semantic
    | .thunk shape, tracked, value, semantic =>
        ∃ (n v k : Nat) (code : PolarizedNeed.Computation Head Operation Effect n v k) (native : Sub Head n m)
          (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId),
          value = .thunk code native values needs ∧
            ∀ world outcome final, Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final →
              ∀ (tracked' : Tracked Head Operation Effect m) (store : ScopedNeed.Store Head StableFault NativeFault m)
                (branch : BranchTrace), tracked <+: tracked' → StoreAgrees tracked' world store →
                GoodFrom shape tracked' outcome semantic final store branch
    | .pack payload, tracked, value, semantic =>
        ∃ inner, value = .packNative semantic.1 inner ∧ RelValue payload tracked inner semantic.2

  /-- A natural outcome, reached in `final`, is good for a computation of the
  reading run from `store`.  For a returner: the machine raised a retry of its
  own, or a world of the reading answers the outcome and ends in a store that
  agrees with `final`.  For a function: every application is good. -/
  def GoodFrom : (shape : CShape) → Tracked Head Operation Effect m →
      PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
      SemComputation Head Effect StableFault NativeFault m shape →
      PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m →
      ScopedNeed.Store Head StableFault NativeFault m → BranchTrace → Prop
    | .returns answer, tracked, outcome, program, final, store, branch =>
        MachineRaised outcome ∨
          ∃ (tracked'' : Tracked Head Operation Effect m)
            (result : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
              (Produced (SemValue Head Effect StableFault NativeFault m answer) StableFault
                (ScopedNeedMachine.Fault NativeFault)) Effect),
            tracked <+: tracked'' ∧ result ∈ runWorldsAt program store branch ∧
              StoreAgrees tracked'' final result.state ∧
              match outcome, result.answer with
              | .value (.returned value), .value semantic => RelValue answer tracked'' value semantic
              | .stableFault fault, .stableFault fault' => fault = fault'
              | .retryableFault reason, .retryableFault reason' => reason = PolarizedNeedEmbedding.retry reason'
              | _, _ => False
    | .nativePi shape, tracked, outcome, function, final, store, branch =>
        ∀ argument,
          match outcome with
          | .value (.nativeFunction body) =>
              ∀ (cells : List CellId) (start : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault
                NativeFault m), Similar cells final start → (∀ cell ∈ cells, NonNeed tracked cell) →
                ∀ outcome' final', Eval primitive (body.open argument) start outcome' final' →
                  GoodFrom shape tracked outcome' (function argument) final' store branch
          | .value _ => False
          | fault => GoodFrom shape tracked fault (function argument) final store branch
    | .arrow domain shape, tracked, outcome, function, final, store, branch =>
        ∀ argument semantic, RelValue domain tracked argument semantic →
          match outcome with
          | .value (.valueFunction body) =>
              ∀ (cells : List CellId) (start : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault
                NativeFault m), Similar cells final start → (∀ cell ∈ cells, NonNeed tracked cell) →
                ∀ outcome' final', Eval primitive (body.open argument) start outcome' final' →
                  GoodFrom shape tracked outcome' (function semantic) final' store branch
          | .value _ => False
          | fault => GoodFrom shape tracked fault (function semantic) final store branch
end

/-- A natural outcome and an answer of the reading agree. -/
def RelOutcome (answer : VShape) (tracked : Tracked Head Operation Effect m) :
    PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
      Produced (SemValue Head Effect StableFault NativeFault m answer) StableFault
        (ScopedNeedMachine.Fault NativeFault) → Prop
  | .value (.returned value), .value semantic => RelValue primitive answer tracked value semantic
  | .stableFault fault, .stableFault fault' => fault = fault'
  | .retryableFault reason, .retryableFault reason' => reason = PolarizedNeedEmbedding.retry reason'
  | _, _ => False

/-- Good from every store that agrees with the starting heap. -/
def Good (shape : CShape) (tracked : Tracked Head Operation Effect m)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m)
    (semantic : SemComputation Head Effect StableFault NativeFault m shape)
    (world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  ∀ (tracked' : Tracked Head Operation Effect m) (store : ScopedNeed.Store Head StableFault NativeFault m)
    (branch : BranchTrace), tracked <+: tracked' → StoreAgrees tracked' world store →
    GoodFrom primitive shape tracked' outcome semantic final store branch

theorem Good.mono {shape : CShape} {tracked tracked' : Tracked Head Operation Effect m} (isPrefix : tracked <+: tracked')
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {semantic : SemComputation Head Effect StableFault NativeFault m shape}
    {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (good : Good primitive shape tracked outcome semantic world final) :
    Good primitive shape tracked' outcome semantic world final :=
  fun tracked'' store branch isPrefix' agrees => good tracked'' store branch (isPrefix.trans isPrefix') agrees

theorem RelValue.mono : (shape : VShape) → {tracked tracked' : Tracked Head Operation Effect m} →
    tracked <+: tracked' → {value : RuntimeValue Head Operation Effect m} →
    {semantic : SemValue Head Effect StableFault NativeFault m shape} →
    RelValue primitive shape tracked value semantic → RelValue primitive shape tracked' value semantic
  | .native, _, _, _, _, _, related => related
  | .thunk _, _, _, isPrefix, _, _, ⟨n, v, k, code, native, values, needs, equal, good⟩ =>
      ⟨n, v, k, code, native, values, needs, equal, fun world outcome final derivation tracked'' store branch
        isPrefix' agrees => good world outcome final derivation tracked'' store branch (isPrefix.trans isPrefix') agrees⟩
  | .pack payload, _, _, isPrefix, _, _, ⟨inner, equal, related⟩ =>
      ⟨inner, equal, RelValue.mono payload isPrefix related⟩

/-- A retry the machine raises is good for anything. -/
theorem GoodFrom.raised : (shape : CShape) → {tracked : Tracked Head Operation Effect m} →
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
    {semantic : SemComputation Head Effect StableFault NativeFault m shape} →
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    MachineRaised outcome → GoodFrom primitive shape tracked outcome semantic final store branch
  | .returns _, _, _, _, _, _, _, raised => .inl raised
  | .nativePi shape, _, outcome, _, _, _, _, raised => fun _ => by
      cases outcome with
      | value _ => exact raised.elim
      | stableFault _ => exact raised.elim
      | retryableFault _ => exact GoodFrom.raised shape raised
  | .arrow _ shape, _, outcome, _, _, _, _, raised => fun _ _ _ => by
      cases outcome with
      | value _ => exact raised.elim
      | stableFault _ => exact raised.elim
      | retryableFault _ => exact GoodFrom.raised shape raised

/-- **Running a program first keeps an outcome good**, when a world of the
program continues into a good run. -/
theorem GoodFrom.bind : (shape : CShape) → {Other : Type} → {tracked : Tracked Head Operation Effect m} →
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
    (program : Program (ScopedNeed.Store Head StableFault NativeFault m) Other Effect) →
    (next : Other → SemComputation Head Effect StableFault NativeFault m shape) →
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    (∃ prior ∈ runWorldsAt program store branch, ∃ tracked₂, tracked <+: tracked₂ ∧
      GoodFrom primitive shape tracked₂ outcome (next prior.answer) final prior.state prior.branch) →
    GoodFrom primitive shape tracked outcome (bindAt shape program next) final store branch
  | .returns _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, .inl raised⟩ => .inl raised
  | .returns _, _, _, _, _, _, _, _, _, ⟨_, member, _, isPrefix, .inr ⟨tracked'', _, isPrefix', resultMember, agrees,
      related⟩⟩ =>
      .inr ⟨tracked'', _, isPrefix.trans isPrefix', ScopedNeed.mem_bind member resultMember, agrees, related⟩
  | .nativePi shape, _, _, outcome, program, next, _, _, _, ⟨prior, member, tracked₂, isPrefix, good⟩ =>
      fun argument => by
        have atArgument := good argument
        cases outcome with
        | value answer =>
            cases answer with
            | nativeFunction body =>
                exact fun cells start similar nonNeed outcome' final' derivation =>
                  GoodFrom.bind shape program (fun other => next other argument)
                    ⟨prior, member, tracked₂, isPrefix, atArgument cells start similar
                      (fun cell member => (nonNeed cell member).mono isPrefix) outcome' final' derivation⟩
            | returned _ => exact atArgument.elim
            | valueFunction _ => exact atArgument.elim
        | stableFault _ =>
            exact GoodFrom.bind shape program (fun other => next other argument)
              ⟨prior, member, tracked₂, isPrefix, atArgument⟩
        | retryableFault _ =>
            exact GoodFrom.bind shape program (fun other => next other argument)
              ⟨prior, member, tracked₂, isPrefix, atArgument⟩
  | .arrow _ shape, _, _, outcome, program, next, _, _, _, ⟨prior, member, tracked₂, isPrefix, good⟩ =>
      fun argument semantic related => by
        have atArgument := good argument semantic (RelValue.mono primitive _ isPrefix related)
        cases outcome with
        | value answer =>
            cases answer with
            | valueFunction body =>
                exact fun cells start similar nonNeed outcome' final' derivation =>
                  GoodFrom.bind shape program (fun other => next other semantic)
                    ⟨prior, member, tracked₂, isPrefix, atArgument cells start similar
                      (fun cell member => (nonNeed cell member).mono isPrefix) outcome' final' derivation⟩
            | returned _ => exact atArgument.elim
            | nativeFunction _ => exact atArgument.elim
        | stableFault _ =>
            exact GoodFrom.bind shape program (fun other => next other semantic)
              ⟨prior, member, tracked₂, isPrefix, atArgument⟩
        | retryableFault _ =>
            exact GoodFrom.bind shape program (fun other => next other semantic)
              ⟨prior, member, tracked₂, isPrefix, atArgument⟩

theorem GoodFrom.failStable : (shape : CShape) → (fault : StableFault) → {tracked : Tracked Head Operation Effect m} →
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    StoreAgrees tracked final store →
    GoodFrom primitive shape tracked (.stableFault fault)
      (failAt (Head := Head) (Effect := Effect) shape (.stableFault fault)) final store branch
  | .returns _, _, _, _, _, _, agrees => .inr ⟨_, _, List.prefix_refl _, List.mem_singleton_self _, agrees, rfl⟩
  | .nativePi shape, fault, _, _, _, _, agrees => fun _ => GoodFrom.failStable shape fault agrees
  | .arrow _ shape, fault, _, _, _, _, agrees => fun _ _ _ => GoodFrom.failStable shape fault agrees

theorem GoodFrom.failRetry : (shape : CShape) → (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) →
    {tracked : Tracked Head Operation Effect m} →
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    StoreAgrees tracked final store →
    GoodFrom primitive shape tracked (.retryableFault (PolarizedNeedEmbedding.retry reason))
      (failAt (Head := Head) (Effect := Effect) shape (.retryableFault reason)) final store branch
  | .returns _, _, _, _, _, _, agrees => .inr ⟨_, _, List.prefix_refl _, List.mem_singleton_self _, agrees, rfl⟩
  | .nativePi shape, reason, _, _, _, _, agrees => fun _ => GoodFrom.failRetry shape reason agrees
  | .arrow _ shape, reason, _, _, _, _, agrees => fun _ _ _ => GoodFrom.failRetry shape reason agrees

/-- **A good outcome stays good in a world alike but at cells of sequencing
or choice.** -/
theorem GoodFrom.similar : (shape : CShape) → {tracked : Tracked Head Operation Effect m} →
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
    {semantic : SemComputation Head Effect StableFault NativeFault m shape} →
    {final final₁ : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    {cells : List CellId} → Similar cells final final₁ → (∀ cell ∈ cells, NonNeed tracked cell) →
    GoodFrom primitive shape tracked outcome semantic final store branch →
    GoodFrom primitive shape tracked outcome semantic final₁ store branch
  | .returns _, _, _, _, _, _, _, _, _, _, _, .inl raised => .inl raised
  | .returns _, _, _, _, _, _, _, _, _, similar, nonNeed, .inr ⟨tracked'', result, isPrefix, member, agrees, related⟩ =>
      .inr ⟨tracked'', result, isPrefix, member,
        agrees.similar similar (fun cell inCells => (nonNeed cell inCells).mono isPrefix), related⟩
  | .nativePi shape, _, outcome, _, _, _, _, _, _, similar, nonNeed, good => fun argument => by
      have atArgument := good argument
      cases outcome with
      | value answer =>
          cases answer with
          | nativeFunction body =>
              exact fun cells' start similar' nonNeed' outcome' final' derivation =>
                atArgument _ start (similar.trans similar') (fun cell member => by
                  rcases List.mem_append.mp member with member | member
                  · exact nonNeed cell member
                  · exact nonNeed' cell member) outcome' final' derivation
          | returned _ => exact atArgument.elim
          | valueFunction _ => exact atArgument.elim
      | stableFault _ => exact GoodFrom.similar shape similar nonNeed atArgument
      | retryableFault _ => exact GoodFrom.similar shape similar nonNeed atArgument
  | .arrow _ shape, _, outcome, _, _, _, _, _, _, similar, nonNeed, good => fun argument semantic related => by
      have atArgument := good argument semantic related
      cases outcome with
      | value answer =>
          cases answer with
          | valueFunction body =>
              exact fun cells' start similar' nonNeed' outcome' final' derivation =>
                atArgument _ start (similar.trans similar') (fun cell member => by
                  rcases List.mem_append.mp member with member | member
                  · exact nonNeed cell member
                  · exact nonNeed' cell member) outcome' final' derivation
          | returned _ => exact atArgument.elim
          | nativeFunction _ => exact atArgument.elim
      | stableFault _ => exact GoodFrom.similar shape similar nonNeed atArgument
      | retryableFault _ => exact GoodFrom.similar shape similar nonNeed atArgument

/-- A reference names a tracked need cell, and every derivation of a selected
occurrence of the cell's origin is good for the reference's producer. -/
def RelRef (tracked : Tracked Head Operation Effect m) (cell : CellId)
    (ref : ScopedNeed.Ref Head Effect StableFault NativeFault m) : Prop :=
  ∃ origin, tracked[ref.1]? = some (cell, some origin) ∧
    ∀ position rule selected, Selection origin position rule selected →
      ∀ world outcome final, Eval primitive selected world outcome final →
        Good primitive (.returns .native) tracked outcome ref.2 world final

theorem RelRef.mono {tracked tracked' : Tracked Head Operation Effect m} (isPrefix : tracked <+: tracked')
    {cell : CellId} {ref : ScopedNeed.Ref Head Effect StableFault NativeFault m}
    (related : RelRef primitive tracked cell ref) : RelRef primitive tracked' cell ref := by
  obtain ⟨origin, located, good⟩ := related
  exact ⟨origin, prefix_getElem isPrefix located,
    fun position rule selected selection world outcome final derivation =>
      Good.mono primitive isPrefix (good position rule selected selection world outcome final derivation)⟩

/-- Run-time and semantic environments agree variable by variable, and the
references agree with the cells. -/
structure RelEnv {scope : List VShape} {k : Nat} (tracked : Tracked Head Operation Effect m)
    (values : Fin scope.length → RuntimeValue Head Operation Effect m)
    (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope)
    (needs : Fin k → CellId) (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) : Prop where
  values : ∀ shape (index : Member scope shape), RelValue primitive shape tracked (values index.index) (env shape index)
  refs : ∀ j, RelRef primitive tracked (needs j) (refs j)

theorem RelEnv.mono {scope : List VShape} {k : Nat} {tracked tracked' : Tracked Head Operation Effect m}
    (isPrefix : tracked <+: tracked') {values : Fin scope.length → RuntimeValue Head Operation Effect m}
    {env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope}
    {needs : Fin k → CellId} {refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m}
    (related : RelEnv primitive tracked values env needs refs) : RelEnv primitive tracked' values env needs refs :=
  ⟨fun shape index => RelValue.mono primitive shape isPrefix (related.values shape index),
    fun j => (related.refs j).mono primitive isPrefix⟩

theorem RelEnv.consValue {scope : List VShape} {k : Nat} {shape : VShape} {tracked : Tracked Head Operation Effect m}
    {values : Fin scope.length → RuntimeValue Head Operation Effect m}
    {env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope}
    {needs : Fin k → CellId} {refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m}
    (related : RelEnv primitive tracked values env needs refs) {value : RuntimeValue Head Operation Effect m}
    {semantic : SemValue Head Effect StableFault NativeFault m shape}
    (head : RelValue primitive shape tracked value semantic) :
    RelEnv primitive tracked (scope := shape :: scope)
      (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) (SemEnv.cons semantic env)
      needs refs := by
  refine ⟨?_, related.refs⟩
  intro shape' index
  cases index with
  | zero => exact head
  | succ index => exact related.values _ index

theorem RelEnv.consRef {scope : List VShape} {k : Nat} {tracked : Tracked Head Operation Effect m}
    {values : Fin scope.length → RuntimeValue Head Operation Effect m}
    {env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope}
    {needs : Fin k → CellId} {refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m}
    (related : RelEnv primitive tracked values env needs refs) {cell : CellId}
    {ref : ScopedNeed.Ref Head Effect StableFault NativeFault m} (head : RelRef primitive tracked cell ref) :
    RelEnv primitive tracked values env (Fin.cases (motive := fun _ => CellId) cell needs)
      (Fin.cases (motive := fun _ => ScopedNeed.Ref Head Effect StableFault NativeFault m) ref refs) := by
  refine ⟨related.values, ?_⟩
  intro j
  refine Fin.cases ?_ (fun j' => ?_) j
  · exact head
  · exact related.refs j'

/-! ## Cells forced at once -/

/-- A cell demanded at once answers what its producer answers; only its own
position of the store changes. -/
theorem cellAt_world (shape : VShape)
    (producer : SemComputation Head Effect StableFault NativeFault m (.returns shape))
    (store : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace)
    {result : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (Produced (SemValue Head Effect StableFault NativeFault m shape) StableFault
        (ScopedNeedMachine.Fault NativeFault)) Effect}
    (member : result ∈ runWorldsAt producer (store ++ [none]) branch) :
    ∃ prior ∈ runWorldsAt (cellAt shape store.length producer) (store ++ [none]) branch,
      prior.answer = result.answer ∧ prior.state.length = result.state.length ∧
        ∀ other, other ≠ store.length → prior.state.getD other none = result.state.getD other none := by
  cases shape with
  | native =>
      have pending : (store ++ [none]).getD store.length none = none := by simp
      have pendingRun := ScopedNeed.demand_pending (Effect := Effect) store.length
        (producer : ScopedNeed.Run Head Effect StableFault NativeFault m) (store ++ [none]) branch pending
      refine ⟨WorldResult.prependIntents result.intents
        ⟨result.branch, result.answer, ScopedNeed.settled store.length result.answer result.state, []⟩, ?_, rfl,
          ScopedNeed.settled_length _ _ _, fun other different => ScopedNeed.settled_other _ _ different _ _⟩
      show _ ∈ runWorldsAt (ScopedNeed.demand store.length
        (producer : ScopedNeed.Run Head Effect StableFault NativeFault m)) (store ++ [none]) branch
      rw [pendingRun]
      refine ScopedNeed.mem_bind member ?_
      rw [ScopedNeed.settle_run]
      exact List.mem_singleton_self _
  | thunk _ => exact ⟨result, member, rfl, rfl, fun _ _ => rfl⟩
  | pack _ => exact ⟨result, member, rfl, rfl, fun _ _ => rfl⟩

/-- The world of the reading's allocation. -/
theorem alloc_member (store : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace) :
    (⟨branch, store.length, store ++ [none], []⟩ : WorldResult _ _ Effect) ∈
      runWorldsAt (.read fun store => .write (store ++ [none]) (.pure store.length)) store branch :=
  List.mem_singleton_self _

/-- **The force of a fresh cell of sequencing or choice**: the machine raises
a retry of its own, or the cell's demand in the reading answers the force's
outcome and ends in a store that agrees with the force's final heap. -/
theorem forced_cell {answer : VShape} {tracked : Tracked Head Operation Effect m}
    {origin : PolarizedNeedMachine.Closure Head Operation Effect m}
    {producer : SemComputation Head Effect StableFault NativeFault m (.returns answer)}
    (selectedGood : ∀ position rule selected, Selection origin position rule selected →
      ∀ world outcome final, Eval primitive selected world outcome final →
        Good primitive (.returns answer) tracked outcome producer world final)
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell))
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (forced : Force primitive cell next outcome final)
    {tracked' : Tracked Head Operation Effect m} {store : ScopedNeed.Store Head StableFault NativeFault m}
    {branch : BranchTrace} (isPrefix : tracked <+: tracked') (agrees : StoreAgrees tracked' world store) :
    MachineRaised outcome ∨
      ∃ (tracked'' : Tracked Head Operation Effect m)
        (prior : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
          (Produced (SemValue Head Effect StableFault NativeFault m answer) StableFault
            (ScopedNeedMachine.Fault NativeFault)) Effect),
        tracked' <+: tracked'' ∧ prior ∈ runWorldsAt (cellAt answer store.length producer) (store ++ [none]) branch ∧
          StoreAgrees tracked'' final prior.state ∧ RelOutcome primitive answer tracked'' outcome prior.answer := by
  have allocatedAgrees := agrees.alloc allocated false
  have present := allocated_suspended allocated
  have located : (tracked' ++ [(cell, if false = true then some origin else none)])[store.length]? =
      some (cell, none) := by
    rw [← agrees.length]; simp
  cases forced with
  | cachedValue found => rw [present] at found; cases found
  | cachedStable found => rw [present] at found; cases found
  | missing found => rw [present] at found; cases found
  | evaluating found => rw [present] at found; cases found
  | @suspended _ _ selected position rule _ bodyFinal bodyOutcome found selection body =>
      rw [present] at found
      cases found
      have entered := allocatedAgrees.enter present position rule
      have good := selectedGood _ _ _ selection _ _ _ body _ (store ++ [none]) branch
        (isPrefix.trans (List.prefix_append _ _)) entered
      rcases finalize_cases bodyFinal cell next.nextEvaluator bodyOutcome with raised | ⟨origin', owned, outcomeEq, heapEq⟩
      · exact .inl raised
      rw [outcomeEq]
      rcases good with raised | ⟨tracked'', result, isPrefix'', member, resultAgrees, related⟩
      · exact .inl raised
      change RelOutcome primitive answer tracked'' bodyOutcome result.answer at related
      obtain ⟨prior, priorMember, answerEq, lengthEq, others⟩ := cellAt_world answer producer store branch member
      refine .inr ⟨tracked'', prior, (List.prefix_append _ _).trans isPrefix'', priorMember, ?_, ?_⟩
      · exact resultAgrees.replace (prefix_getElem isPrefix'' located) _ heapEq lengthEq
          (fun other different => others other different)
          (fun _ impossible => by simp at impossible)
      · rw [answerEq]; exact related

/-- **The force of a fresh cell of choice, at any shape**: the machine raises
a retry of its own, or the outcome, in the finalized world, is good for the
cell's producer, the cell tracked as a cell of choice.  The finalization
changes only that cell, so the outcome's goodness carries over from the
producer's own final world. -/
theorem forced_selected {shape : CShape} {tracked : Tracked Head Operation Effect m}
    {origin : PolarizedNeedMachine.Closure Head Operation Effect m}
    {producer : SemComputation Head Effect StableFault NativeFault m shape}
    (selectedGood : ∀ position rule selected, Selection origin position rule selected →
      ∀ world outcome final, Eval primitive selected world outcome final →
        Good primitive shape tracked outcome producer world final)
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell))
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (forced : Force primitive cell next outcome final)
    {tracked' : Tracked Head Operation Effect m} {store : ScopedNeed.Store Head StableFault NativeFault m}
    {branch : BranchTrace} (isPrefix : tracked <+: tracked') (agrees : StoreAgrees tracked' world store) :
    GoodFrom primitive shape (tracked' ++ [(cell, if false = true then some origin else none)]) outcome producer final
      (store ++ [none]) branch := by
  have allocatedAgrees := agrees.alloc allocated false
  have present := allocated_suspended allocated
  have nonNeed : NonNeed (tracked' ++ [(cell, if false = true then some origin else none)]) cell :=
    ⟨tracked'.length, by simp⟩
  cases forced with
  | cachedValue found => rw [present] at found; cases found
  | cachedStable found => rw [present] at found; cases found
  | missing found => rw [present] at found; cases found
  | evaluating found => rw [present] at found; cases found
  | @suspended _ _ selected position rule _ bodyFinal bodyOutcome found selection body =>
      rw [present] at found
      cases found
      have entered := allocatedAgrees.enter present position rule
      have good := selectedGood _ _ _ selection _ _ _ body _ (store ++ [none]) branch
        (isPrefix.trans (List.prefix_append _ _)) entered
      rcases finalize_cases bodyFinal cell next.nextEvaluator bodyOutcome with
        raised | ⟨origin', owned, outcomeEq, heapEq⟩
      · exact GoodFrom.raised primitive shape raised
      rw [outcomeEq]
      exact GoodFrom.similar primitive shape (finalize_similar bodyFinal cell bodyOutcome owned heapEq)
        (fun other member => by
          rw [List.mem_singleton] at member
          subst member
          exact nonNeed) good

/-! ## Need cells -/

/-- The cache a finalized need cell keeps agrees with the store's settled
entry, when the outcome agrees with the answer. -/
theorem cacheOf_settled {tracked : Tracked Head Operation Effect m}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {semantic : ScopedNeed.Outcome Head StableFault NativeFault m}
    (related : RelOutcome primitive .native tracked outcome semantic)
    {store : ScopedNeed.Store Head StableFault NativeFault m} {index : Nat} (bound : index < store.length)
    (pending : store.getD index none = none) :
    CacheAgrees (cacheOf outcome) ((ScopedNeed.settled index semantic store).getD index none) := by
  cases outcome with
  | value answer =>
      cases answer with
      | returned value =>
          cases semantic with
          | value term =>
              simp only [RelOutcome, RelValue] at related
              subst related
              simp only [cacheOf, ScopedNeed.settled, List.getD_eq_getElem?_getD, List.getElem?_set_self bound,
                Option.getD_some]
              exact .value term
          | stableFault _ => exact related.elim
          | retryableFault _ => exact related.elim
      | nativeFunction _ => cases semantic <;> exact related.elim
      | valueFunction _ => cases semantic <;> exact related.elim
  | stableFault fault =>
      cases semantic with
      | stableFault fault' =>
          simp only [RelOutcome] at related
          subst related
          simp only [cacheOf, ScopedNeed.settled, List.getD_eq_getElem?_getD, List.getElem?_set_self bound,
            Option.getD_some]
          exact .stableFault fault
      | value _ => exact related.elim
      | retryableFault _ => exact related.elim
  | retryableFault reason =>
      cases semantic with
      | retryableFault reason' =>
          simp only [cacheOf, ScopedNeed.settled]
          rw [pending]
          exact .suspended
      | value _ => exact related.elim
      | stableFault _ => exact related.elim

/-- **The force of a need cell**: the machine raises a retry of its own, or
the demand of its reference answers the force's outcome and ends in a store
that agrees with the force's final heap. -/
theorem forced_need {tracked : Tracked Head Operation Effect m} {cell : CellId}
    {ref : ScopedNeed.Ref Head Effect StableFault NativeFault m} (related : RelRef primitive tracked cell ref)
    {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    (forced : Force primitive cell world outcome final)
    {tracked' : Tracked Head Operation Effect m} {store : ScopedNeed.Store Head StableFault NativeFault m}
    {branch : BranchTrace} (isPrefix : tracked <+: tracked') (agrees : StoreAgrees tracked' world store) :
    MachineRaised outcome ∨
      ∃ (tracked'' : Tracked Head Operation Effect m)
        (prior : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
          (ScopedNeed.Outcome Head StableFault NativeFault m) Effect),
        tracked' <+: tracked'' ∧ prior ∈ runWorldsAt (ScopedNeed.demand ref.1 ref.2) store branch ∧
          StoreAgrees tracked'' final prior.state ∧ RelOutcome primitive .native tracked'' outcome prior.answer := by
  obtain ⟨origin, located, good⟩ := related
  have located' := prefix_getElem isPrefix located
  obtain ⟨cache, found, cacheAgrees⟩ := agrees.caches _ _ _ located'
  have bound : ref.1 < store.length := by
    rw [← agrees.length]; exact (List.getElem?_eq_some_iff.mp located').1
  generalize entryEq : store.getD ref.1 none = entry at cacheAgrees
  cases cacheAgrees with
  | suspended =>
      cases forced with
      | cachedValue found' => rw [found] at found'; cases found'
      | cachedStable found' => rw [found] at found'; cases found'
      | missing found' => rw [found] at found'; cases found'
      | evaluating found' => rw [found] at found'; cases found'
      | @suspended _ _ selected position rule _ bodyFinal bodyOutcome found' selection body =>
          rw [found] at found'
          cases found'
          have entered := agrees.enter found position rule
          rcases good _ _ _ selection _ _ _ body tracked' store branch isPrefix entered with
            raised | ⟨tracked'', result, isPrefix'', member, resultAgrees, resultRelated⟩
          · rcases finalize_cases bodyFinal cell world.nextEvaluator bodyOutcome with raised' | ⟨_, _, outcomeEq, _⟩
            · exact .inl raised'
            · rw [outcomeEq]; exact .inl raised
          change RelOutcome primitive .native tracked'' bodyOutcome result.answer at resultRelated
          rcases finalize_cases bodyFinal cell world.nextEvaluator bodyOutcome with
            raised | ⟨origin', owned, outcomeEq, heapEq⟩
          · exact .inl raised
          rw [outcomeEq]
          have located'' := prefix_getElem isPrefix'' located'
          obtain ⟨cache', found'', cacheAgrees'⟩ := resultAgrees.caches _ _ _ located''
          rw [owned] at found''
          cases found''
          have resultBound : ref.1 < result.state.length := by
            rw [← resultAgrees.length]; exact (List.getElem?_eq_some_iff.mp located'').1
          have resultPending : result.state.getD ref.1 none = none := by
            generalize result.state.getD ref.1 none = entry' at cacheAgrees'
            cases cacheAgrees'
            rfl
          refine .inr ⟨tracked'', WorldResult.prependIntents result.intents
            ⟨result.branch, result.answer, ScopedNeed.settled ref.1 result.answer result.state, []⟩,
            isPrefix'', ?_, ?_, resultRelated⟩
          · rw [ScopedNeed.demand_pending _ _ _ _ entryEq]
            refine ScopedNeed.mem_bind member ?_
            rw [ScopedNeed.settle_run]
            exact List.mem_singleton_self _
          · exact resultAgrees.replace located'' (cacheOf bodyOutcome) heapEq (ScopedNeed.settled_length _ _ _)
              (fun other different => ScopedNeed.settled_other _ _ different _ _)
              (fun _ same => by
                cases same
                exact ⟨rfl, cacheOf_settled primitive resultRelated resultBound resultPending⟩)
  | evaluating owner =>
      cases forced with
      | cachedValue found' => rw [found] at found'; cases found'
      | cachedStable found' => rw [found] at found'; cases found'
      | missing found' => rw [found] at found'; cases found'
      | evaluating _ => exact .inl trivial
      | suspended found' _ _ => rw [found] at found'; cases found'
  | value term =>
      cases forced with
      | cachedValue found' =>
          rw [found] at found'
          cases found'
          refine .inr ⟨tracked', ⟨branch, .value term, store, []⟩, List.prefix_refl _, ?_,
            agrees.of_heap rfl, rfl⟩
          rw [ScopedNeed.demand_cached _ _ _ _ _ entryEq]
          exact List.mem_singleton_self _
      | cachedStable found' => rw [found] at found'; cases found'
      | missing found' => rw [found] at found'; cases found'
      | evaluating found' => rw [found] at found'; cases found'
      | suspended found' _ _ => rw [found] at found'; cases found'
  | stableFault fault =>
      cases forced with
      | cachedStable found' =>
          rw [found] at found'
          cases found'
          refine .inr ⟨tracked', ⟨branch, .stableFault fault, store, []⟩, List.prefix_refl _, ?_,
            agrees.of_heap rfl, rfl⟩
          rw [ScopedNeed.demand_cached _ _ _ _ _ entryEq]
          exact List.mem_singleton_self _
      | cachedValue found' => rw [found] at found'; cases found'
      | missing found' => rw [found] at found'; cases found'
      | evaluating found' => rw [found] at found'; cases found'
      | suspended found' _ _ => rw [found] at found'; cases found'

/-- Only a choice has an occurrence other than itself. -/
theorem entry_only {n v k : Nat} {code : PolarizedNeed.Computation Head Operation Effect n v k} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (notChoice : ∀ left right, code ≠ .choose left right)
    {Goal : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m →
      PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
      PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m → Prop}
    (good : ∀ world outcome final, Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final →
      Goal world outcome final) :
    ∀ position rule selected, Selection ⟨n, v, k, code, native, values, needs⟩ position rule selected →
      ∀ world outcome final, Eval primitive selected world outcome final → Goal world outcome final := by
  intro position rule selected selection
  cases selection with
  | entry _ => exact good
  | left left right _ _ _ => exact absurd rfl (notChoice left right)
  | right left right _ _ _ => exact absurd rfl (notChoice left right)

/-! ## The fundamental lemma -/

mutual
  /-- **A value reads as its run-time value**, in agreeing environments. -/
  theorem fundamental_value : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      (value : Value Head Operation Effect n scope k shape) →
      (tracked : Tracked Head Operation Effect m) → (native : Sub Head n m) →
      (values : Fin scope.length → RuntimeValue Head Operation Effect m) → (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) →
      RelEnv primitive tracked values env needs refs →
      RelValue primitive shape tracked (PolarizedNeedMachine.captureValue native values needs value.erase)
        (readValue primitive value native env refs)
    | _, _, _, _, .native _, _, _, _, _, _, _, _ => rfl
    | _, _, _, _, .var index, _, _, _, _, _, _, related => related.values _ index
    | _, _, _, _, .thunk body, _, native, values, needs, env, refs, related =>
        ⟨_, _, _, body.erase, native, values, needs, rfl,
          fun world outcome final derivation tracked' store branch isPrefix agrees =>
            (fundamental_computation body tracked' native values needs env refs (related.mono primitive isPrefix)).1
              world outcome final derivation tracked' store branch (List.prefix_refl _) agrees⟩
    | _, _, _, _, .pack _ value, tracked, native, values, needs, env, refs, related =>
        ⟨_, rfl, fundamental_value value tracked native values needs env refs related⟩

  /-- **The fundamental lemma**: every natural derivation of a computation is
  good for its reading, and every derivation of a selected occurrence is good
  for its reading as a cell's producer. -/
  theorem fundamental_computation : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      (computation : Computation Head Operation Effect n scope k shape) →
      (tracked : Tracked Head Operation Effect m) → (native : Sub Head n m) →
      (values : Fin scope.length → RuntimeValue Head Operation Effect m) → (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) →
      RelEnv primitive tracked values env needs refs →
      (∀ world outcome final,
        Eval primitive ⟨n, scope.length, k, computation.erase, native, values, needs⟩ world outcome final →
          Good primitive shape tracked outcome (readComputation primitive computation native env refs).1 world final) ∧
      (∀ position rule selected,
        Selection ⟨n, scope.length, k, computation.erase, native, values, needs⟩ position rule selected →
          ∀ world outcome final, Eval primitive selected world outcome final →
            Good primitive shape tracked outcome (readComputation primitive computation native env refs).2 world final)
    | _, _, _, _, .returnValue value, tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.returnValue value).erase, native,
            values, needs⟩ world outcome final →
              Good primitive _ tracked outcome (readComputation primitive (.returnValue value) native env refs).1
                world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation
          exact .inr ⟨tracked', _, List.prefix_refl _, List.mem_singleton_self _, agrees,
            fundamental_value value tracked' native values needs env refs (related.mono primitive isPrefix)⟩
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, .call operation argument, tracked, native, values, needs, env, refs, _ => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.call (Head := Head)
            (Effect := Effect) (k := _) (scope := _) operation argument).erase, native, values, needs⟩ world outcome
              final → Good primitive _ tracked outcome
                (readComputation primitive (.call operation argument) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch _ agrees
          cases derivation
          refine .inr ⟨tracked', _, List.prefix_refl _, List.mem_singleton_self _, agrees, ?_⟩
          generalize primitive operation (subst native argument) = produced
          cases produced with
          | value term => rfl
          | stableFault fault => rfl
          | retryableFault reason => cases reason <;> rfl
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .emit effect next, tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.emit effect next).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape tracked outcome (readComputation primitive (.emit effect next) native env refs).1
                world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation with
          | emit _ nextDerivation =>
              exact GoodFrom.bind primitive shape _ _ ⟨⟨branch, (), store, [effect]⟩, List.mem_singleton_self _,
                tracked', List.prefix_refl _,
                (fundamental_computation next tracked native values needs env refs related).1 _ _ _ nextDerivation
                  tracked' store branch isPrefix (agrees.of_heap rfl)⟩
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, .nativeLambda body, tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.nativeLambda body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive _ tracked outcome (readComputation primitive (.nativeLambda body) native env refs).1
                world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation
          intro argument cells start similar nonNeed outcome' final' bodyDerivation
          exact (fundamental_computation body tracked' (Fin.cases (motive := fun _ => Tm Head m) argument native)
            values needs env refs (related.mono primitive isPrefix)).1 _ _ _ bodyDerivation tracked' store branch
              (List.prefix_refl _) (agrees.similar similar nonNeed)
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .nativeApply function argument, tracked, native, values, needs, env,
        refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.nativeApply function argument).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape tracked outcome
                (readComputation primitive (.nativeApply function argument) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          have functionGood := (fundamental_computation function tracked native values needs env refs related).1
          cases derivation with
          | nativeApply _ functionDerivation bodyDerivation =>
              exact functionGood _ _ _ functionDerivation tracked' store branch isPrefix agrees (subst native argument)
                [] _ (Similar.refl _) (fun _ member => nomatch member) _ _ bodyDerivation
          | nativeApplyMismatch _ functionDerivation notFunction =>
              rename_i answer
              have atArgument := functionGood _ _ _ functionDerivation tracked' store branch isPrefix agrees
                (subst native argument)
              exfalso
              revert atArgument
              cases answer with
              | nativeFunction body => exact absurd rfl (notFunction body)
              | returned _ => exact id
              | valueFunction _ => exact id
          | nativeApplyFault _ functionDerivation fault =>
              have atArgument := functionGood _ _ _ functionDerivation tracked' store branch isPrefix agrees
                (subst native argument)
              cases fault <;> exact atArgument
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, .valueLambda body, tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.valueLambda body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive _ tracked outcome (readComputation primitive (.valueLambda body) native env refs).1
                world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation
          intro argument semantic relatedArgument cells start similar nonNeed outcome' final' bodyDerivation
          exact (fundamental_computation body tracked' native
            (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) argument values) needs
            (SemEnv.cons semantic env) refs ((related.mono primitive isPrefix).consValue primitive relatedArgument)).1
              _ _ _ bodyDerivation tracked' store branch (List.prefix_refl _) (agrees.similar similar nonNeed)
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .valueApply function argument,
        tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.valueApply function argument).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape tracked outcome
                (readComputation primitive (.valueApply function argument) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          have functionGood := (fundamental_computation function tracked native values needs env refs related).1
          have argumentRelated := fundamental_value argument tracked' native values needs env refs
            (related.mono primitive isPrefix)
          cases derivation with
          | valueApply _ functionDerivation bodyDerivation =>
              exact functionGood _ _ _ functionDerivation tracked' store branch isPrefix agrees _ _ argumentRelated
                [] _ (Similar.refl _) (fun _ member => nomatch member) _ _ bodyDerivation
          | valueApplyMismatch _ functionDerivation notFunction =>
              rename_i answer
              have atArgument := functionGood _ _ _ functionDerivation tracked' store branch isPrefix agrees _ _
                argumentRelated
              exfalso
              revert atArgument
              cases answer with
              | valueFunction body => exact absurd rfl (notFunction body)
              | returned _ => exact id
              | nativeFunction _ => exact id
          | valueApplyFault _ functionDerivation fault =>
              have atArgument := functionGood _ _ _ functionDerivation tracked' store branch isPrefix agrees _ _
                argumentRelated
              cases fault <;> exact atArgument
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .forceThunk value, tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.forceThunk value).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape tracked outcome (readComputation primitive (.forceThunk value) native env refs).1
                world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          obtain ⟨_, _, _, code, native', values', needs', captured, thunkGood⟩ :=
            fundamental_value value tracked native values needs env refs related
          cases derivation with
          | forceThunk _ captured' thunkDerivation =>
              rw [captured] at captured'
              cases captured'
              exact thunkGood _ _ _ thunkDerivation tracked' store branch isPrefix agrees
          | forceThunkMismatch _ _ notThunk => exact absurd captured (notThunk _ _ _ _ _ _ _)
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .unpackNative value body, tracked, native, values, needs,
        env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.unpackNative value body).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape tracked outcome
                (readComputation primitive (.unpackNative value body) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          obtain ⟨inner, captured, innerRelated⟩ := fundamental_value value tracked native values needs env refs related
          cases derivation with
          | unpackNative _ captured' bodyDerivation =>
              rw [captured] at captured'
              cases captured'
              exact (fundamental_computation body tracked _ _ needs
                (SemEnv.cons (readValue primitive value native env refs).2 env) refs
                (related.consValue primitive innerRelated)).1 _ _ _ bodyDerivation tracked' store branch isPrefix agrees
          | unpackNativeMismatch _ _ _ notPackage => exact absurd captured (notPackage _ _)
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, .forceNeed reference, tracked, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.forceNeed (Head := Head)
            (Operation := Operation) (Effect := Effect) (n := _) (scope := _) reference).erase, native, values, needs⟩
              world outcome final →
              Good primitive _ tracked outcome (readComputation primitive (.forceNeed reference) native env refs).1
                world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation with
          | forceNeed _ forced =>
              rcases forced_need primitive (related.refs reference) forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', member, priorAgrees, priorRelated⟩
              · exact .inl raised
              · exact .inr ⟨tracked'', prior, isPrefix'', member, priorAgrees, priorRelated⟩
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .bindNative first body, tracked, native, values, needs,
        env, refs, related => by
        have producer := (fundamental_computation first tracked native values needs env refs related).2
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.bindNative first body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive shape tracked outcome
                (readComputation primitive (.bindNative first body) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation with
          | @bindNativeValue _ _ _ _ _ _ _ _ _ _ _ _ _ value _ allocated forced bodyDerivation =>
              rcases forced_cell primitive producer allocated forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
              · exact (raised : False).elim
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, tracked'', List.prefix_refl _, ?_⟩
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases answer₂ with
              | value term =>
                  simp only [RelOutcome, RelValue] at priorRelated
                  injection priorRelated with priorRelated
                  subst priorRelated
                  exact (fundamental_computation body tracked'' (Fin.cases (motive := fun _ => Tm Head m) value native)
                    values needs env refs (related.mono primitive (isPrefix.trans isPrefix''))).1 _ _ _ bodyDerivation
                      tracked'' state₂ branch₂ (List.prefix_refl _) priorAgrees
              | stableFault _ => exact priorRelated.elim
              | retryableFault _ => exact priorRelated.elim
          | @bindNativeMismatch _ _ _ _ _ _ _ _ _ _ _ _ answer allocated forced notNative =>
              rcases forced_cell primitive producer allocated forced (branch := branch) isPrefix agrees with
                raised | ⟨tracked'', prior, _, _, _, priorRelated⟩
              · exact (raised : False).elim
              exfalso
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases answer with
              | returned returned =>
                  cases answer₂ with
                  | value term =>
                      simp only [RelOutcome, RelValue] at priorRelated
                      exact notNative term (by rw [priorRelated])
                  | stableFault _ => exact priorRelated
                  | retryableFault _ => exact priorRelated
              | nativeFunction _ => cases answer₂ <;> exact priorRelated
              | valueFunction _ => cases answer₂ <;> exact priorRelated
          | bindNativeFault _ allocated forced fault =>
              rcases forced_cell primitive producer allocated forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
              · exact GoodFrom.raised primitive shape raised
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, tracked'', List.prefix_refl _, ?_⟩
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases fault with
              | stableFault fault =>
                  cases answer₂ with
                  | stableFault fault' =>
                      simp only [RelOutcome] at priorRelated
                      subst priorRelated
                      exact GoodFrom.failStable primitive shape fault priorAgrees
                  | value _ => exact priorRelated.elim
                  | retryableFault _ => exact priorRelated.elim
              | retryableFault reason =>
                  cases answer₂ with
                  | retryableFault reason' =>
                      simp only [RelOutcome] at priorRelated
                      subst priorRelated
                      exact GoodFrom.failRetry primitive shape reason' priorAgrees
                  | value _ => exact priorRelated.elim
                  | stableFault _ => exact priorRelated.elim
          | bindNativeAllocationFailure _ _ =>
              exact GoodFrom.raised primitive shape (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .bindValue (bound := bound) first body, tracked, native,
        values, needs, env, refs, related => by
        have producer := (fundamental_computation first tracked native values needs env refs related).2
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.bindValue first body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive shape tracked outcome
                (readComputation primitive (.bindValue first body) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation with
          | @bindValueValue _ _ _ _ _ _ _ _ _ _ _ _ _ value _ allocated forced bodyDerivation =>
              rcases forced_cell primitive producer allocated forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
              · exact (raised : False).elim
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, tracked'', List.prefix_refl _, ?_⟩
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases answer₂ with
              | value semantic =>
                  exact (fundamental_computation body tracked'' native
                    (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) needs
                    (SemEnv.cons semantic env) refs
                    ((related.mono primitive (isPrefix.trans isPrefix'')).consValue primitive priorRelated)).1 _ _ _
                      bodyDerivation tracked'' state₂ branch₂ (List.prefix_refl _) priorAgrees
              | stableFault _ => exact priorRelated.elim
              | retryableFault _ => exact priorRelated.elim
          | @bindValueMismatch _ _ _ _ _ _ _ _ _ _ _ _ answer allocated forced notReturned =>
              rcases forced_cell primitive producer allocated forced (branch := branch) isPrefix agrees with
                raised | ⟨tracked'', prior, _, _, _, priorRelated⟩
              · exact (raised : False).elim
              exfalso
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases answer with
              | returned value => exact notReturned value rfl
              | nativeFunction _ => cases answer₂ <;> exact priorRelated
              | valueFunction _ => cases answer₂ <;> exact priorRelated
          | bindValueFault _ allocated forced fault =>
              rcases forced_cell primitive producer allocated forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
              · exact GoodFrom.raised primitive shape raised
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, tracked'', List.prefix_refl _, ?_⟩
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases fault with
              | stableFault fault =>
                  cases answer₂ with
                  | stableFault fault' =>
                      simp only [RelOutcome] at priorRelated
                      subst priorRelated
                      exact GoodFrom.failStable primitive shape fault priorAgrees
                  | value _ => exact priorRelated.elim
                  | retryableFault _ => exact priorRelated.elim
              | retryableFault reason =>
                  cases answer₂ with
                  | retryableFault reason' =>
                      simp only [RelOutcome] at priorRelated
                      subst priorRelated
                      exact GoodFrom.failRetry primitive shape reason' priorAgrees
                  | value _ => exact priorRelated.elim
                  | stableFault _ => exact priorRelated.elim
          | bindValueAllocationFailure _ _ =>
              exact GoodFrom.raised primitive shape (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, .choose left right, tracked, native, values, needs, env, refs, related => by
        have leftGood := (fundamental_computation left tracked native values needs env refs related).1
        have rightGood := (fundamental_computation right tracked native values needs env refs related).1
        have selectedGood : ∀ position rule selected,
            Selection ⟨_, _, _, (Computation.choose left right).erase, native, values, needs⟩ position rule selected →
              ∀ world outcome final, Eval primitive selected world outcome final →
                Good primitive shape tracked outcome
                  (readComputation primitive (.choose left right) native env refs).2 world final := by
          intro position rule selected selection world outcome final derivation tracked' store branch isPrefix agrees
          cases selection with
          | entry notChoice => exact absurd rfl (notChoice _ _)
          | left =>
              exact GoodFrom.bind primitive _ _ _ ⟨⟨false :: branch, false, store, []⟩,
                List.mem_append_left _ (List.mem_singleton_self _), tracked', List.prefix_refl _,
                leftGood _ _ _ derivation tracked' store (false :: branch) isPrefix agrees⟩
          | right =>
              exact GoodFrom.bind primitive _ _ _ ⟨⟨true :: branch, true, store, []⟩,
                List.mem_append_right _ (List.mem_singleton_self _), tracked', List.prefix_refl _,
                rightGood _ _ _ derivation tracked' store (true :: branch) isPrefix agrees⟩
        refine ⟨?_, selectedGood⟩
        intro world outcome final derivation tracked' store branch isPrefix agrees
        cases derivation with
        | choose _ _ allocated forced =>
            cases shape with
            | returns answer =>
                rcases forced_cell primitive selectedGood allocated forced isPrefix agrees with
                  raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
                · exact GoodFrom.raised primitive _ raised
                refine GoodFrom.bind primitive _ _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
                exact .inr ⟨tracked'', prior, List.prefix_refl _, priorMember, priorAgrees, priorRelated⟩
            | nativePi shape' =>
                have step := forced_selected primitive selectedGood allocated forced (branch := branch) isPrefix agrees
                exact GoodFrom.bind primitive _ _ _ ⟨_, alloc_member store branch, _, List.prefix_append _ _, step⟩
            | arrow domain shape' =>
                have step := forced_selected primitive selectedGood allocated forced (branch := branch) isPrefix agrees
                exact GoodFrom.bind primitive _ _ _ ⟨_, alloc_member store branch, _, List.prefix_append _ _, step⟩
        | chooseAllocationFailure _ _ _ =>
            exact GoodFrom.raised primitive _ (by
              simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                MachineRaised])
    | _, _, _, shape, .letNeed suspended body, tracked, native, values,
        needs, env, refs, related => by
        have producer := (fundamental_computation suspended tracked native values needs env refs related).2
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.letNeed suspended body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive shape tracked outcome
                (readComputation primitive (.letNeed suspended body) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation with
          | @letNeed _ _ _ _ _ _ _ _ _ _ _ cell _ allocated bodyDerivation =>
              have allocatedAgrees := agrees.alloc allocated true
              have relatedRef : RelRef primitive (tracked' ++ [(cell, if true = true then
                  some ⟨_, _, _, suspended.erase, native, values, needs⟩ else none)]) cell
                  (store.length, (readComputation primitive suspended native env refs).2) :=
                ⟨_, by rw [← agrees.length]; simp,
                  fun position rule selected selection world outcome final derivation =>
                    Good.mono primitive (isPrefix.trans (List.prefix_append _ _))
                      (producer position rule selected selection world outcome final derivation)⟩
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_member store branch,
                tracked' ++ [(cell, if true = true then some ⟨_, _, _, suspended.erase, native, values, needs⟩ else none)],
                List.prefix_append _ _, ?_⟩
              exact (fundamental_computation body _ native values (Fin.cases (motive := fun _ => CellId) cell needs) env
                (Fin.cases (motive := fun _ => ScopedNeed.Ref Head Effect StableFault NativeFault m)
                  (store.length, (readComputation primitive suspended native env refs).2) refs)
                ((related.mono primitive (isPrefix.trans (List.prefix_append _ _))).consRef primitive relatedRef)).1
                  _ _ _ bodyDerivation _ (store ++ [none]) branch (List.prefix_refl _) allocatedAgrees
          | letNeedAllocationFailure _ _ =>
              exact GoodFrom.raised primitive shape (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, .sequenceSigma first body, tracked, native, values, needs,
        env, refs, related => by
        have producer := (fundamental_computation first tracked native values needs env refs related).2
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.sequenceSigma first body).erase,
            native, values, needs⟩ world outcome final →
              Good primitive (.returns .native) tracked outcome
                (readComputation primitive (.sequenceSigma first body) native env refs).1 world final := by
          intro world outcome final derivation tracked' store branch isPrefix agrees
          cases derivation with
          | @sequenceSigmaValue _ _ _ _ _ _ _ _ _ _ _ _ _ value bodyOutcome allocated forced bodyDerivation =>
              rcases forced_cell primitive producer allocated forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
              · exact (raised : False).elim
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨prior, priorMember, tracked'', List.prefix_refl _, ?_⟩
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases answer₂ with
              | value term =>
                  simp only [RelOutcome, RelValue] at priorRelated
                  injection priorRelated with priorRelated
                  subst priorRelated
                  rcases (fundamental_computation body tracked'' (Fin.cases (motive := fun _ => Tm Head m) value native)
                    values needs env refs (related.mono primitive (isPrefix.trans isPrefix''))).1 _ _ _ bodyDerivation
                      tracked'' state₂ branch₂ (List.prefix_refl _) priorAgrees with
                    raised | ⟨tracked₃, second, isPrefix₃, secondMember, secondAgrees, secondRelated⟩
                  · left
                    revert raised
                    cases bodyOutcome with
                    | value _ => exact False.elim
                    | stableFault _ => exact False.elim
                    | retryableFault _ => exact id
                  · right
                    obtain ⟨branch₃, answer₃, state₃, intents₃⟩ := second
                    refine ⟨tracked₃, WorldResult.prependIntents intents₃
                      ⟨branch₃, ScopedNeedNaturalSemantics.pairOutcome value answer₃, state₃, []⟩, isPrefix₃,
                      ScopedNeed.mem_bind secondMember (List.mem_singleton_self _), secondAgrees, ?_⟩
                    revert secondRelated
                    cases bodyOutcome with
                    | value bodyAnswer =>
                        cases bodyAnswer with
                        | returned returned =>
                            cases answer₃ with
                            | value term' =>
                                intro secondRelated
                                simp only [RelValue] at secondRelated
                                subst secondRelated
                                rfl
                            | stableFault _ => exact False.elim
                            | retryableFault _ => exact False.elim
                        | nativeFunction _ => intro secondRelated; cases answer₃ <;> exact secondRelated.elim
                        | valueFunction _ => intro secondRelated; cases answer₃ <;> exact secondRelated.elim
                    | stableFault _ =>
                        cases answer₃ with
                        | stableFault _ => exact id
                        | value _ => exact False.elim
                        | retryableFault _ => exact False.elim
                    | retryableFault _ =>
                        cases answer₃ with
                        | retryableFault _ => exact id
                        | value _ => exact False.elim
                        | stableFault _ => exact False.elim
              | stableFault _ => exact priorRelated.elim
              | retryableFault _ => exact priorRelated.elim
          | @sequenceSigmaMismatch _ _ _ _ _ _ _ _ _ _ _ _ answer allocated forced notNative =>
              rcases forced_cell primitive producer allocated forced (branch := branch) isPrefix agrees with
                raised | ⟨tracked'', prior, _, _, _, priorRelated⟩
              · exact (raised : False).elim
              exfalso
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases answer with
              | returned returned =>
                  cases answer₂ with
                  | value term =>
                      simp only [RelOutcome, RelValue] at priorRelated
                      exact notNative term (by rw [priorRelated])
                  | stableFault _ => exact priorRelated
                  | retryableFault _ => exact priorRelated
              | nativeFunction _ => cases answer₂ <;> exact priorRelated
              | valueFunction _ => cases answer₂ <;> exact priorRelated
          | sequenceSigmaFault _ allocated forced fault =>
              rcases forced_cell primitive producer allocated forced isPrefix agrees with
                raised | ⟨tracked'', prior, isPrefix'', priorMember, priorAgrees, priorRelated⟩
              · exact GoodFrom.raised primitive _ raised
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨_, alloc_member store branch, tracked'', isPrefix'', ?_⟩
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨prior, priorMember, tracked'', List.prefix_refl _, ?_⟩
              obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := prior
              cases fault with
              | stableFault fault =>
                  cases answer₂ with
                  | stableFault fault' =>
                      simp only [RelOutcome] at priorRelated
                      subst priorRelated
                      exact GoodFrom.failStable primitive _ fault priorAgrees
                  | value _ => exact priorRelated.elim
                  | retryableFault _ => exact priorRelated.elim
              | retryableFault reason =>
                  cases answer₂ with
                  | retryableFault reason' =>
                      simp only [RelOutcome] at priorRelated
                      subst priorRelated
                      exact GoodFrom.failRetry primitive _ reason' priorAgrees
                  | value _ => exact priorRelated.elim
                  | stableFault _ => exact priorRelated.elim
          | sequenceSigmaAllocationFailure _ _ =>
              exact GoodFrom.raised primitive _ (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
end

/-! ## Soundness -/

/-- **Every natural outcome is an answer of the reading**, other than a retry
the machine raises itself: for a closed native returner, from any world, with
need cells, first-class thunks, value and native lambdas, packages,
sequencing, and choice at every shape. -/
theorem sound {computation : Computation Head Operation Effect 0 [] 0 (.returns .native)}
    (native : Sub Head 0 m)
    {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    (derivation : Eval primitive ⟨0, 0, 0, computation.erase, native, Fin.elim0, Fin.elim0⟩ world outcome final)
    (notRaised : ¬ MachineRaised outcome) :
    ∃ answer ∈ answers primitive computation native, outcome = PolarizedNeedEmbedding.outcome answer := by
  have emptyEnv : RelEnv (Effect := Effect) primitive (scope := []) (k := 0) []
      (Fin.elim0 : Fin 0 → RuntimeValue Head Operation Effect m)
      (SemEnv.empty (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m))
      (Fin.elim0 : Fin 0 → CellId) (Fin.elim0 : Fin 0 → ScopedNeed.Ref Head Effect StableFault NativeFault m) :=
    RelEnv.mk (fun _ index => nomatch index) (fun j => Fin.elim0 j)
  rcases (fundamental_computation primitive computation [] native Fin.elim0 Fin.elim0 SemEnv.empty Fin.elim0
      emptyEnv).1 world outcome final derivation [] [] [] (List.prefix_refl _)
      (StoreAgrees.empty world) with raised | ⟨_, result, _, member, _, related⟩
  · exact absurd raised notRaised
  refine ⟨result.answer, List.mem_map.mpr ⟨result, member, rfl⟩, ?_⟩
  change RelOutcome primitive .native _ outcome result.answer at related
  revert related
  cases outcome with
  | value answer =>
      cases answer with
      | returned value =>
          cases result.answer with
          | value term => intro related; simp only [RelOutcome, RelValue] at related; subst related; rfl
          | stableFault _ => intro related; exact related.elim
          | retryableFault _ => intro related; exact related.elim
      | nativeFunction _ => intro related; cases result.answer <;> exact related.elim
      | valueFunction _ => intro related; cases result.answer <;> exact related.elim
  | stableFault fault =>
      cases result.answer with
      | value _ => intro related; exact related.elim
      | stableFault _ => intro related; simp only [RelOutcome] at related; subst related; rfl
      | retryableFault _ => intro related; exact related.elim
  | retryableFault reason =>
      cases result.answer with
      | value _ => intro related; exact related.elim
      | stableFault _ => intro related; exact related.elim
      | retryableFault _ => intro related; simp only [RelOutcome] at related; subst related; rfl

#print axioms fundamental_computation
#print axioms sound

/-! ## Examples -/

namespace Examples

open PolarizedValues.Examples
open ScopedNeedNaturalSemantics.Examples (ExampleOperation)

/-- **A need cell captured by a thunk forced twice, in the natural
semantics**: every derivation of the erasure answers one of the two equal
pairs, unless the machine raises a retry of its own. -/
theorem sharedInThunk_natural {world final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    {outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0}
    (derivation : Eval examplePrimitive ⟨0, 0, 0, sharedInThunk.erase, ids, Fin.elim0, Fin.elim0⟩ world outcome final)
    (notRaised : ¬ MachineRaised outcome) :
    outcome ∈ ([.value (.pair (.head 1) (.head 1)), .value (.pair (.head 2) (.head 2))] :
      List (ScopedNeedMachine.Outcome Nat Nat Nat 0)).map PolarizedNeedEmbedding.outcome := by
  obtain ⟨answer, member, equal⟩ := sound examplePrimitive ids derivation notRaised
  rw [sharedInThunk_answers] at member
  exact List.mem_map.mpr ⟨answer, member, equal.symm⟩

/-- **No mixed pair**: a derivation of the erasure never answers a pair of
two different heads. -/
theorem sharedInThunk_no_mixed {world final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    (derivation : Eval examplePrimitive ⟨0, 0, 0, sharedInThunk.erase, ids, Fin.elim0, Fin.elim0⟩ world
      (.value (.returned (.native (.pair (.head 1) (.head 2))))) final) : False := by
  obtain ⟨answer, member, equal⟩ := sound examplePrimitive ids derivation
    (by simp [MachineRaised])
  rw [sharedInThunk_answers] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [PolarizedNeedEmbedding.outcome] at equal

/-- A need cell of a choice, and a choice between two native functions, one
forcing the cell, applied. -/
def needChoice : Shaped.Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .letNeed coin (.nativeApply (.choose (.nativeLambda (.forceNeed 0)) (.nativeLambda (.returnValue (.native (.head 5)))))
    (.head 0))

theorem needChoice_answers :
    PolarizedValues.answers (Effect := Nat) examplePrimitive needChoice ids =
      [.value (.head 1), .value (.head 2), .value (.head 5)] := by
  decide

/-- **A choice between functions, with a need cell, in the natural
semantics**: every derivation answers a head of the cell's choice or the
other function's head, unless the machine raises a retry of its own. -/
theorem needChoice_natural {world final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    {outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0}
    (derivation : Eval examplePrimitive ⟨0, 0, 0, needChoice.erase, ids, Fin.elim0, Fin.elim0⟩ world outcome final)
    (notRaised : ¬ MachineRaised outcome) :
    outcome ∈ ([.value (.head 1), .value (.head 2), .value (.head 5)] :
      List (ScopedNeedMachine.Outcome Nat Nat Nat 0)).map PolarizedNeedEmbedding.outcome := by
  obtain ⟨answer, member, equal⟩ := sound examplePrimitive ids derivation notRaised
  rw [needChoice_answers] at member
  exact List.mem_map.mpr ⟨answer, member, equal.symm⟩

/-! ### Closed applications of the headline theorems -/

/-- The scoped-need soundness, applied to a derivation of the shared pair
that answers a pair. -/
theorem sharedPair_closed_sound
    {world final : ScopedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    (derivation : ScopedNeedNaturalSemantics.Eval examplePrimitive
      ⟨0, 0, ScopedNeed.Examples.sharedPair, ids, Fin.elim0⟩ world
      (.value (.pair ScopedNeed.Examples.headA ScopedNeed.Examples.headA)) final) :
    (.value (.pair ScopedNeed.Examples.headA ScopedNeed.Examples.headA) : ScopedNeedMachine.Outcome Nat Nat Nat 0) ∈
      ScopedNeed.answers (Effect := Nat) examplePrimitive ScopedNeed.Examples.sharedPair ids :=
  ScopedNeed.closed_sound examplePrimitive derivation (by simp [ScopedNeed.MachineRetry])

/-- The completeness of the scoped-need reading, applied to the first world
of the shared pair from the empty heap. -/
theorem sharedPair_complete :
    ∃ (final : ScopedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0) (cells' : List CellId),
      Nonempty (ScopedNeedNaturalSemantics.Eval examplePrimitive ⟨0, 0, ScopedNeed.Examples.sharedPair, ids, Fin.elim0⟩
        ScopedNeedNaturalSemantics.Examples.emptyWorld
        ((runWorldsAt (ScopedNeed.reading (Effect := Nat) examplePrimitive ScopedNeed.Examples.sharedPair ids
          Fin.elim0).1 [] []).head (by decide)).answer final) ∧
      [] <+: cells' ∧
      ScopedNeed.StoreAgrees cells' final
        ((runWorldsAt (ScopedNeed.reading (Effect := Nat) examplePrimitive ScopedNeed.Examples.sharedPair ids
          Fin.elim0).1 [] []).head (by decide)).state ∧
      ScopedNeed.Lands ScopedNeedNaturalSemantics.Examples.emptyWorld final :=
  ScopedNeed.eval_complete examplePrimitive ScopedNeed.Examples.sharedPair ids Fin.elim0 Fin.elim0 Fin.elim0 []
    ScopedNeedNaturalSemantics.Examples.emptyWorld [] [] _ (fun j => j.elim0) ⟨rfl, List.nodup_nil, by simp⟩
    (ScopedNeed.Fresh.empty _ ScopedNeed.Examples.emptyWorld_lookup) (List.head_mem _)

/-- Soundness without need cells, applied to a derivation of the thunked
choice that answers a pair. -/
theorem thunkedCoin_needFree_sound
    {world final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    (derivation : Eval examplePrimitive ⟨0, 0, 0, thunkedCoin.erase, ids, Fin.elim0, Fin.elim0⟩ world
      (.value (.returned (.native (.pair (.head 1) (.head 2))))) final) :
    ∃ answer ∈ PolarizedValues.answers (Effect := Nat) examplePrimitive thunkedCoin ids,
      (.value (.returned (.native (.pair (.head 1) (.head 2)))) :
        PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0) = PolarizedNeedEmbedding.outcome answer :=
  PolarizedValues.needFree_sound examplePrimitive thunkedCoin_needFree ids derivation (by simp [PolarizedValues.MachineRaised])

/-- The agreement on scoped-need code, applied to the shared pair from the
empty heap. -/
theorem sharedPair_embed_agreement (outcome : ScopedNeedMachine.Outcome Nat Nat Nat 0) :
    outcome ∈ PolarizedValues.answers (Effect := Nat) examplePrimitive (embed ScopedNeed.Examples.sharedPair) ids ↔
      ∃ final, Nonempty (ScopedNeedNaturalSemantics.Eval examplePrimitive
        ⟨0, 0, ScopedNeed.Examples.sharedPair, ids, Fin.elim0⟩ ScopedNeedNaturalSemantics.Examples.emptyWorld
          outcome final) :=
  embed_agreement examplePrimitive _ ids _ (ScopedNeed.Fresh.empty _ ScopedNeed.Examples.emptyWorld_lookup) outcome

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.PolarizedNeedCells
