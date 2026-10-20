import Mettapedia.TypeTheory.ContextualCBPVScopedNeed

/-!
# Scoped need: the reading and the natural semantics agree exactly

`ContextualCBPVScopedNeed` shows, from any heap, that every natural derivation
whose outcome is not a retry the machine raises itself is witnessed by a world
of the reading.  This module proves the converse, that every world of the
reading comes from a natural derivation with the same outcome
(`eval_complete`), and soundness for every outcome (`eval_landed`), under the
same two side conditions, so that the two agree exactly (`agreement`; for
closed code, `closed_agreement`).

* `Fresh`: allocation never collides with a cell already in the heap.
* `RefFine`: the cells the code may demand are not being evaluated.

Under both, the machine raises no retry of its own: allocation never
collides, every demanded cell is present and settled, and a producer finishes
owning its cell, so blackholes, missing cells, lost ownership and collisions
do not occur, while a primitive's retryable faults pass through both sides
alike.  Each condition is necessary for each direction.  From a heap that is
not fresh, the reading allocates where the natural semantics collides
(`Examples.collision_negative`, `Examples.collision_unanswered`).  Under a
reference to a cell being evaluated that agrees in every other respect, the
reading runs the producer where the natural semantics finds a blackhole
(`Examples.blackhole_negative`, `Examples.blackhole_unanswered`).

The construction recurses on a weight: a code's size plus a bound on the
weights of the references it may demand, where a reference weighs its
producer's size plus the bound of its own references.  A demanded producer is
lighter than the demand, so the recursion is well founded, and the same weight
shows that no cell reaches itself through the origins of its references
(`RefFine.acyclic`): a cell's own producer never demands it.  Every
derivation from a fresh heap lands in a fresh heap that keeps every cell and
evaluates exactly the cells the starting heap evaluated (`Lands`).
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

/-! ## Weights -/

/-- The size of scoped code. -/
def codeSize : {n k : Nat} → Code Head Operation Effect n k → Nat
  | _, _, .returnValue _ => 1
  | _, _, .call _ _ => 1
  | _, _, .emit _ next => codeSize next + 1
  | _, _, .choose left right => codeSize left + codeSize right + 1
  | _, _, .sequence first body => codeSize first + codeSize body + 1
  | _, _, .sequenceSigma first body => codeSize first + codeSize body + 1
  | _, _, .letNeed suspended body => codeSize suspended + codeSize body + 1
  | _, _, .force _ => 1

/-- The size a cell's producer runs: a choice runs one alternative. -/
def producerSize {n k : Nat} : Code Head Operation Effect n k → Nat
  | .choose left right => max (codeSize left) (codeSize right)
  | code => codeSize code

theorem codeSize_pos {n k : Nat} (code : Code Head Operation Effect n k) : 0 < codeSize code := by
  cases code <;> simp [codeSize]

theorem producerSize_pos {n k : Nat} (code : Code Head Operation Effect n k) : 0 < producerSize code := by
  cases code with
  | choose left right =>
      simp only [producerSize]
      exact lt_of_lt_of_le (codeSize_pos left) (le_max_left _ _)
  | _ => exact codeSize_pos _

theorem producerSize_le {n k : Nat} (code : Code Head Operation Effect n k) :
    producerSize code ≤ codeSize code := by
  cases code with
  | choose left right =>
      simp only [producerSize, codeSize]
      omega
  | _ => exact le_rfl

theorem producerSize_lt_choose {n k : Nat} (left right : Code Head Operation Effect n k) :
    producerSize (Code.choose left right) < codeSize (Code.choose left right) := by
  simp only [producerSize, codeSize]
  omega

/-! ## Fresh allocation -/

/-- Allocation never collides: the cells of the world's lineage are born on a
prefix of its path, and those born on the path itself have smaller slots. -/
def Fresh (world : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  ∀ cell record, world.heap.lookup cell = some record → cell.lineage = world.lineage →
    cell.birth <+: world.path ∧ (cell.birth = world.path → cell.slot < world.nextCell)

/-- Freshness depends only on the allocated cells, the lineage, the path and
the next slot. -/
theorem Fresh.of_same {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world)
    (domain : ∀ cell record, next.heap.lookup cell = some record → ∃ record', world.heap.lookup cell = some record')
    (lineage : next.lineage = world.lineage) (path : next.path = world.path)
    (nextCell : next.nextCell = world.nextCell) : Fresh next := by
  intro cell record present sameLineage
  obtain ⟨record', present'⟩ := domain cell record present
  rw [path, nextCell]
  exact fresh cell record' present' (lineage ▸ sameLineage)

theorem Fresh.record {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) (payload : ReceiptPayload (Closure Head Operation Effect m) ScopedNeedMachine.Rule
      (Tm Head m) StableFault (ScopedNeedMachine.Fault NativeFault) Effect) :
    Fresh (world.record payload).1 :=
  fresh.of_same (fun _cell record present => ⟨record, present⟩) rfl rfl rfl

theorem Fresh.setKnownCache {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (present : world.heap.lookup cell = some record) (state : Cache (Tm Head m) StableFault) :
    Fresh (world.setKnownCache cell record state) := by
  refine fresh.of_same ?_ rfl rfl rfl
  intro other found foundPresent
  simp only [World.setKnownCache] at foundPresent
  rw [lookup_setKnownCache] at foundPresent
  by_cases same : other = cell
  · subst same; exact ⟨record, present⟩
  · rw [if_neg same] at foundPresent; exact ⟨found, foundPresent⟩

theorem Fresh.enter {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) {cell : CellId} {origin : Closure Head Operation Effect m}
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (position : Nat) (rule : ScopedNeedMachine.Rule) :
    Fresh (enterWorld world cell origin position rule) := by
  intro other record found sameLineage
  rw [enterWorld_lookup] at found
  have original : ∃ record', world.heap.lookup other = some record' := by
    by_cases same : other = cell
    · subst same; exact ⟨_, present⟩
    · rw [if_neg same] at found; exact ⟨record, found⟩
  obtain ⟨record', present'⟩ := original
  have lineage : (enterWorld world cell origin position rule).lineage = world.lineage := rfl
  have path : (enterWorld world cell origin position rule).path = world.path ++ [position] := rfl
  have nextCell : (enterWorld world cell origin position rule).nextCell = world.nextCell := rfl
  rw [lineage] at sameLineage
  obtain ⟨isPrefix, _⟩ := fresh other record' present' sameLineage
  rw [path]
  refine ⟨isPrefix.trans (List.prefix_append _ _), fun equal => ?_⟩
  have := isPrefix.length_le
  rw [equal] at this
  simp at this

theorem Fresh.allocate {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) (origin : Closure Head Operation Effect m) :
    ∃ next, world.allocate? origin = some (next, world.freshCell 0) ∧ Fresh next := by
  have absent : world.heap.lookup (world.freshCell 0) = none := by
    cases found : world.heap.lookup (world.freshCell 0) with
    | none => rfl
    | some record =>
        have := (fresh _ record found rfl).2 rfl
        simp [World.freshCell] at this
  unfold World.allocate?
  dsimp only
  have allocated : world.heap.allocate? (world.freshCell 0) origin =
      some { current := Function.update world.heap.current (world.freshCell 0) (some ⟨origin, .suspended⟩),
             spine := .allocate (world.freshCell 0) origin :: world.heap.spine } := by
    unfold Heap.allocate?
    rw [absent]
  rw [allocated]
  refine ⟨_, rfl, ?_⟩
  intro cell record found sameLineage
  simp only [World.record, Heap.lookup] at found sameLineage ⊢
  by_cases same : cell = world.freshCell 0
  · subst same
    simp [World.freshCell]
  · rw [Function.update_of_ne same] at found
    obtain ⟨isPrefix, slot⟩ := fresh cell record found sameLineage
    exact ⟨isPrefix, fun equal => Nat.lt_succ_of_lt (slot equal)⟩

theorem Fresh.empty (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (empty : ∀ cell, world.heap.lookup cell = none) : Fresh world := by
  intro cell record found
  rw [empty cell] at found
  cases found

/-! ## References that are not being evaluated -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

/-- A reference names a cell of the store that is not being evaluated, whose
producer is the reading of the cell's origin, under references of this kind
in turn.  The weight is the producer's size plus a bound on theirs. -/
inductive RefFine (cells : List CellId) (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    CellId → Ref Head Effect StableFault NativeFault m → Nat → Prop where
  | intro {cell : CellId} (index : Nat) (located : cells[index]? = some cell)
      (origin : Closure Head Operation Effect m) (cache : Cache (Tm Head m) StableFault)
      (settled : ∀ owner, cache ≠ .evaluating owner)
      (refs : Fin origin.k → Ref Head Effect StableFault NativeFault m)
      (weights : Fin origin.k → Nat) (bound : Nat) (bounded : ∀ j, weights j ≤ bound)
      (record : world.heap.lookup cell = some ⟨origin, cache⟩)
      (children : ∀ j, RefFine cells world (origin.needs j) (refs j) (weights j)) :
      RefFine cells world cell (index, (reading primitive origin.code origin.values refs).2)
        (producerSize origin.code + bound)

/-- A fine reference names a cell of the heap that is not being evaluated. -/
theorem RefFine.settledRecord {cells : List CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    {ref : Ref Head Effect StableFault NativeFault m} {weight : Nat}
    (fine : RefFine primitive cells world cell ref weight) :
    ∃ origin cache, world.heap.lookup cell = some ⟨origin, cache⟩ ∧ ∀ owner, cache ≠ .evaluating owner := by
  cases fine with
  | intro _ _ origin cache notEvaluating _ _ _ _ record _ => exact ⟨origin, cache, record, notEvaluating⟩

/-- One cell reaches another through the origins of the cells' references. -/
inductive HeapReach (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    CellId → CellId → Prop where
  | refl (cell : CellId) : HeapReach world cell cell
  | step {cell target : CellId} (origin : Closure Head Operation Effect m) (cache : Cache (Tm Head m) StableFault)
      (record : world.heap.lookup cell = some ⟨origin, cache⟩) (j : Fin origin.k)
      (rest : HeapReach world (origin.needs j) target) : HeapReach world cell target

theorem HeapReach.snoc {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {first middle : CellId} (reach : HeapReach world first middle)
    (origin : Closure Head Operation Effect m) (cache : Cache (Tm Head m) StableFault)
    (record : world.heap.lookup middle = some ⟨origin, cache⟩) (j : Fin origin.k) :
    HeapReach world first (origin.needs j) := by
  induction reach with
  | refl cell => exact .step origin cache record j (.refl _)
  | step origin' cache' record' j' _ ih => exact .step origin' cache' record' j' (ih record)

/-- **No cell reaches itself.**  A child weighs less than its parent, so a
cycle through a cell would need a lighter reference to that same cell below
it, and so on without end. -/
theorem RefFine.acyclic {cells : List CellId} {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
    ∀ (weight : Nat) {cell : CellId} {ref : Ref Head Effect StableFault NativeFault m},
      RefFine primitive cells world cell ref weight →
      ∀ (origin : Closure Head Operation Effect m) (cache : Cache (Tm Head m) StableFault),
        world.heap.lookup cell = some ⟨origin, cache⟩ → ∀ j, ¬ HeapReach world (origin.needs j) cell := by
  intro weight
  induction weight using Nat.strong_induction_on with
  | _ weight ih =>
    intro cell ref fine origin cache present j reach
    cases fine with
    | intro index located origin' cache' settled refs weights bound bounded record children =>
      rw [present] at record
      cases record
      have lighter : weights j < producerSize origin.code + bound :=
        lt_of_le_of_lt (bounded j) (by have := producerSize_pos origin.code; omega)
      -- the child reaches the cell, and the cell reaches the child: a cycle at the child
      cases reach with
      | refl _ =>
          exact ih (weights j) lighter (children j) origin cache present j (.refl _)
      | step childOrigin childCache childRecord j' rest =>
          exact ih (weights j) lighter (children j) childOrigin childCache childRecord j'
            (rest.snoc origin cache present j)

/-- A reference stays fine where every cell it reaches is unchanged. -/
theorem RefFine.transport {cells cells' : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {ref : Ref Head Effect StableFault NativeFault m} {weight : Nat}
    (fine : RefFine primitive cells world cell ref weight) (isPrefix : cells <+: cells')
    (same : ∀ target, HeapReach world cell target → next.heap.lookup target = world.heap.lookup target) :
    RefFine primitive cells' next cell ref weight := by
  revert same
  induction fine with
  | intro index located origin cache settled refs weights bound bounded record children ih =>
      intro same
      refine .intro index (prefix_getElem? isPrefix located) origin cache settled refs weights bound bounded
        ?_ (fun j => ih j (fun target reach => same target (.step origin cache record j reach)))
      rw [same _ (.refl _)]
      exact record

/-- A reference stays fine in a heap that keeps every cell and evaluates no
new one. -/
theorem RefFine.mono {cells cells' : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {ref : Ref Head Effect StableFault NativeFault m} {weight : Nat}
    (fine : RefFine primitive cells world cell ref weight) (isPrefix : cells <+: cells')
    (extends' : Extends world next)
    (noNew : ∀ target record owner, next.heap.lookup target = some record →
      record.cache = .evaluating owner → world.heap.lookup target = some record) :
    RefFine primitive cells' next cell ref weight := by
  induction fine with
  | intro index located origin cache settled refs weights bound bounded record children ih =>
      obtain ⟨cache', record'⟩ := extends' _ origin cache record
      refine .intro index (prefix_getElem? isPrefix located) origin cache' ?_ refs weights bound bounded
        record' ih
      intro owner evaluating
      have earlier := noNew _ ⟨origin, cache'⟩ owner record' evaluating
      rw [record] at earlier
      cases earlier
      exact settled owner evaluating

/-! ## Where a derivation lands -/

/-- The final heap of a derivation from a fresh heap: still fresh, keeping
every cell, evaluating exactly the cells the starting heap evaluated. -/
structure Lands (world final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop where
  fresh : Fresh final
  extends' : Extends world final
  keeps : ∀ cell record owner, world.heap.lookup cell = some record → record.cache = .evaluating owner →
    final.heap.lookup cell = some record
  noNew : ∀ cell record owner, final.heap.lookup cell = some record → record.cache = .evaluating owner →
    world.heap.lookup cell = some record

theorem Lands.of_heap {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh next) (same : next.heap = world.heap) : Lands world next :=
  ⟨fresh, Extends.of_heap same, fun cell record _ present _ => by rw [same]; exact present,
    fun cell record _ present _ => by rw [← same]; exact present⟩

theorem Lands.trans {world middle final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (first : Lands world middle) (second : Lands middle final) : Lands world final :=
  ⟨second.fresh, first.extends'.trans second.extends',
    fun cell record owner present evaluating =>
      second.keeps cell record owner (first.keeps cell record owner present evaluating) evaluating,
    fun cell record owner present evaluating =>
      first.noNew cell record owner (second.noNew cell record owner present evaluating) evaluating⟩

theorem Lands.alloc {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) (fresh : Fresh next) : Lands world next := by
  obtain ⟨absent, present, others⟩ := allocate_fresh allocated
  refine ⟨fresh, Extends.alloc allocated, ?_, ?_⟩
  · intro other record owner found _
    have different : other ≠ cell := by
      intro equal; subst equal; rw [absent] at found; cases found
    rw [others other different]; exact found
  · intro other record owner found evaluating
    by_cases same : other = cell
    · subst same
      rw [present] at found
      cases found
      cases evaluating
    · rw [others other same] at found; exact found

/-- A finalization by the owner answers the body's outcome and caches it. -/
theorem finalize_of_owned {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {owner : EvaluatorId}
    {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (present : world.heap.lookup cell = some record) (owned : record.cache = .evaluating owner)
    (outcome : Outcome Head StableFault NativeFault m) :
    (finalize world cell owner outcome).1 = outcome ∧
      (finalize world cell owner outcome).2.heap = (world.setKnownCache cell record (cacheOf outcome)).heap ∧
      (finalize world cell owner outcome).2.lineage = world.lineage ∧
      (finalize world cell owner outcome).2.path = world.path ∧
      (finalize world cell owner outcome).2.nextCell = world.nextCell := by
  unfold finalize
  rw [present]
  simp only [owned, if_true]
  cases outcome <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Completeness -/

theorem mem_bind_inv {Answer Other : Type}
    {program : Program (Store Head StableFault NativeFault m) Answer Effect}
    {next : Answer → Program (Store Head StableFault NativeFault m) Other Effect}
    {store : Store Head StableFault NativeFault m} {branch : BranchTrace}
    {result : WorldResult (Store Head StableFault NativeFault m) Other Effect}
    (member : result ∈ runWorldsAt (program.bind next) store branch) :
    ∃ first ∈ runWorldsAt program store branch,
      ∃ second ∈ runWorldsAt (next first.answer) first.state first.branch,
        result = WorldResult.prependIntents first.intents second := by
  rw [runWorldsAt_bind] at member
  obtain ⟨first, firstMember, inner⟩ := List.mem_flatMap.mp member
  obtain ⟨second, secondMember, equal⟩ := List.mem_map.mp inner
  exact ⟨first, firstMember, second, secondMember, equal.symm⟩

/-- The reference of a cell just allocated for an origin is fine. -/
theorem RefFine.allocated {cells : List CellId}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {store : Store Head StableFault NativeFault m} (agrees : StoreAgrees cells world store)
    {n k : Nat} {code : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {refs : Fin k → Ref Head Effect StableFault NativeFault m} {weights : Fin k → Nat} {bound : Nat}
    (bounded : ∀ j, weights j ≤ bound)
    (fine : ∀ j, RefFine primitive cells world (needs j) (refs j) (weights j)) {cell : CellId}
    (allocated : world.allocate? ⟨n, k, code, values, needs⟩ = some (next, cell)) (freshNext : Fresh next) :
    RefFine primitive (cells ++ [cell]) next cell (store.length, (reading primitive code values refs).2)
      (producerSize code + bound) :=
  .intro store.length (located_last agrees.length cell) ⟨n, k, code, values, needs⟩ .suspended
    (fun owner equal => by cases equal) refs weights bound bounded (allocate_fresh allocated).2.1
    (fun j => (fine j).mono primitive (List.prefix_append _ _) (Extends.alloc allocated)
      (Lands.alloc allocated freshNext).noNew)

/-- Completeness of evaluation for code that weighs at most `limit`. -/
def EvalComplete (limit : Nat) : Prop :=
  ∀ {n k : Nat} (code : Code Head Operation Effect n k) (values : Sub Head n m) (needs : Fin k → CellId)
    (refs : Fin k → Ref Head Effect StableFault NativeFault m) (weights : Fin k → Nat) (bound : Nat)
    (cells : List CellId) (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    (result : WorldResult (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect),
    codeSize code + bound ≤ limit → (∀ j, weights j ≤ bound) →
    (∀ j, RefFine primitive cells world (needs j) (refs j) (weights j)) →
    StoreAgrees cells world store → Fresh world →
    result ∈ runWorldsAt (reading primitive code values refs).1 store branch →
    ∃ (final : NeedWorld Head Operation Effect StableFault NativeFault m) (cells' : List CellId),
      Nonempty (Eval primitive ⟨n, k, code, values, needs⟩ world result.answer final) ∧
      cells <+: cells' ∧ StoreAgrees cells' final result.state ∧ Lands world final

/-- Completeness of demand for references that weigh at most `limit`. -/
def ForceComplete (limit : Nat) : Prop :=
  ∀ (cell : CellId) (ref : Ref Head Effect StableFault NativeFault m) (weight : Nat) (cells : List CellId)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    (result : WorldResult (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect),
    weight ≤ limit → RefFine primitive cells world cell ref weight →
    StoreAgrees cells world store → Fresh world →
    result ∈ runWorldsAt (demand ref.1 ref.2) store branch →
    ∃ (final : NeedWorld Head Operation Effect StableFault NativeFault m) (cells' : List CellId),
      Nonempty (Force primitive cell world result.answer final) ∧
      cells <+: cells' ∧ StoreAgrees cells' final result.state ∧ Lands world final

/-- The weights of a selected occurrence's references: those of its origin. -/
def selectionWeights {origin picked : Closure Head Operation Effect m} {position : Nat}
    {rule : ScopedNeedMachine.Rule} :
    Selection origin position rule picked → (Fin origin.k → Nat) → Fin picked.k → Nat
  | .entry _, weights => weights
  | .left _ _ _ _, weights => weights
  | .right _ _ _ _, weights => weights

theorem selection_fine {cells : List CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin picked : Closure Head Operation Effect m} {position : Nat} {rule : ScopedNeedMachine.Rule}
    (selection : Selection origin position rule picked)
    (refs : Fin origin.k → Ref Head Effect StableFault NativeFault m) (weights : Fin origin.k → Nat)
    (fine : ∀ j, RefFine primitive cells world (origin.needs j) (refs j) (weights j)) :
    ∀ j, RefFine primitive cells world (picked.needs j) (selectionRefs selection refs j)
      (selectionWeights selection weights j) := by
  cases selection <;> exact fine

theorem selection_bounded {origin picked : Closure Head Operation Effect m} {position : Nat}
    {rule : ScopedNeedMachine.Rule} (selection : Selection origin position rule picked)
    (weights : Fin origin.k → Nat) {bound : Nat} (bounded : ∀ j, weights j ≤ bound) :
    ∀ j, selectionWeights selection weights j ≤ bound := by
  cases selection <;> exact bounded

theorem cacheOf_ne_evaluating (outcome : Outcome Head StableFault NativeFault m) (owner : EvaluatorId) :
    cacheOf outcome ≠ .evaluating owner := by
  cases outcome <;> simp [cacheOf]

/-- **A demand is a natural force**, given complete evaluation at its weight. -/
theorem force_of_eval {limit : Nat} (eval : EvalComplete (Effect := Effect) primitive limit) :
    ForceComplete (Effect := Effect) primitive limit := by
  intro cell ref weight cells world store branch result weightBound fine agrees fresh member
  cases fine with
  | intro index located origin cache settled refs weights bound bounded record children =>
    simp only at member
    cases cached : store.getD index none with
    | some outcome =>
        -- a cached value or stable fault is served again
        have agreesCache := agrees.cached located record
        rw [cached] at agreesCache
        rw [demand_cached _ _ store branch outcome cached] at member
        rw [List.mem_singleton] at member
        subst member
        cases agreesCache with
        | value value =>
            exact ⟨_, cells, ⟨Force.cachedValue record⟩, List.prefix_refl _, agrees.of_heap rfl,
              Lands.of_heap (fresh.record _) rfl⟩
        | stableFault fault =>
            exact ⟨_, cells, ⟨Force.cachedStable record⟩, List.prefix_refl _, agrees.of_heap rfl,
              Lands.of_heap (fresh.record _) rfl⟩
    | none =>
        -- a pending cell is suspended, not evaluated
        have agreesCache := agrees.cached located record
        rw [cached] at agreesCache
        have suspended : cache = .suspended := by
          cases agreesCache with
          | suspended => rfl
          | evaluating owner => exact absurd rfl (settled owner)
        subst suspended
        rw [demand_pending _ _ store branch cached] at member
        obtain ⟨first, firstMember, second, secondMember, rfl⟩ := mem_bind_inv member
        rw [settle_run, List.mem_singleton] at secondMember
        subst secondMember
        -- the selected occurrence and the producer's world
        have selected : ∃ (position : Nat) (rule : ScopedNeedMachine.Rule) (picked : Closure Head Operation Effect m)
            (selection : Selection origin position rule picked),
            codeSize picked.code ≤ producerSize origin.code ∧
            first ∈ runWorldsAt (reading primitive picked.code picked.values (selectionRefs selection refs)).1
              store (selectionBranch selection branch) := by
          obtain ⟨n, k, code, values, needs⟩ := origin
          cases code with
          | choose left right =>
              simp only [reading, runWorldsAt] at firstMember
              rcases List.mem_append.mp firstMember with leftMember | rightMember
              · exact ⟨0, .left, _, .left left right values needs,
                  by simp only [producerSize]; exact le_max_left _ _, leftMember⟩
              · exact ⟨1, .right, _, .right left right values needs,
                  by simp only [producerSize]; exact le_max_right _ _, rightMember⟩
          | _ =>
              refine ⟨0, .entry, _, .entry (by intro left right equal; cases equal), le_rfl, ?_⟩
              simpa only [selectionRefs, selectionBranch, reading] using firstMember
        obtain ⟨position, rule, picked, selection, smaller, pickedMember⟩ := selected
        have agreesEnter := agrees.enter record position rule
        have freshEnter := fresh.enter record position rule
        -- the producer's references stay fine: they never reach the cell
        have whole : RefFine primitive cells world cell
            (index, (reading primitive origin.code origin.values refs).2) (producerSize origin.code + bound) :=
          .intro index located origin .suspended settled refs weights bound bounded record children
        have childrenEnter : ∀ j, RefFine primitive cells (enterWorld world cell origin position rule)
            (origin.needs j) (refs j) (weights j) := by
          intro j
          refine (children j).transport primitive (List.prefix_refl _) ?_
          intro target reach
          rw [enterWorld_lookup]
          have different : target ≠ cell := by
            intro equal
            subst equal
            exact RefFine.acyclic primitive _ whole origin .suspended record j reach
          rw [if_neg different]
        obtain ⟨bodyFinal, cells₁, ⟨body⟩, isPrefix, agrees₁, landed⟩ :=
          eval picked.code picked.values picked.needs (selectionRefs selection refs)
            (selectionWeights selection weights) bound cells _ store (selectionBranch selection branch) first
            (by omega) (selection_bounded selection weights bounded)
            (selection_fine primitive selection refs weights childrenEnter) agreesEnter freshEnter pickedMember
        -- the cell is still evaluated by its owner; finalization caches the outcome
        have owned : bodyFinal.heap.lookup cell = some ⟨origin, .evaluating world.nextEvaluator⟩ := by
          refine landed.keeps cell _ world.nextEvaluator ?_ rfl
          rw [enterWorld_lookup, if_pos rfl]
        obtain ⟨outcomeEq, heapEq, lineageEq, pathEq, nextEq⟩ :=
          finalize_of_owned owned rfl first.answer
        have located₁ := prefix_getElem? isPrefix located
        have pending₁ : first.state.getD index none = none :=
          (agrees₁.cached located₁ owned).none_of_evaluating
        have bound₁ : index < first.state.length := by
          rw [← agrees₁.length]
          exact (List.getElem?_eq_some_iff.mp located₁).1
        have force := Force.suspended record selection body
        rw [outcomeEq] at force
        refine ⟨_, cells₁, ⟨force⟩, isPrefix, ?_, ?_⟩
        · exact (agrees₁.replace located₁ (cacheOf first.answer) (settled_length _ _ _)
            (settled_agrees index first.answer first.state bound₁ pending₁)
            (fun other different => settled_other index other different _ _)).of_heap heapEq
        · -- the final heap: the cell settled, every other cell as the producer left it
          have finalLookup : ∀ target, (finalize bodyFinal cell world.nextEvaluator first.answer).2.heap.lookup target =
              if target = cell then some ⟨origin, cacheOf first.answer⟩ else bodyFinal.heap.lookup target := by
            intro target
            rw [heapEq]
            simp only [World.setKnownCache]
            rw [lookup_setKnownCache]
          have enterLookup : ∀ target, target ≠ cell →
              (enterWorld world cell origin position rule).heap.lookup target = world.heap.lookup target := by
            intro target different
            rw [enterWorld_lookup, if_neg different]
          refine ⟨?_, ?_, ?_, ?_⟩
          · refine landed.fresh.of_same ?_ lineageEq pathEq nextEq
            intro target found present
            rw [finalLookup] at present
            by_cases same : target = cell
            · subst same; exact ⟨_, owned⟩
            · rw [if_neg same] at present; exact ⟨found, present⟩
          · exact (Extends.enter record position rule).trans (landed.extends'.trans
              ((Extends.setKnownCache owned (cacheOf first.answer)).trans (Extends.of_heap heapEq)))
          · intro target found owner present evaluating
            have different : target ≠ cell := by
              intro equal; subst equal; rw [record] at present; cases present; cases evaluating
            rw [finalLookup, if_neg different]
            refine landed.keeps target found owner ?_ evaluating
            rw [enterLookup target different]; exact present
          · intro target found owner present evaluating
            rw [finalLookup] at present
            by_cases same : target = cell
            · subst same
              rw [if_pos rfl] at present
              cases present
              exact absurd evaluating (cacheOf_ne_evaluating _ _)
            · rw [if_neg same] at present
              have earlier := landed.noNew target found owner present evaluating
              rw [enterLookup target same] at earlier
              exact earlier

/-- **Evaluation is a natural derivation**, given completeness below its weight. -/
theorem eval_step {limit : Nat}
    (lower : ∀ smaller < limit, EvalComplete (Effect := Effect) primitive smaller ∧
      ForceComplete (Effect := Effect) primitive smaller) :
    EvalComplete (Effect := Effect) primitive limit := by
  intro n k code values needs refs weights bound cells world store branch result measure bounded fine agrees
    fresh member
  -- every reference keeps its weight in a later heap
  have later : ∀ {cells' : List CellId} {next : NeedWorld Head Operation Effect StableFault NativeFault m},
      cells <+: cells' → Lands world next → ∀ j, RefFine primitive cells' next (needs j) (refs j) (weights j) :=
    fun isPrefix landed j => (fine j).mono primitive isPrefix landed.extends' landed.noNew
  cases code with
  | returnValue term =>
      simp only [reading, runWorldsAt, List.mem_singleton] at member
      subst member
      exact ⟨world, cells, ⟨Eval.returnValue term values needs world⟩, List.prefix_refl _, agrees,
        Lands.of_heap fresh rfl⟩
  | call operation argument =>
      simp only [reading, runWorldsAt, List.mem_singleton] at member
      subst member
      exact ⟨world, cells, ⟨Eval.call operation argument values needs world⟩, List.prefix_refl _, agrees,
        Lands.of_heap fresh rfl⟩
  | emit effect next =>
      simp only [reading, runWorldsAt] at member
      obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
      simp only [codeSize] at measure
      obtain ⟨final, cells', ⟨derivation⟩, isPrefix, agrees', landed⟩ :=
        (lower (codeSize next + bound) (by omega)).1 next values needs refs weights bound cells
          (world.record (.effect effect)).1 store branch inner le_rfl bounded
          (fun j => (fine j).transport primitive (List.prefix_refl _) (fun _ _ => rfl))
          (agrees.of_heap rfl) (fresh.record _) innerMember
      exact ⟨final, cells', ⟨Eval.emit effect derivation⟩, isPrefix, agrees',
        (Lands.of_heap (world := world) (fresh.record _) rfl).trans landed⟩
  | force reference =>
      simp only [codeSize] at measure
      obtain ⟨final, cells', ⟨derivation⟩, isPrefix, agrees', landed⟩ :=
        (lower (weights reference) (by have := bounded reference; omega)).2 (needs reference) (refs reference)
          (weights reference) cells world store branch result le_rfl (fine reference) agrees fresh member
      exact ⟨final, cells', ⟨Eval.force reference derivation⟩, isPrefix, agrees', landed⟩
  | choose left right =>
      simp only [codeSize] at measure
      obtain ⟨allocated, allocation, freshAllocated⟩ := fresh.allocate ⟨n, k, .choose left right, values, needs⟩
      simp only [reading] at member
      rw [alloc_run] at member
      obtain ⟨final, cells', ⟨derivation⟩, isPrefix, agrees', landed⟩ :=
        (lower (producerSize (Code.choose left right) + bound)
            (by have := producerSize_lt_choose left right; simp only [codeSize] at this; omega)).2
          _ _ _ _ allocated _ branch result le_rfl
          (RefFine.allocated primitive agrees bounded fine allocation freshAllocated)
          (agrees.alloc allocation) freshAllocated member
      exact ⟨final, cells', ⟨Eval.choose left right allocation derivation⟩,
        (List.prefix_append _ _).trans isPrefix, agrees', (Lands.alloc allocation freshAllocated).trans landed⟩
  | sequence first body =>
      simp only [codeSize] at measure
      obtain ⟨allocated, allocation, freshAllocated⟩ := fresh.allocate ⟨n, k, first, values, needs⟩
      simp only [reading] at member
      rw [alloc_run] at member
      obtain ⟨demanded, demandedMember, rest, restMember, rfl⟩ := mem_bind_inv member
      obtain ⟨middle, cells₁, ⟨forced⟩, prefix₁, agrees₁, landed₁⟩ :=
        (lower (producerSize first + bound) (by have := producerSize_le first; omega)).2
          _ _ _ _ allocated _ branch demanded le_rfl
          (RefFine.allocated primitive agrees bounded fine allocation freshAllocated)
          (agrees.alloc allocation) freshAllocated demandedMember
      have landedMiddle := (Lands.alloc allocation freshAllocated).trans landed₁
      have prefixMiddle := (List.prefix_append cells _).trans prefix₁
      cases answer : demanded.answer with
      | value value =>
          rw [answer] at restMember forced
          simp only [onValue] at restMember
          obtain ⟨final, cells₂, ⟨continued⟩, prefix₂, agrees₂, landed₂⟩ :=
            (lower (codeSize body + bound) (by omega)).1 body (Fin.cases value values) needs refs weights bound
              cells₁ middle demanded.state demanded.branch rest le_rfl bounded (later prefixMiddle landedMiddle)
              agrees₁ landed₁.fresh restMember
          exact ⟨final, cells₂, ⟨Eval.sequenceValue allocation forced continued⟩, prefixMiddle.trans prefix₂,
            agrees₂, landedMiddle.trans landed₂⟩
      | stableFault fault =>
          rw [answer] at restMember forced
          simp only [onValue, runWorldsAt, List.mem_singleton] at restMember
          subst restMember
          exact ⟨middle, cells₁, ⟨Eval.sequenceStable body allocation forced⟩, prefixMiddle, agrees₁, landedMiddle⟩
      | retryableFault reason =>
          rw [answer] at restMember forced
          simp only [onValue, runWorldsAt, List.mem_singleton] at restMember
          subst restMember
          exact ⟨middle, cells₁, ⟨Eval.sequenceRetry body allocation forced⟩, prefixMiddle, agrees₁, landedMiddle⟩
  | sequenceSigma first body =>
      simp only [codeSize] at measure
      obtain ⟨allocated, allocation, freshAllocated⟩ := fresh.allocate ⟨n, k, first, values, needs⟩
      simp only [reading] at member
      rw [alloc_run] at member
      obtain ⟨demanded, demandedMember, rest, restMember, rfl⟩ := mem_bind_inv member
      obtain ⟨middle, cells₁, ⟨forced⟩, prefix₁, agrees₁, landed₁⟩ :=
        (lower (producerSize first + bound) (by have := producerSize_le first; omega)).2
          _ _ _ _ allocated _ branch demanded le_rfl
          (RefFine.allocated primitive agrees bounded fine allocation freshAllocated)
          (agrees.alloc allocation) freshAllocated demandedMember
      have landedMiddle := (Lands.alloc allocation freshAllocated).trans landed₁
      have prefixMiddle := (List.prefix_append cells _).trans prefix₁
      cases answer : demanded.answer with
      | value value =>
          rw [answer] at restMember forced
          simp only [onValue] at restMember
          rw [runWorldsAt_map] at restMember
          obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp restMember
          obtain ⟨final, cells₂, ⟨continued⟩, prefix₂, agrees₂, landed₂⟩ :=
            (lower (codeSize body + bound) (by omega)).1 body (Fin.cases value values) needs refs weights bound
              cells₁ middle demanded.state demanded.branch inner le_rfl bounded (later prefixMiddle landedMiddle)
              agrees₁ landed₁.fresh innerMember
          exact ⟨final, cells₂, ⟨Eval.sequenceSigmaValue allocation forced continued⟩, prefixMiddle.trans prefix₂,
            agrees₂, landedMiddle.trans landed₂⟩
      | stableFault fault =>
          rw [answer] at restMember forced
          simp only [onValue, runWorldsAt, List.mem_singleton] at restMember
          subst restMember
          exact ⟨middle, cells₁, ⟨Eval.sequenceSigmaStable body allocation forced⟩, prefixMiddle, agrees₁,
            landedMiddle⟩
      | retryableFault reason =>
          rw [answer] at restMember forced
          simp only [onValue, runWorldsAt, List.mem_singleton] at restMember
          subst restMember
          exact ⟨middle, cells₁, ⟨Eval.sequenceSigmaRetry body allocation forced⟩, prefixMiddle, agrees₁,
            landedMiddle⟩
  | letNeed suspended body =>
      simp only [codeSize] at measure
      obtain ⟨allocated, allocation, freshAllocated⟩ := fresh.allocate ⟨n, k, suspended, values, needs⟩
      simp only [reading] at member
      rw [alloc_run] at member
      have landedAllocated := Lands.alloc allocation freshAllocated
      obtain ⟨final, cells', ⟨continued⟩, isPrefix, agrees', landed⟩ :=
        (lower (codeSize body + (producerSize suspended + bound))
            (by have := producerSize_le suspended; omega)).1 body values
          (Fin.cases (world.freshCell 0) needs)
          (Fin.cases (store.length, (reading primitive suspended values refs).2) refs)
          (Fin.cases (producerSize suspended + bound) weights) (producerSize suspended + bound)
          (cells ++ [world.freshCell 0]) allocated (store ++ [none]) branch result le_rfl
          (by
            intro j
            refine Fin.cases ?_ (fun j' => ?_) j
            · exact le_rfl
            · have := bounded j'; simp only [Fin.cases_succ]; omega)
          (by
            intro j
            refine Fin.cases ?_ (fun j' => ?_) j
            · exact RefFine.allocated primitive agrees bounded fine allocation freshAllocated
            · exact (fine j').mono primitive (List.prefix_append _ _) landedAllocated.extends'
                landedAllocated.noNew)
          (agrees.alloc allocation) freshAllocated member
      exact ⟨final, cells', ⟨Eval.letNeed allocation continued⟩, (List.prefix_append _ _).trans isPrefix,
        agrees', landedAllocated.trans landed⟩

/-- **Completeness at every weight.** -/
theorem complete (limit : Nat) :
    EvalComplete (Effect := Effect) primitive limit ∧ ForceComplete (Effect := Effect) primitive limit := by
  induction limit using Nat.strong_induction_on with
  | _ limit ih =>
      have eval : EvalComplete (Effect := Effect) primitive limit := eval_step primitive ih
      exact ⟨eval, force_of_eval primitive eval⟩

/-! ## Soundness for every outcome -/

theorem Fresh.allocated {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) {origin : Closure Head Operation Effect m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) : Fresh next := by
  obtain ⟨next', allocated', freshNext⟩ := fresh.allocate origin
  rw [allocated] at allocated'
  cases allocated'
  exact freshNext

theorem Fresh.allocate_ne_none {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) (origin : Closure Head Operation Effect m) : world.allocate? origin ≠ none := by
  obtain ⟨next, allocated, _⟩ := fresh.allocate origin
  rw [allocated]
  exact Option.some_ne_none _

theorem exists_bound {k : Nat} (weights : Fin k → Nat) : ∃ bound, ∀ j, weights j ≤ bound :=
  ⟨∑ j, weights j, fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)⟩

/-- A world of the program answers the outcome, its store agrees with the
final heap, and the derivation lands there. -/
abbrev Landed (cells : List CellId)
    (world final : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (program : Run Head Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace) : Prop :=
  ∃ (cells' : List CellId)
    (result : WorldResult (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect),
    cells <+: cells' ∧ StoreAgrees cells' final result.state ∧ Lands world final ∧
      result ∈ runWorldsAt program store branch ∧ result.answer = outcome

mutual

/-- **Every natural evaluation is witnessed by the reading, whatever its
outcome**, from a fresh heap that agrees with the store, under references to
cells that are not being evaluated.  The machine raises no retry of its own
there: allocation never collides, every demanded cell is present and settled,
and every producer finishes owning its cell. -/
theorem eval_landed : {closure : Closure Head Operation Effect m} →
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} →
    {outcome : Outcome Head StableFault NativeFault m} →
    Eval primitive closure world outcome final →
    (cells : List CellId) → (store : Store Head StableFault NativeFault m) →
    (refs : Fin closure.k → Ref Head Effect StableFault NativeFault m) → (weights : Fin closure.k → Nat) →
    (branch : BranchTrace) →
    StoreAgrees cells world store → Fresh world →
    (∀ j, RefFine primitive cells world (closure.needs j) (refs j) (weights j)) →
    Landed cells world final outcome (reading primitive closure.code closure.values refs).1 store branch
  | _, _, _, _, .returnValue term values _ _, cells, store, _, _, branch, agrees, fresh, _ =>
      ⟨cells, ⟨branch, .value (subst values term), store, []⟩, List.prefix_refl _, agrees,
        Lands.of_heap fresh rfl, by simp [reading, runWorldsAt], rfl⟩
  | _, _, _, _, .call operation argument values _ _, cells, store, _, _, branch, agrees, fresh, _ =>
      ⟨cells, ⟨branch, ScopedNeedMachine.liftOutcome (primitive operation (subst values argument)), store, []⟩,
        List.prefix_refl _, agrees, Lands.of_heap fresh rfl, by simp [reading, runWorldsAt], rfl⟩
  | _, world, _, _, .emit effect nextDerivation, cells, store, refs, weights, branch, agrees, fresh, fine => by
      obtain ⟨cells', result, isPrefix, agrees', landed, member, answer⟩ :=
        eval_landed nextDerivation cells store refs weights branch (agrees.of_heap rfl) (fresh.record _)
          (fun j => (fine j).transport primitive (List.prefix_refl _) (fun _ _ => rfl))
      refine ⟨cells', { result with intents := effect :: result.intents }, isPrefix, agrees',
        (Lands.of_heap (world := world) (fresh.record _) rfl).trans landed, ?_, answer⟩
      simp only [reading, runWorldsAt]
      exact List.mem_map.mpr ⟨result, member, rfl⟩
  | _, _, _, _, .force reference forceDerivation, cells, store, refs, weights, branch, agrees, fresh, fine =>
      force_landed forceDerivation cells store (refs reference) (weights reference) branch agrees fresh
        (fine reference)
  | _, _, _, _, .sequenceValue allocated forceDerivation bodyDerivation, cells, store, refs, weights, branch,
      agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      have landedMiddle := (Lands.alloc allocated freshAllocated).trans landed₂
      have prefixMiddle := (List.prefix_append cells _).trans prefix₂
      obtain ⟨cells₃, second, prefix₃, agrees₃, landed₃, secondMember, secondAnswer⟩ :=
        eval_landed bodyDerivation cells₂ first.state refs weights first.branch agrees₂ landed₂.fresh
          (fun j => (fine j).mono primitive prefixMiddle landedMiddle.extends' landedMiddle.noNew)
      refine ⟨cells₃, WorldResult.prependIntents first.intents second, prefixMiddle.trans prefix₃, agrees₃,
        landedMiddle.trans landed₃, ?_, secondAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      exact secondMember
  | _, _, _, _, .sequenceStable _ allocated forceDerivation, cells, store, refs, weights, branch,
      agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Lands.alloc allocated freshAllocated).trans landed₂,
        ?_, firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .sequenceRetry _ allocated forceDerivation, cells, store, refs, weights, branch,
      agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Lands.alloc allocated freshAllocated).trans landed₂,
        ?_, firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .sequenceSigmaValue (value := value) allocated forceDerivation bodyDerivation, cells, store,
      refs, weights, branch, agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      have landedMiddle := (Lands.alloc allocated freshAllocated).trans landed₂
      have prefixMiddle := (List.prefix_append cells _).trans prefix₂
      obtain ⟨cells₃, second, prefix₃, agrees₃, landed₃, secondMember, secondAnswer⟩ :=
        eval_landed bodyDerivation cells₂ first.state refs weights first.branch agrees₂ landed₂.fresh
          (fun j => (fine j).mono primitive prefixMiddle landedMiddle.extends' landedMiddle.noNew)
      refine ⟨cells₃,
        WorldResult.prependIntents first.intents (WorldResult.mapAnswer (pairOutcome value) second),
        prefixMiddle.trans prefix₃, agrees₃, landedMiddle.trans landed₃, ?_, ?_⟩
      · simp only [reading]
        rw [alloc_run]
        refine mem_bind firstMember ?_
        rw [firstAnswer]
        simp only [onValue]
        rw [runWorldsAt_map]
        exact List.mem_map.mpr ⟨second, secondMember, rfl⟩
      · simp [WorldResult.prependIntents, WorldResult.mapAnswer, secondAnswer]
  | _, _, _, _, .sequenceSigmaStable _ allocated forceDerivation, cells, store, refs, weights, branch,
      agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Lands.alloc allocated freshAllocated).trans landed₂,
        ?_, firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .sequenceSigmaRetry _ allocated forceDerivation, cells, store, refs, weights, branch,
      agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      refine ⟨cells₂, WorldResult.prependIntents first.intents ⟨first.branch, first.answer, first.state, []⟩,
        (List.prefix_append _ _).trans prefix₂, agrees₂, (Lands.alloc allocated freshAllocated).trans landed₂,
        ?_, firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      refine mem_bind firstMember ?_
      rw [firstAnswer]
      simp [onValue, runWorldsAt]
  | _, _, _, _, .choose left right allocated forceDerivation, cells, store, refs, weights, branch,
      agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      obtain ⟨cells₂, first, prefix₂, agrees₂, landed₂, firstMember, firstAnswer⟩ :=
        force_landed forceDerivation _ _ _ _ branch (agrees.alloc allocated) freshAllocated
          (RefFine.allocated primitive agrees bounded fine allocated freshAllocated)
      refine ⟨cells₂, first, (List.prefix_append _ _).trans prefix₂, agrees₂,
        (Lands.alloc allocated freshAllocated).trans landed₂, ?_, firstAnswer⟩
      simp only [reading]
      rw [alloc_run]
      exact firstMember
  | _, _, _, _, .letNeed (suspended := suspended) (values := values) allocated bodyDerivation, cells,
      store, refs, weights, branch, agrees, fresh, fine => by
      obtain ⟨bound, bounded⟩ := exists_bound weights
      have freshAllocated := fresh.allocated allocated
      have landedAllocated := Lands.alloc allocated freshAllocated
      obtain ⟨cells₂, result, prefix₂, agrees₂, landed₂, member, answer⟩ :=
        eval_landed bodyDerivation _ _
          (Fin.cases (store.length, (reading primitive suspended values refs).2) refs)
          (Fin.cases (producerSize suspended + bound) weights) branch (agrees.alloc allocated) freshAllocated (by
          intro j
          refine Fin.cases ?_ (fun j' => ?_) j
          · exact RefFine.allocated primitive agrees bounded fine allocated freshAllocated
          · exact (fine j').mono primitive (List.prefix_append _ _) landedAllocated.extends'
              landedAllocated.noNew)
      refine ⟨cells₂, result, (List.prefix_append _ _).trans prefix₂, agrees₂, landedAllocated.trans landed₂,
        ?_, answer⟩
      simp only [reading]
      rw [alloc_run]
      exact member
  | _, _, _, _, .sequenceAllocationFailure _ failed, _, _, _, _, _, _, fresh, _ =>
      absurd failed (fresh.allocate_ne_none _)
  | _, _, _, _, .sequenceSigmaAllocationFailure _ failed, _, _, _, _, _, _, fresh, _ =>
      absurd failed (fresh.allocate_ne_none _)
  | _, _, _, _, .chooseAllocationFailure _ _ failed, _, _, _, _, _, _, fresh, _ =>
      absurd failed (fresh.allocate_ne_none _)
  | _, _, _, _, .letNeedAllocationFailure _ failed, _, _, _, _, _, _, fresh, _ =>
      absurd failed (fresh.allocate_ne_none _)

/-- **Every natural force is witnessed by the demand of its reference, whatever
its outcome**, for a reference to a cell that is not being evaluated. -/
theorem force_landed : {cell : CellId} →
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} →
    {outcome : Outcome Head StableFault NativeFault m} →
    Force primitive cell world outcome final →
    (cells : List CellId) → (store : Store Head StableFault NativeFault m) →
    (ref : Ref Head Effect StableFault NativeFault m) → (weight : Nat) → (branch : BranchTrace) →
    StoreAgrees cells world store → Fresh world → RefFine primitive cells world cell ref weight →
    Landed cells world final outcome (demand ref.1 ref.2) store branch
  | _, _, _, _, .cachedValue present, cells, store, _, _, branch, agrees, fresh,
      .intro index located _ _ _ _ _ _ _ _ _ => by
      have cached := (agrees.cached located present).of_value
      exact ⟨cells, ⟨branch, _, store, []⟩, List.prefix_refl _, agrees.of_heap rfl,
        Lands.of_heap (fresh.record _) rfl,
        by rw [demand_cached _ _ store branch _ cached]; exact List.mem_singleton_self _, rfl⟩
  | _, _, _, _, .cachedStable present, cells, store, _, _, branch, agrees, fresh,
      .intro index located _ _ _ _ _ _ _ _ _ => by
      have cached := (agrees.cached located present).of_stableFault
      exact ⟨cells, ⟨branch, _, store, []⟩, List.prefix_refl _, agrees.of_heap rfl,
        Lands.of_heap (fresh.record _) rfl,
        by rw [demand_cached _ _ store branch _ cached]; exact List.mem_singleton_self _, rfl⟩
  | _, _, _, _, .missing absent, _, _, _, _, _, _, _, .intro _ _ _ _ _ _ _ _ _ record _ => by
      rw [absent] at record
      cases record
  | _, _, _, _, .evaluating present, _, _, _, _, _, _, _, .intro _ _ _ _ notEvaluating _ _ _ _ record _ => by
      rw [present] at record
      cases record
      exact absurd rfl (notEvaluating _)
  | cell, world, _, _, .suspended (origin := origin) (position := position) (rule := rule)
      (bodyFinal := bodyFinal) (bodyOutcome := bodyOutcome) present selection bodyDerivation,
      cells, store, _, _, branch, agrees, fresh,
      .intro index located origin' cache notEvaluating refs weights bound bounded record children => by
      rw [present] at record
      cases record
      have pending := (agrees.cached located present).none_of_suspended
      -- the producer's references never reach the cell, so they stay fine once it is entered
      have whole : RefFine primitive cells world cell
          (index, (reading primitive origin.code origin.values refs).2) (producerSize origin.code + bound) :=
        .intro index located origin .suspended notEvaluating refs weights bound bounded present children
      have childrenEnter : ∀ j, RefFine primitive cells (enterWorld world cell origin position rule)
          (origin.needs j) (refs j) (weights j) := by
        intro j
        refine (children j).transport primitive (List.prefix_refl _) ?_
        intro target reach
        rw [enterWorld_lookup]
        have different : target ≠ cell := by
          intro equal
          subst equal
          exact RefFine.acyclic primitive _ whole origin .suspended present j reach
        rw [if_neg different]
      obtain ⟨cells₁, first, isPrefix, agrees₁, landed, selectedMember, answer⟩ :=
        eval_landed bodyDerivation cells store (selectionRefs selection refs) (selectionWeights selection weights)
          (selectionBranch selection branch) (agrees.enter present position rule) (fresh.enter present position rule)
          (selection_fine primitive selection refs weights childrenEnter)
      have member := selection_mem primitive selection refs store branch selectedMember
      -- the producer finishes owning the cell; finalization caches its outcome
      have owned : bodyFinal.heap.lookup cell = some ⟨origin, .evaluating world.nextEvaluator⟩ := by
        refine landed.keeps cell _ world.nextEvaluator ?_ rfl
        rw [enterWorld_lookup, if_pos rfl]
      obtain ⟨outcomeEq, heapEq, lineageEq, pathEq, nextEq⟩ := finalize_of_owned owned rfl bodyOutcome
      have located₁ := prefix_getElem? isPrefix located
      have pending₁ : first.state.getD index none = none :=
        (agrees₁.cached located₁ owned).none_of_evaluating
      have bound₁ : index < first.state.length := by
        rw [← agrees₁.length]
        exact (List.getElem?_eq_some_iff.mp located₁).1
      have finalLookup : ∀ target,
          (finalize bodyFinal cell world.nextEvaluator bodyOutcome).2.heap.lookup target =
            if target = cell then some ⟨origin, cacheOf bodyOutcome⟩ else bodyFinal.heap.lookup target := by
        intro target
        rw [heapEq]
        simp only [World.setKnownCache]
        rw [lookup_setKnownCache]
      have enterLookup : ∀ target, target ≠ cell →
          (enterWorld world cell origin position rule).heap.lookup target = world.heap.lookup target := by
        intro target different
        rw [enterWorld_lookup, if_neg different]
      refine ⟨cells₁,
        WorldResult.prependIntents first.intents
          ⟨first.branch, bodyOutcome, settled index bodyOutcome first.state, []⟩,
        isPrefix, ?_, ?_, ?_, outcomeEq.symm⟩
      · exact (agrees₁.replace located₁ (cacheOf bodyOutcome) (settled_length _ _ _)
          (settled_agrees index bodyOutcome first.state bound₁ pending₁)
          (fun other different => settled_other index other different _ _)).of_heap heapEq
      · refine ⟨?_, ?_, ?_, ?_⟩
        · refine landed.fresh.of_same ?_ lineageEq pathEq nextEq
          intro target found foundPresent
          rw [finalLookup] at foundPresent
          by_cases same : target = cell
          · subst same; exact ⟨_, owned⟩
          · rw [if_neg same] at foundPresent; exact ⟨found, foundPresent⟩
        · exact (Extends.enter present position rule).trans (landed.extends'.trans
            ((Extends.setKnownCache owned (cacheOf bodyOutcome)).trans (Extends.of_heap heapEq)))
        · intro target found owner foundPresent evaluating
          have different : target ≠ cell := by
            intro equal; subst equal; rw [present] at foundPresent; cases foundPresent; cases evaluating
          rw [finalLookup, if_neg different]
          refine landed.keeps target found owner ?_ evaluating
          rw [enterLookup target different]; exact foundPresent
        · intro target found owner foundPresent evaluating
          rw [finalLookup] at foundPresent
          by_cases same : target = cell
          · subst same
            rw [if_pos rfl] at foundPresent
            cases foundPresent
            exact absurd evaluating (cacheOf_ne_evaluating _ _)
          · rw [if_neg same] at foundPresent
            have earlier := landed.noNew target found owner foundPresent evaluating
            rw [enterLookup target same] at earlier
            exact earlier
      · rw [demand_pending _ _ store branch pending]
        refine mem_bind member ?_
        rw [answer, settle_run]
        exact List.mem_singleton_self _

end

/-! ## Exact agreement -/

/-- **Every world of the reading is a natural derivation.**  From a fresh heap
that agrees with the store, under references to cells that are not being
evaluated. -/
theorem eval_complete {n k : Nat} (code : Code Head Operation Effect n k) (values : Sub Head n m)
    (needs : Fin k → CellId) (refs : Fin k → Ref Head Effect StableFault NativeFault m)
    (weights : Fin k → Nat) (cells : List CellId)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    (result : WorldResult (Store Head StableFault NativeFault m) (Outcome Head StableFault NativeFault m) Effect)
    (fine : ∀ j, RefFine primitive cells world (needs j) (refs j) (weights j))
    (agrees : StoreAgrees cells world store) (fresh : Fresh world)
    (member : result ∈ runWorldsAt (reading primitive code values refs).1 store branch) :
    ∃ (final : NeedWorld Head Operation Effect StableFault NativeFault m) (cells' : List CellId),
      Nonempty (Eval primitive ⟨n, k, code, values, needs⟩ world result.answer final) ∧
      cells <+: cells' ∧ StoreAgrees cells' final result.state ∧ Lands world final :=
  have bounded := (exists_bound weights).choose_spec
  (complete (Effect := Effect) primitive (codeSize code + (exists_bound weights).choose)).1 code values needs refs
    weights _ cells world store branch result le_rfl bounded fine agrees fresh member

/-- **The reading and the natural semantics agree exactly.**  From a fresh
heap that agrees with the store, under references to cells that are not being
evaluated, the outcomes of the reading's worlds are the natural outcomes, with
none excluded. -/
theorem agreement {n k : Nat} (code : Code Head Operation Effect n k) (values : Sub Head n m)
    (needs : Fin k → CellId) (refs : Fin k → Ref Head Effect StableFault NativeFault m)
    (weights : Fin k → Nat) (cells : List CellId)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (store : Store Head StableFault NativeFault m) (branch : BranchTrace)
    (fine : ∀ j, RefFine primitive cells world (needs j) (refs j) (weights j))
    (agrees : StoreAgrees cells world store) (fresh : Fresh world)
    (outcome : Outcome Head StableFault NativeFault m) :
    outcome ∈ (runWorldsAt (reading primitive code values refs).1 store branch).map WorldResult.answer ↔
      ∃ final, Nonempty (Eval primitive ⟨n, k, code, values, needs⟩ world outcome final) := by
  constructor
  · intro member
    obtain ⟨result, resultMember, answer⟩ := List.mem_map.mp member
    obtain ⟨final, _, derivation, _⟩ :=
      eval_complete primitive code values needs refs weights cells world store branch result fine agrees fresh
        resultMember
    exact ⟨final, answer ▸ derivation⟩
  · rintro ⟨final, ⟨derivation⟩⟩
    obtain ⟨_, result, _, _, _, member, answer⟩ :=
      eval_landed primitive derivation cells store refs weights branch agrees fresh fine
    exact List.mem_map.mpr ⟨result, member, answer⟩

/-- **Closed code from a fresh heap: the reading's answers are exactly the
natural outcomes.** -/
theorem closed_agreement (code : Code Head Operation Effect 0 0) (values : Sub Head 0 m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) (fresh : Fresh world)
    (outcome : Outcome Head StableFault NativeFault m) :
    outcome ∈ answers (Effect := Effect) primitive code values ↔
      ∃ final, Nonempty (Eval primitive ⟨0, 0, code, values, Fin.elim0⟩ world outcome final) :=
  agreement primitive code values Fin.elim0 Fin.elim0 Fin.elim0 [] world [] [] (fun j => j.elim0)
    ⟨rfl, List.nodup_nil, by simp⟩ fresh outcome

#print axioms complete
#print axioms eval_landed
#print axioms agreement
#print axioms closed_agreement

/-- A force of a cell being evaluated answers a blackhole, whatever the
derivation. -/
theorem force_evaluating {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
    {outcome : Outcome Head StableFault NativeFault m}
    (present : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩)
    (derivation : Force primitive cell world outcome final) :
    outcome = .retryableFault (.blackhole cell) := by
  cases derivation with
  | cachedValue found => rw [present] at found; cases found
  | cachedStable found => rw [present] at found; cases found
  | missing found => rw [present] at found; cases found
  | evaluating _ => rfl
  | suspended found _ _ => rw [present] at found; cases found

/-! ## Examples -/

namespace Examples

open ScopedNeedNaturalSemantics.Examples (ExampleOperation ExampleWorld ExampleClosure emptyWorld cell)

/-- The example primitive: it keeps a term, reports a stable fault, or a
retryable fault of its domain. -/
abbrev examplePrimitive := ScopedNeedNaturalSemantics.Examples.primitive

def headA : Tm Nat 0 := .head 1
def headB : Tm Nat 0 := .head 2

theorem emptyWorld_lookup (target : CellId) : emptyWorld.heap.lookup target = none := rfl

/-! ### Positive: a shared choice -/

/-- A cell holding a choice of two heads, demanded twice and paired. -/
def sharedPair : Code Nat ExampleOperation Nat 0 0 :=
  .letNeed (.choose (.returnValue headA) (.returnValue headB))
    (.sequenceSigma (.force 0) (.force 0))

/-- **The cell is demanded once per world.**  The two demands see the same
choice: two pairs, not four. -/
theorem sharedPair_answers :
    answers (Effect := Nat) examplePrimitive sharedPair ids =
      [.value (.pair headA headA), .value (.pair headB headB)] := by
  decide

/-- And so the natural semantics derives exactly those two outcomes, and no
other outcome at all. -/
theorem sharedPair_derives (outcome : Outcome Nat Nat Nat 0) :
    (outcome = .value (.pair headA headA) ∨ outcome = .value (.pair headB headB)) ↔
      ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, sharedPair, ids, Fin.elim0⟩ emptyWorld outcome final) := by
  rw [← closed_agreement (Effect := Nat) examplePrimitive sharedPair ids emptyWorld
    (Fresh.empty _ emptyWorld_lookup) outcome, sharedPair_answers]
  simp

/-- A mixed pair is no natural outcome: the semantics shares the cell. -/
theorem sharedPair_no_mixed :
    ¬ ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, sharedPair, ids, Fin.elim0⟩ emptyWorld
      (.value (.pair headA headB)) final) := by
  rw [← sharedPair_derives]
  simp [headA, headB]

/-! ### Negative: freshness is necessary, in both directions -/

/-- A world whose next allocation collides with a cell it already holds. -/
def collidingWorld : ExampleWorld :=
  { ScopedNeedNaturalSemantics.Examples.allocatedWorld ⟨0, 0, .returnValue headA, ids, Fin.elim0⟩ with
    nextCell := 0 }

theorem collidingWorld_lookup :
    collidingWorld.heap.lookup cell = some ⟨⟨0, 0, .returnValue headA, ids, Fin.elim0⟩, .suspended⟩ := by
  simp [collidingWorld, ScopedNeedNaturalSemantics.Examples.allocatedWorld, Heap.lookup, cell, World.record,
    emptyWorld]

theorem collidingWorld_not_fresh : ¬ Fresh collidingWorld := by
  intro fresh
  have := (fresh cell _ collidingWorld_lookup rfl).2 rfl
  simp [collidingWorld, cell] at this

/-- Closed code, so the store and its references agree trivially. -/
def allocateThenReturn : Code Nat ExampleOperation Nat 0 0 :=
  .letNeed (.returnValue headA) (.returnValue headA)

theorem allocateThenReturn_answers :
    answers (Effect := Nat) examplePrimitive allocateThenReturn ids = [.value headA] := by
  decide

theorem collidingWorld_allocate (origin : ExampleClosure) :
    collidingWorld.allocate? origin = none := by
  simp [collidingWorld, World.allocate?, Heap.allocate?, Heap.lookup, World.freshCell,
    ScopedNeedNaturalSemantics.Examples.allocatedWorld, cell, World.record, emptyWorld]

/-- **Completeness fails without freshness**: the reading allocates where the
natural semantics collides, so the reading's answer has no derivation. -/
theorem collision_negative :
    ¬ ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, allocateThenReturn, ids, Fin.elim0⟩ collidingWorld
      (.value headA) final) := by
  rintro ⟨final, ⟨derivation⟩⟩
  cases derivation with
  | letNeed allocated _ => rw [collidingWorld_allocate] at allocated; cases allocated

/-- **Soundness fails without freshness**: the natural semantics derives the
collision, which the reading never answers. -/
theorem collision_unanswered :
    ∃ outcome final, Nonempty (Eval examplePrimitive ⟨0, 0, allocateThenReturn, ids, Fin.elim0⟩
      collidingWorld outcome final) ∧ outcome ∉ answers (Effect := Nat) examplePrimitive allocateThenReturn ids :=
  ⟨_, _, ⟨Eval.letNeedAllocationFailure _ (collidingWorld_allocate _)⟩, by
    rw [allocateThenReturn_answers]
    simp [retryResult]⟩

/-! ### Negative: references to cells being evaluated are excluded, in both directions -/

/-- A world in which the cell is being evaluated. -/
def evaluatingWorld : ExampleWorld :=
  { emptyWorld with
    heap := { current := Function.update (fun _ => none) cell
                (some ⟨⟨0, 0, .returnValue headA, ids, Fin.elim0⟩, .evaluating 0⟩),
              spine := [] },
    nextCell := 1, nextEvaluator := 1 }

theorem evaluatingWorld_lookup :
    evaluatingWorld.heap.lookup cell = some ⟨⟨0, 0, .returnValue headA, ids, Fin.elim0⟩, .evaluating 0⟩ := by
  simp [evaluatingWorld, Heap.lookup]

def forceIt : Code Nat ExampleOperation Nat 0 1 := .force 0

/-- The reference of the cell: its producer is the reading of its origin. -/
def forceRef : Ref Nat Nat Nat Nat 0 :=
  (0, (reading (Effect := Nat) examplePrimitive (.returnValue headA) ids Fin.elim0).2)

/-- The reading demands the pending cell and runs its producer. -/
theorem forceIt_reading :
    (runWorldsAt (reading (Effect := Nat) examplePrimitive forceIt ids (fun _ => forceRef)).1 [none] []).map
      WorldResult.answer = [.value headA] := by
  decide

theorem evaluatingWorld_agrees : StoreAgrees [cell] evaluatingWorld ([none] : Store Nat Nat Nat 0) := by
  refine ⟨rfl, List.nodup_singleton _, ?_⟩
  intro index target located
  cases index with
  | zero =>
      simp at located
      subst located
      exact ⟨_, evaluatingWorld_lookup, .evaluating 0⟩
  | succ index => simp at located

theorem evaluatingWorld_fresh : Fresh evaluatingWorld := by
  intro target record present sameLineage
  simp only [evaluatingWorld, Heap.lookup] at present
  by_cases same : target = cell
  · subst same; exact ⟨List.prefix_refl _, fun _ => by simp [cell, evaluatingWorld]⟩
  · rw [Function.update_of_ne same] at present; cases present

/-- Everything but settledness holds: the reference names the cell, whose
producer is the reading of its origin. -/
theorem forceRef_agrees : RefAgrees examplePrimitive [cell] evaluatingWorld cell forceRef :=
  .intro 0 rfl ⟨0, 0, .returnValue headA, ids, Fin.elim0⟩ (.evaluating 0) Fin.elim0 evaluatingWorld_lookup
    (fun j => j.elim0)

theorem forceRef_not_fine (weight : Nat) : ¬ RefFine examplePrimitive [cell] evaluatingWorld cell forceRef weight := by
  intro fine
  obtain ⟨origin, cache, record, notEvaluating⟩ := fine.settledRecord
  rw [evaluatingWorld_lookup] at record
  cases record
  exact notEvaluating 0 rfl

/-- **Completeness fails under a reference to a cell being evaluated**: the
reading runs the producer the natural semantics finds blackholed, so the
reading's answer has no derivation. -/
theorem blackhole_negative :
    ¬ ∃ final, Nonempty (Eval examplePrimitive ⟨0, 1, forceIt, ids, fun _ => cell⟩ evaluatingWorld
      (.value headA) final) := by
  rintro ⟨final, ⟨derivation⟩⟩
  cases derivation with
  | force reference forced =>
      have blackhole := force_evaluating examplePrimitive evaluatingWorld_lookup forced
      cases blackhole

/-- **Soundness fails under a reference to a cell being evaluated**: the
natural semantics derives the blackhole, which the reading never answers. -/
theorem blackhole_unanswered :
    ∃ outcome final, Nonempty (Eval examplePrimitive ⟨0, 1, forceIt, ids, fun _ => cell⟩ evaluatingWorld
      outcome final) ∧
      outcome ∉ (runWorldsAt (reading (Effect := Nat) examplePrimitive forceIt ids (fun _ => forceRef)).1
        [none] []).map WorldResult.answer :=
  ⟨_, _, ⟨Eval.force 0 (Force.evaluating evaluatingWorld_lookup)⟩, by
    rw [forceIt_reading]
    simp⟩

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.ScopedNeed
