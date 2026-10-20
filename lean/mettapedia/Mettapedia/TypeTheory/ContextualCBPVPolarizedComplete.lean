import Mettapedia.TypeTheory.ContextualCBPVPolarizedFresh

/-!
# PolarizedNeed's value layer without need cells: exact agreement

`PolarizedFresh.fresh_sound` shows, from a fresh heap, that every natural
outcome of a closed native returner without need cells is an answer of the
reading at shapes.  This module proves the converse, that every answer of the
reading is the outcome of a natural derivation from every fresh heap
(`needFree_complete`), so that the two agree exactly (`needFree_agreement`),
with first-class thunks, value and native lambdas, packages, sequencing and
choice at every shape.

**The relation.**  `Covers` relates a run-time value to a value of the
reading, and `Reaches` relates what derivations from a world reach to a
computation of the reading run from a store, by shape, in the manner of a
normalization proof: at a returner shape every world of the reading is
reached by a derivation that lands, with a covered answer; at a function
shape every application is (`applyNative`, `applyValue`), so the effects of
a function computation are pushed into its applications as the reading
pushes them (`bindAt`).  The fundamental lemma (`reaches_computation`) covers
every computation without need cells and every selected occurrence of a
cell's producer.

**Twins.**  A choice at a function shape finalizes its cell, which caches the
selected function, before the function is applied; the application then runs
from a heap the alternative's own derivation never reaches.  Derivations of
code without need cells never look at a cell they did not allocate, so they
run alike from two worlds that differ only at such cells (`Twin`,
`eval_twin`).  The finalized cell is that one cell.

**Side conditions.**  Both directions need a fresh heap, and nothing of the
primitives.  From a heap whose next allocation collides, the reading's
answer has no derivation (`Examples.collision_incomplete`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.PolarizedComplete

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open PolarizedValues
open PolarizedFresh
open PolarizedNeedMachine (RuntimeValue)
open PolarizedNeedNaturalSemantics (Eval Force Selection FaultOutcome)

/-! ## Allocation, exactly -/

section Generic

variable {Origin Rule Value StableFault RetryableFault Effect : Type}

theorem allocate?_some {world next : World Origin Rule Value StableFault RetryableFault Effect} {origin : Origin}
    {cell : CellId} (allocated : world.allocate? origin = some (next, cell)) :
    cell = world.freshCell 0 ∧ world.heap.lookup cell = none ∧ next.lineage = world.lineage ∧
      next.path = world.path ∧ next.nextCell = world.nextCell + 1 ∧ next.nextEvaluator = world.nextEvaluator ∧
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
      refine ⟨rfl, absent, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp [World.record, Heap.lookup]
      · intro other different
        simp [World.record, Heap.lookup, different]

theorem allocate?_absent {world : World Origin Rule Value StableFault RetryableFault Effect} {origin : Origin}
    (absent : world.heap.lookup (world.freshCell 0) = none) :
    ∃ next, world.allocate? origin = some (next, world.freshCell 0) := by
  unfold World.allocate?
  dsimp only
  have allocated : world.heap.allocate? (world.freshCell 0) origin =
      some { current := Function.update world.heap.current (world.freshCell 0) (some ⟨origin, .suspended⟩),
             spine := .allocate (world.freshCell 0) origin :: world.heap.spine } := by
    unfold Heap.allocate?
    rw [absent]
  rw [allocated]
  exact ⟨_, rfl⟩

theorem allocate?_present {world : World Origin Rule Value StableFault RetryableFault Effect} {origin : Origin}
    {record : CellRecord Origin Value StableFault} (present : world.heap.lookup (world.freshCell 0) = some record) :
    world.allocate? origin = none := by
  unfold World.allocate?
  dsimp only
  have failed : world.heap.allocate? (world.freshCell 0) origin = none := by
    unfold Heap.allocate?
    rw [present]
  rw [failed]

theorem allocate?_none {world : World Origin Rule Value StableFault RetryableFault Effect} {origin : Origin}
    (failed : world.allocate? origin = none) : ∃ record, world.heap.lookup (world.freshCell 0) = some record := by
  cases found : world.heap.lookup (world.freshCell 0) with
  | none =>
      obtain ⟨next, allocated⟩ := allocate?_absent (origin := origin) found
      rw [allocated] at failed
      cases failed
  | some record => exact ⟨record, rfl⟩

/-! ## Twins -/

/-- Two worlds that agree but for their receipts, their heaps' logs, and the
records of the frozen cells, which both hold. -/
structure Twin (frozen : CellId → Prop) (world world' : World Origin Rule Value StableFault RetryableFault Effect) :
    Prop where
  lineage : world'.lineage = world.lineage
  path : world'.path = world.path
  nextCell : world'.nextCell = world.nextCell
  nextEvaluator : world'.nextEvaluator = world.nextEvaluator
  held : ∀ cell, frozen cell →
    (∃ record, world.heap.lookup cell = some record) ∧ ∃ record, world'.heap.lookup cell = some record
  same : ∀ cell, ¬ frozen cell → world'.heap.lookup cell = world.heap.lookup cell

/-- The frozen cells keep their records from one world to a later one. -/
def Untouched (frozen : CellId → Prop) (world final : World Origin Rule Value StableFault RetryableFault Effect) :
    Prop :=
  ∀ cell, frozen cell → final.heap.lookup cell = world.heap.lookup cell

theorem Untouched.trans {frozen : CellId → Prop}
    {world middle final : World Origin Rule Value StableFault RetryableFault Effect}
    (first : Untouched frozen world middle) (second : Untouched frozen middle final) : Untouched frozen world final :=
  fun cell isFrozen => (second cell isFrozen).trans (first cell isFrozen)

variable {frozen : CellId → Prop}

theorem Twin.record {world world' : World Origin Rule Value StableFault RetryableFault Effect}
    (twin : Twin frozen world world') (payload payload' : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    Twin frozen (world.record payload).1 (world'.record payload').1 :=
  ⟨twin.lineage, twin.path, twin.nextCell, twin.nextEvaluator, twin.held, twin.same⟩

/-- Recording on one side only keeps a twin. -/
theorem Twin.record' {world world' : World Origin Rule Value StableFault RetryableFault Effect}
    (twin : Twin frozen world world') (payload' : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    Twin frozen world (world'.record payload').1 :=
  ⟨twin.lineage, twin.path, twin.nextCell, twin.nextEvaluator, twin.held, twin.same⟩

theorem Twin.freshCell {world world' : World Origin Rule Value StableFault RetryableFault Effect}
    (twin : Twin frozen world world') (generation : Nat) : world'.freshCell generation = world.freshCell generation := by
  simp [World.freshCell, twin.lineage, twin.path, twin.nextCell]

theorem Twin.fresh {world world' : World Origin Rule Value StableFault RetryableFault Effect}
    (twin : Twin frozen world world') (fresh : Fresh world) : Fresh world' := by
  intro cell record found sameLineage
  have present : ∃ record', world.heap.lookup cell = some record' := by
    by_cases isFrozen : frozen cell
    · exact (twin.held cell isFrozen).1
    · rw [← twin.same cell isFrozen]; exact ⟨record, found⟩
  obtain ⟨record', present'⟩ := present
  rw [twin.path, twin.nextCell]
  exact fresh cell record' present' (twin.lineage ▸ sameLineage)

theorem Twin.allocate {world world' next : World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {cell : CellId} (twin : Twin frozen world world')
    (allocated : world.allocate? origin = some (next, cell)) :
    ∃ next', world'.allocate? origin = some (next', cell) ∧ Twin frozen next next' ∧ Untouched frozen world' next' ∧
      ¬ frozen cell := by
  obtain ⟨cellEq, absent, lineage, path, nextCell, nextEvaluator, present, others⟩ := allocate?_some allocated
  have thawed : ¬ frozen cell := by
    intro isFrozen
    obtain ⟨⟨record, found⟩, _⟩ := twin.held cell isFrozen
    rw [absent] at found
    cases found
  have absent' : world'.heap.lookup (world'.freshCell 0) = none := by
    rw [twin.freshCell, ← cellEq, twin.same cell thawed, absent]
  obtain ⟨next', allocated'⟩ := allocate?_absent (origin := origin) absent'
  rw [twin.freshCell, ← cellEq] at allocated'
  obtain ⟨_, _, lineage', path', nextCell', nextEvaluator', present', others'⟩ := allocate?_some allocated'
  refine ⟨next', allocated', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, thawed⟩
  · rw [lineage', lineage, twin.lineage]
  · rw [path', path, twin.path]
  · rw [nextCell', nextCell, twin.nextCell]
  · rw [nextEvaluator', nextEvaluator, twin.nextEvaluator]
  · intro other isFrozen
    have different : other ≠ cell := fun equal => thawed (equal ▸ isFrozen)
    rw [others other different, others' other different]
    exact twin.held other isFrozen
  · intro other thawedOther
    by_cases same : other = cell
    · subst same
      rw [present, present']
    · rw [others other same, others' other same]
      exact twin.same other thawedOther
  · intro other isFrozen
    have different : other ≠ cell := fun equal => thawed (equal ▸ isFrozen)
    exact others' other different

theorem Twin.allocate_none {world world' : World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} (twin : Twin frozen world world') (failed : world.allocate? origin = none) :
    world'.allocate? origin = none := by
  obtain ⟨record, present⟩ := allocate?_none failed
  by_cases isFrozen : frozen (world.freshCell 0)
  · obtain ⟨_, record', present'⟩ := twin.held _ isFrozen
    rw [← twin.freshCell] at present'
    exact allocate?_present present'
  · have present' : world'.heap.lookup (world'.freshCell 0) = some record := by
      rw [twin.freshCell, twin.same _ isFrozen, present]
    exact allocate?_present present'

theorem Twin.setKnownCache {world world' : World Origin Rule Value StableFault RetryableFault Effect}
    (twin : Twin frozen world world') {cell : CellId} (thawed : ¬ frozen cell)
    (record : CellRecord Origin Value StableFault) (cache : Cache Value StableFault) :
    Twin frozen (world.setKnownCache cell record cache) (world'.setKnownCache cell record cache) := by
  refine ⟨twin.lineage, twin.path, twin.nextCell, twin.nextEvaluator, ?_, ?_⟩
  · intro other isFrozen
    have different : other ≠ cell := fun equal => thawed (equal ▸ isFrozen)
    simp only [World.setKnownCache]
    rw [ScopedNeed.lookup_setKnownCache, ScopedNeed.lookup_setKnownCache, if_neg different, if_neg different]
    exact twin.held other isFrozen
  · intro other thawedOther
    simp only [World.setKnownCache]
    rw [ScopedNeed.lookup_setKnownCache, ScopedNeed.lookup_setKnownCache]
    split
    · rfl
    · exact twin.same other thawedOther

theorem untouched_setKnownCache {world : World Origin Rule Value StableFault RetryableFault Effect}
    {cell : CellId} (thawed : ¬ frozen cell) (record : CellRecord Origin Value StableFault)
    (cache : Cache Value StableFault) : Untouched frozen world (world.setKnownCache cell record cache) := by
  intro other isFrozen
  have different : other ≠ cell := fun equal => thawed (equal ▸ isFrozen)
  simp only [World.setKnownCache]
  rw [ScopedNeed.lookup_setKnownCache, if_neg different]

end Generic

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat} {frozen : CellId → Prop}

theorem Twin.enter {world world' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (twin : Twin frozen world world') {cell : CellId} (thawed : ¬ frozen cell)
    (origin : PolarizedNeedMachine.Closure Head Operation Effect m) (position : Nat) (rule : PolarizedNeedMachine.Rule) :
    Twin frozen (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule)
        (PolarizedNeedNaturalSemantics.enterWorld world' cell origin position rule) ∧
      Untouched frozen world' (PolarizedNeedNaturalSemantics.enterWorld world' cell origin position rule) := by
  refine ⟨⟨twin.lineage, ?_, twin.nextCell, ?_, ?_, ?_⟩, ?_⟩
  · show world'.path ++ [position] = world.path ++ [position]
    rw [twin.path]
  · show world'.nextEvaluator + 1 = world.nextEvaluator + 1
    rw [twin.nextEvaluator]
  · intro other isFrozen
    have different : other ≠ cell := fun equal => thawed (equal ▸ isFrozen)
    rw [PolarizedNeedCells.enterWorld_lookup, PolarizedNeedCells.enterWorld_lookup, if_neg different,
      if_neg different]
    exact twin.held other isFrozen
  · intro other thawedOther
    rw [PolarizedNeedCells.enterWorld_lookup, PolarizedNeedCells.enterWorld_lookup, twin.nextEvaluator]
    split
    · rfl
    · exact twin.same other thawedOther
  · intro other isFrozen
    have different : other ≠ cell := fun equal => thawed (equal ▸ isFrozen)
    rw [PolarizedNeedCells.enterWorld_lookup, if_neg different]

theorem finalize_twin {world world' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (twin : Twin frozen world world') {cell : CellId} (thawed : ¬ frozen cell) (owner : EvaluatorId)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    (PolarizedNeedNaturalSemantics.finalize world' cell owner outcome).1 =
        (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).1 ∧
      Twin frozen (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2
        (PolarizedNeedNaturalSemantics.finalize world' cell owner outcome).2 ∧
      Untouched frozen world' (PolarizedNeedNaturalSemantics.finalize world' cell owner outcome).2 := by
  unfold PolarizedNeedNaturalSemantics.finalize
  rw [twin.same cell thawed]
  cases found : world.heap.lookup cell with
  | none => exact ⟨rfl, twin.record _ _, fun _ _ => rfl⟩
  | some record =>
      rcases record with ⟨origin, cache⟩
      cases cache with
      | evaluating actual =>
          by_cases owned : actual = owner
          · subst owned
            simp only [if_true]
            cases outcome with
            | value answer =>
                exact ⟨rfl, (twin.setKnownCache thawed _ _).record _ _, untouched_setKnownCache thawed _ _⟩
            | stableFault fault =>
                exact ⟨rfl, (twin.setKnownCache thawed _ _).record _ _, untouched_setKnownCache thawed _ _⟩
            | retryableFault reason =>
                exact ⟨rfl, (twin.setKnownCache thawed _ _).record _ _, untouched_setKnownCache thawed _ _⟩
          · simp only [if_neg owned]
            exact ⟨rfl, twin.record _ _, fun _ _ => rfl⟩
      | suspended => exact ⟨rfl, twin.record _ _, fun _ _ => rfl⟩
      | value _ => exact ⟨rfl, twin.record _ _, fun _ _ => rfl⟩
      | stableFault _ => exact ⟨rfl, twin.record _ _, fun _ _ => rfl⟩

/-! ## Derivations without need cells run alike from twins -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

mutual
  /-- **Code without need cells runs alike from twin worlds**: from a fresh
  heap, a derivation has a twin from every twin world, with the same outcome,
  ending in a twin world, and leaving the frozen cells as they were. -/
  theorem eval_twin : {closure : PolarizedNeedMachine.Closure Head Operation Effect m} →
      {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
      {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
      Eval primitive closure world outcome final → Fresh world → ClosureNeedFree closure →
      ∀ {world' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m},
        Twin frozen world world' →
          ∃ final', Nonempty (Eval primitive closure world' outcome final') ∧ Twin frozen final final' ∧
            Untouched frozen world' final'
    | _, _, _, _, .returnValue value native values needs _, _, _, world', twin =>
        ⟨world', ⟨.returnValue value native values needs world'⟩, twin, fun _ _ => rfl⟩
    | _, _, _, _, .nativeLambda body native values needs _, _, _, world', twin =>
        ⟨world', ⟨.nativeLambda body native values needs world'⟩, twin, fun _ _ => rfl⟩
    | _, _, _, _, .valueLambda body native values needs _, _, _, world', twin =>
        ⟨world', ⟨.valueLambda body native values needs world'⟩, twin, fun _ _ => rfl⟩
    | _, _, _, _, .call operation argument native values needs _, _, _, world', twin =>
        ⟨world', ⟨.call operation argument native values needs world'⟩, twin, fun _ _ => rfl⟩
    | _, _, _, _, .emit effect nextDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | emit _ nextOk =>
            obtain ⟨final', ⟨derivation'⟩, twin', untouched⟩ :=
              eval_twin nextDerivation (fresh.record _) ⟨nextOk, valuesOk⟩ (twin.record (.effect effect) (.effect effect))
            exact ⟨final', ⟨.emit effect derivation'⟩, twin', untouched⟩
    | _, _, _, _, .forceNeed _ _, _, ⟨codeOk, _⟩, _, _ => by cases codeOk
    | _, _, _, _, .nativeApply argument functionDerivation bodyDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | nativeApply _ functionOk =>
            obtain ⟨landed, ⟨bodyOk, bodyValuesOk⟩⟩ :=
              eval_clean primitive functionDerivation fresh ⟨functionOk, valuesOk⟩
            obtain ⟨selected', ⟨functionDerivation'⟩, twin', untouched⟩ :=
              eval_twin functionDerivation fresh ⟨functionOk, valuesOk⟩ twin
            obtain ⟨final', ⟨bodyDerivation'⟩, twin'', untouched'⟩ :=
              eval_twin bodyDerivation landed.fresh ⟨bodyOk, bodyValuesOk⟩ twin'
            exact ⟨final', ⟨.nativeApply argument functionDerivation' bodyDerivation'⟩, twin'',
              untouched.trans untouched'⟩
    | _, _, _, _, .nativeApplyMismatch argument functionDerivation notFunction, fresh, ⟨codeOk, valuesOk⟩, _,
        twin => by
        cases codeOk with
        | nativeApply _ functionOk =>
            obtain ⟨final', ⟨functionDerivation'⟩, twin', untouched⟩ :=
              eval_twin functionDerivation fresh ⟨functionOk, valuesOk⟩ twin
            exact ⟨final', ⟨.nativeApplyMismatch argument functionDerivation' notFunction⟩, twin', untouched⟩
    | _, _, _, _, .nativeApplyFault argument functionDerivation faulted, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | nativeApply _ functionOk =>
            obtain ⟨final', ⟨functionDerivation'⟩, twin', untouched⟩ :=
              eval_twin functionDerivation fresh ⟨functionOk, valuesOk⟩ twin
            exact ⟨final', ⟨.nativeApplyFault argument functionDerivation' faulted⟩, twin', untouched⟩
    | _, _, _, _, .valueApply argument functionDerivation bodyDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | valueApply functionOk argumentOk =>
            obtain ⟨landed, ⟨bodyOk, bodyValuesOk⟩⟩ :=
              eval_clean primitive functionDerivation fresh ⟨functionOk, valuesOk⟩
            obtain ⟨selected', ⟨functionDerivation'⟩, twin', untouched⟩ :=
              eval_twin functionDerivation fresh ⟨functionOk, valuesOk⟩ twin
            obtain ⟨final', ⟨bodyDerivation'⟩, twin'', untouched'⟩ :=
              eval_twin bodyDerivation landed.fresh
                ⟨bodyOk, cases_needFree (capture_needFree valuesOk argumentOk) bodyValuesOk⟩ twin'
            exact ⟨final', ⟨.valueApply argument functionDerivation' bodyDerivation'⟩, twin'',
              untouched.trans untouched'⟩
    | _, _, _, _, .valueApplyMismatch argument functionDerivation notFunction, fresh, ⟨codeOk, valuesOk⟩, _,
        twin => by
        cases codeOk with
        | valueApply functionOk _ =>
            obtain ⟨final', ⟨functionDerivation'⟩, twin', untouched⟩ :=
              eval_twin functionDerivation fresh ⟨functionOk, valuesOk⟩ twin
            exact ⟨final', ⟨.valueApplyMismatch argument functionDerivation' notFunction⟩, twin', untouched⟩
    | _, _, _, _, .valueApplyFault argument functionDerivation faulted, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | valueApply functionOk _ =>
            obtain ⟨final', ⟨functionDerivation'⟩, twin', untouched⟩ :=
              eval_twin functionDerivation fresh ⟨functionOk, valuesOk⟩ twin
            exact ⟨final', ⟨.valueApplyFault argument functionDerivation' faulted⟩, twin', untouched⟩
    | _, _, _, _, @Eval.forceThunk _ _ _ _ _ _ _ _ _ _ _ _ _ value native _ needs _ _ _ _ _ _ _ captured
        thunkDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | forceThunk valueOk =>
            have thunkOk := capture_needFree (native := native) (needs := needs) valuesOk valueOk
            rw [captured] at thunkOk
            cases thunkOk with
            | thunk codeOk' valuesOk' =>
                obtain ⟨final', ⟨thunkDerivation'⟩, twin', untouched⟩ :=
                  eval_twin thunkDerivation fresh ⟨codeOk', valuesOk'⟩ twin
                exact ⟨final', ⟨.forceThunk value captured thunkDerivation'⟩, twin', untouched⟩
    | _, _, _, _, .forceThunkMismatch value _ notThunk, _, _, world', twin =>
        ⟨world', ⟨.forceThunkMismatch value world' notThunk⟩, twin, fun _ _ => rfl⟩
    | _, _, _, _, @Eval.unpackNative _ _ _ _ _ _ _ _ _ _ value _ native _ needs _ _ _ _ _ captured bodyDerivation,
        fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | unpackNative valueOk bodyOk =>
            have packOk := capture_needFree (native := native) (needs := needs) valuesOk valueOk
            rw [captured] at packOk
            cases packOk with
            | packNative _ payloadOk =>
                obtain ⟨final', ⟨bodyDerivation'⟩, twin', untouched⟩ :=
                  eval_twin bodyDerivation fresh ⟨bodyOk, cases_needFree payloadOk valuesOk⟩ twin
                exact ⟨final', ⟨.unpackNative value captured bodyDerivation'⟩, twin', untouched⟩
    | _, _, _, _, .unpackNativeMismatch value body _ notPack, _, _, world', twin =>
        ⟨world', ⟨.unpackNativeMismatch value body world' notPack⟩, twin, fun _ _ => rfl⟩
    | _, _, _, _, .bindNativeValue allocated forced bodyDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | bindNative firstOk bodyOk =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ :=
              force_clean primitive forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨selected', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            obtain ⟨final', ⟨bodyDerivation'⟩, twin'', untouched'⟩ :=
              eval_twin bodyDerivation landed.fresh ⟨bodyOk, valuesOk⟩ twin'
            exact ⟨final', ⟨.bindNativeValue allocated' forced' bodyDerivation'⟩, twin'',
              (untouchedNext.trans untouched).trans untouched'⟩
    | _, _, _, _, .bindNativeMismatch body allocated forced notNative, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | bindNative firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            exact ⟨final', ⟨.bindNativeMismatch body allocated' forced' notNative⟩, twin',
              untouchedNext.trans untouched⟩
    | _, _, _, _, .bindNativeFault body allocated forced faulted, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | bindNative firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            exact ⟨final', ⟨.bindNativeFault body allocated' forced' faulted⟩, twin', untouchedNext.trans untouched⟩
    | _, _, _, _, .bindNativeAllocationFailure _ failed, fresh, _, _, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .bindValueValue allocated forced bodyDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | bindValue firstOk bodyOk =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, valueOk⟩ :=
              force_clean primitive forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨selected', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            obtain ⟨final', ⟨bodyDerivation'⟩, twin'', untouched'⟩ :=
              eval_twin bodyDerivation landed.fresh ⟨bodyOk, cases_needFree valueOk valuesOk⟩ twin'
            exact ⟨final', ⟨.bindValueValue allocated' forced' bodyDerivation'⟩, twin'',
              (untouchedNext.trans untouched).trans untouched'⟩
    | _, _, _, _, .bindValueMismatch body allocated forced notReturned, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | bindValue firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            exact ⟨final', ⟨.bindValueMismatch body allocated' forced' notReturned⟩, twin',
              untouchedNext.trans untouched⟩
    | _, _, _, _, .bindValueFault body allocated forced faulted, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | bindValue firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            exact ⟨final', ⟨.bindValueFault body allocated' forced' faulted⟩, twin', untouchedNext.trans untouched⟩
    | _, _, _, _, .bindValueAllocationFailure _ failed, fresh, _, _, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .sequenceSigmaValue allocated forced bodyDerivation, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | sequenceSigma firstOk bodyOk =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ :=
              force_clean primitive forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨selected', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            obtain ⟨final', ⟨bodyDerivation'⟩, twin'', untouched'⟩ :=
              eval_twin bodyDerivation landed.fresh ⟨bodyOk, valuesOk⟩ twin'
            exact ⟨final', ⟨.sequenceSigmaValue allocated' forced' bodyDerivation'⟩, twin'',
              (untouchedNext.trans untouched).trans untouched'⟩
    | _, _, _, _, .sequenceSigmaMismatch body allocated forced notNative, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | sequenceSigma firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            exact ⟨final', ⟨.sequenceSigmaMismatch body allocated' forced' notNative⟩, twin',
              untouchedNext.trans untouched⟩
    | _, _, _, _, .sequenceSigmaFault body allocated forced faulted, fresh, ⟨codeOk, valuesOk⟩, _, twin => by
        cases codeOk with
        | sequenceSigma firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
            obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
              force_twin forced freshAllocated _ (allocated_suspended allocated) ⟨firstOk, valuesOk⟩ thawed twinNext
            exact ⟨final', ⟨.sequenceSigmaFault body allocated' forced' faulted⟩, twin',
              untouchedNext.trans untouched⟩
    | _, _, _, _, .sequenceSigmaAllocationFailure _ failed, fresh, _, _, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .choose left right allocated forced, fresh, closureOk, _, twin => by
        have freshAllocated := fresh.allocated allocated
        obtain ⟨next', allocated', twinNext, untouchedNext, thawed⟩ := twin.allocate allocated
        obtain ⟨final', ⟨forced'⟩, twin', untouched⟩ :=
          force_twin forced freshAllocated _ (allocated_suspended allocated) closureOk thawed twinNext
        exact ⟨final', ⟨.choose left right allocated' forced'⟩, twin', untouchedNext.trans untouched⟩
    | _, _, _, _, .chooseAllocationFailure _ _ failed, fresh, _, _, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .letNeed _ _, _, ⟨codeOk, _⟩, _, _ => by cases codeOk
    | _, _, _, _, .letNeedAllocationFailure _ _, _, ⟨codeOk, _⟩, _, _ => by cases codeOk

  /-- A suspended cell whose producer has no need cells is forced alike from
  twin worlds. -/
  theorem force_twin : {cell : CellId} →
      {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
      {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
      Force primitive cell world outcome final → Fresh world →
      (origin : PolarizedNeedMachine.Closure Head Operation Effect m) →
      world.heap.lookup cell = some ⟨origin, .suspended⟩ → ClosureNeedFree origin → ¬ frozen cell →
      ∀ {world' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m},
        Twin frozen world world' →
          ∃ final', Nonempty (Force primitive cell world' outcome final') ∧ Twin frozen final final' ∧
            Untouched frozen world' final'
    | _, _, _, _, .cachedValue found, _, _, present, _, _, _, _ => by rw [present] at found; cases found
    | _, _, _, _, .cachedStable found, _, _, present, _, _, _, _ => by rw [present] at found; cases found
    | _, _, _, _, .missing found, _, _, present, _, _, _, _ => by rw [present] at found; cases found
    | _, _, _, _, .evaluating found, _, _, present, _, _, _, _ => by rw [present] at found; cases found
    | _, world, _, _, @Force.suspended _ _ _ _ _ _ _ _ _ _ position rule _ _ bodyOutcome found selection body, fresh,
        _, present, originOk, thawed, world', twin => by
        rw [present] at found
        cases found
        obtain ⟨twinEnter, untouchedEnter⟩ := twin.enter thawed _ position rule
        obtain ⟨bodyFinal', ⟨body'⟩, twinBody, untouchedBody⟩ :=
          eval_twin body (fresh.enter present position rule) (selection_needFree selection originOk) twinEnter
        have present' := (twin.same _ thawed).trans present
        obtain ⟨outcomeEq, twinFinal, untouchedFinal⟩ := finalize_twin twinBody thawed world.nextEvaluator bodyOutcome
        refine ⟨_, ⟨?_⟩, twinFinal, (untouchedEnter.trans untouchedBody).trans untouchedFinal⟩
        have derivation' := Force.suspended present' selection body'
        rw [twin.nextEvaluator] at derivation'
        rw [← outcomeEq]
        exact derivation'
end

#print axioms eval_twin

/-! ## What derivations reach -/

/-- What derivations from a fixed world reach: an outcome and a final world. -/
abbrev Reach (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
    PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m → Prop

/-- Apply what is reached to a native argument, as `nativeApply` does: the
body of a function answer runs on it, and a fault is the application's
outcome. -/
def applyNative (reach : Reach Head Operation Effect StableFault NativeFault m) (argument : Tm Head m) :
    Reach Head Operation Effect StableFault NativeFault m := fun outcome final =>
  (∃ selected body, reach (.value (.nativeFunction body)) selected ∧
      Nonempty (Eval primitive (body.open argument) selected outcome final)) ∨
    (reach outcome final ∧ Nonempty (FaultOutcome outcome))

/-- Apply what is reached to a run-time value, as `valueApply` does. -/
def applyValue (reach : Reach Head Operation Effect StableFault NativeFault m)
    (argument : RuntimeValue Head Operation Effect m) : Reach Head Operation Effect StableFault NativeFault m :=
  fun outcome final =>
    (∃ selected body, reach (.value (.valueFunction body)) selected ∧
        Nonempty (Eval primitive (body.open argument) selected outcome final)) ∨
      (reach outcome final ∧ Nonempty (FaultOutcome outcome))

theorem applyNative_mono {reach reach' : Reach Head Operation Effect StableFault NativeFault m}
    (included : ∀ outcome final, reach outcome final → reach' outcome final) (argument : Tm Head m) :
    ∀ outcome final, applyNative primitive reach argument outcome final →
      applyNative primitive reach' argument outcome final
  | _, _, .inl ⟨selected, body, reached, derivation⟩ => .inl ⟨selected, body, included _ _ reached, derivation⟩
  | _, _, .inr ⟨reached, faulted⟩ => .inr ⟨included _ _ reached, faulted⟩

theorem applyValue_mono {reach reach' : Reach Head Operation Effect StableFault NativeFault m}
    (included : ∀ outcome final, reach outcome final → reach' outcome final)
    (argument : RuntimeValue Head Operation Effect m) :
    ∀ outcome final, applyValue primitive reach argument outcome final →
      applyValue primitive reach' argument outcome final
  | _, _, .inl ⟨selected, body, reached, derivation⟩ => .inl ⟨selected, body, included _ _ reached, derivation⟩
  | _, _, .inr ⟨reached, faulted⟩ => .inr ⟨included _ _ reached, faulted⟩

/-- A natural outcome agrees with an answer of the reading, given when a
returned value agrees with a value of the reading. -/
def OutcomeAgrees {Semantic : Type} (agrees : RuntimeValue Head Operation Effect m → Semantic → Prop) :
    PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
      Produced Semantic StableFault (ScopedNeedMachine.Fault NativeFault) → Prop
  | .value (.returned value), .value semantic => agrees value semantic
  | .stableFault fault, .stableFault fault' => fault = fault'
  | .retryableFault reason, .retryableFault reason' => reason = PolarizedNeedEmbedding.retry reason'
  | _, _ => False

mutual
  /-- **A run-time value covers a value of the reading**: a native term is
  the term; a thunk is a closure without need cells whose derivations, from
  every fresh heap, reach every world of the thunk's computation; a package
  keeps its index and covers its payload. -/
  def Covers : (shape : VShape) → RuntimeValue Head Operation Effect m →
      SemValue Head Effect StableFault NativeFault m shape → Prop
    | .native, value, semantic => value = .native semantic
    | .thunk shape, value, semantic =>
        ∃ (n v k : Nat) (code : PolarizedNeed.Computation Head Operation Effect n v k) (native : Sub Head n m)
          (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId),
          value = .thunk code native values needs ∧ ClosureNeedFree ⟨n, v, k, code, native, values, needs⟩ ∧
            ∀ world, Fresh world → ∀ store branch,
              Reaches shape world
                (fun outcome final =>
                  Nonempty (Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final))
                semantic store branch
    | .pack payload, value, semantic => ∃ inner, value = .packNative semantic.1 inner ∧ Covers payload inner semantic.2

  /-- **What derivations reach covers a computation of the reading**, run
  from a store.  At a returner shape, every world of the reading is reached
  by a derivation that lands, with a covered answer or the same fault.  At a
  function shape, every application is. -/
  def Reaches : (shape : CShape) → PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m →
      Reach Head Operation Effect StableFault NativeFault m → SemComputation Head Effect StableFault NativeFault m shape →
        ScopedNeed.Store Head StableFault NativeFault m → BranchTrace → Prop
    | .returns answer, world, reach, program, store, branch =>
        ∀ result ∈ runWorldsAt program store branch, ∃ outcome final, reach outcome final ∧ Lands world final ∧
          OutcomeAgrees (Covers answer) outcome result.answer
    | .nativePi shape, world, reach, function, store, branch =>
        ∀ argument, Reaches shape world (applyNative primitive reach argument) (function argument) store branch
    | .arrow domain shape, world, reach, function, store, branch =>
        ∀ argument semantic, Covers domain argument semantic →
          Reaches shape world (applyValue primitive reach argument) (function semantic) store branch
end

theorem covers_needFree : (shape : VShape) → {value : RuntimeValue Head Operation Effect m} →
    {semantic : SemValue Head Effect StableFault NativeFault m shape} →
    Covers primitive shape value semantic → RuntimeNeedFree value
  | .native, _, _, covered => by
      simp only [Covers] at covered
      subst covered
      exact .native _
  | .thunk _, _, _, covered => by
      simp only [Covers] at covered
      obtain ⟨_, _, _, _, _, _, _, rfl, ⟨codeOk, valuesOk⟩, _⟩ := covered
      exact .thunk codeOk valuesOk
  | .pack payload, _, _, covered => by
      simp only [Covers] at covered
      obtain ⟨inner, rfl, innerCovered⟩ := covered
      exact .packNative _ (covers_needFree payload innerCovered)

theorem Reaches.mono : (shape : CShape) →
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {reach reach' : Reach Head Operation Effect StableFault NativeFault m} →
    {semantic : SemComputation Head Effect StableFault NativeFault m shape} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    (∀ outcome final, reach outcome final → reach' outcome final) →
    Reaches primitive shape world reach semantic store branch → Reaches primitive shape world reach' semantic store branch
  | .returns _, _, _, _, _, _, _, included, reaches => fun result member => by
      obtain ⟨outcome, final, reached, landed, agrees⟩ := reaches result member
      exact ⟨outcome, final, included _ _ reached, landed, agrees⟩
  | .nativePi shape, _, _, _, _, _, _, included, reaches => fun argument =>
      Reaches.mono shape (applyNative_mono primitive included argument) (reaches argument)
  | .arrow _ shape, _, _, _, _, _, _, included, reaches => fun argument semantic covered =>
      Reaches.mono shape (applyValue_mono primitive included argument) (reaches argument semantic covered)

/-- **Running a program of the reading first**: if every world of the
program continues, from a landing, into a covered run, the whole is
covered. -/
theorem Reaches.bind : (shape : CShape) → {Other : Type} →
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {reach : Reach Head Operation Effect StableFault NativeFault m} →
    (program : Program (ScopedNeed.Store Head StableFault NativeFault m) Other Effect) →
    (next : Other → SemComputation Head Effect StableFault NativeFault m shape) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    (∀ prior ∈ runWorldsAt program store branch,
      ∃ (middle : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
        (reach' : Reach Head Operation Effect StableFault NativeFault m),
        Lands world middle ∧ (∀ outcome final, reach' outcome final → reach outcome final) ∧
          Reaches primitive shape middle reach' (next prior.answer) prior.state prior.branch) →
    Reaches primitive shape world reach (bindAt shape program next) store branch
  | .returns _, _, _, _, _, _, _, _, step => fun result member => by
      obtain ⟨prior, priorMember, inner, innerMember, rfl⟩ := ScopedNeed.mem_bind_inv member
      obtain ⟨middle, reach', landed, included, reaches⟩ := step prior priorMember
      obtain ⟨outcome, final, reached, landed', agrees⟩ := reaches inner innerMember
      exact ⟨outcome, final, included _ _ reached, landed.trans landed', agrees⟩
  | .nativePi shape, _, _, _, program, next, _, _, step => fun argument =>
      Reaches.bind shape program (fun other => next other argument) fun prior member => by
        obtain ⟨middle, reach', landed, included, reaches⟩ := step prior member
        exact ⟨middle, applyNative primitive reach' argument, landed, applyNative_mono primitive included argument,
          reaches argument⟩
  | .arrow _ shape, _, _, _, program, next, _, _, step => fun argument semantic covered =>
      Reaches.bind shape program (fun other => next other semantic) fun prior member => by
        obtain ⟨middle, reach', landed, included, reaches⟩ := step prior member
        exact ⟨middle, applyValue primitive reach' argument, landed, applyValue_mono primitive included argument,
          reaches argument semantic covered⟩

theorem Reaches.failStable : (shape : CShape) → (fault : StableFault) →
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {reach : Reach Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    Fresh world → reach (.stableFault fault) world →
    Reaches primitive shape world reach (failAt (Head := Head) (Effect := Effect) shape (.stableFault fault)) store branch
  | .returns _, _, world, _, _, _, fresh, reached => fun result member => by
      simp only [failAt, runWorldsAt, List.mem_singleton] at member
      subst member
      exact ⟨_, world, reached, Lands.of_heap fresh rfl, rfl⟩
  | .nativePi shape, fault, _, _, _, _, fresh, reached => fun _ =>
      Reaches.failStable shape fault fresh (.inr ⟨reached, ⟨.stableFault fault⟩⟩)
  | .arrow _ shape, fault, _, _, _, _, fresh, reached => fun _ _ _ =>
      Reaches.failStable shape fault fresh (.inr ⟨reached, ⟨.stableFault fault⟩⟩)

theorem Reaches.failRetry : (shape : CShape) → (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) →
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
    {reach : Reach Head Operation Effect StableFault NativeFault m} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    Fresh world → reach (.retryableFault (PolarizedNeedEmbedding.retry reason)) world →
    Reaches primitive shape world reach
      (failAt (Head := Head) (Effect := Effect) shape (.retryableFault reason)) store branch
  | .returns _, _, world, _, _, _, fresh, reached => fun result member => by
      simp only [failAt, runWorldsAt, List.mem_singleton] at member
      subst member
      exact ⟨_, world, reached, Lands.of_heap fresh rfl, rfl⟩
  | .nativePi shape, reason, _, _, _, _, fresh, reached => fun _ =>
      Reaches.failRetry shape reason fresh (.inr ⟨reached, ⟨.retryableFault _⟩⟩)
  | .arrow _ shape, reason, _, _, _, _, fresh, reached => fun _ _ _ =>
      Reaches.failRetry shape reason fresh (.inr ⟨reached, ⟨.retryableFault _⟩⟩)

/-! ## Forcing a cell: the finalized cell is the only difference -/

/-- A finalization by the owner answers the producer's outcome; it differs
from the producer's final world only at the cell, which it settles. -/
theorem finalize_owned_twin {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : PolarizedNeedMachine.Closure Head Operation Effect m} {owner : EvaluatorId}
    (owned : final.heap.lookup cell = some ⟨origin, .evaluating owner⟩)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    (PolarizedNeedNaturalSemantics.finalize final cell owner outcome).1 = outcome ∧
      Twin (· = cell) final (PolarizedNeedNaturalSemantics.finalize final cell owner outcome).2 ∧
      (PolarizedNeedNaturalSemantics.finalize final cell owner outcome).2.heap.lookup cell =
        some ⟨origin, PolarizedNeedCells.cacheOf outcome⟩ := by
  have settled : (final.setKnownCache cell ⟨origin, .evaluating owner⟩ (PolarizedNeedCells.cacheOf outcome)).heap.lookup
      cell = some ⟨origin, PolarizedNeedCells.cacheOf outcome⟩ := by
    simp only [World.setKnownCache]
    rw [ScopedNeed.lookup_setKnownCache, if_pos rfl]
  have twin : Twin (· = cell) final
      (final.setKnownCache cell ⟨origin, .evaluating owner⟩ (PolarizedNeedCells.cacheOf outcome)) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro other isCell
      subst isCell
      exact ⟨⟨_, owned⟩, _, settled⟩
    · intro other different
      simp only [World.setKnownCache]
      rw [ScopedNeed.lookup_setKnownCache, if_neg different]
  unfold PolarizedNeedNaturalSemantics.finalize
  rw [owned]
  simp only [if_true]
  cases outcome with
  | value answer => exact ⟨rfl, twin.record' _, settled⟩
  | stableFault fault => exact ⟨rfl, twin.record' _, settled⟩
  | retryableFault reason => exact ⟨rfl, twin.record' _, settled⟩

/-- Finalizing a cell entered from a world and running on: where the settled
cell is the only difference, the run lands from the world. -/
theorem lands_settled {world final final' : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : PolarizedNeedMachine.Closure Head Operation Effect m} {position : Nat}
    {rule : PolarizedNeedMachine.Rule} (present : world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (landed : Lands (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) final)
    (twin : Twin (· = cell) final final')
    (settled : ∃ cache, final'.heap.lookup cell = some ⟨origin, cache⟩ ∧ ∀ owner, cache ≠ .evaluating owner) :
    Lands world final' := by
  obtain ⟨cache, settledLookup, notEvaluating⟩ := settled
  have enterLookup : ∀ target, target ≠ cell →
      (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).heap.lookup target =
        world.heap.lookup target := by
    intro target different
    rw [PolarizedNeedCells.enterWorld_lookup, if_neg different]
  refine ⟨twin.fresh landed.fresh, ?_, ?_, ?_⟩
  · intro target origin' cache' found
    by_cases same : target = cell
    · rw [same, present] at found
      cases found
      rw [same]
      exact ⟨cache, settledLookup⟩
    · rw [twin.same target same]
      exact landed.extends' target origin' cache' (by rw [enterLookup target same]; exact found)
  · intro target record owner found evaluating
    have different : target ≠ cell := by
      intro equal
      rw [equal, present] at found
      cases found
      cases evaluating
    rw [twin.same target different]
    exact landed.keeps target record owner (by rw [enterLookup target different]; exact found) evaluating
  · intro target record owner found evaluating
    by_cases same : target = cell
    · rw [same, settledLookup] at found
      cases found
      exact absurd evaluating (notEvaluating owner)
    · rw [twin.same target same] at found
      have earlier := landed.noNew target record owner found evaluating
      rw [enterLookup target same] at earlier
      exact earlier

/-- **Settling a forced cell keeps what is reached covered**: what a
cell's selected producer reaches from the entered world, settled and run on
from twin worlds, covers the same computation from the world. -/
theorem Reaches.settle {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : PolarizedNeedMachine.Closure Head Operation Effect m} {position : Nat}
    {rule : PolarizedNeedMachine.Rule} (present : world.heap.lookup cell = some ⟨origin, .suspended⟩) :
    (shape : CShape) → {reach reach' : Reach Head Operation Effect StableFault NativeFault m} →
    {semantic : SemComputation Head Effect StableFault NativeFault m shape} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    (∀ outcome final, reach outcome final →
      OutcomeNeedFree outcome ∧ Lands (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) final) →
    (∀ outcome final, reach outcome final → ∃ final', reach' outcome final' ∧ Twin (· = cell) final final' ∧
      ∃ cache, final'.heap.lookup cell = some ⟨origin, cache⟩ ∧ ∀ owner, cache ≠ .evaluating owner) →
    Reaches primitive shape (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) reach semantic
      store branch →
    Reaches primitive shape world reach' semantic store branch
  | .returns _, _, _, _, _, _, clean, transport, reaches => fun result member => by
      obtain ⟨outcome, final, reached, landed, agrees⟩ := reaches result member
      obtain ⟨final', reached', twin, settled⟩ := transport outcome final reached
      exact ⟨outcome, final', reached', lands_settled present landed twin settled, agrees⟩
  | .nativePi shape, reach, reach', _, _, _, clean, transport, reaches => fun argument => by
      refine Reaches.settle present shape ?_ ?_ (reaches argument)
      · rintro outcome final (⟨selected, body, reached, ⟨derivation⟩⟩ | ⟨reached, _⟩)
        · obtain ⟨⟨bodyOk, bodyValuesOk⟩, landed⟩ := clean _ _ reached
          obtain ⟨landed', outcomeOk⟩ := eval_clean primitive derivation landed.fresh ⟨bodyOk, bodyValuesOk⟩
          exact ⟨outcomeOk, landed.trans landed'⟩
        · exact clean _ _ reached
      · rintro outcome final (⟨selected, body, reached, ⟨derivation⟩⟩ | ⟨reached, faulted⟩)
        · obtain ⟨⟨bodyOk, bodyValuesOk⟩, landed⟩ := clean _ _ reached
          obtain ⟨selected', reached', twin, cache, settledLookup, notEvaluating⟩ := transport _ _ reached
          obtain ⟨final', ⟨derivation'⟩, twin', untouched⟩ :=
            eval_twin primitive derivation landed.fresh ⟨bodyOk, bodyValuesOk⟩ twin
          exact ⟨final', .inl ⟨selected', body, reached', ⟨derivation'⟩⟩, twin', cache,
            (untouched cell rfl).trans settledLookup, notEvaluating⟩
        · obtain ⟨final', reached', twin, settled⟩ := transport _ _ reached
          exact ⟨final', .inr ⟨reached', faulted⟩, twin, settled⟩
  | .arrow domain shape, reach, reach', _, _, _, clean, transport, reaches => fun argument semantic covered => by
      have argumentOk := covers_needFree primitive domain covered
      refine Reaches.settle present shape ?_ ?_ (reaches argument semantic covered)
      · rintro outcome final (⟨selected, body, reached, ⟨derivation⟩⟩ | ⟨reached, _⟩)
        · obtain ⟨⟨bodyOk, bodyValuesOk⟩, landed⟩ := clean _ _ reached
          obtain ⟨landed', outcomeOk⟩ :=
            eval_clean primitive derivation landed.fresh ⟨bodyOk, cases_needFree argumentOk bodyValuesOk⟩
          exact ⟨outcomeOk, landed.trans landed'⟩
        · exact clean _ _ reached
      · rintro outcome final (⟨selected, body, reached, ⟨derivation⟩⟩ | ⟨reached, faulted⟩)
        · obtain ⟨⟨bodyOk, bodyValuesOk⟩, landed⟩ := clean _ _ reached
          obtain ⟨selected', reached', twin, cache, settledLookup, notEvaluating⟩ := transport _ _ reached
          obtain ⟨final', ⟨derivation'⟩, twin', untouched⟩ :=
            eval_twin primitive derivation landed.fresh ⟨bodyOk, cases_needFree argumentOk bodyValuesOk⟩ twin
          exact ⟨final', .inl ⟨selected', body, reached', ⟨derivation'⟩⟩, twin', cache,
            (untouched cell rfl).trans settledLookup, notEvaluating⟩
        · obtain ⟨final', reached', twin, settled⟩ := transport _ _ reached
          exact ⟨final', .inr ⟨reached', faulted⟩, twin, settled⟩

/-- **A forced cell reaches what its selected producer reaches.** -/
theorem reaches_force {shape : CShape}
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin selected : PolarizedNeedMachine.Closure Head Operation Effect m} {position : Nat}
    {rule : PolarizedNeedMachine.Rule} (present : world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (fresh : Fresh world) (selection : Selection origin position rule selected) (selectedOk : ClosureNeedFree selected)
    {semantic : SemComputation Head Effect StableFault NativeFault m shape}
    {store : ScopedNeed.Store Head StableFault NativeFault m} {branch : BranchTrace}
    (reaches : Reaches primitive shape (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule)
      (fun outcome final => Nonempty
        (Eval primitive selected (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) outcome final))
      semantic store branch) :
    Reaches primitive shape world (fun outcome final => Nonempty (Force primitive cell world outcome final)) semantic
      store branch := by
  have freshEntered := fresh.enter present position rule
  refine Reaches.settle primitive present shape ?_ ?_ reaches
  · rintro outcome final ⟨derivation⟩
    obtain ⟨landed, outcomeOk⟩ := eval_clean primitive derivation freshEntered selectedOk
    exact ⟨outcomeOk, landed⟩
  · rintro outcome final ⟨derivation⟩
    obtain ⟨landed, _⟩ := eval_clean primitive derivation freshEntered selectedOk
    have owned : final.heap.lookup cell = some ⟨origin, .evaluating world.nextEvaluator⟩ := by
      refine landed.keeps cell _ world.nextEvaluator ?_ rfl
      rw [PolarizedNeedCells.enterWorld_lookup, if_pos rfl]
    obtain ⟨outcomeEq, twin, settledLookup⟩ := finalize_owned_twin owned outcome
    refine ⟨_, ⟨?_⟩, twin, _, settledLookup, fun owner => cacheOf_ne_evaluating outcome owner⟩
    have forced := Force.suspended present selection derivation
    rw [outcomeEq] at forced
    exact forced

/-! ## The fundamental lemma -/

theorem OutcomeAgrees.cases {Semantic : Type} {agrees : RuntimeValue Head Operation Effect m → Semantic → Prop}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {answer : Produced Semantic StableFault (ScopedNeedMachine.Fault NativeFault)}
    (agreed : OutcomeAgrees agrees outcome answer) :
    (∃ value semantic, outcome = .value (.returned value) ∧ answer = .value semantic ∧ agrees value semantic) ∨
      (∃ fault, outcome = .stableFault fault ∧ answer = .stableFault fault) ∨
      (∃ reason, outcome = .retryableFault (PolarizedNeedEmbedding.retry reason) ∧ answer = .retryableFault reason) := by
  cases outcome with
  | value result =>
      cases result with
      | returned value =>
          cases answer with
          | value semantic => exact .inl ⟨value, semantic, rfl, rfl, agreed⟩
          | stableFault _ => exact agreed.elim
          | retryableFault _ => exact agreed.elim
      | nativeFunction _ => cases answer <;> exact agreed.elim
      | valueFunction _ => cases answer <;> exact agreed.elim
  | stableFault fault =>
      cases answer with
      | value _ => exact agreed.elim
      | stableFault fault' =>
          have equal : fault = fault' := agreed
          subst equal
          exact .inr (.inl ⟨fault, rfl, rfl⟩)
      | retryableFault _ => exact agreed.elim
  | retryableFault reason =>
      cases answer with
      | value _ => exact agreed.elim
      | stableFault _ => exact agreed.elim
      | retryableFault reason' =>
          have equal : reason = PolarizedNeedEmbedding.retry reason' := agreed
          subst equal
          exact .inr (.inr ⟨reason', rfl, rfl⟩)

theorem covers_native {value : RuntimeValue Head Operation Effect m} {term : Tm Head m}
    (covered : Covers (StableFault := StableFault) (NativeFault := NativeFault) primitive .native value term) :
    value = .native term := covered

theorem pair_agrees {first : Tm Head m}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {answer : ScopedNeedMachine.Outcome Head StableFault NativeFault m}
    (agreed : OutcomeAgrees (Covers primitive .native) outcome answer) :
    OutcomeAgrees (Covers primitive .native) (PolarizedNeedNaturalSemantics.pairOutcome first outcome)
      (ScopedNeedNaturalSemantics.pairOutcome first answer) := by
  rcases agreed.cases with ⟨value, term, rfl, rfl, covered⟩ | ⟨fault, rfl, rfl⟩ | ⟨reason, rfl, rfl⟩
  · rw [covers_native primitive covered]
    rfl
  · rfl
  · rfl

/-- Pairing every answer with a native term keeps it covered. -/
theorem Reaches.pair {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {reach reach' : Reach Head Operation Effect StableFault NativeFault m}
    {program : ScopedNeed.Run Head Effect StableFault NativeFault m}
    {store : ScopedNeed.Store Head StableFault NativeFault m} {branch : BranchTrace} (first : Tm Head m)
    (included : ∀ outcome final, reach outcome final →
      reach' (PolarizedNeedNaturalSemantics.pairOutcome first outcome) final)
    (reaches : Reaches primitive (.returns .native) world reach program store branch) :
    Reaches primitive (.returns .native) world reach'
      (Program.map (ScopedNeedNaturalSemantics.pairOutcome first) program) store branch := by
  intro result member
  obtain ⟨inner, innerMember, second, secondMember, rfl⟩ := ScopedNeed.mem_bind_inv member
  simp only [runWorldsAt, List.mem_singleton] at secondMember
  subst secondMember
  obtain ⟨outcome, final, reached, landed, agrees⟩ := reaches inner innerMember
  exact ⟨_, final, included _ _ reached, landed, pair_agrees primitive agrees⟩

/-- A cell demanded at once from a store where it is pending answers what its
producer answers. -/
theorem cellAt_inv (shape : VShape)
    (producer : SemComputation Head Effect StableFault NativeFault m (.returns shape))
    (store : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace)
    {result : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (Produced (SemValue Head Effect StableFault NativeFault m shape) StableFault
        (ScopedNeedMachine.Fault NativeFault)) Effect}
    (member : result ∈ runWorldsAt (cellAt shape store.length producer) (store ++ [none]) branch) :
    ∃ inner ∈ runWorldsAt producer (store ++ [none]) branch, inner.answer = result.answer := by
  cases shape with
  | native =>
      have pending : (store ++ [none]).getD store.length none = none := by simp
      have pendingRun := ScopedNeed.demand_pending (Effect := Effect) store.length
        (producer : ScopedNeed.Run Head Effect StableFault NativeFault m) (store ++ [none]) branch pending
      change result ∈ runWorldsAt (ScopedNeed.demand store.length
        (producer : ScopedNeed.Run Head Effect StableFault NativeFault m)) (store ++ [none]) branch at member
      rw [pendingRun] at member
      obtain ⟨first, firstMember, second, secondMember, rfl⟩ := ScopedNeed.mem_bind_inv member
      rw [ScopedNeed.settle_run] at secondMember
      rw [List.mem_singleton] at secondMember
      subst secondMember
      exact ⟨first, firstMember, rfl⟩
  | thunk _ => exact ⟨result, member, rfl⟩
  | pack _ => exact ⟨result, member, rfl⟩

/-- The run-time values of the value variables cover the reading's. -/
def CoversEnv {scope : List VShape} (values : Fin scope.length → RuntimeValue Head Operation Effect m)
    (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope) : Prop :=
  ∀ shape (index : Member scope shape), Covers primitive shape (values index.index) (env shape index)

theorem CoversEnv.cons {scope : List VShape} {shape : VShape}
    {values : Fin scope.length → RuntimeValue Head Operation Effect m}
    {env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope} (covers : CoversEnv primitive values env)
    {value : RuntimeValue Head Operation Effect m} {semantic : SemValue Head Effect StableFault NativeFault m shape}
    (covered : Covers primitive shape value semantic) :
    CoversEnv primitive (scope := shape :: scope)
      (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) (SemEnv.cons semantic env)
  | _, .zero => covered
  | _, .succ index => covers _ index

/-- The fundamental property of a reading: from every fresh heap, what the
derivations of its closure reach covers the computation, and what forcing a
cell with that producer reaches covers what the cell runs. -/
def Fundamental (shape : CShape) (closure : PolarizedNeedMachine.Closure Head Operation Effect m)
    (reading : SemComputation Head Effect StableFault NativeFault m shape ×
      SemComputation Head Effect StableFault NativeFault m shape) : Prop :=
  (∀ world, Fresh world → ∀ store branch,
    Reaches primitive shape world (fun outcome final => Nonempty (Eval primitive closure world outcome final))
      reading.1 store branch) ∧
  (∀ world cell, Fresh world → world.heap.lookup cell = some ⟨closure, .suspended⟩ → ∀ store branch,
    Reaches primitive shape world (fun outcome final => Nonempty (Force primitive cell world outcome final))
      reading.2 store branch)

/-- Code other than a choice: its cell runs it as it stands. -/
theorem Fundamental.of_entry {shape : CShape} {closure : PolarizedNeedMachine.Closure Head Operation Effect m}
    {reading : SemComputation Head Effect StableFault NativeFault m shape ×
      SemComputation Head Effect StableFault NativeFault m shape}
    (notChoice : ∀ left right, closure.code ≠ .choose left right) (closureOk : ClosureNeedFree closure)
    (same : reading.2 = reading.1)
    (first : ∀ world, Fresh world → ∀ store branch,
      Reaches primitive shape world (fun outcome final => Nonempty (Eval primitive closure world outcome final))
        reading.1 store branch) :
    Fundamental primitive shape closure reading := by
  refine ⟨first, fun world cell fresh present store branch => ?_⟩
  rw [same]
  obtain ⟨n, v, k, code, native, values, needs⟩ := closure
  exact reaches_force primitive present fresh (.entry notChoice) closureOk
    (first _ (fresh.enter present 0 .entry) store branch)

mutual
  /-- **The fundamental lemma for values**: a value without need cells is
  covered by its run-time value. -/
  theorem covers_value : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      {value : Shaped.Value Head Operation Effect n scope k shape} → value.NeedFree →
      (native : Sub Head n m) → (values : Fin scope.length → RuntimeValue Head Operation Effect m) →
      (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) →
      CoversEnv primitive values env → (∀ index, RuntimeNeedFree (values index)) →
      Covers primitive shape (PolarizedNeedMachine.captureValue native values needs value.erase)
        (readValue primitive value native env refs)
    | _, _, _, _, _, .native _, _, _, _, _, _, _, _ => rfl
    | _, _, _, _, _, .var index, _, _, _, _, _, covers, _ => covers _ index
    | _, _, _, _, _, .thunk bodyFree, native, values, needs, env, refs, covers, valuesOk =>
        ⟨_, _, _, _, native, values, needs, rfl, ⟨rawNeedFree_erase bodyFree, valuesOk⟩,
          (reaches_computation bodyFree native values needs env refs covers valuesOk).1⟩
    | _, _, _, _, _, .pack _ payloadFree, native, values, needs, env, refs, covers, valuesOk =>
        ⟨_, rfl, covers_value payloadFree native values needs env refs covers valuesOk⟩

  /-- **The fundamental lemma for computations**: from every fresh heap, what
  the derivations of a computation without need cells reach covers its
  reading, and so does what forcing a cell with it as producer reaches. -/
  theorem reaches_computation : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      {computation : Shaped.Computation Head Operation Effect n scope k shape} → computation.NeedFree →
      (native : Sub Head n m) → (values : Fin scope.length → RuntimeValue Head Operation Effect m) →
      (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) →
      CoversEnv primitive values env → (∀ index, RuntimeNeedFree (values index)) →
      Fundamental primitive shape ⟨n, scope.length, k, computation.erase, native, values, needs⟩
        (readComputation primitive computation native env refs)
    | _, _, _, _, _, .returnValue valueFree, native, values, needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.returnValue valueFree), valuesOk⟩ rfl fun world fresh store branch result member => by
            simp only [readComputation, runWorldsAt, List.mem_singleton] at member
            subst member
            exact ⟨_, world, ⟨.returnValue _ native values needs world⟩, Lands.of_heap fresh rfl,
              covers_value valueFree native values needs env refs covers valuesOk⟩
    | _, _, _, _, _, .call operation argument, native, values, needs, _, _, _, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.call operation argument), valuesOk⟩ rfl fun world fresh store branch result member => by
            simp only [readComputation, runWorldsAt, List.mem_singleton] at member
            subst member
            refine ⟨_, world, ⟨.call operation argument native values needs world⟩, Lands.of_heap fresh rfl, ?_⟩
            generalize primitive operation (subst native argument) = produced
            cases produced with
            | value term => rfl
            | stableFault fault => rfl
            | retryableFault reason => cases reason <;> rfl
    | _, _, _, shape, _, .emit effect nextFree, native, values, needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.emit effect nextFree), valuesOk⟩ rfl fun world fresh store branch => by
            refine Reaches.bind primitive shape _ _ fun prior member => ?_
            simp only [runWorldsAt, List.map_cons, List.map_nil, List.mem_singleton] at member
            subst member
            refine ⟨_, _, Lands.of_heap (world := world) (fresh.record (.effect effect)) rfl, ?_,
              (reaches_computation nextFree native values needs env refs covers valuesOk).1 _
                (fresh.record (.effect effect)) _ _⟩
            rintro outcome final ⟨derivation⟩
            exact ⟨.emit effect derivation⟩
    | _, _, _, _, _, .nativeLambda bodyFree, native, values, needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.nativeLambda bodyFree), valuesOk⟩ rfl fun world fresh store branch argument =>
            Reaches.mono primitive _
              (fun _ _ reached => .inl ⟨world, _, ⟨.nativeLambda _ native values needs world⟩, reached⟩)
              ((reaches_computation bodyFree (Fin.cases (motive := fun _ => Tm Head m) argument native) values needs env refs
                covers valuesOk).1
                world fresh store branch)
    | _, _, _, _, _, .valueLambda (domain := domain) bodyFree, native, values, needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.valueLambda bodyFree), valuesOk⟩ rfl
          fun world fresh store branch argument semantic covered =>
            Reaches.mono primitive _
              (fun _ _ reached => .inl ⟨world, _, ⟨.valueLambda _ native values needs world⟩, reached⟩)
              ((reaches_computation bodyFree native
                (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) argument values) needs
                (SemEnv.cons semantic env) refs (covers.cons primitive covered)
                (cases_needFree (covers_needFree primitive domain covered) valuesOk)).1 world fresh store branch)
    | _, _, _, _, _, .nativeApply argument functionFree, native, values, needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.nativeApply argument functionFree), valuesOk⟩ rfl fun world fresh store branch =>
            Reaches.mono primitive _
              (fun _ _ reached => by
                rcases reached with ⟨_, _, ⟨functionDerivation⟩, ⟨bodyDerivation⟩⟩ | ⟨⟨derivation⟩, ⟨faulted⟩⟩
                · exact ⟨.nativeApply argument functionDerivation bodyDerivation⟩
                · exact ⟨.nativeApplyFault argument derivation faulted⟩)
              ((reaches_computation functionFree native values needs env refs covers valuesOk).1 world fresh store branch
                (subst native argument))
    | _, _, _, _, _, .valueApply (argument := argument) functionFree argumentFree, native, values, needs, env, refs,
        covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.valueApply functionFree argumentFree), valuesOk⟩ rfl fun world fresh store branch =>
            Reaches.mono primitive _
              (fun _ _ reached => by
                rcases reached with ⟨_, _, ⟨functionDerivation⟩, ⟨bodyDerivation⟩⟩ | ⟨⟨derivation⟩, ⟨faulted⟩⟩
                · exact ⟨.valueApply argument.erase functionDerivation bodyDerivation⟩
                · exact ⟨.valueApplyFault argument.erase derivation faulted⟩)
              ((reaches_computation functionFree native values needs env refs covers valuesOk).1 world fresh store branch
                (PolarizedNeedMachine.captureValue native values needs argument.erase)
                (readValue primitive argument native env refs)
                (covers_value argumentFree native values needs env refs covers valuesOk))
    | _, _, _, _, _, .forceThunk (value := value) valueFree, native, values, needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.forceThunk valueFree), valuesOk⟩ rfl fun world fresh store branch => by
            obtain ⟨_, _, _, _, _, _, _, captured, _, reaches⟩ :=
              covers_value valueFree native values needs env refs covers valuesOk
            exact Reaches.mono primitive _ (fun _ _ ⟨derivation⟩ => ⟨.forceThunk value.erase captured derivation⟩)
              (reaches world fresh store branch)
    | _, _, _, _, _, .unpackNative (payload := payload) (value := value) valueFree bodyFree, native, values, needs,
        env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.unpackNative valueFree bodyFree), valuesOk⟩ rfl fun world fresh store branch => by
            obtain ⟨inner, captured, innerCovered⟩ := covers_value valueFree native values needs env refs covers valuesOk
            exact Reaches.mono primitive _ (fun _ _ ⟨derivation⟩ => ⟨.unpackNative value.erase captured derivation⟩)
              ((reaches_computation bodyFree
                (Fin.cases (motive := fun _ => Tm Head m) (readValue primitive value native env refs).1 native)
                (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) inner values) needs
                (SemEnv.cons (readValue primitive value native env refs).2 env) refs (covers.cons primitive innerCovered)
                (cases_needFree (covers_needFree primitive payload innerCovered) valuesOk)).1 world fresh store branch)
    | _, _, scope, shape, _, .bindNative (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.bindNative firstFree bodyFree), valuesOk⟩ rfl fun world fresh store branch => by
            obtain ⟨next, allocated, freshNext⟩ := fresh.allocate ⟨_, scope.length, _, first.erase, native, values, needs⟩
            have producer := (reaches_computation firstFree native values needs env refs covers valuesOk).2 next _
              freshNext (allocated_suspended allocated)
            refine Reaches.bind primitive shape _ _ fun prior member => ?_
            simp only [runWorldsAt, List.mem_singleton] at member
            subst member
            refine ⟨next, _, Lands.alloc allocated freshNext, fun _ _ reached => reached, ?_⟩
            refine Reaches.bind primitive shape _ _ fun prior' member' => ?_
            obtain ⟨inner, innerMember, answerEq⟩ := cellAt_inv .native _ store branch member'
            obtain ⟨outcome, middle, ⟨forced⟩, landed, agrees⟩ := producer (store ++ [none]) branch inner innerMember
            rw [← answerEq]
            refine ⟨middle, _, landed, fun _ _ reached => reached, ?_⟩
            generalize inner.answer = answer at agrees ⊢
            rcases agrees.cases with ⟨value, term, rfl, rfl, covered⟩ | ⟨fault, rfl, rfl⟩ | ⟨reason, rfl, rfl⟩
            · rw [covers_native primitive covered] at forced
              exact Reaches.mono primitive _ (fun _ _ ⟨derivation⟩ => ⟨.bindNativeValue allocated forced derivation⟩)
                ((reaches_computation bodyFree (Fin.cases (motive := fun _ => Tm Head m) term native) values needs env refs
                  covers valuesOk).1
                  middle landed.fresh _ _)
            · exact Reaches.failStable primitive shape fault landed.fresh
                ⟨.bindNativeFault body.erase allocated forced (.stableFault fault)⟩
            · exact Reaches.failRetry primitive shape reason landed.fresh
                ⟨.bindNativeFault body.erase allocated forced (.retryableFault _)⟩
    | _, _, scope, shape, _, .bindValue (bound := bound) (first := first) (body := body) firstFree bodyFree, native, values,
        needs, env, refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.bindValue firstFree bodyFree), valuesOk⟩ rfl fun world fresh store branch => by
            obtain ⟨next, allocated, freshNext⟩ := fresh.allocate ⟨_, scope.length, _, first.erase, native, values, needs⟩
            have producer := (reaches_computation firstFree native values needs env refs covers valuesOk).2 next _
              freshNext (allocated_suspended allocated)
            refine Reaches.bind primitive shape _ _ fun prior member => ?_
            simp only [runWorldsAt, List.mem_singleton] at member
            subst member
            refine ⟨next, _, Lands.alloc allocated freshNext, fun _ _ reached => reached, ?_⟩
            refine Reaches.bind primitive shape _ _ fun prior' member' => ?_
            obtain ⟨inner, innerMember, answerEq⟩ := cellAt_inv bound _ store branch member'
            obtain ⟨outcome, middle, ⟨forced⟩, landed, agrees⟩ := producer (store ++ [none]) branch inner innerMember
            rw [← answerEq]
            refine ⟨middle, _, landed, fun _ _ reached => reached, ?_⟩
            generalize inner.answer = answer at agrees ⊢
            rcases agrees.cases with ⟨value, semantic, rfl, rfl, covered⟩ | ⟨fault, rfl, rfl⟩ | ⟨reason, rfl, rfl⟩
            · exact Reaches.mono primitive _ (fun _ _ ⟨derivation⟩ => ⟨.bindValueValue allocated forced derivation⟩)
                ((reaches_computation bodyFree native
                  (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) needs
                  (SemEnv.cons semantic env) refs (covers.cons primitive covered)
                  (cases_needFree (covers_needFree primitive bound covered) valuesOk)).1 middle landed.fresh _ _)
            · exact Reaches.failStable primitive shape fault landed.fresh
                ⟨.bindValueFault body.erase allocated forced (.stableFault fault)⟩
            · exact Reaches.failRetry primitive shape reason landed.fresh
                ⟨.bindValueFault body.erase allocated forced (.retryableFault _)⟩
    | _, _, scope, _, _, .sequenceSigma (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, covers, valuesOk =>
        Fundamental.of_entry primitive (fun _ _ equal => by cases equal)
          ⟨rawNeedFree_erase (.sequenceSigma firstFree bodyFree), valuesOk⟩ rfl fun world fresh store branch => by
            obtain ⟨next, allocated, freshNext⟩ := fresh.allocate ⟨_, scope.length, _, first.erase, native, values, needs⟩
            have producer := (reaches_computation firstFree native values needs env refs covers valuesOk).2 next _
              freshNext (allocated_suspended allocated)
            refine Reaches.bind primitive (.returns .native) _ _ fun prior member => ?_
            simp only [runWorldsAt, List.mem_singleton] at member
            subst member
            refine ⟨next, _, Lands.alloc allocated freshNext, fun _ _ reached => reached, ?_⟩
            refine Reaches.bind primitive (.returns .native) _ _ fun prior' member' => ?_
            obtain ⟨inner, innerMember, answerEq⟩ := cellAt_inv .native _ store branch member'
            obtain ⟨outcome, middle, ⟨forced⟩, landed, agrees⟩ := producer (store ++ [none]) branch inner innerMember
            rw [← answerEq]
            refine ⟨middle, _, landed, fun _ _ reached => reached, ?_⟩
            generalize inner.answer = answer at agrees ⊢
            rcases agrees.cases with ⟨value, term, rfl, rfl, covered⟩ | ⟨fault, rfl, rfl⟩ | ⟨reason, rfl, rfl⟩
            · rw [covers_native primitive covered] at forced
              exact Reaches.pair primitive term
                (fun _ _ ⟨derivation⟩ => ⟨.sequenceSigmaValue allocated forced derivation⟩)
                ((reaches_computation bodyFree (Fin.cases (motive := fun _ => Tm Head m) term native) values needs env refs
                  covers valuesOk).1
                  middle landed.fresh _ _)
            · exact Reaches.failStable primitive (.returns .native) fault landed.fresh
                ⟨.sequenceSigmaFault body.erase allocated forced (.stableFault fault)⟩
            · exact Reaches.failRetry primitive (.returns .native) reason landed.fresh
                ⟨.sequenceSigmaFault body.erase allocated forced (.retryableFault _)⟩
    | _, _, scope, shape, _, .choose (left := left) (right := right) leftFree rightFree, native, values, needs, env, refs,
        covers, valuesOk => by
        have leftReaches := (reaches_computation leftFree native values needs env refs covers valuesOk).1
        have rightReaches := (reaches_computation rightFree native values needs env refs covers valuesOk).1
        have leftOk : ClosureNeedFree ⟨_, scope.length, _, left.erase, native, values, needs⟩ :=
          ⟨rawNeedFree_erase leftFree, valuesOk⟩
        have rightOk : ClosureNeedFree ⟨_, scope.length, _, right.erase, native, values, needs⟩ :=
          ⟨rawNeedFree_erase rightFree, valuesOk⟩
        have producer : ∀ world cell, Fresh world →
            world.heap.lookup cell =
              some ⟨⟨_, scope.length, _, (Shaped.Computation.choose left right).erase, native, values, needs⟩, .suspended⟩ →
            ∀ store branch, Reaches primitive shape world
              (fun outcome final => Nonempty (Force primitive cell world outcome final))
              (chooseAt shape (readComputation primitive left native env refs).1
                (readComputation primitive right native env refs).1) store branch := by
          intro world cell fresh present store branch
          refine Reaches.bind primitive shape _ _ fun prior member => ?_
          simp only [runWorldsAt, List.mem_append, List.mem_singleton] at member
          rcases member with rfl | rfl
          · exact ⟨world, _, Lands.of_heap fresh rfl, fun _ _ reached => reached,
              reaches_force primitive present fresh (.left _ _ native values needs) leftOk
                (leftReaches _ (fresh.enter present 0 .left) _ _)⟩
          · exact ⟨world, _, Lands.of_heap fresh rfl, fun _ _ reached => reached,
              reaches_force primitive present fresh (.right _ _ native values needs) rightOk
                (rightReaches _ (fresh.enter present 1 .right) _ _)⟩
        refine ⟨fun world fresh store branch => ?_, producer⟩
        obtain ⟨next, allocated, freshNext⟩ :=
          fresh.allocate ⟨_, scope.length, _, (Shaped.Computation.choose left right).erase, native, values, needs⟩
        have present := allocated_suspended allocated
        refine Reaches.bind primitive shape _ _ fun prior member => ?_
        simp only [runWorldsAt, List.mem_singleton] at member
        subst member
        refine ⟨next, fun outcome final => Nonempty (Force primitive (world.freshCell 0) next outcome final),
          Lands.alloc allocated freshNext, fun _ _ ⟨forced⟩ => ⟨.choose _ _ allocated forced⟩, ?_⟩
        cases shape with
        | returns answer =>
            intro result member
            obtain ⟨inner, innerMember, answerEq⟩ := cellAt_inv answer _ store branch member
            simp only [runWorldsAt, List.mem_append] at innerMember
            rcases innerMember with innerMember | innerMember
            · obtain ⟨outcome, final, reached, landed, agrees⟩ :=
                reaches_force primitive present freshNext (.left _ _ native values needs) leftOk
                  (leftReaches _ (freshNext.enter present 0 .left) _ _) inner innerMember
              exact ⟨outcome, final, reached, landed, answerEq ▸ agrees⟩
            · obtain ⟨outcome, final, reached, landed, agrees⟩ :=
                reaches_force primitive present freshNext (.right _ _ native values needs) rightOk
                  (rightReaches _ (freshNext.enter present 1 .right) _ _) inner innerMember
              exact ⟨outcome, final, reached, landed, answerEq ▸ agrees⟩
        | nativePi shape => exact producer next _ freshNext present (store ++ [none]) branch
        | arrow domain shape => exact producer next _ freshNext present (store ++ [none]) branch
end

#print axioms reaches_computation

/-! ## Exact agreement -/

theorem outcomeAgrees_native {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {answer : ScopedNeedMachine.Outcome Head StableFault NativeFault m}
    (agreed : OutcomeAgrees (Covers primitive .native) outcome answer) :
    outcome = PolarizedNeedEmbedding.outcome answer := by
  rcases agreed.cases with ⟨value, term, rfl, rfl, covered⟩ | ⟨fault, rfl, rfl⟩ | ⟨reason, rfl, rfl⟩
  · rw [covers_native primitive covered]
    rfl
  · rfl
  · rfl

/-- **Every answer of the reading is a natural outcome**: from every fresh
heap, for a closed native returner without need cells, with first-class
thunks, value and native lambdas, packages, sequencing and choice at every
shape. -/
theorem needFree_complete {computation : Shaped.Computation Head Operation Effect 0 [] 0 (.returns .native)}
    (needFree : computation.NeedFree) (native : Sub Head 0 m)
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} (fresh : Fresh world)
    {answer : ScopedNeedMachine.Outcome Head StableFault NativeFault m}
    (member : answer ∈ answers primitive computation native) :
    ∃ final, Nonempty (Eval primitive ⟨0, 0, 0, computation.erase, native, Fin.elim0, Fin.elim0⟩ world
      (PolarizedNeedEmbedding.outcome answer) final) := by
  obtain ⟨result, resultMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨outcome, final, ⟨derivation⟩, _, agrees⟩ :=
    (reaches_computation primitive needFree native Fin.elim0 Fin.elim0 SemEnv.empty Fin.elim0
      (fun _ index => nomatch index) (fun index => index.elim0)).1 world fresh [] [] result resultMember
  rw [← outcomeAgrees_native primitive agrees]
  exact ⟨final, ⟨derivation⟩⟩

/-- **The reading and the natural semantics agree exactly**: from every
fresh heap, for a closed native returner without need cells and every
primitive, the natural outcomes are the reading's answers, with none
excluded. -/
theorem needFree_agreement
    {computation : Shaped.Computation Head Operation Effect 0 [] 0 (.returns .native)}
    (needFree : computation.NeedFree) (native : Sub Head 0 m)
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} (fresh : Fresh world)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    outcome ∈ (answers primitive computation native).map PolarizedNeedEmbedding.outcome ↔
      ∃ final, Nonempty (Eval primitive ⟨0, 0, 0, computation.erase, native, Fin.elim0, Fin.elim0⟩ world outcome
        final) := by
  constructor
  · intro member
    obtain ⟨answer, answerMember, rfl⟩ := List.mem_map.mp member
    exact needFree_complete primitive needFree native fresh answerMember
  · rintro ⟨final, ⟨derivation⟩⟩
    obtain ⟨answer, answerMember, equal⟩ := fresh_sound primitive needFree native fresh derivation
    exact List.mem_map.mpr ⟨answer, answerMember, equal.symm⟩

#print axioms needFree_complete
#print axioms needFree_agreement

/-! ## Examples -/

namespace Examples

open Shaped
open ScopedNeedNaturalSemantics.Examples (ExampleOperation)
open PolarizedValues.Examples (examplePrimitive thunkedCoin thunkedCoin_needFree thunkedCoin_answers collidingWorld
  sequenced sequenced_answers)
open PolarizedFresh.Examples (emptyWorld emptyWorld_fresh)

/-- **Positive: a thunk of a choice, forced twice, from the empty heap**:
the natural outcomes are exactly the four pairs, the mixed ones among them. -/
theorem thunkedCoin_agreement (outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0) :
    outcome ∈ ([.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
      .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] :
        List (ScopedNeedMachine.Outcome Nat Nat Nat 0)).map PolarizedNeedEmbedding.outcome ↔
      ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, 0, thunkedCoin.erase, ids, Fin.elim0, Fin.elim0⟩ emptyWorld
        outcome final) := by
  rw [← thunkedCoin_answers]
  exact needFree_agreement examplePrimitive thunkedCoin_needFree ids emptyWorld_fresh outcome

/-- A choice between two native functions, applied to a head. -/
def appliedChoice : Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .nativeApply (.choose (.nativeLambda (.returnValue (.native (.var 0))))
    (.nativeLambda (.returnValue (.native (.head 2))))) (.head 1)

theorem appliedChoice_needFree : appliedChoice.NeedFree := by
  repeat' constructor

theorem appliedChoice_answers :
    answers (Effect := Nat) examplePrimitive appliedChoice ids = [.value (.head 1), .value (.head 2)] := by
  decide

/-- **Positive: a choice between functions, applied, reaches both answers**:
the selected function runs after its cell caches it, from a heap the
alternative's own derivation never reached. -/
theorem appliedChoice_left :
    ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, 0, appliedChoice.erase, ids, Fin.elim0, Fin.elim0⟩ emptyWorld
      (.value (.returned (.native (.head 1)))) final) :=
  needFree_complete examplePrimitive appliedChoice_needFree ids emptyWorld_fresh
    (answer := .value (.head 1)) (by rw [appliedChoice_answers]; exact List.mem_cons_self ..)

theorem appliedChoice_agreement (outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0) :
    outcome ∈ ([.value (.head 1), .value (.head 2)] :
        List (ScopedNeedMachine.Outcome Nat Nat Nat 0)).map PolarizedNeedEmbedding.outcome ↔
      ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, 0, appliedChoice.erase, ids, Fin.elim0, Fin.elim0⟩ emptyWorld
        outcome final) := by
  rw [← appliedChoice_answers]
  exact needFree_agreement examplePrimitive appliedChoice_needFree ids emptyWorld_fresh outcome

/-- A world holding one cell, behind the next allocation, with a given cache. -/
def heldWorld (cache : Cache (PolarizedNeedMachine.Answer Nat ExampleOperation Nat 0) Nat) :
    PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0 :=
  { lineage := 0, path := [], receipts := .empty, nextCell := 1, nextEvaluator := 0,
    heap := { current := Function.update (fun _ => none) ⟨0, [], 0, 0⟩
                (some ⟨⟨0, 0, 0, .returnValue (.native (.head 7)), ids, Fin.elim0, Fin.elim0⟩, cache⟩),
              spine := [] } }

theorem heldWorld_fresh (cache : Cache (PolarizedNeedMachine.Answer Nat ExampleOperation Nat 0) Nat) :
    Fresh (heldWorld cache) := by
  intro cell record found _
  by_cases same : cell = ⟨0, [], 0, 0⟩
  · subst same
    exact ⟨List.prefix_refl _, fun _ => Nat.zero_lt_one⟩
  · simp [heldWorld, Heap.lookup, Function.update_of_ne same] at found

/-- Two held worlds differ only at their one cell. -/
theorem heldWorld_twin (cache cache' : Cache (PolarizedNeedMachine.Answer Nat ExampleOperation Nat 0) Nat) :
    Twin (· = (⟨0, [], 0, 0⟩ : CellId)) (heldWorld cache) (heldWorld cache') := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro cell same
    subst same
    exact ⟨⟨⟨⟨0, 0, 0, .returnValue (.native (.head 7)), ids, Fin.elim0, Fin.elim0⟩, cache⟩,
        by simp [heldWorld, Heap.lookup]⟩,
      ⟨⟨0, 0, 0, .returnValue (.native (.head 7)), ids, Fin.elim0, Fin.elim0⟩, cache'⟩,
        by simp [heldWorld, Heap.lookup]⟩
  · intro cell different
    simp [heldWorld, Heap.lookup, Function.update_of_ne different]

theorem appliedChoice_held :
    ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, 0, appliedChoice.erase, ids, Fin.elim0, Fin.elim0⟩
      (heldWorld .suspended) (.value (.returned (.native (.head 1)))) final) :=
  needFree_complete examplePrimitive appliedChoice_needFree ids (heldWorld_fresh .suspended)
    (answer := .value (.head 1)) (by rw [appliedChoice_answers]; exact List.mem_cons_self ..)

/-- **Positive: what a cell the code never allocated caches does not
matter**: the applied choice, derived from a world whose one cell is
suspended, runs alike from the twin world where that cell caches an answer,
and leaves the cell as it was. -/
theorem appliedChoice_twin :
    ∃ final', Nonempty (Eval examplePrimitive ⟨0, 0, 0, appliedChoice.erase, ids, Fin.elim0, Fin.elim0⟩
        (heldWorld (.value (.returned (.native (.head 9))))) (.value (.returned (.native (.head 1)))) final') ∧
      Twin (· = (⟨0, [], 0, 0⟩ : CellId)) (Classical.choose appliedChoice_held) final' ∧
      Untouched (· = (⟨0, [], 0, 0⟩ : CellId)) (heldWorld (.value (.returned (.native (.head 9))))) final' :=
  eval_twin examplePrimitive (Classical.choose_spec appliedChoice_held).some (heldWorld_fresh .suspended)
    ⟨rawNeedFree_erase appliedChoice_needFree, fun index => index.elim0⟩ (heldWorld_twin _ _)

/-- **Negative: without a fresh heap an answer of the reading has no
derivation**: from the colliding world the allocation of `sequenced`
collides, so its only answer is not a natural outcome. -/
theorem collision_incomplete :
    (.value (.head 1) : ScopedNeedMachine.Outcome Nat Nat Nat 0) ∈ answers (Effect := Nat) examplePrimitive sequenced ids ∧
      ¬ ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, 0, sequenced.erase, ids, Fin.elim0, Fin.elim0⟩ collidingWorld
        (PolarizedNeedEmbedding.outcome (.value (.head 1))) final) := by
  refine ⟨by rw [sequenced_answers]; exact List.mem_singleton_self _, ?_⟩
  rintro ⟨final, ⟨derivation⟩⟩
  have collides : ∀ origin : PolarizedNeedMachine.Closure Nat ExampleOperation Nat 0,
      collidingWorld.allocate? origin = none := by
    intro origin
    simp [collidingWorld, World.allocate?, Heap.allocate?, Heap.lookup, World.freshCell]
  cases derivation with
  | bindNativeValue allocated _ _ => rw [collides] at allocated; cases allocated
  | bindNativeFault _ allocated _ faulted => cases faulted

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.PolarizedComplete
