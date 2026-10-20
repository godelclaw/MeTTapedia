import Mettapedia.TypeTheory.ContextualCBPVPolarizedNeedCells

/-!
# Fresh heaps in place of the retry exclusion

`PolarizedValues.needFree_sound` and `PolarizedNeedCells.sound` hold from any
world for every natural outcome other than a retry the machine raises itself.
From a fresh heap the machine raises none, so the exclusion goes away.

* `Fresh` and `Lands` are run 4's freshness and landing invariants, stated for
  the generic world of the need machines.
* `eval_clean`: from a fresh heap, a derivation of a closure without need
  cells lands in a fresh heap that keeps every cell and evaluates exactly the
  cells the starting heap evaluated, and answers values and functions without
  need cells.
* `fresh_sound`: from a fresh heap, every natural outcome of a closed native
  returner without need cells is an answer of the reading, for every
  primitive, with no outcome excluded.  The proof is the logical relation of
  `needFree_sound` read from fresh heaps (`RelValueF`, `GoodFromF`,
  `fundamental_computationF`): every intermediate heap is fresh by
  `eval_clean`, so allocation never collides and every finalization answers
  its producer's outcome, and a retry a primitive reports is an answer of the
  reading like any other outcome, whatever its reason.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.PolarizedFresh

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open PolarizedValues
open PolarizedNeedMachine (RuntimeValue)
open PolarizedNeedNaturalSemantics (Eval Force Selection)

/-! ## Freshness and landing for every need world -/

section Generic

variable {Origin Rule Value StableFault RetryableFault Effect : Type}

/-- Allocation never collides: the cells of the world's lineage are born on a
prefix of its path, and those born on the path itself have smaller slots. -/
def Fresh (world : World Origin Rule Value StableFault RetryableFault Effect) : Prop :=
  ∀ cell record, world.heap.lookup cell = some record → cell.lineage = world.lineage →
    cell.birth <+: world.path ∧ (cell.birth = world.path → cell.slot < world.nextCell)

theorem Fresh.of_same {world next : World Origin Rule Value StableFault RetryableFault Effect}
    (fresh : Fresh world)
    (domain : ∀ cell record, next.heap.lookup cell = some record → ∃ record', world.heap.lookup cell = some record')
    (lineage : next.lineage = world.lineage) (path : next.path = world.path)
    (nextCell : next.nextCell = world.nextCell) : Fresh next := by
  intro cell record present sameLineage
  obtain ⟨record', present'⟩ := domain cell record present
  rw [path, nextCell]
  exact fresh cell record' present' (lineage ▸ sameLineage)

theorem Fresh.record {world : World Origin Rule Value StableFault RetryableFault Effect} (fresh : Fresh world)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) : Fresh (world.record payload).1 :=
  fresh.of_same (fun _cell record present => ⟨record, present⟩) rfl rfl rfl

theorem Fresh.allocate {world : World Origin Rule Value StableFault RetryableFault Effect} (fresh : Fresh world)
    (origin : Origin) : ∃ next, world.allocate? origin = some (next, world.freshCell 0) ∧ Fresh next := by
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

theorem Fresh.allocated {world next : World Origin Rule Value StableFault RetryableFault Effect} (fresh : Fresh world)
    {origin : Origin} {cell : CellId} (allocated : world.allocate? origin = some (next, cell)) : Fresh next := by
  obtain ⟨next', allocated', freshNext⟩ := fresh.allocate origin
  rw [allocated] at allocated'
  cases allocated'
  exact freshNext

theorem Fresh.allocate_ne_none {world : World Origin Rule Value StableFault RetryableFault Effect}
    (fresh : Fresh world) (origin : Origin) : world.allocate? origin ≠ none := by
  obtain ⟨next, allocated, _⟩ := fresh.allocate origin
  rw [allocated]
  exact Option.some_ne_none _

theorem Fresh.empty (world : World Origin Rule Value StableFault RetryableFault Effect)
    (empty : ∀ cell, world.heap.lookup cell = none) : Fresh world := by
  intro cell record found
  rw [empty cell] at found
  cases found

/-- The final heap of a derivation from a fresh heap: still fresh, keeping
every cell with its origin, evaluating exactly the cells the starting heap
evaluated. -/
structure Lands (world final : World Origin Rule Value StableFault RetryableFault Effect) : Prop where
  fresh : Fresh final
  extends' : ∀ cell origin cache, world.heap.lookup cell = some ⟨origin, cache⟩ →
    ∃ cache', final.heap.lookup cell = some ⟨origin, cache'⟩
  keeps : ∀ cell record owner, world.heap.lookup cell = some record → record.cache = .evaluating owner →
    final.heap.lookup cell = some record
  noNew : ∀ cell record owner, final.heap.lookup cell = some record → record.cache = .evaluating owner →
    world.heap.lookup cell = some record

theorem Lands.of_heap {world next : World Origin Rule Value StableFault RetryableFault Effect}
    (fresh : Fresh next) (same : next.heap = world.heap) : Lands world next :=
  ⟨fresh, fun cell origin cache present => ⟨cache, by rw [same]; exact present⟩,
    fun cell record _ present _ => by rw [same]; exact present,
    fun cell record _ present _ => by rw [← same]; exact present⟩

theorem Lands.trans {world middle final : World Origin Rule Value StableFault RetryableFault Effect}
    (first : Lands world middle) (second : Lands middle final) : Lands world final :=
  ⟨second.fresh, fun cell origin cache present => by
      obtain ⟨cache', present'⟩ := first.extends' cell origin cache present
      exact second.extends' cell origin cache' present',
    fun cell record owner present evaluating =>
      second.keeps cell record owner (first.keeps cell record owner present evaluating) evaluating,
    fun cell record owner present evaluating =>
      first.noNew cell record owner (second.noNew cell record owner present evaluating) evaluating⟩

theorem Lands.alloc {world next : World Origin Rule Value StableFault RetryableFault Effect} {origin : Origin}
    {cell : CellId} (allocated : world.allocate? origin = some (next, cell)) (fresh : Fresh next) :
    Lands world next := by
  obtain ⟨absent, present, others⟩ := PolarizedNeedCells.allocate_spec allocated
  refine ⟨fresh, ?_, ?_, ?_⟩
  · intro other origin' cache found
    have different : other ≠ cell := by
      intro equal; subst equal; rw [absent] at found; cases found
    rw [others other different]
    exact ⟨cache, found⟩
  · intro other record owner found _
    have different : other ≠ cell := by
      intro equal; subst equal; rw [absent] at found; cases found
    rw [others other different]
    exact found
  · intro other record owner found evaluating
    by_cases same : other = cell
    · subst same
      rw [present] at found
      cases found
      cases evaluating
    · rw [others other same] at found
      exact found

end Generic

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

theorem Fresh.enter {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world) {cell : CellId} {origin : PolarizedNeedMachine.Closure Head Operation Effect m}
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (position : Nat) (rule : PolarizedNeedMachine.Rule) :
    Fresh (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) := by
  intro other record found sameLineage
  rw [PolarizedNeedCells.enterWorld_lookup] at found
  have original : ∃ record', world.heap.lookup other = some record' := by
    by_cases same : other = cell
    · subst same; exact ⟨_, present⟩
    · rw [if_neg same] at found; exact ⟨record, found⟩
  obtain ⟨record', present'⟩ := original
  have lineage : (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).lineage = world.lineage := rfl
  have path : (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).path =
      world.path ++ [position] := rfl
  have nextCell : (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).nextCell =
      world.nextCell := rfl
  rw [lineage] at sameLineage
  obtain ⟨isPrefix, _⟩ := fresh other record' present' sameLineage
  rw [path]
  refine ⟨isPrefix.trans (List.prefix_append _ _), fun equal => ?_⟩
  have := isPrefix.length_le
  rw [equal] at this
  simp at this

/-- A finalization by the owner answers the producer's outcome and caches it. -/
theorem finalize_of_owned {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {owner : EvaluatorId}
    {record : CellRecord (PolarizedNeedMachine.Closure Head Operation Effect m)
      (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault}
    (present : world.heap.lookup cell = some record) (owned : record.cache = .evaluating owner)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).1 = outcome ∧
      (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2.heap =
        (world.setKnownCache cell record (PolarizedNeedCells.cacheOf outcome)).heap ∧
      (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2.lineage = world.lineage ∧
      (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2.path = world.path ∧
      (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).2.nextCell = world.nextCell := by
  unfold PolarizedNeedNaturalSemantics.finalize
  rw [present]
  simp only [owned, if_true]
  cases outcome <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cacheOf_ne_evaluating (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m)
    (owner : EvaluatorId) : PolarizedNeedCells.cacheOf outcome ≠ .evaluating owner := by
  cases outcome <;> simp [PolarizedNeedCells.cacheOf]

/-- A cell forced from a fresh heap: entering it, running its producer to a
landing, and finalizing it lands again, and the owner answers the producer's
outcome. -/
theorem lands_force {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : PolarizedNeedMachine.Closure Head Operation Effect m}
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩) (position : Nat) (rule : PolarizedNeedMachine.Rule)
    {bodyFinal : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {bodyOutcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    (landed : Lands (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule) bodyFinal) :
    (PolarizedNeedNaturalSemantics.finalize bodyFinal cell world.nextEvaluator bodyOutcome).1 = bodyOutcome ∧
      Lands world (PolarizedNeedNaturalSemantics.finalize bodyFinal cell world.nextEvaluator bodyOutcome).2 := by
  have owned : bodyFinal.heap.lookup cell = some ⟨origin, .evaluating world.nextEvaluator⟩ := by
    refine landed.keeps cell _ world.nextEvaluator ?_ rfl
    rw [PolarizedNeedCells.enterWorld_lookup, if_pos rfl]
  obtain ⟨outcomeEq, heapEq, lineageEq, pathEq, nextEq⟩ := finalize_of_owned owned rfl bodyOutcome
  refine ⟨outcomeEq, ?_⟩
  have finalLookup : ∀ target,
      (PolarizedNeedNaturalSemantics.finalize bodyFinal cell world.nextEvaluator bodyOutcome).2.heap.lookup target =
        if target = cell then some ⟨origin, PolarizedNeedCells.cacheOf bodyOutcome⟩ else bodyFinal.heap.lookup target := by
    intro target
    rw [heapEq]
    simp only [World.setKnownCache]
    rw [ScopedNeed.lookup_setKnownCache]
  have enterLookup : ∀ target, target ≠ cell →
      (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).heap.lookup target =
        world.heap.lookup target := by
    intro target different
    rw [PolarizedNeedCells.enterWorld_lookup, if_neg different]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine landed.fresh.of_same ?_ lineageEq pathEq nextEq
    intro target found foundPresent
    rw [finalLookup] at foundPresent
    by_cases same : target = cell
    · subst same; exact ⟨_, owned⟩
    · rw [if_neg same] at foundPresent; exact ⟨found, foundPresent⟩
  · intro target origin' cache found
    rw [finalLookup]
    by_cases same : target = cell
    · subst same
      rw [present] at found
      cases found
      rw [if_pos rfl]
      exact ⟨_, rfl⟩
    · rw [if_neg same]
      have entered : (PolarizedNeedNaturalSemantics.enterWorld world cell origin position rule).heap.lookup target =
          some ⟨origin', cache⟩ := by rw [enterLookup target same]; exact found
      exact landed.extends' target origin' cache entered
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

/-! ## Code and values without need cells -/

mutual
  /-- Raw values whose thunks use no need cell. -/
  inductive RawValueNeedFree : {n v k : Nat} → PolarizedNeed.Value Head Operation Effect n v k → Prop where
    | native {n v k : Nat} (term : Tm Head n) :
        RawValueNeedFree (PolarizedNeed.Value.native (Operation := Operation) (Effect := Effect) (v := v) (k := k) term)
    | variable {n v k : Nat} (index : Fin v) :
        RawValueNeedFree
          (PolarizedNeed.Value.variable (Head := Head) (Operation := Operation) (Effect := Effect) (n := n) (k := k) index)
    | thunk {n v k : Nat} {body : PolarizedNeed.Computation Head Operation Effect n v k} :
        RawNeedFree body → RawValueNeedFree (.thunk body)
    | packNative {n v k : Nat} (index : Tm Head n) {value : PolarizedNeed.Value Head Operation Effect n v k} :
        RawValueNeedFree value → RawValueNeedFree (.packNative index value)

  /-- Raw code without `letNeed` or `forceNeed`. -/
  inductive RawNeedFree : {n v k : Nat} → PolarizedNeed.Computation Head Operation Effect n v k → Prop where
    | returnValue {n v k : Nat} {value : PolarizedNeed.Value Head Operation Effect n v k} :
        RawValueNeedFree value → RawNeedFree (.returnValue value)
    | bindNative {n v k : Nat} {first : PolarizedNeed.Computation Head Operation Effect n v k}
        {body : PolarizedNeed.Computation Head Operation Effect (n + 1) v k} :
        RawNeedFree first → RawNeedFree body → RawNeedFree (.bindNative first body)
    | bindValue {n v k : Nat} {first : PolarizedNeed.Computation Head Operation Effect n v k}
        {body : PolarizedNeed.Computation Head Operation Effect n (v + 1) k} :
        RawNeedFree first → RawNeedFree body → RawNeedFree (.bindValue first body)
    | sequenceSigma {n v k : Nat} {first : PolarizedNeed.Computation Head Operation Effect n v k}
        {body : PolarizedNeed.Computation Head Operation Effect (n + 1) v k} :
        RawNeedFree first → RawNeedFree body → RawNeedFree (.sequenceSigma first body)
    | nativeLambda {n v k : Nat} {body : PolarizedNeed.Computation Head Operation Effect (n + 1) v k} :
        RawNeedFree body → RawNeedFree (.nativeLambda body)
    | nativeApply {n v k : Nat} {function : PolarizedNeed.Computation Head Operation Effect n v k}
        (argument : Tm Head n) : RawNeedFree function → RawNeedFree (.nativeApply function argument)
    | valueLambda {n v k : Nat} {body : PolarizedNeed.Computation Head Operation Effect n (v + 1) k} :
        RawNeedFree body → RawNeedFree (.valueLambda body)
    | valueApply {n v k : Nat} {function : PolarizedNeed.Computation Head Operation Effect n v k}
        {argument : PolarizedNeed.Value Head Operation Effect n v k} :
        RawNeedFree function → RawValueNeedFree argument → RawNeedFree (.valueApply function argument)
    | forceThunk {n v k : Nat} {value : PolarizedNeed.Value Head Operation Effect n v k} :
        RawValueNeedFree value → RawNeedFree (.forceThunk value)
    | unpackNative {n v k : Nat} {value : PolarizedNeed.Value Head Operation Effect n v k}
        {body : PolarizedNeed.Computation Head Operation Effect (n + 1) (v + 1) k} :
        RawValueNeedFree value → RawNeedFree body → RawNeedFree (.unpackNative value body)
    | choose {n v k : Nat} {left right : PolarizedNeed.Computation Head Operation Effect n v k} :
        RawNeedFree left → RawNeedFree right → RawNeedFree (.choose left right)
    | call {n v k : Nat} (operation : Operation) (argument : Tm Head n) :
        RawNeedFree (PolarizedNeed.Computation.call (Head := Head) (Effect := Effect) (v := v) (k := k) operation argument)
    | emit {n v k : Nat} (effect : Effect) {next : PolarizedNeed.Computation Head Operation Effect n v k} :
        RawNeedFree next → RawNeedFree (.emit effect next)
end

/-- Run-time values whose thunks use no need cell. -/
inductive RuntimeNeedFree : RuntimeValue Head Operation Effect m → Prop where
  | native (term : Tm Head m) : RuntimeNeedFree (.native term)
  | thunk {n v k : Nat} {code : PolarizedNeed.Computation Head Operation Effect n v k} {native : Sub Head n m}
      {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId} :
      RawNeedFree code → (∀ index, RuntimeNeedFree (values index)) →
        RuntimeNeedFree (.thunk code native values needs)
  | packNative (index : Tm Head m) {value : RuntimeValue Head Operation Effect m} :
      RuntimeNeedFree value → RuntimeNeedFree (.packNative index value)

/-- A closure without need cells. -/
def ClosureNeedFree (closure : PolarizedNeedMachine.Closure Head Operation Effect m) : Prop :=
  RawNeedFree closure.code ∧ ∀ index, RuntimeNeedFree (closure.values index)

/-- An outcome without need cells: a returned value or a function body. -/
def OutcomeNeedFree : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m → Prop
  | .value (.returned value) => RuntimeNeedFree value
  | .value (.nativeFunction body) => RawNeedFree body.code ∧ ∀ index, RuntimeNeedFree (body.values index)
  | .value (.valueFunction body) => RawNeedFree body.code ∧ ∀ index, RuntimeNeedFree (body.values index)
  | _ => True

theorem capture_needFree {n v k : Nat} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (valuesOk : ∀ index, RuntimeNeedFree (values index)) :
    {value : PolarizedNeed.Value Head Operation Effect n v k} → RawValueNeedFree value →
      RuntimeNeedFree (PolarizedNeedMachine.captureValue native values needs value)
  | _, .native term => .native _
  | _, .variable index => valuesOk index
  | _, .thunk bodyOk => .thunk bodyOk valuesOk
  | _, .packNative index valueOk => .packNative _ (capture_needFree valuesOk valueOk)

theorem cases_needFree {v : Nat} {value : RuntimeValue Head Operation Effect m}
    {values : Fin v → RuntimeValue Head Operation Effect m}
    (head : RuntimeNeedFree value) (rest : ∀ index, RuntimeNeedFree (values index)) :
    ∀ index, RuntimeNeedFree ((Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values :
      Fin (v + 1) → RuntimeValue Head Operation Effect m) index) := by
  intro index
  refine Fin.cases ?_ (fun j => ?_) index
  · exact head
  · exact rest j

theorem pairOutcome_needFree {first : Tm Head m}
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    OutcomeNeedFree (PolarizedNeedNaturalSemantics.pairOutcome first outcome) := by
  cases outcome with
  | value answer =>
      cases answer with
      | returned value =>
          cases value with
          | native term => exact RuntimeNeedFree.native _
          | thunk _ _ _ _ => simp [PolarizedNeedNaturalSemantics.pairOutcome, OutcomeNeedFree]
          | packNative _ _ => simp [PolarizedNeedNaturalSemantics.pairOutcome, OutcomeNeedFree]
      | nativeFunction _ => simp [PolarizedNeedNaturalSemantics.pairOutcome, OutcomeNeedFree]
      | valueFunction _ => simp [PolarizedNeedNaturalSemantics.pairOutcome, OutcomeNeedFree]
  | stableFault _ => simp [PolarizedNeedNaturalSemantics.pairOutcome, OutcomeNeedFree]
  | retryableFault _ => simp [PolarizedNeedNaturalSemantics.pairOutcome, OutcomeNeedFree]

theorem selection_needFree {origin selected : PolarizedNeedMachine.Closure Head Operation Effect m}
    {position : Nat} {rule : PolarizedNeedMachine.Rule}
    (selection : Selection origin position rule selected) (originOk : ClosureNeedFree origin) :
    ClosureNeedFree selected := by
  cases selection with
  | entry _ => exact originOk
  | left =>
      obtain ⟨codeOk, valuesOk⟩ := originOk
      cases codeOk with
      | choose leftOk _ => exact ⟨leftOk, valuesOk⟩
  | right =>
      obtain ⟨codeOk, valuesOk⟩ := originOk
      cases codeOk with
      | choose _ rightOk => exact ⟨rightOk, valuesOk⟩

/-! ## From a fresh heap the machine raises no retry -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

/-- What a derivation from a fresh heap keeps: a landing, and an answer
without need cells. -/
abbrev Clean (world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) : Prop :=
  Lands world final ∧ OutcomeNeedFree outcome

mutual
  /-- **From a fresh heap, a derivation of a closure without need cells is
  clean**: it lands, and its answer has no need cells. -/
  theorem eval_clean : {closure : PolarizedNeedMachine.Closure Head Operation Effect m} →
      {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
      {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
      Eval primitive closure world outcome final → Fresh world → ClosureNeedFree closure → Clean world final outcome
    | _, _, _, _, .returnValue _ _ _ _ _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | returnValue valueOk =>
            exact ⟨Lands.of_heap fresh rfl, capture_needFree valuesOk valueOk⟩
    | _, _, _, _, .nativeLambda _ _ _ _ _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | nativeLambda bodyOk => exact ⟨Lands.of_heap fresh rfl, bodyOk, valuesOk⟩
    | _, _, _, _, .valueLambda _ _ _ _ _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | valueLambda bodyOk => exact ⟨Lands.of_heap fresh rfl, bodyOk, valuesOk⟩
    | _, _, _, _, .call operation argument native _ _ _, fresh, _ => by
        refine ⟨Lands.of_heap fresh rfl, ?_⟩
        generalize primitive operation (subst native argument) = produced
        cases produced with
        | value term => exact RuntimeNeedFree.native _
        | stableFault _ => trivial
        | retryableFault _ => trivial
    | _, world, _, _, .emit effect nextDerivation, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | emit _ nextOk =>
            obtain ⟨landed, outcomeOk⟩ := eval_clean nextDerivation (fresh.record _) ⟨nextOk, valuesOk⟩
            exact ⟨(Lands.of_heap (world := world) (fresh.record _) rfl).trans landed, outcomeOk⟩
    | _, _, _, _, .forceNeed _ _, _, ⟨codeOk, _⟩ => by cases codeOk
    | _, _, _, _, .nativeApply _ functionDerivation bodyDerivation, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | nativeApply _ functionOk =>
            obtain ⟨landed, ⟨bodyOk, bodyValuesOk⟩⟩ :=
              eval_clean functionDerivation fresh ⟨functionOk, valuesOk⟩
            obtain ⟨landed', outcomeOk⟩ :=
              eval_clean bodyDerivation landed.fresh ⟨bodyOk, bodyValuesOk⟩
            exact ⟨landed.trans landed', outcomeOk⟩
    | _, _, _, _, .nativeApplyMismatch _ functionDerivation _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | nativeApply _ functionOk =>
            obtain ⟨landed, _⟩ := eval_clean functionDerivation fresh ⟨functionOk, valuesOk⟩
            exact ⟨landed, trivial⟩
    | _, _, _, _, .nativeApplyFault _ functionDerivation _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | nativeApply _ functionOk => exact eval_clean functionDerivation fresh ⟨functionOk, valuesOk⟩
    | _, _, _, _, .valueApply _ functionDerivation bodyDerivation, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | valueApply functionOk argumentOk =>
            obtain ⟨landed, ⟨bodyOk, bodyValuesOk⟩⟩ :=
              eval_clean functionDerivation fresh ⟨functionOk, valuesOk⟩
            obtain ⟨landed', outcomeOk⟩ :=
              eval_clean bodyDerivation landed.fresh
                ⟨bodyOk, cases_needFree (capture_needFree valuesOk argumentOk) bodyValuesOk⟩
            exact ⟨landed.trans landed', outcomeOk⟩
    | _, _, _, _, .valueApplyMismatch _ functionDerivation _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | valueApply functionOk _ =>
            obtain ⟨landed, _⟩ := eval_clean functionDerivation fresh ⟨functionOk, valuesOk⟩
            exact ⟨landed, trivial⟩
    | _, _, _, _, .valueApplyFault _ functionDerivation _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | valueApply functionOk _ => exact eval_clean functionDerivation fresh ⟨functionOk, valuesOk⟩
    | _, _, _, _, @Eval.forceThunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ native _ needs _ _ _ _ _ _ _ captured thunkDerivation,
        fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | forceThunk valueOk =>
            have thunkOk := capture_needFree (native := native) (needs := needs) valuesOk valueOk
            rw [captured] at thunkOk
            cases thunkOk with
            | thunk codeOk' valuesOk' => exact eval_clean thunkDerivation fresh ⟨codeOk', valuesOk'⟩
    | _, _, _, _, .forceThunkMismatch _ _ _, fresh, _ => ⟨Lands.of_heap fresh rfl, trivial⟩
    | _, _, _, _, @Eval.unpackNative _ _ _ _ _ _ _ _ _ _ _ _ native _ needs _ _ _ _ _ captured bodyDerivation,
        fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | unpackNative valueOk bodyOk =>
            have packOk := capture_needFree (native := native) (needs := needs) valuesOk valueOk
            rw [captured] at packOk
            cases packOk with
            | packNative _ payloadOk =>
                exact eval_clean bodyDerivation fresh ⟨bodyOk, cases_needFree payloadOk valuesOk⟩
    | _, _, _, _, .unpackNativeMismatch _ _ _ _, fresh, _ => ⟨Lands.of_heap fresh rfl, trivial⟩
    | _, _, _, _, .bindNativeValue allocated forced bodyDerivation, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | bindNative firstOk bodyOk =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            obtain ⟨landed', outcomeOk⟩ := eval_clean bodyDerivation landed.fresh ⟨bodyOk, valuesOk⟩
            exact ⟨((Lands.alloc allocated freshAllocated).trans landed).trans landed', outcomeOk⟩
    | _, _, _, _, .bindNativeMismatch _ allocated forced _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | bindNative firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            exact ⟨(Lands.alloc allocated freshAllocated).trans landed, trivial⟩
    | _, _, _, _, .bindNativeFault _ allocated forced _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | bindNative firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, outcomeOk⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            exact ⟨(Lands.alloc allocated freshAllocated).trans landed, outcomeOk⟩
    | _, _, _, _, .bindNativeAllocationFailure _ failed, fresh, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .bindValueValue allocated forced bodyDerivation, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | bindValue firstOk bodyOk =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, valueOk⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            obtain ⟨landed', outcomeOk⟩ :=
              eval_clean bodyDerivation landed.fresh ⟨bodyOk, cases_needFree valueOk valuesOk⟩
            exact ⟨((Lands.alloc allocated freshAllocated).trans landed).trans landed', outcomeOk⟩
    | _, _, _, _, .bindValueMismatch _ allocated forced _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | bindValue firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            exact ⟨(Lands.alloc allocated freshAllocated).trans landed, trivial⟩
    | _, _, _, _, .bindValueFault _ allocated forced _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | bindValue firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, outcomeOk⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            exact ⟨(Lands.alloc allocated freshAllocated).trans landed, outcomeOk⟩
    | _, _, _, _, .bindValueAllocationFailure _ failed, fresh, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .sequenceSigmaValue allocated forced bodyDerivation, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | sequenceSigma firstOk bodyOk =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            obtain ⟨landed', _⟩ := eval_clean bodyDerivation landed.fresh ⟨bodyOk, valuesOk⟩
            exact ⟨((Lands.alloc allocated freshAllocated).trans landed).trans landed',
              pairOutcome_needFree _⟩
    | _, _, _, _, .sequenceSigmaMismatch _ allocated forced _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | sequenceSigma firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, _⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            exact ⟨(Lands.alloc allocated freshAllocated).trans landed, trivial⟩
    | _, _, _, _, .sequenceSigmaFault _ allocated forced _, fresh, ⟨codeOk, valuesOk⟩ => by
        cases codeOk with
        | sequenceSigma firstOk _ =>
            have freshAllocated := fresh.allocated allocated
            obtain ⟨landed, outcomeOk⟩ := force_clean forced freshAllocated _
              (allocated_suspended allocated) ⟨firstOk, valuesOk⟩
            exact ⟨(Lands.alloc allocated freshAllocated).trans landed, outcomeOk⟩
    | _, _, _, _, .sequenceSigmaAllocationFailure _ failed, fresh, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .choose _ _ allocated forced, fresh, closureOk => by
        have freshAllocated := fresh.allocated allocated
        obtain ⟨landed, outcomeOk⟩ := force_clean forced freshAllocated _
          (allocated_suspended allocated) closureOk
        exact ⟨(Lands.alloc allocated freshAllocated).trans landed, outcomeOk⟩
    | _, _, _, _, .chooseAllocationFailure _ _ failed, fresh, _ => absurd failed (fresh.allocate_ne_none _)
    | _, _, _, _, .letNeed _ _, _, ⟨codeOk, _⟩ => by cases codeOk
    | _, _, _, _, .letNeedAllocationFailure _ _, _, ⟨codeOk, _⟩ => by cases codeOk

  theorem force_clean : {cell : CellId} →
      {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} →
      {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
      Force primitive cell world outcome final → Fresh world →
      (origin : PolarizedNeedMachine.Closure Head Operation Effect m) →
      world.heap.lookup cell = some ⟨origin, .suspended⟩ → ClosureNeedFree origin → Clean world final outcome
    | _, _, _, _, .cachedValue found, _, _, present, _ => by rw [present] at found; cases found
    | _, _, _, _, .cachedStable found, _, _, present, _ => by rw [present] at found; cases found
    | _, _, _, _, .missing found, _, _, present, _ => by rw [present] at found; cases found
    | _, _, _, _, .evaluating found, _, _, present, _ => by rw [present] at found; cases found
    | _, _, _, _, @Force.suspended _ _ _ _ _ _ _ _ _ _ position rule _ _ _ found selection body, fresh, _, present,
        originOk => by
        rw [present] at found
        cases found
        obtain ⟨landed, outcomeOk⟩ :=
          eval_clean body (fresh.enter present position rule) (selection_needFree selection originOk)
        obtain ⟨outcomeEq, landedForce⟩ := lands_force present position rule landed
        rw [outcomeEq]
        exact ⟨landedForce, outcomeOk⟩
end

/-! ## Erasure keeps code without need cells -/

mutual
  theorem rawValueNeedFree_erase : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      {value : Shaped.Value Head Operation Effect n scope k shape} → value.NeedFree → RawValueNeedFree value.erase
    | _, _, _, _, _, .native term => .native term
    | _, _, _, _, _, .var index => .variable index.index
    | _, _, _, _, _, .thunk bodyOk => .thunk (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .pack index valueOk => .packNative index (rawValueNeedFree_erase valueOk)

  theorem rawNeedFree_erase : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      {computation : Shaped.Computation Head Operation Effect n scope k shape} → computation.NeedFree →
        RawNeedFree computation.erase
    | _, _, _, _, _, .returnValue valueOk => .returnValue (rawValueNeedFree_erase valueOk)
    | _, _, _, _, _, .bindNative firstOk bodyOk => .bindNative (rawNeedFree_erase firstOk) (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .bindValue firstOk bodyOk => .bindValue (rawNeedFree_erase firstOk) (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .sequenceSigma firstOk bodyOk =>
        .sequenceSigma (rawNeedFree_erase firstOk) (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .nativeLambda bodyOk => .nativeLambda (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .nativeApply argument functionOk => .nativeApply argument (rawNeedFree_erase functionOk)
    | _, _, _, _, _, .valueLambda bodyOk => .valueLambda (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .valueApply functionOk argumentOk =>
        .valueApply (rawNeedFree_erase functionOk) (rawValueNeedFree_erase argumentOk)
    | _, _, _, _, _, .forceThunk valueOk => .forceThunk (rawValueNeedFree_erase valueOk)
    | _, _, _, _, _, .unpackNative valueOk bodyOk =>
        .unpackNative (rawValueNeedFree_erase valueOk) (rawNeedFree_erase bodyOk)
    | _, _, _, _, _, .choose leftOk rightOk => .choose (rawNeedFree_erase leftOk) (rawNeedFree_erase rightOk)
    | _, _, _, _, _, .call operation argument => .call operation argument
    | _, _, _, _, _, .emit effect nextOk => .emit effect (rawNeedFree_erase nextOk)
end

/-! ## Soundness from a fresh heap, for every primitive -/

mutual
  /-- A run-time value and a value of the reading agree at a shape, for
  derivations from fresh heaps. -/
  def RelValueF : (shape : VShape) → RuntimeValue Head Operation Effect m →
      SemValue Head Effect StableFault NativeFault m shape → Prop
    | .native, value, semantic => value = .native semantic
    | .thunk shape, value, semantic =>
        ∃ (n v k : Nat) (code : PolarizedNeed.Computation Head Operation Effect n v k) (native : Sub Head n m)
          (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId),
          value = .thunk code native values needs ∧
            ∀ world, Fresh world → ∀ outcome final,
              Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final →
                ∀ store branch, GoodFromF shape outcome semantic store branch
    | .pack payload, value, semantic =>
        ∃ inner, value = .packNative semantic.1 inner ∧ RelValueF payload inner semantic.2

  /-- **A natural outcome is good for a computation of the reading**, run
  from a store.  For a returner, a world of the reading answers the outcome;
  no retry is excluded.  For a function, every application from a fresh heap
  is good. -/
  def GoodFromF : (shape : CShape) → PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
      SemComputation Head Effect StableFault NativeFault m shape → ScopedNeed.Store Head StableFault NativeFault m →
        BranchTrace → Prop
    | .returns answer, outcome, program, store, branch =>
        ∃ result ∈ runWorldsAt program store branch,
          match outcome, result.answer with
          | .value (.returned value), .value semantic => RelValueF answer value semantic
          | .stableFault fault, .stableFault fault' => fault = fault'
          | .retryableFault reason, .retryableFault reason' => reason = PolarizedNeedEmbedding.retry reason'
          | _, _ => False
    | .nativePi shape, outcome, function, store, branch =>
        ∀ argument,
          match outcome with
          | .value (.nativeFunction body) =>
              ∀ world, Fresh world → ∀ outcome' final', Eval primitive (body.open argument) world outcome' final' →
                GoodFromF shape outcome' (function argument) store branch
          | .value _ => False
          | fault => GoodFromF shape fault (function argument) store branch
    | .arrow domain shape, outcome, function, store, branch =>
        ∀ argument semantic, RelValueF domain argument semantic → RuntimeNeedFree argument →
          match outcome with
          | .value (.valueFunction body) =>
              ∀ world, Fresh world → ∀ outcome' final', Eval primitive (body.open argument) world outcome' final' →
                GoodFromF shape outcome' (function semantic) store branch
          | .value _ => False
          | fault => GoodFromF shape fault (function semantic) store branch
end

/-- Good from every store. -/
def GoodF (shape : CShape) (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m)
    (semantic : SemComputation Head Effect StableFault NativeFault m shape) : Prop :=
  ∀ store branch, GoodFromF primitive shape outcome semantic store branch

theorem GoodFromF.bind : (shape : CShape) → {Other : Type} →
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
    (program : Program (ScopedNeed.Store Head StableFault NativeFault m) Other Effect) →
    (next : Other → SemComputation Head Effect StableFault NativeFault m shape) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    (∃ prior ∈ runWorldsAt program store branch,
      GoodFromF primitive shape outcome (next prior.answer) prior.state prior.branch) →
    GoodFromF primitive shape outcome (bindAt shape program next) store branch
  | .returns _, _, _, _, _, _, _, ⟨_, member, _, resultMember, agrees⟩ =>
      ⟨_, ScopedNeed.mem_bind member resultMember, agrees⟩
  | .nativePi shape, _, outcome, program, next, _, _, ⟨prior, member, good⟩ => fun argument => by
      have atArgument := good argument
      cases outcome with
      | value answer =>
          cases answer with
          | nativeFunction body =>
              exact fun world fresh outcome' final' derivation =>
                GoodFromF.bind shape program (fun other => next other argument)
                  ⟨prior, member, atArgument world fresh outcome' final' derivation⟩
          | returned _ => exact atArgument.elim
          | valueFunction _ => exact atArgument.elim
      | stableFault _ =>
          exact GoodFromF.bind shape program (fun other => next other argument) ⟨prior, member, atArgument⟩
      | retryableFault _ =>
          exact GoodFromF.bind shape program (fun other => next other argument) ⟨prior, member, atArgument⟩
  | .arrow _ shape, _, outcome, program, next, _, _, ⟨prior, member, good⟩ => fun argument semantic related argumentOk => by
      have atArgument := good argument semantic related argumentOk
      cases outcome with
      | value answer =>
          cases answer with
          | valueFunction body =>
              exact fun world fresh outcome' final' derivation =>
                GoodFromF.bind shape program (fun other => next other semantic)
                  ⟨prior, member, atArgument world fresh outcome' final' derivation⟩
          | returned _ => exact atArgument.elim
          | nativeFunction _ => exact atArgument.elim
      | stableFault _ =>
          exact GoodFromF.bind shape program (fun other => next other semantic) ⟨prior, member, atArgument⟩
      | retryableFault _ =>
          exact GoodFromF.bind shape program (fun other => next other semantic) ⟨prior, member, atArgument⟩

theorem GoodFromF.failStable : (shape : CShape) → (fault : StableFault) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    GoodFromF primitive shape (.stableFault fault)
      (failAt (Head := Head) (Effect := Effect) shape (.stableFault fault)) store branch
  | .returns _, _, _, _ => ⟨_, List.mem_singleton_self _, rfl⟩
  | .nativePi shape, fault, _, _ => fun _ => GoodFromF.failStable shape fault
  | .arrow _ shape, fault, _, _ => fun _ _ _ _ => GoodFromF.failStable shape fault

theorem GoodFromF.failRetry : (shape : CShape) → (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    GoodFromF primitive shape (.retryableFault (PolarizedNeedEmbedding.retry reason))
      (failAt (Head := Head) (Effect := Effect) shape (.retryableFault reason)) store branch
  | .returns _, _, _, _ => ⟨_, List.mem_singleton_self _, rfl⟩
  | .nativePi shape, reason, _, _ => fun _ => GoodFromF.failRetry shape reason
  | .arrow _ shape, reason, _, _ => fun _ _ _ _ => GoodFromF.failRetry shape reason

/-- **The force of a fresh cell is good for its producer**, if every selected
occurrence of its origin is good from a fresh heap. -/
theorem forced_goodF {shape : CShape} {producer : SemComputation Head Effect StableFault NativeFault m shape}
    {origin : PolarizedNeedMachine.Closure Head Operation Effect m} (originOk : ClosureNeedFree origin)
    (selectedGood : ∀ position rule selected, Selection origin position rule selected →
      ∀ world, Fresh world → ∀ outcome final, Eval primitive selected world outcome final →
        GoodF primitive shape outcome producer)
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (fresh : Fresh world) (allocated : world.allocate? origin = some (next, cell))
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (forced : Force primitive cell next outcome final) : GoodF primitive shape outcome producer := by
  have freshNext := fresh.allocated allocated
  have present := allocated_suspended allocated
  cases forced with
  | cachedValue found => rw [present] at found; cases found
  | cachedStable found => rw [present] at found; cases found
  | missing found => rw [present] at found; cases found
  | evaluating found => rw [present] at found; cases found
  | @suspended _ _ selected position rule _ bodyFinal bodyOutcome found selection body =>
      rw [present] at found
      cases found
      have freshEntered := freshNext.enter present position rule
      obtain ⟨landed, _⟩ := eval_clean primitive body freshEntered (selection_needFree selection originOk)
      obtain ⟨outcomeEq, _⟩ := lands_force present position rule landed
      rw [outcomeEq]
      exact selectedGood _ _ _ selection _ freshEntered _ _ body

theorem GoodF.chooseLeft {shape : CShape}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {left right : SemComputation Head Effect StableFault NativeFault m shape} (good : GoodF primitive shape outcome left) :
    GoodF primitive shape outcome (chooseAt shape left right) := fun store branch =>
  GoodFromF.bind primitive shape _ _ ⟨⟨false :: branch, false, store, []⟩,
    List.mem_append_left _ (List.mem_singleton_self _), good store (false :: branch)⟩

theorem GoodF.chooseRight {shape : CShape}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {left right : SemComputation Head Effect StableFault NativeFault m shape} (good : GoodF primitive shape outcome right) :
    GoodF primitive shape outcome (chooseAt shape left right) := fun store branch =>
  GoodFromF.bind primitive shape _ _ ⟨⟨true :: branch, true, store, []⟩,
    List.mem_append_right _ (List.mem_singleton_self _), good store (true :: branch)⟩

/-- Only a choice has an occurrence other than itself. -/
theorem entry_onlyF {n v k : Nat} {code : PolarizedNeed.Computation Head Operation Effect n v k}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (notChoice : ∀ left right, code ≠ .choose left right)
    {Goal : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m → Prop}
    (good : ∀ world, Fresh world → ∀ outcome final,
      Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final → Goal outcome) :
    ∀ position rule selected, Selection ⟨n, v, k, code, native, values, needs⟩ position rule selected →
      ∀ world, Fresh world → ∀ outcome final, Eval primitive selected world outcome final → Goal outcome := by
  intro position rule selected selection
  cases selection with
  | entry _ => exact good
  | left left right _ _ _ => exact absurd rfl (notChoice left right)
  | right left right _ _ _ => exact absurd rfl (notChoice left right)

/-- Run-time and semantic environments agree variable by variable. -/
def RelEnvF {scope : List VShape} (values : Fin scope.length → RuntimeValue Head Operation Effect m)
    (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope) : Prop :=
  ∀ shape (index : Member scope shape), RelValueF primitive shape (values index.index) (env shape index)

theorem RelEnvF.cons {scope : List VShape} {shape : VShape}
    {values : Fin scope.length → RuntimeValue Head Operation Effect m}
    {env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope}
    (related : RelEnvF primitive values env) {value : RuntimeValue Head Operation Effect m}
    {semantic : SemValue Head Effect StableFault NativeFault m shape}
    (head : RelValueF primitive shape value semantic) :
    RelEnvF primitive (scope := shape :: scope)
      (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) (SemEnv.cons semantic env) := by
  intro shape' index
  cases index with
  | zero => exact head
  | succ index => exact related _ index

mutual
  /-- **A value reads as its run-time value**, in agreeing environments. -/
  theorem fundamental_valueF : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      {value : Shaped.Value Head Operation Effect n scope k shape} → value.NeedFree →
      (native : Sub Head n m) → (values : Fin scope.length → RuntimeValue Head Operation Effect m) →
      (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) → RelEnvF primitive values env →
      (∀ index, RuntimeNeedFree (values index)) →
      RelValueF primitive shape (PolarizedNeedMachine.captureValue native values needs value.erase)
        (readValue primitive value native env refs)
    | _, _, _, _, _, .native _, _, _, _, _, _, _, _ => rfl
    | _, _, _, _, _, .var index, _, _, _, _, _, related, _ => related _ index
    | _, _, _, _, _, .thunk (body := body) bodyFree, native, values, needs, env, refs, related, valuesOk =>
        ⟨_, _, _, body.erase, native, values, needs, rfl,
          (fundamental_computationF bodyFree native values needs env refs related valuesOk).1⟩
    | _, _, _, _, _, .pack _ (value := value) valueFree, native, values, needs, env, refs, related, valuesOk =>
        ⟨_, rfl, fundamental_valueF valueFree native values needs env refs related valuesOk⟩

  /-- **The fundamental lemma from fresh heaps**: every natural derivation of
  a computation without need cells, from a fresh heap, is good for its
  reading, and so is every derivation of a selected occurrence. -/
  theorem fundamental_computationF : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      {computation : Shaped.Computation Head Operation Effect n scope k shape} → computation.NeedFree →
      (native : Sub Head n m) → (values : Fin scope.length → RuntimeValue Head Operation Effect m) →
      (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) → RelEnvF primitive values env →
      (∀ index, RuntimeNeedFree (values index)) →
      (∀ world, Fresh world → ∀ outcome final,
        Eval primitive ⟨n, scope.length, k, computation.erase, native, values, needs⟩ world outcome final →
          GoodF primitive shape outcome (readComputation primitive computation native env refs).1) ∧
      (∀ position rule selected,
        Selection ⟨n, scope.length, k, computation.erase, native, values, needs⟩ position rule selected →
          ∀ world, Fresh world → ∀ outcome final, Eval primitive selected world outcome final →
            GoodF primitive shape outcome (readComputation primitive computation native env refs).2)
    | _, _, _, _, _, .returnValue (value := value) valueFree, native, values, needs, env, refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.returnValue value).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive _ outcome (readComputation primitive (.returnValue value) native env refs).1 := by
          intro world fresh outcome final derivation
          cases derivation
          exact fun store branch =>
            ⟨_, List.mem_singleton_self _, fundamental_valueF valueFree native values needs env refs related valuesOk⟩
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .call operation argument, native, values, needs, env, refs, _, _ => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.call (Head := Head) (Effect := Effect) (k := _) (scope := _)
              operation argument).erase, native, values, needs⟩ world outcome final →
              GoodF primitive _ outcome (readComputation primitive (.call operation argument) native env refs).1 := by
          intro world fresh outcome final derivation
          cases derivation
          intro store branch
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          generalize primitive operation (subst native argument) = produced
          cases produced with
          | value term => rfl
          | stableFault fault => rfl
          | retryableFault reason => cases reason <;> rfl
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .emit effect (next := next) nextFree, native, values, needs, env, refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.emit effect next).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive shape outcome (readComputation primitive (.emit effect next) native env refs).1 := by
          intro world fresh outcome final derivation
          cases derivation with
          | emit _ nextDerivation =>
              intro store branch
              exact GoodFromF.bind primitive shape _ _ ⟨⟨branch, (), store, [effect]⟩, List.mem_singleton_self _,
                (fundamental_computationF nextFree native values needs env refs related valuesOk).1 _
                  (fresh.record _) _ _ nextDerivation store branch⟩
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .nativeLambda (body := body) bodyFree, native, values, needs, env, refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.nativeLambda body).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive _ outcome (readComputation primitive (.nativeLambda body) native env refs).1 := by
          intro world fresh outcome final derivation
          cases derivation
          intro store branch argument world' fresh' outcome' final' bodyDerivation
          exact (fundamental_computationF bodyFree (Fin.cases (motive := fun _ => Tm Head m) argument native) values
            needs env refs related valuesOk).1 _ fresh' _ _ bodyDerivation store branch
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .nativeApply (function := function) argument functionFree, native, values, needs, env, refs,
        related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.nativeApply function argument).erase, native, values, needs⟩
              world outcome final →
              GoodF primitive shape outcome
                (readComputation primitive (.nativeApply function argument) native env refs).1 := by
          intro world fresh outcome final derivation
          have functionGood := (fundamental_computationF functionFree native values needs env refs related valuesOk).1
          cases derivation with
          | nativeApply _ functionDerivation bodyDerivation =>
              intro store branch
              obtain ⟨landed, _⟩ :=
                eval_clean primitive functionDerivation fresh ⟨rawNeedFree_erase functionFree, valuesOk⟩
              exact functionGood _ fresh _ _ functionDerivation store branch (subst native argument) _ landed.fresh _ _
                bodyDerivation
          | nativeApplyMismatch _ functionDerivation notFunction =>
              rename_i answer
              have atArgument := functionGood _ fresh _ _ functionDerivation [] [] (subst native argument)
              exfalso
              revert atArgument
              cases answer with
              | nativeFunction body => exact absurd rfl (notFunction body)
              | returned _ => exact id
              | valueFunction _ => exact id
          | nativeApplyFault _ functionDerivation fault =>
              intro store branch
              have atArgument := functionGood _ fresh _ _ functionDerivation store branch (subst native argument)
              cases fault <;> exact atArgument
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .valueLambda (domain := domain) (body := body) bodyFree, native, values, needs, env, refs, related,
        valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.valueLambda body).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive _ outcome (readComputation primitive (.valueLambda body) native env refs).1 := by
          intro world fresh outcome final derivation
          cases derivation
          intro store branch argument semantic relatedArgument argumentOk world' fresh' outcome' final' bodyDerivation
          exact (fundamental_computationF bodyFree native
            (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) argument values) needs
            (SemEnv.cons semantic env) refs (related.cons primitive relatedArgument)
            (cases_needFree argumentOk valuesOk)).1 _ fresh' _ _ bodyDerivation store branch
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .valueApply (function := function) (argument := argument) functionFree argumentFree,
        native, values, needs, env, refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.valueApply function argument).erase, native, values, needs⟩
              world outcome final →
              GoodF primitive shape outcome
                (readComputation primitive (.valueApply function argument) native env refs).1 := by
          intro world fresh outcome final derivation
          have functionGood := (fundamental_computationF functionFree native values needs env refs related valuesOk).1
          have argumentRelated := fundamental_valueF argumentFree native values needs env refs related valuesOk
          have argumentOk := capture_needFree (native := native) (needs := needs) valuesOk
            (rawValueNeedFree_erase argumentFree)
          cases derivation with
          | valueApply _ functionDerivation bodyDerivation =>
              intro store branch
              obtain ⟨landed, _⟩ :=
                eval_clean primitive functionDerivation fresh ⟨rawNeedFree_erase functionFree, valuesOk⟩
              exact functionGood _ fresh _ _ functionDerivation store branch _ _ argumentRelated argumentOk _
                landed.fresh _ _ bodyDerivation
          | valueApplyMismatch _ functionDerivation notFunction =>
              rename_i answer
              have atArgument := functionGood _ fresh _ _ functionDerivation [] [] _ _ argumentRelated argumentOk
              exfalso
              revert atArgument
              cases answer with
              | valueFunction body => exact absurd rfl (notFunction body)
              | returned _ => exact id
              | nativeFunction _ => exact id
          | valueApplyFault _ functionDerivation fault =>
              intro store branch
              have atArgument := functionGood _ fresh _ _ functionDerivation store branch _ _ argumentRelated argumentOk
              cases fault <;> exact atArgument
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .forceThunk (value := value) valueFree, native, values, needs, env, refs, related, valuesOk =>
        by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.forceThunk value).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive shape outcome (readComputation primitive (.forceThunk value) native env refs).1 := by
          intro world fresh outcome final derivation
          obtain ⟨_, _, _, code, native', values', needs', captured, thunkGood⟩ :=
            fundamental_valueF valueFree native values needs env refs related valuesOk
          cases derivation with
          | forceThunk _ captured' thunkDerivation =>
              rw [captured] at captured'
              cases captured'
              exact thunkGood _ fresh _ _ thunkDerivation
          | forceThunkMismatch _ _ notThunk => exact absurd captured (notThunk _ _ _ _ _ _ _)
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .unpackNative (payload := payload) (value := value) (body := body) valueFree bodyFree, native,
        values, needs, env, refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.unpackNative value body).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive shape outcome (readComputation primitive (.unpackNative value body) native env refs).1 := by
          intro world fresh outcome final derivation
          obtain ⟨inner, captured, innerRelated⟩ :=
            fundamental_valueF valueFree native values needs env refs related valuesOk
          have packOk := capture_needFree (native := native) (needs := needs) valuesOk (rawValueNeedFree_erase valueFree)
          rw [captured] at packOk
          cases packOk with
          | packNative _ innerOk =>
              cases derivation with
              | unpackNative _ captured' bodyDerivation =>
                  rw [captured] at captured'
                  cases captured'
                  exact (fundamental_computationF bodyFree _ _ needs
                    (SemEnv.cons (readValue primitive value native env refs).2 env) refs
                    (related.cons primitive innerRelated) (cases_needFree innerOk valuesOk)).1 _ fresh _ _
                      bodyDerivation
              | unpackNativeMismatch _ _ _ notPackage => exact absurd captured (notPackage _ _)
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .bindNative (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.bindNative first body).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive shape outcome (readComputation primitive (.bindNative first body) native env refs).1 := by
          intro world fresh outcome final derivation
          have producer := (fundamental_computationF firstFree native values needs env refs related valuesOk).2
          have firstOk : ClosureNeedFree ⟨_, _, _, first.erase, native, values, needs⟩ :=
            ⟨rawNeedFree_erase firstFree, valuesOk⟩
          cases derivation with
          | bindNativeValue allocated forced bodyDerivation =>
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              obtain ⟨landed, _⟩ :=
                force_clean primitive forced (fresh.allocated allocated) _ (allocated_suspended allocated) firstOk
              have bodyGood := (fundamental_computationF bodyFree _ values needs env refs related valuesOk).1 _
                landed.fresh _ _ bodyDerivation
              intro store branch
              refine GoodFromF.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              obtain ⟨result, member, agrees⟩ := firstGood (store ++ [none]) branch
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFromF.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases result.answer with
              | value semantic =>
                  intro agrees
                  simp only [RelValueF] at agrees
                  injection agrees with agrees
                  subst agrees
                  exact bodyGood _ _
              | stableFault _ => intro agrees; exact agrees.elim
              | retryableFault _ => intro agrees; exact agrees.elim
          | bindNativeMismatch _ allocated forced notNative =>
              rename_i answer
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              obtain ⟨result, _, agrees⟩ := firstGood [] []
              exfalso
              revert agrees
              cases answer with
              | returned returned =>
                  cases result.answer with
                  | value semantic =>
                      intro agrees
                      simp only [RelValueF] at agrees
                      exact notNative semantic (by rw [agrees])
                  | stableFault _ => intro agrees; exact agrees
                  | retryableFault _ => intro agrees; exact agrees
              | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees
              | valueFunction _ => intro agrees; cases result.answer <;> exact agrees
          | bindNativeFault _ allocated forced fault =>
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              intro store branch
              refine GoodFromF.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              obtain ⟨result, member, agrees⟩ := firstGood (store ++ [none]) branch
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFromF.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases fault with
              | stableFault fault =>
                  cases result.answer with
                  | stableFault fault' => intro agrees; subst agrees; exact GoodFromF.failStable primitive shape fault
                  | value _ => intro agrees; exact agrees.elim
                  | retryableFault _ => intro agrees; exact agrees.elim
              | retryableFault reason =>
                  cases result.answer with
                  | retryableFault reason' =>
                      intro agrees; subst agrees; exact GoodFromF.failRetry primitive shape reason'
                  | value _ => intro agrees; exact agrees.elim
                  | stableFault _ => intro agrees; exact agrees.elim
          | bindNativeAllocationFailure _ failed => exact absurd failed (fresh.allocate_ne_none _)
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .bindValue (bound := bound) (first := first) (body := body) firstFree bodyFree, native, values,
        needs, env, refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.bindValue first body).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive shape outcome (readComputation primitive (.bindValue first body) native env refs).1 := by
          intro world fresh outcome final derivation
          have producer := (fundamental_computationF firstFree native values needs env refs related valuesOk).2
          have firstOk : ClosureNeedFree ⟨_, _, _, first.erase, native, values, needs⟩ :=
            ⟨rawNeedFree_erase firstFree, valuesOk⟩
          cases derivation with
          | bindValueValue allocated forced bodyDerivation =>
              rename_i value
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              obtain ⟨landed, valueOk⟩ :=
                force_clean primitive forced (fresh.allocated allocated) _ (allocated_suspended allocated) firstOk
              intro store branch
              refine GoodFromF.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              obtain ⟨result, member, agrees⟩ := firstGood (store ++ [none]) branch
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world _ _ store branch member
              refine GoodFromF.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases result.answer with
              | value semantic =>
                  intro agrees
                  exact (fundamental_computationF bodyFree native
                    (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) needs
                    (SemEnv.cons semantic env) refs (related.cons primitive agrees)
                    (cases_needFree valueOk valuesOk)).1 _ landed.fresh _ _ bodyDerivation _ _
              | stableFault _ => intro agrees; exact agrees.elim
              | retryableFault _ => intro agrees; exact agrees.elim
          | bindValueMismatch _ allocated forced notReturned =>
              rename_i answer
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              obtain ⟨result, _, agrees⟩ := firstGood [] []
              exfalso
              revert agrees
              cases answer with
              | returned value => exact absurd rfl (notReturned value)
              | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees
              | valueFunction _ => intro agrees; cases result.answer <;> exact agrees
          | bindValueFault _ allocated forced fault =>
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              intro store branch
              refine GoodFromF.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              obtain ⟨result, member, agrees⟩ := firstGood (store ++ [none]) branch
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world _ _ store branch member
              refine GoodFromF.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases fault with
              | stableFault fault =>
                  cases result.answer with
                  | stableFault fault' => intro agrees; subst agrees; exact GoodFromF.failStable primitive shape fault
                  | value _ => intro agrees; exact agrees.elim
                  | retryableFault _ => intro agrees; exact agrees.elim
              | retryableFault reason =>
                  cases result.answer with
                  | retryableFault reason' =>
                      intro agrees; subst agrees; exact GoodFromF.failRetry primitive shape reason'
                  | value _ => intro agrees; exact agrees.elim
                  | stableFault _ => intro agrees; exact agrees.elim
          | bindValueAllocationFailure _ failed => exact absurd failed (fresh.allocate_ne_none _)
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .sequenceSigma (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, related, valuesOk => by
        have good : ∀ world, Fresh world → ∀ outcome final,
            Eval primitive ⟨_, _, _, (Shaped.Computation.sequenceSigma first body).erase, native, values, needs⟩ world
              outcome final →
              GoodF primitive (.returns .native) outcome
                (readComputation primitive (.sequenceSigma first body) native env refs).1 := by
          intro world fresh outcome final derivation
          have producer := (fundamental_computationF firstFree native values needs env refs related valuesOk).2
          have firstOk : ClosureNeedFree ⟨_, _, _, first.erase, native, values, needs⟩ :=
            ⟨rawNeedFree_erase firstFree, valuesOk⟩
          cases derivation with
          | sequenceSigmaValue allocated forced bodyDerivation =>
              rename_i value bodyOutcome
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              obtain ⟨landed, _⟩ :=
                force_clean primitive forced (fresh.allocated allocated) _ (allocated_suspended allocated) firstOk
              have bodyGood := (fundamental_computationF bodyFree _ values needs env refs related valuesOk).1 _
                landed.fresh _ _ bodyDerivation
              intro store branch
              refine GoodFromF.bind primitive (.returns .native) _ _ ⟨_, alloc_world store branch, ?_⟩
              obtain ⟨result, member, agrees⟩ := firstGood (store ++ [none]) branch
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFromF.bind primitive (.returns .native) _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases result.answer with
              | value semantic =>
                  intro agrees
                  simp only [RelValueF] at agrees
                  injection agrees with agrees
                  subst agrees
                  obtain ⟨second, secondMember, secondAgrees⟩ := bodyGood prior.state prior.branch
                  obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := second
                  refine ⟨WorldResult.prependIntents intents₂
                    ⟨branch₂, ScopedNeedNaturalSemantics.pairOutcome value answer₂, state₂, []⟩,
                    ScopedNeed.mem_bind secondMember (List.mem_singleton_self _), ?_⟩
                  revert secondAgrees
                  cases bodyOutcome with
                  | value bodyAnswer =>
                      cases bodyAnswer with
                      | returned returned =>
                          cases answer₂ with
                          | value term =>
                              intro secondAgrees
                              simp only [RelValueF] at secondAgrees
                              subst secondAgrees
                              rfl
                          | stableFault _ => exact False.elim
                          | retryableFault _ => exact False.elim
                      | nativeFunction _ => intro secondAgrees; cases answer₂ <;> exact secondAgrees.elim
                      | valueFunction _ => intro secondAgrees; cases answer₂ <;> exact secondAgrees.elim
                  | stableFault _ =>
                      cases answer₂ with
                      | stableFault _ => exact id
                      | value _ => exact False.elim
                      | retryableFault _ => exact False.elim
                  | retryableFault _ =>
                      cases answer₂ with
                      | retryableFault _ => exact id
                      | value _ => exact False.elim
                      | stableFault _ => exact False.elim
              | stableFault _ => intro agrees; exact agrees.elim
              | retryableFault _ => intro agrees; exact agrees.elim
          | sequenceSigmaMismatch _ allocated forced notNative =>
              rename_i answer
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              obtain ⟨result, _, agrees⟩ := firstGood [] []
              exfalso
              revert agrees
              cases answer with
              | returned returned =>
                  cases result.answer with
                  | value semantic =>
                      intro agrees
                      simp only [RelValueF] at agrees
                      exact notNative semantic (by rw [agrees])
                  | stableFault _ => intro agrees; exact agrees
                  | retryableFault _ => intro agrees; exact agrees
              | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees
              | valueFunction _ => intro agrees; cases result.answer <;> exact agrees
          | sequenceSigmaFault _ allocated forced fault =>
              have firstGood := forced_goodF primitive firstOk producer fresh allocated forced
              intro store branch
              refine GoodFromF.bind primitive (.returns .native) _ _ ⟨_, alloc_world store branch, ?_⟩
              obtain ⟨result, member, agrees⟩ := firstGood (store ++ [none]) branch
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFromF.bind primitive (.returns .native) _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases fault with
              | stableFault fault =>
                  cases result.answer with
                  | stableFault fault' => intro agrees; subst agrees; exact GoodFromF.failStable primitive _ fault
                  | value _ => intro agrees; exact agrees.elim
                  | retryableFault _ => intro agrees; exact agrees.elim
              | retryableFault reason =>
                  cases result.answer with
                  | retryableFault reason' =>
                      intro agrees; subst agrees; exact GoodFromF.failRetry primitive _ reason'
                  | value _ => intro agrees; exact agrees.elim
                  | stableFault _ => intro agrees; exact agrees.elim
          | sequenceSigmaAllocationFailure _ failed => exact absurd failed (fresh.allocate_ne_none _)
        exact ⟨good, entry_onlyF primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .choose (left := left) (right := right) leftFree rightFree, native, values, needs, env, refs,
        related, valuesOk => by
        have leftGood := (fundamental_computationF leftFree native values needs env refs related valuesOk).1
        have rightGood := (fundamental_computationF rightFree native values needs env refs related valuesOk).1
        have closureOk : ClosureNeedFree ⟨_, _, _, (Shaped.Computation.choose left right).erase, native, values, needs⟩ :=
          ⟨rawNeedFree_erase (.choose leftFree rightFree), valuesOk⟩
        have selectedGood : ∀ position rule selected,
            Selection ⟨_, _, _, (Shaped.Computation.choose left right).erase, native, values, needs⟩ position rule
              selected →
              ∀ world, Fresh world → ∀ outcome final, Eval primitive selected world outcome final →
                GoodF primitive shape outcome (readComputation primitive (.choose left right) native env refs).2 := by
          intro position rule selected selection world fresh outcome final derivation
          cases selection with
          | entry notChoice => exact absurd rfl (notChoice _ _)
          | left => exact GoodF.chooseLeft primitive (leftGood _ fresh _ _ derivation)
          | right => exact GoodF.chooseRight primitive (rightGood _ fresh _ _ derivation)
        refine ⟨?_, selectedGood⟩
        intro world fresh outcome final derivation
        cases derivation with
        | choose _ _ allocated forced =>
            have producerGood := forced_goodF primitive closureOk selectedGood fresh allocated forced
            intro store branch
            refine GoodFromF.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
            cases shape with
            | returns answer =>
                obtain ⟨result, member, agrees⟩ := producerGood (store ++ [none]) branch
                obtain ⟨prior, priorMember, sameAnswer⟩ := cellAt_world answer _ store branch member
                exact ⟨prior, priorMember, sameAnswer ▸ agrees⟩
            | nativePi shape => exact producerGood (store ++ [none]) branch
            | arrow domain shape => exact producerGood (store ++ [none]) branch
        | chooseAllocationFailure _ _ failed => exact absurd failed (fresh.allocate_ne_none _)
end

/-- **From a fresh heap, every natural outcome is an answer of the reading**:
for a closed native returner without need cells, with every primitive and no
outcome excluded. -/
theorem fresh_sound {computation : Shaped.Computation Head Operation Effect 0 [] 0 (.returns .native)}
    (needFree : computation.NeedFree) (native : Sub Head 0 m)
    {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    (fresh : Fresh world)
    (derivation : Eval primitive ⟨0, 0, 0, computation.erase, native, Fin.elim0, Fin.elim0⟩ world outcome final) :
    ∃ answer ∈ answers primitive computation native, outcome = PolarizedNeedEmbedding.outcome answer := by
  obtain ⟨result, member, agrees⟩ := (fundamental_computationF primitive needFree native Fin.elim0 Fin.elim0
    SemEnv.empty Fin.elim0 (fun _ index => nomatch index) (fun index => index.elim0)).1 world fresh outcome final
    derivation [] []
  refine ⟨result.answer, List.mem_map.mpr ⟨result, member, rfl⟩, ?_⟩
  revert agrees
  cases outcome with
  | value answer =>
      cases answer with
      | returned value =>
          cases result.answer with
          | value term => intro agrees; simp only [RelValueF] at agrees; subst agrees; rfl
          | stableFault _ => intro agrees; exact agrees.elim
          | retryableFault _ => intro agrees; exact agrees.elim
      | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees.elim
      | valueFunction _ => intro agrees; cases result.answer <;> exact agrees.elim
  | stableFault fault =>
      cases result.answer with
      | value _ => intro agrees; exact agrees.elim
      | stableFault _ => intro agrees; subst agrees; rfl
      | retryableFault _ => intro agrees; exact agrees.elim
  | retryableFault reason =>
      cases result.answer with
      | value _ => intro agrees; exact agrees.elim
      | stableFault _ => intro agrees; exact agrees.elim
      | retryableFault _ => intro agrees; subst agrees; rfl

#print axioms eval_clean
#print axioms fundamental_computationF
#print axioms fresh_sound

/-! ## Examples -/

namespace Examples

open Shaped
open ScopedNeedNaturalSemantics.Examples (ExampleOperation)
open PolarizedValues.Examples (examplePrimitive thunkedCoin thunkedCoin_needFree thunkedCoin_answers collidingWorld
  raised_necessary)

/-- The empty world of the need machine. -/
def emptyWorld : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0 :=
  { lineage := 0, path := [], heap := .empty, receipts := .empty, nextCell := 0, nextEvaluator := 0 }

theorem emptyWorld_fresh : Fresh emptyWorld := Fresh.empty _ (fun _ => rfl)

/-- **Positive: from the empty heap a thunk of a choice, forced twice,
answers one of the four pairs**, with no outcome excluded. -/
theorem thunkedCoin_fresh {outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0}
    {final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    (derivation : Eval examplePrimitive ⟨0, 0, 0, thunkedCoin.erase, ids, Fin.elim0, Fin.elim0⟩ emptyWorld
      outcome final) :
    outcome ∈ ([.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
      .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] :
        List (ScopedNeedMachine.Outcome Nat Nat Nat 0)).map PolarizedNeedEmbedding.outcome := by
  obtain ⟨answer, member, equal⟩ :=
    fresh_sound examplePrimitive thunkedCoin_needFree ids emptyWorld_fresh derivation
  rw [thunkedCoin_answers] at member
  exact List.mem_map.mpr ⟨answer, member, equal.symm⟩

/-- **From the empty heap a derivation of the thunked choice lands**, and its
answer has no need cells. -/
theorem thunkedCoin_lands {outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0}
    {final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    (derivation : Eval examplePrimitive ⟨0, 0, 0, thunkedCoin.erase, ids, Fin.elim0, Fin.elim0⟩ emptyWorld
      outcome final) :
    Lands emptyWorld final ∧ OutcomeNeedFree outcome :=
  eval_clean examplePrimitive derivation emptyWorld_fresh ⟨rawNeedFree_erase thunkedCoin_needFree, fun index => index.elim0⟩

/-- **Negative: the colliding world of `raised_necessary` is not fresh**: it
holds the cell its next allocation would create, so freshness is exactly
what rules that counterexample out. -/
theorem collidingWorld_not_fresh : ¬ Fresh collidingWorld := by
  intro fresh
  exact Nat.lt_irrefl 0 ((fresh ⟨0, [], 0, 0⟩ _ rfl rfl).2 rfl)

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.PolarizedFresh
