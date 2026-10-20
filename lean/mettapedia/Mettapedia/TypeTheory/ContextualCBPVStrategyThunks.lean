import Mettapedia.TypeTheory.ContextualCBPVStrategyElaboration
import Mettapedia.TypeTheory.ContextualCBPVPolarizedComplete

/-!
# Name binders through thunks, equivalent to inlining

`ContextualCBPVStrategyElaboration` elaborates a name binder by inlining its
producer at every use.  PolarizedNeed's value layer has first-class thunks, so
a name binder can instead bind a thunk of its producer, by a value lambda
applied to the thunk, and every use forces it (`elaborateThunks`).  Value
binders sequence and need binders allocate a need cell, as before.

**Equivalence.**  The two elaborations have the same answers
(`thunks_answers`).  Their programs differ: a forced thunk of a choice
allocates the choice's own cell, which an inlined choice, selected at the
cell of its binder, does not.  The proof is a logical relation between runs
over stores related by a renaming of cells (`StoreRel`, `RunRel`): the cells
of the inlined code map into those of the thunk code, and the thunk code's
extra cells are demanded once, at their allocation, and never again.  The
relation is preserved by every operation of the reading (`RunRel.bind`,
`RunRel.alloc`, `RunRel.demand`, `RunRel.allocExtra`), and the thunk
elaboration is related to the strategy semantics `denote` program by program
(`thunks_related`).

**On the machines.**  Without need binders, the thunk elaboration has no
need cells, so its natural outcomes on PolarizedNeed's machine, from a fresh
heap, are the natural outcomes of the inlined code on the scoped-need machine
(`thunks_natural`), through `PolarizedComplete.needFree_agreement` and
`ScopedNeed.closed_agreement`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.StrategyThunks

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ScopedNeed (Strategy Annotated)
open ScopedNeed.Strategy (values needs names Place locate)
open PolarizedValues

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-! ## The thunk elaboration -/

/-- The value scope of the thunk elaboration: a thunk for every name binder. -/
def thunkScope : List Strategy → List VShape
  | [] => []
  | .value :: rest => thunkScope rest
  | .need :: rest => thunkScope rest
  | .name :: rest => .thunk (.returns .native) :: thunkScope rest

/-- The thunk variable of a name variable. -/
def thunkMember : (scope : List Strategy) → Fin (names scope) → Member (thunkScope scope) (.thunk (.returns .native))
  | [], index => index.elim0
  | .value :: rest, index => thunkMember rest index
  | .need :: rest, index => thunkMember rest index
  | .name :: rest, index => Fin.cases .zero (fun j => .succ (thunkMember rest j)) index

/-- **The thunk elaboration.**  A value binder sequences, a need binder
allocates a need cell, and a name binder applies a value lambda to a thunk
of its producer, which every use forces. -/
def elaborateThunks : {scope : List Strategy} → Annotated Head Operation Effect scope →
    Shaped.Computation Head Operation Effect (values scope) (thunkScope scope) (needs scope) (.returns .native)
  | _, .ret term => .returnValue (.native term)
  | _, .call operation argument => .call operation argument
  | _, .emit effect next => .emit effect (elaborateThunks next)
  | _, .choose left right => .choose (elaborateThunks left) (elaborateThunks right)
  | scope, .use position =>
      match locate scope position with
      | .native index => .returnValue (.native (.var index))
      | .reference index => .forceNeed index
      | .producer index => .forceThunk (.var (thunkMember scope index))
  | _, .bind .value bound body => .bindNative (elaborateThunks bound) (elaborateThunks body)
  | _, .bind .need bound body => .letNeed (elaborateThunks bound) (elaborateThunks body)
  | _, .bind .name bound body => .valueApply (.valueLambda (elaborateThunks body)) (.thunk (elaborateThunks bound))
  | _, .pair first body => .sequenceSigma (elaborateThunks first) (elaborateThunks body)

/-! ## Runs over renamed stores -/

/-- The cells of a store `store'` renamed into a store `store`: the cell at
position `index` of `store'` is the cell `cells[index]` of `store`, with the
same cache; the other cells of `store` are extra. -/
def StoreRel (cells : List Nat) (store store' : ScopedNeed.Store Head StableFault NativeFault m) : Prop :=
  cells.length = store'.length ∧ cells.Nodup ∧
    ∀ index (bound : index < cells.length),
      cells[index] < store.length ∧ store'.getD index none = store.getD cells[index] none

/-- Two worlds agree: the same branch and answer, and stores related by a
renaming that extends `cells` by cells no older than `store`. -/
def WorldRel (cells : List Nat) (store : ScopedNeed.Store Head StableFault NativeFault m)
    (world world' : WorldResult (ScopedNeed.Store Head StableFault NativeFault m) (ScopedNeed.Outcome Head StableFault NativeFault m)
      Effect) : Prop :=
  world.branch = world'.branch ∧ world.answer = world'.answer ∧ store.length ≤ world.state.length ∧
    ∃ more : List Nat, StoreRel (cells ++ more) world.state world'.state ∧ ∀ cell ∈ more, store.length ≤ cell

/-- **Two runs agree** under a renaming of cells, and under every extension
of it: from related stores, their worlds agree in order. -/
def RunRel (cells : List Nat) (run run' : ScopedNeed.Run Head Effect StableFault NativeFault m) : Prop :=
  ∀ (more : List Nat) (store store' : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace),
    StoreRel (cells ++ more) store store' →
      List.Forall₂ (WorldRel (cells ++ more) store) (runWorldsAt run store branch) (runWorldsAt run' store' branch)

/-- Two references agree: renamed cells and agreeing producers. -/
def RefRel (cells : List Nat) (ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m) : Prop :=
  ∃ bound : ref'.1 < cells.length, cells[ref'.1] = ref.1 ∧ RunRel cells ref.2 ref'.2

theorem StoreRel.lt {cells : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (related : StoreRel cells store store') {cell : Nat} (member : cell ∈ cells) : cell < store.length := by
  obtain ⟨index, bound, rfl⟩ := List.getElem_of_mem member
  exact (related.2.2 index bound).1

theorem StoreRel.getD {cells : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (related : StoreRel cells store store') {cell : Nat} (bound : cell < cells.length) :
    store'.getD cell none = store.getD cells[cell] none :=
  (related.2.2 cell bound).2

theorem RunRel.mono {cells : List Nat} {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (related : RunRel cells run run') (extra : List Nat) : RunRel (cells ++ extra) run run' := by
  intro more store store' branch storeRel
  rw [List.append_assoc] at storeRel ⊢
  exact related (extra ++ more) store store' branch storeRel

theorem RefRel.mono {cells : List Nat} {ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m}
    (related : RefRel cells ref ref') (extra : List Nat) : RefRel (cells ++ extra) ref ref' := by
  obtain ⟨bound, located, runs⟩ := related
  refine ⟨by rw [List.length_append]; omega, ?_, runs.mono extra⟩
  rw [List.getElem_append_left bound]
  exact located

theorem WorldRel.prepend {cells : List Nat} {store : ScopedNeed.Store Head StableFault NativeFault m}
    {world world' : WorldResult (ScopedNeed.Store Head StableFault NativeFault m) (ScopedNeed.Outcome Head StableFault NativeFault m)
      Effect} (related : WorldRel cells store world world') (intents intents' : List Effect) :
    WorldRel cells store (WorldResult.prependIntents intents world) (WorldResult.prependIntents intents' world') :=
  related

theorem RunRel.pure (cells : List Nat) (answer : ScopedNeed.Outcome Head StableFault NativeFault m) :
    RunRel (Effect := Effect) cells (.pure answer) (.pure answer) := by
  intro more store store' branch storeRel
  exact .cons ⟨rfl, rfl, le_rfl, [], by rw [List.append_nil]; exact storeRel, fun _ member => nomatch member⟩ .nil

theorem RunRel.bind {cells : List Nat} {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    {next next' : ScopedNeed.Outcome Head StableFault NativeFault m → ScopedNeed.Run Head Effect StableFault NativeFault m}
    (first : RunRel cells run run') (continued : ∀ answer, RunRel cells (next answer) (next' answer)) :
    RunRel cells (run.bind next) (run'.bind next') := by
  intro more store store' branch storeRel
  rw [runWorldsAt_bind, runWorldsAt_bind]
  refine List.rel_flatMap (first more store store' branch storeRel) ?_
  rintro world world' ⟨sameBranch, sameAnswer, longer, more', storeRel', fresher⟩
  dsimp only
  rw [← sameBranch, ← sameAnswer]
  rw [List.append_assoc] at storeRel'
  have inner := (continued world.answer) (more ++ more') world.state world'.state world.branch storeRel'
  refine List.rel_map (fun {inner inner'} related => ?_) inner
  obtain ⟨sameBranch', sameAnswer', longer', more'', storeRel'', fresher'⟩ := related
  refine ⟨sameBranch', sameAnswer', le_trans longer longer', more' ++ more'', ?_, ?_⟩
  · simp only [List.append_assoc] at storeRel'' ⊢
    exact storeRel''
  · intro cell member
    rcases List.mem_append.mp member with member | member
    · exact fresher cell member
    · exact le_trans longer (fresher' cell member)

theorem RunRel.choose {cells : List Nat} {left left' right right' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (leftRel : RunRel cells left left') (rightRel : RunRel cells right right') :
    RunRel cells (.choose left right) (.choose left' right') := by
  intro more store store' branch storeRel
  exact List.rel_append (leftRel more store store' (false :: branch) storeRel)
    (rightRel more store store' (true :: branch) storeRel)

theorem RunRel.intent {cells : List Nat} {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m} (effect : Effect)
    (related : RunRel cells run run') : RunRel cells (.intent effect run) (.intent effect run') := by
  intro more store store' branch storeRel
  simp only [runWorldsAt]
  refine List.rel_map ?_ (related more store store' branch storeRel)
  intro world world' worldRel
  exact worldRel

theorem RunRel.map {cells : List Nat} {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (function : ScopedNeed.Outcome Head StableFault NativeFault m → ScopedNeed.Outcome Head StableFault NativeFault m)
    (related : RunRel cells run run') : RunRel cells (Program.map function run) (Program.map function run') :=
  related.bind fun answer => RunRel.pure cells (function answer)

theorem StoreRel.alloc {cells : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (related : StoreRel cells store store') :
    StoreRel (cells ++ [store.length]) (store ++ [none]) (store' ++ [none]) := by
  obtain ⟨length, nodup, entries⟩ := related
  refine ⟨by simp [length], ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨nodup, List.nodup_singleton _, ?_⟩
    intro cell member other otherMember equal
    rw [List.mem_singleton] at otherMember
    subst otherMember
    subst equal
    exact absurd (StoreRel.lt ⟨length, nodup, entries⟩ member) (lt_irrefl _)
  · intro index bound
    rw [List.length_append, List.length_singleton] at bound
    by_cases old : index < cells.length
    · rw [List.getElem_append_left old]
      obtain ⟨entryBound, agrees⟩ := entries index old
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append _ _ _ _ (length ▸ old), List.getD_append _ _ _ _ entryBound]
      exact agrees
    · have equal : index = cells.length := by omega
      subst equal
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      refine ⟨by rw [List.length_append]; simp, ?_⟩
      rw [length, List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (le_refl _)]
      simp

theorem StoreRel.extra {cells : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (related : StoreRel cells store store') : StoreRel cells (store ++ [none]) store' := by
  obtain ⟨length, nodup, entries⟩ := related
  refine ⟨length, nodup, fun index bound => ?_⟩
  obtain ⟨entryBound, agrees⟩ := entries index bound
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [List.getD_append _ _ _ _ entryBound]
  exact agrees

theorem StoreRel.settleExtra {cells : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (related : StoreRel cells store store') {cell : Nat} (absent : cell ∉ cells)
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    StoreRel cells (ScopedNeed.settled cell outcome store) store' := by
  obtain ⟨length, nodup, entries⟩ := related
  refine ⟨length, nodup, fun index bound => ?_⟩
  obtain ⟨entryBound, agrees⟩ := entries index bound
  have different : cells[index] ≠ cell := fun equal => absent (equal ▸ List.getElem_mem bound)
  refine ⟨by rw [ScopedNeed.settled_length]; exact entryBound, ?_⟩
  rw [ScopedNeed.settled_other cell _ different]
  exact agrees

theorem StoreRel.settle {cells : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (related : StoreRel cells store store') {cell' : Nat} (bound : cell' < cells.length)
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    StoreRel cells (ScopedNeed.settled cells[cell'] outcome store) (ScopedNeed.settled cell' outcome store') := by
  obtain ⟨length, nodup, entries⟩ := related
  refine ⟨by rw [ScopedNeed.settled_length]; exact length, nodup, fun index indexBound => ?_⟩
  obtain ⟨entryBound, agrees⟩ := entries index indexBound
  refine ⟨by rw [ScopedNeed.settled_length]; exact entryBound, ?_⟩
  by_cases same : index = cell'
  · subst same
    have cellBound : cells[index] < store.length := entryBound
    have storeBound : index < store'.length := length ▸ indexBound
    cases outcome with
    | value value =>
        simp [ScopedNeed.settled, List.getD_eq_getElem?_getD, List.getElem?_set_self storeBound,
          List.getElem?_set_self cellBound]
    | stableFault fault =>
        simp [ScopedNeed.settled, List.getD_eq_getElem?_getD, List.getElem?_set_self storeBound,
          List.getElem?_set_self cellBound]
    | retryableFault reason => exact agrees
  · have different : cells[index] ≠ cells[cell'] := by
      intro equal
      exact same ((List.Nodup.getElem_inj_iff nodup).mp equal)
    rw [ScopedNeed.settled_other _ _ same, ScopedNeed.settled_other _ _ different]
    exact agrees

theorem RunRel.settle {cells : List Nat} {cell' : Nat} (bound : cell' < cells.length)
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    RunRel (Effect := Effect) cells (ScopedNeed.settle cells[cell'] outcome) (ScopedNeed.settle cell' outcome) := by
  intro more store store' branch storeRel
  rw [ScopedNeed.settle_run, ScopedNeed.settle_run]
  have bound' : cell' < (cells ++ more).length := by rw [List.length_append]; omega
  have located : (cells ++ more)[cell'] = cells[cell'] := List.getElem_append_left bound
  have settledRel := storeRel.settle bound' outcome
  rw [located] at settledRel
  exact .cons ⟨rfl, rfl, by rw [ScopedNeed.settled_length], [], by rw [List.append_nil]; exact settledRel,
    fun _ member => nomatch member⟩ .nil

/-- **Demanding agreeing references agrees.** -/
theorem RunRel.demand {cells : List Nat} {ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m}
    (related : RefRel cells ref ref') : RunRel cells (ScopedNeed.demand ref.1 ref.2) (ScopedNeed.demand ref'.1 ref'.2) := by
  obtain ⟨bound, located, runs⟩ := related
  intro more store store' branch storeRel
  have bound' : ref'.1 < (cells ++ more).length := by rw [List.length_append]; omega
  have cached : store'.getD ref'.1 none = store.getD ref.1 none := by
    rw [storeRel.getD bound', List.getElem_append_left bound, located]
  unfold ScopedNeed.demand
  simp only [runWorldsAt]
  rw [cached]
  cases found : store.getD ref.1 none with
  | some outcome =>
      dsimp only
      exact (RunRel.pure (Effect := Effect) cells outcome) more store store' branch storeRel
  | none =>
      dsimp only
      have settleRel : ∀ outcome : ScopedNeed.Outcome Head StableFault NativeFault m, RunRel (Effect := Effect) cells (ScopedNeed.settle ref.1 outcome) (ScopedNeed.settle ref'.1 outcome) := by
        intro outcome
        have := RunRel.settle (Effect := Effect) bound outcome
        rw [located] at this
        exact this
      exact (runs.bind settleRel) more store store' branch storeRel

/-- **Allocating on both sides agrees**, if the continuations agree on the
new cells. -/
theorem RunRel.alloc {cells : List Nat}
    {next next' : Nat → ScopedNeed.Run Head Effect StableFault NativeFault m}
    (continued : ∀ (more : List Nat) (store store' : ScopedNeed.Store Head StableFault NativeFault m),
      StoreRel (cells ++ more) store store' →
        RunRel (cells ++ more ++ [store.length]) (next store.length) (next' store'.length)) :
    RunRel cells (ScopedNeed.alloc next) (ScopedNeed.alloc next') := by
  intro more store store' branch storeRel
  simp only [ScopedNeed.alloc, runWorldsAt]
  have inner := continued more store store' storeRel [] (store ++ [none]) (store' ++ [none]) branch
    (by rw [List.append_nil]; exact storeRel.alloc)
  refine List.Forall₂.imp (fun {world world'} related => ?_) inner
  obtain ⟨sameBranch, sameAnswer, longer, more', storeRel', fresher⟩ := related
  refine ⟨sameBranch, sameAnswer, le_trans (by simp) longer, [store.length] ++ more', ?_, ?_⟩
  · simpa [List.append_assoc] using storeRel'
  · intro cell member
    rcases List.mem_append.mp member with member | member
    · rw [List.mem_singleton] at member
      exact le_of_eq member.symm
    · exact le_trans (by simp) (fresher cell member)

/-- **An extra cell demanded at once agrees with its producer run in place.** -/
theorem RunRel.allocExtra {cells : List Nat} {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (related : RunRel cells run run') : RunRel cells (ScopedNeed.alloc fun cell => ScopedNeed.demand cell run) run' := by
  intro more store store' branch storeRel
  have pending : (store ++ [none]).getD store.length none = none := by simp
  have expand : runWorldsAt (ScopedNeed.alloc fun cell => ScopedNeed.demand cell run) store branch =
      runWorldsAt (run.bind (ScopedNeed.settle store.length)) (store ++ [none]) branch := by
    simp only [ScopedNeed.alloc, runWorldsAt]
    exact ScopedNeed.demand_pending store.length run (store ++ [none]) branch pending
  rw [expand, runWorldsAt_bind]
  have inner := related more (store ++ [none]) store' branch storeRel.extra
  have flat : ∀ worlds : List (WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (ScopedNeed.Outcome Head StableFault NativeFault m) Effect),
      worlds.flatMap (fun prior => (runWorldsAt (ScopedNeed.settle (Effect := Effect) store.length prior.answer) prior.state
          prior.branch).map (WorldResult.prependIntents prior.intents)) =
        worlds.map fun prior => WorldResult.prependIntents prior.intents
          { branch := prior.branch, answer := prior.answer, state := ScopedNeed.settled store.length prior.answer prior.state,
            intents := [] } := by
    intro worlds
    induction worlds with
    | nil => rfl
    | cons prior rest ih =>
        rw [List.flatMap_cons, List.map_cons, ScopedNeed.settle_run, ih]
        rfl
  rw [flat]
  rw [← List.map_id (runWorldsAt run' store' branch)]
  refine List.rel_map (fun {world world'} worldRel => ?_) inner
  obtain ⟨sameBranch, sameAnswer, longer, more', storeRel', fresher⟩ := worldRel
  have absent : store.length ∉ cells ++ more ++ more' := by
    intro member
    rcases List.mem_append.mp member with member | member
    · exact lt_irrefl _ (storeRel.lt member)
    · have := fresher _ member
      simp at this
  refine ⟨sameBranch, sameAnswer, ?_, more', storeRel'.settleExtra absent _, ?_⟩
  · show store.length ≤ (ScopedNeed.settled store.length world.answer world.state).length
    rw [ScopedNeed.settled_length]
    exact le_trans (by simp) longer
  · intro cell member
    exact le_trans (by simp) (fresher cell member)

/-- A cell allocated on both sides is a reference of both, renamed into the
other. -/
theorem RefRel.alloc {cells more : List Nat} {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (storeRel : StoreRel (cells ++ more) store store') {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (related : RunRel cells run run') :
    RefRel (cells ++ more ++ [store.length]) (store.length, run) (store'.length, run') := by
  have length : (cells ++ more).length = store'.length := storeRel.1
  have outside : ¬ store'.length < cells.length := by rw [← length, List.length_append]; omega
  have past : ¬ store'.length - cells.length < more.length := by rw [← length, List.length_append]; omega
  refine ⟨by rw [List.length_append, length]; simp, ?_, (related.mono more).mono [store.length]⟩
  show (cells ++ more ++ [store.length])[store'.length]'(by rw [List.length_append, length]; simp) = store.length
  simp [List.getElem_append, outside, past]

/-! ## The thunk elaboration agrees with the strategy semantics -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

/-- **The thunk elaboration is related to the strategy semantics**, program
for program and producer for producer: under agreeing references, and
thunks that agree with the name variables' programs and producers. -/
theorem thunks_related {scope : List Strategy} (program : Annotated Head Operation Effect scope) :
    ∀ (cells : List Nat)
      (thunks : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) (thunkScope scope))
      (refs : Fin (needs scope) → ScopedNeed.Ref Head Effect StableFault NativeFault m)
      (env : ScopedNeed.Env Head Effect StableFault NativeFault m scope),
      (∀ j, RefRel cells (refs j) (env.references j)) →
      (∀ j, RunRel cells (thunks _ (thunkMember scope j)) (env.producers j).1 ∧
        RunRel cells (thunks _ (thunkMember scope j)) (env.producers j).2) →
      RunRel cells (readComputation primitive (elaborateThunks program) env.native thunks refs).1
          (ScopedNeed.denote primitive program env).1 ∧
        RunRel cells (readComputation primitive (elaborateThunks program) env.native thunks refs).1
          (ScopedNeed.denote primitive program env).2 ∧
        RunRel cells (readComputation primitive (elaborateThunks program) env.native thunks refs).2
          (ScopedNeed.denote primitive program env).2 := by
  induction program with
  | ret term =>
      intro cells thunks refs env _ _
      have h := RunRel.pure (Effect := Effect) cells
        (.value (subst env.native term) : ScopedNeed.Outcome Head StableFault NativeFault m)
      exact ⟨h, h, h⟩
  | call operation argument =>
      intro cells thunks refs env _ _
      have h := RunRel.pure (Effect := Effect) cells
        (ScopedNeedMachine.liftOutcome (primitive operation (subst env.native argument)))
      exact ⟨h, h, h⟩
  | emit effect next ih =>
      intro cells thunks refs env refsRel thunksRel
      obtain ⟨first, _, _⟩ := ih cells thunks refs env refsRel thunksRel
      have h := first.intent effect
      exact ⟨h, h, h⟩
  | choose left right ihLeft ihRight =>
      intro cells thunks refs env refsRel thunksRel
      obtain ⟨leftFirst, _, _⟩ := ihLeft cells thunks refs env refsRel thunksRel
      obtain ⟨rightFirst, _, _⟩ := ihRight cells thunks refs env refsRel thunksRel
      have chosen := RunRel.choose leftFirst rightFirst
      have first := RunRel.alloc (cells := cells)
        (next := fun cell => ScopedNeed.demand cell
          (.choose (readComputation primitive (elaborateThunks left) env.native thunks refs).1
            (readComputation primitive (elaborateThunks right) env.native thunks refs).1))
        (next' := fun cell => ScopedNeed.demand cell
          (.choose (ScopedNeed.denote primitive left env).1 (ScopedNeed.denote primitive right env).1))
        fun more store store' storeRel => RunRel.demand (RefRel.alloc storeRel chosen)
      exact ⟨first, RunRel.allocExtra chosen, chosen⟩
  | @use inner position =>
      intro cells thunks refs env refsRel thunksRel
      simp only [elaborateThunks, ScopedNeed.denote]
      cases locate inner position with
      | native index =>
          have h := RunRel.pure (Effect := Effect) cells
            (.value (env.native index) : ScopedNeed.Outcome Head StableFault NativeFault m)
          exact ⟨h, h, h⟩
      | reference index =>
          have h := RunRel.demand (refsRel index)
          exact ⟨h, h, h⟩
      | producer index => exact ⟨(thunksRel index).1, (thunksRel index).2, (thunksRel index).2⟩
  | @bind inner strategy bound body ihBound ihBody =>
      cases strategy with
      | value =>
          intro cells thunks refs env refsRel thunksRel
          obtain ⟨_, _, boundProducer⟩ := ihBound cells thunks refs env refsRel thunksRel
          have step := RunRel.alloc (cells := cells)
            (next := fun cell => sequenceAt (.returns .native)
              (cellAt .native cell (readComputation primitive (elaborateThunks bound) env.native thunks refs).2)
              fun value => (readComputation primitive (elaborateThunks body) (Fin.cases value env.native) thunks refs).1)
            (next' := fun cell => (ScopedNeed.demand cell (ScopedNeed.denote primitive bound env).2).bind
              (ScopedNeed.onValue fun value => (ScopedNeed.denote primitive body (env.bindValue value)).1))
            fun more store store' storeRel => by
              refine RunRel.bind
                (run := ScopedNeed.demand store.length
                  (readComputation primitive (elaborateThunks bound) env.native thunks refs).2)
                (run' := ScopedNeed.demand store'.length (ScopedNeed.denote primitive bound env).2)
                (RunRel.demand (RefRel.alloc storeRel boundProducer)) ?_
              intro answer
              cases answer with
              | value value =>
                  exact (ihBody _ thunks refs (env.bindValue value)
                    (fun j => ((refsRel j).mono more).mono [store.length])
                    (fun j => ⟨((thunksRel j).1.mono more).mono [store.length],
                      ((thunksRel j).2.mono more).mono [store.length]⟩)).1
              | stableFault fault => exact RunRel.pure _ (.stableFault fault)
              | retryableFault reason => exact RunRel.pure _ (.retryableFault reason)
          exact ⟨step, step, step⟩
      | need =>
          intro cells thunks refs env refsRel thunksRel
          obtain ⟨_, _, boundProducer⟩ := ihBound cells thunks refs env refsRel thunksRel
          have step := RunRel.alloc (cells := cells)
            (next := fun cell => (readComputation primitive (elaborateThunks body) env.native thunks
              (Fin.cases (motive := fun _ => ScopedNeed.Ref Head Effect StableFault NativeFault m)
                (cell, (readComputation primitive (elaborateThunks bound) env.native thunks refs).2) refs)).1)
            (next' := fun cell =>
              (ScopedNeed.denote primitive body (env.bindNeed (cell, (ScopedNeed.denote primitive bound env).2))).1)
            fun more store store' storeRel => by
              refine (ihBody (cells ++ more ++ [store.length]) thunks
                (Fin.cases (motive := fun _ => ScopedNeed.Ref Head Effect StableFault NativeFault m)
                  (store.length, (readComputation primitive (elaborateThunks bound) env.native thunks refs).2) refs)
                (env.bindNeed (store'.length, (ScopedNeed.denote primitive bound env).2)) ?_
                (fun j => ⟨((thunksRel j).1.mono more).mono [store.length],
                  ((thunksRel j).2.mono more).mono [store.length]⟩)).1
              intro j
              refine Fin.cases ?_ (fun j' => ?_) j
              · exact RefRel.alloc storeRel boundProducer
              · exact ((refsRel j').mono more).mono [store.length]
          exact ⟨step, step, step⟩
      | name =>
          intro cells thunks refs env refsRel thunksRel
          obtain ⟨boundFirst, boundSecond, _⟩ := ihBound cells thunks refs env refsRel thunksRel
          obtain ⟨first, second, _⟩ := ihBody cells
            (SemEnv.cons (readComputation primitive (elaborateThunks bound) env.native thunks refs).1 thunks) refs
            (env.bindName (ScopedNeed.denote primitive bound env)) refsRel (fun j => by
              refine Fin.cases ?_ (fun j' => ?_) j
              · exact ⟨boundFirst, boundSecond⟩
              · exact thunksRel j')
          exact ⟨first, second, second⟩
  | @pair inner first body ihFirst ihBody =>
      intro cells thunks refs env refsRel thunksRel
      obtain ⟨_, _, firstProducer⟩ := ihFirst cells thunks refs env refsRel thunksRel
      have step := RunRel.alloc (cells := cells)
        (next := fun cell => sequenceAt (.returns .native)
          (cellAt .native cell (readComputation primitive (elaborateThunks first) env.native thunks refs).2)
          fun value => Program.map (ScopedNeedNaturalSemantics.pairOutcome value)
            (readComputation primitive (elaborateThunks body) (Fin.cases value env.native) thunks refs).1)
        (next' := fun cell => (ScopedNeed.demand cell (ScopedNeed.denote primitive first env).2).bind
          (ScopedNeed.onValue fun value => Program.map (ScopedNeedNaturalSemantics.pairOutcome value)
            (ScopedNeed.denote primitive body (env.bindValue value)).1))
        fun more store store' storeRel => by
          refine RunRel.bind
            (run := ScopedNeed.demand store.length
              (readComputation primitive (elaborateThunks first) env.native thunks refs).2)
            (run' := ScopedNeed.demand store'.length (ScopedNeed.denote primitive first env).2)
            (RunRel.demand (RefRel.alloc storeRel firstProducer)) ?_
          intro answer
          cases answer with
          | value value =>
              exact RunRel.map _ (ihBody _ thunks refs (env.bindValue value)
                (fun j => ((refsRel j).mono more).mono [store.length])
                (fun j => ⟨((thunksRel j).1.mono more).mono [store.length],
                  ((thunksRel j).2.mono more).mono [store.length]⟩)).1
          | stableFault fault => exact RunRel.pure _ (.stableFault fault)
          | retryableFault reason => exact RunRel.pure _ (.retryableFault reason)
      exact ⟨step, step, step⟩

#print axioms thunks_related

theorem answers_of_forall₂ {cells : List Nat} {store : ScopedNeed.Store Head StableFault NativeFault m}
    {worlds worlds' : List (WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (ScopedNeed.Outcome Head StableFault NativeFault m) Effect)}
    (related : List.Forall₂ (WorldRel cells store) worlds worlds') :
    worlds.map WorldResult.answer = worlds'.map WorldResult.answer := by
  induction related with
  | nil => rfl
  | cons head _ ih => rw [List.map_cons, List.map_cons, head.2.1, ih]

/-- **Name binders through thunks are equivalent to inlining**: for a closed
annotated program, the thunk elaboration has the answers of the inlining
elaboration. -/
theorem thunks_answers (program : Annotated Head Operation Effect []) (native : Sub Head 0 m) :
    PolarizedValues.answers (Effect := Effect) primitive (elaborateThunks program) native =
      ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate program Fin.elim0) native := by
  rw [ScopedNeed.elaborate_answers]
  have related := (thunks_related primitive program [] SemEnv.empty Fin.elim0 ⟨native, Fin.elim0, Fin.elim0⟩
    (fun j => j.elim0) (fun j => j.elim0)).1 [] [] [] []
    ⟨rfl, List.nodup_nil, fun _ bound => absurd bound (Nat.not_lt_zero _)⟩
  exact answers_of_forall₂ related

#print axioms thunks_answers

/-! ## On the machines -/

/-- Annotated programs without need binders. -/
inductive NoNeed : {scope : List Strategy} → Annotated Head Operation Effect scope → Prop where
  | ret {scope : List Strategy} (term : Tm Head (values scope)) :
      NoNeed (Annotated.ret (Operation := Operation) (Effect := Effect) term)
  | call {scope : List Strategy} (operation : Operation) (argument : Tm Head (values scope)) :
      NoNeed (Annotated.call (Effect := Effect) operation argument)
  | emit {scope : List Strategy} (effect : Effect) {next : Annotated Head Operation Effect scope} :
      NoNeed next → NoNeed (.emit effect next)
  | choose {scope : List Strategy} {left right : Annotated Head Operation Effect scope} :
      NoNeed left → NoNeed right → NoNeed (.choose left right)
  | use {scope : List Strategy} (position : Fin scope.length) :
      NoNeed (Annotated.use (Head := Head) (Operation := Operation) (Effect := Effect) position)
  | bindValue {scope : List Strategy} {bound : Annotated Head Operation Effect scope}
      {body : Annotated Head Operation Effect (.value :: scope)} :
      NoNeed bound → NoNeed body → NoNeed (.bind .value bound body)
  | bindName {scope : List Strategy} {bound : Annotated Head Operation Effect scope}
      {body : Annotated Head Operation Effect (.name :: scope)} :
      NoNeed bound → NoNeed body → NoNeed (.bind .name bound body)
  | pair {scope : List Strategy} {first : Annotated Head Operation Effect scope}
      {body : Annotated Head Operation Effect (.value :: scope)} :
      NoNeed first → NoNeed body → NoNeed (.pair first body)

/-- Without need binders the thunk elaboration has no need cells. -/
theorem elaborateThunks_needFree {scope : List Strategy} {program : Annotated Head Operation Effect scope}
    (noNeed : NoNeed program) (none : needs scope = 0) : (elaborateThunks program).NeedFree := by
  induction noNeed with
  | ret term => exact .returnValue (.native _)
  | call operation argument => exact .call operation argument
  | emit effect _ ih => exact .emit effect (ih none)
  | choose _ _ ihLeft ihRight => exact .choose (ihLeft none) (ihRight none)
  | @use inner position =>
      simp only [elaborateThunks]
      cases locate inner position with
      | native index => exact .returnValue (.native _)
      | reference index =>
          have bound := index.isLt
          omega
      | producer index => exact .forceThunk (.var _)
  | bindValue _ _ ihBound ihBody => exact .bindNative (ihBound none) (ihBody none)
  | bindName _ _ ihBound ihBody => exact .valueApply (.valueLambda (ihBody none)) (.thunk (ihBound none))
  | pair _ _ ihFirst ihBody => exact .sequenceSigma (ihFirst none) (ihBody none)

/-- Read a fault of PolarizedNeed's machine back as a scoped-need fault. -/
def backFault : PolarizedNeedMachine.Fault NativeFault → ScopedNeedMachine.Fault NativeFault
  | .native fault => .native fault
  | _ => .allocationResumeDemanded

def backRetry : RetryReason (PolarizedNeedMachine.Fault NativeFault) → RetryReason (ScopedNeedMachine.Fault NativeFault)
  | .domain fault => .domain (backFault fault)
  | .blackhole cell => .blackhole cell
  | .outOfScope cell => .outOfScope cell
  | .noRule cell => .noRule cell
  | .ownershipLost cell expected actual => .ownershipLost cell expected actual
  | .allocationCollision cell => .allocationCollision cell

/-- Read an outcome of PolarizedNeed's machine back as a scoped-need
outcome, where it is one. -/
def backOutcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
    Option (ScopedNeedMachine.Outcome Head StableFault NativeFault m)
  | .value (.returned (.native term)) => some (.value term)
  | .value _ => none
  | .stableFault fault => some (.stableFault fault)
  | .retryableFault reason => some (.retryableFault (backRetry reason))

theorem backOutcome_outcome (outcome : ScopedNeedMachine.Outcome Head StableFault NativeFault m) :
    backOutcome (Operation := Operation) (Effect := Effect) (PolarizedNeedEmbedding.outcome outcome) = some outcome := by
  rcases outcome with term | fault | reason
  · rfl
  · rfl
  · cases reason with
    | domain fault => cases fault <;> rfl
    | blackhole _ => rfl
    | outOfScope _ => rfl
    | noRule _ => rfl
    | ownershipLost _ _ _ => rfl
    | allocationCollision _ => rfl

theorem embed_outcome_injective :
    Function.Injective (PolarizedNeedEmbedding.outcome (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m)) := fun first second equal =>
  Option.some.inj ((backOutcome_outcome first).symm.trans ((congrArg backOutcome equal).trans (backOutcome_outcome second)))

/-- **On the two machines, name binders through thunks run like inlining**:
for a closed annotated program without need binders and every primitive,
from fresh heaps, an outcome is natural for the thunk elaboration on
PolarizedNeed's machine exactly when it is natural for the inlined code on the
scoped-need machine. -/
theorem thunks_natural
    (program : Annotated Head Operation Effect []) (noNeed : NoNeed program) (native : Sub Head 0 m)
    {world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (fresh : PolarizedFresh.Fresh world)
    {world' : ScopedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} (fresh' : ScopedNeed.Fresh world')
    (outcome : ScopedNeedMachine.Outcome Head StableFault NativeFault m) :
    (∃ final, Nonempty (PolarizedNeedNaturalSemantics.Eval primitive
        ⟨0, 0, 0, (elaborateThunks program).erase, native, Fin.elim0, Fin.elim0⟩ world
        (PolarizedNeedEmbedding.outcome outcome) final)) ↔
      ∃ final, Nonempty (ScopedNeedNaturalSemantics.Eval primitive
        ⟨0, 0, ScopedNeed.elaborate program Fin.elim0, native, Fin.elim0⟩ world' outcome final) := by
  have polarized := PolarizedComplete.needFree_agreement primitive (computation := elaborateThunks program)
    (elaborateThunks_needFree noNeed rfl) native fresh (PolarizedNeedEmbedding.outcome outcome)
  have inlined := ScopedNeed.closed_agreement primitive (ScopedNeed.elaborate program Fin.elim0) native world' fresh'
    outcome
  rw [List.mem_map_of_injective embed_outcome_injective, thunks_answers] at polarized
  exact polarized.symm.trans inlined

#print axioms thunks_natural

/-! ## Examples -/

namespace Examples

open ScopedNeedNaturalSemantics.Examples (ExampleOperation)
open ScopedNeed.Examples (twice coin examplePrimitive twice_name twice_need)

/-- **Name through thunks**: every force chooses again, as inlining does. -/
theorem twice_name_thunks :
    PolarizedValues.answers (Effect := Nat) examplePrimitive (elaborateThunks (twice .name)) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
       .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] :=
  (thunks_answers examplePrimitive (twice .name) ids).trans twice_name

/-- The relation at the name binder of `twice`, from the empty store. -/
theorem twice_name_related :
    RunRel [] (readComputation (Effect := Nat) examplePrimitive (elaborateThunks (twice .name)) ids SemEnv.empty
        Fin.elim0).1
      (ScopedNeed.denote examplePrimitive (twice .name) ⟨ids, Fin.elim0, Fin.elim0⟩).1 :=
  (thunks_related examplePrimitive (twice .name) [] SemEnv.empty Fin.elim0 ⟨ids, Fin.elim0, Fin.elim0⟩
    (fun j => j.elim0) (fun j => j.elim0)).1

/-- **Need beside thunks**: the need elaboration in the value layer shares
one choice. -/
theorem twice_need_thunks :
    PolarizedValues.answers (Effect := Nat) examplePrimitive (elaborateThunks (twice .need)) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 2) (.head 2))] :=
  (thunks_answers examplePrimitive (twice .need) ids).trans twice_need

/-- The two elaborations differ as programs: forcing a thunk of a choice
allocates the choice's cell, so the thunk elaboration of a name binder read
once allocates one cell more than its inlining. -/
def onceByName : Annotated Nat ExampleOperation Nat [] :=
  .bind .name coin (.bind .value (.use 0) (.ret (.var ⟨0, by decide⟩)))

theorem onceByName_cells :
    ((runWorlds (readComputation (Effect := Nat) examplePrimitive (elaborateThunks onceByName) ids SemEnv.empty
        Fin.elim0).1 []).map fun world => world.state.length) = [2, 2] ∧
      ((runWorlds (ScopedNeed.reading (Effect := Nat) examplePrimitive (ScopedNeed.elaborate onceByName Fin.elim0) ids
        Fin.elim0).1 []).map fun world => world.state.length) = [1, 1] := by
  constructor <;> decide

theorem onceByName_answers :
    PolarizedValues.answers (Effect := Nat) examplePrimitive (elaborateThunks onceByName) ids =
      ScopedNeed.answers (Effect := Nat) examplePrimitive (ScopedNeed.elaborate onceByName Fin.elim0) ids :=
  thunks_answers examplePrimitive onceByName ids

theorem twice_name_noNeed : NoNeed (twice .name) :=
  .bindName (.choose (.ret _) (.ret _)) (.pair (.use _) (.use _))

/-- **On the machines**: the mixed pair of the name binder is natural for
both elaborations, from the empty heaps. -/
theorem twice_name_thunks_mixed :
    ∃ final, Nonempty (PolarizedNeedNaturalSemantics.Eval examplePrimitive
      ⟨0, 0, 0, (elaborateThunks (twice .name)).erase, ids, Fin.elim0, Fin.elim0⟩ PolarizedFresh.Examples.emptyWorld
      (PolarizedNeedEmbedding.outcome (.value (.pair (.head 1) (.head 2)))) final) :=
  (thunks_natural examplePrimitive (twice .name) twice_name_noNeed ids
    PolarizedFresh.Examples.emptyWorld_fresh
    (ScopedNeed.Fresh.empty _ ScopedNeed.Examples.emptyWorld_lookup) _).mpr ScopedNeed.Examples.twice_name_mixed

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.StrategyThunks
