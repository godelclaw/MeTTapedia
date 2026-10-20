import Mettapedia.TypeTheory.ContextualCBPVStrategyThunks

/-!
# The strategy laws on elaborated code

`ContextualCBPVEquations` proves the CBPV strategy laws for the contextual
model: reuse is licensed for a read-only returner, raising or not, and
discarding for one that also never raises.  Here they are carried over to
strategy-annotated programs, and through `elaborate_answers` and
`thunks_answers` to both elaborations.

* **Reuse** (`need_name_answers`): a need binder may be rebound by name when
  its producer always answers one outcome, a fault included.
* **Discard** (`need_value_answers`): a need binder may be rebound by value
  when that outcome is a value.
* **A raise is not discardable** (`Examples.raise_not_discardable`): rebinding
  by value a producer that raises changes the answers of a body that never
  reads it.

The laws hold as a congruence, at any binder of any program (`Retag`): the
two programs are alike binder by binder (`Corr`), but for need binders of the
left one that the right one rebinds by name or by value.  The proof is a
logical relation between runs over stores whose cells are linked pairwise
(`StoreRel`, `RunRel`): a rebound need binder's cell is pinned, pending or
caching its producer's one outcome, and the extra cells of either side are
free.  Its fundamental lemma is `retag_related`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.StrategyLaws

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ScopedNeed (Strategy Annotated)
open ScopedNeed.Strategy (values needs names Place locate)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-! ## Runs over linked stores -/

/-- Two stores linked cell by cell: a linked pair holds the same cache, a
pinned cell of the left store is pending or caches its outcome, and every
other cell is free. -/
def StoreRel (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (store store' : ScopedNeed.Store Head StableFault NativeFault m) : Prop :=
  (links.map Prod.fst).Nodup ∧ (links.map Prod.snd).Nodup ∧ (pins.map Prod.fst).Nodup ∧
    (∀ link ∈ links, link.1 < store.length ∧ link.2 < store'.length ∧
      store.getD link.1 none = store'.getD link.2 none) ∧
    ∀ pin ∈ pins, pin.1 < store.length ∧ pin.1 ∉ links.map Prod.fst ∧
      (store.getD pin.1 none = none ∨ store.getD pin.1 none = some pin.2)

/-- Two worlds agree: the same branch and answer, and stores related by
links and pins that extend the given ones by cells no older than `store`. -/
def WorldRel (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (store : ScopedNeed.Store Head StableFault NativeFault m)
    (world world' : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (ScopedNeed.Outcome Head StableFault NativeFault m) Effect) : Prop :=
  world.branch = world'.branch ∧ world.answer = world'.answer ∧ store.length ≤ world.state.length ∧
    ∃ (links' : List (Nat × Nat)) (pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)),
      StoreRel (links ++ links') (pins ++ pins') world.state world'.state ∧
        (∀ link ∈ links', store.length ≤ link.1) ∧ ∀ pin ∈ pins', store.length ≤ pin.1

/-- **Two runs agree** under links and pins, and under every extension of
them: from related stores, their worlds agree in order. -/
def RunRel (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (run run' : ScopedNeed.Run Head Effect StableFault NativeFault m) : Prop :=
  ∀ (links' : List (Nat × Nat)) (pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (store store' : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace),
    StoreRel (links ++ links') (pins ++ pins') store store' →
      List.Forall₂ (WorldRel (links ++ links') (pins ++ pins') store)
        (runWorldsAt run store branch) (runWorldsAt run' store' branch)

/-- Two references agree: linked cells and agreeing producers. -/
def RefRel (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m) : Prop :=
  (ref.1, ref'.1) ∈ links ∧ RunRel links pins ref.2 ref'.2

theorem RunRel.mono {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m} (related : RunRel links pins run run')
    (moreLinks : List (Nat × Nat)) (morePins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)) :
    RunRel (links ++ moreLinks) (pins ++ morePins) run run' := by
  intro links' pins' store store' branch storeRel
  rw [List.append_assoc, List.append_assoc] at storeRel ⊢
  exact related (moreLinks ++ links') (morePins ++ pins') store store' branch storeRel

theorem RefRel.mono {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m} (related : RefRel links pins ref ref')
    (moreLinks : List (Nat × Nat)) (morePins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)) :
    RefRel (links ++ moreLinks) (pins ++ morePins) ref ref' :=
  ⟨List.mem_append_left _ related.1, related.2.mono moreLinks morePins⟩

theorem RunRel.pure (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (answer : ScopedNeed.Outcome Head StableFault NativeFault m) :
    RunRel (Effect := Effect) links pins (.pure answer) (.pure answer) := by
  intro links' pins' store store' branch storeRel
  refine .cons ⟨rfl, rfl, le_rfl, [], [], ?_, ?_, ?_⟩ .nil
  · simpa using storeRel
  · intro link member
    cases member
  · intro pin member
    cases member

theorem RunRel.bind {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    {next next' : ScopedNeed.Outcome Head StableFault NativeFault m → ScopedNeed.Run Head Effect StableFault NativeFault m}
    (first : RunRel links pins run run') (continued : ∀ answer, RunRel links pins (next answer) (next' answer)) :
    RunRel links pins (run.bind next) (run'.bind next') := by
  intro links' pins' store store' branch storeRel
  rw [runWorldsAt_bind, runWorldsAt_bind]
  refine List.rel_flatMap (first links' pins' store store' branch storeRel) ?_
  rintro world world' ⟨sameBranch, sameAnswer, longer, links'', pins'', storeRel', freshLinks, freshPins⟩
  dsimp only
  rw [← sameBranch, ← sameAnswer]
  rw [List.append_assoc, List.append_assoc] at storeRel'
  have inner := (continued world.answer) (links' ++ links'') (pins' ++ pins'') world.state world'.state world.branch
    storeRel'
  refine List.rel_map (fun {inner inner'} related => ?_) inner
  obtain ⟨sameBranch', sameAnswer', longer', links''', pins''', storeRel'', freshLinks', freshPins'⟩ := related
  refine ⟨sameBranch', sameAnswer', le_trans longer longer', links'' ++ links''', pins'' ++ pins''', ?_, ?_, ?_⟩
  · simp only [List.append_assoc] at storeRel'' ⊢
    exact storeRel''
  · intro link member
    rcases List.mem_append.mp member with member | member
    · exact freshLinks link member
    · exact le_trans longer (freshLinks' link member)
  · intro pin member
    rcases List.mem_append.mp member with member | member
    · exact freshPins pin member
    · exact le_trans longer (freshPins' pin member)

theorem RunRel.choose {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {left left' right right' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (leftRel : RunRel links pins left left') (rightRel : RunRel links pins right right') :
    RunRel links pins (.choose left right) (.choose left' right') := by
  intro links' pins' store store' branch storeRel
  exact List.rel_append (leftRel links' pins' store store' (false :: branch) storeRel)
    (rightRel links' pins' store store' (true :: branch) storeRel)

theorem RunRel.intent {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m} (effect : Effect)
    (related : RunRel links pins run run') : RunRel links pins (.intent effect run) (.intent effect run') := by
  intro links' pins' store store' branch storeRel
  simp only [runWorldsAt]
  refine List.rel_map ?_ (related links' pins' store store' branch storeRel)
  intro world world' worldRel
  exact worldRel

theorem RunRel.map {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (function : ScopedNeed.Outcome Head StableFault NativeFault m → ScopedNeed.Outcome Head StableFault NativeFault m)
    (related : RunRel links pins run run') : RunRel links pins (Program.map function run) (Program.map function run') :=
  related.bind fun answer => RunRel.pure links pins (function answer)

/-! ### Stores -/

section Stores

variable {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
  {store store' : ScopedNeed.Store Head StableFault NativeFault m}

theorem StoreRel.linkLeft (related : StoreRel links pins store store') {cell : Nat}
    (member : cell ∈ links.map Prod.fst) : cell < store.length := by
  obtain ⟨link, linked, rfl⟩ := List.mem_map.mp member
  exact (related.2.2.2.1 link linked).1

theorem StoreRel.linkRight (related : StoreRel links pins store store') {cell : Nat}
    (member : cell ∈ links.map Prod.snd) : cell < store'.length := by
  obtain ⟨link, linked, rfl⟩ := List.mem_map.mp member
  exact (related.2.2.2.1 link linked).2.1

theorem StoreRel.pinLeft (related : StoreRel links pins store store') {cell : Nat}
    (member : cell ∈ pins.map Prod.fst) : cell < store.length := by
  obtain ⟨pin, pinned, rfl⟩ := List.mem_map.mp member
  exact (related.2.2.2.2 pin pinned).1

theorem StoreRel.alloc (related : StoreRel links pins store store') :
    StoreRel (links ++ [(store.length, store'.length)]) pins (store ++ [none]) (store' ++ [none]) := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩ := related
  have related : StoreRel links pins store store' := ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩
  refine ⟨?_, ?_, pinNodup, ?_, ?_⟩
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨leftNodup, List.nodup_singleton _, ?_⟩
    intro cell member other otherMember equal
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at otherMember
    subst otherMember
    subst equal
    exact lt_irrefl _ (related.linkLeft member)
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨rightNodup, List.nodup_singleton _, ?_⟩
    intro cell member other otherMember equal
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at otherMember
    subst otherMember
    subst equal
    exact lt_irrefl _ (related.linkRight member)
  · intro link member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨leftBound, rightBound, same⟩ := linked link member
      refine ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append _ _ _ _ leftBound, List.getD_append _ _ _ _ rightBound]
      exact same
    · rw [List.mem_singleton] at member
      subst member
      refine ⟨by simp, by simp, ?_⟩
      rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (le_refl _)]
      simp
  · intro pin member
    obtain ⟨bound, unlinked, cached⟩ := pinned pin member
    refine ⟨by rw [List.length_append]; omega, ?_, ?_⟩
    · rw [List.map_append]
      intro linkedMember
      rcases List.mem_append.mp linkedMember with linkedMember | linkedMember
      · exact unlinked linkedMember
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at linkedMember
        omega
    · rw [List.getD_append _ _ _ _ bound]
      exact cached

theorem StoreRel.allocPin (related : StoreRel links pins store store')
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    StoreRel links (pins ++ [(store.length, outcome)]) (store ++ [none]) store' := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩ := related
  have related : StoreRel links pins store store' := ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩
  refine ⟨leftNodup, rightNodup, ?_, ?_, ?_⟩
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨pinNodup, List.nodup_singleton _, ?_⟩
    intro cell member other otherMember equal
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at otherMember
    subst otherMember
    subst equal
    exact lt_irrefl _ (related.pinLeft member)
  · intro link member
    obtain ⟨leftBound, rightBound, same⟩ := linked link member
    refine ⟨by rw [List.length_append]; omega, rightBound, ?_⟩
    rw [List.getD_append _ _ _ _ leftBound]
    exact same
  · intro pin member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨bound, unlinked, cached⟩ := pinned pin member
      refine ⟨by rw [List.length_append]; omega, unlinked, ?_⟩
      rw [List.getD_append _ _ _ _ bound]
      exact cached
    · rw [List.mem_singleton] at member
      subst member
      refine ⟨by simp, fun linkedMember => lt_irrefl _ (related.linkLeft linkedMember), .inl ?_⟩
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp

theorem StoreRel.allocLeft (related : StoreRel links pins store store') :
    StoreRel links pins (store ++ [none]) store' := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩ := related
  refine ⟨leftNodup, rightNodup, pinNodup, fun link member => ?_, fun pin member => ?_⟩
  · obtain ⟨leftBound, rightBound, same⟩ := linked link member
    refine ⟨by rw [List.length_append]; omega, rightBound, ?_⟩
    rw [List.getD_append _ _ _ _ leftBound]
    exact same
  · obtain ⟨bound, unlinked, cached⟩ := pinned pin member
    refine ⟨by rw [List.length_append]; omega, unlinked, ?_⟩
    rw [List.getD_append _ _ _ _ bound]
    exact cached

theorem StoreRel.allocRight (related : StoreRel links pins store store') :
    StoreRel links pins store (store' ++ [none]) := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩ := related
  refine ⟨leftNodup, rightNodup, pinNodup, fun link member => ?_, pinned⟩
  obtain ⟨leftBound, rightBound, same⟩ := linked link member
  refine ⟨leftBound, by rw [List.length_append]; omega, ?_⟩
  rw [List.getD_append _ _ _ _ rightBound]
  exact same

theorem settled_getD_self (cell : Nat) (outcome : ScopedNeed.Outcome Head StableFault NativeFault m)
    (store : ScopedNeed.Store Head StableFault NativeFault m) (bound : cell < store.length) :
    (ScopedNeed.settled cell outcome store).getD cell none =
      match outcome with
      | .retryableFault _ => store.getD cell none
      | outcome => some outcome := by
  cases outcome with
  | value value => simp [ScopedNeed.settled, List.getD_eq_getElem?_getD, List.getElem?_set_self bound]
  | stableFault fault => simp [ScopedNeed.settled, List.getD_eq_getElem?_getD, List.getElem?_set_self bound]
  | retryableFault reason => rfl

theorem StoreRel.settleLinked (related : StoreRel links pins store store') {cell cell' : Nat}
    (linked : (cell, cell') ∈ links) (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    StoreRel links pins (ScopedNeed.settled cell outcome store) (ScopedNeed.settled cell' outcome store') := by
  obtain ⟨leftNodup, rightNodup, pinNodup, links', pinned⟩ := related
  refine ⟨leftNodup, rightNodup, pinNodup, fun link member => ?_, fun pin member => ?_⟩
  · obtain ⟨leftBound, rightBound, same⟩ := links' link member
    refine ⟨by rw [ScopedNeed.settled_length]; exact leftBound, by rw [ScopedNeed.settled_length]; exact rightBound, ?_⟩
    by_cases same' : link = (cell, cell')
    · subst same'
      rw [settled_getD_self _ _ _ leftBound, settled_getD_self _ _ _ rightBound]
      cases outcome
      · rfl
      · rfl
      · exact same
    · have leftDifferent : link.1 ≠ cell := fun equal =>
        same' (List.inj_on_of_nodup_map leftNodup member linked equal)
      have rightDifferent : link.2 ≠ cell' := fun equal =>
        same' (List.inj_on_of_nodup_map rightNodup member linked equal)
      rw [ScopedNeed.settled_other _ _ leftDifferent, ScopedNeed.settled_other _ _ rightDifferent]
      exact same
  · obtain ⟨bound, unlinked, cached⟩ := pinned pin member
    have different : pin.1 ≠ cell := fun equal =>
      unlinked (equal ▸ List.mem_map.mpr ⟨_, linked, rfl⟩)
    refine ⟨by rw [ScopedNeed.settled_length]; exact bound, unlinked, ?_⟩
    rw [ScopedNeed.settled_other _ _ different]
    exact cached

theorem StoreRel.settlePinned (related : StoreRel links pins store store') {cell : Nat}
    {outcome : ScopedNeed.Outcome Head StableFault NativeFault m} (pinned : (cell, outcome) ∈ pins) :
    StoreRel links pins (ScopedNeed.settled cell outcome store) store' := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pins'⟩ := related
  obtain ⟨cellBound, cellUnlinked, _⟩ := pins' _ pinned
  refine ⟨leftNodup, rightNodup, pinNodup, fun link member => ?_, fun pin member => ?_⟩
  · obtain ⟨leftBound, rightBound, same⟩ := linked link member
    have different : link.1 ≠ cell := fun equal =>
      cellUnlinked (equal ▸ List.mem_map.mpr ⟨_, member, rfl⟩)
    refine ⟨by rw [ScopedNeed.settled_length]; exact leftBound, rightBound, ?_⟩
    rw [ScopedNeed.settled_other _ _ different]
    exact same
  · obtain ⟨bound, unlinked, cached⟩ := pins' pin member
    refine ⟨by rw [ScopedNeed.settled_length]; exact bound, unlinked, ?_⟩
    by_cases same : pin.1 = cell
    · have equal : pin = (cell, outcome) := List.inj_on_of_nodup_map pinNodup member pinned same
      subst equal
      rw [settled_getD_self _ _ _ cellBound]
      cases outcome
      · exact .inr rfl
      · exact .inr rfl
      · exact cached
    · rw [ScopedNeed.settled_other _ _ same]
      exact cached

theorem StoreRel.settleLeftFree (related : StoreRel links pins store store') {cell : Nat}
    (unlinked : cell ∉ links.map Prod.fst) (unpinned : cell ∉ pins.map Prod.fst)
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    StoreRel links pins (ScopedNeed.settled cell outcome store) store' := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩ := related
  refine ⟨leftNodup, rightNodup, pinNodup, fun link member => ?_, fun pin member => ?_⟩
  · obtain ⟨leftBound, rightBound, same⟩ := linked link member
    have different : link.1 ≠ cell := fun equal => unlinked (equal ▸ List.mem_map.mpr ⟨_, member, rfl⟩)
    refine ⟨by rw [ScopedNeed.settled_length]; exact leftBound, rightBound, ?_⟩
    rw [ScopedNeed.settled_other _ _ different]
    exact same
  · obtain ⟨bound, pinUnlinked, cached⟩ := pinned pin member
    have different : pin.1 ≠ cell := fun equal => unpinned (equal ▸ List.mem_map.mpr ⟨_, member, rfl⟩)
    refine ⟨by rw [ScopedNeed.settled_length]; exact bound, pinUnlinked, ?_⟩
    rw [ScopedNeed.settled_other _ _ different]
    exact cached

theorem StoreRel.settleRightFree (related : StoreRel links pins store store') {cell' : Nat}
    (unlinked : cell' ∉ links.map Prod.snd) (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    StoreRel links pins store (ScopedNeed.settled cell' outcome store') := by
  obtain ⟨leftNodup, rightNodup, pinNodup, linked, pinned⟩ := related
  refine ⟨leftNodup, rightNodup, pinNodup, fun link member => ?_, pinned⟩
  obtain ⟨leftBound, rightBound, same⟩ := linked link member
  have different : link.2 ≠ cell' := fun equal => unlinked (equal ▸ List.mem_map.mpr ⟨_, member, rfl⟩)
  refine ⟨leftBound, by rw [ScopedNeed.settled_length]; exact rightBound, ?_⟩
  rw [ScopedNeed.settled_other _ _ different]
  exact same

end Stores

/-! ### Cells -/

theorem RunRel.settle {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {cell cell' : Nat} (linked : (cell, cell') ∈ links) (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    RunRel (Effect := Effect) links pins (ScopedNeed.settle cell outcome) (ScopedNeed.settle cell' outcome) := by
  intro links' pins' store store' branch storeRel
  rw [ScopedNeed.settle_run, ScopedNeed.settle_run]
  refine .cons ⟨rfl, rfl, by rw [ScopedNeed.settled_length], [], [], ?_, ?_, ?_⟩ .nil
  · simpa using storeRel.settleLinked (List.mem_append_left _ linked) outcome
  · intro link member
    cases member
  · intro pin member
    cases member

/-- **Demanding linked references agrees.** -/
theorem RunRel.demand {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m} (related : RefRel links pins ref ref') :
    RunRel links pins (ScopedNeed.demand ref.1 ref.2) (ScopedNeed.demand ref'.1 ref'.2) := by
  obtain ⟨linked, runs⟩ := related
  intro links' pins' store store' branch storeRel
  have cached : store'.getD ref'.1 none = store.getD ref.1 none :=
    ((storeRel.2.2.2.1 _ (List.mem_append_left _ linked)).2.2).symm
  unfold ScopedNeed.demand
  simp only [runWorldsAt]
  rw [cached]
  cases found : store.getD ref.1 none with
  | some outcome =>
      dsimp only
      exact (RunRel.pure (Effect := Effect) links pins outcome) links' pins' store store' branch storeRel
  | none =>
      dsimp only
      exact (runs.bind fun outcome => RunRel.settle linked outcome) links' pins' store store' branch storeRel

/-- **A pinned cell answers its outcome**, demanded or not. -/
theorem RunRel.demandPinned {links : List (Nat × Nat)}
    {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)} {cell : Nat}
    {outcome : ScopedNeed.Outcome Head StableFault NativeFault m} (pinned : (cell, outcome) ∈ pins) :
    RunRel (Effect := Effect) links pins (ScopedNeed.demand cell (.pure outcome)) (.pure outcome) := by
  intro links' pins' store store' branch storeRel
  have pinned' : (cell, outcome) ∈ pins ++ pins' := List.mem_append_left _ pinned
  obtain ⟨_, _, cached⟩ := storeRel.2.2.2.2 _ pinned'
  unfold ScopedNeed.demand
  simp only [runWorldsAt]
  rcases cached with pending | settled
  · rw [pending]
    dsimp only
    rw [runWorldsAt_bind]
    simp only [runWorldsAt, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ScopedNeed.settle_run]
    simp only [List.map_cons, List.map_nil]
    refine .cons ⟨rfl, rfl, ?_, [], [], ?_, ?_, ?_⟩ .nil
    · show store.length ≤ (ScopedNeed.settled cell outcome store).length
      rw [ScopedNeed.settled_length]
    · simpa [WorldResult.prependIntents] using storeRel.settlePinned pinned'
    · intro link member
      cases member
    · intro pin member
      cases member
  · rw [settled]
    dsimp only
    exact (RunRel.pure (Effect := Effect) links pins outcome) links' pins' store store' branch storeRel

/-- **Allocating a linked cell on both sides agrees**, if the continuations
agree on it. -/
theorem RunRel.alloc {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {next next' : Nat → ScopedNeed.Run Head Effect StableFault NativeFault m}
    (continued : ∀ (links' : List (Nat × Nat)) (pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
      (store store' : ScopedNeed.Store Head StableFault NativeFault m),
      StoreRel (links ++ links') (pins ++ pins') store store' →
        RunRel (links ++ links' ++ [(store.length, store'.length)]) (pins ++ pins') (next store.length)
          (next' store'.length)) :
    RunRel links pins (ScopedNeed.alloc next) (ScopedNeed.alloc next') := by
  intro links' pins' store store' branch storeRel
  simp only [ScopedNeed.alloc, runWorldsAt]
  have inner := continued links' pins' store store' storeRel [] [] (store ++ [none]) (store' ++ [none]) branch
    (by simpa using storeRel.alloc)
  refine List.Forall₂.imp (fun {world world'} related => ?_) inner
  obtain ⟨sameBranch, sameAnswer, longer, links'', pins'', storeRel', freshLinks, freshPins⟩ := related
  refine ⟨sameBranch, sameAnswer, le_trans (by simp) longer, [(store.length, store'.length)] ++ links'', pins'', ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using storeRel'
  · intro link member
    rcases List.mem_append.mp member with member | member
    · rw [List.mem_singleton] at member
      subst member
      exact le_refl _
    · exact le_trans (by simp) (freshLinks link member)
  · intro pin member
    exact le_trans (by simp) (freshPins pin member)

/-- **A pinned cell allocated on the left only.** -/
theorem RunRel.allocPin {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m)
    {next : Nat → ScopedNeed.Run Head Effect StableFault NativeFault m}
    {run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (continued : ∀ (links' : List (Nat × Nat)) (pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
      (store store' : ScopedNeed.Store Head StableFault NativeFault m),
      StoreRel (links ++ links') (pins ++ pins') store store' →
        RunRel (links ++ links') (pins ++ pins' ++ [(store.length, outcome)]) (next store.length) run') :
    RunRel links pins (ScopedNeed.alloc next) run' := by
  intro links' pins' store store' branch storeRel
  simp only [ScopedNeed.alloc, runWorldsAt]
  have inner := continued links' pins' store store' storeRel [] [] (store ++ [none]) store' branch
    (by simpa using storeRel.allocPin outcome)
  refine List.Forall₂.imp (fun {world world'} related => ?_) inner
  obtain ⟨sameBranch, sameAnswer, longer, links'', pins'', storeRel', freshLinks, freshPins⟩ := related
  refine ⟨sameBranch, sameAnswer, le_trans (by simp) longer, links'', [(store.length, outcome)] ++ pins'', ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using storeRel'
  · intro link member
    exact le_trans (by simp) (freshLinks link member)
  · intro pin member
    rcases List.mem_append.mp member with member | member
    · rw [List.mem_singleton] at member
      subst member
      exact le_refl _
    · exact le_trans (by simp) (freshPins pin member)

/-- **A cell allocated and demanded at once on the right only**, with a
producer of one outcome. -/
theorem RunRel.allocDemandRight {links : List (Nat × Nat)}
    {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (outcome : ScopedNeed.Outcome Head StableFault NativeFault m)
    {next' : ScopedNeed.Outcome Head StableFault NativeFault m → ScopedNeed.Run Head Effect StableFault NativeFault m}
    (related : RunRel links pins run (next' outcome)) :
    RunRel links pins run
      (ScopedNeed.alloc fun cell => (ScopedNeed.demand cell (.pure outcome)).bind next') := by
  intro links' pins' store store' branch storeRel
  have pending : (store' ++ [none]).getD store'.length none = none := by simp
  have expand : runWorldsAt (ScopedNeed.alloc fun cell => (ScopedNeed.demand cell (.pure outcome)).bind next') store'
      branch = (runWorldsAt (next' outcome) (ScopedNeed.settled store'.length outcome (store' ++ [none])) branch).map
        (WorldResult.prependIntents []) := by
    simp only [ScopedNeed.alloc, runWorldsAt]
    rw [runWorldsAt_bind, ScopedNeed.demand_pending _ _ _ _ pending, runWorldsAt_bind]
    simp only [runWorldsAt, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ScopedNeed.settle_run]
    simp [WorldResult.prependIntents]
  rw [expand]
  have unlinked : store'.length ∉ (links ++ links').map Prod.snd := fun member =>
    lt_irrefl _ (storeRel.linkRight member)
  have inner := related links' pins' store (ScopedNeed.settled store'.length outcome (store' ++ [none])) branch
    (storeRel.allocRight.settleRightFree unlinked outcome)
  rw [List.forall₂_map_right_iff]
  exact inner.imp fun _ _ worldRel => worldRel

/-- **An extra cell demanded at once on the left agrees with its producer
run in place.** -/
theorem RunRel.allocExtra {links : List (Nat × Nat)}
    {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m}
    (related : RunRel links pins run run') :
    RunRel links pins (ScopedNeed.alloc fun cell => ScopedNeed.demand cell run) run' := by
  intro links' pins' store store' branch storeRel
  have pending : (store ++ [none]).getD store.length none = none := by simp
  have expand : runWorldsAt (ScopedNeed.alloc fun cell => ScopedNeed.demand cell run) store branch =
      (runWorldsAt run (store ++ [none]) branch).map fun prior => WorldResult.prependIntents prior.intents
        { branch := prior.branch, answer := prior.answer,
          state := ScopedNeed.settled store.length prior.answer prior.state, intents := [] } := by
    simp only [ScopedNeed.alloc, runWorldsAt]
    rw [ScopedNeed.demand_pending _ _ _ _ pending, runWorldsAt_bind]
    induction runWorldsAt run (store ++ [none]) branch with
    | nil => rfl
    | cons prior rest ih =>
        rw [List.flatMap_cons, List.map_cons, ScopedNeed.settle_run, ih]
        rfl
  rw [expand, ← List.map_id (runWorldsAt run' store' branch)]
  refine List.rel_map (fun {world world'} worldRel => ?_) (related links' pins' (store ++ [none]) store' branch
    storeRel.allocLeft)
  obtain ⟨sameBranch, sameAnswer, longer, links'', pins'', storeRel', freshLinks, freshPins⟩ := worldRel
  have unlinked : store.length ∉ (links ++ links' ++ links'').map Prod.fst := by
    intro member
    rw [List.map_append] at member
    rcases List.mem_append.mp member with member | member
    · exact lt_irrefl _ (storeRel.linkLeft member)
    · obtain ⟨link, linked, equal⟩ := List.mem_map.mp member
      have := freshLinks link linked
      rw [equal] at this
      simp at this
  have unpinned : store.length ∉ (pins ++ pins' ++ pins'').map Prod.fst := by
    intro member
    rw [List.map_append] at member
    rcases List.mem_append.mp member with member | member
    · exact lt_irrefl _ (storeRel.pinLeft member)
    · obtain ⟨pin, pinnedMember, equal⟩ := List.mem_map.mp member
      have := freshPins pin pinnedMember
      rw [equal] at this
      simp at this
  refine ⟨sameBranch, sameAnswer, ?_, links'', pins'', storeRel'.settleLeftFree unlinked unpinned _, ?_, ?_⟩
  · show store.length ≤ (ScopedNeed.settled store.length world.answer world.state).length
    rw [ScopedNeed.settled_length]
    exact le_trans (by simp) longer
  · intro link member
    exact le_trans (by simp) (freshLinks link member)
  · intro pin member
    exact le_trans (by simp) (freshPins pin member)

theorem RunRel.pure_inj {links : List (Nat × Nat)}
    {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {outcome outcome' : ScopedNeed.Outcome Head StableFault NativeFault m}
    (related : RunRel (Effect := Effect) links pins (.pure outcome) (.pure outcome'))
    {links' : List (Nat × Nat)} {pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    (storeRel : StoreRel (links ++ links') (pins ++ pins') store store') : outcome = outcome' := by
  have worlds := related links' pins' store store' [] storeRel
  simp only [runWorldsAt] at worlds
  cases worlds with
  | cons head _ => exact head.2.1

theorem RunRel.weaken {links links₂ : List (Nat × Nat)}
    {pins pins₂ : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m} (related : RunRel links pins run run')
    (linkPrefix : links <+: links₂) (pinPrefix : pins <+: pins₂) : RunRel links₂ pins₂ run run' := by
  obtain ⟨moreLinks, rfl⟩ := linkPrefix
  obtain ⟨morePins, rfl⟩ := pinPrefix
  exact related.mono moreLinks morePins

theorem RefRel.weaken {links links₂ : List (Nat × Nat)}
    {pins pins₂ : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m} (related : RefRel links pins ref ref')
    (linkPrefix : links <+: links₂) (pinPrefix : pins <+: pins₂) : RefRel links₂ pins₂ ref ref' :=
  ⟨linkPrefix.subset related.1, related.2.weaken linkPrefix pinPrefix⟩

/-- A cell allocated on both sides is a linked reference of both. -/
theorem RefRel.alloc {links links' : List (Nat × Nat)}
    {pins pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {store store' : ScopedNeed.Store Head StableFault NativeFault m}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m} (related : RunRel links pins run run') :
    RefRel (links ++ links' ++ [(store.length, store'.length)]) (pins ++ pins') (store.length, run)
      (store'.length, run') :=
  ⟨List.mem_append_right _ (List.mem_singleton_self _),
    related.weaken ((List.prefix_append _ _).trans (List.prefix_append _ _)) (List.prefix_append _ _)⟩

theorem answers_of_forall₂ {links : List (Nat × Nat)}
    {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {store : ScopedNeed.Store Head StableFault NativeFault m}
    {worlds worlds' : List (WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (ScopedNeed.Outcome Head StableFault NativeFault m) Effect)}
    (related : List.Forall₂ (WorldRel links pins store) worlds worlds') :
    worlds.map WorldResult.answer = worlds'.map WorldResult.answer := by
  induction related with
  | nil => rfl
  | cons head _ ih => rw [List.map_cons, List.map_cons, head.2.1, ih]

/-! ## Programs alike but for rebound need binders -/

/-- How a need binder of the left program is rebound on the right. -/
inductive Kind where
  | name
  | value
  deriving DecidableEq

/-- The strategy a kind rebinds by. -/
def Kind.strategy : Kind → Strategy
  | .name => .name
  | .value => .value

/-- Two scopes, binder by binder: the same strategy on both sides, or a need
binder on the left rebound by name or by value on the right. -/
inductive Corr : List Strategy → List Strategy → Type where
  | nil : Corr [] []
  | same (strategy : Strategy) {left right : List Strategy} : Corr left right →
      Corr (strategy :: left) (strategy :: right)
  | swap (kind : Kind) {left right : List Strategy} : Corr left right → Corr (.need :: left) (kind.strategy :: right)

namespace Corr

/-- The value variables of the left scope among those of the right. -/
def native : {left right : List Strategy} → Corr left right → Fin (values left) → Fin (values right)
  | _, _, .nil, index => index.elim0
  | _, _, @Corr.same .value _ right corr, index =>
      Fin.cases (motive := fun _ => Fin (values right + 1)) (0 : Fin (values right + 1))
        (fun i => (corr.native i).succ) index
  | _, _, .same .need corr, index => corr.native index
  | _, _, .same .name corr, index => corr.native index
  | _, _, .swap .name corr, index => corr.native index
  | _, _, .swap .value corr, index => (corr.native index).succ

/-- The references of the right scope among those of the left. -/
def ref : {left right : List Strategy} → Corr left right → Fin (needs right) → Fin (needs left)
  | _, _, .nil, index => index.elim0
  | _, _, .same .value corr, index => corr.ref index
  | _, _, @Corr.same .need left _ corr, index =>
      Fin.cases (motive := fun _ => Fin (needs left + 1)) (0 : Fin (needs left + 1)) (fun j => (corr.ref j).succ) index
  | _, _, .same .name corr, index => corr.ref index
  | _, _, .swap .name corr, index => (corr.ref index).succ
  | _, _, .swap .value corr, index => (corr.ref index).succ

/-- The producers of the left scope among those of the right. -/
def producer : {left right : List Strategy} → Corr left right → Fin (names left) → Fin (names right)
  | _, _, .nil, index => index.elim0
  | _, _, .same .value corr, index => corr.producer index
  | _, _, .same .need corr, index => corr.producer index
  | _, _, @Corr.same .name _ right corr, index =>
      Fin.cases (motive := fun _ => Fin (names right + 1)) (0 : Fin (names right + 1))
        (fun j => (corr.producer j).succ) index
  | _, _, .swap .name corr, index => (corr.producer index).succ
  | _, _, .swap .value corr, index => corr.producer index

/-- The positions of the left scope as those of the right. -/
def position : {left right : List Strategy} → Corr left right → Fin left.length → Fin right.length
  | _, _, .nil, index => index.elim0
  | _, _, @Corr.same _ _ right corr, index =>
      Fin.cases (motive := fun _ => Fin (right.length + 1)) (0 : Fin (right.length + 1))
        (fun p => (corr.position p).succ) index
  | _, _, @Corr.swap _ _ right corr, index =>
      Fin.cases (motive := fun _ => Fin (right.length + 1)) (0 : Fin (right.length + 1))
        (fun p => (corr.position p).succ) index

/-- The rebound binders. -/
def Site : {left right : List Strategy} → Corr left right → Type
  | _, _, .nil => Empty
  | _, _, .same _ corr => corr.Site
  | _, _, .swap _ corr => Option corr.Site

/-- The reference a rebound binder's cell has on the left. -/
def siteRef : {left right : List Strategy} → (corr : Corr left right) → corr.Site → Fin (needs left)
  | _, _, .nil, site => site.elim
  | _, _, .same .value corr, site => corr.siteRef site
  | _, _, .same .need corr, site => (corr.siteRef site).succ
  | _, _, .same .name corr, site => corr.siteRef site
  | _, _, @Corr.swap _ left _ corr, site =>
      Option.elim (site : Option corr.Site) (0 : Fin (needs left + 1)) fun site => (corr.siteRef site).succ

/-- The place a rebound binder's variable has on the right. -/
def sitePlace : {left right : List Strategy} → (corr : Corr left right) → corr.Site → Place right
  | _, _, .nil, site => site.elim
  | _, _, .same strategy corr, site => (corr.sitePlace site).weaken strategy
  | _, _, .swap kind corr, site =>
      Option.elim (site : Option corr.Site) (Place.here kind.strategy) fun site =>
        (corr.sitePlace site).weaken kind.strategy

/-- The correspondence of a scope with itself. -/
def refl : (scope : List Strategy) → Corr scope scope
  | [] => .nil
  | strategy :: rest => .same strategy (refl rest)

theorem refl_native : (scope : List Strategy) → ∀ index, (refl scope).native index = index
  | [], index => index.elim0
  | .value :: rest, index => by
      refine Fin.cases rfl (fun i => ?_) index
      show ((refl rest).native i).succ = i.succ
      rw [refl_native rest i]
  | .need :: rest, index => refl_native rest index
  | .name :: rest, index => refl_native rest index

theorem refl_position : (scope : List Strategy) → ∀ position, (refl scope).position position = position
  | [], position => position.elim0
  | _ :: rest, position => by
      refine Fin.cases rfl (fun p => ?_) position
      show ((refl rest).position p).succ = p.succ
      rw [refl_position rest p]

end Corr

/-- Corresponding places of two scopes. -/
inductive Located {left right : List Strategy} (corr : Corr left right) : Place left → Place right → Prop where
  | native (index : Fin (values left)) : Located corr (.native index) (.native (corr.native index))
  | reference (index : Fin (needs right)) : Located corr (.reference (corr.ref index)) (.reference index)
  | producer (index : Fin (names left)) : Located corr (.producer index) (.producer (corr.producer index))
  | site (site : corr.Site) : Located corr (.reference (corr.siteRef site)) (corr.sitePlace site)

theorem Located.weakenSame {left right : List Strategy} {corr : Corr left right} {place : Place left}
    {place' : Place right} (located : Located corr place place') (strategy : Strategy) :
    Located (.same strategy corr) (place.weaken strategy) (place'.weaken strategy) := by
  cases located with
  | native index =>
      cases strategy
      · exact Located.native (corr := .same .value corr) index.succ
      · exact Located.native (corr := .same .need corr) index
      · exact Located.native (corr := .same .name corr) index
  | reference index =>
      cases strategy
      · exact Located.reference (corr := .same .value corr) index
      · exact Located.reference (corr := .same .need corr) index.succ
      · exact Located.reference (corr := .same .name corr) index
  | producer index =>
      cases strategy
      · exact Located.producer (corr := .same .value corr) index
      · exact Located.producer (corr := .same .need corr) index
      · exact Located.producer (corr := .same .name corr) index.succ
  | site site =>
      cases strategy
      · exact Located.site (corr := .same .value corr) site
      · exact Located.site (corr := .same .need corr) site
      · exact Located.site (corr := .same .name corr) site

theorem Located.weakenSwap {left right : List Strategy} {corr : Corr left right} {place : Place left}
    {place' : Place right} (located : Located corr place place') (kind : Kind) :
    Located (.swap kind corr) (place.weaken .need) (place'.weaken kind.strategy) := by
  cases located with
  | native index =>
      cases kind
      · exact Located.native (corr := .swap .name corr) index
      · exact Located.native (corr := .swap .value corr) index
  | reference index =>
      cases kind
      · exact Located.reference (corr := .swap .name corr) index
      · exact Located.reference (corr := .swap .value corr) index
  | producer index =>
      cases kind
      · exact Located.producer (corr := .swap .name corr) index
      · exact Located.producer (corr := .swap .value corr) index
  | site site =>
      cases kind
      · exact Located.site (corr := .swap .name corr) (some site)
      · exact Located.site (corr := .swap .value corr) (some site)

/-- **Corresponding positions have corresponding places.** -/
theorem locate_located : {left right : List Strategy} → (corr : Corr left right) → (position : Fin left.length) →
    Located corr (locate left position) (locate right (corr.position position))
  | _, _, .nil, position => position.elim0
  | _, _, .same strategy corr, position => by
      refine Fin.cases ?_ (fun p => ?_) position
      · cases strategy
        · exact Located.native (corr := .same .value corr) ⟨0, Nat.succ_pos _⟩
        · exact Located.reference (corr := .same .need corr) ⟨0, Nat.succ_pos _⟩
        · exact Located.producer (corr := .same .name corr) ⟨0, Nat.succ_pos _⟩
      · exact (locate_located corr p).weakenSame strategy
  | _, _, .swap kind corr, position => by
      refine Fin.cases ?_ (fun p => ?_) position
      · cases kind
        · exact Located.site (corr := .swap .name corr) none
        · exact Located.site (corr := .swap .value corr) none
      · exact (locate_located corr p).weakenSwap kind

theorem meaning_weaken_value {scope : List Strategy} (env : ScopedNeed.Env Head Effect StableFault NativeFault m scope)
    (value : Tm Head m) (place : Place scope) :
    (env.bindValue value).meaning (place.weaken .value) = env.meaning place := by
  cases place <;> rfl

theorem meaning_weaken_need {scope : List Strategy} (env : ScopedNeed.Env Head Effect StableFault NativeFault m scope)
    (ref : ScopedNeed.Ref Head Effect StableFault NativeFault m) (place : Place scope) :
    (env.bindNeed ref).meaning (place.weaken .need) = env.meaning place := by
  cases place <;> rfl

theorem meaning_weaken_name {scope : List Strategy} (env : ScopedNeed.Env Head Effect StableFault NativeFault m scope)
    (producer : ScopedNeed.Run Head Effect StableFault NativeFault m × ScopedNeed.Run Head Effect StableFault NativeFault m)
    (place : Place scope) :
    (env.bindName producer).meaning (place.weaken .name) = env.meaning place := by
  cases place <;> rfl

/-! ## Agreeing environments -/

/-- Two runs agree as a program and producer pair: program with program,
program with producer, producer with producer. -/
def PairRel (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (pair pair' : ScopedNeed.Run Head Effect StableFault NativeFault m × ScopedNeed.Run Head Effect StableFault NativeFault m) :
    Prop :=
  RunRel links pins pair.1 pair'.1 ∧ RunRel links pins pair.1 pair'.2 ∧ RunRel links pins pair.2 pair'.2

theorem PairRel.mono {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {pair pair' : ScopedNeed.Run Head Effect StableFault NativeFault m × ScopedNeed.Run Head Effect StableFault NativeFault m}
    (related : PairRel links pins pair pair') (moreLinks : List (Nat × Nat))
    (morePins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)) :
    PairRel (links ++ moreLinks) (pins ++ morePins) pair pair' :=
  ⟨related.1.mono _ _, related.2.1.mono _ _, related.2.2.mono _ _⟩

theorem PairRel.same {links : List (Nat × Nat)} {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
    {run run' : ScopedNeed.Run Head Effect StableFault NativeFault m} (related : RunRel links pins run run') :
    PairRel links pins (run, run) (run', run') :=
  ⟨related, related, related⟩

/-- Environments that agree under a correspondence: equal native values,
linked references, agreeing producers, and rebound binders whose left cell is
pinned to the one outcome that the right side answers. -/
structure EnvRel {left right : List Strategy} (corr : Corr left right) (links : List (Nat × Nat))
    (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
    (envL : ScopedNeed.Env Head Effect StableFault NativeFault m left)
    (envR : ScopedNeed.Env Head Effect StableFault NativeFault m right) : Prop where
  native : ∀ index, envL.native index = envR.native (corr.native index)
  references : ∀ index, RefRel links pins (envL.references (corr.ref index)) (envR.references index)
  producers : ∀ index, PairRel links pins (envL.producers index) (envR.producers (corr.producer index))
  sites : ∀ site, ∃ outcome, (envL.references (corr.siteRef site)).2 = .pure outcome ∧
    ((envL.references (corr.siteRef site)).1, outcome) ∈ pins ∧
    envR.meaning (corr.sitePlace site) = (.pure outcome, .pure outcome)

section EnvRel

variable {left right : List Strategy} {corr : Corr left right} {links : List (Nat × Nat)}
  {pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)}
  {envL : ScopedNeed.Env Head Effect StableFault NativeFault m left}
  {envR : ScopedNeed.Env Head Effect StableFault NativeFault m right}

theorem EnvRel.mono (related : EnvRel corr links pins envL envR) (moreLinks : List (Nat × Nat))
    (morePins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)) :
    EnvRel corr (links ++ moreLinks) (pins ++ morePins) envL envR := by
  refine ⟨related.native, fun index => (related.references index).mono _ _,
    fun index => (related.producers index).mono _ _, fun site => ?_⟩
  obtain ⟨outcome, producer, pinned, meaning⟩ := related.sites site
  exact ⟨outcome, producer, List.mem_append_left _ pinned, meaning⟩

theorem EnvRel.weaken (related : EnvRel corr links pins envL envR) {links₂ : List (Nat × Nat)}
    {pins₂ : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m)} (linkPrefix : links <+: links₂)
    (pinPrefix : pins <+: pins₂) : EnvRel corr links₂ pins₂ envL envR := by
  obtain ⟨moreLinks, rfl⟩ := linkPrefix
  obtain ⟨morePins, rfl⟩ := pinPrefix
  exact related.mono moreLinks morePins

theorem EnvRel.bindValue (related : EnvRel corr links pins envL envR) (value : Tm Head m) :
    EnvRel (.same .value corr) links pins (envL.bindValue value) (envR.bindValue value) := by
  refine ⟨fun index => ?_, related.references, related.producers, fun site => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) index
    · rfl
    · exact related.native i
  · obtain ⟨outcome, producer, pinned, meaning⟩ := related.sites site
    refine ⟨outcome, producer, pinned, ?_⟩
    show (envR.bindValue value).meaning ((corr.sitePlace site).weaken .value) = _
    rw [meaning_weaken_value]
    exact meaning

theorem EnvRel.bindNeed (related : EnvRel corr links pins envL envR)
    {ref ref' : ScopedNeed.Ref Head Effect StableFault NativeFault m} (refRel : RefRel links pins ref ref') :
    EnvRel (.same .need corr) links pins (envL.bindNeed ref) (envR.bindNeed ref') := by
  refine ⟨related.native, fun index => ?_, related.producers, fun site => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) index
    · exact refRel
    · exact related.references j
  · obtain ⟨outcome, producer, pinned, meaning⟩ := related.sites site
    refine ⟨outcome, producer, pinned, ?_⟩
    show (envR.bindNeed ref').meaning ((corr.sitePlace site).weaken .need) = _
    rw [meaning_weaken_need]
    exact meaning

theorem EnvRel.bindName (related : EnvRel corr links pins envL envR)
    {producer producer' : ScopedNeed.Run Head Effect StableFault NativeFault m ×
      ScopedNeed.Run Head Effect StableFault NativeFault m}
    (pairRel : PairRel links pins producer producer') :
    EnvRel (.same .name corr) links pins (envL.bindName producer) (envR.bindName producer') := by
  refine ⟨related.native, related.references, fun index => ?_, fun site => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) index
    · exact pairRel
    · exact related.producers j
  · obtain ⟨outcome, producer, pinned, meaning⟩ := related.sites site
    refine ⟨outcome, producer, pinned, ?_⟩
    show (envR.bindName producer').meaning ((corr.sitePlace site).weaken .name) = _
    rw [meaning_weaken_name]
    exact meaning

theorem EnvRel.swapName (related : EnvRel corr links pins envL envR) {cell : Nat}
    {outcome : ScopedNeed.Outcome Head StableFault NativeFault m} (pinned : (cell, outcome) ∈ pins) :
    EnvRel (.swap .name corr) links pins (envL.bindNeed (cell, .pure outcome))
      (envR.bindName (.pure outcome, .pure outcome)) := by
  refine ⟨related.native, related.references, related.producers, fun site => ?_⟩
  cases site with
  | none => exact ⟨outcome, rfl, pinned, rfl⟩
  | some site =>
      obtain ⟨outcome', producer, pinned', meaning⟩ := related.sites site
      refine ⟨outcome', producer, pinned', ?_⟩
      show (envR.bindName (.pure outcome, .pure outcome)).meaning ((corr.sitePlace site).weaken .name) = _
      rw [meaning_weaken_name]
      exact meaning

theorem EnvRel.swapValue (related : EnvRel corr links pins envL envR) {cell : Nat} {value : Tm Head m}
    (pinned : (cell, (.value value : ScopedNeed.Outcome Head StableFault NativeFault m)) ∈ pins) :
    EnvRel (.swap .value corr) links pins (envL.bindNeed (cell, .pure (.value value))) (envR.bindValue value) := by
  refine ⟨related.native, related.references, related.producers, fun site => ?_⟩
  cases site with
  | none => exact ⟨.value value, rfl, pinned, rfl⟩
  | some site =>
      obtain ⟨outcome', producer, pinned', meaning⟩ := related.sites site
      refine ⟨outcome', producer, pinned', ?_⟩
      show (envR.bindValue value).meaning ((corr.sitePlace site).weaken .value) = _
      rw [meaning_weaken_value]
      exact meaning

end EnvRel

/-! ## Programs alike but for rebound need binders -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

/-- A producer that answers one outcome, under every environment, without
effects or choices. -/
def Constant {scope : List Strategy} (bound : Annotated Head Operation Effect scope) : Prop :=
  ∀ env : ScopedNeed.Env Head Effect StableFault NativeFault m scope,
    ∃ outcome, ScopedNeed.denote primitive bound env = (.pure outcome, .pure outcome)

/-- A producer that answers one value, under every environment. -/
def Returns {scope : List Strategy} (bound : Annotated Head Operation Effect scope) : Prop :=
  ∀ env : ScopedNeed.Env Head Effect StableFault NativeFault m scope,
    ∃ value, ScopedNeed.denote primitive bound env = (.pure (.value value), .pure (.value value))

/-- **Programs alike but for rebound need binders**: binder by binder the
same, under a correspondence of their scopes, but where a need binder of the
left program is rebound by name, its producer answering one outcome, or by
value, its producer answering one value. -/
inductive Retag : {left right : List Strategy} → Corr left right → Annotated Head Operation Effect left →
    Annotated Head Operation Effect right → Prop where
  | ret {left right : List Strategy} {corr : Corr left right} (term : Tm Head (values left))
      (term' : Tm Head (values right)) (renamed : term' = rename corr.native term) :
      Retag corr (.ret term) (.ret term')
  | call {left right : List Strategy} {corr : Corr left right} (operation : Operation)
      (argument : Tm Head (values left)) (argument' : Tm Head (values right))
      (renamed : argument' = rename corr.native argument) :
      Retag corr (.call operation argument) (.call operation argument')
  | emit {left right : List Strategy} {corr : Corr left right} (effect : Effect)
      {next : Annotated Head Operation Effect left} {next' : Annotated Head Operation Effect right} :
      Retag corr next next' → Retag corr (.emit effect next) (.emit effect next')
  | choose {left right : List Strategy} {corr : Corr left right}
      {first second : Annotated Head Operation Effect left} {first' second' : Annotated Head Operation Effect right} :
      Retag corr first first' → Retag corr second second' → Retag corr (.choose first second) (.choose first' second')
  | use {left right : List Strategy} {corr : Corr left right} (position : Fin left.length)
      (position' : Fin right.length) (located : position' = corr.position position) :
      Retag corr (.use position) (.use position')
  | bind {left right : List Strategy} {corr : Corr left right} (strategy : Strategy)
      {bound : Annotated Head Operation Effect left} {bound' : Annotated Head Operation Effect right}
      {body : Annotated Head Operation Effect (strategy :: left)}
      {body' : Annotated Head Operation Effect (strategy :: right)} :
      Retag corr bound bound' → Retag (.same strategy corr) body body' →
        Retag corr (.bind strategy bound body) (.bind strategy bound' body')
  | pair {left right : List Strategy} {corr : Corr left right}
      {first : Annotated Head Operation Effect left} {first' : Annotated Head Operation Effect right}
      {body : Annotated Head Operation Effect (.value :: left)}
      {body' : Annotated Head Operation Effect (.value :: right)} :
      Retag corr first first' → Retag (.same .value corr) body body' →
        Retag corr (.pair first body) (.pair first' body')
  | needName {left right : List Strategy} {corr : Corr left right}
      {bound : Annotated Head Operation Effect left} {bound' : Annotated Head Operation Effect right}
      {body : Annotated Head Operation Effect (.need :: left)}
      {body' : Annotated Head Operation Effect (.name :: right)} :
      Constant primitive bound → Constant primitive bound' → Retag corr bound bound' →
        Retag (.swap .name corr) body body' → Retag corr (.bind .need bound body) (.bind .name bound' body')
  | needValue {left right : List Strategy} {corr : Corr left right}
      {bound : Annotated Head Operation Effect left} {bound' : Annotated Head Operation Effect right}
      {body : Annotated Head Operation Effect (.need :: left)}
      {body' : Annotated Head Operation Effect (.value :: right)} :
      Returns primitive bound → Returns primitive bound' → Retag corr bound bound' →
        Retag (.swap .value corr) body body' → Retag corr (.bind .need bound body) (.bind .value bound' body')

/-- Every program is alike itself. -/
theorem retag_refl : {scope : List Strategy} → (program : Annotated Head Operation Effect scope) →
    Retag primitive (Corr.refl scope) program program
  | scope, .ret term => .ret term term (by rw [rename_ext (Corr.refl_native scope)]; exact (rename_id term).symm)
  | scope, .call operation argument =>
      .call operation argument argument
        (by rw [rename_ext (Corr.refl_native scope)]; exact (rename_id argument).symm)
  | _, .emit effect next => .emit effect (retag_refl next)
  | _, .choose first second => .choose (retag_refl first) (retag_refl second)
  | scope, .use position => .use position position (Corr.refl_position scope position).symm
  | _, .bind strategy bound body => .bind strategy (retag_refl bound) (retag_refl body)
  | _, .pair first body => .pair (retag_refl first) (retag_refl body)

/-- **The fundamental lemma**: alike programs, under agreeing environments,
have agreeing programs and producers. -/
theorem retag_related {left right : List Strategy} {corr : Corr left right}
    {program : Annotated Head Operation Effect left} {program' : Annotated Head Operation Effect right}
    (retag : Retag primitive corr program program') :
    ∀ (links : List (Nat × Nat)) (pins : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
      (envL : ScopedNeed.Env Head Effect StableFault NativeFault m left)
      (envR : ScopedNeed.Env Head Effect StableFault NativeFault m right),
      EnvRel corr links pins envL envR →
        PairRel links pins (ScopedNeed.denote primitive program envL) (ScopedNeed.denote primitive program' envR) := by
  induction retag with
  | @ret left right corr term term' renamed =>
      intro links pins envL envR related
      subst renamed
      have equal : subst envR.native (rename corr.native term) = subst envL.native term := by
        rw [subst_rename]
        congr 1
        funext index
        exact (related.native index).symm
      simp only [ScopedNeed.denote, equal]
      exact PairRel.same (RunRel.pure links pins _)
  | @call left right corr operation argument argument' renamed =>
      intro links pins envL envR related
      subst renamed
      have equal : subst envR.native (rename corr.native argument) = subst envL.native argument := by
        rw [subst_rename]
        congr 1
        funext index
        exact (related.native index).symm
      simp only [ScopedNeed.denote, equal]
      exact PairRel.same (RunRel.pure links pins _)
  | @emit left right corr effect next next' _ ih =>
      intro links pins envL envR related
      exact PairRel.same ((ih links pins envL envR related).1.intent effect)
  | @choose left right corr first second first' second' _ _ ihFirst ihSecond =>
      intro links pins envL envR related
      have chosen := RunRel.choose (ihFirst links pins envL envR related).1 (ihSecond links pins envL envR related).1
      have program := RunRel.alloc (links := links) (pins := pins)
        (next := fun cell => ScopedNeed.demand cell
          (.choose (ScopedNeed.denote primitive first envL).1 (ScopedNeed.denote primitive second envL).1))
        (next' := fun cell => ScopedNeed.demand cell
          (.choose (ScopedNeed.denote primitive first' envR).1 (ScopedNeed.denote primitive second' envR).1))
        fun links' pins' store store' storeRel => RunRel.demand (RefRel.alloc chosen)
      exact ⟨program, RunRel.allocExtra chosen, chosen⟩
  | @use left right corr position position' located =>
      intro links pins envL envR related
      subst located
      simp only [ScopedNeed.denote]
      have located := locate_located corr position
      generalize locate left position = place at located ⊢
      generalize locate right (corr.position position) = place' at located ⊢
      cases located with
      | native index =>
          simp only [ScopedNeed.Env.meaning, related.native index]
          exact PairRel.same (RunRel.pure links pins _)
      | reference index => exact PairRel.same (RunRel.demand (related.references index))
      | producer index => exact related.producers index
      | site site =>
          obtain ⟨outcome, producer, pinned, meaning⟩ := related.sites site
          rw [meaning]
          simp only [ScopedNeed.Env.meaning]
          rw [producer]
          exact PairRel.same (RunRel.demandPinned pinned)
  | @bind left right corr strategy bound bound' body body' _ _ ihBound ihBody =>
      cases strategy with
      | value =>
          intro links pins envL envR related
          obtain ⟨_, _, producer⟩ := ihBound links pins envL envR related
          have step := RunRel.alloc (links := links) (pins := pins)
            (next := fun cell => (ScopedNeed.demand cell (ScopedNeed.denote primitive bound envL).2).bind
              (ScopedNeed.onValue fun value => (ScopedNeed.denote primitive body (envL.bindValue value)).1))
            (next' := fun cell => (ScopedNeed.demand cell (ScopedNeed.denote primitive bound' envR).2).bind
              (ScopedNeed.onValue fun value => (ScopedNeed.denote primitive body' (envR.bindValue value)).1))
            fun links' pins' store store' storeRel => by
              refine RunRel.bind (RunRel.demand (RefRel.alloc producer)) ?_
              intro answer
              cases answer with
              | value value =>
                  exact (ihBody _ _ (envL.bindValue value) (envR.bindValue value)
                    ((related.weaken ((List.prefix_append _ _).trans (List.prefix_append _ _))
                      (List.prefix_append _ _)).bindValue value)).1
              | stableFault fault => exact RunRel.pure _ _ _
              | retryableFault reason => exact RunRel.pure _ _ _
          exact PairRel.same step
      | need =>
          intro links pins envL envR related
          obtain ⟨_, _, producer⟩ := ihBound links pins envL envR related
          have step := RunRel.alloc (links := links) (pins := pins)
            (next := fun cell =>
              (ScopedNeed.denote primitive body (envL.bindNeed (cell, (ScopedNeed.denote primitive bound envL).2))).1)
            (next' := fun cell =>
              (ScopedNeed.denote primitive body' (envR.bindNeed (cell, (ScopedNeed.denote primitive bound' envR).2))).1)
            fun links' pins' store store' storeRel =>
              (ihBody _ _ _ _ ((related.weaken ((List.prefix_append _ _).trans (List.prefix_append _ _))
                (List.prefix_append _ _)).bindNeed (RefRel.alloc producer))).1
          exact PairRel.same step
      | name =>
          intro links pins envL envR related
          exact ihBody links pins _ _ (related.bindName (ihBound links pins envL envR related))
  | @pair left right corr first first' body body' _ _ ihFirst ihBody =>
      intro links pins envL envR related
      obtain ⟨_, _, producer⟩ := ihFirst links pins envL envR related
      have step := RunRel.alloc (links := links) (pins := pins)
        (next := fun cell => (ScopedNeed.demand cell (ScopedNeed.denote primitive first envL).2).bind
          (ScopedNeed.onValue fun value => Program.map (ScopedNeedNaturalSemantics.pairOutcome value)
            (ScopedNeed.denote primitive body (envL.bindValue value)).1))
        (next' := fun cell => (ScopedNeed.demand cell (ScopedNeed.denote primitive first' envR).2).bind
          (ScopedNeed.onValue fun value => Program.map (ScopedNeedNaturalSemantics.pairOutcome value)
            (ScopedNeed.denote primitive body' (envR.bindValue value)).1))
        fun links' pins' store store' storeRel => by
          refine RunRel.bind (RunRel.demand (RefRel.alloc producer)) ?_
          intro answer
          cases answer with
          | value value =>
              exact RunRel.map _ (ihBody _ _ (envL.bindValue value) (envR.bindValue value)
                ((related.weaken ((List.prefix_append _ _).trans (List.prefix_append _ _))
                  (List.prefix_append _ _)).bindValue value)).1
          | stableFault fault => exact RunRel.pure _ _ _
          | retryableFault reason => exact RunRel.pure _ _ _
      exact PairRel.same step
  | @needName left right corr bound bound' body body' constant constant' _ _ ihBound ihBody =>
      intro links pins envL envR related
      obtain ⟨outcome, boundEq⟩ := constant envL
      obtain ⟨outcome', boundEq'⟩ := constant' envR
      have boundRel := (ihBound links pins envL envR related).1
      rw [boundEq, boundEq'] at boundRel
      simp only [ScopedNeed.denote]
      rw [boundEq, boundEq']
      have bodyRel : ∀ (links' : List (Nat × Nat)) (pins' : List (Nat × ScopedNeed.Outcome Head StableFault NativeFault m))
          (store store' : ScopedNeed.Store Head StableFault NativeFault m),
          StoreRel (links ++ links') (pins ++ pins') store store' →
            PairRel (links ++ links') (pins ++ pins' ++ [(store.length, outcome)])
              (ScopedNeed.denote primitive body (envL.bindNeed (store.length, .pure outcome)))
              (ScopedNeed.denote primitive body' (envR.bindName (.pure outcome, .pure outcome))) :=
        fun links' pins' store store' _ =>
          ihBody _ _ _ _ ((related.weaken (List.prefix_append _ _)
            ((List.prefix_append _ _).trans (List.prefix_append _ _))).swapName
            (List.mem_append_right _ (List.mem_singleton_self _)))
      have first : RunRel links pins
          (ScopedNeed.alloc fun cell => (ScopedNeed.denote primitive body (envL.bindNeed (cell, .pure outcome))).1)
          (ScopedNeed.denote primitive body' (envR.bindName (.pure outcome', .pure outcome'))).1 :=
        RunRel.allocPin outcome fun links' pins' store store' storeRel => by
          have same := boundRel.pure_inj storeRel
          subst same
          exact (bodyRel links' pins' store store' storeRel).1
      have second : RunRel links pins
          (ScopedNeed.alloc fun cell => (ScopedNeed.denote primitive body (envL.bindNeed (cell, .pure outcome))).1)
          (ScopedNeed.denote primitive body' (envR.bindName (.pure outcome', .pure outcome'))).2 :=
        RunRel.allocPin outcome fun links' pins' store store' storeRel => by
          have same := boundRel.pure_inj storeRel
          subst same
          exact (bodyRel links' pins' store store' storeRel).2.1
      exact ⟨first, second, second⟩
  | @needValue left right corr bound bound' body body' returns returns' _ _ ihBound ihBody =>
      intro links pins envL envR related
      obtain ⟨value, boundEq⟩ := returns envL
      obtain ⟨value', boundEq'⟩ := returns' envR
      have boundRel := (ihBound links pins envL envR related).1
      rw [boundEq, boundEq'] at boundRel
      simp only [ScopedNeed.denote]
      rw [boundEq, boundEq']
      have step : RunRel links pins
          (ScopedNeed.alloc fun cell =>
            (ScopedNeed.denote primitive body (envL.bindNeed (cell, .pure (.value value)))).1)
          (ScopedNeed.alloc fun cell => (ScopedNeed.demand cell (.pure (.value value'))).bind
            (ScopedNeed.onValue fun value => (ScopedNeed.denote primitive body' (envR.bindValue value)).1)) :=
        RunRel.allocPin (.value value) fun links' pins' store store' storeRel => by
          have same := boundRel.pure_inj storeRel
          injection same with same
          subst same
          exact RunRel.allocDemandRight (.value value) (ihBody _ _ _ _
            ((related.weaken (List.prefix_append _ _)
              ((List.prefix_append _ _).trans (List.prefix_append _ _))).swapValue
              (List.mem_append_right _ (List.mem_singleton_self _)))).1
      exact PairRel.same step

/-! ## The laws -/

/-- **The strategy laws as a congruence, on elaborated code**: alike closed
programs have the same answers, under the inlining elaboration. -/
theorem retag_answers {program program' : Annotated Head Operation Effect []}
    (retag : Retag primitive .nil program program') (native : Sub Head 0 m) :
    ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate program Fin.elim0) native =
      ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate program' Fin.elim0) native := by
  rw [ScopedNeed.elaborate_answers, ScopedNeed.elaborate_answers]
  have related := (retag_related primitive retag [] [] ⟨native, Fin.elim0, Fin.elim0⟩ ⟨native, Fin.elim0, Fin.elim0⟩
    ⟨fun index => index.elim0, fun index => index.elim0, fun index => index.elim0, fun site => site.elim⟩).1
    [] [] [] [] [] (by simp [StoreRel])
  exact answers_of_forall₂ related

/-- And under the thunk elaboration. -/
theorem retag_thunks_answers {program program' : Annotated Head Operation Effect []}
    (retag : Retag primitive .nil program program') (native : Sub Head 0 m) :
    PolarizedValues.answers (Effect := Effect) primitive (StrategyThunks.elaborateThunks program) native =
      PolarizedValues.answers (Effect := Effect) primitive (StrategyThunks.elaborateThunks program') native := by
  rw [StrategyThunks.thunks_answers, StrategyThunks.thunks_answers]
  exact retag_answers primitive retag native

/-- **Reuse**: a need binder whose producer answers one outcome, a fault
included, may be rebound by name. -/
theorem need_name_answers {bound : Annotated Head Operation Effect []} (constant : Constant primitive bound)
    {body : Annotated Head Operation Effect [.need]} {body' : Annotated Head Operation Effect [.name]}
    (retag : Retag primitive (.swap .name .nil) body body') (native : Sub Head 0 m) :
    ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate (.bind .need bound body) Fin.elim0) native =
      ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate (.bind .name bound body') Fin.elim0) native :=
  retag_answers primitive (.needName constant constant (retag_refl primitive bound) retag) native

/-- **Discard**: a need binder whose producer answers one value may be
rebound by value. -/
theorem need_value_answers {bound : Annotated Head Operation Effect []} (returns : Returns primitive bound)
    {body : Annotated Head Operation Effect [.need]} {body' : Annotated Head Operation Effect [.value]}
    (retag : Retag primitive (.swap .value .nil) body body') (native : Sub Head 0 m) :
    ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate (.bind .need bound body) Fin.elim0) native =
      ScopedNeed.answers (Effect := Effect) primitive (ScopedNeed.elaborate (.bind .value bound body') Fin.elim0) native :=
  retag_answers primitive (.needValue returns returns (retag_refl primitive bound) retag) native

#print axioms retag_related
#print axioms retag_answers

/-! ## Producers of one outcome -/

theorem constant_ret {scope : List Strategy} (term : Tm Head (values scope)) :
    Constant (Effect := Effect) primitive (Annotated.ret (Operation := Operation) term) :=
  fun env => ⟨.value (subst env.native term), rfl⟩

theorem constant_call {scope : List Strategy} (operation : Operation) (argument : Tm Head (values scope)) :
    Constant (Effect := Effect) primitive (Annotated.call operation argument) :=
  fun env => ⟨ScopedNeedMachine.liftOutcome (primitive operation (subst env.native argument)), rfl⟩

theorem returns_ret {scope : List Strategy} (term : Tm Head (values scope)) :
    Returns (Effect := Effect) primitive (Annotated.ret (Operation := Operation) term) :=
  fun env => ⟨subst env.native term, rfl⟩

/-! ## Examples -/

namespace Examples

open ScopedNeedNaturalSemantics.Examples (ExampleOperation)
open ScopedNeed.Examples (coin examplePrimitive twice twice_need twice_name)

/-- Bind a producer by a strategy, read it twice and pair the two answers. -/
def twiceOf (strategy : Strategy) (bound : Annotated Nat ExampleOperation Nat []) :
    Annotated Nat ExampleOperation Nat [] :=
  .bind strategy bound (.pair (.use 0) (.use 1))

/-- Bind a producer by a strategy and never read it. -/
def unusedOf (strategy : Strategy) (bound : Annotated Nat ExampleOperation Nat []) :
    Annotated Nat ExampleOperation Nat [] :=
  .bind strategy bound (.ret (.head 3))

/-- A raising call. -/
def raise : Annotated Nat ExampleOperation Nat [] := .call .stable (.head 0)

theorem raiseTwice_answers :
    ScopedNeed.answers (Effect := Nat) examplePrimitive (ScopedNeed.elaborate (twiceOf .need raise) Fin.elim0) ids =
      [.stableFault 11] := by
  decide

/-- **Reuse with a fault**: a raising call bound by need and read twice may
be rebound by name. -/
theorem raiseTwice_reuse :
    ScopedNeed.answers (Effect := Nat) examplePrimitive (ScopedNeed.elaborate (twiceOf .need raise) Fin.elim0) ids =
      ScopedNeed.answers (Effect := Nat) examplePrimitive (ScopedNeed.elaborate (twiceOf .name raise) Fin.elim0) ids :=
  need_name_answers examplePrimitive (constant_call examplePrimitive _ _) (.pair (.use 0 0 rfl) (.use 1 1 rfl)) ids

/-- And under the thunk elaboration. -/
theorem raiseTwice_reuse_thunks :
    PolarizedValues.answers (Effect := Nat) examplePrimitive (StrategyThunks.elaborateThunks (twiceOf .need raise)) ids =
      PolarizedValues.answers (Effect := Nat) examplePrimitive (StrategyThunks.elaborateThunks (twiceOf .name raise))
        ids :=
  retag_thunks_answers examplePrimitive
    (.needName (constant_call examplePrimitive _ _) (constant_call examplePrimitive _ _)
      (retag_refl examplePrimitive raise) (.pair (.use 0 0 rfl) (.use 1 1 rfl))) ids

/-- **Discard with a value**: a value bound by need and never read may be
rebound by value. -/
theorem unusedValue_discard :
    ScopedNeed.answers (Effect := Nat) examplePrimitive
        (ScopedNeed.elaborate (unusedOf .need (.ret (.head 1))) Fin.elim0) ids =
      ScopedNeed.answers (Effect := Nat) examplePrimitive
        (ScopedNeed.elaborate (unusedOf .value (.ret (.head 1))) Fin.elim0) ids :=
  need_value_answers examplePrimitive (returns_ret examplePrimitive _) (.ret _ _ rfl) ids

/-- **Discard with a value read twice.** -/
theorem valueTwice_discard :
    ScopedNeed.answers (Effect := Nat) examplePrimitive
        (ScopedNeed.elaborate (twiceOf .need (.ret (.head 1))) Fin.elim0) ids =
      ScopedNeed.answers (Effect := Nat) examplePrimitive
        (ScopedNeed.elaborate (twiceOf .value (.ret (.head 1))) Fin.elim0) ids :=
  need_value_answers examplePrimitive (returns_ret examplePrimitive _) (.pair (.use 0 0 rfl) (.use 1 1 rfl)) ids

/-- **Negative: a raise is not discardable.**  A raising call bound by need
and never read is never run; bound by value, it raises.  So the discard law
needs a producer that answers a value. -/
theorem raise_not_discardable :
    ScopedNeed.answers (Effect := Nat) examplePrimitive
        (ScopedNeed.elaborate (unusedOf .need raise) Fin.elim0) ids = [.value (.head 3)] ∧
      ScopedNeed.answers (Effect := Nat) examplePrimitive
        (ScopedNeed.elaborate (unusedOf .value raise) Fin.elim0) ids = [.stableFault 11] ∧
      ¬ Returns (Effect := Nat) examplePrimitive raise := by
  refine ⟨by decide, by decide, fun returns => ?_⟩
  obtain ⟨value, equal⟩ := returns ⟨ids, Fin.elim0, Fin.elim0⟩
  simp [raise, ScopedNeed.denote, ScopedNeedNaturalSemantics.Examples.primitive, ScopedNeedMachine.liftOutcome] at equal

/-- **Negative: reuse needs one outcome.**  A choice bound by need and read
twice gives two pairs, by name four (`twice_need`, `twice_name`): a choice
answers two outcomes. -/
theorem coin_not_constant : ¬ Constant (Effect := Nat) examplePrimitive (coin (scope := [])) := by
  intro constant
  obtain ⟨outcome, equal⟩ := constant ⟨ids, Fin.elim0, Fin.elim0⟩
  simp [coin, ScopedNeed.denote, ScopedNeed.alloc] at equal

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.StrategyLaws
