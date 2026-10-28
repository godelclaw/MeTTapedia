import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitProtocol
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# Parked `await` and `whenever`: the wait index, and the fairness each guard needs

A reactive firing **parks** until its guard holds: `await X` fires once, `whenever X` fires on
each enabling. A runtime does not re-match every parked firing after every commit. It keeps a
**wait index**: a parked firing is *awake* (it will be re-matched) or *asleep* (its last re-match
found no row), and a commit wakes the parked firings that the index associates with it. This module
gives that runtime a semantics over the commits of `Commits` and proves what keeps happening.

## The reactive system (`reactive`)

A parked firing (`Parked`) has the ground rows its guard can fire, the region its guard reads (its
key in the index), and whether it is persistent. Its **guard** holds when some row is fireable: the
row's takes and keeps are present, nothing is both, its predicate queries hold (`Matches`), and its
fresh identities are unborn. The steps are an outside commit (`env`), running an awake parked firing
with one of its fireable rows (`run`), putting an awake firing to sleep when its guard fails
(`sleep`), and the idle step. A commit wakes the parked firings that the index selects for it.

## The wait index loses no wakeup

* An index **loses no wakeup** for a parked firing (`NoLostWakeup`) when every commit that turns its
  guard from false to true is one the index wakes it for.
* **The region index loses no wakeup** (`regionIndex_noLostWakeup`): wake a firing for every commit
  that writes into its region, provided its rows live in its region (`InRegion`). This is K's
  `woken_requires_write` applied to the guard.
* **The kind index loses no wakeup** (`kindIndex_noLostWakeup`): a firing whose rows query nothing
  is woken only by makes in its region (`positive_woken_by_make`); others by any write.
* **Invariant** (`WakeInv`, `wakeInv_next`, `Run.wakeInv`): with an index that loses no wakeup,
  every parked firing whose guard holds is awake, in every reachable state.

## What keeps happening

* **Strong fairness wakes and fires every parked `await` whose guard holds infinitely often**
  (`await_fires`), and fires a `whenever` infinitely often (`whenever_fires_often`). The fairness is
  that of the scheduler's choice among awake firings (the task `runTask p`).
* **Weak fairness suffices for a stable guard** (`await_fires_of_stable`): once the guard holds it
  keeps holding until the firing runs. A row without predicate queries stays fireable across any
  commit that does not take what it uses or claim its fresh identities (`fireable_after_commit`),
  so a guard without competitors (the only receiver on a private channel, a reader of facts nobody
  takes) needs only weak fairness (`await_fires_of_sole_consumer`).
* Strong fairness is implementable: the aging scheduler of `FairRuns` gives a strongly fair run of
  every reactive system with finitely many parked firings (`exists_stronglyFair_reactive_run`).

## Controls

* `Controls.flicker_weaklyFair`, `Controls.flicker_await_never_fires`: an `await` that takes a
  token competes with a `whenever` that holds and releases it. The run in which the whenever toggles
  forever is weakly fair for both and never fires the await, whose guard holds at every other
  step: **weak fairness is not enough for a guard that flickers.**
* `Controls.flicker_stronglyFair_fires`: in every strongly fair run of the same system the await
  fires.
* `Controls.makesIndex_loses_wakeup`: an index that wakes a firing only for makes in its region is
  wrong for an absence guard. "Add an output unless locked" sleeps while the lock is present; the
  lock is taken; the index does not wake it; its guard then holds forever, and it never runs in a run
  that is strongly fair, because it is never awake. With the region index the same commit wakes it
  (`Controls.regionIndex_wakes`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Rows and guards -/

/-- What a row needs from the store: its takes and keeps present, nothing both, its predicate
queries holding. Freshness is the allocator's and is checked against the identities ever born. -/
structure Matches (label : O → R) (store : Finset O) (c : Commit O R) : Prop where
  taken_subset : c.taken ⊆ store
  kept_subset : c.kept ⊆ store
  apart : Disjoint c.taken c.kept
  queries_hold : ∀ read ∈ c.queries, read.Holds label store

/-- A row is fireable: it matches and its fresh identities are unborn. -/
abbrev Fireable (label : O → R) (store born : Finset O) (c : Commit O R) : Prop :=
  Matches label store c ∧ Disjoint c.made born

omit [DecidableEq O] in
/-- A fireable row is an enabled commit, when every live occurrence is born. -/
theorem Fireable.enabled {label : O → R} {store born : Finset O} {c : Commit O R}
    (fireable : Fireable label store born c) (sub : store ⊆ born) : Enabled label store c where
  taken_subset := fireable.1.taken_subset
  kept_subset := fireable.1.kept_subset
  apart := fireable.1.apart
  fresh := Finset.disjoint_of_subset_right sub fireable.2
  queries_hold := fireable.1.queries_hold

/-- A parked firing: the rows its guard can fire, the region its guard reads, and whether it is
persistent (`whenever`) or fires once (`await`). -/
structure Parked (O : Type u) (R : Type v) where
  rows : Set (Commit O R)
  region : R → Bool
  persistent : Bool

/-- The guard of a parked firing holds: some row is fireable. -/
abbrev Guard (label : O → R) (p : Parked O R) (store born : Finset O) : Prop :=
  ∃ c ∈ p.rows, Fireable label store born c

/-- The rows of a parked firing live in its region: what they take and keep, and the regions of
their predicate queries. -/
def InRegion (label : O → R) (p : Parked O R) : Prop :=
  ∀ c ∈ p.rows, (∀ o ∈ c.taken ∪ c.kept, p.region (label o) = true) ∧
    ∀ read ∈ c.queries, ∀ r, read.region r = true → p.region r = true

/-- The rows of a parked firing have no predicate queries. -/
def PositiveRows (p : Parked O R) : Prop := ∀ c ∈ p.rows, c.queries = []

/-- A row in a region matches a store exactly when it matches the store's part in the region. -/
theorem matches_regionOf_iff {label : O → R} {store : Finset O} {region : R → Bool}
    {c : Commit O R} (uses : ∀ o ∈ c.taken ∪ c.kept, region (label o) = true)
    (reads : ∀ read ∈ c.queries, ∀ r, read.region r = true → region r = true) :
    Matches label store c ↔ Matches label (regionOf label store region) c := by
  have subsetIff : ∀ X : Finset O, (∀ o ∈ X, region (label o) = true) →
      (X ⊆ store ↔ X ⊆ regionOf label store region) := by
    intro X inside
    constructor
    · intro sub o member
      exact mem_regionOf.mpr ⟨sub member, inside o member⟩
    · intro sub o member
      exact (mem_regionOf.mp (sub member)).1
  have readIff : ∀ read ∈ c.queries,
      regionOf label (regionOf label store region) read.region = regionOf label store read.region := by
    intro read member
    ext o
    simp only [mem_regionOf]
    constructor
    · rintro ⟨⟨inStore, _⟩, inRead⟩
      exact ⟨inStore, inRead⟩
    · rintro ⟨inStore, inRead⟩
      exact ⟨⟨inStore, reads read member _ inRead⟩, inRead⟩
  have takenInside : ∀ o ∈ c.taken, region (label o) = true :=
    fun o member => uses o (Finset.mem_union_left _ member)
  have keptInside : ∀ o ∈ c.kept, region (label o) = true :=
    fun o member => uses o (Finset.mem_union_right _ member)
  constructor
  · intro m
    refine ⟨(subsetIff _ takenInside).1 m.taken_subset, (subsetIff _ keptInside).1 m.kept_subset,
      m.apart, fun read member => ?_⟩
    unfold PredicateQuery.Holds
    rw [readIff read member]
    exact m.queries_hold read member
  · intro m
    refine ⟨(subsetIff _ takenInside).2 m.taken_subset, (subsetIff _ keptInside).2 m.kept_subset,
      m.apart, fun read member => ?_⟩
    have := m.queries_hold read member
    unfold PredicateQuery.Holds at this ⊢
    rwa [readIff read member] at this

/-- **A row without predicate queries stays fireable** across a commit that takes nothing it uses
and claims none of its fresh identities. -/
theorem fireable_after_commit {label : O → R} {store born : Finset O} {c d : Commit O R}
    (fireable : Fireable label store born c) (positive : c.queries = [])
    (untouched : Disjoint d.taken (c.taken ∪ c.kept)) (ownIds : Disjoint d.made c.made) :
    Fireable label (fire store d) (born ∪ d.made) c := by
  have survives : ∀ o ∈ c.taken ∪ c.kept, o ∈ store → o ∈ fire store d := fun o used inStore =>
    mem_fire.mpr (Or.inl ⟨inStore, fun taken => Finset.disjoint_left.mp untouched taken used⟩)
  refine ⟨⟨fun o taken => survives o (Finset.mem_union_left _ taken) (fireable.1.taken_subset taken),
      fun o kept => survives o (Finset.mem_union_right _ kept) (fireable.1.kept_subset kept),
      fireable.1.apart, by simp [positive]⟩, ?_⟩
  exact Finset.disjoint_union_right.mpr ⟨fireable.2, ownIds.symm⟩

/-! ## Wait indexes -/

/-- An index **loses no wakeup** for a parked firing: every commit that turns its guard from false to
true is one the index wakes it for. -/
def NoLostWakeup (label : O → R) (index : Parked O R → Commit O R → Prop) (p : Parked O R) : Prop :=
  ∀ (store born : Finset O) (d : Commit O R), store ⊆ born → Enabled label store d →
    Disjoint d.made born → ¬ Guard label p store born →
      Guard label p (fire store d) (born ∪ d.made) → index p d

/-- The region index: wake a firing for every commit that writes into its region (`Writes`). -/
def regionIndex (label : O → R) (p : Parked O R) (d : Commit O R) : Prop :=
  Writes label d p.region

/-- The kind index: a firing whose rows have no predicate queries is woken by makes in its region;
any
other by any write in its region. -/
def kindIndex (label : O → R) (p : Parked O R) (d : Commit O R) : Prop :=
  (PositiveRows p ∧ ∃ o ∈ d.made, p.region (label o) = true) ∨
    (¬ PositiveRows p ∧ regionIndex label p d)

/-- The makes index: wake a firing only for makes in its region. Right for positive guards, wrong
for absence guards (`Controls.makesIndex_loses_wakeup`). -/
def makesIndex (label : O → R) (p : Parked O R) (d : Commit O R) : Prop :=
  ∃ o ∈ d.made, p.region (label o) = true

/-- The test a guard applies to the part of the store in its region, with fixed born identities. -/
def regionTest (label : O → R) (p : Parked O R) (born : Finset O) (X : Finset O) : Prop :=
  ∃ c ∈ p.rows, Matches label X c ∧ Disjoint c.made born

theorem regionTest_iff_guard {label : O → R} {p : Parked O R} (inRegion : InRegion label p)
    {store born : Finset O} :
    regionTest label p born (regionOf label store p.region) ↔ Guard label p store born := by
  constructor
  · rintro ⟨c, row, m, fresh⟩
    exact ⟨c, row, (matches_regionOf_iff (inRegion c row).1 (inRegion c row).2).2 m, fresh⟩
  · rintro ⟨c, row, m, fresh⟩
    exact ⟨c, row, (matches_regionOf_iff (inRegion c row).1 (inRegion c row).2).1 m, fresh⟩

theorem not_regionTest_of_not_guard {label : O → R} {p : Parked O R} (inRegion : InRegion label p)
    {store born : Finset O} {extra : Finset O} (before : ¬ Guard label p store born) :
    ¬ regionTest label p (born ∪ extra) (regionOf label store p.region) := by
  rintro ⟨c, row, m, fresh⟩
  exact before ⟨c, row, (matches_regionOf_iff (inRegion c row).1 (inRegion c row).2).2 m,
    Finset.disjoint_of_subset_right Finset.subset_union_left fresh⟩

/-- **The region index loses no wakeup.** -/
theorem regionIndex_noLostWakeup {label : O → R} {p : Parked O R} (inRegion : InRegion label p) :
    NoLostWakeup label (regionIndex label) p := by
  intro store born d _ _ _ before after
  exact woken_requires_write (test := regionTest label p (born ∪ d.made))
    (not_regionTest_of_not_guard inRegion before) ((regionTest_iff_guard inRegion).2 after)

/-- **The kind index loses no wakeup.** -/
theorem kindIndex_noLostWakeup {label : O → R} {p : Parked O R} (inRegion : InRegion label p) :
    NoLostWakeup label (kindIndex label) p := by
  intro store born d sub enabled fresh before after
  by_cases positive : PositiveRows p
  · refine Or.inl ⟨positive, positive_woken_by_make (test := regionTest label p (born ∪ d.made)) ?_
      (not_regionTest_of_not_guard inRegion before) ((regionTest_iff_guard inRegion).2 after)⟩
    rintro small large le ⟨c, row, m, freshC⟩
    exact ⟨c, row, ⟨m.taken_subset.trans le, m.kept_subset.trans le, m.apart,
      by simp [positive c row]⟩, freshC⟩
  · exact Or.inr ⟨positive, regionIndex_noLostWakeup inRegion store born d sub enabled fresh before after⟩

/-! ## The reactive system -/

/-- The runtime state: the store, every identity ever born, the parked firings, the awake ones. -/
structure RState (O : Type u) (P : Type w) where
  store : Finset O
  born : Finset O
  parked : Set P
  awake : Set P

/-- A step: an outside commit, running a parked firing with one of its rows, putting a firing to
sleep, or idling. -/
inductive RLabel (O : Type u) (R : Type v) (P : Type w) where
  | env (d : Commit O R)
  | run (p : P) (c : Commit O R)
  | sleep (p : P)
  | idle

variable {P : Type w}

section System

variable (label : O → R) (proc : P → Parked O R) (index : Parked O R → Commit O R → Prop)
  (envOK : Commit O R → Prop)

/-- The parked firings a commit wakes. -/
def woken (σ : RState O P) (d : Commit O R) : Set P := {q | q ∈ σ.parked ∧ index (proc q) d}

/-- When a step may happen. -/
def rAllowed (σ : RState O P) : RLabel O R P → Prop
  | .env d => envOK d ∧ Enabled label σ.store d ∧ Disjoint d.made σ.born
  | .run p c => p ∈ σ.parked ∧ p ∈ σ.awake ∧ c ∈ (proc p).rows ∧ Fireable label σ.store σ.born c
  | .sleep p => p ∈ σ.awake ∧ ¬ Guard label (proc p) σ.store σ.born
  | .idle => True

/-- What a step does. -/
def rNext (σ : RState O P) : RLabel O R P → RState O P
  | .env d => ⟨fire σ.store d, σ.born ∪ d.made, σ.parked, σ.awake ∪ woken proc index σ d⟩
  | .run p c => ⟨fire σ.store c, σ.born ∪ c.made,
      if (proc p).persistent then σ.parked else σ.parked \ {p},
      if (proc p).persistent then σ.awake ∪ woken proc index σ c
      else (σ.awake ∪ woken proc index σ c) \ {p}⟩
  | .sleep p => ⟨σ.store, σ.born, σ.parked, σ.awake \ {p}⟩
  | .idle => σ

/-- The reactive system. -/
def reactive : LTS (RState O P) (RLabel O R P) := ⟨rAllowed label proc envOK, rNext proc index⟩

@[simp] theorem reactive_next : (reactive label proc index envOK).next = rNext proc index := rfl

@[simp] theorem reactive_allowed :
    (reactive label proc index envOK).Allowed = rAllowed label proc envOK := rfl

/-- The task "run parked firing `p`". -/
def runTask (p : P) : RLabel O R P → Prop
  | .run q _ => q = p
  | _ => False

/-- The invariant of the wait index: every live occurrence is born, and every parked firing whose
guard holds is awake. -/
structure WakeInv (σ : RState O P) : Prop where
  store_born : σ.store ⊆ σ.born
  awake_of_guard : ∀ q ∈ σ.parked, Guard label (proc q) σ.store σ.born → q ∈ σ.awake

end System

section Invariant

variable {label : O → R} {proc : P → Parked O R} {index : Parked O R → Commit O R → Prop}
  {envOK : Commit O R → Prop}

theorem fire_subset_born {store born : Finset O} {d : Commit O R} (sub : store ⊆ born) :
    fire store d ⊆ born ∪ d.made := by
  intro o member
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact Finset.mem_union_left _ (sub inStore)
  · exact Finset.mem_union_right _ made

/-- After a commit, a parked firing whose guard holds was awake or is woken. -/
theorem awake_after_commit (adequate : ∀ q, NoLostWakeup label index (proc q)) {σ : RState O P}
    (inv : WakeInv label proc σ) {d : Commit O R} (enabled : Enabled label σ.store d)
    (fresh : Disjoint d.made σ.born) {q : P} (parked : q ∈ σ.parked)
    (after : Guard label (proc q) (fire σ.store d) (σ.born ∪ d.made)) :
    q ∈ σ.awake ∪ woken proc index σ d := by
  by_cases before : Guard label (proc q) σ.store σ.born
  · exact Or.inl (inv.awake_of_guard q parked before)
  · exact Or.inr ⟨parked, adequate q σ.store σ.born d inv.store_born enabled fresh before after⟩

/-- **Every step keeps the wait-index invariant**, for an index that loses no wakeup. -/
theorem wakeInv_next (adequate : ∀ q, NoLostWakeup label index (proc q)) {σ : RState O P}
    (inv : WakeInv label proc σ) {a : RLabel O R P} (allowed : rAllowed label proc envOK σ a) :
    WakeInv label proc (rNext proc index σ a) := by
  cases a with
  | env d =>
      obtain ⟨_, enabled, fresh⟩ := allowed
      exact ⟨fire_subset_born inv.store_born,
        fun q parked after => awake_after_commit adequate inv enabled fresh parked after⟩
  | run p c =>
      obtain ⟨_, _, _, fireable⟩ := allowed
      have enabled := fireable.enabled inv.store_born
      refine ⟨fire_subset_born inv.store_born, fun q parked after => ?_⟩
      simp only [rNext] at parked after ⊢
      cases persistent : (proc p).persistent
      · simp only [persistent, Bool.false_eq_true, if_false] at parked ⊢
        obtain ⟨parkedOld, notP⟩ := parked
        exact ⟨awake_after_commit adequate inv enabled fireable.2 parkedOld after, notP⟩
      · simp only [persistent, if_true] at parked ⊢
        exact awake_after_commit adequate inv enabled fireable.2 parked after
  | sleep p =>
      obtain ⟨_, noGuard⟩ := allowed
      refine ⟨inv.store_born, fun q parked guard => ⟨inv.awake_of_guard q parked guard, ?_⟩⟩
      rintro rfl
      exact noGuard guard
  | idle => exact inv

/-- **The invariant holds along every run that starts in it.** -/
theorem Run.wakeInv (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) :
    ∀ n, WakeInv label proc (r.state n) := by
  intro n
  induction n with
  | zero => exact init
  | succ n ih =>
      rw [r.step n]
      exact wakeInv_next adequate ih (r.allowed n)

/-- A parked firing stays parked unless it runs. -/
theorem parked_next {σ : RState O P} {a : RLabel O R P} {p : P} (parked : p ∈ σ.parked)
    (notRun : ¬ runTask p a) : p ∈ (rNext proc index σ a).parked := by
  cases a with
  | env d => exact parked
  | run q c =>
      have different : q ≠ p := notRun
      simp only [rNext]
      split_ifs
      · exact parked
      · exact ⟨parked, fun same => different (Set.mem_singleton_iff.mp same).symm⟩
  | sleep q => exact parked
  | idle => exact parked

/-- A persistent firing stays parked. -/
theorem parked_next_of_persistent {σ : RState O P} {a : RLabel O R P} {p : P}
    (persistent : (proc p).persistent = true) (parked : p ∈ σ.parked) :
    p ∈ (rNext proc index σ a).parked := by
  by_cases runs : runTask p a
  · cases a with
    | run q c =>
        have same : q = p := runs
        subst same
        simp only [rNext, persistent, if_true]
        exact parked
    | env d => exact absurd runs id
    | sleep q => exact absurd runs id
    | idle => exact absurd runs id
  · exact parked_next parked runs

/-- A parked firing that never runs stays parked forever. -/
theorem Run.parked_forever (r : Run (reactive label proc index envOK)) {p : P} {N : ℕ}
    (parked : p ∈ (r.state N).parked) (never : ∀ n ≥ N, ¬ runTask p (r.label n)) :
    ∀ n ≥ N, p ∈ (r.state n).parked := by
  intro n le
  induction n, le using Nat.le_induction with
  | base => exact parked
  | succ n le ih =>
      rw [r.step n]
      exact parked_next ih (never n le)

/-- A parked firing whose guard holds, under the invariant, can run. -/
theorem runTask_enabled {σ : RState O P} (inv : WakeInv label proc σ) {p : P}
    (parked : p ∈ σ.parked) (guard : Guard label (proc p) σ.store σ.born) :
    (reactive label proc index envOK).TaskEnabled (runTask p) σ := by
  obtain ⟨c, row, fireable⟩ := guard
  exact ⟨.run p c, rfl, parked, inv.awake_of_guard p parked ⟨c, row, fireable⟩, row, fireable⟩

end Invariant

/-! ## What keeps happening -/

section Liveness

variable {label : O → R} {proc : P → Parked O R} {index : Parked O R → Commit O R → Prop}
  {envOK : Commit O R → Prop}

/-- **Strong fairness wakes and fires every parked `await` whose guard holds infinitely often.** -/
theorem await_fires (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    (parked : p ∈ (r.state 0).parked) (fair : r.StronglyFair (runTask p))
    (often : InfinitelyOften fun n => Guard label (proc p) (r.state n).store (r.state n).born) :
    ∃ n, runTask p (r.label n) := by
  by_contra never
  push Not at never
  have stays := Run.parked_forever r parked fun n _ => never n
  have enabledOften : InfinitelyOften fun n =>
      (reactive label proc index envOK).TaskEnabled (runTask p) (r.state n) := by
    intro N
    obtain ⟨n, le, guard⟩ := often N
    exact ⟨n, le, runTask_enabled (Run.wakeInv adequate r init n) (stays n (Nat.zero_le n)) guard⟩
  obtain ⟨n, _, fires⟩ := fair enabledOften 0
  exact never n fires

/-- **Strong fairness fires a parked `whenever` infinitely often when its guard holds infinitely
often.** -/
theorem whenever_fires_often (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    (persistent : (proc p).persistent = true) (parked : p ∈ (r.state 0).parked)
    (fair : r.StronglyFair (runTask p))
    (often : InfinitelyOften fun n => Guard label (proc p) (r.state n).store (r.state n).born) :
    InfinitelyOften fun n => runTask p (r.label n) := by
  have stays : ∀ n, p ∈ (r.state n).parked := by
    intro n
    induction n with
    | zero => exact parked
    | succ n ih => rw [r.step n]; exact parked_next_of_persistent persistent ih
  apply fair
  intro N
  obtain ⟨n, le, guard⟩ := often N
  exact ⟨n, le, runTask_enabled (Run.wakeInv adequate r init n) (stays n) guard⟩

/-- **Weak fairness suffices for a stable guard**: a guard that holds at `N` and keeps holding until
the firing runs. -/
theorem await_fires_of_stable (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    {N : ℕ} (parked : p ∈ (r.state N).parked) (fair : r.WeaklyFair (runTask p))
    (holds : Guard label (proc p) (r.state N).store (r.state N).born)
    (stable : ∀ n ≥ N, Guard label (proc p) (r.state n).store (r.state n).born →
      ¬ runTask p (r.label n) → Guard label (proc p) (r.state (n + 1)).store (r.state (n + 1)).born) :
    ∃ n ≥ N, runTask p (r.label n) := by
  apply fair.fires N
  intro n le notYet
  have both : Guard label (proc p) (r.state n).store (r.state n).born ∧ p ∈ (r.state n).parked := by
    induction n, le using Nat.le_induction with
    | base => exact ⟨holds, parked⟩
    | succ n le ih =>
        have before := ih fun m lo hi => notYet m lo (by omega)
        have notRun := notYet n le (Nat.lt_succ_self n)
        refine ⟨stable n le before.1 notRun, ?_⟩
        rw [r.step n]
        exact parked_next before.2 notRun
  exact runTask_enabled (Run.wakeInv adequate r init n) both.2 both.1

/-- The commit a step performs, if any. -/
def performed : RLabel O R P → Option (Commit O R)
  | .env d => some d
  | .run _ c => some c
  | _ => none

/-- **A guard without competitors needs only weak fairness.** A row of a parked `await` that has no
predicate queries is fireable at `N`, and until the firing runs no step takes what the row uses
or claims its fresh identities; then the firing runs. -/
theorem await_fires_of_sole_consumer (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    {N : ℕ} (parked : p ∈ (r.state N).parked) (fair : r.WeaklyFair (runTask p)) {c : Commit O R}
    (row : c ∈ (proc p).rows) (positive : c.queries = [])
    (fireable : Fireable label (r.state N).store (r.state N).born c)
    (noCompetition : ∀ n ≥ N, ¬ runTask p (r.label n) → ∀ d, performed (r.label n) = some d →
      Disjoint d.taken (c.taken ∪ c.kept) ∧ Disjoint d.made c.made) :
    ∃ n ≥ N, runTask p (r.label n) := by
  have stays : ∀ n ≥ N, (∀ m, N ≤ m → m < n → ¬ runTask p (r.label m)) →
      Fireable label (r.state n).store (r.state n).born c := by
    intro n le
    induction n, le using Nat.le_induction with
    | base => exact fun _ => fireable
    | succ n le ih =>
        intro notYet
        have before := ih fun m lo hi => notYet m lo (by omega)
        have notRun := notYet n le (Nat.lt_succ_self n)
        rw [r.step n]
        cases labelIs : r.label n with
        | env d =>
            obtain ⟨untouched, ownIds⟩ := noCompetition n le notRun d (by rw [labelIs]; rfl)
            exact fireable_after_commit before positive untouched ownIds
        | run q d =>
            obtain ⟨untouched, ownIds⟩ := noCompetition n le notRun d (by rw [labelIs]; rfl)
            exact fireable_after_commit before positive untouched ownIds
        | sleep q => exact before
        | idle => exact before
  have parkedUntil : ∀ n ≥ N, (∀ m, N ≤ m → m < n → ¬ runTask p (r.label m)) →
      p ∈ (r.state n).parked := by
    intro n le
    induction n, le using Nat.le_induction with
    | base => exact fun _ => parked
    | succ n le ih =>
        intro notYet
        rw [r.step n]
        exact parked_next (ih fun m lo hi => notYet m lo (by omega)) (notYet n le (Nat.lt_succ_self n))
  apply fair.fires N
  intro n le notYet
  exact runTask_enabled (Run.wakeInv adequate r init n) (parkedUntil n le notYet)
    ⟨c, row, stays n le notYet⟩

omit [DecidableEq O] in
/-- The reactive system never blocks: the idle step is always allowed. -/
theorem reactive_nonBlocking [DecidableEq O] (label : O → R) (proc : P → Parked O R)
    (index : Parked O R → Commit O R → Prop) (envOK : Commit O R → Prop) :
    (reactive label proc index envOK).NonBlocking :=
  fun _ => ⟨.idle, trivial⟩

/-- **Strong fairness is implementable**: with finitely many parked firings, the aging scheduler
gives a run that is strongly fair for running every one of them. -/
theorem exists_stronglyFair_reactive_run [Fintype P] [DecidableEq P] (label : O → R)
    (proc : P → Parked O R) (index : Parked O R → Commit O R → Prop) (envOK : Commit O R → Prop)
    (σ : RState O P) :
    ∃ r : Run (reactive label proc index envOK), r.state 0 = σ ∧ ∀ p, r.StronglyFair (runTask p) :=
  exists_stronglyFair_run (fun p => runTask p) (reactive_nonBlocking label proc index envOK) σ

end Liveness

/-! ## Controls -/

namespace Controls

/-! ### A flickering guard: a token held and released -/

/-- Where a token occurrence is: free or held. -/
inductive Spot where
  | free
  | held
  deriving DecidableEq

/-- Even identities are free tokens, odd ones held tokens. -/
def spot (o : ℕ) : Spot := if o % 2 = 0 then .free else .held

/-- The free region. -/
def isFree : Spot → Bool
  | .free => true
  | .held => false

/-- The toggler's step at identity `k`: take it and make the next identity. -/
def toggle (k : ℕ) : Commit ℕ Spot := ⟨{k}, ∅, {k + 1}, []⟩

/-- The await's row at a free token `2k`: take it. -/
def grab (k : ℕ) : Commit ℕ Spot := ⟨{2 * k}, ∅, ∅, []⟩

/-- `true` is the await that takes a free token; `false` is the whenever that holds and releases
the token. -/
def flickerProc : Bool → Parked ℕ Spot
  | true => ⟨{c | ∃ k, c = grab k}, isFree, false⟩
  | false => ⟨{c | ∃ k, c = toggle k}, fun _ => true, true⟩

/-- The flicker system, with the region index and no outside commits. -/
abbrev flickerSystem := reactive spot flickerProc (regionIndex spot) (fun _ => False)

/-- The start: token `0` free, both firings parked and awake. -/
def flickerStart : RState ℕ Bool := ⟨{0}, {0}, Set.univ, Set.univ⟩

theorem flicker_inRegion (p : Bool) : InRegion spot (flickerProc p) := by
  cases p
  · rintro c ⟨k, rfl⟩
    exact ⟨fun _ _ => rfl, by simp [toggle]⟩
  · rintro c ⟨k, rfl⟩
    refine ⟨fun o member => ?_, by simp [grab]⟩
    simp only [grab, Finset.union_empty, Finset.mem_singleton] at member
    subst member
    simp [flickerProc, spot, isFree]

theorem flicker_adequate (p : Bool) : NoLostWakeup spot (regionIndex spot) (flickerProc p) :=
  regionIndex_noLostWakeup (flicker_inRegion p)

theorem flickerStart_inv : WakeInv spot flickerProc flickerStart :=
  ⟨le_rfl, fun _ _ _ => Set.mem_univ _⟩

/-- The await's guard holds at a single token exactly when the token is free. -/
theorem await_guard_iff {m : ℕ} {born : Finset ℕ} :
    Guard spot (flickerProc true) {m} born ↔ m % 2 = 0 := by
  constructor
  · rintro ⟨c, ⟨k, rfl⟩, m', _⟩
    have := m'.taken_subset (Finset.mem_singleton_self (2 * k))
    simp only [Finset.mem_singleton] at this
    omega
  · intro even
    refine ⟨grab (m / 2), ⟨m / 2, rfl⟩, ⟨?_, by simp [grab], by simp [grab], by simp [grab]⟩,
      by simp [grab]⟩
    intro o member
    simp only [grab, Finset.mem_singleton] at member ⊢
    omega

/-- The run in which the whenever toggles forever. -/
def flickerRun : Run flickerSystem where
  state n := ⟨{n}, Finset.range (n + 1), Set.univ, Set.univ⟩
  label n := .run false (toggle n)
  allowed n := by
    refine ⟨Set.mem_univ _, Set.mem_univ _, ⟨n, rfl⟩, ⟨?_, by simp [toggle], by simp [toggle],
      by simp [toggle]⟩, by simp [toggle]⟩
    simp [toggle]
  step n := by
    have store : fire ({n} : Finset ℕ) (toggle n) = {n + 1} := by ext o; simp [toggle, mem_fire]
    have born : Finset.range (n + 1) ∪ (toggle n).made = Finset.range (n + 1 + 1) := by
      ext o; simp [toggle, Finset.mem_range]; omega
    show (⟨{n + 1}, Finset.range (n + 1 + 1), Set.univ, Set.univ⟩ : RState ℕ Bool) =
      ⟨fire {n} (toggle n), Finset.range (n + 1) ∪ (toggle n).made, Set.univ,
        Set.univ ∪ woken flickerProc (regionIndex spot) ⟨{n}, Finset.range (n + 1), Set.univ, Set.univ⟩
          (toggle n)⟩
    rw [store, born, Set.univ_union]

theorem flickerRun_enabled_iff (n : ℕ) :
    flickerSystem.TaskEnabled (runTask true) (flickerRun.state n) ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨a, inTask, allowed⟩
    cases a with
    | run q c =>
        have same : q = true := inTask
        subst same
        obtain ⟨_, _, row, fireable⟩ := allowed
        exact await_guard_iff.1 ⟨c, row, fireable⟩
    | env d => exact absurd inTask id
    | sleep q => exact absurd inTask id
    | idle => exact absurd inTask id
  · intro even
    exact runTask_enabled (index := regionIndex spot) (envOK := fun _ => False)
      ⟨fun o member => by
        change o ∈ ({n} : Finset ℕ) at member
        change o ∈ Finset.range (n + 1)
        simp only [Finset.mem_singleton] at member
        simp [member], fun _ _ _ => Set.mem_univ _⟩
      (Set.mem_univ _)
      (await_guard_iff.2 even)

/-- In the toggling run the await never runs. -/
theorem flicker_await_never_fires : ∀ n, ¬ runTask true (flickerRun.label n) :=
  fun _ same => Bool.false_ne_true same

/-- **The toggling run is weakly fair for both firings**, and the await's guard holds at every
other step. -/
theorem flicker_weaklyFair :
    (∀ p, flickerRun.WeaklyFair (runTask p)) ∧
      InfinitelyOften fun n => Guard spot (flickerProc true) (flickerRun.state n).store
        (flickerRun.state n).born := by
  refine ⟨fun p => ?_, fun N => ⟨2 * N, by omega, await_guard_iff.2 (by omega)⟩⟩
  cases p
  · intro _ N
    exact ⟨N, le_rfl, rfl⟩
  · rintro ⟨N, always⟩
    have := (flickerRun_enabled_iff (2 * N + 1)).1 (always _ (by omega))
    omega

/-- The toggling run is not strongly fair for the await. -/
theorem flicker_not_stronglyFair : ¬ flickerRun.StronglyFair (runTask true) := by
  intro fair
  obtain ⟨n, _, fires⟩ := fair (fun N => ⟨2 * N, by omega, (flickerRun_enabled_iff _).2 (by omega)⟩) 0
  exact flicker_await_never_fires n fires

/-- While the await has not run, the store is one token and the born identities are those up to
it. -/
theorem flicker_shape (r : Run flickerSystem) (start : r.state 0 = flickerStart)
    (never : ∀ n, ¬ runTask true (r.label n)) :
    ∀ n, ∃ m, (r.state n).store = {m} ∧ (r.state n).born = Finset.range (m + 1) ∧
      (r.state n).parked = Set.univ := by
  intro n
  induction n with
  | zero => exact ⟨0, by rw [start]; rfl, by rw [start]; rfl, by rw [start]; rfl⟩
  | succ n ih =>
      obtain ⟨m, store, born, parked⟩ := ih
      have allowed := r.allowed n
      rw [r.step n]
      cases labelIs : r.label n with
      | env d =>
          rw [labelIs] at allowed
          exact absurd allowed.1 id
      | run q c =>
          cases q with
          | true => exact absurd (by rw [labelIs]; rfl : runTask true (r.label n)) (never n)
          | false =>
              rw [labelIs] at allowed
              obtain ⟨_, _, ⟨k, rfl⟩, fireable, _⟩ := allowed
              have kIs : k = m := by
                have := fireable.taken_subset (Finset.mem_singleton_self k)
                simpa [toggle, store] using this
              subst kIs
              refine ⟨k + 1, ?_, ?_, ?_⟩
              · simp only [reactive_next, rNext, store]; ext o; simp [toggle, mem_fire]
              · simp only [reactive_next, rNext, born]; ext o; simp [toggle, Finset.mem_range]; omega
              · simp only [reactive_next, rNext, flickerProc, if_true]; exact parked
      | sleep q => exact ⟨m, store, born, parked⟩
      | idle => exact ⟨m, store, born, parked⟩

/-- **In every strongly fair run of the flicker system the await runs.** -/
theorem flicker_stronglyFair_fires (r : Run flickerSystem) (start : r.state 0 = flickerStart)
    (fair : ∀ p, r.StronglyFair (runTask p)) : ∃ n, runTask true (r.label n) := by
  by_contra never
  push Not at never
  have shape := flicker_shape r start never
  have inv := Run.wakeInv flicker_adequate r (start ▸ flickerStart_inv)
  -- the whenever can always run
  have togglerEnabled : ∀ n, flickerSystem.TaskEnabled (runTask false) (r.state n) := by
    intro n
    obtain ⟨m, store, born, parked⟩ := shape n
    refine runTask_enabled (inv n) (by rw [parked]; trivial) ⟨toggle m, ⟨m, rfl⟩, ⟨?_, by simp [toggle],
      by simp [toggle], by simp [toggle]⟩, ?_⟩
    · rw [store]; simp [toggle]
    · rw [born]; simp [toggle]
  -- the await's guard holds infinitely often
  have often : InfinitelyOften fun n => Guard spot (flickerProc true) (r.state n).store (r.state n).born := by
    by_contra notOften
    obtain ⟨N, never'⟩ := not_infinitelyOften_iff.mp notOften
    obtain ⟨n, le, fires⟩ := (fair false).weaklyFair ⟨0, fun n _ => togglerEnabled n⟩ N
    obtain ⟨m, store, _, _⟩ := shape n
    have odd : m % 2 = 1 := by
      have : ¬ Guard spot (flickerProc true) (r.state n).store (r.state n).born := never' n le
      rw [store, await_guard_iff] at this
      omega
    obtain ⟨m', store', _, _⟩ := shape (n + 1)
    have next : m' = m + 1 := by
      have allowed := r.allowed n
      have stepEq := r.step n
      cases labelIs : r.label n with
      | run q c =>
          have qIs : q = false := by rw [labelIs] at fires; exact fires
          subst qIs
          rw [labelIs] at allowed stepEq
          obtain ⟨_, _, ⟨k, rfl⟩, fireable, _⟩ := allowed
          have kIs : k = m := by
            have := fireable.taken_subset (Finset.mem_singleton_self k)
            simpa [toggle, store] using this
          subst kIs
          have : (r.state (n + 1)).store = {k + 1} := by
            rw [stepEq]; simp only [reactive_next, rNext, store]; ext o; simp [toggle, mem_fire]
          rw [store'] at this
          exact Finset.singleton_injective this
      | env d => rw [labelIs] at fires; exact absurd fires id
      | sleep q => rw [labelIs] at fires; exact absurd fires id
      | idle => rw [labelIs] at fires; exact absurd fires id
    have : ¬ Guard spot (flickerProc true) (r.state (n + 1)).store (r.state (n + 1)).born :=
      never' (n + 1) (by omega)
    rw [store', await_guard_iff] at this
    omega
  obtain ⟨n, fires⟩ := await_fires flicker_adequate r (start ▸ flickerStart_inv)
    (by rw [start]; trivial) (fair true) often
  exact never n fires

/-! ### A lost wakeup: an absence guard keyed on makes -/

section LostWakeup

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-- "Add an output unless locked", parked. -/
def unlessLockedProc : Unit → Parked ℕ Atom := fun _ => ⟨{unlessLocked}, isLock, false⟩

/-- The only outside commit: take the lock. -/
def onlyUnlock (d : Commit ℕ Atom) : Prop := d = lockTaker

/-- The start: the lock present, the firing parked and awake. -/
def lockedStart : RState ℕ Unit := ⟨{1}, {1}, Set.univ, Set.univ⟩

/-- After the firing sleeps. -/
def asleep : RState ℕ Unit := ⟨{1}, {1}, Set.univ, Set.univ \ {()}⟩

/-- After the lock is taken, under the makes index. -/
def unlocked : RState ℕ Unit := rNext unlessLockedProc (makesIndex label) asleep (.env lockTaker)

/-- The system with the makes index. -/
abbrev makesSystem := reactive label unlessLockedProc (makesIndex label) onlyUnlock

theorem not_guard_locked : ¬ Guard label (unlessLockedProc ()) {1} {1} := by
  rintro ⟨c, row, m, _⟩
  have same : c = unlessLocked := row
  subst same
  have := m.queries_hold ⟨isLock, ∅⟩ (by simp [unlessLocked])
  revert this
  decide

theorem lockTaker_enabled_locked : Enabled label {1} lockTaker :=
  ⟨by decide, by decide, by decide, by decide, by simp [lockTaker]⟩

/-- Once the lock is taken, the guard holds. -/
theorem guard_unlocked : Guard label (unlessLockedProc ()) (fire {1} lockTaker) ({1} ∪ lockTaker.made) :=
  ⟨unlessLocked, rfl, ⟨by simp [unlessLocked], by simp [unlessLocked], by simp [unlessLocked],
    by simp only [unlessLocked, List.mem_singleton, forall_eq]; decide⟩, by decide⟩

theorem unlocked_asleep : () ∉ unlocked.awake := by
  rintro (⟨_, notMem⟩ | ⟨_, o, made, inRegion⟩)
  · exact notMem rfl
  · simp only [lockTaker, Finset.mem_singleton] at made
    subst made
    revert inRegion
    decide

/-- Sleep, take the lock, then idle forever. -/
def lostRun : Run makesSystem where
  state n := match n with
    | 0 => lockedStart
    | 1 => asleep
    | _ + 2 => unlocked
  label n := match n with
    | 0 => .sleep ()
    | 1 => .env lockTaker
    | _ + 2 => .idle
  allowed n := match n with
    | 0 => ⟨Set.mem_univ _, not_guard_locked⟩
    | 1 => ⟨rfl, lockTaker_enabled_locked, by decide⟩
    | _ + 2 => trivial
  step n := match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

theorem lostRun_never_enabled (n : ℕ) : ¬ makesSystem.TaskEnabled (runTask ()) (lostRun.state n) := by
  rintro ⟨a, inTask, allowed⟩
  cases a with
  | run q c =>
      obtain ⟨_, awake, row, fireable⟩ := allowed
      match n with
      | 0 => exact not_guard_locked ⟨c, row, fireable⟩
      | 1 => exact awake.2 rfl
      | _ + 2 => exact unlocked_asleep awake
  | env d => exact absurd inTask id
  | sleep q => exact absurd inTask id
  | idle => exact absurd inTask id

/-- **The makes index loses the wakeup of an absence guard.** After the lock is taken the guard
holds forever, the run is strongly fair for the firing, and the firing never runs; the makes index
fails `NoLostWakeup` for it. -/
theorem makesIndex_loses_wakeup :
    (∀ n ≥ 2, Guard label (unlessLockedProc ()) (lostRun.state n).store (lostRun.state n).born) ∧
      (∀ n, ¬ runTask () (lostRun.label n)) ∧ lostRun.StronglyFair (runTask ()) ∧
      ¬ NoLostWakeup label (makesIndex label) (unlessLockedProc ()) := by
  refine ⟨fun n le => ?_, fun n => ?_, fun often => ?_, fun adequate => ?_⟩
  · match n, le with
    | _ + 2, _ => exact guard_unlocked
  · match n with
    | 0 => exact id
    | 1 => exact id
    | _ + 2 => exact id
  · obtain ⟨n, _, enabled⟩ := often 0
    exact absurd enabled (lostRun_never_enabled n)
  · obtain ⟨o, made, inRegion⟩ := adequate {1} {1} lockTaker le_rfl lockTaker_enabled_locked
      (by decide) not_guard_locked guard_unlocked
    simp only [lockTaker, Finset.mem_singleton] at made
    subst made
    revert inRegion
    decide

/-- **The region index wakes it**: the same commit, taking the lock, wakes the firing. -/
theorem regionIndex_wakes :
    () ∈ (rNext unlessLockedProc (regionIndex label) asleep (.env lockTaker)).awake :=
  Or.inr ⟨Set.mem_univ _, 1, by simp [lockTaker], rfl⟩

/-- A stale guard check cannot justify parking after an intervening commit,
    even with the region index. Rechecking rejects the sleep; applying that
    unallowed sleep anyway leaves an enabled firing asleep and breaks the
    wake invariant. This is a model control, not an implementation of the
    registration/parking protocol. -/
theorem stale_check_after_unlock_loses_wakeup :
    let after := rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)
    let slept := rNext unlessLockedProc (regionIndex label) after (.sleep ())
    rAllowed label unlessLockedProc onlyUnlock lockedStart (.sleep ()) ∧
      rAllowed label unlessLockedProc onlyUnlock lockedStart (.env lockTaker) ∧
      ¬ rAllowed label unlessLockedProc onlyUnlock after (.sleep ()) ∧
      Guard label (unlessLockedProc ()) slept.store slept.born ∧
      () ∉ slept.awake ∧ ¬ WakeInv label unlessLockedProc slept := by
  dsimp only
  have before : rAllowed label unlessLockedProc onlyUnlock lockedStart (.sleep ()) :=
    ⟨Set.mem_univ _, not_guard_locked⟩
  have committed : rAllowed label unlessLockedProc onlyUnlock lockedStart (.env lockTaker) :=
    ⟨rfl, lockTaker_enabled_locked, by decide⟩
  have ready : Guard label (unlessLockedProc ())
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)).store
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)).born := by
    simpa [rNext, lockedStart] using guard_unlocked
  have rejected : ¬ rAllowed label unlessLockedProc onlyUnlock
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ()) :=
    fun h => h.2 ready
  have stillReady : Guard label (unlessLockedProc ())
      (rNext unlessLockedProc (regionIndex label)
        (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ())).store
      (rNext unlessLockedProc (regionIndex label)
        (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ())).born := by
    simpa [rNext] using ready
  have asleep : () ∉ (rNext unlessLockedProc (regionIndex label)
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ())).awake := by
    simp [rNext]
  refine ⟨before, committed, rejected, stillReady, asleep, ?_⟩
  intro inv
  apply asleep
  apply inv.awake_of_guard ()
  · simp [rNext, lockedStart]
  · exact stillReady

end LostWakeup

/-! ### Matching, fireable rows, regions, positive rows -/

/-- **Matches, positive**: grabbing occurrence `0` matches the store `{0}`. -/
theorem grab_matches : Matches spot {0} (grab 0) :=
  ⟨by decide, by decide, by decide, by simp [grab]⟩

/-- **Matches, negative**: it does not match the empty store. -/
theorem grab_not_matches_empty : ¬ Matches spot ∅ (grab 0) := fun matched =>
  absurd matched.taken_subset (by decide)

/-- **Fireable, negative**: toggling `0` matches `{0}`, but its fresh identity `1` is already
born. (The flicker runs fire positive instances.) -/
theorem toggle_reborn_not_fireable : ¬ Fireable spot {0} {0, 1} (toggle 0) := fun fireable =>
  absurd fireable.2 (by decide)

/-- **Positive rows, positive**: no row of either flicker firing has a predicate query. -/
theorem flicker_positiveRows (p : Bool) : PositiveRows (flickerProc p) := by
  intro c member
  cases p
  · obtain ⟨k, rfl⟩ := member; rfl
  · obtain ⟨k, rfl⟩ := member; rfl

/-- A parked firing whose one row queries the free region. -/
def queryingProc : Parked ℕ Spot := ⟨{⟨∅, ∅, ∅, [⟨isFree, ∅⟩]⟩}, isFree, false⟩

/-- **Positive rows, negative**: its row has a predicate query. -/
theorem queryingProc_not_positive : ¬ PositiveRows queryingProc := fun positive => by
  have := positive _ (Set.mem_singleton _)
  simp at this

/-- A parked firing whose region is the free spots but whose row takes the held spot `1`. -/
def outsideProc : Parked ℕ Spot := ⟨{⟨{1}, ∅, ∅, []⟩}, isFree, false⟩

/-- **In region, negative**: its row takes outside its region. (`flicker_inRegion` is the
positive control.) -/
theorem outsideProc_not_inRegion : ¬ InRegion spot outsideProc := fun inRegion => by
  have := (inRegion _ (Set.mem_singleton _)).1 1 (by simp)
  revert this
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
