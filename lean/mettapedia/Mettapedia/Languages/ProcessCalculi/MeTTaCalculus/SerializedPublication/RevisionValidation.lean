import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitProtocol
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies

/-!
# Publication validated by one revision per space

A runtime can match a proposal against a snapshot of a space, prepare its result privately
(possibly on a worker thread), and publish it later from one coordinating thread, checking only
that the space's revision number has not moved since the snapshot. This module states exactly
what that protocol guarantees, in the vocabulary of `OccurrenceCommits`, and what it does not.

## The model

The revision check is a predicate query of the whole space that saw the snapshot: it holds exactly
when the store is the snapshot (`revisionQuery_holds_iff`). A proposal `c` matched at snapshot `S`
is therefore published as the commit `widen S c`, which is `c` with that one extra predicate query
(`widen_enabled_iff`: `widen S c` is enabled at a store exactly when `c` is and the store is `S`).
Bumping the revision on every write is the per-region epoch of `CommitProtocol` for the single
region `everywhere`, which every writing commit writes into (`writes_everywhere_iff`). So the
protocol is the commit protocol of `CommitProtocol` run over widened transactions; serialized
publication makes its claims uncontended.

## What it guarantees

* **Serializability by serialization.** The base commits of any run of the widened protocol are
  an executable sequence of the atomic semantics (`revision_run_refines`, through
  `CommitProtocol.Run.refines` and `executable_of_widened`).
* In an executable sequence of proposals widened at one snapshot, every commit before the last
  one writes nothing (`writers_only_last`): one snapshot publishes at most one writer.

## What it does not guarantee

* **Independence is not preserved.** Any writing commit spoils every widened commit
  (`spoils_widen_of_writes`), so two writers widened at one snapshot form a precedence two-cycle
  (`widen_pair_not_acyclic`) and have no executable order (`no_order_of_two_widened_writers`),
  although their base commits may be independent and then run in both orders
  (`Exactness.independent_iff_both_orders`).
* **One write anywhere makes every open transaction stale.** After any writing commit, a
  transaction that validates a whole-space revision and began earlier commits in no
  continuation (`stale_after_any_write`), through `CommitProtocol.Run.stale_never_commits` for the
  region `everywhere`. This is the validation the shared case of read polarity needs, and more
  than the owned case needs (`RegionPermissions.SharedReads`); the interaction kernel keeps one
  revision per space (`RegionPermissions.KernelCommit.revisionQuery`).

## Controls

Two takers of distinct tokens are independent (`Controls.takers_independent`). Under the
per-occurrence protocol they begin at one state and both commit (`Controls.base_both_commit`).
Widened at their common snapshot, once the first has committed the second commits in no
continuation (`Controls.widened_second_never_commits`), and the widened pair has no executable
order at all (`Controls.widened_pair_no_order`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

/-! ## Widening a proposal by its revision check -/

section Widening

variable {O : Type u} {R : Type v}

/-- The region of the whole space. -/
def everywhere : R → Bool := fun _ => true

/-- The read that a revision check performs: the whole space is exactly the snapshot. -/
def revisionQuery (snapshot : Finset O) : PredicateQuery O R := ⟨everywhere, snapshot⟩

/-- A proposal matched at `snapshot` and validated by the space's revision. -/
def widen (snapshot : Finset O) (c : Commit O R) : Commit O R :=
  { c with queries := revisionQuery snapshot :: c.queries }

@[simp] theorem widen_taken (snapshot : Finset O) (c : Commit O R) :
    (widen snapshot c).taken = c.taken := rfl

@[simp] theorem widen_kept (snapshot : Finset O) (c : Commit O R) :
    (widen snapshot c).kept = c.kept := rfl

@[simp] theorem widen_made (snapshot : Finset O) (c : Commit O R) :
    (widen snapshot c).made = c.made := rfl

@[simp] theorem widen_reads (snapshot : Finset O) (c : Commit O R) :
    (widen snapshot c).queries = revisionQuery snapshot :: c.queries := rfl

theorem regionOf_everywhere (label : O → R) (store : Finset O) :
    regionOf label store everywhere = store := by
  ext o
  simp [regionOf, everywhere]

/-- A revision check holds exactly when the store is the snapshot. -/
theorem revisionQuery_holds_iff {label : O → R} {store snapshot : Finset O} :
    (revisionQuery snapshot : PredicateQuery O R).Holds label store ↔ store = snapshot := by
  unfold PredicateQuery.Holds
  simp [revisionQuery, regionOf_everywhere]

/-- **A widened proposal is enabled exactly when the proposal is and the store is its
snapshot.** -/
theorem widen_enabled_iff {label : O → R} {store snapshot : Finset O} {c : Commit O R} :
    Enabled label store (widen snapshot c) ↔ Enabled label store c ∧ store = snapshot := by
  constructor
  · intro enabled
    refine ⟨⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh,
      fun read member => enabled.queries_hold read (List.mem_cons_of_mem _ member)⟩, ?_⟩
    exact revisionQuery_holds_iff.mp (enabled.queries_hold _ List.mem_cons_self)
  · rintro ⟨enabled, rfl⟩
    refine ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, ?_⟩
    intro read member
    rcases List.mem_cons.mp member with same | member
    · subst same
      exact revisionQuery_holds_iff.mpr rfl
    · exact enabled.queries_hold read member

/-- Widening changes what a commit checks, never what it does. -/
@[simp] theorem fire_widen [DecidableEq O] (store snapshot : Finset O) (c : Commit O R) :
    fire store (widen snapshot c) = fire store c := rfl

/-- A commit writes: it takes or makes something (`Commit.writes` is not empty). -/
def WritesSomething [DecidableEq O] (c : Commit O R) : Prop := c.writes.Nonempty

/-- **Any write spoils a widened commit.** -/
theorem spoils_widen_of_writes [DecidableEq O] {label : O → R} {d c : Commit O R}
    {snapshot : Finset O} (writes : WritesSomething d) : Spoils label d (widen snapshot c) := by
  obtain ⟨o, member⟩ := writes
  exact Or.inr ⟨revisionQuery snapshot, List.mem_cons_self, o, member, rfl⟩

/-- **Two distinct writers widened at one snapshot form a precedence two-cycle.** -/
theorem widen_pair_not_acyclic [DecidableEq O] {label : O → R} {snapshot : Finset O}
    {c d : Commit O R} (different : widen snapshot c ≠ widen snapshot d)
    (writesC : WritesSomething c) (writesD : WritesSomething d) :
    ¬ Acyclic label [widen snapshot c, widen snapshot d] := by
  intro acyclic
  have first : BeforeOn label [widen snapshot c, widen snapshot d]
      (widen snapshot c) (widen snapshot d) :=
    ⟨by simp, by simp, different,
      spoils_widen_of_writes (d := widen snapshot d) writesD⟩
  have second : BeforeOn label [widen snapshot c, widen snapshot d]
      (widen snapshot d) (widen snapshot c) :=
    ⟨by simp, by simp, Ne.symm different,
      spoils_widen_of_writes (d := widen snapshot c) writesC⟩
  exact acyclic _ (Relation.TransGen.tail (Relation.TransGen.single first) second)

/-- **Two writers widened at one snapshot have no executable order**, whatever their base
commits are. -/
theorem no_order_of_two_widened_writers [DecidableEq O] {label : O → R} {snapshot : Finset O}
    {c d : Commit O R} (enabledC : Enabled label snapshot c) (enabledD : Enabled label snapshot d)
    (different : widen snapshot c ≠ widen snapshot d)
    (writesC : WritesSomething c) (writesD : WritesSomething d) :
    ¬ ∃ l, l.Perm [widen snapshot c, widen snapshot d] ∧ Executable label snapshot l := by
  intro exists_order
  have enabled : ∀ e ∈ [widen snapshot c, widen snapshot d], Enabled label snapshot e := by
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst same; exact widen_enabled_iff.mpr ⟨enabledC, rfl⟩
    · subst same; exact widen_enabled_iff.mpr ⟨enabledD, rfl⟩
  exact widen_pair_not_acyclic different writesC writesD
    ((exists_executable_perm_iff_noClash_and_acyclic enabled).mp exists_order).2

/-- A writing commit that is enabled changes the store. -/
theorem fire_ne_of_writes [DecidableEq O] {label : O → R} {store : Finset O} {c : Commit O R}
    (enabled : Enabled label store c) (writes : WritesSomething c) : fire store c ≠ store := by
  obtain ⟨o, member⟩ := writes
  intro same
  rcases Finset.mem_union.mp member with taken | made
  · have gone : o ∉ fire store c := Finset.disjoint_left.mp (disjoint_taken_fire enabled) taken
    rw [same] at gone
    exact gone (enabled.taken_subset taken)
  · have present : o ∈ fire store c := made_subset_fire made
    rw [same] at present
    exact Finset.disjoint_left.mp enabled.fresh made present

/-- **In an executable sequence of proposals widened at one snapshot, every commit before the
last one writes nothing.** -/
theorem writers_only_last [DecidableEq O] {label : O → R} {snapshot : Finset O}
    {e : Commit O R} {rest : List (Commit O R)}
    (widened : ∀ x ∈ e :: rest, ∃ c, x = widen snapshot c)
    (executable : Executable label snapshot (e :: rest)) (nonempty : rest ≠ []) :
    ¬ WritesSomething e := by
  intro writes
  obtain ⟨enabledE, executableRest⟩ := executable_cons_iff.mp executable
  obtain ⟨next, after, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  obtain ⟨enabledNext, _⟩ := executable_cons_iff.mp executableRest
  obtain ⟨base, same⟩ := widened next (by simp)
  subst same
  exact fire_ne_of_writes enabledE writes (widen_enabled_iff.mp enabledNext).2

/-- Widening only adds checks: the base commits of an executable widened sequence are
executable. -/
theorem executable_of_widened [DecidableEq O] {label : O → R} {ι : Type w}
    (snapshot : ι → Finset O) (base : ι → Commit O R) :
    ∀ (l : List ι) (store : Finset O),
      Executable label store (l.map fun i => widen (snapshot i) (base i)) →
      Executable label store (l.map base)
  | [], store, _ => .nil store
  | i :: rest, store, executable => by
      obtain ⟨enabled, executableRest⟩ := executable_cons_iff.mp executable
      have restBase := executable_of_widened snapshot base rest (fire store (base i))
        (by simpa using executableRest)
      exact .cons (widen_enabled_iff.mp enabled).1 restBase

/-- Widening does not change where a sequence of commits leads. -/
theorem fireList_widened [DecidableEq O] {ι : Type w} (snapshot : ι → Finset O)
    (base : ι → Commit O R) :
    ∀ (l : List ι) (store : Finset O),
      fireList store (l.map fun i => widen (snapshot i) (base i)) = fireList store (l.map base)
  | [], _ => rfl
  | i :: rest, store => by
      simpa using fireList_widened snapshot base rest (fire store (base i))

end Widening

/-! ## The revision protocol as an instance of the commit protocol -/

section RevisionProtocol

variable {O : Type u} [LinearOrder O] {R : Type v} {T : Type w} [DecidableEq T]

/-- A commit writes into the region `everywhere` exactly when it takes or makes something. -/
theorem writes_everywhere_iff (label : O → R) (c : Commit O R) :
    Writes label c everywhere ↔ WritesSomething c := by
  unfold Writes WritesSomething
  constructor
  · rintro ⟨o, member, _⟩; exact ⟨o, member⟩
  · rintro ⟨o, member⟩; exact ⟨o, member, rfl⟩

variable {label : O → R}

/-- **Serializability by serialization.** In a run of the commit protocol whose transactions are
proposals widened at their snapshots, the base commits, in commit order, are an executable
sequence from the initial store, and the run ends where they lead. -/
theorem revision_run_refines {snapshot : T → Finset O} {base : T → Commit O R}
    {σ σ' : ProtocolState O R T} {trace : List T}
    (run : Run label (fun t => widen (snapshot t) (base t)) σ
      (trace.map fun t => (t, widen (snapshot t) (base t))) σ')
    (wf : WellFormed label (fun t => widen (snapshot t) (base t)) σ) :
    Executable label σ.store (trace.map base) ∧
      σ'.store = fireList σ.store (trace.map base) := by
  obtain ⟨executable, endStore, _⟩ := run.refines wf
  have mapped : (trace.map fun t => (t, widen (snapshot t) (base t))).map Prod.snd =
      trace.map fun t => widen (snapshot t) (base t) := by
    simp [List.map_map, Function.comp_def]
  rw [mapped] at executable endStore
  exact ⟨executable_of_widened snapshot base trace σ.store executable,
    endStore.trans (fireList_widened snapshot base trace σ.store)⟩

/-- **One write anywhere makes every open transaction stale.** Once a writing commit of another
transaction has been published, a transaction that validates a whole-space revision and was
active before it commits in no continuation, whatever the two commits are otherwise. -/
theorem stale_after_any_write {txn : T → Commit O R} {σ : ProtocolState O R T}
    (wf : WellFormed label txn σ) {writer waiting : T} (different : waiting ≠ writer)
    {seen : (R → Bool) → ℕ} (active : σ.phase waiting = .active seen) {snapshot : Finset O}
    (validated : revisionQuery snapshot ∈ (txn waiting).queries)
    (writes : WritesSomething (txn writer)) :
    ∀ σ' trace, Run label txn (commitState label txn writer σ) trace σ' →
      ∀ entry ∈ trace, entry.1 ≠ waiting := by
  intro σ' trace later
  refine later.stale_never_commits (t := waiting) (seen := seen)
    (read := revisionQuery snapshot) validated (Or.inr ⟨?_, ?_⟩)
  · simp [commitState, Function.update_of_ne different, active]
  · have bumped : Writes label (txn writer) everywhere := (writes_everywhere_iff label _).mpr writes
    have le := wf.seen_le waiting seen active everywhere
    show seen everywhere < (commitState label txn writer σ).epoch everywhere
    simp only [commitState, if_pos bumped]
    omega

end RevisionProtocol

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls (Atom)

/-- The label of the controls: occurrence `0` is a token, `1` a lock, the rest outputs. -/
abbrev lab : ℕ → Atom := OccurrenceCommits.Controls.label

/-- Take the token `0`. -/
def takeFirst : Commit ℕ Atom := ⟨{0}, ∅, {5}, []⟩

/-- Take the occurrence `2`, a second token-like occurrence. -/
def takeSecond : Commit ℕ Atom := ⟨{2}, ∅, {6}, []⟩

/-- The base transactions: two takers of distinct occurrences. -/
def base : Bool → Commit ℕ Atom
  | true => takeFirst
  | false => takeSecond

/-- The snapshot both proposals are matched at. -/
def snapshot : Finset ℕ := {0, 2}

/-- The two takers are independent. -/
theorem takers_independent : Independent lab takeFirst takeSecond := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Clash; simp [takeFirst, takeSecond]
  · unfold Spoils WritesInto; simp [takeFirst, takeSecond]
  · unfold Spoils WritesInto; simp [takeFirst, takeSecond]

theorem takeFirst_enabled : Enabled lab snapshot takeFirst where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [takeFirst]

theorem takeSecond_enabled : Enabled lab snapshot takeSecond where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [takeSecond]

/-- The common starting state: both occurrences present and born, nothing claimed, epochs zero,
every transaction idle. -/
def start : ProtocolState ℕ Atom Bool where
  store := snapshot
  born := snapshot
  claim := fun _ => none
  epoch := fun _ => 0
  phase := fun _ => .idle

theorem start_initial : Initial start := ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩

/-- Both transactions have begun at the start state. -/
def begun : ProtocolState ℕ Atom Bool :=
  { start with
    phase := (Function.update (Function.update start.phase true (.active start.epoch)) false
      (.active start.epoch)) }

/-- Both have begun and the first has claimed its occurrence. -/
def claimed : ProtocolState ℕ Atom Bool :=
  { begun with claim := Function.update begun.claim 0 (some true) }

/-- **Positive control.** Under the per-occurrence protocol both independent takers, begun at one
state, commit one after the other. -/
theorem base_both_commit :
    ∃ σ, Run lab base start [(true, takeFirst), (false, takeSecond)] σ := by
  let afterFirst := commitState lab base true claimed
  let secondClaimed : ProtocolState ℕ Atom Bool :=
    { afterFirst with claim := Function.update afterFirst.claim 2 (some false) }
  have activeSecond : afterFirst.phase false = .active (fun _ => 0) := by
    simp [afterFirst, commitState, claimed, begun, start]
  have liveSecond : 2 ∈ afterFirst.store := by
    simp [afterFirst, commitState, claimed, begun, start, snapshot, base, takeFirst, fire]
  have freeSecond : afterFirst.claim 2 = none := by
    simp [afterFirst, commitState, claimed, begun, start, base, takeFirst]
  have unbornSecond : Disjoint takeSecond.made secondClaimed.born := by
    simp [secondClaimed, afterFirst, commitState, claimed, begun, start, snapshot, base,
      takeFirst, takeSecond]
  exact ⟨_, .step (.begin _ true rfl takeFirst_enabled)
    (.step (.begin _ false rfl takeSecond_enabled)
      (.step (.claim _ true (fun _ => 0) 0 rfl (by simp [base, takeFirst]) (by decide) rfl
          (by simp [base, takeFirst]))
        (.step (.commit _ true (fun _ => 0) rfl (by simp [base, takeFirst])
            (by simp [base, takeFirst]) (by simp [base, takeFirst]) (by decide))
          (.step (.claim afterFirst false (fun _ => 0) 2 activeSecond (by simp [base, takeSecond])
              liveSecond freeSecond (by simp [base, takeSecond]))
            (.step (.commit secondClaimed false (fun _ => 0) activeSecond
                (by simp [secondClaimed, base, takeSecond]) (by simp [base, takeSecond])
                (by simp [base, takeSecond]) unbornSecond)
              (.refl _))))))⟩

/-- The two takers widened at their common snapshot. -/
def widened : Bool → Commit ℕ Atom := fun t => widen snapshot (base t)

/-- **Negative control.** Widened at their common snapshot, the same two independent takers
cannot both commit: once the first has committed, the second commits in no continuation. -/
theorem widened_second_never_commits :
    ∃ σ, Run lab widened start [(true, widened true)] σ ∧
      ∀ σ' trace, Run lab widened σ trace σ' → ∀ entry ∈ trace, entry.1 ≠ false := by
  have enabledFirst : Enabled lab snapshot (widened true) :=
    widen_enabled_iff.mpr ⟨takeFirst_enabled, rfl⟩
  have enabledSecond : Enabled lab snapshot (widened false) :=
    widen_enabled_iff.mpr ⟨takeSecond_enabled, rfl⟩
  have toClaimed : Run lab widened start [] claimed :=
    .step (.begin _ true rfl enabledFirst)
      (.step (.begin _ false rfl enabledSecond)
        (.step (.claim _ true (fun _ => 0) 0 rfl (by simp [widened, base, takeFirst]) (by decide)
            rfl (by simp [widened, base, takeFirst]))
          (.refl _)))
  have wfClaimed : WellFormed lab widened claimed :=
    (toClaimed.refines (wellFormed_of_initial start_initial)).2.2
  have commitFirst : Step lab widened claimed (some (true, widened true))
      (commitState lab widened true claimed) := by
    refine .commit _ true (fun _ => 0) rfl (by simp [claimed, widened, base, takeFirst])
      (by simp [widened, base, takeFirst]) ?_ (by decide)
    intro read member
    simp only [widened, widen_reads, base, takeFirst, List.mem_singleton] at member
    subst member
    rfl
  have run : Run lab widened start [(true, widened true)] (commitState lab widened true claimed) :=
    .step (.begin _ true rfl enabledFirst)
      (.step (.begin _ false rfl enabledSecond)
        (.step (.claim _ true (fun _ => 0) 0 rfl (by simp [widened, base, takeFirst]) (by decide)
            rfl (by simp [widened, base, takeFirst]))
          (.step commitFirst (.refl _))))
  refine ⟨_, run, fun σ' trace later => ?_⟩
  exact stale_after_any_write wfClaimed (writer := true) (waiting := false) (by decide)
    (seen := fun _ => 0) rfl (snapshot := snapshot) (by simp [widened])
    ⟨0, by simp [widened, base, takeFirst]⟩ σ' trace later

/-- The widened pair has no executable order at its snapshot, although the base pair runs in
both orders. -/
theorem widened_pair_no_order :
    ¬ (∃ l, l.Perm [widened true, widened false] ∧ Executable lab snapshot l) ∧
      Executable lab snapshot [takeFirst, takeSecond] ∧
      Executable lab snapshot [takeSecond, takeFirst] := by
  have orders := (independent_iff_both_orders takeFirst_enabled takeSecond_enabled).mp
    takers_independent
  refine ⟨no_order_of_two_widened_writers (c := base true) (d := base false)
      takeFirst_enabled takeSecond_enabled ?_ ⟨0, by simp [base, takeFirst]⟩
      ⟨2, by simp [base, takeSecond]⟩,
    .cons takeFirst_enabled (.cons orders.1 (.nil _)),
    .cons takeSecond_enabled (.cons orders.2 (.nil _))⟩
  intro same
  have := congrArg Commit.taken same
  simp [base, takeFirst, takeSecond] at this

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication
