import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ReactiveTransitions
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# Optimistic validation with re-matching: progress, and starvation

A transaction **proposes** a commit matched at the current store, and later **commits** it if its
proposal is still valid, or **aborts**. This module is the attempt-level model of optimistic
execution. An attempt's validity is **sticky**: a commit that breaks a check of the mode marks every
attempt it breaks as invalid (`Invalidates`), as a per-occurrence claim or a per-region epoch does
in the commit protocol (`CommitProtocol.Run.stale_never_commits`, `Run.gone_never_commits`).

## Re-matching after an abort

An invalid attempt aborts, and the transaction is **idle again: it proposes again from the new
store**, with any of its rows enabled there (`OLabel.begin`). Each transaction has a set of rows,
not one fixed commit. A one-shot transaction finishes when it commits, or **fails** when it is idle
and none of its rows is enabled (a snapshot `transform` with no row). A persistent transaction (a
rule that keeps firing) is idle again after each commit. Aborts happen only to invalid attempts:
the protocol never gives up an attempt that could still commit.

Two pieces of bookkeeping are kept for the policies of `PriorityRemedies`: a step counter and, per
transaction, the time its current firing first proposed (`age`), which survives re-matching.

## Safety, inherited

* **Every committed attempt is permitted by its mode at the store where it commits**
  (`OInv`, `oInv_next`, `commit_permitted`): validity is sound for the checks of `Permits`.
* **Under serializable validation the commits of every execution are an executable sequence of the
  atomic semantics** ending at the store reached (`exec_refines`).

## Progress conditions (no fairness assumption)

* **Bounded lock-freedom** (`commitFree_bound`, `Run.commit_within`): a step that is not a commit
  lowers a potential (idle 2, valid attempt 1, invalid attempt 3, finished 0) by at least one. So
  every stretch of `3 * |T| + 1` consecutive steps contains a commit, in every run, for every mode
  and every refusal policy. Commits happen infinitely often in every infinite run
  (`Run.commits_infinitelyOften`).
* **Obstruction-freedom** (`Run.solo_commit_within`): four consecutive steps all by one
  transaction include a commit.
* **Wait-freedom where nothing invalidates** (`never_aborts`): in `unchecked` mode
  (`neverInvalidated_unchecked`), and for monotone programs in every mode (rows that take nothing and
  query nothing, `neverInvalidated_monotone`), no reachable state allows an abort, and every
  active attempt may commit at once.

A refused commit is not a step here: `refuse` removes the commit from the allowed steps, so a
refusal can block but never spin. A runtime that answers a refusal with a step that changes nothing
(a retained poll) is outside this bound; it can livelock even in a run strongly fair for every
step kind (`RefusalRetention.fair_livelock`).

## Starvation, and the fairness that prevents it

* **Optimistic validation is not wait-free** (`Controls.optimistic_starvation`): a one-shot
  transaction taking a token, and a persistent one that takes the token and makes a new one. In the
  run where the second always commits between the first's proposal and commit, the first re-matches
  forever and never commits. Every transaction takes infinitely many steps, aborts are never
  gratuitous, and the run is weakly fair for every step kind of every transaction. It is not
  strongly fair for the victim's commit step, which is enabled at every other step.
* **Strong fairness of the commit step prevents starvation**
  (`commits_of_stronglyFair_commit`): a transaction that proposes infinitely often commits, if the
  run is strongly fair for its commit step. A scheduler that sees validity can provide that
  (`FairRuns.agingRun_stronglyFair`); a runtime whose commits race in parallel cannot, which is what
  the remedies of `PriorityRemedies` address with weak fairness only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {T : Type w}

/-! ## Invalidation -/

/-- A committed commit `d` **invalidates** an attempt `c` under a mode when it breaks one of the
mode's checks: it takes what `c` takes, takes what `c` keeps, or writes into a region `c`
queries. -/
def Invalidates (label : O → R) (mode : Finset Check) (d c : Commit O R) : Prop :=
  (Check.takes ∈ mode ∧ ¬ Disjoint d.taken c.taken) ∨
    (Check.keeps ∈ mode ∧ ¬ Disjoint d.taken c.kept) ∨
    (Check.regions ∈ mode ∧ WritesInto label d c)

instance (label : O → R) (mode : Finset Check) (d c : Commit O R) :
    Decidable (Invalidates label mode d c) := by
  unfold Invalidates WritesInto
  infer_instance

/-- Under serializable validation, invalidation is exactly a take clash or a spoil. -/
theorem invalidates_serializable_iff {label : O → R} {d c : Commit O R} :
    Invalidates label Mode.serializable d c ↔ ¬ Disjoint d.taken c.taken ∨ Spoils label d c := by
  unfold Invalidates Spoils
  simp only [Mode.serializable, Finset.mem_univ, true_and]

/-- A commit that breaks no check keeps an attempt permitted. -/
theorem permits_fire_of_not_invalidates {label : O → R} {mode : Finset Check} {store : Finset O}
    {c d : Commit O R} (permits : Permits label mode store c)
    (notInvalid : ¬ Invalidates label mode d c) (madeApart : Disjoint c.made d.made) :
    Permits label mode (fire store d) c := by
  unfold Invalidates at notInvalid
  push Not at notInvalid
  obtain ⟨noTakes, noKeeps, noRegions⟩ := notInvalid
  obtain ⟨takes, keeps, regions, fresh⟩ := permits
  refine ⟨fun member o taken => ?_, fun member o kept => ?_, fun member read inQueries => ?_, ?_⟩
  · exact mem_fire.mpr (Or.inl ⟨takes member taken, fun inD =>
      Finset.disjoint_left.mp (noTakes member) inD taken⟩)
  · exact mem_fire.mpr (Or.inl ⟨keeps member kept, fun inD =>
      Finset.disjoint_left.mp (noKeeps member) inD kept⟩)
  · have noWrite := noRegions member
    exact PredicateQuery.holds_fire_of_no_write (fun o written => by
        by_contra inRegion
        exact noWrite ⟨read, inQueries, o, written, by simpa using inRegion⟩)
      (regions member read inQueries)
  · refine Finset.disjoint_left.mpr fun o made inFire => ?_
    rcases mem_fire.mp inFire with ⟨inStore, _⟩ | madeD
    · exact Finset.disjoint_left.mp fresh made inStore
    · exact Finset.disjoint_left.mp madeApart made madeD

/-! ## The system -/

/-- The phase of a transaction: idle, an active attempt with its validity, committed, failed. -/
inductive Phase (O : Type u) (R : Type v) where
  | idle
  | active (c : Commit O R) (valid : Bool)
  | committed
  | failed

/-- The state: the store, every identity ever born, each transaction's phase, the step counter,
and the time each transaction's current firing first proposed. -/
structure OState (T : Type w) (O : Type u) (R : Type v) where
  store : Finset O
  born : Finset O
  phase : T → Phase O R
  clock : ℕ
  age : T → Option ℕ

/-- A step: propose a row, commit, abort, or fail (no row). -/
inductive OLabel (T : Type w) (O : Type u) (R : Type v) where
  | begin (t : T) (c : Commit O R)
  | commit (t : T)
  | abort (t : T)
  | fail (t : T)

/-- The transaction that takes a step. -/
def OLabel.actor : OLabel T O R → T
  | .begin t _ => t
  | .commit t => t
  | .abort t => t
  | .fail t => t

/-- A commit step. -/
def OLabel.IsCommit : OLabel T O R → Prop
  | .commit _ => True
  | _ => False

/-- A program: the rows of each transaction, and which transactions are persistent. -/
structure Program (T : Type w) (O : Type u) (R : Type v) where
  rows : T → Set (Commit O R)
  persistent : T → Bool

variable [DecidableEq T]

section System

variable (label : O → R) (mode : Finset Check) (prog : Program T O R)
  (refuse : OState T O R → T → Prop)

/-- Some row of `t` is enabled at the store, with unborn fresh identities. -/
def CanMatch (σ : OState T O R) (t : T) : Prop :=
  ∃ c ∈ prog.rows t, Enabled label σ.store c ∧ Disjoint c.made σ.born

/-- When a step may happen. A commit may be refused by a policy (`refuse`). -/
def oAllowed (σ : OState T O R) : OLabel T O R → Prop
  | .begin t c => σ.phase t = .idle ∧ c ∈ prog.rows t ∧ Enabled label σ.store c ∧
      Disjoint c.made σ.born
  | .commit t => (∃ c, σ.phase t = .active c true) ∧ ¬ refuse σ t
  | .abort t => ∃ c, σ.phase t = .active c false
  | .fail t => σ.phase t = .idle ∧ prog.persistent t = false ∧ ¬ CanMatch label prog σ t

/-- What a commit of `d` does to another transaction's phase. -/
def invalidate (d : Commit O R) : Phase O R → Phase O R
  | .active c v => .active c (v && !decide (Invalidates label mode d c))
  | p => p

/-- What a step does. -/
def oNext (σ : OState T O R) : OLabel T O R → OState T O R
  | .begin t c =>
      { store := σ.store, born := σ.born ∪ c.made,
        phase := Function.update σ.phase t (.active c true), clock := σ.clock + 1,
        age := if σ.age t = none then Function.update σ.age t (some σ.clock) else σ.age }
  | .commit t =>
      match σ.phase t with
      | .active c _ =>
          { store := fire σ.store c, born := σ.born,
            phase := fun t' => if t' = t then (if prog.persistent t then .idle else .committed)
              else invalidate label mode c (σ.phase t'),
            clock := σ.clock + 1,
            age := if prog.persistent t then Function.update σ.age t none else σ.age }
      | _ => { σ with clock := σ.clock + 1 }
  | .abort t => { σ with phase := Function.update σ.phase t .idle, clock := σ.clock + 1 }
  | .fail t => { σ with phase := Function.update σ.phase t .failed, clock := σ.clock + 1 }

/-- The optimistic system under a mode, a program and a refusal policy. -/
def optimistic : LTS (OState T O R) (OLabel T O R) :=
  ⟨oAllowed label prog refuse, oNext label mode prog⟩

@[simp] theorem optimistic_next : (optimistic label mode prog refuse).next = oNext label mode prog :=
  rfl

@[simp] theorem optimistic_allowed :
    (optimistic label mode prog refuse).Allowed = oAllowed label prog refuse := rfl

/-- The invariant of optimistic execution. -/
structure OInv (σ : OState T O R) : Prop where
  store_born : σ.store ⊆ σ.born
  active_row : ∀ t c v, σ.phase t = .active c v → c ∈ prog.rows t
  apart : ∀ t c v, σ.phase t = .active c v → Disjoint c.taken c.kept
  made_born : ∀ t c v, σ.phase t = .active c v → c.made ⊆ σ.born
  made_fresh : ∀ t c v, σ.phase t = .active c v → Disjoint c.made σ.store
  made_apart : ∀ t t' c c' v v', t ≠ t' → σ.phase t = .active c v → σ.phase t' = .active c' v' →
    Disjoint c.made c'.made
  valid_permits : ∀ t c, σ.phase t = .active c true → Permits label mode σ.store c

/-- An initial state: every live occurrence born, every transaction idle. -/
def OInitial (σ : OState T O R) : Prop := σ.store ⊆ σ.born ∧ ∀ t, σ.phase t = .idle

end System

/-- No refusals: the base protocol. -/
def noRefusal : OState T O R → T → Prop := fun _ _ => False

section Invariant

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {refuse : OState T O R → T → Prop}

omit [DecidableEq O] [DecidableEq T] in
theorem oInv_of_initial {σ : OState T O R} (initial : OInitial σ) : OInv label mode prog σ where
  store_born := initial.1
  active_row t c v h := by rw [initial.2 t] at h; cases h
  apart t c v h := by rw [initial.2 t] at h; cases h
  made_born t c v h := by rw [initial.2 t] at h; cases h
  made_fresh t c v h := by rw [initial.2 t] at h; cases h
  made_apart t _ c _ v _ _ h := by rw [initial.2 t] at h; cases h
  valid_permits t c h := by rw [initial.2 t] at h; cases h

omit [DecidableEq O] in
theorem permits_of_enabled {store : Finset O} {c : Commit O R} (enabled : Enabled label store c) :
    Permits label mode store c :=
  ⟨fun _ => enabled.taken_subset, fun _ => enabled.kept_subset, fun _ => enabled.queries_hold,
    enabled.fresh⟩

theorem invalidate_eq_active {d c : Commit O R} {v : Bool} {p : Phase O R}
    (h : invalidate label mode d p = .active c v) :
    ∃ v₀, p = .active c v₀ ∧ (v = true → v₀ = true ∧ ¬ Invalidates label mode d c) := by
  cases p with
  | active c₀ v₀ =>
      simp only [invalidate, Phase.active.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨v₀, rfl, fun valid => ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at valid
      exact ⟨valid.1, valid.2⟩
  | idle => cases h
  | committed => cases h
  | failed => cases h

omit [DecidableEq O] in
/-- Retiring a transaction's attempt (to idle or failed) keeps the invariant. -/
theorem oInv_of_retire {σ σ' : OState T O R} (inv : OInv label mode prog σ) (t : T)
    (p : Phase O R) (notActive : ∀ c v, p ≠ .active c v) (store : σ'.store = σ.store)
    (born : σ'.born = σ.born) (phase : σ'.phase = Function.update σ.phase t p) :
    OInv label mode prog σ' := by
  have back : ∀ t' c v, σ'.phase t' = .active c v → σ.phase t' = .active c v := by
    intro t' c v h
    rw [phase] at h
    by_cases same : t' = t
    · subst same
      rw [Function.update_self] at h
      exact absurd h (notActive c v)
    · rwa [Function.update_of_ne same] at h
  refine ⟨by rw [store, born]; exact inv.store_born, fun t c v h => inv.active_row t c v (back t c v h),
    fun t c v h => inv.apart t c v (back t c v h), fun t c v h => by
      rw [born]; exact inv.made_born t c v (back t c v h),
    fun t c v h => by rw [store]; exact inv.made_fresh t c v (back t c v h),
    fun t₁ t₂ c₁ c₂ v₁ v₂ different h₁ h₂ =>
      inv.made_apart t₁ t₂ c₁ c₂ v₁ v₂ different (back _ _ _ h₁) (back _ _ _ h₂),
    fun t c h => by rw [store]; exact inv.valid_permits t c (back t c true h)⟩

/-- **Every step keeps the invariant.** -/
theorem oInv_next {σ : OState T O R} (inv : OInv label mode prog σ) {a : OLabel T O R}
    (allowed : oAllowed label prog refuse σ a) : OInv label mode prog (oNext label mode prog σ a) := by
  cases a with
  | begin t c =>
      obtain ⟨idle, row, enabled, fresh⟩ := allowed
      have phaseAt : ∀ t' c' v', (Function.update σ.phase t (.active c true)) t' = .active c' v' →
          (t' = t ∧ c' = c ∧ v' = true) ∨ (t' ≠ t ∧ σ.phase t' = .active c' v') := by
        intro t' c' v' h
        by_cases same : t' = t
        · subst same
          simp only [Function.update_self, Phase.active.injEq] at h
          exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
        · rw [Function.update_of_ne same] at h
          exact Or.inr ⟨same, h⟩
      refine ⟨inv.store_born.trans Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t' c' v' h
        rcases phaseAt t' c' v' h with ⟨rfl, rfl, rfl⟩ | ⟨_, h'⟩
        · exact row
        · exact inv.active_row t' c' v' h'
      · intro t' c' v' h
        rcases phaseAt t' c' v' h with ⟨rfl, rfl, rfl⟩ | ⟨_, h'⟩
        · exact enabled.apart
        · exact inv.apart t' c' v' h'
      · intro t' c' v' h
        rcases phaseAt t' c' v' h with ⟨rfl, rfl, rfl⟩ | ⟨_, h'⟩
        · exact Finset.subset_union_right
        · exact (inv.made_born t' c' v' h').trans Finset.subset_union_left
      · intro t' c' v' h
        rcases phaseAt t' c' v' h with ⟨rfl, rfl, rfl⟩ | ⟨_, h'⟩
        · exact enabled.fresh
        · exact inv.made_fresh t' c' v' h'
      · intro t₁ t₂ c₁ c₂ v₁ v₂ different h₁ h₂
        rcases phaseAt t₁ c₁ v₁ h₁ with ⟨rfl, rfl, rfl⟩ | ⟨ne₁, h₁'⟩ <;>
          rcases phaseAt t₂ c₂ v₂ h₂ with ⟨rfl, rfl, rfl⟩ | ⟨ne₂, h₂'⟩
        · exact absurd rfl different
        · exact Finset.disjoint_of_subset_right (inv.made_born _ _ _ h₂') fresh
        · exact (Finset.disjoint_of_subset_right (inv.made_born _ _ _ h₁') fresh).symm
        · exact inv.made_apart t₁ t₂ c₁ c₂ v₁ v₂ different h₁' h₂'
      · intro t' c' h
        rcases phaseAt t' c' true h with ⟨rfl, rfl, -⟩ | ⟨_, h'⟩
        · exact permits_of_enabled enabled
        · exact inv.valid_permits t' c' h'
  | commit t =>
      obtain ⟨⟨c, isActive⟩, _⟩ := allowed
      have permitsC := inv.valid_permits t c isActive
      have phaseAt : ∀ t' c' v', (fun t'' => if t'' = t then (if prog.persistent t then Phase.idle
            else Phase.committed) else invalidate label mode c (σ.phase t'')) t' = .active c' v' →
          t' ≠ t ∧ ∃ v₀, σ.phase t' = .active c' v₀ ∧
            (v' = true → v₀ = true ∧ ¬ Invalidates label mode c c') := by
        intro t' c' v' h
        by_cases same : t' = t
        · subst same
          simp only [if_true] at h
          split_ifs at h
        · simp only [same, if_false] at h
          exact ⟨same, invalidate_eq_active h⟩
      simp only [oNext, isActive]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o member
        rcases mem_fire.mp member with ⟨inStore, _⟩ | made
        · exact inv.store_born inStore
        · exact inv.made_born t c true isActive made
      · intro t' c' v' h
        obtain ⟨_, v₀, h', _⟩ := phaseAt t' c' v' h
        exact inv.active_row t' c' v₀ h'
      · intro t' c' v' h
        obtain ⟨_, v₀, h', _⟩ := phaseAt t' c' v' h
        exact inv.apart t' c' v₀ h'
      · intro t' c' v' h
        obtain ⟨_, v₀, h', _⟩ := phaseAt t' c' v' h
        exact inv.made_born t' c' v₀ h'
      · intro t' c' v' h
        obtain ⟨different, v₀, h', _⟩ := phaseAt t' c' v' h
        refine Finset.disjoint_left.mpr fun o made inFire => ?_
        rcases mem_fire.mp inFire with ⟨inStore, _⟩ | madeC
        · exact Finset.disjoint_left.mp (inv.made_fresh t' c' v₀ h') made inStore
        · exact Finset.disjoint_left.mp (inv.made_apart t' t c' c v₀ true different h' isActive) made madeC
      · intro t₁ t₂ c₁ c₂ v₁ v₂ different h₁ h₂
        obtain ⟨_, w₁, h₁', _⟩ := phaseAt t₁ c₁ v₁ h₁
        obtain ⟨_, w₂, h₂', _⟩ := phaseAt t₂ c₂ v₂ h₂
        exact inv.made_apart t₁ t₂ c₁ c₂ w₁ w₂ different h₁' h₂'
      · intro t' c' h
        obtain ⟨different, v₀, h', stillValid⟩ := phaseAt t' c' true h
        obtain ⟨wasValid, notInvalid⟩ := stillValid rfl
        subst wasValid
        exact permits_fire_of_not_invalidates (inv.valid_permits t' c' h') notInvalid
          (inv.made_apart t' t c' c true true different h' isActive)
  | abort t =>
      exact oInv_of_retire inv t .idle (fun _ _ h => by cases h) rfl rfl rfl
  | fail t =>
      exact oInv_of_retire inv t .failed (fun _ _ h => by cases h) rfl rfl rfl

end Invariant

/-! ## Safety, inherited -/

section Safety

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {refuse : OState T O R → T → Prop}

omit [DecidableEq O] [DecidableEq T] in
/-- A committed attempt is permitted by its mode at the store where it commits. -/
theorem commit_permitted {σ : OState T O R} (inv : OInv label mode prog σ) {t : T} {c : Commit O R}
    (isActive : σ.phase t = .active c true) : Permits label mode σ.store c :=
  inv.valid_permits t c isActive

/-- The commit a step publishes, if any. -/
def published (σ : OState T O R) : OLabel T O R → List (Commit O R)
  | .commit t =>
      match σ.phase t with
      | .active c _ => [c]
      | _ => []
  | _ => []

variable (label mode prog) in
/-- The commits an execution publishes, in order. -/
def history : OState T O R → List (OLabel T O R) → List (Commit O R)
  | _, [] => []
  | σ, a :: l => published σ a ++ history (oNext label mode prog σ a) l

/-- **Refinement.** Under serializable validation, the commits of every execution form an
executable sequence of the atomic semantics, ending at the store the execution reaches. -/
theorem exec_refines {σ σ' : OState T O R} {l : List (OLabel T O R)}
    (exec : (optimistic label Mode.serializable prog refuse).Exec σ l σ')
    (inv : OInv label Mode.serializable prog σ) :
    Executable label σ.store (history label Mode.serializable prog σ l) ∧
      σ'.store = fireList σ.store (history label Mode.serializable prog σ l) := by
  induction exec with
  | nil s => exact ⟨.nil _, rfl⟩
  | @cons s a l s' allowed rest ih =>
      have allowed' : oAllowed label prog refuse s a := allowed
      obtain ⟨executable, finish⟩ := ih (oInv_next inv allowed')
      cases a with
      | commit t =>
          obtain ⟨⟨c, isActive⟩, _⟩ := allowed'
          have enabled : Enabled label s.store c :=
            (permits_serializable_iff (inv.apart t c true isActive)).1 (inv.valid_permits t c isActive)
          have nextStore : (oNext label Mode.serializable prog s (.commit t)).store = fire s.store c := by
            simp [oNext, isActive]
          simp only [history, published, isActive, List.singleton_append]
          simp only [optimistic_next] at executable finish
          rw [nextStore] at executable finish
          exact ⟨.cons enabled executable, finish⟩
      | begin t c => exact ⟨executable, finish⟩
      | abort t => exact ⟨executable, finish⟩
      | fail t => exact ⟨executable, finish⟩

end Safety

/-! ## Progress without fairness -/

section Progress

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {refuse : OState T O R → T → Prop}

/-- The weight of a phase: idle 2, valid attempt 1, invalid attempt 3, finished 0. -/
def weight : Phase O R → ℕ
  | .idle => 2
  | .active _ true => 1
  | .active _ false => 3
  | .committed => 0
  | .failed => 0

omit [DecidableEq O] in
theorem weight_le_three (p : Phase O R) : weight p ≤ 3 := by
  cases p with
  | active c v => cases v <;> simp [weight]
  | _ => simp [weight]

/-- The potential of the phases. -/
def potential [Fintype T] (phase : T → Phase O R) : ℕ := ∑ t, weight (phase t)

omit [DecidableEq O] [DecidableEq T] in
theorem potential_le [Fintype T] (phase : T → Phase O R) : potential phase ≤ 3 * Fintype.card T := by
  unfold potential
  calc ∑ t, weight (phase t) ≤ ∑ _t : T, 3 := Finset.sum_le_sum fun t _ => weight_le_three _
    _ = 3 * Fintype.card T := by simp [Finset.card_univ, mul_comm]

omit [DecidableEq O] in
theorem potential_update [Fintype T] (phase : T → Phase O R) (t : T) (p : Phase O R) :
    potential (Function.update phase t p) + weight (phase t) = potential phase + weight p := by
  have first := Finset.sum_erase_add Finset.univ (fun x => weight (Function.update phase t p x))
    (Finset.mem_univ t)
  have second := Finset.sum_erase_add Finset.univ (fun x => weight (phase x)) (Finset.mem_univ t)
  have rest : ∑ x ∈ Finset.univ.erase t, weight (Function.update phase t p x) =
      ∑ x ∈ Finset.univ.erase t, weight (phase x) :=
    Finset.sum_congr rfl fun x member => by rw [Function.update_of_ne (Finset.ne_of_mem_erase member)]
  simp only [Function.update_self] at first
  unfold potential
  omega

/-- **A step that is not a commit lowers the potential.** -/
theorem potential_next_lt [Fintype T] {σ : OState T O R} {a : OLabel T O R}
    (allowed : oAllowed label prog refuse σ a) (notCommit : ¬ a.IsCommit) :
    potential (oNext label mode prog σ a).phase + 1 ≤ potential σ.phase := by
  cases a with
  | begin t c =>
      have := potential_update σ.phase t (.active c true)
      rw [allowed.1] at this
      simp only [weight] at this
      show potential (Function.update σ.phase t (.active c true)) + 1 ≤ _
      omega
  | commit t => exact absurd trivial notCommit
  | abort t =>
      obtain ⟨c, isActive⟩ := allowed
      have := potential_update σ.phase t .idle
      rw [isActive] at this
      simp only [weight] at this
      show potential (Function.update σ.phase t .idle) + 1 ≤ _
      omega
  | fail t =>
      have := potential_update σ.phase t .failed
      rw [allowed.1] at this
      simp only [weight] at this
      show potential (Function.update σ.phase t .failed) + 1 ≤ _
      omega

/-- **Bounded lock-freedom, finite form.** An execution without commits is no longer than the
potential it starts from. -/
theorem commitFree_bound [Fintype T] {σ σ' : OState T O R} {l : List (OLabel T O R)}
    (exec : (optimistic label mode prog refuse).Exec σ l σ') (noCommit : ∀ a ∈ l, ¬ a.IsCommit) :
    l.length + potential σ'.phase ≤ potential σ.phase := by
  induction exec with
  | nil s => simp
  | @cons s a l s' allowed rest ih =>
      have step := potential_next_lt (mode := mode) allowed (noCommit a List.mem_cons_self)
      have later := ih fun b member => noCommit b (List.mem_cons_of_mem _ member)
      simp only [List.length_cons]
      have : (optimistic label mode prog refuse).next s a = oNext label mode prog s a := rfl
      rw [this] at later
      omega

/-- **Bounded lock-freedom.** In every run, every `3 * |T| + 1` consecutive steps contain a commit,
whatever the mode and the refusal policy. -/
theorem Run.commit_within [Fintype T] (r : Run (optimistic label mode prog refuse)) (n : ℕ) :
    ∃ k ≤ 3 * Fintype.card T, (r.label (n + k)).IsCommit := by
  by_contra none
  push Not at none
  have bound := commitFree_bound (r.exec_window (3 * Fintype.card T + 1) n) fun a member => by
    obtain ⟨m, lt, rfl⟩ := r.mem_window member
    exact none m (by omega)
  rw [r.length_window] at bound
  have := potential_le (r.state n).phase
  omega

/-- **Lock-freedom.** Commits happen infinitely often in every run. -/
theorem Run.commits_infinitelyOften [Fintype T] (r : Run (optimistic label mode prog refuse)) :
    InfinitelyOften fun n => (r.label n).IsCommit := by
  intro N
  obtain ⟨k, _, isCommit⟩ := r.commit_within N
  exact ⟨N + k, by omega, isCommit⟩

/-- A step of `t` that is not a commit lowers `t`'s weight. -/
theorem weight_next_lt {σ : OState T O R} {a : OLabel T O R} {t : T}
    (allowed : oAllowed label prog refuse σ a) (notCommit : ¬ a.IsCommit) (byT : a.actor = t) :
    weight ((oNext label mode prog σ a).phase t) + 1 ≤ weight (σ.phase t) := by
  cases a with
  | begin t' c =>
      have same : t' = t := byT
      subst same
      simp [oNext, allowed.1, weight]
  | commit t' => exact absurd trivial notCommit
  | abort t' =>
      have same : t' = t := byT
      subst same
      obtain ⟨c, isActive⟩ := allowed
      simp [oNext, isActive, weight]
  | fail t' =>
      have same : t' = t := byT
      subst same
      simp [oNext, allowed.1, weight]

/-- **Obstruction-freedom, finite form.** An execution of steps all by `t`, none a commit, is no
longer than `t`'s weight. -/
theorem solo_bound {σ σ' : OState T O R} {l : List (OLabel T O R)} {t : T}
    (exec : (optimistic label mode prog refuse).Exec σ l σ')
    (solo : ∀ a ∈ l, ¬ a.IsCommit ∧ a.actor = t) :
    l.length + weight (σ'.phase t) ≤ weight (σ.phase t) := by
  induction exec with
  | nil s => simp
  | @cons s a l s' allowed rest ih =>
      have step := weight_next_lt (mode := mode) allowed (solo a List.mem_cons_self).1
        (solo a List.mem_cons_self).2
      have later := ih fun b member => solo b (List.mem_cons_of_mem _ member)
      simp only [List.length_cons]
      have : (optimistic label mode prog refuse).next s a = oNext label mode prog s a := rfl
      rw [this] at later
      omega

/-- **Obstruction-freedom.** Four consecutive steps all by one transaction include a commit. -/
theorem Run.solo_commit_within (r : Run (optimistic label mode prog refuse)) (n : ℕ) {t : T}
    (solo : ∀ k < 4, (r.label (n + k)).actor = t) : ∃ k < 4, (r.label (n + k)).IsCommit := by
  by_contra none
  push Not at none
  have bound := solo_bound (t := t) (r.exec_window 4 n) fun a member => by
    obtain ⟨m, lt, rfl⟩ := r.mem_window member
    exact ⟨none m lt, solo m lt⟩
  rw [r.length_window] at bound
  have := weight_le_three ((r.state n).phase t)
  omega

end Progress

/-! ## Where nothing invalidates: wait-freedom -/

section WaitFree

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}

/-- No row of the program invalidates a row of the program under the mode. -/
def NeverInvalidated (label : O → R) (mode : Finset Check) (prog : Program T O R) : Prop :=
  ∀ t t' d c, d ∈ prog.rows t → c ∈ prog.rows t' → ¬ Invalidates label mode d c

omit [DecidableEq O] [DecidableEq T] in
/-- Unchecked mode invalidates nothing. -/
theorem neverInvalidated_unchecked [DecidableEq O] : NeverInvalidated label Mode.unchecked prog := by
  intro _ _ _ _ _ _ invalid
  simp [Invalidates, Mode.unchecked] at invalid

omit [DecidableEq T] in
/-- Rows that take nothing and query nothing invalidate nothing, in every mode. -/
theorem neverInvalidated_monotone (monotone : ∀ t, ∀ c ∈ prog.rows t, c.taken = ∅ ∧ c.queries = []) :
    NeverInvalidated label mode prog := by
  intro t t' d c rowD rowC invalid
  rcases invalid with ⟨_, clash⟩ | ⟨_, clash⟩ | ⟨_, read, member, _⟩
  · exact clash (by simp [(monotone t d rowD).1])
  · exact clash (by simp [(monotone t d rowD).1])
  · rw [(monotone t' c rowC).2] at member
    cases member

/-- Every active attempt is valid. -/
def AllValid (σ : OState T O R) : Prop := ∀ t c v, σ.phase t = .active c v → v = true

theorem allValid_next {refuse : OState T O R → T → Prop} (never : NeverInvalidated label mode prog)
    {σ : OState T O R} (inv : OInv label mode prog σ) (valid : AllValid σ) {a : OLabel T O R}
    (allowed : oAllowed label prog refuse σ a) : AllValid (oNext label mode prog σ a) := by
  intro t' c' v' h
  cases a with
  | begin t c =>
      simp only [oNext] at h
      by_cases same : t' = t
      · subst same
        simp only [Function.update_self, Phase.active.injEq] at h
        exact h.2.symm
      · rw [Function.update_of_ne same] at h
        exact valid t' c' v' h
  | commit t =>
      obtain ⟨⟨c, isActive⟩, _⟩ := allowed
      simp only [oNext, isActive] at h
      by_cases same : t' = t
      · subst same
        simp only [if_true] at h
        split_ifs at h
      · simp only [same, if_false] at h
        cases p : σ.phase t' with
        | active c₀ v₁ =>
            have v₁true : v₁ = true := valid t' c₀ v₁ p
            subst v₁true
            rw [p] at h
            have notInv := never t t' c c₀ (inv.active_row t c true isActive)
              (inv.active_row t' c₀ true p)
            simp only [invalidate, decide_eq_false notInv, Bool.not_false, Bool.and_self,
              Phase.active.injEq] at h
            exact h.2.symm
        | idle => rw [p] at h; simp [invalidate] at h
        | committed => rw [p] at h; simp [invalidate] at h
        | failed => rw [p] at h; simp [invalidate] at h
  | abort t =>
      simp only [oNext] at h
      by_cases same : t' = t
      · subst same; simp at h
      · rw [Function.update_of_ne same] at h; exact valid t' c' v' h
  | fail t =>
      simp only [oNext] at h
      by_cases same : t' = t
      · subst same; simp at h
      · rw [Function.update_of_ne same] at h; exact valid t' c' v' h

/-- **Where nothing invalidates, no reachable state allows an abort**, and every active attempt
may commit at once (wait-freedom: each firing commits at its next step after proposing). -/
theorem never_aborts (never : NeverInvalidated label mode prog) {σ₀ σ : OState T O R}
    {l : List (OLabel T O R)} (initial : OInitial σ₀)
    (exec : (optimistic label mode prog noRefusal).Exec σ₀ l σ) (t : T) :
    ¬ oAllowed label prog noRefusal σ (.abort t) ∧
      ∀ c v, σ.phase t = .active c v → oAllowed label prog noRefusal σ (.commit t) := by
  have both : OInv label mode prog σ ∧ AllValid σ := by
    have start : OInv label mode prog σ₀ ∧ AllValid σ₀ :=
      ⟨oInv_of_initial initial, fun t c v h => by rw [initial.2 t] at h; cases h⟩
    clear initial
    induction exec with
    | nil s => exact start
    | @cons s a l s' allowed rest ih =>
        exact ih ⟨oInv_next start.1 allowed, allValid_next never start.1 start.2 allowed⟩
  refine ⟨fun ⟨c, isActive⟩ => ?_, fun c v isActive => ?_⟩
  · cases both.2 t c false isActive
  · have := both.2 t c v isActive
    subst this
    exact ⟨⟨c, isActive⟩, id⟩

end WaitFree

/-! ## Tasks, and the fairness that prevents starvation -/

/-- The kinds of steps. -/
inductive StepKind where
  | begin
  | commit
  | abort
  | fail
  deriving DecidableEq

/-- The task "a step of kind `k` by `t`". -/
def kindTask (k : StepKind) (t : T) : OLabel T O R → Prop
  | .begin t' _ => k = .begin ∧ t' = t
  | .commit t' => k = .commit ∧ t' = t
  | .abort t' => k = .abort ∧ t' = t
  | .fail t' => k = .fail ∧ t' = t

/-- The task "any step by `t`" (process-level scheduling). -/
def stepTask (t : T) (a : OLabel T O R) : Prop := a.actor = t

section Fairness

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}

/-- **Strong fairness of the commit step prevents starvation.** A transaction that proposes
infinitely often commits infinitely often, if the run is strongly fair for its commit step. -/
theorem commits_of_stronglyFair_commit (r : Run (optimistic label mode prog noRefusal)) {t : T}
    (fair : r.StronglyFair (kindTask .commit t))
    (proposes : InfinitelyOften fun n => ∃ c, r.label n = .begin t c) :
    InfinitelyOften fun n => kindTask .commit t (r.label n) := by
  apply fair
  intro N
  obtain ⟨n, le, c, isBegin⟩ := proposes N
  refine ⟨n + 1, by omega, .commit t, ⟨rfl, rfl⟩, ⟨c, ?_⟩, id⟩
  rw [r.step n, isBegin]
  simp [oNext]

end Fairness

/-! ## Controls -/

namespace Controls

/-- Take token `k`. -/
def takeTok (k : ℕ) : Commit ℕ Unit := ⟨{k}, ∅, ∅, []⟩

/-- Take token `k` and make token `k + 1`. -/
def bump (k : ℕ) : Commit ℕ Unit := ⟨{k}, ∅, {k + 1}, []⟩

/-- `true` is a one-shot transaction taking a token; `false` a persistent one renewing it. -/
def starveProg : Program Bool ℕ Unit where
  rows t := if t then {c | ∃ k, c = takeTok k} else {c | ∃ k, c = bump k}
  persistent t := !t

/-- The unit label. -/
def unitLabel : ℕ → Unit := fun _ => ()

variable (mode : Finset Check)

/-- The schedule: the victim proposes, the renewer proposes and commits, the victim aborts. -/
def starveLabel (n : ℕ) : OLabel Bool ℕ Unit :=
  match n % 4 with
  | 0 => .begin true (takeTok (n / 4))
  | 1 => .begin false (bump (n / 4))
  | 2 => .commit false
  | _ => .abort true

/-- The states of the schedule. -/
def starveState : ℕ → OState Bool ℕ Unit
  | 0 => ⟨{0}, {0}, fun _ => .idle, 0, fun _ => none⟩
  | n + 1 => oNext unitLabel mode starveProg (starveState n) (starveLabel n)

theorem starveLabel_eq (k : ℕ) :
    starveLabel (4 * k) = .begin true (takeTok k) ∧ starveLabel (4 * k + 1) = .begin false (bump k) ∧
      starveLabel (4 * k + 2) = .commit false ∧ starveLabel (4 * k + 3) = .abort true := by
  have h0 : (4 * k) % 4 = 0 := by omega
  have h0' : 4 * k / 4 = k := by omega
  have h1 : (4 * k + 1) % 4 = 1 := by omega
  have h1' : (4 * k + 1) / 4 = k := by omega
  have h2 : (4 * k + 2) % 4 = 2 := by omega
  have h3 : (4 * k + 3) % 4 = 3 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [starveLabel, h0, h0', h1, h1', h2, h3]

/-- At the start of each period: one token `k`, identities up to `k` born, all idle. -/
def PeriodStart (σ : OState Bool ℕ Unit) (k : ℕ) : Prop :=
  σ.store = {k} ∧ σ.born = Finset.range (k + 1) ∧ ∀ t, σ.phase t = .idle

variable {mode}

theorem invalidates_bump_take (takes : Check.takes ∈ mode) (k : ℕ) :
    Invalidates unitLabel mode (bump k) (takeTok k) :=
  Or.inl ⟨takes, by simp [bump, takeTok]⟩

theorem takeTok_row (k : ℕ) : takeTok k ∈ starveProg.rows true := ⟨k, rfl⟩

theorem bump_row (k : ℕ) : bump k ∈ starveProg.rows false := ⟨k, rfl⟩

theorem takeTok_enabled (k : ℕ) : Enabled unitLabel {k} (takeTok k) :=
  ⟨by simp [takeTok], by simp [takeTok], by simp [takeTok], by simp [takeTok], by simp [takeTok]⟩

theorem bump_enabled (k : ℕ) : Enabled unitLabel {k} (bump k) :=
  ⟨by simp [bump], by simp [bump], by simp [bump], by simp [bump], by simp [bump]⟩

/-- One period of the schedule, step by step. -/
theorem starve_period (takes : Check.takes ∈ mode) (k : ℕ)
    (start : PeriodStart (starveState mode (4 * k)) k) :
    ((starveState mode (4 * k + 1)).store = {k} ∧
        (starveState mode (4 * k + 1)).born = Finset.range (k + 1) ∧
        (starveState mode (4 * k + 1)).phase true = .active (takeTok k) true ∧
        (starveState mode (4 * k + 1)).phase false = .idle) ∧
      ((starveState mode (4 * k + 2)).store = {k} ∧
        (starveState mode (4 * k + 2)).born = Finset.range (k + 2) ∧
        (starveState mode (4 * k + 2)).phase true = .active (takeTok k) true ∧
        (starveState mode (4 * k + 2)).phase false = .active (bump k) true) ∧
      ((starveState mode (4 * k + 3)).store = {k + 1} ∧
        (starveState mode (4 * k + 3)).born = Finset.range (k + 2) ∧
        (starveState mode (4 * k + 3)).phase true = .active (takeTok k) false ∧
        (starveState mode (4 * k + 3)).phase false = .idle) ∧
      PeriodStart (starveState mode (4 * (k + 1))) (k + 1) := by
  obtain ⟨l0, l1, l2, l3⟩ := starveLabel_eq k
  obtain ⟨store₀, born₀, phase₀⟩ := start
  have e1 : starveState mode (4 * k + 1) =
      oNext unitLabel mode starveProg (starveState mode (4 * k)) (.begin true (takeTok k)) := by
    rw [← l0]; rfl
  have e2 : starveState mode (4 * k + 2) =
      oNext unitLabel mode starveProg (starveState mode (4 * k + 1)) (.begin false (bump k)) := by
    rw [← l1]; rfl
  have e3 : starveState mode (4 * k + 3) =
      oNext unitLabel mode starveProg (starveState mode (4 * k + 2)) (.commit false) := by
    rw [← l2]; rfl
  have e4 : starveState mode (4 * (k + 1)) =
      oNext unitLabel mode starveProg (starveState mode (4 * k + 3)) (.abort true) := by
    rw [show 4 * (k + 1) = 4 * k + 3 + 1 by ring, ← l3]; rfl
  have s1 : (starveState mode (4 * k + 1)).store = {k} ∧
      (starveState mode (4 * k + 1)).born = Finset.range (k + 1) ∧
      (starveState mode (4 * k + 1)).phase true = .active (takeTok k) true ∧
      (starveState mode (4 * k + 1)).phase false = .idle := by
    rw [e1]
    refine ⟨by simp [oNext, store₀], by simp [oNext, born₀, takeTok], by simp [oNext], ?_⟩
    simp [oNext, phase₀]
  obtain ⟨store₁, born₁, true₁, false₁⟩ := s1
  have s2 : (starveState mode (4 * k + 2)).store = {k} ∧
      (starveState mode (4 * k + 2)).born = Finset.range (k + 2) ∧
      (starveState mode (4 * k + 2)).phase true = .active (takeTok k) true ∧
      (starveState mode (4 * k + 2)).phase false = .active (bump k) true := by
    rw [e2]
    refine ⟨by simp [oNext, store₁], ?_, by simp [oNext, true₁], by simp [oNext]⟩
    simp only [oNext, born₁, bump]
    ext o
    simp [Finset.mem_range]
    omega
  obtain ⟨store₂, born₂, true₂, false₂⟩ := s2
  have s3 : (starveState mode (4 * k + 3)).store = {k + 1} ∧
      (starveState mode (4 * k + 3)).born = Finset.range (k + 2) ∧
      (starveState mode (4 * k + 3)).phase true = .active (takeTok k) false ∧
      (starveState mode (4 * k + 3)).phase false = .idle := by
    rw [e3]
    refine ⟨?_, by simp [oNext, false₂, born₂], ?_, by simp [oNext, false₂, starveProg]⟩
    · simp only [oNext, false₂, store₂]
      ext o
      simp [bump, mem_fire]
    · simp [oNext, false₂, true₂, invalidate, invalidates_bump_take takes k]
  obtain ⟨store₃, born₃, true₃, false₃⟩ := s3
  refine ⟨⟨store₁, born₁, true₁, false₁⟩, ⟨store₂, born₂, true₂, false₂⟩,
    ⟨store₃, born₃, true₃, false₃⟩, ?_⟩
  rw [e4]
  refine ⟨by simp [oNext, store₃], by simp [oNext, born₃], fun t => ?_⟩
  cases t
  · simp [oNext, false₃]
  · simp [oNext]

theorem starve_start (takes : Check.takes ∈ mode) : ∀ k, PeriodStart (starveState mode (4 * k)) k := by
  intro k
  induction k with
  | zero => exact ⟨rfl, by simp [starveState], fun _ => rfl⟩
  | succ k ih => exact (starve_period takes k ih).2.2.2

theorem starve_allowed (takes : Check.takes ∈ mode) (n : ℕ) :
    oAllowed unitLabel starveProg noRefusal (starveState mode n) (starveLabel n) := by
  obtain ⟨k, j, lt, rfl⟩ : ∃ k j, j < 4 ∧ n = 4 * k + j :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 4).symm⟩
  obtain ⟨l0, l1, l2, l3⟩ := starveLabel_eq k
  have start := starve_start takes k
  obtain ⟨⟨store₁, born₁, true₁, false₁⟩, ⟨_, _, _, false₂⟩, ⟨_, _, true₃, _⟩, _⟩ :=
    starve_period takes k start
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [Nat.add_zero, l0]
    refine ⟨start.2.2 true, takeTok_row k, ?_, by simp [takeTok]⟩
    rw [start.1]
    exact takeTok_enabled k
  · rw [l1]
    refine ⟨false₁, bump_row k, ?_, ?_⟩
    · rw [store₁]; exact bump_enabled k
    · rw [born₁]; simp [bump]
  · rw [l2]
    exact ⟨⟨bump k, false₂⟩, id⟩
  · rw [l3]
    exact ⟨takeTok k, true₃⟩

/-- The starving run. -/
def starveRun (takes : Check.takes ∈ mode) : Run (optimistic unitLabel mode starveProg noRefusal) where
  state := starveState mode
  label := starveLabel
  allowed := starve_allowed takes
  step _ := rfl

/-- At the start of every period only proposals are enabled. -/
theorem starve_disabled_at_start (takes : Check.takes ∈ mode) (k : ℕ) {kind : StepKind} {x : Bool}
    (notBegin : kind ≠ .begin) :
    ¬ (optimistic unitLabel mode starveProg noRefusal).TaskEnabled (kindTask kind x)
      (starveState mode (4 * k)) := by
  obtain ⟨store₀, born₀, phase₀⟩ := starve_start takes k
  rintro ⟨a, inTask, allowed⟩
  cases a with
  | begin t c => exact notBegin inTask.1
  | commit t =>
      obtain ⟨⟨c, isActive⟩, _⟩ := allowed
      rw [phase₀] at isActive
      cases isActive
  | abort t =>
      obtain ⟨c, isActive⟩ := allowed
      rw [phase₀] at isActive
      cases isActive
  | fail t =>
      obtain ⟨_, oneShot, noMatch⟩ := allowed
      cases t
      · simp [starveProg] at oneShot
      · apply noMatch
        refine ⟨takeTok k, takeTok_row k, ?_, by simp [takeTok]⟩
        show Enabled unitLabel (starveState mode (4 * k)).store (takeTok k)
        rw [store₀]
        exact takeTok_enabled k

/-- **Optimistic validation is not wait-free.** In the starving run the victim takes infinitely
many steps and never commits, while the renewer commits infinitely often. The run is weakly fair
for every step kind of every transaction, and for every transaction's steps as a whole; it is not
strongly fair for the victim's commit step. Aborts are never gratuitous (an abort needs an invalid
attempt). -/
theorem optimistic_starvation (takes : Check.takes ∈ mode) :
    (∀ n, ¬ kindTask .commit true ((starveRun takes).label n)) ∧
      InfinitelyOften (fun n => stepTask true ((starveRun takes).label n)) ∧
      InfinitelyOften (fun n => kindTask .commit false ((starveRun takes).label n)) ∧
      (∀ kind x, (starveRun takes).WeaklyFair (kindTask kind x)) ∧
      (∀ x, (starveRun takes).StronglyFair (stepTask x)) ∧
      ¬ (starveRun takes).StronglyFair (kindTask .commit true) := by
  have labelAt : ∀ n, ∃ k j, j < 4 ∧ n = 4 * k + j := fun n =>
    ⟨n / 4, n % 4, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 4).symm⟩
  have never : ∀ n, ¬ kindTask .commit true ((starveRun takes).label n) := by
    intro n
    obtain ⟨k, j, lt, rfl⟩ := labelAt n
    obtain ⟨l0, l1, l2, l3⟩ := starveLabel_eq k
    show ¬ kindTask .commit true (starveLabel (4 * k + j))
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rw [Nat.add_zero, l0]; simp [kindTask]
    · rw [l1]; simp [kindTask]
    · rw [l2]; simp [kindTask]
    · rw [l3]; simp [kindTask]
  have often : ∀ (P : OLabel Bool ℕ Unit → Prop) (j : ℕ), j < 4 →
      (∀ k, P (starveLabel (4 * k + j))) → InfinitelyOften fun n => P ((starveRun takes).label n) :=
    fun P j _ holds N => ⟨4 * N + j, by omega, holds N⟩
  have victimSteps : InfinitelyOften fun n => stepTask true ((starveRun takes).label n) :=
    often _ 0 (by decide) fun k => by rw [Nat.add_zero, (starveLabel_eq k).1]; rfl
  have renewerSteps : InfinitelyOften fun n => stepTask false ((starveRun takes).label n) :=
    often _ 1 (by decide) fun k => by rw [(starveLabel_eq k).2.1]; rfl
  have renewerCommits : InfinitelyOften fun n => kindTask .commit false ((starveRun takes).label n) :=
    often _ 2 (by decide) fun k => by rw [(starveLabel_eq k).2.2.1]; exact ⟨rfl, rfl⟩
  have notAlways : ∀ kind x, kind ≠ .begin → (starveRun takes).WeaklyFair (kindTask kind x) := by
    rintro kind x notBegin ⟨N, always⟩
    exact absurd (always (4 * N) (by omega)) (starve_disabled_at_start takes N notBegin)
  refine ⟨never, victimSteps, renewerCommits, fun kind x => ?_, fun x => ?_, fun fair => ?_⟩
  · cases kind <;> cases x
    · exact fun _ => often _ 1 (by decide) fun k => by rw [(starveLabel_eq k).2.1]; exact ⟨rfl, rfl⟩
    · exact fun _ => often _ 0 (by decide) fun k => by
        rw [Nat.add_zero, (starveLabel_eq k).1]; exact ⟨rfl, rfl⟩
    · exact fun _ => renewerCommits
    · exact notAlways _ _ (by decide)
    · exact notAlways _ _ (by decide)
    · exact fun _ => often _ 3 (by decide) fun k => by rw [(starveLabel_eq k).2.2.2]; exact ⟨rfl, rfl⟩
    · exact notAlways _ _ (by decide)
    · exact notAlways _ _ (by decide)
  · cases x
    · exact fun _ => renewerSteps
    · exact fun _ => victimSteps
  · obtain ⟨n, _, fires⟩ := fair (fun N => ⟨4 * N + 1, by omega, .commit true, ⟨rfl, rfl⟩,
      ⟨⟨takeTok N, (starve_period takes N (starve_start takes N)).1.2.2.1⟩, id⟩⟩) 0
    exact never n fires

/-- **Invalidates, negative**: under `snapshot` a take of token `0` does not invalidate a take of
token `2`: their takes are apart. (`invalidates_bump_take` is the positive control.) -/
theorem disjoint_takes_not_invalidating :
    ¬ Invalidates unitLabel Mode.snapshot (takeTok 0) (takeTok 2) := by
  unfold Mode.snapshot; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
