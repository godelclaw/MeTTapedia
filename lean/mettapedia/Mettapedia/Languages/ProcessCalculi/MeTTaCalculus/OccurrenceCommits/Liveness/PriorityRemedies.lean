import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.OptimisticRetries

/-!
# Remedies for starvation: the elder wins

Optimistic validation lets a transaction lose forever (`OptimisticRetries.Controls.optimistic_starvation`)
unless the scheduler is strongly fair for its commit step. The classical remedies resolve conflicts
by a **priority order on firings**: a commit that would invalidate a valid attempt of an *elder*
is refused, and the younger waits (`elderRefusal`). This module proves when that makes **weak,
process-level fairness** enough: every scheduler that keeps running a transaction that can step
then decides every one-shot transaction.

## The elder-wins theorem (`decided_of_elder_rule`)

A priority key assigns some firings a number; an elder has a key smaller than the other's, or the
other has none. For a one-shot transaction `t` with key `a` from some time on, the run being weakly
fair for every transaction's steps, `t` commits or fails, provided the keys behave as a priority
order of type at most ω around `t` (`ElderHyps`):

* `t`'s key stays `a`; a transaction's key changes only at its own steps;
* no new elder of `t` appears;
* an elder of `t` that commits is no longer an elder, or is finished;
* no other transaction shares `t`'s key.

The proof: elders of `t` that are not finished never become more, and each elder commit removes
one, so after some time no elder commits (`elderCommits_eventually_stop`). After that, an elder
whose valid attempt is active can only be invalidated by an older elder's commit, so it stays
valid; the eldest such elder is never refused, so by weak fairness it would commit: there is none
(`no_valid_elder`). Then `t` is never invalidated and never refused, its steps stay enabled, and
its weight (`OptimisticRetries.weight`) drops at each of its steps: it is decided.

## Instances

* **Aging** (`aging_decides`): the key is the time the current firing first proposed (`OState.age`),
  kept across re-matching. Every one-shot transaction of a run from an initial state is decided,
  under weak fairness of every transaction's steps.
* **A fixed order** (`sequenced_decides`): the key is a position in a log fixed in advance, for
  example by a sequencer as in deterministic databases. Every transaction is decided, under the same
  fairness, when all transactions are one-shot.

## Control

* `Controls.staticPriority_starves`: priority by a fixed rank of *processes* is not a priority of
  firings: a persistent elder process regenerates its firings, so its elder commits never stop.
  The starving schedule of `OptimisticRetries` is a run under that policy, weakly fair for both
  processes, and the victim never commits. What matters is retirement: an elder's key must not
  survive its commit.

So the fairness each strategy needs (with `OptimisticRetries`): no remedy needs strong fairness of
the commit step; aging and a fixed order need only weak fairness of each transaction's steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {T : Type w} [DecidableEq T]

/-- A finished transaction: committed or failed. -/
def Finished : Phase O R → Prop
  | .committed => True
  | .failed => True
  | _ => False

section Policy

variable (label : O → R) (mode : Finset Check) (key : OState T O R → T → Option ℕ)

/-- `g` is an elder of `u`: it has a key, and `u` has none or a larger one. -/
def Elder (σ : OState T O R) (g u : T) : Prop :=
  ∃ b, key σ g = some b ∧ ∀ b', key σ u = some b' → b < b'

/-- **The elder wins**: refuse a commit that would invalidate a valid attempt of an elder. -/
def elderRefusal (σ : OState T O R) (u : T) : Prop :=
  ∃ g, g ≠ u ∧ Elder key σ g u ∧ ∃ c d, σ.phase g = .active c true ∧ σ.phase u = .active d true ∧
    Invalidates label mode d c

end Policy

/-- Aging: the key is the time the current firing first proposed. -/
def agingKey : OState T O R → T → Option ℕ := fun σ t => σ.age t

/-- A fixed order: the key is a position fixed in advance. -/
def sequenceKey (seq : T → ℕ) : OState T O R → T → Option ℕ := fun _ t => some (seq t)

/-! ## Steps, phase by phase -/

section Steps

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {refuse : OState T O R → T → Prop}

/-- A finished transaction stays finished. -/
theorem finished_next {σ : OState T O R} {a : OLabel T O R} (allowed : oAllowed label prog refuse σ a)
    {x : T} (finished : Finished (σ.phase x)) : Finished ((oNext label mode prog σ a).phase x) := by
  cases a with
  | begin t c =>
      by_cases same : x = t
      · subst same; rw [allowed.1] at finished; exact absurd finished id
      · simpa [oNext, Function.update_of_ne same] using finished
  | commit t =>
      obtain ⟨⟨c, isActive⟩, _⟩ := allowed
      by_cases same : x = t
      · subst same; rw [isActive] at finished; exact absurd finished id
      · simp only [oNext, isActive, same, if_false]
        cases p : σ.phase x with
        | committed => simp [invalidate, Finished]
        | failed => simp [invalidate, Finished]
        | idle => rw [p] at finished; exact absurd finished id
        | active c v => rw [p] at finished; exact absurd finished id
  | abort t =>
      obtain ⟨c, isActive⟩ := allowed
      by_cases same : x = t
      · subst same; rw [isActive] at finished; exact absurd finished id
      · simpa [oNext, Function.update_of_ne same] using finished
  | fail t =>
      by_cases same : x = t
      · subst same; rw [allowed.1] at finished; exact absurd finished id
      · simpa [oNext, Function.update_of_ne same] using finished

/-- A step by another transaction leaves a phase alone, unless it is a commit that invalidates a
valid attempt. -/
theorem phase_next_of_ne {σ : OState T O R} {a : OLabel T O R} (allowed : oAllowed label prog refuse σ a)
    {x : T} (other : a.actor ≠ x) :
    (oNext label mode prog σ a).phase x = σ.phase x ∨
      ∃ u c d, a = .commit u ∧ σ.phase u = .active d true ∧ σ.phase x = .active c true ∧
        (oNext label mode prog σ a).phase x = .active c false ∧ Invalidates label mode d c := by
  cases a with
  | begin t c =>
      left
      have ne : x ≠ t := fun h => other h.symm
      simp [oNext, Function.update_of_ne ne]
  | commit t =>
      obtain ⟨⟨d, isActive⟩, _⟩ := allowed
      have ne : x ≠ t := fun h => other h.symm
      simp only [oNext, isActive, ne, if_false]
      cases p : σ.phase x with
      | active c v =>
          by_cases invalid : Invalidates label mode d c
          · cases v with
            | false => left; simp [invalidate]
            | true => exact Or.inr ⟨t, c, d, rfl, isActive, rfl, by simp [invalidate, invalid], invalid⟩
          · left; simp [invalidate, invalid]
      | idle => left; rfl
      | committed => left; rfl
      | failed => left; rfl
  | abort t =>
      left
      have ne : x ≠ t := fun h => other h.symm
      simp [oNext, Function.update_of_ne ne]
  | fail t =>
      left
      have ne : x ≠ t := fun h => other h.symm
      simp [oNext, Function.update_of_ne ne]

/-- **What invalidates an attempt**: a commit of another transaction, valid at that moment. -/
theorem invalidation_cause {σ : OState T O R} {a : OLabel T O R} (allowed : oAllowed label prog refuse σ a)
    {x : T} {c : Commit O R} (before : σ.phase x = .active c true)
    (after : (oNext label mode prog σ a).phase x = .active c false) :
    ∃ u d, a = .commit u ∧ u ≠ x ∧ σ.phase u = .active d true ∧ Invalidates label mode d c ∧
      ¬ refuse σ u := by
  by_cases mine : a.actor = x
  · exfalso
    cases a with
    | begin t c' =>
        have same : t = x := mine
        subst same
        rw [allowed.1] at before
        cases before
    | commit t =>
        have same : t = x := mine
        subst same
        obtain ⟨⟨d, isActive⟩, _⟩ := allowed
        simp only [oNext, isActive, if_true] at after
        split_ifs at after
    | abort t =>
        have same : t = x := mine
        subst same
        obtain ⟨d, isActive⟩ := allowed
        rw [isActive] at before
        simp only [Phase.active.injEq] at before
        exact Bool.false_ne_true before.2
    | fail t =>
        have same : t = x := mine
        subst same
        rw [allowed.1] at before
        cases before
  · rcases phase_next_of_ne (mode := mode) allowed mine with same | ⟨u, c', d, rfl, activeU, activeX, _, invalid⟩
    · rw [same, before] at after
      simp at after
    · rw [before] at activeX
      simp only [Phase.active.injEq, and_true] at activeX
      subst activeX
      have ne : u ≠ x := mine
      exact ⟨u, d, rfl, ne, activeU, invalid, allowed.2⟩

end Steps

/-! ## Runs with an idle step -/

section Runs

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {refuse : OState T O R → T → Prop}

/-- A step of a run with idling: idle, or an allowed step of the system. -/
theorem idle_or_step (r : Run (optimistic label mode prog refuse).withIdle) (n : ℕ) :
    (r.label n = none ∧ r.state (n + 1) = r.state n) ∨
      ∃ a, r.label n = some a ∧ oAllowed label prog refuse (r.state n) a ∧
        r.state (n + 1) = oNext label mode prog (r.state n) a := by
  have step := r.step n
  have allowed := r.allowed n
  cases labelIs : r.label n with
  | none => exact Or.inl ⟨rfl, by rw [step, labelIs]; rfl⟩
  | some a =>
      rw [labelIs] at allowed
      exact Or.inr ⟨a, rfl, allowed, by rw [step, labelIs]; rfl⟩

/-- The invariant holds along a run that starts in it. -/
theorem idleRun_oInv (r : Run (optimistic label mode prog refuse).withIdle)
    (init : OInv label mode prog (r.state 0)) : ∀ n, OInv label mode prog (r.state n) := by
  intro n
  induction n with
  | zero => exact init
  | succ n ih =>
      rcases idle_or_step r n with ⟨_, same⟩ | ⟨a, _, allowed, next⟩
      · rw [same]; exact ih
      · rw [next]; exact oInv_next ih allowed

/-- Finished stays finished along a run. -/
theorem idleRun_finished (r : Run (optimistic label mode prog refuse).withIdle) {x : T} {n : ℕ}
    (finished : Finished ((r.state n).phase x)) : ∀ m ≥ n, Finished ((r.state m).phase x) := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => exact finished
  | succ m _ ih =>
      rcases idle_or_step r m with ⟨_, same⟩ | ⟨a, _, allowed, next⟩
      · rw [same]; exact ih
      · rw [next]; exact finished_next allowed ih

/-- A transaction that can step makes its step task enabled. -/
theorem stepTask_enabled_of_allowed {σ : OState T O R} {a : OLabel T O R}
    (allowed : oAllowed label prog refuse σ a) :
    (optimistic label mode prog refuse).withIdle.TaskEnabled (LTS.liftTask (stepTask a.actor)) σ :=
  (LTS.withIdle_taskEnabled_iff _ _ _).2 ⟨a, rfl, allowed⟩

omit [DecidableEq O] [DecidableEq T] in
/-- An idle one-shot transaction can always step: propose a row, or fail. -/
theorem idle_can_step {σ : OState T O R} {t : T} (idle : σ.phase t = .idle)
    (oneShot : prog.persistent t = false) :
    ∃ a : OLabel T O R, a.actor = t ∧ oAllowed label prog refuse σ a := by
  by_cases canMatch : CanMatch label prog σ t
  · obtain ⟨c, row, enabled, fresh⟩ := canMatch
    exact ⟨.begin t c, rfl, idle, row, enabled, fresh⟩
  · exact ⟨.fail t, rfl, idle, oneShot, canMatch⟩

end Runs

/-! ## The elder-wins theorem -/

section Elder

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {key : OState T O R → T → Option ℕ}

/-- The hypotheses on the keys, around a transaction `t` with key `a` from time `n₀`. -/
structure ElderHyps (key : OState T O R → T → Option ℕ)
    (r : Run (optimistic label mode prog (elderRefusal label mode key)).withIdle)
    (t : T) (n₀ a : ℕ) : Prop where
  keyed : ∀ n ≥ n₀, key (r.state n) t = some a
  keyStable : ∀ n ≥ n₀, ∀ g, (∀ b, r.label n = some b → b.actor ≠ g) →
    key (r.state (n + 1)) g = key (r.state n) g
  noNewElders : ∀ n ≥ n₀, ∀ g b, key (r.state (n + 1)) g = some b → b < a →
    key (r.state n) g = some b
  retires : ∀ n ≥ n₀, ∀ g b, r.label n = some (.commit g) → key (r.state n) g = some b → b < a →
    key (r.state (n + 1)) g = none ∨ Finished ((r.state (n + 1)).phase g)
  distinct : ∀ n ≥ n₀, ∀ g, key (r.state n) g = some a → g = t

variable {r : Run (optimistic label mode prog (elderRefusal label mode key)).withIdle}
  {t : T} {n₀ a : ℕ}

/-- `g` is an elder of `t` at time `n`. -/
def ElderAt (key : OState T O R → T → Option ℕ)
    (r : Run (optimistic label mode prog (elderRefusal label mode key)).withIdle) (a n : ℕ)
    (g : T) : Prop :=
  ∃ b, key (r.state n) g = some b ∧ b < a

/-- An elder of `t` commits at time `n`. -/
def ElderCommit (key : OState T O R → T → Option ℕ)
    (r : Run (optimistic label mode prog (elderRefusal label mode key)).withIdle) (a n : ℕ) : Prop :=
  ∃ g, r.label n = some (.commit g) ∧ ElderAt key r a n g

theorem elder_iff (hyps : ElderHyps key r t n₀ a) {n : ℕ} (le : n₀ ≤ n) {g : T} :
    Elder key (r.state n) g t ↔ ElderAt key r a n g := by
  rw [Elder, hyps.keyed n le]
  constructor
  · rintro ⟨b, isKey, below⟩
    exact ⟨b, isKey, below a rfl⟩
  · rintro ⟨b, isKey, below⟩
    exact ⟨b, isKey, fun b' same => by cases same; exact below⟩

open Classical in
/-- The elders of `t` that are not finished. -/
noncomputable def liveElders (key : OState T O R → T → Option ℕ)
    (r : Run (optimistic label mode prog (elderRefusal label mode key)).withIdle) (a n : ℕ)
    [Fintype T] : Finset T :=
  Finset.univ.filter fun g => ElderAt key r a n g ∧ ¬ Finished ((r.state n).phase g)

/-- **Elder commits eventually stop.** -/
theorem elderCommits_eventually_stop [Fintype T] (hyps : ElderHyps key r t n₀ a) :
    ∃ N ≥ n₀, ∀ n ≥ N, ¬ ElderCommit key r a n := by
  classical
  have mono : ∀ n ≥ n₀, liveElders key r a (n + 1) ⊆ liveElders key r a n := by
    intro n le g member
    simp only [liveElders, Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    obtain ⟨⟨b, isKey, below⟩, notFinished⟩ := member
    refine ⟨⟨b, hyps.noNewElders n le g b isKey below, below⟩, fun finished => notFinished ?_⟩
    exact idleRun_finished r finished (n + 1) (Nat.le_succ n)
  have drop : ∀ n ≥ n₀, ElderCommit key r a n →
      (liveElders key r a (n + 1)).card < (liveElders key r a n).card := by
    rintro n le ⟨g, isCommit, b, isKey, below⟩
    have allowed := r.allowed n
    rw [isCommit] at allowed
    obtain ⟨⟨c, isActive⟩, _⟩ := allowed
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset (mono n le)).2 ⟨g, ?_, ?_⟩
    · simp only [liveElders, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨b, isKey, below⟩, by rw [isActive]; exact id⟩
    · simp only [liveElders, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
      intro ⟨b', isKey', _⟩
      rcases hyps.retires n le g b isCommit isKey below with gone | finished
      · rw [gone] at isKey'; cases isKey'
      · exact finished
  have notOften := not_infinitelyOften_of_descent (P := ElderCommit key r a)
    (fun n => (liveElders key r a n).card) n₀
    (fun n le => Finset.card_le_card (mono n le)) drop
  obtain ⟨N, never⟩ := not_infinitelyOften_iff.mp notOften
  exact ⟨max N n₀, le_max_right _ _, fun n le => never n (le_of_max_le_left le)⟩

/-- An attempt of an elder (or of `t`) invalidated after time `N` points at an elder commit. -/
theorem elderCommit_of_invalidation (hyps : ElderHyps key r t n₀ a) {n : ℕ} (le : n₀ ≤ n) {x : T}
    {c : Commit O R} {bx : ℕ} (keyX : key (r.state n) x = some bx) (bound : bx ≤ a)
    (distinctX : bx = a → x = t)
    (before : (r.state n).phase x = .active c true)
    (after : (r.state (n + 1)).phase x = .active c false) : ElderCommit key r a n := by
  rcases idle_or_step r n with ⟨_, same⟩ | ⟨step, isLabel, allowed, next⟩
  · rw [same, before] at after
    simp at after
  · rw [next] at after
    obtain ⟨u, d, rfl, ne, activeU, invalid, notRefused⟩ := invalidation_cause allowed before after
    refine ⟨u, isLabel, ?_⟩
    by_contra notElder
    apply notRefused
    refine ⟨x, Ne.symm ne, ⟨bx, keyX, fun b' keyU => ?_⟩, c, d, before, activeU, invalid⟩
    by_contra notBelow
    push Not at notBelow
    rcases lt_or_eq_of_le (notBelow.trans bound) with lt | eq
    · exact notElder ⟨b', keyU, lt⟩
    · have := hyps.distinct n le u (by rw [keyU, eq])
      have xIsT := distinctX (le_antisymm bound (eq ▸ notBelow))
      exact ne (this.trans xIsT.symm)

/-- After elder commits stop, a valid elder stays valid, keeps its key, and takes no step. -/
theorem valid_elder_stays (hyps : ElderHyps key r t n₀ a) {N : ℕ} (leN : n₀ ≤ N)
    (stop : ∀ n ≥ N, ¬ ElderCommit key r a n) {g : T} {c : Commit O R} {m b : ℕ} (leM : N ≤ m)
    (keyG : key (r.state m) g = some b) (below : b < a)
    (valid : (r.state m).phase g = .active c true) :
    ∀ n ≥ m, key (r.state n) g = some b ∧ (r.state n).phase g = .active c true ∧
      ∀ step, r.label n = some step → step.actor ≠ g := by
  have stepFacts : ∀ n ≥ m, key (r.state n) g = some b → (r.state n).phase g = .active c true →
      (∀ step, r.label n = some step → step.actor ≠ g) := by
    intro n le keyN validN step isLabel mine
    have allowed := r.allowed n
    rw [isLabel] at allowed
    cases step with
    | begin u c' =>
        have same : u = g := mine
        subst same
        rw [allowed.1] at validN
        cases validN
    | commit u =>
        have same : u = g := mine
        subst same
        exact stop n (by omega) ⟨u, isLabel, b, keyN, below⟩
    | abort u =>
        have same : u = g := mine
        subst same
        obtain ⟨c', isActive⟩ := allowed
        rw [isActive] at validN
        simp only [Phase.active.injEq] at validN
        exact Bool.false_ne_true validN.2
    | fail u =>
        have same : u = g := mine
        subst same
        rw [allowed.1] at validN
        cases validN
  have invariant : ∀ n ≥ m, key (r.state n) g = some b ∧ (r.state n).phase g = .active c true := by
    intro n le
    induction n, le using Nat.le_induction with
    | base => exact ⟨keyG, valid⟩
    | succ n le ih =>
        obtain ⟨keyN, validN⟩ := ih
        have notMine := stepFacts n le keyN validN
        have keyNext : key (r.state (n + 1)) g = some b := by
          rw [hyps.keyStable n (by omega) g notMine, keyN]
        refine ⟨keyNext, ?_⟩
        rcases idle_or_step r n with ⟨_, same⟩ | ⟨step, isLabel, allowed, next⟩
        · rw [same]; exact validN
        · rcases phase_next_of_ne (mode := mode) allowed (notMine step isLabel) with
            same | ⟨u, c', d, _, _, activeG, afterG, _⟩
          · rw [next, same]; exact validN
          · rw [validN] at activeG
            simp only [Phase.active.injEq, and_true] at activeG
            subst activeG
            exact absurd (elderCommit_of_invalidation hyps (by omega) keyN below.le
              (fun eq => absurd eq (Nat.ne_of_lt below)) validN (by rw [next]; exact afterG))
              (stop n (by omega))
  intro n le
  obtain ⟨keyN, validN⟩ := invariant n le
  exact ⟨keyN, validN, stepFacts n le keyN validN⟩

/-- **After elder commits stop, no elder has a valid attempt.** -/
theorem no_valid_elder [Fintype T] (hyps : ElderHyps key r t n₀ a)
    (fair : ∀ x, r.WeaklyFair (LTS.liftTask (stepTask x))) {N : ℕ} (leN : n₀ ≤ N)
    (stop : ∀ n ≥ N, ¬ ElderCommit key r a n) :
    ∀ n ≥ N, ∀ g, ElderAt key r a n g → ∀ c, (r.state n).phase g ≠ .active c true := by
  classical
  by_contra existsValid
  push Not at existsValid
  -- the elders that have a valid attempt at some time after `N`
  let Witness : T → Prop := fun g => ∃ m ≥ N, ElderAt key r a m g ∧ ∃ c, (r.state m).phase g = .active c true
  have chosen : ∀ g, Witness g → ∃ m b c, N ≤ m ∧ key (r.state m) g = some b ∧ b < a ∧
      (r.state m).phase g = .active c true := by
    rintro g ⟨m, le, ⟨b, keyG, below⟩, c, valid⟩
    exact ⟨m, b, c, le, keyG, below, valid⟩
  -- the key of a witnessed elder is the same at all its witnessing times
  have keyAt : ∀ g m b c m' b' c', N ≤ m → key (r.state m) g = some b → b < a →
      (r.state m).phase g = .active c true → N ≤ m' → key (r.state m') g = some b' → b' < a →
      (r.state m').phase g = .active c' true → b = b' := by
    intro g m b c m' b' c' le keyG below valid le' keyG' below' valid'
    rcases le_total m m' with first | second
    · have := (valid_elder_stays hyps leN stop le keyG below valid m' first).1
      rw [keyG'] at this
      exact (Option.some.inj this).symm
    · have := (valid_elder_stays hyps leN stop le' keyG' below' valid' m second).1
      rw [keyG] at this
      exact Option.some.inj this
  let V : Finset T := Finset.univ.filter Witness
  obtain ⟨n₁, le₁, g₁, elder₁, c₁, valid₁⟩ := existsValid
  have nonempty : V.Nonempty := ⟨g₁, by simp [V, Witness]; exact ⟨n₁, le₁, elder₁, c₁, valid₁⟩⟩
  let keyOf : T → ℕ := fun g =>
    if h : Witness g then Classical.choose (Classical.choose_spec (chosen g h)) else 0
  obtain ⟨g, inV, least⟩ := Finset.exists_min_image V keyOf nonempty
  have witness : Witness g := by simpa [V] using inV
  obtain ⟨m, b, c, le, keyG, below, valid⟩ := chosen g witness
  have keyOfG : keyOf g = b := by
    have spec := Classical.choose_spec (Classical.choose_spec (chosen g witness))
    obtain ⟨c', le', keyG', below', valid'⟩ := spec
    simp only [keyOf, dif_pos witness]
    exact keyAt g _ _ _ m b c le' keyG' below' valid' le keyG below valid
  have stays := valid_elder_stays hyps leN stop le keyG below valid
  -- from `m` on, the eldest witnessed elder is never refused
  have enabled : ∀ n ≥ m, (optimistic label mode prog (elderRefusal label mode key)).withIdle.TaskEnabled
      (LTS.liftTask (stepTask g)) (r.state n) := by
    intro n leN'
    obtain ⟨keyN, validN, _⟩ := stays n leN'
    refine stepTask_enabled_of_allowed (a := .commit g) ⟨⟨c, validN⟩, ?_⟩
    rintro ⟨h, ne, ⟨bh, keyH, olderH⟩, ch, dg, validH, validG, _⟩
    have bhBelow : bh < b := olderH b keyN
    have witnessH : Witness h := ⟨n, by omega, ⟨bh, keyH, by omega⟩, ch, validH⟩
    have keyOfH : keyOf h = bh := by
      have spec := Classical.choose_spec (Classical.choose_spec (chosen h witnessH))
      obtain ⟨c', le', keyH', below', valid'⟩ := spec
      simp only [keyOf, dif_pos witnessH]
      exact keyAt h _ _ _ n bh ch le' keyH' below' valid' (by omega) keyH (by omega) validH
    have := least h (by simp [V]; exact witnessH)
    omega
  obtain ⟨n, leN', fires⟩ := (fair g) ⟨m, enabled⟩ m
  obtain ⟨_, _, notMine⟩ := stays n leN'
  cases labelIs : r.label n with
  | none => rw [labelIs] at fires; exact fires
  | some step =>
      rw [labelIs] at fires
      exact notMine step labelIs fires

/-- **The elder-wins theorem.** Under the elder rule and weak fairness of every transaction's
steps, a one-shot transaction whose key behaves as a priority of type at most ω is decided. -/
theorem decided_of_elder_rule [Fintype T] (hyps : ElderHyps key r t n₀ a)
    (fair : ∀ x, r.WeaklyFair (LTS.liftTask (stepTask x))) (oneShot : prog.persistent t = false) :
    ∃ n, Finished ((r.state n).phase t) := by
  obtain ⟨N, leN, stop⟩ := elderCommits_eventually_stop hyps
  have noElder := no_valid_elder hyps fair leN stop
  by_contra never
  push Not at never
  -- `t` is never invalidated after `N`
  have notInvalidated : ∀ n ≥ N, ∀ c, (r.state n).phase t = .active c true →
      (r.state (n + 1)).phase t ≠ .active c false := by
    intro n le c before after
    exact stop n le (elderCommit_of_invalidation hyps (by omega) (hyps.keyed n (by omega)) le_rfl
      (fun _ => rfl) before after)
  -- `t` can always step after `N`
  have enabled : ∀ n ≥ N, (optimistic label mode prog (elderRefusal label mode key)).withIdle.TaskEnabled
      (LTS.liftTask (stepTask t)) (r.state n) := by
    intro n le
    cases phase : (r.state n).phase t with
    | idle =>
        obtain ⟨step, actor, allowed⟩ := idle_can_step (refuse := elderRefusal label mode key) phase oneShot
        rw [← actor]
        exact stepTask_enabled_of_allowed allowed
    | active c v =>
        cases v with
        | false => exact stepTask_enabled_of_allowed (a := .abort t) ⟨c, phase⟩
        | true =>
            refine stepTask_enabled_of_allowed (a := .commit t) ⟨⟨c, phase⟩, ?_⟩
            rintro ⟨g, _, elder, cg, _, validG, _, _⟩
            exact noElder n le g ((elder_iff hyps (by omega)).1 elder) cg validG
    | committed => exact absurd (by rw [phase]; trivial) (never n)
    | failed => exact absurd (by rw [phase]; trivial) (never n)
  have often := (fair t) ⟨N, enabled⟩
  -- the weight of `t` never grows after `N`, and drops at each of its steps
  have mono : ∀ n ≥ N, weight ((r.state (n + 1)).phase t) ≤ weight ((r.state n).phase t) ∧
      (LTS.liftTask (stepTask t) (r.label n) →
        weight ((r.state (n + 1)).phase t) < weight ((r.state n).phase t)) := by
    intro n le
    rcases idle_or_step r n with ⟨isIdle, same⟩ | ⟨step, isLabel, allowed, next⟩
    · rw [same, isIdle]
      exact ⟨le_rfl, fun h => h.elim⟩
    · rw [isLabel]
      by_cases mine : step.actor = t
      · have notCommit : ¬ step.IsCommit := by
          intro isCommit
          cases step with
          | commit u =>
              have same : u = t := mine
              subst same
              obtain ⟨⟨c, isActive⟩, _⟩ := allowed
              apply never (n + 1)
              rw [next]
              simp [oNext, isActive, oneShot, Finished]
          | _ => exact isCommit
        have := weight_next_lt (mode := mode) allowed notCommit mine
        rw [next]
        exact ⟨by omega, fun _ => by omega⟩
      · refine ⟨?_, fun fires => absurd fires mine⟩
        rcases phase_next_of_ne (mode := mode) allowed mine with same | ⟨u, c, d, _, _, before, after, _⟩
        · rw [next, same]
        · exact absurd (by rw [next]; exact after) (notInvalidated n le c before)
  exact not_infinitelyOften_of_descent (fun n => weight ((r.state n).phase t)) N
    (fun n le => (mono n le).1) (fun n le => (mono n le).2) often

end Elder

/-! ## Instances -/

section Instances

variable {label : O → R} {mode : Finset Check} {prog : Program T O R}
  {refuse : OState T O R → T → Prop}

/-- Ages are below the step counter and distinct. -/
def AgeInv (σ : OState T O R) : Prop :=
  (∀ g b, σ.age g = some b → b < σ.clock) ∧ ∀ g h b, σ.age g = some b → σ.age h = some b → g = h

theorem ageInv_next {σ : OState T O R} (inv : AgeInv σ) {a : OLabel T O R}
    (allowed : oAllowed label prog refuse σ a) :
    AgeInv (oNext label mode prog σ a) ∧ (oNext label mode prog σ a).clock = σ.clock + 1 := by
  obtain ⟨below, distinct⟩ := inv
  cases a with
  | begin u c =>
      refine ⟨⟨fun g b h => ?_, fun g h b hg hh => ?_⟩, rfl⟩
      · simp only [oNext] at h ⊢
        split_ifs at h with fresh
        · by_cases same : g = u
          · subst same; simp at h; omega
          · rw [Function.update_of_ne same] at h; have := below g b h; omega
        · have := below g b h; omega
      · simp only [oNext] at hg hh
        split_ifs at hg hh with fresh
        · by_cases sg : g = u <;> by_cases sh : h = u
          · rw [sg, sh]
          · subst sg; simp at hg; rw [Function.update_of_ne sh] at hh
            have := below h b hh; omega
          · subst sh; simp at hh; rw [Function.update_of_ne sg] at hg
            have := below g b hg; omega
          · rw [Function.update_of_ne sg] at hg; rw [Function.update_of_ne sh] at hh
            exact distinct g h b hg hh
        · exact distinct g h b hg hh
  | commit u =>
      obtain ⟨⟨c, isActive⟩, _⟩ := allowed
      refine ⟨⟨fun g b h => ?_, fun g h b hg hh => ?_⟩, by simp [oNext, isActive]⟩
      · simp only [oNext, isActive] at h ⊢
        split_ifs at h with persistent
        · by_cases same : g = u
          · subst same; simp at h
          · rw [Function.update_of_ne same] at h; have := below g b h; omega
        · have := below g b h; omega
      · simp only [oNext, isActive] at hg hh
        split_ifs at hg hh with persistent
        · by_cases sg : g = u
          · subst sg; simp at hg
          · by_cases sh : h = u
            · subst sh; simp at hh
            · rw [Function.update_of_ne sg] at hg; rw [Function.update_of_ne sh] at hh
              exact distinct g h b hg hh
        · exact distinct g h b hg hh
  | abort u =>
      exact ⟨⟨fun g b h => by have := below g b h; simp only [oNext]; omega, distinct⟩, rfl⟩
  | fail u =>
      exact ⟨⟨fun g b h => by have := below g b h; simp only [oNext]; omega, distinct⟩, rfl⟩

/-- A step by another transaction leaves an age alone. -/
theorem age_next_of_ne {σ : OState T O R} {a : OLabel T O R} (allowed : oAllowed label prog refuse σ a)
    {g : T} (other : a.actor ≠ g) : (oNext label mode prog σ a).age g = σ.age g := by
  have ne : g ≠ a.actor := fun h => other h.symm
  cases a with
  | begin u c =>
      simp only [oNext]
      split_ifs
      · exact Function.update_of_ne ne _ _
      · rfl
  | commit u =>
      obtain ⟨⟨c, isActive⟩, _⟩ := allowed
      simp only [oNext, isActive]
      split_ifs
      · exact Function.update_of_ne ne _ _
      · rfl
  | abort u => rfl
  | fail u => rfl

/-- A one-shot transaction's age, once set, never changes. -/
theorem age_next_of_some {σ : OState T O R} {a : OLabel T O R} (allowed : oAllowed label prog refuse σ a)
    {t : T} (oneShot : prog.persistent t = false) {b : ℕ} (aged : σ.age t = some b) :
    (oNext label mode prog σ a).age t = some b := by
  by_cases mine : a.actor = t
  · cases a with
    | begin u c =>
        have same : u = t := mine
        subst same
        simp [oNext, aged]
    | commit u =>
        have same : u = t := mine
        subst same
        obtain ⟨⟨c, isActive⟩, _⟩ := allowed
        simp [oNext, isActive, oneShot, aged]
    | abort u => exact aged
    | fail u => exact aged
  · rw [age_next_of_ne allowed mine, aged]

/-- **Aging decides every one-shot transaction**: with the key "time of the first proposal of the
current firing", kept across re-matching, every one-shot transaction of a run from an initial state
commits or fails, under weak fairness of every transaction's steps. -/
theorem aging_decides [Fintype T]
    (r : Run (optimistic label mode prog (elderRefusal label mode agingKey)).withIdle)
    (initial : OInitial (r.state 0)) (unaged : ∀ g, (r.state 0).age g = none)
    (fair : ∀ x, r.WeaklyFair (LTS.liftTask (stepTask x))) {t : T}
    (oneShot : prog.persistent t = false) : ∃ n, Finished ((r.state n).phase t) := by
  by_contra never
  push Not at never
  -- invariants: ages below the counter and distinct; the counter never goes back
  have ageInv : ∀ n, AgeInv (r.state n) ∧ ∀ m ≥ n, (r.state n).clock ≤ (r.state m).clock := by
    have inv : ∀ n, AgeInv (r.state n) := by
      intro n
      induction n with
      | zero =>
          refine ⟨fun g b h => ?_, fun g _ b h _ => ?_⟩
          · rw [unaged g] at h; cases h
          · rw [unaged g] at h; cases h
      | succ n ih =>
          rcases idle_or_step r n with ⟨_, same⟩ | ⟨a, _, allowed, next⟩
          · rw [same]; exact ih
          · rw [next]; exact (ageInv_next (mode := mode) ih allowed).1
    have clockStep : ∀ n, (r.state n).clock ≤ (r.state (n + 1)).clock := by
      intro n
      rcases idle_or_step r n with ⟨_, same⟩ | ⟨a, _, allowed, next⟩
      · rw [same]
      · rw [next, (ageInv_next (mode := mode) (inv n) allowed).2]; omega
    refine fun n => ⟨inv n, fun m le => ?_⟩
    induction m, le using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact ih.trans (clockStep m)
  -- the first step of `t` is a proposal
  have idleUntil : ∀ n, (∀ m < n, ¬ LTS.liftTask (stepTask t) (r.label m)) →
      (r.state n).phase t = .idle := by
    intro n
    induction n with
    | zero => exact fun _ => initial.2 t
    | succ n ih =>
        intro notYet
        have idleN := ih fun m lt => notYet m (by omega)
        rcases idle_or_step r n with ⟨_, same⟩ | ⟨a, isLabel, allowed, next⟩
        · rw [same]; exact idleN
        · have notMine : a.actor ≠ t := fun mine => notYet n (Nat.lt_succ_self n) (by
            rw [isLabel]; exact mine)
          rcases phase_next_of_ne (mode := mode) allowed notMine with same | ⟨_, _, _, _, _, active, _⟩
          · rw [next, same]; exact idleN
          · rw [idleN] at active; cases active
  obtain ⟨n, -, fires⟩ := (fair t).fires 0 fun n _ notYet => by
    obtain ⟨a, actor, allowed⟩ := idle_can_step (refuse := elderRefusal label mode agingKey)
      (idleUntil n fun m lt => notYet m (Nat.zero_le m) lt) oneShot
    rw [← actor]
    exact stepTask_enabled_of_allowed allowed
  -- take the first step of `t`
  classical
  have ex : ∃ m, LTS.liftTask (stepTask t) (r.label m) := ⟨n, fires⟩
  let first := Nat.find ex
  have firstFires : LTS.liftTask (stepTask t) (r.label first) := Nat.find_spec ex
  have idleFirst := idleUntil first fun m lt => Nat.find_min ex lt
  rcases idle_or_step r first with ⟨isIdle, _⟩ | ⟨a, isLabel, allowed, next⟩
  · rw [isIdle] at firstFires; exact firstFires
  · rw [isLabel] at firstFires
    have actor : a.actor = t := firstFires
    cases a with
    | commit u =>
        have same : u = t := actor; subst same
        obtain ⟨⟨c, isActive⟩, _⟩ := allowed
        rw [idleFirst] at isActive; cases isActive
    | abort u =>
        have same : u = t := actor; subst same
        obtain ⟨c, isActive⟩ := allowed
        rw [idleFirst] at isActive; cases isActive
    | fail u =>
        have same : u = t := actor; subst same
        apply never (first + 1)
        rw [next]
        simp [oNext, Finished]
    | begin u c =>
        have same : u = t := actor; subst same
        -- the age of `u` from `first + 1` on
        obtain ⟨b, aged⟩ : ∃ b, (r.state (first + 1)).age u = some b := by
          rw [next]
          simp only [oNext]
          split_ifs with fresh
          · exact ⟨_, Function.update_self _ _ _⟩
          · exact Option.ne_none_iff_exists'.mp fresh
        have keyed : ∀ m ≥ first + 1, (r.state m).age u = some b := by
          intro m le
          induction m, le using Nat.le_induction with
          | base => exact aged
          | succ m _ ih =>
              rcases idle_or_step r m with ⟨_, same⟩ | ⟨a', _, allowed', next'⟩
              · rw [same]; exact ih
              · rw [next']; exact age_next_of_some allowed' oneShot ih
        have bBelow : b < (r.state (first + 1)).clock := (ageInv (first + 1)).1.1 u b aged
        refine absurd (decided_of_elder_rule (key := agingKey) (t := u) (n₀ := first + 1) (a := b)
          ⟨keyed, ?_, ?_, ?_, ?_⟩ fair oneShot) (fun ⟨m, done⟩ => never m done)
        · -- keyStable
          intro m _ g notMine
          rcases idle_or_step r m with ⟨_, same⟩ | ⟨a', isLabel', allowed', next'⟩
          · simp only [agingKey]; rw [same]
          · simp only [agingKey]; rw [next']
            exact age_next_of_ne allowed' (notMine a' isLabel')
        · -- no new elders
          intro m le g b' newKey below
          simp only [agingKey] at newKey ⊢
          rcases idle_or_step r m with ⟨_, same⟩ | ⟨a', isLabel', allowed', next'⟩
          · rw [same] at newKey; exact newKey
          · rw [next'] at newKey
            by_cases mine : a'.actor = g
            · cases a' with
              | begin g' c' =>
                  have same : g' = g := mine; subst same
                  simp only [oNext] at newKey
                  split_ifs at newKey with unagedG
                  · simp only [Function.update_self, Option.some.injEq] at newKey
                    have := (ageInv (first + 1)).2 m le
                    omega
                  · exact newKey
              | commit g' =>
                  have same : g' = g := mine; subst same
                  obtain ⟨⟨c', isActive⟩, _⟩ := allowed'
                  simp only [oNext, isActive] at newKey
                  split_ifs at newKey
                  · simp at newKey
                  · exact newKey
              | abort g' => exact newKey
              | fail g' => exact newKey
            · rw [age_next_of_ne allowed' mine] at newKey; exact newKey
        · -- elder commits retire
          intro m _ g b' isCommit keyG below
          have allowed' := r.allowed m
          rw [isCommit] at allowed'
          obtain ⟨⟨c', isActive⟩, _⟩ := allowed'
          rcases idle_or_step r m with ⟨isIdle, _⟩ | ⟨a', isLabel', _, next'⟩
          · rw [isIdle] at isCommit; cases isCommit
          · rw [isCommit] at isLabel'
            cases isLabel'
            cases persistent : prog.persistent g
            · right; rw [next']; simp [oNext, isActive, persistent, Finished]
            · left; simp only [agingKey]; rw [next']; simp [oNext, isActive, persistent]
        · -- distinct
          intro m _ g keyG
          exact (ageInv m).1.2 g u b keyG (keyed m (by omega))

/-- **A fixed order decides every transaction**: with keys fixed in advance and distinct, and every
transaction one-shot, every transaction commits or fails under weak fairness of every
transaction's steps. -/
theorem sequenced_decides [Fintype T] (seq : T → ℕ) (injective : Function.Injective seq)
    (allOneShot : ∀ g, prog.persistent g = false)
    (r : Run (optimistic label mode prog (elderRefusal label mode (sequenceKey seq))).withIdle)
    (fair : ∀ x, r.WeaklyFair (LTS.liftTask (stepTask x))) (t : T) :
    ∃ n, Finished ((r.state n).phase t) := by
  refine decided_of_elder_rule (key := sequenceKey seq) (n₀ := 0) (a := seq t)
    ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ g b newKey _ => newKey, ?_, ?_⟩ fair (allOneShot t)
  · intro m _ g b isCommit _ _
    right
    have allowed := r.allowed m
    rw [isCommit] at allowed
    obtain ⟨⟨c, isActive⟩, _⟩ := allowed
    rcases idle_or_step r m with ⟨isIdle, _⟩ | ⟨a, isLabel, _, next⟩
    · rw [isIdle] at isCommit; cases isCommit
    · rw [isCommit] at isLabel
      cases isLabel
      rw [next]
      simp [oNext, isActive, allOneShot g, Finished]
  · intro m _ g same
    exact injective (Option.some.inj same)

end Instances

/-! ## Control: priority by process, not by firing -/

namespace Controls

/-- Priority by process: the renewer (`false`) always ranks before the victim (`true`). -/
def staticKey : OState Bool ℕ Unit → Bool → Option ℕ := fun _ g => some (if g then 1 else 0)

variable {mode : Finset Check}

/-- The starving schedule is a run under priority by process. -/
def staticRun (takes : Check.takes ∈ mode) :
    Run (optimistic unitLabel mode starveProg (elderRefusal unitLabel mode staticKey)) where
  state := starveState mode
  label := starveLabel
  allowed n := by
    have allowed := starve_allowed takes n
    obtain ⟨k, j, lt, rfl⟩ : ∃ k j, j < 4 ∧ n = 4 * k + j :=
      ⟨n / 4, n % 4, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 4).symm⟩
    obtain ⟨l0, l1, l2, l3⟩ := starveLabel_eq k
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rw [Nat.add_zero, l0] at allowed ⊢; exact allowed
    · rw [l1] at allowed ⊢; exact allowed
    · rw [l2] at allowed ⊢
      refine ⟨allowed.1, ?_⟩
      rintro ⟨g, ne, ⟨b, keyG, older⟩, _⟩
      cases g
      · exact ne rfl
      · simp only [staticKey, if_true, Option.some.injEq] at keyG
        have := older 0 (by simp [staticKey])
        omega
    · rw [l3] at allowed ⊢; exact allowed
  step _ := rfl

/-- **Priority by process starves.** Under the elder rule with a fixed rank of processes, the
starving schedule is a run, weakly fair for the steps of both processes, in which the victim never
commits: the renewer is always the elder, because its rank survives its commits. -/
theorem staticPriority_starves (takes : Check.takes ∈ mode) :
    (∀ x, (staticRun takes).WeaklyFair (stepTask x)) ∧
      ∀ n, ¬ kindTask .commit true ((staticRun takes).label n) := by
  obtain ⟨never, _, renewerCommits, _, _, _⟩ := optimistic_starvation takes
  refine ⟨fun x => ?_, never⟩
  cases x
  · intro _ N
    obtain ⟨n, le, commits⟩ := renewerCommits N
    refine ⟨n, le, ?_⟩
    change stepTask false (starveLabel n)
    change kindTask .commit false (starveLabel n) at commits
    cases labelIs : starveLabel n with
    | commit u =>
        rw [labelIs] at commits
        exact commits.2
    | begin u c => rw [labelIs] at commits; exact absurd commits.1 (by decide)
    | abort u => rw [labelIs] at commits; exact absurd commits.1 (by decide)
    | fail u => rw [labelIs] at commits; exact absurd commits.1 (by decide)
  · rintro ⟨N, always⟩
    exfalso
    obtain ⟨_, ⟨_, _, true₂, false₂⟩, _, _⟩ := starve_period takes N (starve_start takes N)
    obtain ⟨a, mine, allowed⟩ := always (4 * N + 2) (by omega)
    change oAllowed unitLabel starveProg (elderRefusal unitLabel mode staticKey)
      (starveState mode (4 * N + 2)) a at allowed
    cases a with
    | begin u c =>
        have same : u = true := mine
        subst same
        have := allowed.1
        rw [true₂] at this
        cases this
    | commit u =>
        have same : u = true := mine
        subst same
        apply allowed.2
        refine ⟨false, by decide, ⟨0, rfl, fun b' keyT => ?_⟩, bump N, takeTok N, false₂, true₂,
          Or.inl ⟨takes, by simp [bump, takeTok]⟩⟩
        simp only [staticKey, if_true, Option.some.injEq] at keyT
        omega
    | abort u =>
        have same : u = true := mine
        subst same
        obtain ⟨c, isActive⟩ := allowed
        rw [true₂] at isActive
        simp at isActive
    | fail u =>
        have same : u = true := mine
        subst same
        have := allowed.1
        rw [true₂] at this
        cases this

/-- **Finished, positive**: a committed transaction is finished. -/
theorem committed_finished : Finished (.committed : Phase ℕ Unit) := trivial

/-- **Finished, negative**: an idle transaction is not. -/
theorem idle_not_finished : ¬ Finished (.idle : Phase ℕ Unit) := id

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
