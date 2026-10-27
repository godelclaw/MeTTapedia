import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitProtocol

/-!
# The claim protocol: re-matching after an abort, deadlock-freedom, and blocking

`CommitProtocol` fixes one commit per transaction (`txn t`), matched when the transaction begins;
after an abort nothing re-matches. This module adds the re-matching layer at the level of that
protocol, proves what its canonical claim order buys for progress, and shows what claims cost.

## Re-matching (`AttemptStep`, `AttemptRun`)

An **attempt** is a transaction, an attempt number and the commit it matched. The re-matching layer
runs the protocol of `CommitProtocol` over attempts: a transaction begins an attempt with any of its
rows enabled at the current store; an abort or a commit moves it to its next attempt number, so an
aborted transaction **proposes again from the new store** (`abort_then_rematch`).

* **Refinement is inherited** (`AttemptRun.refines`): every run of the layer is a run of the protocol of
  `CommitProtocol` over attempts (`AttemptStep.core`), so its commits are an executable sequence of the
  atomic semantics (`CommitProtocol.Run.refines`).
* **Re-matching rescues the loser of a claim race** (`Controls.rematch_rescues_loser`): two
  transactions race for one token; the winner takes it and makes a new token; the loser aborts,
  re-matches with the new token and commits. With one fixed commit per transaction the loser commits
  in no continuation (`CommitProtocol.Controls.lost_claim_aborts`).

## Progress (`progress_available`)

A transaction that "can commit" is one that is `CommitProtocol.Ready`, and its commit is a step
(`CommitProtocol.Ready.step`).

**Canonical claim order makes the protocol deadlock-free.** In every well-formed state with an
active transaction, some active transaction can claim, or can commit, or fails a commit guard other
than its claims (so aborting it gives up nothing that could commit). The proof picks, among active
transactions that still need a claim, the one whose next needed occurrence is largest: if that
occurrence is free it can be claimed, and if it is held, the holder needs a larger occurrence
(`CommitProtocol.waitsFor_increases`) or none, and then it can commit.

* Control (`Controls.any_order_deadlock`): without canonical order, two transactions that take the
  same two occurrences each hold one and wait for the other; no claim and no commit is possible,
  both pass every other guard, and the state is not well formed (it is unreachable with canonical
  order).

## Claims block (`Run.claim_blocks`)

While a transaction that holds a claim has not finished, no commit of any run takes the claimed
occurrence. So the claim protocol is **not obstruction-free**: a stalled holder blocks every
transaction that needs its claim, even one running alone (`Controls.stalled_holder_blocks`). This is
why crash-tolerant takes bound claims by leases (`Coordination.FencedLeases`), and why the attempt
model of `OptimisticRetries`, which validates at commit time and holds nothing across steps, is
obstruction-free.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O : Type u} [LinearOrder O] {R : Type v}

/-! ## Progress in the claim protocol -/

section Progress

variable {T : Type w} [DecidableEq T] {label : O → R} {txn : T → Commit O R}

/-- The guards of a commit other than its claims: its takes and keeps live, its predicate queries
at the epochs it saw, its fresh identities unborn. -/
def OtherGuards (txn : T → Commit O R) (σ : ProtocolState O R T) (t : T)
    (seen : (R → Bool) → ℕ) : Prop :=
  (txn t).taken ⊆ σ.store ∧ (txn t).kept ⊆ σ.store ∧
    (∀ read ∈ (txn t).queries, σ.epoch read.region = seen read.region) ∧ Disjoint (txn t).made σ.born

/-- A transaction can claim an occurrence now. -/
def CanClaim (txn : T → Commit O R) (σ : ProtocolState O R T) (t : T) : Prop :=
  ∃ seen o, σ.phase t = .active seen ∧ o ∈ (txn t).taken ∧ o ∈ σ.store ∧ σ.claim o = none ∧
    ∀ o' ∈ (txn t).taken, o' < o → σ.claim o' = some t

omit [DecidableEq T] in
/-- A claim that `CanClaim` allows is a step of the protocol. -/
theorem CanClaim.step [DecidableEq T] {σ : ProtocolState O R T} {t : T} (can : CanClaim txn σ t) :
    ∃ σ', Step label txn σ none σ' := by
  obtain ⟨seen, o, active, taken, live, free, canonical⟩ := can
  exact ⟨_, .claim σ t seen o active taken live free canonical⟩

omit [DecidableEq T] in
/-- An active transaction that needs no further claim has all its takes claimed. -/
theorem all_claimed_of_no_next {σ : ProtocolState O R T} {t : T}
    (none : ∀ o, ¬ NextNeeded (txn := txn) σ t o) : ∀ o ∈ (txn t).taken, σ.claim o = some t := by
  classical
  by_contra notAll
  push Not at notAll
  let missing := (txn t).taken.filter fun o => σ.claim o ≠ some t
  have nonempty : missing.Nonempty := by
    obtain ⟨o, taken, notT⟩ := notAll
    exact ⟨o, Finset.mem_filter.2 ⟨taken, notT⟩⟩
  have least := Finset.min'_mem missing nonempty
  apply none (missing.min' nonempty)
  refine ⟨(Finset.mem_filter.1 least).1, (Finset.mem_filter.1 least).2, fun o' taken lt => ?_⟩
  by_contra notT
  have : o' ∈ missing := Finset.mem_filter.2 ⟨taken, notT⟩
  exact absurd (Finset.min'_le missing o' this) (not_le.2 lt)

/-- **Deadlock-freedom from canonical order.** In a well-formed state with an active transaction,
some active transaction fails a commit guard other than its claims, or can claim, or can commit.
`A` is any finite set containing every active transaction. -/
theorem progress_available {σ : ProtocolState O R T} (wf : WellFormed label txn σ) (A : Finset T)
    (covers : ∀ t seen, σ.phase t = .active seen → t ∈ A) {t₀ : T} {seen₀ : (R → Bool) → ℕ}
    (active₀ : σ.phase t₀ = .active seen₀) :
    ∃ t seen, σ.phase t = .active seen ∧
      (¬ OtherGuards txn σ t seen ∨ CanClaim txn σ t ∨ Ready (txn := txn) σ t) := by
  classical
  by_contra stuck
  push Not at stuck
  -- every active transaction passes its other guards and can neither claim nor commit
  have guards : ∀ t seen, σ.phase t = .active seen → OtherGuards txn σ t seen :=
    fun t seen active => (stuck t seen active).1
  -- every active transaction needs a further claim
  have needs : ∀ t seen, σ.phase t = .active seen → ∃ o, NextNeeded (txn := txn) σ t o := by
    intro t seen active
    by_contra none
    push Not at none
    obtain ⟨_, keptLive, epochsFresh, unborn⟩ := guards t seen active
    exact (stuck t seen active).2.2 ⟨seen, active, all_claimed_of_no_next none, keptLive, epochsFresh,
      unborn⟩
  let P := A.filter fun t => ∃ seen, σ.phase t = .active seen
  have inP : t₀ ∈ P := Finset.mem_filter.2 ⟨covers t₀ seen₀ active₀, seen₀, active₀⟩
  have chosen : ∀ t ∈ P, ∃ o, NextNeeded (txn := txn) σ t o := fun t member => by
    obtain ⟨seen, active⟩ := (Finset.mem_filter.1 member).2
    exact needs t seen active
  let next : T → O := fun t => if h : t ∈ P then Classical.choose (chosen t h) else
    Classical.choose (chosen t₀ inP)
  have nextSpec : ∀ t (h : t ∈ P), NextNeeded (txn := txn) σ t (next t) := by
    intro t h
    simp only [next, dif_pos h]
    exact Classical.choose_spec (chosen t h)
  obtain ⟨t, member, largest⟩ := Finset.exists_max_image P next ⟨t₀, inP⟩
  obtain ⟨seen, active⟩ := (Finset.mem_filter.1 member).2
  have need := nextSpec t member
  cases holder : σ.claim (next t) with
  | none =>
      exact (stuck t seen active).2.1 ⟨seen, next t, active, need.1,
        (guards t seen active).1 need.1, holder, need.2.2⟩
  | some t' =>
      obtain ⟨_, _, seen', active'⟩ := wf.claim_live (next t) t' holder
      have member' : t' ∈ P := Finset.mem_filter.2 ⟨covers t' seen' active', seen', active'⟩
      have increases := waitsFor_increases wf ⟨next t, need, holder⟩ need (nextSpec t' member')
      exact absurd (largest t' member') (not_le.2 increases)

end Progress

/-! ## Claims block -/

section Blocking

variable {T : Type w} [DecidableEq T] {label : O → R} {txn : T → Commit O R}

/-- One step keeps a claim held by an unfinished transaction, or finishes that transaction; and a
commit of the step that takes the claimed occurrence is by the holder. -/
theorem step_claim_or_done {σ σ' : ProtocolState O R T} {out : Option (T × Commit O R)}
    (step : Step label txn σ out σ') {o : O} {t : T}
    (before : σ.claim o = some t ∨ σ.phase t = .done) :
    (σ'.claim o = some t ∨ σ'.phase t = .done) ∧
      ∀ entry ∈ out.toList, σ.claim o = some t → o ∈ entry.2.taken → entry.1 = t := by
  cases step with
  | begin t' idle enabled =>
      refine ⟨?_, by simp⟩
      rcases before with held | done
      · exact Or.inl held
      · right
        by_cases same : t = t'
        · subst same; rw [idle] at done; cases done
        · simp [Function.update_of_ne same, done]
  | claim t' seen o' active taken live free canonical =>
      refine ⟨?_, by simp⟩
      rcases before with held | done
      · left
        by_cases same : o = o'
        · subst same; rw [held] at free; cases free
        · simp [Function.update_of_ne same, held]
      · exact Or.inr done
  | commit t' seen active claimed keptLive epochsFresh unborn =>
      refine ⟨?_, ?_⟩
      · rcases before with held | done
        · by_cases taken : o ∈ (txn t').taken
          · have := claimed o taken
            rw [held] at this
            cases this
            right
            simp [commitState]
          · left
            simp [commitState, taken, held]
        · right
          by_cases same : t = t'
          · subst same; rw [active] at done; cases done
          · simp [commitState, Function.update_of_ne same, done]
      · intro entry member held taken
        simp only [Option.toList_some, List.mem_singleton] at member
        subst member
        have := claimed o taken
        rw [held] at this
        exact (Option.some.inj this).symm
  | abort t' seen active =>
      refine ⟨?_, by simp⟩
      rcases before with held | done
      · by_cases same : t = t'
        · subst same
          right
          simp [abortState]
        · left
          simp [abortState, held, same]
      · right
        by_cases same : t = t'
        · subst same; rw [active] at done; cases done
        · simp [abortState, Function.update_of_ne same, done]

/-- **Claims block.** Along every run from a well-formed state, while the holder of a claim has not
finished, no commit takes the claimed occurrence; and if the holder has not finished at the end, no
commit of the run took it. -/
theorem claim_blocks {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') (wf : WellFormed label txn σ) {o : O} {t : T}
    (held : σ.claim o = some t) (unfinished : σ'.phase t ≠ .done) :
    σ'.claim o = some t ∧ ∀ entry ∈ trace, o ∉ entry.2.taken := by
  -- a done transaction stays done
  have staysDone : ∀ {ρ ρ' : ProtocolState O R T} {tr : List (T × Commit O R)},
      Run label txn ρ tr ρ' → ρ.phase t = .done → ρ'.phase t = .done := by
    intro ρ ρ' tr run' done
    induction run' with
    | refl => exact done
    | @step ρ₁ ρ₂ ρ₃ out tr first rest ih =>
        apply ih
        cases first with
        | begin t' idle _ =>
            by_cases same : t = t'
            · subst same; rw [idle] at done; cases done
            · simp [Function.update_of_ne same, done]
        | claim => exact done
        | commit t' _ active _ _ _ _ =>
            by_cases same : t = t'
            · subst same; rw [active] at done; cases done
            · simp [commitState, Function.update_of_ne same, done]
        | abort t' _ active =>
            by_cases same : t = t'
            · subst same; rw [active] at done; cases done
            · simp [abortState, Function.update_of_ne same, done]
  induction run with
  | refl => exact ⟨held, by simp⟩
  | @step ρ₁ ρ₂ ρ₃ out tr first rest ih =>
      obtain ⟨after, byHolder⟩ := step_claim_or_done first (Or.inl held)
      have wf₂ := first.wellFormed wf
      rcases after with held₂ | done₂
      · obtain ⟨final, untaken⟩ := ih wf₂ held₂ unfinished
        refine ⟨final, fun entry member => ?_⟩
        rcases List.mem_append.mp member with inOut | inRest
        · intro taken
          have isHolder := byHolder entry inOut held taken
          -- the holder committed here, so it is done afterwards and at the end
          cases out with
          | none => simp at inOut
          | some pair =>
              simp only [Option.toList_some, List.mem_singleton] at inOut
              subst inOut
              cases first with
              | commit t' _ _ _ _ _ _ =>
                  have same : t' = t := isHolder
                  subst same
                  exact unfinished (staysDone rest (by simp [commitState]))
        · exact untaken entry inRest
      · exact absurd (staysDone rest done₂) unfinished

end Blocking

/-! ## Re-matching after an abort -/

section Rematching

variable {T : Type w} [DecidableEq T]

/-- An attempt: a transaction, its attempt number, and the commit it matched. -/
abbrev Attempt (T : Type w) (O : Type u) (R : Type v) := T × ℕ × Commit O R

/-- The commit of an attempt. -/
def attemptCommit : Attempt T O R → Commit O R := fun a => a.2.2

/-- Commits are compared classically: attempts are identified by their commit, not computed with. -/
noncomputable abbrev commitDecEq : DecidableEq (Commit O R) := Classical.decEq _

attribute [local instance] commitDecEq

/-- The state of the re-matching layer: the protocol state over attempts, each transaction's
current attempt number, and which transactions are finished. -/
structure AttemptState (T : Type w) (O : Type u) (R : Type v) where
  core : ProtocolState O R (Attempt T O R)
  attempt : T → ℕ
  finished : T → Bool

variable (label : O → R) (rows : T → Set (Commit O R)) (persistent : T → Bool)

/-- A step of the re-matching layer: the protocol's step on the current attempt of a transaction.
A transaction begins with any row enabled at the current store; a commit or an abort moves it to
its next attempt. -/
inductive AttemptStep : AttemptState T O R → Option (T × Commit O R) → AttemptState T O R → Prop
  | begin (ρ : AttemptState T O R) (t : T) (c : Commit O R) (unfinished : ρ.finished t = false)
      (row : c ∈ rows t) (single : ∀ c' seen, ρ.core.phase (t, ρ.attempt t, c') ≠ .active seen)
      (idle : ρ.core.phase (t, ρ.attempt t, c) = .idle) (enabled : Enabled label ρ.core.store c) :
      AttemptStep ρ none ⟨{ ρ.core with
        phase := Function.update ρ.core.phase (t, ρ.attempt t, c) (.active ρ.core.epoch) },
        ρ.attempt, ρ.finished⟩
  | claim (ρ : AttemptState T O R) (t : T) (c : Commit O R) (seen : (R → Bool) → ℕ) (o : O)
      (active : ρ.core.phase (t, ρ.attempt t, c) = .active seen) (taken : o ∈ c.taken)
      (live : o ∈ ρ.core.store) (free : ρ.core.claim o = none)
      (canonical : ∀ o' ∈ c.taken, o' < o → ρ.core.claim o' = some (t, ρ.attempt t, c)) :
      AttemptStep ρ none ⟨{ ρ.core with
        claim := Function.update ρ.core.claim o (some (t, ρ.attempt t, c)) }, ρ.attempt, ρ.finished⟩
  | commit (ρ : AttemptState T O R) (t : T) (c : Commit O R) (seen : (R → Bool) → ℕ)
      (active : ρ.core.phase (t, ρ.attempt t, c) = .active seen)
      (claimed : ∀ o ∈ c.taken, ρ.core.claim o = some (t, ρ.attempt t, c))
      (keptLive : c.kept ⊆ ρ.core.store)
      (epochsFresh : ∀ read ∈ c.queries, ρ.core.epoch read.region = seen read.region)
      (unborn : Disjoint c.made ρ.core.born) :
      AttemptStep ρ (some (t, c)) ⟨commitState label attemptCommit (t, ρ.attempt t, c) ρ.core,
        Function.update ρ.attempt t (ρ.attempt t + 1),
        if persistent t then ρ.finished else Function.update ρ.finished t true⟩
  | abort (ρ : AttemptState T O R) (t : T) (c : Commit O R) (seen : (R → Bool) → ℕ)
      (active : ρ.core.phase (t, ρ.attempt t, c) = .active seen) :
      AttemptStep ρ none ⟨abortState (t, ρ.attempt t, c) ρ.core,
        Function.update ρ.attempt t (ρ.attempt t + 1), ρ.finished⟩

/-- A run of the re-matching layer, with its commits in order. -/
inductive AttemptRun : AttemptState T O R → List (T × Commit O R) → AttemptState T O R → Prop
  | refl (ρ : AttemptState T O R) : AttemptRun ρ [] ρ
  | step {ρ ρ' ρ'' : AttemptState T O R} {out : Option (T × Commit O R)} {trace : List (T × Commit O R)}
      (first : AttemptStep label rows persistent ρ out ρ') (rest : AttemptRun ρ' trace ρ'') :
      AttemptRun ρ (out.toList ++ trace) ρ''

variable {label rows persistent}

/-- **Each step of the layer is a step of the protocol over attempts.** -/
theorem AttemptStep.core {ρ ρ' : AttemptState T O R} {out : Option (T × Commit O R)}
    (step : AttemptStep label rows persistent ρ out ρ') :
    Step label attemptCommit ρ.core (out.map fun p => ((p.1, ρ.attempt p.1, p.2), p.2)) ρ'.core := by
  cases step with
  | begin t c _ _ _ idle enabled => exact .begin ρ.core (t, ρ.attempt t, c) idle enabled
  | claim t c seen o active taken live free canonical =>
      exact .claim ρ.core (t, ρ.attempt t, c) seen o active taken live free canonical
  | commit t c seen active claimed keptLive epochsFresh unborn =>
      exact .commit ρ.core (t, ρ.attempt t, c) seen active claimed keptLive epochsFresh unborn
  | abort t c seen active => exact .abort ρ.core (t, ρ.attempt t, c) seen active

/-- Every run of the layer is a run of the protocol over attempts, with the same commits. -/
theorem AttemptRun.core {ρ ρ' : AttemptState T O R} {trace : List (T × Commit O R)}
    (run : AttemptRun label rows persistent ρ trace ρ') :
    ∃ trace', Run label attemptCommit ρ.core trace' ρ'.core ∧
      trace'.map Prod.snd = trace.map Prod.snd := by
  induction run with
  | refl ρ => exact ⟨[], .refl _, rfl⟩
  | @step ρ ρ' ρ'' out trace first rest ih =>
      obtain ⟨trace', run', same⟩ := ih
      refine ⟨(out.map fun p => ((p.1, ρ.attempt p.1, p.2), p.2)).toList ++ trace',
        .step first.core run', ?_⟩
      cases out <;> simp [same]

/-- **Refinement, inherited.** The commits of every run of the layer from a well-formed state are an
executable sequence of the atomic semantics, ending at the layer's store. -/
theorem AttemptRun.refines {ρ ρ' : AttemptState T O R} {trace : List (T × Commit O R)}
    (run : AttemptRun label rows persistent ρ trace ρ') (wf : WellFormed label attemptCommit ρ.core) :
    Executable label ρ.core.store (trace.map Prod.snd) ∧
      ρ'.core.store = fireList ρ.core.store (trace.map Prod.snd) := by
  obtain ⟨trace', run', same⟩ := run.core
  obtain ⟨executable, finish, _⟩ := run'.refines wf
  rw [same] at executable finish
  exact ⟨executable, finish⟩

/-- The layer's invariant: attempts beyond the current one are idle, and the current one is not
done. -/
def AttemptInv (ρ : AttemptState T O R) : Prop :=
  ∀ t j c, (ρ.attempt t < j → ρ.core.phase (t, j, c) = .idle) ∧
    (j = ρ.attempt t → ρ.core.phase (t, j, c) ≠ .done)

omit [LinearOrder O] [DecidableEq T] in
theorem attemptInv_of_idle {ρ : AttemptState T O R} (idle : ∀ a, ρ.core.phase a = .idle) : AttemptInv ρ :=
  fun t j c => ⟨fun _ => idle _, fun _ h => by rw [idle] at h; cases h⟩

omit [LinearOrder O] in
/-- Moving a transaction to its next attempt, after its current attempt is done, keeps the
invariant. -/
theorem attemptInv_advance {ρ : AttemptState T O R} (inv : AttemptInv ρ) (t : T) (c : Commit O R)
    (core : ProtocolState O R (Attempt T O R))
    (phase : core.phase = Function.update ρ.core.phase (t, ρ.attempt t, c) .done) (finished : T → Bool) :
    AttemptInv ⟨core, Function.update ρ.attempt t (ρ.attempt t + 1), finished⟩ := by
  intro t' j c'
  by_cases same : t' = t
  · subst same
    simp only [Function.update_self]
    have ne : ∀ j', ρ.attempt t' < j' → (t', j', c') ≠ (t', ρ.attempt t', c) := by
      intro j' lt h
      simp only [Prod.mk.injEq] at h
      omega
    refine ⟨fun lt => ?_, fun eq => ?_⟩
    · rw [phase, Function.update_of_ne (ne j (by omega))]
      exact (inv t' j c').1 (by omega)
    · rw [phase, Function.update_of_ne (ne j (by omega)), (inv t' j c').1 (by omega)]
      exact fun h => by cases h
  · simp only [Function.update_of_ne same]
    have ne : (t', j, c') ≠ (t, ρ.attempt t, c) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact same h.1
    rw [phase, Function.update_of_ne ne]
    exact inv t' j c'

/-- **Every step of the layer keeps its invariant.** -/
theorem AttemptStep.attemptInv {ρ ρ' : AttemptState T O R} {out : Option (T × Commit O R)}
    (step : AttemptStep label rows persistent ρ out ρ') (inv : AttemptInv ρ) : AttemptInv ρ' := by
  cases step with
  | begin t c _ _ _ _ _ =>
      intro t' j c'
      by_cases same : (t', j, c') = (t, ρ.attempt t, c)
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        simp only [Function.update_self]
        exact ⟨fun lt => absurd lt (lt_irrefl _), fun _ h => by cases h⟩
      · simp only [Function.update_of_ne same]
        exact inv t' j c'
  | claim => exact inv
  | commit t c _ _ _ _ _ _ => exact attemptInv_advance inv t c _ rfl _
  | abort t c _ _ => exact attemptInv_advance inv t c _ rfl _

/-- **A transaction with no active attempt can begin with any row enabled at the current store.** -/
theorem rematch_available {ρ : AttemptState T O R} (inv : AttemptInv ρ) {t : T}
    (unfinished : ρ.finished t = false)
    (noActive : ∀ c' seen, ρ.core.phase (t, ρ.attempt t, c') ≠ .active seen) {c : Commit O R}
    (row : c ∈ rows t) (enabled : Enabled label ρ.core.store c) :
    ∃ ρ', AttemptStep label rows persistent ρ none ρ' := by
  have idle : ρ.core.phase (t, ρ.attempt t, c) = .idle := by
    cases phase : ρ.core.phase (t, ρ.attempt t, c) with
    | idle => rfl
    | active seen => exact absurd phase (noActive c seen)
    | done => exact absurd phase ((inv t _ c).2 rfl)
  exact ⟨_, .begin ρ t c unfinished row noActive idle enabled⟩

/-- **An aborted transaction proposes again from the new store**: after the abort of its current
attempt, it has no active attempt, and it can begin with any of its rows enabled at the store the
abort leaves. -/
theorem abort_then_rematch {ρ : AttemptState T O R} (inv : AttemptInv ρ) {t : T} {c : Commit O R}
    {seen : (R → Bool) → ℕ} (active : ρ.core.phase (t, ρ.attempt t, c) = .active seen)
    (unfinished : ρ.finished t = false) {c' : Commit O R} (row : c' ∈ rows t)
    (enabled : Enabled label ρ.core.store c') :
    ∃ ρ'', AttemptStep label rows persistent
      ⟨abortState (t, ρ.attempt t, c) ρ.core, Function.update ρ.attempt t (ρ.attempt t + 1),
        ρ.finished⟩ none ρ'' := by
  have inv' := (AttemptStep.abort (label := label) (rows := rows) (persistent := persistent) ρ t c seen
    active).attemptInv inv
  refine rematch_available inv' unfinished (fun c'' seen' h => ?_) row enabled
  have ne : (t, ρ.attempt t + 1, c'') ≠ (t, ρ.attempt t, c) := by simp
  have phaseEq : (abortState (t, ρ.attempt t, c) ρ.core).phase (t, ρ.attempt t + 1, c'') = .idle := by
    simp only [abortState]
    rw [Function.update_of_ne ne]
    exact (inv t (ρ.attempt t + 1) c'').1 (Nat.lt_succ_self _)
  simp only [Function.update_self] at h
  rw [phaseEq] at h
  cases h

end Rematching

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-! ### Without canonical order: a deadlock -/

/-- Two transactions that take occurrences `0` and `1`. -/
def pairTxn : Bool → Commit ℕ Atom
  | true => ⟨{0, 1}, ∅, {5}, []⟩
  | false => ⟨{0, 1}, ∅, {6}, []⟩

/-- A claim step without the canonical-order guard, and the begin step of the protocol. -/
inductive AnyOrderStep : ProtocolState ℕ Atom Bool → ProtocolState ℕ Atom Bool → Prop
  | begin (σ : ProtocolState ℕ Atom Bool) (t : Bool) (idle : σ.phase t = .idle)
      (enabled : Enabled label σ.store (pairTxn t)) :
      AnyOrderStep σ { σ with phase := Function.update σ.phase t (.active σ.epoch) }
  | claim (σ : ProtocolState ℕ Atom Bool) (t : Bool) (seen : (Atom → Bool) → ℕ) (o : ℕ)
      (active : σ.phase t = .active seen) (taken : o ∈ (pairTxn t).taken) (live : o ∈ σ.store)
      (free : σ.claim o = none) :
      AnyOrderStep σ { σ with claim := Function.update σ.claim o (some t) }

/-- Both idle, nothing claimed. -/
def pairStart : ProtocolState ℕ Atom Bool := ⟨{0, 1}, {0, 1}, fun _ => none, fun _ => 0, fun _ => .idle⟩

/-- `true` holds `1`, `false` holds `0`. -/
def crossed : ProtocolState ℕ Atom Bool :=
  ⟨{0, 1}, {0, 1}, Function.update (Function.update (fun _ => none) 1 (some true)) 0 (some false),
    fun _ => 0,
    Function.update (Function.update (fun _ => .idle) true (.active fun _ => 0)) false
      (.active fun _ => 0)⟩

theorem pairTxn_enabled (t : Bool) : Enabled label {0, 1} (pairTxn t) := by
  cases t <;> exact ⟨by decide, by decide, by decide, by decide, by simp [pairTxn]⟩

/-- **Without canonical order the protocol deadlocks.** Claims in any order reach the crossed
state; there both transactions pass every guard but their claims, no occurrence they need is free,
neither can commit, and the state is not well formed, so it is unreachable with canonical order. -/
theorem any_order_deadlock :
    Relation.ReflTransGen AnyOrderStep pairStart crossed ∧
      (∀ t, OtherGuards pairTxn crossed t (fun _ => 0)) ∧
      (∀ t o, o ∈ (pairTxn t).taken → crossed.claim o ≠ none) ∧
      (∀ t, ¬ Ready (txn := pairTxn) crossed t) ∧ ¬ WellFormed label pairTxn crossed := by
  refine ⟨?_, fun t => ?_, fun t o taken => ?_, fun t => ?_, fun wf => ?_⟩
  · refine .tail (.tail (.tail (.tail (.refl) (.begin _ true rfl (pairTxn_enabled true)))
      (.begin _ false rfl (pairTxn_enabled false)))
      (.claim _ true (fun _ => 0) 1 (by simp [pairStart]) (by simp [pairTxn]) (by simp [pairStart]) rfl))
      (.claim _ false (fun _ => 0) 0 (by simp [pairStart]) (by simp [pairTxn]) (by simp [pairStart])
        (by simp [pairStart]))
  · cases t <;> exact ⟨by decide, by decide, by simp [pairTxn], by decide⟩
  · cases t <;> simp only [pairTxn, Finset.mem_insert, Finset.mem_singleton] at taken <;>
      rcases taken with rfl | rfl <;> simp [crossed]
  · rintro ⟨_, _, claimed, _⟩
    cases t
    · have := claimed 1 (by simp [pairTxn]); simp [crossed] at this
    · have := claimed 0 (by simp [pairTxn]); simp [crossed] at this
  · have := wf.canonical true 1 (by simp [crossed]) 0 (by simp [pairTxn]) (by decide)
    simp [crossed] at this

/-! ### A stalled holder blocks -/

/-- Commits of a run are the transactions' commits. -/
theorem run_entries {T : Type w} [DecidableEq T] {label' : ℕ → Atom} {txn : T → Commit ℕ Atom}
    {σ σ' : ProtocolState ℕ Atom T} {trace : List (T × Commit ℕ Atom)}
    (run : Run label' txn σ trace σ') : ∀ entry ∈ trace, entry.2 = txn entry.1 := by
  induction run with
  | refl => simp
  | @step σ₁ σ₂ σ₃ out tr first rest ih =>
      intro entry member
      rcases List.mem_append.mp member with inOut | inRest
      · cases first with
        | commit t _ _ _ _ _ _ =>
            simp only [Option.toList_some, List.mem_singleton] at inOut
            subst inOut
            rfl
        | begin => simp at inOut
        | claim => simp at inOut
        | abort => simp at inOut
      · exact ih entry inRest

/-- **A stalled claim holder blocks.** The token's first claimant takes its claim and stops; in
every continuation in which it does not finish, the other claimant never commits, even running
alone. -/
theorem stalled_holder_blocks :
    ∃ σh, Run label rivals protocolStart [] σh ∧
      ∀ σ' trace, Run label rivals σh trace σ' → σ'.phase true ≠ .done →
        ∀ entry ∈ trace, entry.1 ≠ false := by
  have first : Run label rivals protocolStart [] _ :=
    .step (.begin _ true rfl taker_enabled)
      (.step (.claim _ true (fun _ => 0) 0 rfl (by simp [rivals, taker]) (by decide) rfl
          (by simp [rivals, taker])) (.refl _))
  refine ⟨_, first, fun σ' trace later unfinished entry member isFalse => ?_⟩
  obtain ⟨_, _, wf⟩ := first.refines (wellFormed_of_initial protocolStart_initial)
  obtain ⟨_, untaken⟩ := claim_blocks later wf (o := 0) (t := true) (by simp) unfinished
  have isTxn := run_entries later entry member
  rw [isFalse] at isTxn
  apply untaken entry member
  rw [isTxn]
  simp [rivals, taker₂]

/-! ### Re-matching rescues the loser of a claim race -/

/-- The winner takes token `0` and makes token `2`. -/
def winRow : Commit ℕ Atom := ⟨{0}, ∅, {2}, []⟩

/-- The loser takes token `0`. -/
def loseRow₀ : Commit ℕ Atom := ⟨{0}, ∅, {3}, []⟩

/-- The loser takes token `2`. -/
def loseRow₂ : Commit ℕ Atom := ⟨{2}, ∅, {4}, []⟩

/-- `true` is the winner, `false` the loser, which may take either token. -/
def raceRows : Bool → Set (Commit ℕ Atom)
  | true => {winRow}
  | false => {loseRow₀, loseRow₂}

/-- Token `0` live, nothing claimed, everything idle at attempt `0`. -/
def raceStart : AttemptState Bool ℕ Atom :=
  ⟨⟨{0}, {0}, fun _ => none, fun _ => 0, fun _ => .idle⟩, fun _ => 0, fun _ => false⟩

theorem enabled_single (k : ℕ) (made : Finset ℕ) (fresh : Disjoint made {k}) :
    Enabled label {k} ⟨{k}, ∅, made, []⟩ :=
  ⟨by simp, by simp, by simp, fresh, by simp⟩

/-- The epochs after the winner's commit. -/
def afterWin : (Atom → Bool) → ℕ := fun region => if Writes label winRow region then 1 else 0

/-- **Re-matching rescues the loser.** Both propose taking token `0`; the winner claims it and
commits, making token `2`; the loser aborts, re-matches with token `2` from the new store, claims
it and commits. Both commit. With one fixed commit per transaction the loser commits in no
continuation (`CommitProtocol.Controls.lost_claim_aborts`). -/
theorem rematch_rescues_loser :
    ∃ ρ trace, AttemptRun label raceRows (fun _ => false) raceStart trace ρ ∧
      trace = [(true, winRow), (false, loseRow₂)] ∧ ρ.finished true = true ∧
      ρ.finished false = true := by
  refine ⟨_, _, .step (.begin raceStart true winRow rfl rfl (fun _ _ h => by cases h) rfl
      (enabled_single 0 {2} (by decide)))
    (.step (.begin _ false loseRow₀ rfl (by simp [raceRows]) (fun c' seen h => ?single₁) ?idle₁
      (enabled_single 0 {3} (by decide)))
    (.step (.claim _ true winRow (fun _ => 0) 0 ?active₁ (by simp [winRow]) (by simp [raceStart])
      (by simp [raceStart]) (by simp [winRow]))
    (.step (.commit _ true winRow (fun _ => 0) ?active₂ ?claimed₂ (by simp [winRow])
      (by simp [winRow]) (by simp [winRow, raceStart]))
    (.step (.abort _ false loseRow₀ (fun _ => 0) ?active₃)
    (.step (.begin _ false loseRow₂ ?unfinished₄ (by simp [raceRows]) (fun c' seen h => ?single₄)
      ?idle₄ ?enabled₄)
    (.step (.claim _ false loseRow₂ afterWin 2 ?active₅ (by simp [loseRow₂]) ?live₅ ?free₅
      (by simp [loseRow₂]))
    (.step (.commit _ false loseRow₂ afterWin ?active₆ ?claimed₆ (by simp [loseRow₂])
      (by simp [loseRow₂]) ?unborn₆)
    (.refl _)))))))), rfl, ?finishedTrue, ?finishedFalse⟩
  case single₁ => simp [raceStart] at h
  case single₄ =>
    simp [raceStart, winRow, loseRow₀, commitState, abortState, attemptCommit, Function.update_apply] at h
  case enabled₄ =>
    simp only [raceStart, commitState, abortState, attemptCommit]
    exact ⟨by decide, by decide, by decide, by decide, by simp [loseRow₂]⟩
  all_goals simp [raceStart, winRow, loseRow₀, loseRow₂, commitState, abortState, attemptCommit]
  all_goals first | rfl | decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
