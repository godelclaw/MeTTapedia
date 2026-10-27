import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Chain
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# A program is a process

## The file

A file is a list of items: top-level atoms, which are makes into the program's space, and `!`
expressions, whose evaluation today performs a list of effects in order (`Item`, `fileEffects`).
The file as a process is the chain of its effects (`Chain`): a private continuation token per
step, so the token after the last effect of one `!` is the continuation of the next.

* **Every scheduler runs the file as today** (`file_runs_as_today`): every maximal run of the
  file's process is its chain, so it performs today's effects in today's order and gives today's
  answers in today's order. Under the bag observation the answers of one expression form a bag;
  the embedding keeps even their order.

## What a parallel mode may change

A parallel mode runs other processes beside the program (spawned work, other agents, services).

* **It never reorders the program's own steps** (`Chain.chain_order_cancel`).
* **Where the system is conflict-free it changes no outcome** (`parallel_agrees_with_sequential`):
  every maximal run has the store and the answer bag of the sequential schedule. The answers of
  different processes may come in another order, which the bag does not see.
* **Where a take is shared it can change the outcome** (`Controls.parallel_exposes_choice`): the
  sequential policy always serves one worker; another schedule serves the other. This is the real
  choice of `Determinacy`, not a fault of the parallel mode.

## The REPL

The REPL is an open process: the environment sends lines, and stage `i` of the chain first takes
line `i`. Whatever the arrival times, the stages run in order (`Chain.chain_order_cancel`, with
the arrivals as the other process); in a concrete REPL, a line that arrives early waits for its
continuation, and two arrival orders give the same result (`Controls.repl_arrivals_agree`).
Without the continuation token, stages fire in arrival order and the result depends on it
(`Controls.untokened_repl_depends_on_arrival`).

## Running under a budget, and resuming

A scheduler policy picks an enabled commit or reports that none is (`Policy`). Running under a
budget of `n` steps returns the commits fired and the store (`Policy.run`); the store holds the
data, the pending work and the continuation, because all three are occurrences.

* **A budget cut is invisible** (`Policy.run_add`): running `n` steps, then resuming for `m`, is
  running `n + m` steps.
* **Every budget cut is a reachable store** (`Policy.run_reaches`), so every invariant of the
  system holds there (`Policy.run_invariant`): safety holds of every finite prefix.
* **Stopping early means quiescence** (`Policy.run_terminal`).
* **Liveness needs fairness** (`Controls.spinner_starves_task`, `Controls.fair_serves_task`): a
  policy that always serves a spinner never serves an always-enabled task, in any budget; every
  weakly fair run (`Liveness.Run.WeaklyFair`) serves it.

## The reflected agenda

Continuations are occurrences at an agenda name, and acting on them is acting on occurrences.

* **Reading a continuation never runs it** (`inspect_keeps_step`): an inspection that keeps the
  token, takes nothing and makes apart identities leaves the step it guards enabled and the token
  in place. The data law
  (`Reflection.DataLaw`) says the same of stored code.
* **Taking it cancels** (`Chain.chain_order_cancel`): after a cancelling take no step of the
  program ever fires.
* **Only holders may cancel** (`cancel_needs_receive`, `no_cancel_without_authority`): a formed
  cancellation needs `receive` at the agenda name, and if no process holds or is carried that facet
  there, no run of formed, attenuating steps ever cancels (`InteractionTypes.AuthorityRun`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe uO uR uN uI uA

section File

variable {O : Type uO} [DecidableEq O] {R : Type uR} {label : O → R}

/-- An item of a file: a top-level atom, made into the program's space, or a `!` expression with
the effects its evaluation performs today, in order. -/
inductive Item (O : Type uO) (R : Type uR) where
  | atom (occurrence : O)
  | bang (effects : List (Commit O R))

/-- The effects of a file, in order. -/
def fileEffects : List (Item O R) → List (Commit O R)
  | [] => []
  | .atom o :: rest => Commit.makeOne o :: fileEffects rest
  | .bang effects :: rest => effects ++ fileEffects rest

/-- **Every scheduler runs the file as today.** -/
theorem file_runs_as_today {tok : ℕ → O} (injective : Function.Injective tok) {initial : Finset O}
    (free : TokenFree tok initial) {file : List (Item O R)}
    (apart : ∀ e ∈ fileEffects file, EffectApart label tok e)
    (today : Executable label initial (fileEffects file)) (run : List (Commit O R)) :
    Maximal label (fun c => c ∈ chain tok 0 (fileEffects file)) (insert (tok 0) initial) run ↔
      run = chain tok 0 (fileEffects file) :=
  maximal_chain_iff injective free apart today run

/-- **Where the system is conflict-free, a parallel mode changes no outcome**: every maximal run
has the store and the answer bag of the sequential schedule. -/
theorem parallel_agrees_with_sequential {A : Type uA} {sys : Commit O R → Prop}
    {store : Finset O} (free : ConflictFree label sys store) (answer : Commit O R → A)
    {sequential run : List (Commit O R)} (maxSequential : Maximal label sys store sequential)
    (maxRun : Maximal label sys store run) :
    fireList store run = fireList store sequential ∧
      ((run.map answer : List A) : Multiset A) = (sequential.map answer : List A) := by
  obtain ⟨perm, same⟩ := free.maximal_agree maxRun maxSequential
  exact ⟨same, Multiset.coe_eq_coe.mpr (perm.map answer)⟩

end File

/-! ## Running under a budget, and resuming -/

section Budget

variable {O : Type uO} [DecidableEq O] {R : Type uR} {label : O → R} {sys : Commit O R → Prop}

/-- A scheduler policy: it picks an enabled commit of the system, or reports that none is. -/
structure Policy (label : O → R) (sys : Commit O R → Prop) where
  pick : Finset O → Option (Commit O R)
  sound : ∀ store c, pick store = some c → sys c ∧ Enabled label store c
  complete : ∀ store, pick store = none → Terminal label sys store

/-- **Run under a budget**: at most `n` steps; the commits fired, and the store reached. -/
def Policy.run (policy : Policy label sys) : ℕ → Finset O → List (Commit O R) × Finset O
  | 0, store => ([], store)
  | n + 1, store =>
      match policy.pick store with
      | none => ([], store)
      | some c => (c :: (policy.run n (fire store c)).1, (policy.run n (fire store c)).2)

/-- The commits a budgeted run fires are a run of the system, ending at the store it returns. -/
theorem Policy.run_isRun (policy : Policy label sys) :
    ∀ (n : ℕ) (store : Finset O), IsRun label sys store (policy.run n store).1 ∧
      fireList store (policy.run n store).1 = (policy.run n store).2
  | 0, store => ⟨IsRun.nil _, rfl⟩
  | n + 1, store => by
      cases h : policy.pick store with
      | none => simp only [Policy.run, h]; exact ⟨IsRun.nil _, rfl⟩
      | some c =>
          obtain ⟨member, enabled⟩ := policy.sound store c h
          obtain ⟨isRun, ends⟩ := policy.run_isRun n (fire store c)
          simp only [Policy.run, h]
          exact ⟨isRun_cons_iff.mpr ⟨member, enabled, isRun⟩, by simpa using ends⟩

/-- **Every budget cut is a reachable store.** -/
theorem Policy.run_reaches (policy : Policy label sys) (n : ℕ) (store : Finset O) :
    Reaches label sys store (policy.run n store).2 :=
  ⟨_, (policy.run_isRun n store).1, (policy.run_isRun n store).2⟩

/-- **Safety holds at every budget cut**: an invariant preserved by every enabled commit of the
system holds at every store a budgeted run returns. -/
theorem Policy.run_invariant (policy : Policy label sys) {invariant : Finset O → Prop}
    (preserved : ∀ t c, invariant t → sys c → Enabled label t c → invariant (fire t c)) :
    ∀ (n : ℕ) (store : Finset O), invariant store → invariant (policy.run n store).2
  | 0, _, holds => holds
  | n + 1, store, holds => by
      cases h : policy.pick store with
      | none => simp only [Policy.run, h]; exact holds
      | some c =>
          obtain ⟨member, enabled⟩ := policy.sound store c h
          simp only [Policy.run, h]
          exact policy.run_invariant preserved n _ (preserved store c holds member enabled)

/-- A policy that has stopped stays stopped. -/
theorem Policy.run_stopped (policy : Policy label sys) {store : Finset O}
    (stopped : policy.pick store = none) : ∀ m, policy.run m store = ([], store)
  | 0 => rfl
  | m + 1 => by simp only [Policy.run, stopped]

/-- **A budget cut is invisible**: running `n` steps and resuming for `m` is running `n + m`. -/
theorem Policy.run_add (policy : Policy label sys) :
    ∀ (n m : ℕ) (store : Finset O),
      policy.run (n + m) store =
        ((policy.run n store).1 ++ (policy.run m (policy.run n store).2).1,
          (policy.run m (policy.run n store).2).2)
  | 0, m, store => by simp [Policy.run]
  | n + 1, m, store => by
      rw [show n + 1 + m = (n + m) + 1 by omega]
      cases h : policy.pick store with
      | none => simp [Policy.run, h, policy.run_stopped h]
      | some c => simp [Policy.run, h, policy.run_add n m (fire store c)]

/-- **Stopping early means quiescence**: a budgeted run that fires fewer commits than its budget
ends at a store where no commit of the system is enabled. -/
theorem Policy.run_terminal (policy : Policy label sys) :
    ∀ (n : ℕ) (store : Finset O), (policy.run n store).1.length < n →
      Terminal label sys (policy.run n store).2
  | 0, _, short => absurd short (by simp)
  | n + 1, store, short => by
      cases h : policy.pick store with
      | none => simp only [Policy.run, h]; exact policy.complete store h
      | some c =>
          simp only [Policy.run, h, List.length_cons] at short ⊢
          exact policy.run_terminal n (fire store c) (by omega)

end Budget

/-! ## The reflected agenda -/

section Agenda

variable {O : Type uO} [DecidableEq O] {R : Type uR} {N : Type uN} {label : O → R}

/-- **Reading a continuation never runs it.** An inspection that takes nothing and makes identities
apart from the step's (and outside the step's queried regions) leaves the step it inspects
enabled, and what it read in place. -/
theorem inspect_keeps_step {store : Finset O} {step inspect : Commit O R}
    (enabledStep : Enabled label store step) (enabledInspect : Enabled label store inspect)
    (takesNothing : inspect.taken = ∅) (madeApart : Disjoint inspect.made step.made)
    (outsideQueries : ∀ read ∈ step.queries, ∀ o ∈ inspect.made, read.region (label o) = false) :
    Enabled label (fire store inspect) step ∧ inspect.kept ⊆ fire store inspect := by
  refine ⟨(enabled_fire_iff enabledStep enabledInspect).mpr ⟨?_, ?_⟩, kept_subset_fire enabledInspect⟩
  · rintro (taken | made)
    · exact taken (by rw [takesNothing]; exact Finset.disjoint_empty_right _)
    · exact made madeApart.symm
  · rintro (kept | ⟨read, member, o, written, inRegion⟩)
    · exact kept (by rw [takesNothing]; exact Finset.disjoint_empty_left _)
    · rcases Finset.mem_union.mp written with taken | made
      · rw [takesNothing] at taken; simp at taken
      · rw [outsideQueries read member o made] at inRegion; exact absurd inRegion (by decide)

omit [DecidableEq O] in
/-- **Only holders may cancel**: a formed commit that takes a continuation token at the agenda
name holds `receive` there. -/
theorem cancel_needs_receive {loc : R → N} {Γ : Rights N} {tok : ℕ → O} {agenda : N}
    (atAgenda : ∀ i, loc (label (tok i)) = agenda) {c : Commit O R}
    (formed : FormedUnder label loc Γ c) (cancels : Cancels tok c) : Γ agenda .receive = true := by
  obtain ⟨i, takes⟩ := cancels.takes
  have := formed.taken _ takes
  rwa [atAgenda i] at this

/-- **No cancellation without authority**: if no process holds `receive` at the agenda name and
no occurrence carries it, no step of a run of formed, attenuating steps takes a continuation
token. -/
theorem no_cancel_without_authority {I : Type uI} [DecidableEq I] {loc : R → N}
    {carries : R → N → Facet → Bool} {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)} {tok : ℕ → O} {agenda : N}
    (atAgenda : ∀ i, loc (label (tok i)) = agenda)
    (r : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    (unheld : ¬ Authority label carries Γ S agenda .receive) :
    ∀ x ∈ run, ∀ i, tok i ∉ x.2.taken := fun x member i takes =>
  r.never_receives unheld x member (tok i) takes (atAgenda i)

end Agenda

/-! ## Controls -/

namespace Controls

/-! ### A file of two expressions -/

/-- Continuation tokens are `100, 101, …`. -/
def tok (i : ℕ) : ℕ := 100 + i

theorem tok_injective : Function.Injective tok := fun _ _ same => by simpa [tok] using same

/-- A token is never a small identity. -/
theorem tok_ne (i k : ℕ) (small : k < 100) : tok i ≠ k := by unfold tok; omega

/-- Today: one `!` reads `a` (identity `1`) and makes `b` (`2`); the next takes `a` and makes
`c` (`3`). -/
def readA : Commit ℕ Unit := ⟨∅, {1}, {2}, []⟩
def takeA : Commit ℕ Unit := ⟨{1}, ∅, {3}, []⟩

/-- The file. -/
def file : List (Item ℕ Unit) := [.bang [readA], .bang [takeA]]

theorem file_effects : fileEffects file = [readA, takeA] := rfl

/-- **Positive control.** The file's process has exactly one maximal run, its chain: the read
before the take, as today, ending with `b`, `c` and the last token. -/
theorem file_unique_run (run : List (Commit ℕ Unit)) :
    (Maximal here (fun c => c ∈ chain tok 0 (fileEffects file)) (insert (tok 0) {1}) run ↔
      run = chain tok 0 (fileEffects file)) ∧
      fireList (insert (tok 0) {1}) (chain tok 0 (fileEffects file)) = {102, 2, 3} := by
  have apart : ∀ e ∈ fileEffects file, EffectApart here tok e := by
    intro e member
    rw [file_effects] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨fun i h => by simp [readA] at h, fun i h => tok_ne i 1 (by norm_num) (Finset.mem_singleton.mp h),
        fun i h => tok_ne i 2 (by norm_num) (Finset.mem_singleton.mp h),
        fun _ member => by simp [readA] at member⟩
    · exact ⟨fun i h => tok_ne i 1 (by norm_num) (Finset.mem_singleton.mp h),
        fun i h => by simp [takeA] at h, fun i h => tok_ne i 3 (by norm_num) (Finset.mem_singleton.mp h),
        fun _ member => by simp [takeA] at member⟩
  refine ⟨file_runs_as_today tok_injective (fun i h => tok_ne i 1 (by norm_num) (Finset.mem_singleton.mp h)) apart
    (by rw [file_effects]; exact .cons (by decide) (.cons (by decide) (.nil _))) run, by decide⟩

/-- **Negative control.** Without the continuation the same effects run in either order: taking
`a` first leaves the read disabled, and the two maximal runs end at different stores. -/
theorem untokened_file_two_outcomes :
    Maximal here (fun c => c = readA ∨ c = takeA) {1} [readA, takeA] ∧
      Maximal here (fun c => c = readA ∨ c = takeA) {1} [takeA] ∧
      fireList ({1} : Finset ℕ) [readA, takeA] ≠ fireList ({1} : Finset ℕ) [takeA] := by
  refine ⟨⟨⟨.cons (by decide) (.cons (by decide) (.nil _)), by simp⟩, ?_⟩,
    ⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩, by decide⟩
  · rintro c (rfl | rfl) <;> decide
  · rintro c (rfl | rfl) <;> decide

/-! ### Competing consumers under the parallel mode -/

/-- Workers `a` and `b` each take the job `1`; `a` records `40`, `b` records `50`. -/
def jobA : Commit ℕ Unit := ⟨{1}, ∅, {40}, []⟩
def jobB : Commit ℕ Unit := ⟨{1}, ∅, {50}, []⟩

/-- The sequential policy: it serves worker `a` whenever it can. -/
def sequentialPolicy : Policy here (fun c => c = jobA ∨ c = jobB) where
  pick store := if Enabled here store jobA then some jobA
    else if Enabled here store jobB then some jobB else none
  sound store c picked := by
    by_cases ha : Enabled here store jobA
    · simp only [ha, ↓reduceIte, Option.some.injEq] at picked; subst picked; exact ⟨Or.inl rfl, ha⟩
    · by_cases hb : Enabled here store jobB
      · simp only [ha, hb, ↓reduceIte, Option.some.injEq] at picked
        subst picked; exact ⟨Or.inr rfl, hb⟩
      · simp [ha, hb] at picked
  complete store none := by
    intro c member
    by_cases ha : Enabled here store jobA
    · simp [ha] at none
    · by_cases hb : Enabled here store jobB
      · simp [ha, hb] at none
      · rcases member with rfl | rfl <;> assumption

/-- **The parallel mode can expose a real choice.** The sequential policy always serves `a`;
another maximal run serves `b`, with a different store. -/
theorem parallel_exposes_choice :
    (sequentialPolicy.run 5 {1}).1 = [jobA] ∧
      Maximal here (fun c => c = jobA ∨ c = jobB) {1} [jobB] ∧
      fireList ({1} : Finset ℕ) [jobB] ≠ (sequentialPolicy.run 5 {1}).2 := by
  refine ⟨rfl, ⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩, by decide⟩
  rintro c (rfl | rfl) <;> decide

/-! ### The REPL -/

/-- REPL stage `1` takes line `1` (identity `11`), reads the fact `30` and makes `21`; stage `2`
takes line `2` (identity `12`) and the fact `30`, and makes `22`. In the file's order the read
comes before the take. -/
def stage₁ : Commit ℕ Unit := ⟨{11}, {30}, {21}, []⟩
def stage₂ : Commit ℕ Unit := ⟨{12, 30}, ∅, {22}, []⟩

/-- Two senders deliver the lines, each once (identities `201`, `202` are their one-shot turns). -/
def sender₁ : Commit ℕ Unit := ⟨{201}, ∅, {11}, []⟩
def sender₂ : Commit ℕ Unit := ⟨{202}, ∅, {12}, []⟩

/-- The REPL with its continuation chain, beside the senders. -/
def repl : Commit ℕ Unit → Prop :=
  fun c => c ∈ chain tok 0 [stage₁, stage₂] ∨ c = sender₁ ∨ c = sender₂

/-- The start: the first token, the senders' turns, and the fact. -/
def replStart : Finset ℕ := {100, 201, 202, 30}

theorem repl_terminal : Terminal here repl {21, 102, 22} := by
  rintro c (inChain | rfl | rfl)
  · simp only [chain_cons, chain_nil, List.mem_cons, List.not_mem_nil, or_false] at inChain
    rcases inChain with rfl | rfl <;> decide
  · decide
  · decide

/-- **Positive control, the REPL.** Line `2` arriving before line `1`, or after stage `1` has run,
gives the same result: stage `2` waits for its continuation. -/
theorem repl_arrivals_agree :
    Maximal here repl replStart
        [sender₂, sender₁, threaded (tok 0) (tok 1) stage₁, threaded (tok 1) (tok 2) stage₂] ∧
      Maximal here repl replStart
        [sender₁, threaded (tok 0) (tok 1) stage₁, sender₂, threaded (tok 1) (tok 2) stage₂] ∧
      fireList replStart
          [sender₂, sender₁, threaded (tok 0) (tok 1) stage₁, threaded (tok 1) (tok 2) stage₂] =
        fireList replStart
          [sender₁, threaded (tok 0) (tok 1) stage₁, sender₂, threaded (tok 1) (tok 2) stage₂] ∧
      ¬ Enabled here (fire replStart sender₂) (threaded (tok 1) (tok 2) stage₂) := by
  have inRepl : ∀ c, c = sender₁ ∨ c = sender₂ ∨ c = threaded (tok 0) (tok 1) stage₁ ∨
      c = threaded (tok 1) (tok 2) stage₂ → repl c := by
    rintro c (rfl | rfl | rfl | rfl) <;> simp [repl]
  refine ⟨⟨⟨.cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _)))),
      fun c member => inRepl c (by simp at member; tauto)⟩, by
        rw [show fireList replStart
          [sender₂, sender₁, threaded (tok 0) (tok 1) stage₁, threaded (tok 1) (tok 2) stage₂] =
          {21, 102, 22} by decide]; exact repl_terminal⟩,
    ⟨⟨.cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _)))),
      fun c member => inRepl c (by simp at member; tauto)⟩, by
        rw [show fireList replStart
          [sender₁, threaded (tok 0) (tok 1) stage₁, sender₂, threaded (tok 1) (tok 2) stage₂] =
          {21, 102, 22} by decide]; exact repl_terminal⟩,
    by decide, by decide⟩

/-- Without its continuation, stage `2` is a rule that fires as soon as its line arrives. -/
def untokened : Commit ℕ Unit → Prop :=
  fun c => c = stage₁ ∨ c = stage₂ ∨ c = sender₁ ∨ c = sender₂

/-- **Negative control, the REPL without its continuation.** Stages fire in arrival order: when
line `2` arrives first, stage `2` takes the fact before stage `1` can read it, stage `1` never
runs, and the result differs from the file's. -/
theorem untokened_repl_depends_on_arrival :
    Maximal here untokened {201, 202, 30} [sender₁, stage₁, sender₂, stage₂] ∧
      Maximal here untokened {201, 202, 30} [sender₂, stage₂, sender₁] ∧
      fireList ({201, 202, 30} : Finset ℕ) [sender₁, stage₁, sender₂, stage₂] ≠
        fireList ({201, 202, 30} : Finset ℕ) [sender₂, stage₂, sender₁] := by
  refine ⟨⟨⟨.cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _)))),
      by simp [untokened]⟩, ?_⟩,
    ⟨⟨.cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _))), by simp [untokened]⟩, ?_⟩,
    by decide⟩
  · rintro c (rfl | rfl | rfl | rfl) <;> decide
  · rintro c (rfl | rfl | rfl | rfl) <;> decide

/-! ### Liveness needs fairness -/

open Liveness

/-- A spinner: step `j` takes `2 j + 2` and makes `2 j + 4`. -/
def spin (j : ℕ) : Commit ℕ Unit := ⟨{2 * j + 2}, ∅, {2 * j + 4}, []⟩

/-- A task: take `1` and make `3`. -/
def task : Commit ℕ Unit := ⟨{1}, ∅, {3}, []⟩

/-- The spinner and the task. -/
def spinSys : Commit ℕ Unit → Prop := fun c => (∃ j, c = spin j) ∨ c = task

/-- The commit system as a transition system. -/
def commitLTS : LTS (Finset ℕ) (Commit ℕ Unit) where
  Allowed store c := spinSys c ∧ Enabled here store c
  next store c := fire store c

theorem spin_enabled (j : ℕ) : Enabled here {1, 2 * j + 2} (spin j) where
  taken_subset := by intro o member; simp [spin] at member; simp [member]
  kept_subset := by simp [spin]
  apart := by simp [spin]
  fresh := by
    rw [Finset.disjoint_left]
    intro o member inStore
    simp [spin] at member
    simp at inStore
    omega
  queries_hold := by simp [spin]

theorem spin_fire (j : ℕ) : fire ({1, 2 * j + 2} : Finset ℕ) (spin j) = {1, 2 * (j + 1) + 2} := by
  ext o
  simp only [fire, spin, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton]
  omega

/-- The run of the policy that always serves the spinner. -/
def spinRun : Run commitLTS where
  state n := {1, 2 * n + 2}
  label n := spin n
  allowed n := ⟨Or.inl ⟨n, rfl⟩, spin_enabled n⟩
  step n := (spin_fire n).symm

theorem task_enabled_spin (n : ℕ) : Enabled here {1, 2 * n + 2} task where
  taken_subset := by simp [task]
  kept_subset := by simp [task]
  apart := by simp [task]
  fresh := by
    rw [Finset.disjoint_left]
    intro o member inStore
    simp [task] at member
    simp at inStore
    omega
  queries_hold := by simp [task]

/-- **The spinner policy starves the task, in every budget.** The task is enabled at every moment
of the run and never served; so the run is not weakly fair for it. -/
theorem spinner_starves_task :
    (∀ n, commitLTS.TaskEnabled (· = task) (spinRun.state n)) ∧ (∀ n, spinRun.label n ≠ task) ∧
      ¬ spinRun.WeaklyFair (· = task) := by
  have enabled : ∀ n, commitLTS.TaskEnabled (· = task) (spinRun.state n) :=
    fun n => ⟨task, rfl, Or.inr rfl, task_enabled_spin n⟩
  have never : ∀ n, spinRun.label n ≠ task := by
    intro n same
    have := congrArg Commit.taken same
    simp only [spinRun, spin, task, Finset.singleton_inj] at this
    omega
  refine ⟨enabled, never, fun fair => ?_⟩
  obtain ⟨n, _, fires⟩ := fair ⟨0, fun n _ => enabled n⟩ 0
  exact never n fires

/-- Until the task fires, a run from `{1, 2}` keeps the task enabled. -/
theorem task_stays_enabled (r : Run commitLTS) (start : r.state 0 = {1, 2}) :
    ∀ n, (∀ m < n, r.label m ≠ task) → 1 ∈ r.state n ∧ 3 ∉ r.state n
  | 0, _ => by rw [start]; decide
  | n + 1, before => by
      obtain ⟨inN, notN⟩ := task_stays_enabled r start n fun m lt => before m (by omega)
      have notTask := before n (by omega)
      obtain ⟨member, _⟩ := r.allowed n
      rcases member with ⟨j, same⟩ | same
      · rw [r.step n]
        show 1 ∈ fire (r.state n) (r.label n) ∧ 3 ∉ fire (r.state n) (r.label n)
        rw [same]
        simp only [mem_fire, spin, Finset.mem_singleton]
        refine ⟨Or.inl ⟨inN, by omega⟩, ?_⟩
        rintro (⟨inState, _⟩ | made)
        · exact notN inState
        · omega
      · exact absurd same notTask

/-- **Every weakly fair run serves the task.** -/
theorem fair_serves_task (r : Run commitLTS) (start : r.state 0 = {1, 2})
    (fair : r.WeaklyFair (· = task)) : ∃ n, r.label n = task := by
  obtain ⟨n, _, fires⟩ := Run.WeaklyFair.fires fair 0 fun n _ before => by
    obtain ⟨inN, notN⟩ := task_stays_enabled r start n fun m lt => before m (Nat.zero_le m) lt
    refine ⟨task, rfl, Or.inr rfl, ?_⟩
    exact ⟨by simpa [task] using inN, by simp [task], by simp [task],
      by simpa [task] using notN, by simp [task]⟩
  exact ⟨n, fires⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
