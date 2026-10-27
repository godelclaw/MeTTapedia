import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Fair runs: weak and strong fairness, and why fairness never changes a safety result

Safety says that nothing bad happens; it is a property of finite prefixes. Liveness says that
something good keeps happening; it is a property of infinite runs, and it holds only under an
assumption about the scheduler. This module fixes the vocabulary used by every liveness module of
this folder and proves the one general fact that separates the two: **fairness assumptions of the
usual kinds never change which finite behaviours are possible.**

## Systems, runs and tasks

* A system (`LTS`) has a guard `Allowed s a` and a deterministic effect `next s a` for each label.
* A run (`Run`) is an infinite sequence of allowed steps. A finite execution is `LTS.Exec`.
* A **task** is a set of labels, for example "transaction `t` commits" or "any step of process
  `p`". It is enabled at a state when one of its labels is allowed there (`LTS.TaskEnabled`).

## Weak and strong fairness

* **Weak fairness** of a task (`Run.WeaklyFair`): if it is enabled at every moment from some time
  on, it fires infinitely often. ("Continuously enabled implies eventually fires.")
* **Strong fairness** (`Run.StronglyFair`): if it is enabled infinitely often, it fires infinitely
  often. ("Infinitely often enabled implies eventually fires.")
* Strong implies weak (`Run.StronglyFair.weaklyFair`). The converse fails for a task whose
  enabling flickers (`Controls.weak_not_strong`): a weakly fair run never fires it.
* The usable forms: under weak fairness a task that stays enabled until it fires does fire
  (`Run.WeaklyFair.fires`); under strong fairness a task enabled infinitely often fires after any
  time (`Run.StronglyFair.fires`).

## Strong fairness is implementable: the aging scheduler

For finitely many tasks and a system that never blocks, the **aging scheduler** serves, among the
enabled tasks, the one served least recently (ties broken by a fixed rank), and records the time.
Its runs are strongly fair for every task (`agingRun_stronglyFair`). The proof is a measure: the
number of tasks waiting longer than a given task never grows, and it drops every time that task is
enabled and not served. This is the scheduler-level form of aging; the same measure argument is
`PriorityFairness.fires_within` in the tree, for a least-first queue.

## Machine closure: fairness changes no safety result

A class of runs is **machine closed** (`MachineClosed`) when every finite execution is a prefix of
one of its runs. Strongly fair runs are machine closed (`machineClosed_stronglyFair`): run the
finite execution, then the aging scheduler. Hence so are weakly fair runs and all runs. For a
machine-closed class:

* an invariant holds on every run of the class exactly when it holds at every reachable state
  (`MachineClosed.invariant_iff`);
* a property of finite label sequences holds of every prefix of every run of the class exactly when
  it holds of every finite execution (`MachineClosed.traceSafety_iff`);
* a state is visited by some run of the class exactly when it is reachable
  (`MachineClosed.visits_iff`): the outcome set does not depend on the policy.

So the safety theorems of the commit semantics (refinement, no double take, the validation
ladder, the wave theorems) hold under every fairness assumption and need none, and the set of
reachable outcomes is the same under every machine-closed scheduler policy. What a scheduler policy
changes is which infinite runs are admitted: liveness, and, with probabilities, the distribution.

A system that can block is first given an idle step (`LTS.withIdle`), which is the usual stuttering
step; it adds no reachable state (`withIdle_reachable_iff`) and is never part of a task.

## Controls

* `Controls.weak_not_strong`: a flickering task, weakly but not strongly fair.
* `Controls.not_machine_closed`: an assumption on runs that is not machine closed ("the counter is
  never incremented") makes a false invariant hold on all admitted runs. Machine closure is the
  hypothesis that matters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

/-! ## Infinitely often, eventually always -/

/-- `P` holds infinitely often. -/
def InfinitelyOften (P : ℕ → Prop) : Prop := ∀ N, ∃ n ≥ N, P n

/-- `P` holds at every moment from some time on. -/
def EventuallyAlways (P : ℕ → Prop) : Prop := ∃ N, ∀ n ≥ N, P n

theorem EventuallyAlways.infinitelyOften {P : ℕ → Prop} (always : EventuallyAlways P) :
    InfinitelyOften P := by
  obtain ⟨N, holds⟩ := always
  intro M
  exact ⟨max N M, le_max_right _ _, holds _ (le_max_left _ _)⟩

theorem not_infinitelyOften_iff {P : ℕ → Prop} :
    ¬ InfinitelyOften P ↔ EventuallyAlways fun n => ¬ P n := by
  unfold InfinitelyOften EventuallyAlways
  constructor
  · intro notOften
    push Not at notOften
    exact notOften
  · rintro ⟨N, never⟩ often
    obtain ⟨n, le, holds⟩ := often N
    exact never n le holds

theorem infinitelyOften_succ_iff {P : ℕ → Prop} :
    InfinitelyOften (fun n => P (n + 1)) ↔ InfinitelyOften P := by
  constructor
  · intro often N
    obtain ⟨n, le, holds⟩ := often N
    exact ⟨n + 1, by omega, holds⟩
  · intro often N
    obtain ⟨n, le, holds⟩ := often (N + 1)
    refine ⟨n - 1, by omega, ?_⟩
    show P (n - 1 + 1)
    rwa [show n - 1 + 1 = n by omega]

theorem eventuallyAlways_succ_iff {P : ℕ → Prop} :
    EventuallyAlways (fun n => P (n + 1)) ↔ EventuallyAlways P := by
  constructor
  · rintro ⟨N, holds⟩
    refine ⟨N + 1, fun n le => ?_⟩
    have : P (n - 1 + 1) := holds (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega] at this
  · rintro ⟨N, holds⟩
    exact ⟨N, fun n le => holds (n + 1) (by omega)⟩

/-- **Descent.** A natural-number measure that never increases from time `N` on, and drops at
every moment `P` holds, lets `P` hold only finitely often. -/
theorem not_infinitelyOften_of_descent {P : ℕ → Prop} (f : ℕ → ℕ) (N : ℕ)
    (mono : ∀ n ≥ N, f (n + 1) ≤ f n) (drop : ∀ n ≥ N, P n → f (n + 1) < f n) :
    ¬ InfinitelyOften P := by
  have le_of : ∀ n ≥ N, ∀ k, f (n + k) ≤ f n := by
    intro n hn k
    induction k with
    | zero => simp
    | succ k ih => exact (mono (n + k) (by omega)).trans ih
  have key : ∀ v n, N ≤ n → f n ≤ v → ∃ M ≥ n, ∀ k ≥ M, ¬ P k := by
    intro v
    induction v with
    | zero =>
        intro n hn hv
        refine ⟨n, le_rfl, fun k hk holds => ?_⟩
        have dropped := drop k (by omega) holds
        have bound := le_of n hn (k - n)
        rw [show n + (k - n) = k by omega] at bound
        omega
    | succ v ih =>
        intro n hn hv
        by_cases some : ∃ k ≥ n, P k
        · obtain ⟨k, hk, holds⟩ := some
          have dropped := drop k (by omega) holds
          have bound := le_of n hn (k - n)
          rw [show n + (k - n) = k by omega] at bound
          obtain ⟨M, hM, rest⟩ := ih (k + 1) (by omega) (by omega)
          exact ⟨M, by omega, rest⟩
        · push Not at some
          exact ⟨n, le_rfl, some⟩
  intro often
  obtain ⟨M, -, never⟩ := key (f N) N le_rfl le_rfl
  obtain ⟨k, hk, holds⟩ := often M
  exact never k hk holds

/-! ## Systems, runs, tasks -/

/-- A labelled transition system: which labels are allowed at a state, and what each does. -/
structure LTS (S : Type u) (A : Type v) where
  Allowed : S → A → Prop
  next : S → A → S

variable {S : Type u} {A : Type v}

namespace LTS

variable (sys : LTS S A)

/-- A task (a set of labels) is enabled at a state when one of its labels is allowed there. -/
def TaskEnabled (task : A → Prop) (s : S) : Prop := ∃ a, task a ∧ sys.Allowed s a

/-- Every state allows some step. -/
def NonBlocking : Prop := ∀ s, ∃ a, sys.Allowed s a

/-- A finite execution from one state to another, with its labels. -/
inductive Exec : S → List A → S → Prop
  | nil (s : S) : Exec s [] s
  | cons {s : S} {a : A} {l : List A} {s' : S} (allowed : sys.Allowed s a)
      (rest : Exec (sys.next s a) l s') : Exec s (a :: l) s'

/-- Reachable by a finite execution. -/
def Reachable (s₀ s : S) : Prop := ∃ l, sys.Exec s₀ l s

variable {sys}

/-- The end of an execution is determined by its start and its labels. -/
theorem Exec.deterministic {s₀ s s' : S} {l : List A} (first : sys.Exec s₀ l s)
    (second : sys.Exec s₀ l s') : s = s' := by
  induction first generalizing s' with
  | nil => cases second; rfl
  | cons _ _ ih =>
      cases second with
      | cons _ rest => exact ih rest

/-- Extending an execution by one allowed step. -/
theorem Exec.snoc {s₀ s : S} {l : List A} (exec : sys.Exec s₀ l s) {a : A}
    (allowed : sys.Allowed s a) : sys.Exec s₀ (l ++ [a]) (sys.next s a) := by
  induction exec with
  | nil s => exact .cons allowed (.nil _)
  | cons first _ ih => exact .cons first (ih allowed)

end LTS

/-- An infinite run. -/
structure Run (sys : LTS S A) where
  state : ℕ → S
  label : ℕ → A
  allowed : ∀ n, sys.Allowed (state n) (label n)
  step : ∀ n, state (n + 1) = sys.next (state n) (label n)

namespace Run

variable {sys : LTS S A}

/-- **Weak fairness** of a task: continuously enabled from some time on implies fired infinitely
often. -/
def WeaklyFair (r : Run sys) (task : A → Prop) : Prop :=
  EventuallyAlways (fun n => sys.TaskEnabled task (r.state n)) →
    InfinitelyOften (fun n => task (r.label n))

/-- **Strong fairness** of a task: enabled infinitely often implies fired infinitely often. -/
def StronglyFair (r : Run sys) (task : A → Prop) : Prop :=
  InfinitelyOften (fun n => sys.TaskEnabled task (r.state n)) →
    InfinitelyOften (fun n => task (r.label n))

/-- **Strong fairness implies weak fairness.** -/
theorem StronglyFair.weaklyFair {r : Run sys} {task : A → Prop} (fair : r.StronglyFair task) :
    r.WeaklyFair task :=
  fun always => fair always.infinitelyOften

/-- **Weak fairness, usable form.** A task that is enabled at every moment from `N` until it fires
does fire at or after `N`. -/
theorem WeaklyFair.fires {r : Run sys} {task : A → Prop} (fair : r.WeaklyFair task) (N : ℕ)
    (enabled : ∀ n ≥ N, (∀ m, N ≤ m → m < n → ¬ task (r.label m)) →
      sys.TaskEnabled task (r.state n)) :
    ∃ n ≥ N, task (r.label n) := by
  by_contra never
  push Not at never
  obtain ⟨n, le, fires⟩ := fair ⟨N, fun n le => enabled n le fun m lo _ => never m lo⟩ N
  exact never n le fires

/-- **Strong fairness, usable form.** A task enabled infinitely often fires after any time. -/
theorem StronglyFair.fires {r : Run sys} {task : A → Prop} (fair : r.StronglyFair task)
    (often : InfinitelyOften fun n => sys.TaskEnabled task (r.state n)) (N : ℕ) :
    ∃ n ≥ N, task (r.label n) :=
  fair often N

/-- The labels of a run from time `k`, `n` of them. -/
def window (r : Run sys) : ℕ → ℕ → List A
  | _, 0 => []
  | k, n + 1 => r.label k :: window r (k + 1) n

theorem length_window (r : Run sys) (k n : ℕ) : (r.window k n).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [window, ih]

/-- A label in a window is a label of the run at a time inside the window. -/
theorem mem_window (r : Run sys) {k n : ℕ} {a : A} (member : a ∈ r.window k n) :
    ∃ m < n, r.label (k + m) = a := by
  induction n generalizing k with
  | zero => simp [window] at member
  | succ n ih =>
      simp only [window, List.mem_cons] at member
      rcases member with rfl | rest
      · exact ⟨0, by omega, by simp⟩
      · obtain ⟨m, lt, eq⟩ := ih rest
        exact ⟨m + 1, by omega, by rw [← eq, show k + (m + 1) = k + 1 + m by omega]⟩

/-- Every window of a run is a finite execution. -/
theorem exec_window (r : Run sys) (n : ℕ) :
    ∀ k, sys.Exec (r.state k) (r.window k n) (r.state (k + n)) := by
  induction n with
  | zero => intro k; exact .nil _
  | succ n ih =>
      intro k
      refine .cons (r.allowed k) ?_
      rw [← r.step k, show k + (n + 1) = k + 1 + n by omega]
      exact ih (k + 1)

/-- Every state of a run is reachable from its first state. -/
theorem reachable (r : Run sys) (n : ℕ) : sys.Reachable (r.state 0) (r.state n) :=
  ⟨r.window 0 n, by simpa using r.exec_window n 0⟩

/-- A window equals a list whose entries are the labels. -/
theorem window_eq_of_labels (r : Run sys) :
    ∀ (l : List A) (k : ℕ), (∀ m (h : m < l.length), r.label (k + m) = l[m]) →
      r.window k l.length = l
  | [], _, _ => rfl
  | a :: l, k, labels => by
      have head := labels 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at head
      simp only [List.length_cons, window, head, List.cons.injEq, true_and]
      exact window_eq_of_labels r l (k + 1) fun m h => by
        have := labels (m + 1) (by simp; omega)
        rwa [show k + (m + 1) = k + 1 + m by omega] at this

/-- A run with one step in front. -/
def cons (s : S) (a : A) (allowed : sys.Allowed s a) (r : Run sys)
    (start : r.state 0 = sys.next s a) : Run sys where
  state n := match n with
    | 0 => s
    | n + 1 => r.state n
  label n := match n with
    | 0 => a
    | n + 1 => r.label n
  allowed n := by
    cases n with
    | zero => exact allowed
    | succ n => exact r.allowed n
  step n := by
    cases n with
    | zero => exact start
    | succ n => exact r.step n

/-- Fairness is a property of the tail: one step in front changes nothing. -/
theorem cons_stronglyFair_iff {s : S} {a : A} {allowed : sys.Allowed s a} {r : Run sys}
    {start : r.state 0 = sys.next s a} {task : A → Prop} :
    (cons s a allowed r start).StronglyFair task ↔ r.StronglyFair task := by
  unfold StronglyFair
  have enabledIff := infinitelyOften_succ_iff
    (P := fun n => sys.TaskEnabled task ((cons s a allowed r start).state n))
  have firesIff := infinitelyOften_succ_iff
    (P := fun n => task ((cons s a allowed r start).label n))
  rw [← enabledIff, ← firesIff]
  rfl

end Run

/-! ## The aging scheduler -/

section Aging

variable {sys : LTS S A} {ι : Type w} [Fintype ι] [DecidableEq ι] (tasks : ι → A → Prop)

/-- The rank of a task in a fixed enumeration of the tasks. -/
noncomputable def rank (i : ι) : ℕ := (Fintype.equivFin ι i : ℕ)

omit [DecidableEq ι] in
theorem rank_injective : Function.Injective (rank (ι := ι)) := fun _ _ same =>
  (Fintype.equivFin ι).injective (Fin.ext same)

/-- The waiting key of a task: when it was last served, ties broken by rank. A smaller key has
waited longer. -/
noncomputable def waitKey (last : ι → ℕ) (i : ι) : ℕ ×ₗ ℕ := toLex (last i, rank i)

omit [DecidableEq ι] in
theorem waitKey_injective (last : ι → ℕ) : Function.Injective (waitKey last) := by
  intro i j same
  have := congrArg (fun x => (ofLex x).2) same
  exact rank_injective this

omit [DecidableEq ι] in
/-- Some enabled task has waited at least as long as every enabled task. -/
theorem exists_longest_waiting {s : S} (last : ι → ℕ)
    (some : ∃ i, sys.TaskEnabled (tasks i) s) :
    ∃ i, sys.TaskEnabled (tasks i) s ∧
      ∀ j, sys.TaskEnabled (tasks j) s → waitKey last i ≤ waitKey last j := by
  classical
  obtain ⟨i, enabled⟩ := some
  obtain ⟨m, member, least⟩ := Finset.exists_min_image
    (Finset.univ.filter fun j => sys.TaskEnabled (tasks j) s) (waitKey last) ⟨i, by simpa using enabled⟩
  exact ⟨m, by simpa using member, fun j enabledJ => least j (by simpa using enabledJ)⟩

open Classical in
/-- The aging choice: the task served (none when no task is enabled) and the label taken. -/
noncomputable def agingChoice (nb : sys.NonBlocking) (s : S) (last : ι → ℕ) : Option ι × A :=
  if some : ∃ i, sys.TaskEnabled (tasks i) s then
    (Option.some (Classical.choose (exists_longest_waiting tasks last some)),
      Classical.choose (Classical.choose_spec (exists_longest_waiting tasks last some)).1)
  else (none, Classical.choose (nb s))

omit [DecidableEq ι] in
theorem agingChoice_allowed (nb : sys.NonBlocking) (s : S) (last : ι → ℕ) :
    sys.Allowed s (agingChoice tasks nb s last).2 := by
  unfold agingChoice
  split_ifs with some
  · exact (Classical.choose_spec (Classical.choose_spec (exists_longest_waiting tasks last some)).1).2
  · exact Classical.choose_spec (nb s)

omit [DecidableEq ι] in
theorem agingChoice_some {nb : sys.NonBlocking} {s : S} {last : ι → ℕ} {i : ι}
    (served : (agingChoice tasks nb s last).1 = some i) :
    tasks i (agingChoice tasks nb s last).2 ∧ sys.TaskEnabled (tasks i) s ∧
      ∀ j, sys.TaskEnabled (tasks j) s → waitKey last i ≤ waitKey last j := by
  unfold agingChoice at served ⊢
  by_cases some : ∃ i, sys.TaskEnabled (tasks i) s
  · rw [dif_pos some] at served ⊢
    simp only [Option.some.injEq] at served
    subst served
    exact ⟨(Classical.choose_spec (Classical.choose_spec (exists_longest_waiting tasks last some)).1).1,
      (Classical.choose_spec (exists_longest_waiting tasks last some)).1,
      (Classical.choose_spec (exists_longest_waiting tasks last some)).2⟩
  · rw [dif_neg some] at served
    cases served

omit [DecidableEq ι] in
theorem agingChoice_none {nb : sys.NonBlocking} {s : S} {last : ι → ℕ}
    (none : (agingChoice tasks nb s last).1 = none) : ∀ i, ¬ sys.TaskEnabled (tasks i) s := by
  unfold agingChoice at none
  by_cases some : ∃ i, sys.TaskEnabled (tasks i) s
  · rw [dif_pos some] at none
    cases none
  · push Not at some
    exact some

/-- Record a service. -/
def serve : Option ι → (ι → ℕ) → ℕ → (ι → ℕ)
  | some i, last, t => Function.update last i t
  | none, last, _ => last

/-- The states of the aging scheduler, with the last service time of each task. -/
noncomputable def agingTrace (nb : sys.NonBlocking) (s₀ : S) : ℕ → S × (ι → ℕ)
  | 0 => (s₀, fun _ => 0)
  | n + 1 =>
      (sys.next (agingTrace nb s₀ n).1 (agingChoice tasks nb (agingTrace nb s₀ n).1 (agingTrace nb s₀ n).2).2,
        serve (agingChoice tasks nb (agingTrace nb s₀ n).1 (agingTrace nb s₀ n).2).1
          (agingTrace nb s₀ n).2 (n + 1))

/-- The run of the aging scheduler. -/
noncomputable def agingRun (nb : sys.NonBlocking) (s₀ : S) : Run sys where
  state n := (agingTrace tasks nb s₀ n).1
  label n := (agingChoice tasks nb (agingTrace tasks nb s₀ n).1 (agingTrace tasks nb s₀ n).2).2
  allowed _ := agingChoice_allowed tasks nb _ _
  step _ := rfl

theorem agingTrace_last_le (nb : sys.NonBlocking) (s₀ : S) :
    ∀ n i, (agingTrace tasks nb s₀ n).2 i ≤ n := by
  intro n
  induction n with
  | zero => intro i; simp [agingTrace]
  | succ n ih =>
      intro i
      simp only [agingTrace]
      cases (agingChoice tasks nb (agingTrace tasks nb s₀ n).1 (agingTrace tasks nb s₀ n).2).1 with
      | none => simp only [serve]; exact (ih i).trans (Nat.le_succ n)
      | some j =>
          simp only [serve]
          by_cases same : i = j
          · subst same; simp
          · rw [Function.update_of_ne same]; exact (ih i).trans (Nat.le_succ n)

/-- The tasks that have waited longer than `i`. -/
noncomputable def ahead (last : ι → ℕ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => waitKey last j < waitKey last i

/-- One step of the aging scheduler, seen from a task `i` that it does not serve: the tasks ahead
of `i` do not grow, and they shrink when `i` was enabled. -/
theorem ahead_step (nb : sys.NonBlocking) (s₀ : S) (i : ι) (n : ℕ)
    (notI : ¬ tasks i ((agingRun tasks nb s₀).label n)) :
    (ahead ((agingTrace tasks nb s₀ (n + 1)).2) i).card ≤ (ahead (agingTrace tasks nb s₀ n).2 i).card ∧
      (sys.TaskEnabled (tasks i) ((agingRun tasks nb s₀).state n) →
        (ahead ((agingTrace tasks nb s₀ (n + 1)).2) i).card <
          (ahead (agingTrace tasks nb s₀ n).2 i).card) := by
  set last := (agingTrace tasks nb s₀ n).2 with lastDef
  set choice := agingChoice tasks nb (agingTrace tasks nb s₀ n).1 last with choiceDef
  have nextLast : (agingTrace tasks nb s₀ (n + 1)).2 = serve choice.1 last (n + 1) := rfl
  have bound : ∀ i, last i ≤ n := agingTrace_last_le tasks nb s₀ n
  rcases served : choice.1 with _ | j
  · -- nothing enabled: nothing changes, and `i` was not enabled
    have none := agingChoice_none tasks served
    rw [nextLast, served]
    exact ⟨le_rfl, fun enabled => absurd enabled (none i)⟩
  · obtain ⟨firesJ, _, least⟩ := agingChoice_some tasks served
    have different : j ≠ i := by
      rintro rfl
      exact notI firesJ
    rw [nextLast, served]
    have newKey : waitKey last i < waitKey (serve (some j) last (n + 1)) j := by
      simp only [serve, waitKey, Function.update_self]
      exact Prod.Lex.lt_iff.2 (Or.inl (by simp only [ofLex_toLex]; have := bound i; omega))
    have sameI : waitKey (serve (some j) last (n + 1)) i = waitKey last i := by
      simp [serve, waitKey, Function.update_of_ne (Ne.symm different)]
    have subset : ahead (serve (some j) last (n + 1)) i ⊆ (ahead last i).erase j := by
      intro k member
      simp only [ahead, Finset.mem_filter, Finset.mem_univ, true_and] at member
      rw [sameI] at member
      by_cases same : k = j
      · subst same; exact absurd newKey (not_lt.2 member.le)
      · refine Finset.mem_erase.2 ⟨same, ?_⟩
        simp only [ahead, Finset.mem_filter, Finset.mem_univ, true_and]
        have : waitKey (serve (some j) last (n + 1)) k = waitKey last k := by
          simp [serve, waitKey, Function.update_of_ne same]
        rwa [this] at member
    refine ⟨(Finset.card_le_card subset).trans (Finset.card_erase_le), fun enabled => ?_⟩
    have jAhead : j ∈ ahead last i := by
      simp only [ahead, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne (least i enabled) fun same => different (waitKey_injective last same)
    exact lt_of_le_of_lt (Finset.card_le_card subset) (Finset.card_erase_lt_of_mem jAhead)

/-- **The aging scheduler is strongly fair for every task.** -/
theorem agingRun_stronglyFair (nb : sys.NonBlocking) (s₀ : S) (i : ι) :
    (agingRun tasks nb s₀).StronglyFair (tasks i) := by
  intro often
  by_contra notOften
  obtain ⟨N, never⟩ := not_infinitelyOften_iff.mp notOften
  exact not_infinitelyOften_of_descent
    (fun n => (ahead (agingTrace tasks nb s₀ n).2 i).card) N
    (fun n le => (ahead_step tasks nb s₀ i n (never n le)).1)
    (fun n le enabled => (ahead_step tasks nb s₀ i n (never n le)).2 enabled) often

/-- Strongly fair runs exist from every state of a system that never blocks. -/
theorem exists_stronglyFair_run (nb : sys.NonBlocking) (s₀ : S) :
    ∃ r : Run sys, r.state 0 = s₀ ∧ ∀ i, r.StronglyFair (tasks i) :=
  ⟨agingRun tasks nb s₀, rfl, agingRun_stronglyFair tasks nb s₀⟩

/-- **Every finite execution extends to a strongly fair run.** -/
theorem exists_stronglyFair_run_through (nb : sys.NonBlocking) {s₀ s : S} {l : List A}
    (exec : sys.Exec s₀ l s) :
    ∃ r : Run sys, r.state 0 = s₀ ∧ r.state l.length = s ∧
      (∀ m (h : m < l.length), r.label m = l[m]) ∧ ∀ i, r.StronglyFair (tasks i) := by
  induction exec with
  | nil s =>
      obtain ⟨r, start, fair⟩ := exists_stronglyFair_run tasks nb s
      exact ⟨r, start, start, fun m h => absurd h (by simp), fair⟩
  | @cons s a l s' allowed rest ih =>
      obtain ⟨r, start, finish, labels, fair⟩ := ih
      refine ⟨Run.cons s a allowed r start, rfl, finish, fun m h => ?_,
        fun i => Run.cons_stronglyFair_iff.2 (fair i)⟩
      cases m with
      | zero => rfl
      | succ m => exact labels m (by simp at h; omega)

end Aging

/-! ## Machine closure -/

/-- A class of runs is **machine closed** at `s₀` when every finite execution from `s₀` is a prefix
of one of its runs. -/
def MachineClosed (sys : LTS S A) (s₀ : S) (Fair : Run sys → Prop) : Prop :=
  ∀ l s, sys.Exec s₀ l s → ∃ r : Run sys, Fair r ∧ r.state 0 = s₀ ∧ r.window 0 l.length = l

theorem MachineClosed.mono {sys : LTS S A} {s₀ : S} {Fair Fair' : Run sys → Prop}
    (closed : MachineClosed sys s₀ Fair) (weaker : ∀ r, Fair r → Fair' r) :
    MachineClosed sys s₀ Fair' := by
  intro l s exec
  obtain ⟨r, fair, start, window⟩ := closed l s exec
  exact ⟨r, weaker r fair, start, window⟩

/-- **Strongly fair runs are machine closed**, for finitely many tasks of a system that never
blocks. -/
theorem machineClosed_stronglyFair {sys : LTS S A} {ι : Type w} [Fintype ι] [DecidableEq ι]
    (tasks : ι → A → Prop) (nb : sys.NonBlocking) (s₀ : S) :
    MachineClosed sys s₀ fun r => ∀ i, r.StronglyFair (tasks i) := by
  intro l s exec
  obtain ⟨r, start, _, labels, fair⟩ := exists_stronglyFair_run_through tasks nb exec
  exact ⟨r, fair, start, r.window_eq_of_labels l 0 fun m h => by simpa using labels m h⟩

/-- Weakly fair runs are machine closed. -/
theorem machineClosed_weaklyFair {sys : LTS S A} {ι : Type w} [Fintype ι] [DecidableEq ι]
    (tasks : ι → A → Prop) (nb : sys.NonBlocking) (s₀ : S) :
    MachineClosed sys s₀ fun r => ∀ i, r.WeaklyFair (tasks i) :=
  (machineClosed_stronglyFair tasks nb s₀).mono fun _ fair i => (fair i).weaklyFair

/-- **An invariant holds on every run of a machine-closed class exactly when it holds at every
reachable state.** Fairness does not change safety. -/
theorem MachineClosed.invariant_iff {sys : LTS S A} {s₀ : S} {Fair : Run sys → Prop}
    (closed : MachineClosed sys s₀ Fair) (Inv : S → Prop) :
    (∀ r : Run sys, Fair r → r.state 0 = s₀ → ∀ n, Inv (r.state n)) ↔
      ∀ s, sys.Reachable s₀ s → Inv s := by
  constructor
  · rintro onRuns s ⟨l, exec⟩
    obtain ⟨r, fair, start, window⟩ := closed l s exec
    have reached := r.exec_window l.length 0
    rw [window, Nat.zero_add, start] at reached
    rw [exec.deterministic reached]
    exact onRuns r fair start l.length
  · intro onReachable r _ start n
    exact onReachable _ (start ▸ r.reachable n)

/-- **A property of finite label sequences holds of every prefix of every run of a machine-closed
class exactly when it holds of every finite execution.** -/
theorem MachineClosed.traceSafety_iff {sys : LTS S A} {s₀ : S} {Fair : Run sys → Prop}
    (closed : MachineClosed sys s₀ Fair) (Safe : List A → Prop) :
    (∀ r : Run sys, Fair r → r.state 0 = s₀ → ∀ n, Safe (r.window 0 n)) ↔
      ∀ l s, sys.Exec s₀ l s → Safe l := by
  constructor
  · intro onRuns l s exec
    obtain ⟨r, fair, start, window⟩ := closed l s exec
    rw [← window]
    exact onRuns r fair start l.length
  · intro onExecs r _ start n
    have := r.exec_window n 0
    rw [Nat.zero_add, start] at this
    exact onExecs _ _ this

/-- **The outcomes are the same under every machine-closed policy**: a state is visited by some
run of the class exactly when it is reachable. -/
theorem MachineClosed.visits_iff {sys : LTS S A} {s₀ : S} {Fair : Run sys → Prop}
    (closed : MachineClosed sys s₀ Fair) (s : S) :
    (∃ r : Run sys, Fair r ∧ r.state 0 = s₀ ∧ ∃ n, r.state n = s) ↔ sys.Reachable s₀ s := by
  constructor
  · rintro ⟨r, _, start, n, rfl⟩
    exact start ▸ r.reachable n
  · rintro ⟨l, exec⟩
    obtain ⟨r, fair, start, window⟩ := closed l s exec
    have reached := r.exec_window l.length 0
    rw [window, Nat.zero_add, start] at reached
    exact ⟨r, fair, start, l.length, (exec.deterministic reached).symm⟩

/-! ## The idle step -/

namespace LTS

/-- The system with an idle step, allowed everywhere and changing nothing. -/
def withIdle (sys : LTS S A) : LTS S (Option A) where
  Allowed s
    | none => True
    | some a => sys.Allowed s a
  next s
    | none => s
    | some a => sys.next s a

theorem withIdle_nonBlocking (sys : LTS S A) : sys.withIdle.NonBlocking := fun _ => ⟨none, trivial⟩

/-- A task of the system, as a task of the system with an idle step: the idle step is in no task. -/
def liftTask (task : A → Prop) : Option A → Prop
  | none => False
  | some a => task a

theorem withIdle_taskEnabled_iff (sys : LTS S A) (task : A → Prop) (s : S) :
    sys.withIdle.TaskEnabled (liftTask task) s ↔ sys.TaskEnabled task s := by
  constructor
  · rintro ⟨a, inTask, allowed⟩
    cases a with
    | none => exact absurd inTask id
    | some a => exact ⟨a, inTask, allowed⟩
  · rintro ⟨a, inTask, allowed⟩
    exact ⟨some a, inTask, allowed⟩

/-- **The idle step adds no reachable state.** -/
theorem withIdle_reachable_iff (sys : LTS S A) (s₀ s : S) :
    sys.withIdle.Reachable s₀ s ↔ sys.Reachable s₀ s := by
  constructor
  · rintro ⟨l, exec⟩
    induction exec with
    | nil s => exact ⟨[], .nil s⟩
    | @cons s a l s' allowed _ ih =>
        cases a with
        | none => exact ih
        | some a =>
            obtain ⟨l', exec'⟩ := ih
            exact ⟨a :: l', .cons allowed exec'⟩
  · rintro ⟨l, exec⟩
    induction exec with
    | nil s => exact ⟨[], .nil s⟩
    | @cons s a l s' allowed _ ih =>
        obtain ⟨l', exec'⟩ := ih
        exact ⟨some a :: l', .cons (a := some a) allowed exec'⟩

end LTS

/-! ## Controls -/

namespace Controls

/-- Two moves on a token that is free (`true`) or held (`false`): toggle it, or take it while free. -/
inductive Move where
  | toggle
  | take
  deriving DecidableEq

/-- The token system: `take` is allowed only while the token is free and changes nothing here;
only its enabling matters. -/
def tokenSystem : LTS Bool Move where
  Allowed s
    | .toggle => True
    | .take => s = true
  next s
    | .toggle => !s
    | .take => s

/-- The run that toggles forever. -/
def toggleRun : Run tokenSystem where
  state n := decide (n % 2 = 0)
  label _ := .toggle
  allowed _ := trivial
  step n := by
    show decide ((n + 1) % 2 = 0) = !decide (n % 2 = 0)
    rcases Nat.mod_two_eq_zero_or_one n with even | odd
    · simp [even, Nat.add_mod]
    · simp [odd, Nat.add_mod]

/-- The take task. -/
def takeTask : Move → Prop := fun m => m = .take

/-- **Weak fairness is not strong fairness.** The toggling run is weakly fair for `take`, whose
enabling flickers, and never takes; it is not strongly fair for `take`. -/
theorem weak_not_strong :
    toggleRun.WeaklyFair takeTask ∧ ¬ toggleRun.StronglyFair takeTask ∧
      ∀ n, ¬ takeTask (toggleRun.label n) := by
  have enabledIff : ∀ n, tokenSystem.TaskEnabled takeTask (toggleRun.state n) ↔ n % 2 = 0 := by
    intro n
    constructor
    · rintro ⟨m, rfl, allowed⟩
      simpa [tokenSystem, toggleRun] using allowed
    · intro even
      exact ⟨.take, rfl, by simp [tokenSystem, toggleRun, even]⟩
  have never : ∀ n, ¬ takeTask (toggleRun.label n) := fun n h => by cases h
  refine ⟨?_, ?_, never⟩
  · rintro ⟨N, always⟩
    have odd := (enabledIff (2 * N + 1)).1 (always _ (by omega))
    omega
  · intro fair
    obtain ⟨n, _, fires⟩ := fair (fun N => ⟨2 * N, by omega, (enabledIff _).2 (by omega)⟩) 0
    exact never n fires

/-- A counter that may stay or increment. -/
def counter : LTS ℕ Bool where
  Allowed _ _ := True
  next s
    | true => s + 1
    | false => s

/-- The assumption "the counter is never incremented" is not machine closed. -/
def NeverIncrement (r : Run counter) : Prop := ∀ n, r.label n = false

/-- **An assumption that is not machine closed changes safety.** Every run under it keeps the
counter at zero, yet one is reachable; machine closure fails. -/
theorem not_machine_closed :
    (∀ r : Run counter, NeverIncrement r → r.state 0 = 0 → ∀ n, r.state n = 0) ∧
      counter.Reachable 0 1 ∧ ¬ MachineClosed counter 0 NeverIncrement := by
  have zero : ∀ r : Run counter, NeverIncrement r → r.state 0 = 0 → ∀ n, r.state n = 0 := by
    intro r never start n
    induction n with
    | zero => exact start
    | succ n ih => rw [r.step n, never n, ih]; rfl
  have reach : counter.Reachable 0 1 := ⟨[true], .cons trivial (.nil _)⟩
  refine ⟨zero, reach, fun closed => ?_⟩
  have := (closed.invariant_iff (fun s => s = 0)).1 (fun r never start n => zero r never start n) 1 reach
  cases this

/-! ### Non-blocking systems, machine closure, weak fairness -/

/-- **Non-blocking, positive**: the token system always allows a toggle. -/
theorem token_nonBlocking : tokenSystem.NonBlocking := fun _ => ⟨.toggle, trivial⟩

/-- A system that may only count down: state `0` allows no step. -/
def stuckAtZero : LTS ℕ Unit where
  Allowed s _ := s ≠ 0
  next s _ := s - 1

/-- **Non-blocking, negative**: state `0` of `stuckAtZero` allows no step. -/
theorem stuckAtZero_blocks : ¬ stuckAtZero.NonBlocking := fun nonBlocking => by
  obtain ⟨_, allowed⟩ := nonBlocking 0
  exact allowed rfl

/-- **Machine closed, positive**: strong fairness for `take` is machine closed on the token system,
which never blocks: every finite execution extends to a strongly fair run.
(`not_machine_closed` is the negative control.) -/
theorem token_stronglyFair_machineClosed :
    MachineClosed tokenSystem true fun r => ∀ _ : Unit, r.StronglyFair takeTask :=
  machineClosed_stronglyFair (fun _ : Unit => takeTask) token_nonBlocking true

/-- The counter staying at `0` forever. -/
def stayRun : Run counter where
  state _ := 0
  label _ := false
  allowed _ := trivial
  step _ := rfl

/-- **Weak fairness, negative**: incrementing is enabled at every moment of `stayRun` and never
taken. (`flicker_weaklyFair` and `weak_not_strong` contain positive controls.) -/
theorem stay_not_weaklyFair : ¬ stayRun.WeaklyFair fun b => b = true := by
  intro fair
  obtain ⟨n, -, taken⟩ := fair ⟨0, fun _ _ => ⟨true, rfl, trivial⟩⟩ 0
  exact Bool.false_ne_true taken

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
