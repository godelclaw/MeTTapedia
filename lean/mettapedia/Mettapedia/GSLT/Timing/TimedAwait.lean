import Mettapedia.GSLT.Timing.ClockModels
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScopeExtrusion

/-!
# A timed `await` is a choice whose second arm is a deadline

`(await X)` with a timeout parks one occurrence `k`, the continuation. It has two arms, each an
ordinary commit of `OccurrenceCommits`:

* the **wake arm** takes `k` and the awaited message `m` and makes the resumption (`wakeArm`);
* the **deadline arm** takes `k` and a deadline occurrence `dl` and makes the timed-out
  resumption (`deadlineArm`).

The deadline occurrence is made by the **clock region**: a region only the clock writes, whose one
commit takes the armed timer and makes `dl` (`fireDeadline`). The clock fires that commit when its
reading has passed the deadline (`ClockModels.Passed`); what this means in real time is the
clock model's business. The semantics of the `await` itself has no clock in it.

## The deadline is just another commit

* Every commit here is positive (`wakeArm_positive`, `deadlineArm_positive`,
  `fireDeadline_positive`). So the frame law holds for them, and a parked deadline arm is woken by
  exactly one arrival, the deadline occurrence (`deadline_minimal_wake`): it waits on the clock
  region's arrival queue like any positive guard in K's wait index.

## Cancellation by deadline keeps the authority and continuation laws

* **The arms clash** (`arms_clash`): both take `k`. A cancel arm, which takes `k` and a cancel
  token, clashes with both as well (`cancel_clashes`).
* **At most one taker of the continuation** (`at_most_one_take`): in every executable run in which
  no commit makes `k` again, at most one commit takes `k`.
* **Exactly one wins** (`exactly_one_take`): if, at the end of such a run, `k` is gone, exactly one
  commit took it; when the only commits that may take `k` are the arms (the continuation is held
  by the `await` alone), that commit is an arm.
* **A fired deadline cannot be lost** (`deadline_enabled`, `parked_gone_of_quiescent`): while `k`
  is parked and `dl` is present, the deadline arm is enabled; a store where `dl` is present and the
  deadline arm is not enabled has no `k`.
* **Time grants no authority** (`deadline_learns_parked`, `wake_learns`): the names the deadline
  arm learns are those of the parked continuation, since a deadline occurrence carries no names;
  the wake arm learns the continuation's names and the message's. The clock region's commit
  learns only what the timer carries (`fireDeadline_learns`). Control: a supervisor that takes the
  continuation and keeps its own capability learns the capability's names
  (`Controls.supervisor_learns_capability`): cancellation by another process changes authority,
  cancellation by deadline does not.

## What "the deadline fires" means

* **In synchrony with a prompt wake, a timeout means no reply came in time**
  (`wake_before_deadline`): a reply within `R` of arming, woken within `Φ`, with the caller's clock
  at most at `fast / den` and `fast · (R + Φ) < den · D`, wakes the continuation before the
  deadline passes; after the wake no deadline arm is ever enabled (`deadline_dead_after_wake`).
* **Otherwise the reply may come after the timeout** (`Controls.late_reply_orphaned`): the clock
  fires, the deadline arm takes `k`, and the reply then arrives and stays, an orphan that nobody
  takes. That is the late completion that `TimeoutUnknown` matches by identifier: a timeout
  resumes the continuation with "unknown", never with "failed".
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Timing.TimedAwait

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- The wake arm: take the parked continuation `k` and the message `m`, make the resumption. -/
def wakeArm (k m out : O) : Commit O R := ⟨{k, m}, ∅, {out}, []⟩

/-- The deadline arm: take the parked continuation `k` and the deadline occurrence `dl`, make the
timed-out resumption. -/
def deadlineArm (k dl out : O) : Commit O R := ⟨{k, dl}, ∅, {out}, []⟩

/-- A cancel arm: take the parked continuation and a cancel token. -/
def cancelArm (k token out : O) : Commit O R := ⟨{k, token}, ∅, {out}, []⟩

/-- The clock region's commit: take the armed timer, make the deadline occurrence. -/
def fireDeadline (timer dl : O) : Commit O R := ⟨{timer}, ∅, {dl}, []⟩

/-! ## The deadline is just another commit -/

theorem wakeArm_positive (k m out : O) : (wakeArm k m out : Commit O R).Positive := rfl

theorem deadlineArm_positive (k dl out : O) : (deadlineArm k dl out : Commit O R).Positive := rfl

omit [DecidableEq O] in
theorem fireDeadline_positive (timer dl : O) : (fireDeadline timer dl : Commit O R).Positive := rfl

/-- **A parked deadline arm is woken by exactly the deadline occurrence.** At a store holding the
continuation and not the deadline, the minimal waking context of the deadline arm is `{dl}`. -/
theorem deadline_minimal_wake {label : O → R} {store : Finset O} {k dl out : O}
    (parked : k ∈ store) (notYet : dl ∉ store) (apart : k ≠ dl) (fresh : out ∉ store)
    (outNew : out ≠ dl) :
    ((deadlineArm k dl out : Commit O R).taken ∪ (deadlineArm k dl out : Commit O R).kept) \ store =
        {dl} ∧
      Enabled label (store ∪ {dl}) (deadlineArm k dl out) := by
  have need : ((deadlineArm k dl out : Commit O R).taken ∪
      (deadlineArm k dl out : Commit O R).kept) \ store = {dl} := by
    ext o
    simp only [deadlineArm, Finset.union_empty, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, notIn⟩
      · exact absurd parked notIn
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, notYet⟩
  refine ⟨need, ?_⟩
  have := (minimal_wake (label := label) (store := store) (c := deadlineArm k dl out) rfl
    (by simp [deadlineArm, Finset.disjoint_empty_right])
    (by simp [deadlineArm, fresh])
    (by rw [need]; simp [deadlineArm, outNew])).1
  rwa [need] at this

/-! ## Clash, and at most one taker -/

theorem arms_clash (k m dl out out' : O) :
    Clash (wakeArm k m out : Commit O R) (deadlineArm k dl out') :=
  Or.inl (Finset.not_disjoint_iff.mpr ⟨k, by simp [wakeArm], by simp [deadlineArm]⟩)

theorem cancel_clashes (k m dl token out out' : O) :
    Clash (cancelArm k token out : Commit O R) (wakeArm k m out') ∧
      Clash (cancelArm k token out : Commit O R) (deadlineArm k dl out') :=
  ⟨Or.inl (Finset.not_disjoint_iff.mpr ⟨k, by simp [cancelArm], by simp [wakeArm]⟩),
    Or.inl (Finset.not_disjoint_iff.mpr ⟨k, by simp [cancelArm], by simp [deadlineArm]⟩)⟩

/-- An occurrence that is absent and never made is never taken. -/
theorem no_take_of_absent {label : O → R} {k : O} :
    ∀ {store : Finset O} {run : List (Commit O R)}, Executable label store run → k ∉ store →
      (∀ c ∈ run, k ∉ c.made) → ∀ c ∈ run, k ∉ c.taken := by
  intro store run executable
  induction executable with
  | nil => intro _ _ c member; simp at member
  | @cons store c rest enabled after ih =>
      intro absent neverMade d member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact fun taken => absent (enabled.taken_subset taken)
      · apply ih _ (fun e inRest' => neverMade e (List.mem_cons_of_mem _ inRest')) d inRest
        intro inFire
        rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
        · exact absent inStore
        · exact neverMade c List.mem_cons_self made

/-- **At most one taker of the continuation**: in every executable run in which no commit makes
`k`, at most one commit takes `k`. -/
theorem at_most_one_take {label : O → R} {k : O} :
    ∀ {store : Finset O} {run : List (Commit O R)}, Executable label store run →
      (∀ c ∈ run, k ∉ c.made) → (run.filter fun c => decide (k ∈ c.taken)).length ≤ 1 := by
  intro store run executable
  induction executable with
  | nil => intro _; simp
  | @cons store c rest enabled after ih =>
      intro neverMade
      have restNeverMade : ∀ d ∈ rest, k ∉ d.made := fun d member =>
        neverMade d (List.mem_cons_of_mem _ member)
      by_cases takes : k ∈ c.taken
      · have gone : k ∉ fire store c := fun inFire => by
          rcases mem_fire.mp inFire with ⟨_, notTaken⟩ | made
          · exact notTaken takes
          · exact neverMade c List.mem_cons_self made
        have none := no_take_of_absent after gone restNeverMade
        have empty : (rest.filter fun d => decide (k ∈ d.taken)) = [] :=
          List.filter_eq_nil_iff.mpr fun d member => by simpa using none d member
        simp [takes, empty]
      · simpa [List.filter_cons, takes] using ih restNeverMade

/-- Only a take removes an occurrence. -/
theorem taken_of_gone {label : O → R} {k : O} :
    ∀ {store : Finset O} {run : List (Commit O R)}, Executable label store run → k ∈ store →
      k ∉ fireList store run → ∃ c ∈ run, k ∈ c.taken := by
  intro store run executable
  induction executable with
  | nil => intro present gone; exact absurd present gone
  | @cons store c rest enabled after ih =>
      intro present gone
      by_cases takes : k ∈ c.taken
      · exact ⟨c, List.mem_cons_self, takes⟩
      · obtain ⟨d, member, taken⟩ := ih (mem_fire.mpr (Or.inl ⟨present, takes⟩)) gone
        exact ⟨d, List.mem_cons_of_mem _ member, taken⟩

/-- **Exactly one wins**: in an executable run from a store holding `k`, in which no commit makes
`k`, if `k` is gone at the end then exactly one commit took it; if moreover only the arms may take
`k`, that commit is an arm. -/
theorem exactly_one_take {label : O → R} {k : O} {store : Finset O} {run : List (Commit O R)}
    (executable : Executable label store run) (present : k ∈ store) (neverMade : ∀ c ∈ run, k ∉ c.made)
    (gone : k ∉ fireList store run) {IsArm : Commit O R → Prop}
    (onlyArms : ∀ c ∈ run, k ∈ c.taken → IsArm c) :
    (run.filter fun c => decide (k ∈ c.taken)).length = 1 ∧ ∃ c ∈ run, k ∈ c.taken ∧ IsArm c := by
  obtain ⟨c, member, taken⟩ := taken_of_gone executable present gone
  refine ⟨le_antisymm (at_most_one_take executable neverMade) ?_, c, member, taken,
    onlyArms c member taken⟩
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨member, by simpa using taken⟩)

/-! ## A fired deadline cannot be lost -/

/-- **While the continuation is parked and the deadline has fired, the deadline arm is
enabled.** -/
theorem deadline_enabled {label : O → R} {store : Finset O} {k dl out : O} (parked : k ∈ store)
    (fired : dl ∈ store) (fresh : out ∉ store) :
    Enabled label store (deadlineArm k dl out) where
  taken_subset := by
    intro o member
    simp only [deadlineArm, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact parked
    · exact fired
  kept_subset := by simp [deadlineArm]
  apart := by simp [deadlineArm]
  fresh := by simp [deadlineArm, fresh]
  queries_hold := by simp [deadlineArm]

/-- **No quiescent store keeps a timed-out continuation parked**: where the deadline has fired and
the deadline arm is not enabled (with a fresh resumption), the continuation is gone. -/
theorem parked_gone_of_quiescent {label : O → R} {store : Finset O} {k dl out : O}
    (fired : dl ∈ store) (fresh : out ∉ store)
    (quiescent : ¬ Enabled label store (deadlineArm k dl out)) : k ∉ store :=
  fun parked => quiescent (deadline_enabled parked fired fresh)

/-- **After the wake, no deadline arm is ever enabled**: once the wake arm has fired, in every
continuation that does not make `k` again, the deadline arm is not enabled. -/
theorem deadline_dead_after_wake {label : O → R} {store : Finset O} {k m dl out out' : O}
    {rest : List (Commit O R)}
    (executable : Executable label (fire store (wakeArm k m out : Commit O R)) rest)
    (neverMade : ∀ c ∈ rest, k ∉ c.made) (outNotK : out ≠ k) :
    ¬ Enabled label (fireList (fire store (wakeArm k m out : Commit O R)) rest) (deadlineArm k dl out') := by
  intro enabled
  have gone : k ∉ fire store (wakeArm k m out : Commit O R) := fun inFire => by
    rcases mem_fire.mp inFire with ⟨_, notTaken⟩ | made
    · exact notTaken (by simp [wakeArm])
    · simp only [wakeArm, Finset.mem_singleton] at made
      exact outNotK made.symm
  have stillGone : ∀ (l : List (Commit O R)) (S : Finset O), Executable label S l → k ∉ S →
      (∀ c ∈ l, k ∉ c.made) → k ∉ fireList S l := by
    intro l
    induction l with
    | nil => intro S _ absent _; exact absent
    | cons c tail ih =>
        intro S exec absent never
        rcases executable_cons_iff.mp exec with ⟨_, after⟩
        apply ih _ after _ (fun d member => never d (List.mem_cons_of_mem _ member))
        intro inFire
        rcases mem_fire.mp inFire with ⟨inS, _⟩ | made
        · exact absent inS
        · exact never c List.mem_cons_self made
  exact stillGone rest _ executable gone neverMade (enabled.taken_subset (by simp [deadlineArm]))

/-! ## Time grants no authority -/

section Authority

variable {N : Type w} [DecidableEq N] (label : O → R) (names : R → Finset N)

/-- **The deadline arm learns the parked continuation's names and nothing else**: a deadline
occurrence carries no names. -/
theorem deadline_learns_parked {k dl out : O} (nameless : names (label dl) = ∅) :
    learned label names (deadlineArm k dl out : Commit O R) = names (label k) := by
  ext n
  simp [learned, deadlineArm, nameless]

/-- The wake arm learns the continuation's names and the message's. -/
theorem wake_learns (k m out : O) :
    learned label names (wakeArm k m out : Commit O R) = names (label k) ∪ names (label m) := by
  ext n
  simp [learned, wakeArm]

/-- The clock region's commit learns only what the timer carries. -/
theorem fireDeadline_learns (timer dl : O) :
    learned label names (fireDeadline timer dl : Commit O R) = names (label timer) := by
  ext n
  simp [learned, fireDeadline]

end Authority

/-! ## What "the deadline fires" means in real time -/

/-- **In synchrony with a prompt wake, the wake comes first.** The continuation is armed at `t₀`
with a deadline of `D` units of the caller's clock, which runs at most at `fast / den`. The reply
is made by `t₀ + R` and the wake arm fires within `Φ` of it. If `fast · (R + Φ) < den · D`, the wake
fires strictly before the deadline passes, so before the clock region can make the deadline
occurrence. -/
theorem wake_before_deadline {c : Mettapedia.GSLT.Timing.Clock} {den slow fast t₀ D R Φ tm tw td : ℕ}
    (rates : Mettapedia.GSLT.Timing.RateBounds c den slow fast) (replyBy : tm ≤ t₀ + R)
    (prompt : tw ≤ tm + Φ) (margin : fast * (R + Φ) < den * D)
    (passed : Mettapedia.GSLT.Timing.Passed c t₀ D td) : tw < td :=
  Mettapedia.GSLT.Timing.reply_before_passed rates (r := tw) (R := R + Φ) (by omega) margin passed

/-! ## Controls -/

namespace Controls

/-- Labels: the parked continuation with its names, the reply, the timer and the deadline, the
supervisor's capability, the two resumptions, a cancel token. -/
inductive Item where
  | parked
  | reply
  | timer
  | deadline
  | capability
  | resumed
  | timedOut
  | cancelToken
  deriving DecidableEq, Repr

/-- Occurrence `0` is the continuation, `1` the reply, `2` the timer, `3` the deadline, `4` the
supervisor's capability, `5` the resumption, `6` the timed-out resumption, `7` a cancel token. -/
def item : ℕ → Item
  | 0 => .parked
  | 1 => .reply
  | 2 => .timer
  | 3 => .deadline
  | 4 => .capability
  | 5 => .resumed
  | 6 => .timedOut
  | _ => .cancelToken

/-- The names each item carries: the continuation holds name `10`, the supervisor's capability
name `20`; the clock's items carry none. -/
def carried : Item → Finset ℕ
  | .parked => {10}
  | .capability => {20}
  | .timedOut => {10}
  | .resumed => {10}
  | _ => ∅

/-- A supervisor's timeout: take the continuation, keep the supervisor's capability, and resume it. -/
def supervisorCancel : Commit ℕ Item := ⟨{0}, {4}, {6}, []⟩

/-- **Cancellation by another process changes authority**: the supervisor's commit learns the
capability's name `20`, while the deadline arm learns only the continuation's name `10`. -/
theorem supervisor_learns_capability :
    learned item carried supervisorCancel = {10, 20} ∧
      learned item carried (deadlineArm 0 3 6 : Commit ℕ Item) = {10} := by
  refine ⟨by decide, deadline_learns_parked item carried (by rfl)⟩

/-- **A reply after the timeout is orphaned.** The continuation and the timer are present; the
clock fires the deadline; the deadline arm takes the continuation; the late reply arrives. The
run is executable; at the end the timed-out resumption and the reply are there, the continuation
is not, and the wake arm can never fire. -/
def sendReply : Commit ℕ Item := ⟨∅, ∅, {1}, []⟩

theorem late_reply_orphaned :
    Executable item {0, 2} [fireDeadline 2 3, deadlineArm 0 3 6, sendReply] ∧
      fireList {0, 2} [fireDeadline 2 3, deadlineArm 0 3 6, sendReply] = {6, 1} ∧
      ¬ Enabled item (fireList {0, 2} [fireDeadline 2 3, deadlineArm 0 3 6, sendReply])
        (wakeArm 0 1 5) := by
  refine ⟨?_, by decide, fun enabled => ?_⟩
  · refine .cons ⟨by decide, by decide, by decide, by decide, by simp [fireDeadline]⟩
      (.cons ⟨by decide, by decide, by decide, by decide, by simp [deadlineArm]⟩
        (.cons ⟨by decide, by decide, by decide, by decide, by simp [sendReply]⟩ (.nil _)))
  · have := enabled.taken_subset (show 0 ∈ (wakeArm 0 1 5 : Commit ℕ Item).taken by decide)
    revert this
    decide

/-- **Positive control: a timely reply wins.** The reply arrives first and the wake arm fires;
afterwards the clock fires the deadline, and the deadline occurrence is an orphan. Exactly one
commit of the run takes the continuation, and it is the wake arm. -/
theorem timely_reply_wins :
    Executable item {0, 2} [sendReply, wakeArm 0 1 5, fireDeadline 2 3] ∧
      fireList {0, 2} [sendReply, wakeArm 0 1 5, fireDeadline 2 3] = {5, 3} ∧
      ([sendReply, wakeArm 0 1 5, fireDeadline 2 3].filter
        fun c : Commit ℕ Item => decide (0 ∈ c.taken)).map (fun c => c.made) = [{5}] := by
  refine ⟨?_, by decide, by decide⟩
  refine .cons ⟨by decide, by decide, by decide, by decide, by simp [sendReply]⟩
    (.cons ⟨by decide, by decide, by decide, by decide, by simp [wakeArm]⟩
      (.cons ⟨by decide, by decide, by decide, by decide, by simp [fireDeadline]⟩ (.nil _)))

/-- **Cancel, wake and deadline: whichever commits first, the others are disabled.** -/
theorem cancel_first_disables :
    Enabled item {0, 1, 3, 7} (cancelArm 0 7 6 : Commit ℕ Item) ∧
      ¬ Enabled item (fire {0, 1, 3, 7} (cancelArm 0 7 6 : Commit ℕ Item)) (wakeArm 0 1 5) ∧
      ¬ Enabled item (fire {0, 1, 3, 7} (cancelArm 0 7 6 : Commit ℕ Item)) (deadlineArm 0 3 5) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by simp [cancelArm]⟩,
    fun enabled => ?_, fun enabled => ?_⟩
  · have := enabled.taken_subset (show 0 ∈ (wakeArm 0 1 5 : Commit ℕ Item).taken by decide)
    revert this; decide
  · have := enabled.taken_subset (show 0 ∈ (deadlineArm 0 3 5 : Commit ℕ Item).taken by decide)
    revert this; decide

end Controls

end Mettapedia.GSLT.Timing.TimedAwait
