/-!

This analysis concerns the historical hold policy. The simplified dispatcher
uses the all-call alternative; `SequentialTools.lean` states its current
ordered-receipt and stop contract.
# CommandHolds — what the dependency hold and the failure stop cost

A tool-using agent's model call returns a batch of commands. The host runs them in order, and
their results reach the model in its next call. The runtime modelled here (godelclaw
`mettaclaw` @ `f4893ea`; paths below are relative to that repository) adds two holds to this
loop, and a bookkeeping rule for what they withhold:

* **Dependency hold.** `needs_observation` (`src/admission_frontier.py:89-117`), called for
  every command from `reserve_command` (`src/strategy_host.py:551`). A command is held when it
  is neither an observation (`OBSERVATION_TOOLS`, `:34-44`) nor `rest`/`nop`, and some earlier
  command of the same batch has no target, a target of another kind, or the same target. Only
  file writes (`write-file`, `append-file`, `edit-file`; target: the file) and addressed sends
  (`mailbox-send`, `send-telegram-chat`; target: the address) have targets (`:103-114`). The one
  exception is a `mailbox-send` whose correlation matches that of every earlier command, all of
  them `mailbox-wait` (`:100-102`). In effect: an effect after a read is held, and an
  unclassified effect after anything is held. A held command is recorded as `COMMAND_WITHHELD`
  (`src/skills.pl:262-265`), a record that does not permit the rest of the batch.
* **Failure stop.** `run_command_list_unless_stimulus` (`src/skills.pl:110-131`) with
  `failed_command_partition` and `command_result_permits_suffix` (`:139-146`), which call
  `strategy_host.result_permits_suffix` (`src/strategy_host.py:581-609`). With the observed
  strategy on, as deployed, the first result that is not a plain success ends the batch: an
  exception or missing result, or a rendering that begins `read failed`, `read-lines failed`,
  `ls-tree failed`, `SHELL_ERROR` (every non-zero shell exit, `src/skills.pl:36-51`) and the
  like. Nothing of the remainder runs.
* **Bookkeeping.** Every proposed position whose command did not run is a `not_run` pair
  (`src/task_context.py:128`). Such pairs, and those with an exception or no result, are pending
  until a `task_resolutions` row names them (`:113`, `:204-206`). Only `task-resolve` writes such
  a row (`:182-188`); running the same command again later does not. `task-resolve` has no
  target, so the dependency hold applies to it.

`heldRun` is this rule: commands run in order; a held command and everything after it come back
to the model as not run; a failed result ends the batch after itself. `allRun` runs every command
in order and pairs each with its result, all of which the model sees in its next call. That is the
discipline of the harnesses compared, as a sequential quotient (concurrency is not modelled).
Codex 0.162 sets `parallel_tool_calls: true`, runs every emitted call (a read/write lock only
serialises tools that are not parallel-safe), collects every result in call order before the
next request, and when user input arrives mid-response lets the calls already emitted run to
completion (`core/src/tools/parallel.rs`, `turn.rs` `drain_in_flight`). opencode runs all calls
concurrently. Claude Code runs read-only tools concurrently and mutating tools sequentially, all
of them. Iter runs every call up to ten per response (`IterGrounding`). None holds an emitted call
because an earlier call of the same response was a read.

A `World` gives each command's result as a function of the commands executed before it, so the
same commands in the same order give the same results. Changes made by others between model
calls, the new-input guard, quarantined commands and blockers left by earlier turns are not
modelled; the last three can only withhold further commands. Command contents, file identities
(device and inode, or the resolved path) and addresses are abstract numbers.

Observed data from the first two hours after deployment, on two agents (not a theorem): Gödel
ran every command of the batch in 44 of 86 batches, Lila in 10 of 44; Lila had 66 commands held
against 65 run. Held commands were re-proposed on the next call nearly unchanged (reworded sends,
the same `chmod`, the same mailbox text). Lila proposed `task-resolve` 6 times; none was recorded.
A failed `read-lines` stopped the `grep-files` that was searching for the right path.

Results:
* Pure delay. `pure_delay`: if the model re-proposes whatever was held (`Reproposes`), the
  deployed rule executes exactly the proposed batch, with exactly the results of `allRun`, and
  needs `1 + stops` model calls where `allRun` needs one; no smaller number of calls finishes the
  batch. `stop_reason`: every stop is a hold or a failure stop.
* Call blow-up. `alternation_cost`: the batch `[r₁, e₁, …, rₙ, eₙ]` of reads and effects takes
  `n + 1` calls instead of one (`three_reads_three_effects`: `n = 3`).
* Injection inversion. `allCall_noninterference`: what an `allRun` call executes is fixed by the
  history before the call, whatever its reads return. `hold_opens_channel`: under the hold, one
  policy executes different effects for two different results of the same read. Both runners
  show the read result to the next call; only the hold lets it change an effect the model had
  already chosen. Under `allRun` there is no channel from a batch's read results to that batch's
  effects to close; the hold opens one. It cannot be justified as protection against malicious
  read content.
* Grounding needs no hold. `allCall_grounded`: `allRun` gives every proposed call exactly one
  result, in call order, defers nothing, and puts every result in the history of the next
  decision (S1, S2, S3 of `ContextCore`, restated for this vocabulary). `heldCall_accounts`: the
  deployed rule is not silent either; the holds add nothing to grounding.
* Bookkeeping livelock. `resolves_per_call`: at most one `task-resolve` per call takes effect;
  `heldRun_later_classified`: an unclassified command runs only as the first of its call. `pending_per_call`: every call adds each command it did not run
  to the pending set and removes at most one entry. `pending_falls_only_when_nothing_held`,
  `draining_takes_calls` (clearing `d` entries takes at least `d` calls),
  `resolve_batch_never_drains` (a call proposing `m` resolves adds `m - 1` entries and clears at
  most one: no decrease for `m ≥ 2`, growth for `m ≥ 3`), and `alternation_pending`: the
  alternating batch, run to completion, leaves `n * n` pending entries although every command
  ran (`three_pairs_run`: 9 for `n = 3`).
* Failure-stop search cost. `failure_stop_search`: with `k - 1` failing candidates before the one
  that succeeds, `allRun` returns the success in its one call, while the deployed rule under
  re-proposal runs one failing candidate per call and reaches it in call `k`. `failures_seen`:
  for every policy, a call returns at most one failure, so seeing `j` failures takes `j` calls.
* The boundary. The hold changes what executes only on runs where the model would revise the
  held command after seeing the result (`hold_opens_channel`); otherwise it is pure delay.
  `ActThenObserve.observed_value_ge_blind_value` shows that deciding after an observation never
  loses in expectation when calls are free. With a cost per call: `holdValue_eq` (expected value
  of a hold is the gain of revisions minus the cost of the extra call),
  `hold_negative_below_threshold` (a revision probability below `cost / G`, where `G` bounds the
  gain of a revision, makes the hold lose), `hold_without_revision`, `steered_revision_never_pays`
  (a revision that gains nothing, such as one steered by read content, never pays), and
  `hold_can_pay` (a frequent, valuable revision can repay the call).
* Deployed shapes, by `decide`: `query_then_send_holds_send`, `two_resolves_hold_second`,
  `failed_read_stops_search`, `disjoint_writes_both_run`, `same_file_writes_hold_second`,
  `wait_then_correlated_send_runs`, `chat_then_mailbox_holds`, and `effect_then_read_runs` (the
  hold is one-sided: a read after an effect runs).

Self-contained: no imports beyond Lean core.
-/

set_option autoImplicit false

namespace PettaClaw.CommandHolds

/-! ## 1. Commands as the host classifies them -/

/-- The host's classification of one command (`admission_frontier.py:34-44,100-114`). -/
inductive Kind where
  /-- A tool in `OBSERVATION_TOOLS`: `read-file`, `read-lines`, `ls-tree`, `grep-files`,
  `query`, `search`, `task-read`, `mailbox-read`, ... -/
  | observe
  /-- `rest` or `nop`. -/
  | idle
  /-- `write-file`, `append-file` or `edit-file`; `file` is the file identity. -/
  | write (file : Nat)
  /-- `mailbox-send` to an address; `correlation` is present when it has three arguments. -/
  | mailboxSend (to : Nat) (correlation : Option Nat)
  /-- `send-telegram-chat` to an address. -/
  | chatSend (to : Nat)
  /-- `mailbox-wait` with its correlation. Unclassified; it matters only for the exception. -/
  | mailboxWait (correlation : Nat)
  /-- `task-resolve` naming a pending call (serial, position). Unclassified. -/
  | resolve (call : Nat × Nat)
  /-- Every other command: `send`, `shell`, `remember`, `mailbox-reply`,
  `request-disposition`, ... Unclassified. -/
  | other
  deriving DecidableEq, Repr

/-- A proposed command: its content, abstracted to a number, and its classification. -/
structure Cmd where
  name : Nat
  kind : Kind
  deriving DecidableEq, Repr

inductive Channel where
  | file
  | mailbox
  | chat
  deriving DecidableEq, Repr

/-- `target` (`admission_frontier.py:104-114`): only writes and addressed sends have one. -/
def Kind.target : Kind → Option (Channel × Nat)
  | .write f => some (.file, f)
  | .mailboxSend to _ => some (.mailbox, to)
  | .chatSend to => some (.chat, to)
  | _ => none

/-- Commands the hold never applies to: observations, `rest` and `nop` (`:96`). -/
def Kind.exempt : Kind → Bool
  | .observe => true
  | .idle => true
  | _ => false

def Kind.isWaitFor (r : Nat) : Kind → Bool
  | .mailboxWait r' => r' == r
  | _ => false

/-- The one hand-written exception (`:100-102`): a correlated `mailbox-send` after nothing but
`mailbox-wait` commands with the same correlation. -/
def continuesWait (c : Cmd) (before : List Cmd) : Bool :=
  match c.kind with
  | .mailboxSend _ (some r) => before.all (fun p => p.kind.isWaitFor r)
  | _ => false

/-- An earlier command lets a targeted one share the batch only when it has a target on the
same channel with a different key. -/
def disjoint (own : Channel × Nat) : Option (Channel × Nat) → Bool
  | some (ch, k) => ch == own.1 && k != own.2
  | none => false

/-- `needs_observation command before` (`admission_frontier.py:89-117`), clause by clause. -/
def needsObservation (c : Cmd) (before : List Cmd) : Bool :=
  if before.isEmpty || c.kind.exempt || continuesWait c before then false
  else match c.kind.target with
    | none => true
    | some own => before.any (fun p => !disjoint own p.kind.target)

/-! ## 2. Results and worlds -/

/-- What an executed command returns, as `result_permits_suffix` reads it. -/
inductive Result where
  /-- Returned, and read as permitting the rest of the batch. -/
  | ok (out : Nat)
  /-- Returned with a failure rendering (`read-lines failed`, `SHELL_ERROR exit N`, ...). -/
  | failed (out : Nat)
  /-- An exception or no result; such a pair is also pending. -/
  | lost
  deriving DecidableEq, Repr

def Result.permitsSuffix : Result → Bool
  | .ok _ => true
  | _ => false

/-- Each command's result, given every command executed before it. -/
abbrev World := List Cmd → Cmd → Result

/-! ## 3. The two runners -/

/-- Every command runs, in order, and is paired with its result. `log` is what ran before this
call; `before` what ran earlier in this call. -/
def allRun (w : World) (log : List Cmd) : List Cmd → List Cmd → List (Cmd × Result)
  | _, [] => []
  | before, c :: rest => (c, w (log ++ before) c) :: allRun w log (before ++ [c]) rest

/-- The deployed rule: run in order; a held command and everything after it do not run; a result
that does not permit the suffix ends the batch after itself. Returns what ran, with results, and
the suffix that did not run. -/
def heldRun (w : World) (log : List Cmd) :
    List Cmd → List Cmd → List (Cmd × Result) × List Cmd
  | _, [] => ([], [])
  | before, c :: rest =>
    if needsObservation c before then ([], c :: rest)
    else if (w (log ++ before) c).permitsSuffix then
      ((c, w (log ++ before) c) :: (heldRun w log (before ++ [c]) rest).1,
        (heldRun w log (before ++ [c]) rest).2)
    else ([(c, w (log ++ before) c)], rest)

/-- One model call: the batch proposed, what ran with its results, and what did not run. -/
structure Call where
  proposed : List Cmd
  ran : List (Cmd × Result)
  notRun : List Cmd
  deriving DecidableEq, Repr

/-- The model's observation history: every call so far, oldest first. -/
abbrev History := List Call

/-- Every command executed so far, in order. -/
def History.log (h : History) : List Cmd := h.flatMap (fun c => c.ran.map Prod.fst)

/-- Every result so far, paired with its command. -/
def History.evidence (h : History) : List (Cmd × Result) := h.flatMap Call.ran

/-- What the last call did not run. -/
def History.held (h : History) : List Cmd :=
  match h.getLast? with
  | some c => c.notRun
  | none => []

/-- The model: a batch for every observation history. -/
abbrev Policy := History → List Cmd

def allCall (w : World) (pol : Policy) (h : History) : History :=
  h ++ [⟨pol h, allRun w h.log [] (pol h), []⟩]

def heldCall (w : World) (pol : Policy) (h : History) : History :=
  h ++ [⟨pol h, (heldRun w h.log [] (pol h)).1, (heldRun w h.log [] (pol h)).2⟩]

def run {α : Type} (step : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => run step k (step a)

/-- The stability hypothesis matching the observed re-proposals: whenever the last call held
something, the model proposes exactly that again. -/
def Reproposes (pol : Policy) : Prop := ∀ h : History, h.held ≠ [] → pol h = h.held

/-- The calls the deployed rule makes for one batch when the held suffix is re-proposed each
time (`fuel` bounds the recursion; the batch length suffices). -/
def drain (w : World) : Nat → List Cmd → List Cmd → List Call
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, log, c :: cs =>
    ⟨c :: cs, (heldRun w log [] (c :: cs)).1, (heldRun w log [] (c :: cs)).2⟩ ::
      drain w fuel (log ++ (heldRun w log [] (c :: cs)).1.map Prod.fst)
        (heldRun w log [] (c :: cs)).2

def heldCalls (w : World) (log b : List Cmd) : List Call := drain w b.length log b

/-- Stop points: calls of that schedule that ended with something held. -/
def stops (w : World) (log b : List Cmd) : Nat :=
  (heldCalls w log b).countP (fun c => !c.notRun.isEmpty)

/-! ## 4. Basic facts -/

theorem History.log_append (h : History) (c : Call) :
    (h ++ [c]).log = h.log ++ c.ran.map Prod.fst := by
  simp [History.log, List.flatMap_append]

theorem History.evidence_append (h : History) (c : Call) :
    (h ++ [c]).evidence = h.evidence ++ c.ran := by
  simp [History.evidence, List.flatMap_append]

theorem History.held_append (h : History) (c : Call) : (h ++ [c]).held = c.notRun := by
  simp [History.held, List.getLast?_append]

theorem History.held_append_list (h : History) (l : List Call) (c : Call)
    (hl : l.getLast? = some c) : (h ++ l).held = c.notRun := by
  simp [History.held, List.getLast?_append, hl]

theorem History.log_append_list (h l : History) : (h ++ l).log = h.log ++ l.log := by
  simp [History.log, List.flatMap_append]

theorem History.log_eq_evidence (h : History) : h.log = h.evidence.map Prod.fst := by
  simp [History.log, History.evidence, List.map_flatMap]

theorem allRun_cmds (w : World) (log : List Cmd) :
    ∀ (before b : List Cmd), (allRun w log before b).map Prod.fst = b := by
  intro before b
  induction b generalizing before with
  | nil => rfl
  | cons c rest ih => simp [allRun, ih]

theorem allRun_shift (w : World) :
    ∀ (b log before : List Cmd), allRun w log before b = allRun w (log ++ before) [] b := by
  intro b
  induction b with
  | nil => intro log before; rfl
  | cons c rest ih =>
    intro log before
    simp only [allRun, List.append_nil, List.nil_append]
    rw [ih log (before ++ [c]), ih (log ++ before) [c], List.append_assoc]

theorem allRun_append (w : World) (log : List Cmd) :
    ∀ (p s before : List Cmd),
      allRun w log before (p ++ s) = allRun w log before p ++ allRun w log (before ++ p) s := by
  intro p
  induction p with
  | nil => intro s before; simp [allRun]
  | cons c p ih => intro s before; simp [allRun, ih]

/-- Every proposed command either ran or is in the returned suffix, in order. -/
theorem heldRun_partition (w : World) (log : List Cmd) :
    ∀ (b before : List Cmd),
      (heldRun w log before b).1.map Prod.fst ++ (heldRun w log before b).2 = b := by
  intro b
  induction b with
  | nil => intro before; rfl
  | cons c rest ih =>
    intro before
    simp only [heldRun]
    split
    · rfl
    · split
      · simp [ih]
      · rfl

/-- What the deployed rule runs is a prefix of what `allRun` runs, with the same results. -/
theorem heldRun_allRun (w : World) (log : List Cmd) :
    ∀ (b before : List Cmd),
      allRun w log before b = (heldRun w log before b).1 ++
        allRun w log (before ++ (heldRun w log before b).1.map Prod.fst)
          (heldRun w log before b).2 := by
  intro b
  induction b with
  | nil => intro before; rfl
  | cons c rest ih =>
    intro before
    simp only [heldRun]
    split
    · simp
    · split
      · simp only [allRun, List.map_cons, List.cons_append]
        rw [ih (before ++ [c])]
        simp
      · simp [allRun]

theorem needsObservation_nil (c : Cmd) : needsObservation c [] = false := by
  simp [needsObservation]

theorem needsObservation_exempt (c : Cmd) (before : List Cmd) (h : c.kind.exempt = true) :
    needsObservation c before = false := by
  simp [needsObservation, h]

/-- An effect after a read is held, whatever its target. -/
theorem needs_after_observe (e : Cmd) (before : List Cmd) (he : e.kind.exempt = false)
    (p : Cmd) (hp : p ∈ before) (hobs : p.kind = .observe) :
    needsObservation e before = true := by
  have hne : before.isEmpty = false := by
    cases before with
    | nil => simp at hp
    | cons _ _ => rfl
  have hcw : continuesWait e before = false := by
    unfold continuesWait
    split
    · rw [List.all_eq_false]; exact ⟨p, hp, by simp [hobs, Kind.isWaitFor]⟩
    · rfl
  unfold needsObservation
  rw [hne, he, hcw]
  simp only [Bool.or_false, Bool.false_eq_true, if_false]
  split
  · rfl
  · rw [List.any_eq_true]; exact ⟨p, hp, by simp [hobs, Kind.target, disjoint]⟩

/-- An unclassified effect after anything is held. -/
theorem unclassified_held (c : Cmd) (before : List Cmd) (ht : c.kind.target = none)
    (he : c.kind.exempt = false) (hb : before ≠ []) : needsObservation c before = true := by
  have hne : before.isEmpty = false := by
    cases before with
    | nil => exact absurd rfl hb
    | cons _ _ => rfl
  have hcw : continuesWait c before = false := by
    unfold continuesWait
    split
    · next k hk => rw [hk] at ht; simp [Kind.target] at ht
    · rfl
  unfold needsObservation
  rw [hne, he, hcw, ht]
  rfl

/-- The first command of a call always runs. -/
theorem heldRun_first (w : World) (log : List Cmd) (c : Cmd) (cs : List Cmd) :
    (heldRun w log [] (c :: cs)).1 ≠ [] := by
  simp only [heldRun, needsObservation_nil, Bool.false_eq_true, if_false]
  split <;> simp

theorem heldRun_length (w : World) (log before b : List Cmd) :
    (heldRun w log before b).1.length + (heldRun w log before b).2.length = b.length := by
  have h := congrArg List.length (heldRun_partition w log b before)
  simpa using h

theorem heldRun_shorter (w : World) (log : List Cmd) (c : Cmd) (cs : List Cmd) :
    (heldRun w log [] (c :: cs)).2.length < (c :: cs).length := by
  have h1 := heldRun_length w log [] (c :: cs)
  have h2 := heldRun_first w log c cs
  have : 0 < (heldRun w log [] (c :: cs)).1.length := List.length_pos_iff.mpr h2
  omega

theorem drain_nil (w : World) (fuel : Nat) (log : List Cmd) : drain w fuel log [] = [] := by
  cases fuel <;> rfl

theorem drain_results (w : World) :
    ∀ (fuel : Nat) (log b : List Cmd), b.length ≤ fuel →
      (drain w fuel log b).flatMap Call.ran = allRun w log [] b := by
  intro fuel
  induction fuel with
  | zero =>
    intro log b hb
    have : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ fuel ih =>
    intro log b hb
    cases b with
    | nil => rfl
    | cons c cs =>
      have hs := heldRun_shorter w log c cs
      simp only [drain, List.flatMap_cons]
      rw [ih _ _ (by omega), heldRun_allRun w log (c :: cs) [], allRun_shift w _ log]
      simp

theorem drain_ran_ne (w : World) :
    ∀ (fuel : Nat) (log b : List Cmd), ∀ c ∈ drain w fuel log b, c.ran ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro log b c hc; simp [drain] at hc
  | succ fuel ih =>
    intro log b c hc
    cases b with
    | nil => simp [drain] at hc
    | cons d ds =>
      simp only [drain, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact heldRun_first w log d ds
      · exact ih _ _ c hc

theorem drain_length (w : World) :
    ∀ (fuel : Nat) (log b : List Cmd), b ≠ [] → b.length ≤ fuel →
      (drain w fuel log b).length =
        1 + (drain w fuel log b).countP (fun c => !c.notRun.isEmpty) := by
  intro fuel
  induction fuel with
  | zero => intro log b hne hb; exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hne
  | succ fuel ih =>
    intro log b hne hb
    cases b with
    | nil => exact absurd rfl hne
    | cons c cs =>
      have hs := heldRun_shorter w log c cs
      simp only [drain, List.length_cons, List.countP_cons]
      cases hr : (heldRun w log [] (c :: cs)).2 with
      | nil => simp [drain_nil]
      | cons d ds =>
        rw [hr] at hs
        have := ih (log ++ (heldRun w log [] (c :: cs)).1.map Prod.fst) (d :: ds)
          (by simp) (by simp at hs hb ⊢; omega)
        simp only [List.isEmpty_cons, Bool.not_false, if_true]
        omega

theorem drain_last (w : World) :
    ∀ (fuel : Nat) (log b : List Cmd), b ≠ [] → b.length ≤ fuel →
      ∃ c, (drain w fuel log b).getLast? = some c ∧ c.notRun = [] := by
  intro fuel
  induction fuel with
  | zero => intro log b hne hb; exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hne
  | succ fuel ih =>
    intro log b hne hb
    cases b with
    | nil => exact absurd rfl hne
    | cons c cs =>
      have hs := heldRun_shorter w log c cs
      simp only [drain]
      cases hr : (heldRun w log [] (c :: cs)).2 with
      | nil => simp [drain_nil]
      | cons d ds =>
        rw [hr] at hs
        obtain ⟨e, he, hn⟩ := ih (log ++ (heldRun w log [] (c :: cs)).1.map Prod.fst) (d :: ds)
          (by simp) (by simp at hs hb ⊢; omega)
        refine ⟨e, ?_, hn⟩
        rw [List.getLast?_cons, he]
        rfl

/-- Under re-proposal, the deployed runner makes exactly the calls of `drain`. -/
theorem run_drain (w : World) (pol : Policy) (stable : Reproposes pol) :
    ∀ (fuel : Nat) (h : History), (pol h).length ≤ fuel →
      ∀ k, k ≤ (drain w fuel h.log (pol h)).length →
        run (heldCall w pol) k h = h ++ (drain w fuel h.log (pol h)).take k := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hb k hk
    have : pol h = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this] at hk ⊢
    simp [drain] at hk
    subst hk; simp [run]
  | succ fuel ih =>
    intro h hb k hk
    cases k with
    | zero => simp [run]
    | succ k =>
      cases hp : pol h with
      | nil => rw [hp] at hk; simp [drain] at hk
      | cons c cs =>
        rw [hp] at hk hb
        have hs := heldRun_shorter w h.log c cs
        simp only [run]
        have hcall : heldCall w pol h = h ++ [⟨c :: cs, (heldRun w h.log [] (c :: cs)).1,
            (heldRun w h.log [] (c :: cs)).2⟩] := by
          simp [heldCall, hp]
        rw [hcall]
        simp only [drain, List.length_cons, List.take_succ_cons] at hk ⊢
        by_cases hr : (heldRun w h.log [] (c :: cs)).2 = []
        · rw [hr, drain_nil] at hk ⊢
          have : k = 0 := by simp at hk; omega
          subst this; simp [run]
        · let c₁ : Call := ⟨c :: cs, (heldRun w h.log [] (c :: cs)).1,
              (heldRun w h.log [] (c :: cs)).2⟩
          have hheld : (h ++ [c₁]).held = (heldRun w h.log [] (c :: cs)).2 :=
            History.held_append _ _
          have hpol := stable _ (by rw [hheld]; exact hr)
          rw [hheld] at hpol
          have hlog : (h ++ [c₁]).log = h.log ++ (heldRun w h.log [] (c :: cs)).1.map Prod.fst :=
            History.log_append h c₁
          have := ih (h ++ [c₁]) (by rw [hpol]; simp at hs hb ⊢; omega) k
            (by rw [hpol, hlog]; simpa using hk)
          rw [hpol, hlog] at this
          show run (heldCall w pol) k (h ++ [c₁]) = _
          rw [this]
          simp [c₁]

/-! ## 5. Pure delay -/

/-- If the model re-proposes whatever was held, the deployed rule executes exactly the proposed
batch with exactly the results of `allRun`, leaves nothing held, and needs `1 + stops` calls
where `allRun` needs one. Fewer calls do not finish the batch. -/
theorem pure_delay (w : World) (pol : Policy) (stable : Reproposes pol) (h : History) :
    let calls := heldCalls w h.log (pol h)
    let done := run (heldCall w pol) calls.length h
    done = h ++ calls ∧
    done.log = h.log ++ pol h ∧
    done.evidence = (run (allCall w pol) 1 h).evidence ∧
    done.held = [] ∧
    (∀ k < calls.length, (run (heldCall w pol) k h).log.length < (h.log ++ pol h).length) ∧
    (pol h ≠ [] → calls.length = 1 + stops w h.log (pol h)) := by
  intro calls done
  have hrun : ∀ k, k ≤ calls.length → run (heldCall w pol) k h = h ++ calls.take k :=
    run_drain w pol stable (pol h).length h (Nat.le_refl _)
  have hdone : done = h ++ calls := by
    simp only [done]; rw [hrun _ (Nat.le_refl _), List.take_length]
  have hres : calls.flatMap Call.ran = allRun w h.log [] (pol h) :=
    drain_results w _ _ _ (Nat.le_refl _)
  have hlog : History.log calls = pol h := by
    rw [History.log_eq_evidence]
    simp only [History.evidence]
    rw [hres, allRun_cmds]
  refine ⟨hdone, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdone, History.log_append_list, hlog]
  · rw [hdone]
    simp [run, allCall, History.evidence, List.flatMap_append, hres]
  · rw [hdone]
    by_cases hp : pol h = []
    · have hc : calls = [] := by simp only [calls, heldCalls, hp]; exact drain_nil w _ _
      rw [hc, List.append_nil]
      by_cases hh : h.held = []
      · exact hh
      · exact absurd (hp ▸ stable h hh) (Ne.symm hh)
    · obtain ⟨c, hc, hn⟩ := drain_last w (pol h).length h.log (pol h) hp (Nat.le_refl _)
      rw [History.held_append_list h calls c hc, hn]
  · intro k hk
    rw [hrun k (Nat.le_of_lt hk), History.log_append_list, List.length_append,
      List.length_append, ← hlog]
    have hsplit : History.log calls =
        History.log (calls.take k) ++ History.log (calls.drop k) := by
      rw [← History.log_append_list, List.take_append_drop]
    have hne : (calls.drop k) ≠ [] := by
      intro he; have := congrArg List.length he; simp at this; omega
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    have hc : c ∈ calls := List.mem_of_mem_drop (by rw [hcs]; exact List.mem_cons_self)
    have hran := drain_ran_ne w _ _ _ c hc
    have : 0 < (History.log (calls.drop k)).length := by
      rw [hcs]; simp [History.log]
      have := List.length_pos_iff.mpr hran; omega
    rw [hsplit, List.length_append]; omega
  · intro hp
    exact drain_length w _ _ _ hp (Nat.le_refl _)

/-- Every stop is a hold of the first command not run, or a failure of the last command run. -/
theorem stop_reason (w : World) (log : List Cmd) :
    ∀ (b before : List Cmd) (d : Cmd) (ds : List Cmd), (heldRun w log before b).2 = d :: ds →
      needsObservation d (before ++ (heldRun w log before b).1.map Prod.fst) = true ∨
      ∃ p, (heldRun w log before b).1.getLast? = some p ∧ p.2.permitsSuffix = false := by
  intro b
  induction b with
  | nil => intro before d ds h; simp [heldRun] at h
  | cons c rest ih =>
    intro before d ds h
    simp only [heldRun] at h ⊢
    split at h
    · next hn =>
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hn]
    · next hn =>
      split at h
      · next hok =>
        simp only [hn, Bool.false_eq_true, if_false, hok, if_true]
        rcases ih (before ++ [c]) d ds h with h1 | ⟨p, hp, hf⟩
        · left; simpa using h1
        · right; refine ⟨p, ?_, hf⟩
          cases hr : (heldRun w log (before ++ [c]) rest).1 with
          | nil => rw [hr] at hp; simp at hp
          | cons q qs => rw [hr] at hp; simp only [List.getLast?_cons_cons]; exact hp
      · next hok =>
        simp only [hn, Bool.false_eq_true, if_false, hok, if_false]
        right; exact ⟨_, rfl, by simpa using hok⟩

/-! ## 6. Call blow-up: reads and effects alternating -/

/-- `[r₁, e₁, …, rₙ, eₙ]`. -/
def alternate (ps : List (Cmd × Cmd)) : List Cmd := ps.flatMap (fun p => [p.1, p.2])

/-- Each pair is a read followed by an effect (anything but an observation, `rest` or `nop`). -/
def ReadThenEffect (ps : List (Cmd × Cmd)) : Prop :=
  ∀ p ∈ ps, p.1.kind = .observe ∧ p.2.kind.exempt = false

theorem alternate_cons (p : Cmd × Cmd) (ps : List (Cmd × Cmd)) :
    alternate (p :: ps) = p.1 :: p.2 :: alternate ps := by
  simp [alternate]

theorem alternate_length (ps : List (Cmd × Cmd)) : (alternate ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [alternate_cons]; simp [ih]; omega

theorem sq_succ (q : Nat) : 2 * q + 1 + q * q = (q + 1) * (q + 1) := by
  rw [Nat.add_mul, Nat.mul_add]; omega

/-- Total length of the suffixes held over a sequence of calls. -/
def heldTotal (calls : List Call) : Nat := (calls.map fun c => c.notRun.length).sum

theorem drain_alternate_tail (w : World) (ok : ∀ l c, (w l c).permitsSuffix = true) :
    ∀ (ps : List (Cmd × Cmd)), ReadThenEffect ps →
      ∀ (fuel : Nat) (log : List Cmd) (e : Cmd), (e :: alternate ps).length ≤ fuel →
        (drain w fuel log (e :: alternate ps)).length = ps.length + 1 ∧
        heldTotal (drain w fuel log (e :: alternate ps)) = ps.length * ps.length := by
  intro ps
  induction ps with
  | nil =>
    intro _ fuel log e hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp [drain, alternate, heldRun, needsObservation_nil, ok, drain_nil, heldTotal]
  | cons p ps ih =>
    intro hps fuel log e hf
    obtain ⟨r, e'⟩ := p
    have hr : r.kind = .observe := (hps (r, e') (by simp)).1
    have he' : e'.kind.exempt = false := (hps (r, e') (by simp)).2
    have hrest : ReadThenEffect ps := fun q hq => hps q (by simp [hq])
    have h1 : needsObservation r [e] = false :=
      needsObservation_exempt _ _ (by simp [hr, Kind.exempt])
    have h2 : needsObservation e' [e, r] = true := needs_after_observe e' _ he' r (by simp) hr
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hcall : heldRun w log [] (e :: alternate ((r, e') :: ps)) =
          ([(e, w log e), (r, w (log ++ [e]) r)], e' :: alternate ps) := by
        simp [alternate, heldRun, needsObservation_nil, h1, h2, ok]
      have hlen := alternate_length ps
      obtain ⟨ih1, ih2⟩ := ih hrest fuel (log ++ [e, r]) e'
        (by simp [alternate_cons] at hf ⊢; omega)
      simp only [drain.eq_3, hcall, List.map_cons, List.map_nil]
      refine ⟨by simp [ih1], ?_⟩
      simp only [heldTotal, List.map_cons, List.sum_cons, List.length_cons] at ih2 ⊢
      rw [ih2, hlen]
      have := sq_succ ps.length
      omega

/-- With every result a success, `n` read/effect pairs take `n + 1` calls under the deployed
rule (each effect is held behind the read before it), hold `n * n` commands in total along the
way, and run in one call under `allRun`. -/
theorem alternation_cost (w : World) (ok : ∀ l c, (w l c).permitsSuffix = true)
    (log : List Cmd) (ps : List (Cmd × Cmd)) (hps : ReadThenEffect ps) (hne : ps ≠ []) :
    (heldCalls w log (alternate ps)).length = ps.length + 1 ∧
    stops w log (alternate ps) = ps.length ∧
    heldTotal (heldCalls w log (alternate ps)) = ps.length * ps.length ∧
    (allRun w log [] (alternate ps)).map Prod.fst = alternate ps := by
  obtain ⟨⟨r, e⟩, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hr : r.kind = .observe := (hps (r, e) (by simp)).1
  have he : e.kind.exempt = false := (hps (r, e) (by simp)).2
  have hrest : ReadThenEffect qs := fun q hq => hps q (by simp [hq])
  have h1 : needsObservation e [r] = true := needs_after_observe e _ he r (by simp) hr
  have hb : alternate ((r, e) :: qs) = r :: e :: alternate qs := alternate_cons _ _
  have hcall : heldRun w log [] (r :: e :: alternate qs) =
      ([(r, w log r)], e :: alternate qs) := by
    simp [heldRun, needsObservation_nil, h1, ok]
  have hqs := alternate_length qs
  obtain ⟨t1, t2⟩ := drain_alternate_tail w ok qs hrest
    ((alternate qs).length + 1) (log ++ [r]) e (by simp)
  have hd : heldCalls w log (alternate ((r, e) :: qs)) =
      ⟨r :: e :: alternate qs, [(r, w log r)], e :: alternate qs⟩ ::
        drain w ((alternate qs).length + 1) (log ++ [r]) (e :: alternate qs) := by
    have hlen : (alternate ((r, e) :: qs)).length = (alternate qs).length + 1 + 1 := by
      rw [hb]; rfl
    simp only [heldCalls]
    rw [hlen]
    conv => lhs; rw [hb]
    rw [drain.eq_3, hcall]
    simp only [List.map_cons, List.map_nil]
  have hlen : (heldCalls w log (alternate ((r, e) :: qs))).length = qs.length + 2 := by
    rw [hd, List.length_cons, t1]
  refine ⟨by simpa using hlen, ?_, ?_, allRun_cmds _ _ _ _⟩
  · have := drain_length w _ log (alternate ((r, e) :: qs)) (by simp [hb]) (Nat.le_refl _)
    simp only [stops, heldCalls] at this hlen ⊢
    simp at hlen this ⊢; omega
  · rw [hd]
    simp only [heldTotal, List.map_cons, List.sum_cons, List.length_cons] at t2 ⊢
    rw [t2, hqs]
    have := sq_succ qs.length
    omega

/-! ## 7. Injection inversion -/

/-- What an `allRun` call executes is the batch chosen from the history before the call. -/
theorem allCall_log (w : World) (pol : Policy) (h : History) :
    (allCall w pol h).log = h.log ++ pol h := by
  simp [allCall, History.log_append, allRun_cmds]

/-- Noninterference: in two worlds that differ in what the batch's reads return, an `allRun`
call executes the same commands. No read result can change an effect of its own batch. -/
theorem allCall_noninterference (w w' : World) (pol : Policy) (h : History) :
    (allCall w pol h).log = (allCall w' pol h).log := by
  rw [allCall_log, allCall_log]

/-- A world in which only the read `r` has an interesting result, `x`. -/
def readWorld (r : Cmd) (x : Nat) : World := fun _ c => if c = r then .ok x else .ok 0

/-- Propose `[r, e]`; if `e` was held after `r` returned `y`, choose `e'` instead; otherwise
re-propose whatever was held. -/
def reviseOn (r e e' : Cmd) (y : Nat) : Policy := fun h =>
  match h.getLast? with
  | none => [r, e]
  | some c => if c.ran = [(r, .ok y)] ∧ c.notRun = [e] then [e'] else c.notRun

/-- The same policy in two worlds that differ only in what one read returns: `allRun` executes
the effect chosen before the read in both, the deployed rule executes `e` in one and `e'` in the
other. The hold is what lets read content choose the effect. -/
theorem hold_opens_channel (r e e' : Cmd) (x y : Nat)
    (hr : r.kind = .observe) (he : e.kind.exempt = false) (hxy : x ≠ y) :
    (run (allCall (readWorld r x) (reviseOn r e e' y)) 1 []).log = [r, e] ∧
    (run (allCall (readWorld r y) (reviseOn r e e' y)) 1 []).log = [r, e] ∧
    (run (heldCall (readWorld r x) (reviseOn r e e' y)) 2 []).log = [r, e] ∧
    (run (heldCall (readWorld r y) (reviseOn r e e' y)) 2 []).log = [r, e'] := by
  have hne : e ≠ r := by
    intro h; subst h; rw [hr] at he; simp [Kind.exempt] at he
  have h1 : needsObservation e [r] = true := needs_after_observe e _ he r (by simp) hr
  have hcall : ∀ z, heldRun (readWorld r z) [] [] [r, e] = ([(r, .ok z)], [e]) := by
    intro z; simp [heldRun, needsObservation_nil, h1, readWorld, Result.permitsSuffix]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [run]; rw [allCall_log]; simp [reviseOn, History.log]
  · simp only [run]; rw [allCall_log]; simp [reviseOn, History.log]
  · have hxy' : ¬ ([(r, Result.ok x)] = [(r, Result.ok y)]) := by simp [hxy]
    simp [run, heldCall, reviseOn, History.log, hcall, hxy', heldRun, needsObservation_nil,
      readWorld, hne, Result.permitsSuffix]
  · simp [run, heldCall, reviseOn, History.log, hcall, heldRun, needsObservation_nil,
      readWorld, Result.permitsSuffix]
    split <;> simp

/-! ## 8. Grounding without the holds -/

/-- `allRun` gives every proposed call exactly one result, in call order (S1), defers nothing
(S2), and the next decision sees the whole history with every new result (S3). -/
theorem allCall_grounded (w : World) (pol : Policy) (h : History) :
    let c : Call := ⟨pol h, allRun w h.log [] (pol h), []⟩
    allCall w pol h = h ++ [c] ∧ c.ran.map Prod.fst = c.proposed ∧ c.notRun = [] ∧
      (allCall w pol h).evidence = h.evidence ++ c.ran := by
  intro c
  exact ⟨rfl, allRun_cmds _ _ _ _, rfl, History.evidence_append _ _⟩

/-- The deployed rule accounts for every proposed call as run or not run; neither runner is
silent, so the holds add nothing to grounding. -/
theorem heldCall_accounts (w : World) (pol : Policy) (h : History) :
    (heldRun w h.log [] (pol h)).1.map Prod.fst ++ (heldRun w h.log [] (pol h)).2 = pol h :=
  heldRun_partition _ _ _ _

/-! ## 9. Bookkeeping livelock -/

/-- A call identity: (serial of the proposal, position in it). -/
abbrev CallId := Nat × Nat

/-- The pending set, and the serial of the next proposal. -/
structure Ledger where
  serial : Nat
  pending : List CallId
  deriving DecidableEq, Repr

/-- Pending identities are distinct and belong to earlier proposals. -/
def Ledger.Wf (l : Ledger) : Prop := l.pending.Nodup ∧ ∀ i ∈ l.pending, i.1 < l.serial

def lostAt (ran : List (Cmd × Result)) (i : Nat) : Bool :=
  match ran[i]? with
  | some (_, .lost) => true
  | _ => false

/-- The positions of this proposal that become pending: executed with no result, or not run. -/
def freshIds (serial : Nat) (ran : List (Cmd × Result)) (notRun : List Cmd) : List CallId :=
  ((List.range ran.length).filter (lostAt ran) ++ List.range' ran.length notRun.length).map
    (fun i => (serial, i))

/-- A `task-resolve` that returned records a resolution for the call it names. -/
def resolvedId : Cmd × Result → Option CallId
  | (⟨_, .resolve i⟩, .ok _) => some i
  | _ => none

def resolvedBy (ran : List (Cmd × Result)) : List CallId := ran.filterMap resolvedId

/-- One call's effect on the pending set (`task_context.py:99-131,182-209`): the new pending
pairs join, and every pair a resolution of this call names leaves. -/
def settle (l : Ledger) (ran : List (Cmd × Result)) (notRun : List Cmd) : Ledger :=
  ⟨l.serial + 1,
    (l.pending ++ freshIds l.serial ran notRun).filter (fun i => !(resolvedBy ran).contains i)⟩

/-- The pending set along the deployed runner. -/
def heldLedgerCall (w : World) (pol : Policy) (s : History × Ledger) : History × Ledger :=
  (heldCall w pol s.1,
    settle s.2 (heldRun w s.1.log [] (pol s.1)).1 (heldRun w s.1.log [] (pol s.1)).2)

def settleAll (l : Ledger) (calls : List Call) : Ledger :=
  calls.foldl (fun l c => settle l c.ran c.notRun) l

theorem freshIds_nodup (s : Nat) (ran : List (Cmd × Result)) (notRun : List Cmd) :
    (freshIds s ran notRun).Nodup := by
  unfold freshIds
  have base : (List.filter (lostAt ran) (List.range ran.length) ++
      List.range' ran.length notRun.length).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.Pairwise.filter _ List.nodup_range, List.nodup_range' _, ?_⟩
    intro a ha b hb
    simp only [List.mem_filter, List.mem_range] at ha
    simp only [List.mem_range'] at hb
    omega
  exact List.Pairwise.map _ (fun a b (hab : a ≠ b) h => hab (congrArg Prod.snd h)) base

theorem freshIds_serial (s : Nat) (ran : List (Cmd × Result)) (notRun : List Cmd) :
    ∀ i ∈ freshIds s ran notRun, i.1 = s := by
  intro i hi
  simp only [freshIds, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi; rfl

theorem freshIds_length (s : Nat) (ran : List (Cmd × Result)) (notRun : List Cmd) :
    notRun.length ≤ (freshIds s ran notRun).length := by
  simp [freshIds]

theorem settle_base_nodup (l : Ledger) (hl : l.Wf) (ran : List (Cmd × Result))
    (notRun : List Cmd) : (l.pending ++ freshIds l.serial ran notRun).Nodup := by
  rw [List.nodup_append]
  refine ⟨hl.1, freshIds_nodup _ _ _, ?_⟩
  intro a ha b hb hab
  have h1 := hl.2 a ha
  have h2 := freshIds_serial _ _ _ b hb
  subst hab; omega

theorem settle_wf (l : Ledger) (hl : l.Wf) (ran : List (Cmd × Result)) (notRun : List Cmd) :
    (settle l ran notRun).Wf := by
  refine ⟨List.Pairwise.filter _ (settle_base_nodup l hl ran notRun), ?_⟩
  intro i hi
  simp only [settle, List.mem_filter, List.mem_append] at hi
  rcases hi.1 with h | h
  · have := hl.2 i h; simp only [settle]; omega
  · have := freshIds_serial _ _ _ i h; simp only [settle]; omega

/-- With at most one resolution, a call removes at most one entry and adds every command it did
not run. -/
theorem settle_length (l : Ledger) (hl : l.Wf) (ran : List (Cmd × Result)) (notRun : List Cmd)
    (one : (resolvedBy ran).length ≤ 1) :
    l.pending.length + notRun.length ≤
      (settle l ran notRun).pending.length + (resolvedBy ran).length := by
  have hf := freshIds_length l.serial ran notRun
  have hnd := settle_base_nodup l hl ran notRun
  simp only [settle]
  generalize hR : resolvedBy ran = R at one ⊢
  generalize hL : l.pending ++ freshIds l.serial ran notRun = L at hnd
  have hLlen : L.length = l.pending.length + (freshIds l.serial ran notRun).length := by
    rw [← hL, List.length_append]
  match R, one with
  | [], _ =>
    have : L.filter (fun i => !([] : List CallId).contains i) = L :=
      List.filter_eq_self.mpr (by simp)
    rw [this]; simp; omega
  | [x], _ =>
    have : L.filter (fun i => !([x] : List CallId).contains i) = L.erase x := by
      rw [List.Nodup.erase_eq_filter hnd]
      apply List.filter_congr
      intro i _
      by_cases hix : i = x <;> simp [hix]
    rw [this, List.length_erase]
    split <;> simp <;> omega

theorem settle_quiet (l : Ledger) (ran : List (Cmd × Result)) (notRun : List Cmd)
    (none : resolvedBy ran = []) (kept : ∀ p ∈ ran, p.2 ≠ .lost) :
    (settle l ran notRun).pending.length = l.pending.length + notRun.length := by
  have hlost : (List.range ran.length).filter (lostAt ran) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i _
    unfold lostAt
    cases hget : ran[i]? with
    | none => simp
    | some p =>
      have hp := kept p (List.mem_of_getElem? hget)
      obtain ⟨c, r⟩ := p
      cases r <;> simp_all
  simp only [settle, none]
  rw [List.filter_eq_self.mpr (by simp)]
  simp [freshIds, hlost]

theorem settleAll_quiet (calls : List Call)
    (quiet : ∀ c ∈ calls, resolvedBy c.ran = [] ∧ ∀ p ∈ c.ran, p.2 ≠ .lost) :
    ∀ l, (settleAll l calls).pending.length = l.pending.length + heldTotal calls := by
  induction calls with
  | nil => intro l; simp [settleAll, heldTotal]
  | cons c cs ih =>
    intro l
    have := ih (fun d hd => quiet d (by simp [hd]))
    simp only [settleAll, List.foldl_cons] at this ⊢
    rw [this, settle_quiet _ _ _ (quiet c (by simp)).1 (quiet c (by simp)).2]
    simp [heldTotal]; omega

theorem heldRun_later_classified (w : World) (log : List Cmd) :
    ∀ (b before : List Cmd), before ≠ [] → ∀ p ∈ (heldRun w log before b).1,
      p.1.kind.target ≠ none ∨ p.1.kind.exempt = true := by
  intro b
  induction b with
  | nil => intro before _ p hp; simp [heldRun] at hp
  | cons c rest ih =>
    intro before hb p hp
    simp only [heldRun] at hp
    split at hp
    · simp at hp
    · next hn =>
      have hc : c.kind.target ≠ none ∨ c.kind.exempt = true := by
        by_cases ht : c.kind.target = none
        · by_cases he : c.kind.exempt = true
          · exact Or.inr he
          · have := unclassified_held c before ht (by simpa using he) hb
            simp_all
        · exact Or.inl ht
      split at hp
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hc
        · exact ih (before ++ [c]) (by simp) p hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; exact hc

theorem resolvedId_classified (p : Cmd × Result)
    (h : p.1.kind.target ≠ none ∨ p.1.kind.exempt = true) : resolvedId p = none := by
  obtain ⟨⟨n, k⟩, r⟩ := p
  cases k <;> cases r <;> simp_all [resolvedId, Kind.target, Kind.exempt]

/-- At most one `task-resolve` per call takes effect: an unclassified command runs only as the
first command of its call. -/
theorem resolves_per_call (w : World) (log b : List Cmd) :
    (resolvedBy (heldRun w log [] b).1).length ≤ 1 := by
  cases b with
  | nil => simp [heldRun, resolvedBy]
  | cons c cs =>
    simp only [heldRun, needsObservation_nil, Bool.false_eq_true, if_false]
    split
    · have hrest : resolvedBy (heldRun w log [c] cs).1 = [] := by
        unfold resolvedBy
        rw [List.filterMap_eq_nil_iff]
        intro p hp
        exact resolvedId_classified p (heldRun_later_classified w log cs _ (by simp) p hp)
      simp only [resolvedBy, List.filterMap_cons, List.nil_append, List.append_nil] at hrest ⊢
      split <;> simp [hrest]
    · simp only [resolvedBy, List.filterMap_cons, List.filterMap_nil]
      split <;> simp

/-- Every call, whatever the policy: the ledger stays well formed, each command not run joins
the pending set, and at most one entry leaves. -/
theorem pending_per_call (w : World) (pol : Policy) (s : History × Ledger) (hs : s.2.Wf) :
    (heldLedgerCall w pol s).2.Wf ∧
    s.2.pending.length + (heldRun w s.1.log [] (pol s.1)).2.length ≤
      (heldLedgerCall w pol s).2.pending.length + 1 := by
  refine ⟨settle_wf _ hs _ _, ?_⟩
  have h1 := resolves_per_call w s.1.log (pol s.1)
  have h2 := settle_length s.2 hs _ (heldRun w s.1.log [] (pol s.1)).2 h1
  simp only [heldLedgerCall]; omega

/-- The pending set shrinks only in a call that holds nothing and resolves something, and then
by exactly one. -/
theorem pending_falls_only_when_nothing_held (w : World) (pol : Policy) (s : History × Ledger)
    (hs : s.2.Wf) (fall : (heldLedgerCall w pol s).2.pending.length < s.2.pending.length) :
    (heldRun w s.1.log [] (pol s.1)).2 = [] ∧
    (heldLedgerCall w pol s).2.pending.length + 1 = s.2.pending.length ∧
    resolvedBy (heldRun w s.1.log [] (pol s.1)).1 ≠ [] := by
  have h1 := resolves_per_call w s.1.log (pol s.1)
  have h2 := settle_length s.2 hs _ (heldRun w s.1.log [] (pol s.1)).2 h1
  simp only [heldLedgerCall] at fall ⊢
  refine ⟨?_, ?_, ?_⟩
  · apply List.eq_nil_of_length_eq_zero; omega
  · omega
  · intro h; rw [h] at h2; simp at h2; omega

/-- Clearing `d` pending entries takes at least `d` model calls, for every policy. -/
theorem draining_takes_calls (w : World) (pol : Policy) :
    ∀ (k : Nat) (s : History × Ledger), s.2.Wf →
      s.2.pending.length ≤ (run (heldLedgerCall w pol) k s).2.pending.length + k := by
  intro k
  induction k with
  | zero => intro s _; simp [run]
  | succ k ih =>
    intro s hs
    obtain ⟨hwf, hle⟩ := pending_per_call w pol s hs
    have := ih (heldLedgerCall w pol s) hwf
    simp only [run]; omega

/-- A batch whose second and later commands are `task-resolve`: the first command runs, every
other is held. -/
theorem resolve_batch (w : World) (log : List Cmd) (c : Cmd) (cs : List Cmd)
    (hres : ∀ d ∈ cs, ∃ i, d.kind = .resolve i) :
    (heldRun w log [] (c :: cs)).1.length = 1 ∧ (heldRun w log [] (c :: cs)).2 = cs := by
  simp only [heldRun, needsObservation_nil, Bool.false_eq_true, if_false]
  split
  · cases cs with
    | nil => simp [heldRun]
    | cons d ds =>
      obtain ⟨i, hi⟩ := hres d (by simp)
      have : needsObservation d [c] = true :=
        unclassified_held d _ (by simp [hi, Kind.target]) (by simp [hi, Kind.exempt]) (by simp)
      simp [heldRun, this]
  · simp

/-- A call proposing `m = cs.length + 1` resolves adds `m - 1` pending entries and clears at
most one: the pending set never shrinks for `m ≥ 2` and grows for `m ≥ 3`. -/
theorem resolve_batch_never_drains (w : World) (pol : Policy) (s : History × Ledger)
    (hs : s.2.Wf) (c : Cmd) (cs : List Cmd) (hb : pol s.1 = c :: cs)
    (hres : ∀ d ∈ cs, ∃ i, d.kind = .resolve i) (two : 1 ≤ cs.length) :
    s.2.pending.length ≤ (heldLedgerCall w pol s).2.pending.length ∧
    (2 ≤ cs.length → s.2.pending.length < (heldLedgerCall w pol s).2.pending.length) := by
  have := (pending_per_call w pol s hs).2
  rw [hb, (resolve_batch w s.1.log c cs hres).2] at this
  omega

theorem heldRun_ran_from (w : World) (log : List Cmd) :
    ∀ (b before : List Cmd), ∀ p ∈ (heldRun w log before b).1,
      p.1 ∈ b ∧ ∃ l, p.2 = w l p.1 := by
  intro b
  induction b with
  | nil => intro before p hp; simp [heldRun] at hp
  | cons c rest ih =>
    intro before p hp
    simp only [heldRun] at hp
    split at hp
    · simp at hp
    · split at hp
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨List.mem_cons_self, _, rfl⟩
        · obtain ⟨h1, h2⟩ := ih _ p hp
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; exact ⟨List.mem_cons_self, _, rfl⟩

theorem drain_ran_from (w : World) :
    ∀ (fuel : Nat) (log b : List Cmd), ∀ c ∈ drain w fuel log b, ∀ p ∈ c.ran,
      p.1 ∈ b ∧ ∃ l, p.2 = w l p.1 := by
  intro fuel
  induction fuel with
  | zero => intro log b c hc; simp [drain] at hc
  | succ fuel ih =>
    intro log b c hc p hp
    cases b with
    | nil => simp [drain] at hc
    | cons d ds =>
      simp only [drain, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact heldRun_ran_from w log _ [] p hp
      · obtain ⟨h1, h2⟩ := ih _ _ c hc p hp
        refine ⟨?_, h2⟩
        have hpart := heldRun_partition w log (d :: ds) []
        rw [← hpart]
        exact List.mem_append_right _ h1

theorem run_heldCall_extends (w : World) (pol : Policy) :
    ∀ (k : Nat) (h : History), ∃ t, run (heldCall w pol) k h = h ++ t := by
  intro k
  induction k with
  | zero => intro h; exact ⟨[], by simp [run]⟩
  | succ k ih =>
    intro h
    obtain ⟨t, ht⟩ := ih (heldCall w pol h)
    refine ⟨⟨pol h, (heldRun w h.log [] (pol h)).1, (heldRun w h.log [] (pol h)).2⟩ :: t, ?_⟩
    simp only [run]
    rw [ht]
    simp [heldCall]

theorem run_ledger (w : World) (pol : Policy) :
    ∀ (k : Nat) (s : History × Ledger),
      run (heldLedgerCall w pol) k s =
        (run (heldCall w pol) k s.1,
          settleAll s.2 ((run (heldCall w pol) k s.1).drop s.1.length)) := by
  intro k
  induction k with
  | zero => intro s; simp [run, settleAll]
  | succ k ih =>
    intro s
    simp only [run]
    rw [ih]
    obtain ⟨t, ht⟩ := run_heldCall_extends w pol k (heldCall w pol s.1)
    have hc : heldCall w pol s.1 = s.1 ++ [⟨pol s.1, (heldRun w s.1.log [] (pol s.1)).1,
        (heldRun w s.1.log [] (pol s.1)).2⟩] := rfl
    refine Prod.ext rfl ?_
    show settleAll (settle s.2 (heldRun w s.1.log [] (pol s.1)).1
          (heldRun w s.1.log [] (pol s.1)).2)
        (List.drop (heldCall w pol s.1).length (run (heldCall w pol) k (heldCall w pol s.1))) =
      settleAll s.2 (List.drop s.1.length (run (heldCall w pol) k (heldCall w pol s.1)))
    rw [ht, List.drop_left, hc, List.append_assoc, List.drop_left]
    rfl

/-- Run to completion under re-proposal, a batch of `n` read/effect pairs (no resolves among
them, every result a success) executes every command and leaves `n * n` new pending entries,
each of which only a `task-resolve` clears, one per call at most. -/
theorem alternation_pending (w : World) (ok : ∀ l c, (w l c).permitsSuffix = true)
    (pol : Policy) (stable : Reproposes pol) (h : History) (l : Ledger)
    (ps : List (Cmd × Cmd)) (hps : ReadThenEffect ps) (hne : ps ≠ [])
    (hb : pol h = alternate ps) (noResolve : ∀ p ∈ ps, ∀ i, p.2.kind ≠ .resolve i) :
    let s := run (heldLedgerCall w pol) (ps.length + 1) (h, l)
    s.1.log = h.log ++ alternate ps ∧
    s.2.pending.length = l.pending.length + ps.length * ps.length := by
  intro s
  obtain ⟨c1, _, c3, _⟩ := alternation_cost w ok h.log ps hps hne
  have hpd := pure_delay w pol stable h
  simp only [hb] at hpd
  obtain ⟨hdone, hlog, _⟩ := hpd
  rw [c1] at hdone hlog
  have hs : s = (h ++ heldCalls w h.log (alternate ps),
      settleAll l (heldCalls w h.log (alternate ps))) := by
    simp only [s]
    rw [run_ledger]
    simp only
    rw [hdone, List.drop_left]
  refine ⟨by rw [hs]; simp only; rw [← hdone]; exact hlog, ?_⟩
  rw [hs]
  simp only
  rw [settleAll_quiet _ _ l, c3]
  intro c hc
  have hfrom := drain_ran_from w _ _ _ c hc
  refine ⟨?_, ?_⟩
  · unfold resolvedBy
    rw [List.filterMap_eq_nil_iff]
    intro p hp
    obtain ⟨hm, _⟩ := hfrom p hp
    obtain ⟨⟨n, k⟩, r⟩ := p
    simp only [alternate, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨q, hq, hq'⟩ := hm
    cases k with
    | resolve i =>
      rcases hq' with hq' | hq'
      · have := (hps q hq).1; rw [← hq'] at this; simp at this
      · exact absurd (by rw [← hq']) (noResolve q hq i)
    | _ => cases r <;> rfl
  · intro p hp
    obtain ⟨_, l', hl'⟩ := hfrom p hp
    intro hlost
    have := ok l' p.1
    rw [← hl', hlost] at this
    simp [Result.permitsSuffix] at this

/-! ## 10. Failure-stop search cost -/

/-- A call returns at most one failure: the first one ends it. -/
theorem failures_per_call (w : World) (log : List Cmd) :
    ∀ (b before : List Cmd),
      ((heldRun w log before b).1.filter (fun p => !p.2.permitsSuffix)).length ≤ 1 := by
  intro b
  induction b with
  | nil => intro before; simp [heldRun]
  | cons c rest ih =>
    intro before
    simp only [heldRun]
    split
    · simp
    · split
      · next hok => simp only [List.filter_cons, hok, Bool.not_true]; exact ih _
      · simp only [List.filter_cons, List.filter_nil]; split <;> simp

/-- For every policy, `k` calls return at most `k` failures. -/
theorem failures_seen (w : World) (pol : Policy) :
    ∀ (k : Nat) (h : History),
      ((run (heldCall w pol) k h).evidence.filter (fun p => !p.2.permitsSuffix)).length ≤
        (h.evidence.filter (fun p => !p.2.permitsSuffix)).length + k := by
  intro k
  induction k with
  | zero => intro h; simp [run]
  | succ k ih =>
    intro h
    have := ih (heldCall w pol h)
    have hev : (heldCall w pol h).evidence = h.evidence ++ (heldRun w h.log [] (pol h)).1 :=
      History.evidence_append _ _
    have h1 := failures_per_call w h.log (pol h) []
    rw [hev, List.filter_append, List.length_append] at this
    simp only [run]; omega

theorem drain_failing (w : World) (rest : List Cmd) :
    ∀ (fails : List Cmd) (fuel : Nat) (log : List Cmd),
      (∀ f ∈ fails, ∀ l, (w l f).permitsSuffix = false) →
      fails.length + rest.length ≤ fuel →
      History.log ((drain w fuel log (fails ++ rest)).take fails.length) = fails ∧
      (∀ c ∈ (drain w fuel log (fails ++ rest)).take fails.length, c.ran.length = 1) ∧
      (drain w fuel log (fails ++ rest)).drop fails.length =
        drain w (fuel - fails.length) (log ++ fails) rest := by
  intro fails
  induction fails with
  | nil => intro fuel log _ _; simp [History.log]
  | cons f fs ih =>
    intro fuel log hf hlen
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      have hff : (w log f).permitsSuffix = false := hf f (by simp) log
      have hcall : heldRun w log [] (f :: (fs ++ rest)) = ([(f, w log f)], fs ++ rest) := by
        simp [heldRun, needsObservation_nil, hff]
      obtain ⟨h1, h2, h3⟩ := ih fuel (log ++ [f]) (fun g hg => hf g (by simp [hg]))
        (by simp at hlen; omega)
      simp only [List.cons_append, List.length_cons, drain.eq_3, hcall, List.take_succ_cons,
        List.drop_succ_cons, List.map_cons, List.map_nil]
      refine ⟨?_, ?_, ?_⟩
      · simp only [History.log, List.flatMap_cons] at h1 ⊢
        rw [h1]; rfl
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · rfl
        · exact h2 c hc
      · rw [h3]; simp

/-- Candidates `fails` fail and `hit` succeeds. Under re-proposal the deployed rule spends one
call on each failing candidate, so the hit's result arrives in call `fails.length + 1`;
`allRun` returns it in its one call. -/
theorem failure_stop_search (w : World) (log : List Cmd) (fails more : List Cmd) (hit : Cmd)
    (failing : ∀ f ∈ fails, ∀ l, (w l f).permitsSuffix = false)
    (found : ∀ l, (w l hit).permitsSuffix = true) :
    let calls := heldCalls w log (fails ++ hit :: more)
    hit ∉ fails ∧
    History.log (calls.take fails.length) = fails ∧
    (∀ c ∈ calls.take fails.length, c.ran.length = 1) ∧
    ((calls.drop fails.length).head?.bind (fun c => c.ran.head?)) =
      some (hit, w (log ++ fails) hit) ∧
    (hit, w (log ++ fails) hit) ∈ allRun w log [] (fails ++ hit :: more) := by
  intro calls
  have hnot : hit ∉ fails := by
    intro hm; have := failing hit hm []; rw [found] at this; simp at this
  obtain ⟨h1, h2, h3⟩ := drain_failing w (hit :: more) fails (fails ++ hit :: more).length log
    failing (by simp)
  refine ⟨hnot, h1, h2, ?_, ?_⟩
  · simp only [calls, heldCalls]
    rw [h3]
    have hf : (fails ++ hit :: more).length - fails.length = more.length + 1 := by
      simp <;> omega
    rw [hf]
    simp [drain, heldRun, needsObservation_nil, found]
  · rw [allRun_append, allRun_shift w (hit :: more)]
    simp [allRun]

/-! ## 11. The boundary: what a hold is worth

One held command, one extra call. Outcomes of the read carry a weight (an unnormalised
probability), whether the model would revise the held command after seeing it, and the gain of
that revision over running the command as first chosen. Without a revision the executed command
is the same, so the gain is zero by construction; the extra call is paid on every outcome. -/

structure Outcome where
  weight : Nat
  revised : Bool
  gain : Int
  deriving DecidableEq, Repr

def totalWeight (os : List Outcome) : Nat := (os.map Outcome.weight).sum

def revisedWeight (os : List Outcome) : Nat :=
  ((os.filter Outcome.revised).map Outcome.weight).sum

def revisedGain (os : List Outcome) : Int :=
  ((os.filter Outcome.revised).map fun o => (o.weight : Int) * o.gain).sum

/-- Expected value of the hold against running the command as chosen, times total weight. -/
def holdValue (cost : Nat) (os : List Outcome) : Int :=
  (os.map fun o => (o.weight : Int) * ((if o.revised then o.gain else 0) - cost)).sum

theorem holdValue_eq (cost : Nat) (os : List Outcome) :
    holdValue cost os = revisedGain os - (cost : Int) * (totalWeight os : Int) := by
  induction os with
  | nil => simp [holdValue, revisedGain, totalWeight]
  | cons o os ih =>
    simp only [holdValue, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    cases hr : o.revised
    · simp only [revisedGain, totalWeight, List.filter_cons, hr, Bool.false_eq_true, if_false,
        List.map_cons, List.sum_cons, Int.natCast_add]
      rw [Int.mul_sub, Int.mul_add]
      simp only [Int.mul_zero, Int.zero_sub]
      rw [Int.mul_comm (o.weight : Int) (cost : Int)]
      omega
    · simp only [revisedGain, totalWeight, List.filter_cons, hr, if_true,
        List.map_cons, List.sum_cons, Int.natCast_add]
      rw [Int.mul_sub, Int.mul_add, Int.mul_comm (o.weight : Int) (cost : Int)]
      omega

theorem revisedGain_le (os : List Outcome) (G : Nat)
    (bound : ∀ o ∈ os, o.revised = true → o.gain ≤ G) :
    revisedGain os ≤ (revisedWeight os : Int) * G := by
  induction os with
  | nil => simp [revisedGain, revisedWeight]
  | cons o os ih =>
    have ih' := ih (fun q hq => bound q (by simp [hq]))
    cases hr : o.revised
    · simp only [revisedGain, revisedWeight, List.filter_cons, hr, Bool.false_eq_true, if_false]
        at ih' ⊢
      exact ih'
    · simp only [revisedGain, revisedWeight, List.filter_cons, hr, if_true, List.map_cons,
        List.sum_cons, Int.natCast_add] at ih' ⊢
      have hg := bound o (by simp) hr
      have : (o.weight : Int) * o.gain ≤ (o.weight : Int) * G :=
        Int.mul_le_mul_of_nonneg_left hg (Int.natCast_nonneg _)
      rw [Int.add_mul]
      omega

/-- If a revision gains at most `G` and the revision probability is below `cost / G`
(`revisedWeight * G < cost * totalWeight`), the hold has negative value. -/
theorem hold_negative_below_threshold (cost G : Nat) (os : List Outcome)
    (bound : ∀ o ∈ os, o.revised = true → o.gain ≤ G)
    (rare : revisedWeight os * G < cost * totalWeight os) :
    holdValue cost os < 0 := by
  rw [holdValue_eq]
  have h1 := revisedGain_le os G bound
  have h2 : ((revisedWeight os * G : Nat) : Int) < ((cost * totalWeight os : Nat) : Int) :=
    Int.ofNat_lt.mpr rare
  simp only [Int.natCast_mul] at h2
  omega

/-- Without revisions the hold is pure cost. -/
theorem hold_without_revision (cost : Nat) (os : List Outcome)
    (never : ∀ o ∈ os, o.revised = false) :
    holdValue cost os = -((cost : Int) * totalWeight os) := by
  rw [holdValue_eq]
  have : os.filter Outcome.revised = [] := List.filter_eq_nil_iff.mpr (by simp_all)
  simp [revisedGain, this]

/-- A revision that gains nothing, such as one steered by injected read content, never repays a
call with positive cost. -/
theorem steered_revision_never_pays (cost : Nat) (os : List Outcome)
    (steered : ∀ o ∈ os, o.revised = true → o.gain ≤ 0)
    (paid : 0 < cost) (weighted : 0 < totalWeight os) :
    holdValue cost os < 0 :=
  hold_negative_below_threshold cost 0 os (by simpa using steered)
    (by rw [Nat.mul_zero]; exact Nat.mul_pos paid weighted)

/-! ## 12. Deployed shapes -/

namespace Shapes

def query : Cmd := ⟨1, .observe⟩
def send : Cmd := ⟨2, .other⟩
def resolveA : Cmd := ⟨3, .resolve (0, 1)⟩
def resolveB : Cmd := ⟨4, .resolve (0, 2)⟩
def resolveC : Cmd := ⟨5, .resolve (0, 3)⟩
def readLines : Cmd := ⟨6, .observe⟩
def grepFiles : Cmd := ⟨7, .observe⟩
def writeA : Cmd := ⟨8, .write 1⟩
def writeB : Cmd := ⟨9, .write 2⟩
def waitR : Cmd := ⟨10, .mailboxWait 5⟩
def sendR : Cmd := ⟨11, .mailboxSend 3 (some 5)⟩
def chatX : Cmd := ⟨12, .chatSend 4⟩
def mailY : Cmd := ⟨13, .mailboxSend 6 none⟩

def okWorld : World := fun _ _ => .ok 0
def readLinesFails : World := fun _ c => if c = readLines then .failed 0 else .ok 0

/-- Propose `b` first, then re-propose whatever was held, then nothing. -/
def reproposeOr (b : List Cmd) : Policy := fun h =>
  if h.held = [] then (if h = [] then b else []) else h.held

def threePairs : List Cmd := alternate [(query, send), (readLines, writeA), (grepFiles, chatX)]

end Shapes

open Shapes

/-- `[query, send]`: the send is held. -/
theorem query_then_send_holds_send :
    heldRun okWorld [] [] [query, send] = ([(query, .ok 0)], [send]) := by decide

/-- `[task-resolve, task-resolve]`: the second is held. -/
theorem two_resolves_hold_second :
    heldRun okWorld [] [] [resolveA, resolveB] = ([(resolveA, .ok 0)], [resolveB]) := by decide

/-- `[read-lines (fails), grep-files]`: the search does not run. -/
theorem failed_read_stops_search :
    heldRun readLinesFails [] [] [readLines, grepFiles] =
      ([(readLines, .failed 0)], [grepFiles]) := by decide

/-- `[write-file A, write-file B]`, disjoint files: both run. -/
theorem disjoint_writes_both_run :
    heldRun okWorld [] [] [writeA, writeB] = ([(writeA, .ok 0), (writeB, .ok 0)], []) := by
  decide

/-- `[write-file A, write-file A]`: the second is held. -/
theorem same_file_writes_hold_second :
    heldRun okWorld [] [] [writeA, writeA] = ([(writeA, .ok 0)], [writeA]) := by decide

/-- `[mailbox-wait r, mailbox-send … r]`: the exception lets both run. -/
theorem wait_then_correlated_send_runs :
    heldRun okWorld [] [] [waitR, sendR] = ([(waitR, .ok 0), (sendR, .ok 0)], []) := by decide

/-- `[send-telegram-chat x, mailbox-send y]`: targets of different kinds; the second is held. -/
theorem chat_then_mailbox_holds :
    heldRun okWorld [] [] [chatX, mailY] = ([(chatX, .ok 0)], [mailY]) := by decide

/-- `[send, query]`: a read after an effect runs; the hold is one-sided. -/
theorem effect_then_read_runs :
    heldRun okWorld [] [] [send, query] = ([(send, .ok 0), (query, .ok 0)], []) := by decide

/-- Three read/effect pairs: four calls, three stops, against one call that runs all six. -/
theorem three_reads_three_effects :
    (heldCalls okWorld [] threePairs).length = 4 ∧
    stops okWorld [] threePairs = 3 ∧
    (allRun okWorld [] [] threePairs).length = 6 := by decide

/-- Three resolves against two pending entries: one is cleared, two are added. -/
theorem three_resolves_grow_pending :
    settle ⟨1, [(0, 1), (0, 2)]⟩
        (heldRun okWorld [] [] [resolveA, resolveB, resolveC]).1
        (heldRun okWorld [] [] [resolveA, resolveB, resolveC]).2 =
      ⟨2, [(0, 2), (1, 1), (1, 2)]⟩ := by decide

theorem reproposeOr_reproposes (b : List Cmd) : Reproposes (reproposeOr b) := by
  intro h hh; simp [reproposeOr, hh]

/-- The deployed runner on three pairs with re-proposal: every command runs after four calls,
not after three, and nine pending entries remain; `allRun` runs all six in one call. -/
theorem three_pairs_run :
    (run (heldLedgerCall okWorld (reproposeOr threePairs)) 4 ([], ⟨0, []⟩)).1.log =
      threePairs ∧
    (run (heldLedgerCall okWorld (reproposeOr threePairs)) 3 ([], ⟨0, []⟩)).1.held ≠ [] ∧
    (run (heldLedgerCall okWorld (reproposeOr threePairs)) 4 ([], ⟨0, []⟩)).2.pending.length =
      9 ∧
    (run (allCall okWorld (reproposeOr threePairs)) 1 []).log = threePairs := by decide

/-- A revision on half the outcomes, gaining 3, repays a call costing 1. -/
theorem hold_can_pay : holdValue 1 [⟨1, true, 3⟩, ⟨1, false, 0⟩] = 1 := by decide

/-- A revision on one outcome in ten, gaining 5, does not repay a call costing 1. -/
theorem rare_revision_loses : holdValue 1 [⟨1, true, 5⟩, ⟨9, false, 0⟩] = -5 := by decide

end PettaClaw.CommandHolds

#print axioms PettaClaw.CommandHolds.History.log_append
#print axioms PettaClaw.CommandHolds.History.evidence_append
#print axioms PettaClaw.CommandHolds.History.held_append
#print axioms PettaClaw.CommandHolds.History.held_append_list
#print axioms PettaClaw.CommandHolds.History.log_append_list
#print axioms PettaClaw.CommandHolds.History.log_eq_evidence
#print axioms PettaClaw.CommandHolds.allRun_cmds
#print axioms PettaClaw.CommandHolds.allRun_shift
#print axioms PettaClaw.CommandHolds.allRun_append
#print axioms PettaClaw.CommandHolds.heldRun_partition
#print axioms PettaClaw.CommandHolds.heldRun_allRun
#print axioms PettaClaw.CommandHolds.needsObservation_nil
#print axioms PettaClaw.CommandHolds.needsObservation_exempt
#print axioms PettaClaw.CommandHolds.needs_after_observe
#print axioms PettaClaw.CommandHolds.unclassified_held
#print axioms PettaClaw.CommandHolds.heldRun_first
#print axioms PettaClaw.CommandHolds.heldRun_length
#print axioms PettaClaw.CommandHolds.heldRun_shorter
#print axioms PettaClaw.CommandHolds.drain_nil
#print axioms PettaClaw.CommandHolds.drain_results
#print axioms PettaClaw.CommandHolds.drain_ran_ne
#print axioms PettaClaw.CommandHolds.drain_length
#print axioms PettaClaw.CommandHolds.drain_last
#print axioms PettaClaw.CommandHolds.run_drain
#print axioms PettaClaw.CommandHolds.pure_delay
#print axioms PettaClaw.CommandHolds.stop_reason
#print axioms PettaClaw.CommandHolds.alternate_cons
#print axioms PettaClaw.CommandHolds.alternate_length
#print axioms PettaClaw.CommandHolds.sq_succ
#print axioms PettaClaw.CommandHolds.drain_alternate_tail
#print axioms PettaClaw.CommandHolds.alternation_cost
#print axioms PettaClaw.CommandHolds.allCall_log
#print axioms PettaClaw.CommandHolds.allCall_noninterference
#print axioms PettaClaw.CommandHolds.hold_opens_channel
#print axioms PettaClaw.CommandHolds.allCall_grounded
#print axioms PettaClaw.CommandHolds.heldCall_accounts
#print axioms PettaClaw.CommandHolds.freshIds_nodup
#print axioms PettaClaw.CommandHolds.freshIds_serial
#print axioms PettaClaw.CommandHolds.freshIds_length
#print axioms PettaClaw.CommandHolds.settle_base_nodup
#print axioms PettaClaw.CommandHolds.settle_wf
#print axioms PettaClaw.CommandHolds.settle_length
#print axioms PettaClaw.CommandHolds.settle_quiet
#print axioms PettaClaw.CommandHolds.settleAll_quiet
#print axioms PettaClaw.CommandHolds.heldRun_later_classified
#print axioms PettaClaw.CommandHolds.resolvedId_classified
#print axioms PettaClaw.CommandHolds.resolves_per_call
#print axioms PettaClaw.CommandHolds.pending_per_call
#print axioms PettaClaw.CommandHolds.pending_falls_only_when_nothing_held
#print axioms PettaClaw.CommandHolds.draining_takes_calls
#print axioms PettaClaw.CommandHolds.resolve_batch
#print axioms PettaClaw.CommandHolds.resolve_batch_never_drains
#print axioms PettaClaw.CommandHolds.heldRun_ran_from
#print axioms PettaClaw.CommandHolds.drain_ran_from
#print axioms PettaClaw.CommandHolds.run_heldCall_extends
#print axioms PettaClaw.CommandHolds.run_ledger
#print axioms PettaClaw.CommandHolds.alternation_pending
#print axioms PettaClaw.CommandHolds.failures_per_call
#print axioms PettaClaw.CommandHolds.failures_seen
#print axioms PettaClaw.CommandHolds.drain_failing
#print axioms PettaClaw.CommandHolds.failure_stop_search
#print axioms PettaClaw.CommandHolds.holdValue_eq
#print axioms PettaClaw.CommandHolds.revisedGain_le
#print axioms PettaClaw.CommandHolds.hold_negative_below_threshold
#print axioms PettaClaw.CommandHolds.hold_without_revision
#print axioms PettaClaw.CommandHolds.steered_revision_never_pays
#print axioms PettaClaw.CommandHolds.query_then_send_holds_send
#print axioms PettaClaw.CommandHolds.two_resolves_hold_second
#print axioms PettaClaw.CommandHolds.failed_read_stops_search
#print axioms PettaClaw.CommandHolds.disjoint_writes_both_run
#print axioms PettaClaw.CommandHolds.same_file_writes_hold_second
#print axioms PettaClaw.CommandHolds.wait_then_correlated_send_runs
#print axioms PettaClaw.CommandHolds.chat_then_mailbox_holds
#print axioms PettaClaw.CommandHolds.effect_then_read_runs
#print axioms PettaClaw.CommandHolds.three_reads_three_effects
#print axioms PettaClaw.CommandHolds.three_resolves_grow_pending
#print axioms PettaClaw.CommandHolds.reproposeOr_reproposes
#print axioms PettaClaw.CommandHolds.three_pairs_run
#print axioms PettaClaw.CommandHolds.hold_can_pay
#print axioms PettaClaw.CommandHolds.rare_revision_loses
