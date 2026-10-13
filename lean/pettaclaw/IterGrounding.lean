/-!
# IterGrounding — paired results ground the loop; the broker keeps it safe

Three tool loops as small transition systems over one vocabulary:

* `iter`  — Patrick Hammer's Iter (`patham9/iter` @ `f4064d9`, `iter.py`):
  up to ten native tool calls per response (`:22`, `:286`), every one
  executed (`:298-320`), exactly one `tool` message per call carrying its
  `tool_call_id` (`:319`), appended verbatim to `experience` modulo a marked
  5000-character cut (`:317-318`); the next request is the whole experience
  plus a "continue the current task" control message (`:250`, `:275`).
  Old tool contents are cleared to a marked stub outside the last ten messages
  (`:217-225`); at 100 messages the oldest are dropped down to 80 and leading
  tool messages are removed (`:226-230`).
* `godel` — the godelclaw broker since `b7e8837`
  (godelclaw `mettaclaw` @ `59c03b7`): the effective batch
  limit is the requested one only when every command is a broker-known
  independent read, else 1 (`strategy_host.py:35-38,350-354`); the admitted
  prefix runs, the suffix is recorded once as `COMMAND_BATCH_DEFERRED` with a
  suffix receipt (`skills.pl:61-80,96-106`); a command whose reservation fails
  (`strategy_host.reserve_command`, which also checks the admission frontier,
  `:434-462`) is recorded as `COMMAND_WITHHELD` and gets no receipt
  (`skills.pl:251-254`). The next request shows the last step's records
  (`loop.metta:66-67`), a tail of 18 receipts (`effect_receipts.py:19`,
  14,000 characters, `context_sources.py:35`) and the model's past proposals
  without results.
* `hybrid` — Iter's paired transcript, godelclaw's admission gate and
  receipts, a stop rule for dependent effects, explicit `notRun` results with
  a pending entry, and a pinned originating request.

Invariant names are shared with `ContextCore` (S1 result totality, S2 no silent
deferral, S3 decide only on complete evidence, S7 compaction retention).
`EffectSafe` is the admission-side property: no executed effect depends on a
result that was produced in the same response and therefore seen by no
decision.

Results:
* Iter: `iter_S1`, `iter_S2`, `iter_S3` hold by construction;
  `iter_clean_preserves_pairing`, `iter_trim_preserves_pairing` and
  `iter_clean_keeps_last_step_verbatim` show its trimming keeps them.
  Weaknesses: `iter_runs_blind_effect`, `iter_runs_effect_after_unobserved_effect`,
  `iter_executes_precommitted_effect_wrong_somewhere` (no effect gate),
  `iter_trim_drops_request`, `iter_trim_forgets_oldest` and
  `iter_continues_without_request` (S7 fails; no record outlives the trim),
  `iter_erases_calls_beyond_cap`, `iter_S3_needs_result_preserving_transformations`.
* godelclaw: `godel_effect_safe` (for every dependency relation, given
  that its batchable reads are observations) and
  `godel_admission_respected` — its strength. Failures: `godel_S2_fails`
  (withheld command: no receipt), `godel_S3_fails` (a result the ledger holds
  is not in the view), `godel_view_has_unpaired_proposal`,
  `godel_0027_trace` (deferred write, later send claiming it, no write; the
  deferral line *was* in view), `godel_deferral_drops_out_of_view`,
  `godel_new_input_truncates_original`, `godel_prompt_overstates_limit`,
  `godel_limit_throttles_pure_reads`. Honest positive: `godel_S2_holds_when_reserved`.
* hybrid: the headline `hybrid_grounded_and_safe` (S1, S2, S3, S7,
  `EffectSafe`, admission, together, for every gate, dependency relation,
  world and proposal), `hybrid_trim_preserves`, `hybrid_invariants_forever`,
  `hybrid_nonrun_resolved_or_visible` and `hybrid_no_silent_deferral`
  (multi-step S2: a not-run call stays pending, hence visible, until a call
  with the same content executes),
  `hybrid_blind_safe_for_every_dependency`, `hybrid_dominates_godel` (never
  runs less than godelclaw when nothing fails; `hybrid_stops_reads_after_failure`
  is the trade-off when a read fails), and on the 00:27 shape
  `hybrid_0027_pending_visible`, `hybrid_0027_claim_gate_blocks`,
  `hybrid_without_claim_gate_admits_claim`.

Host assumptions: call identities are supplied by the provider (godelclaw:
turn and position); `kind` and `batchable` are trusted host classifications
(`admission_frontier.py:33-42`, `strategy_host.py:35-38`); `dep` is a host
over-approximation of "the later call needs the earlier result";
`blindDep` (every earlier result may matter) needs no trust. Claims are
declared on the command (`claims`); extracting claims from prose is out of
scope. Character budgets are modeled as record counts. Self-contained: no
imports beyond Lean core.
-/

set_option autoImplicit false

namespace IterGrounding

/-! ## 1. Vocabulary -/

/-- The broker's observation contract (`AdmissionFrontier.Kind`). -/
inductive Kind where
  | observation
  | effect
  deriving DecidableEq, Repr

def Kind.isEffect : Kind → Bool
  | .effect => true
  | .observation => false

/-- One proposed call. `id` is the call identity, `name` its content (tool and
arguments). `batchable` is membership in godelclaw's `INDEPENDENT_READS`;
`claims` lists contents this call asserts were done (a declared claim). -/
structure Cmd where
  id : Nat
  name : Nat
  kind : Kind
  batchable : Bool := false
  claims : List Nat := []
  deriving DecidableEq, Repr

/-- What the world returns for an executed call. -/
inductive Outcome where
  | ok (out : Nat)
  | error (msg : Nat)
  deriving DecidableEq, Repr

def Outcome.failed : Outcome → Bool
  | .ok _ => false
  | .error _ => true

/-- Why a call did not run. -/
inductive Reason where
  | batchLimit
  | withheld
  | dependsOnUnobserved
  | afterStop
  | overCap
  deriving DecidableEq, Repr

/-- S1 statuses. Silence is not a status. -/
inductive Status where
  | ok (out : Nat)
  | error (msg : Nat)
  | denied
  | notRun (why : Reason)
  deriving DecidableEq, Repr

def Outcome.status : Outcome → Status
  | .ok o => .ok o
  | .error m => .error m

/-- The status says the call did not execute. -/
def Status.nonRun : Status → Bool
  | .denied => true
  | .notRun _ => true
  | _ => false

def Status.isOk : Status → Bool
  | .ok _ => true
  | _ => false

theorem Outcome.status_nonRun (o : Outcome) : o.status.nonRun = false := by
  cases o <;> rfl

/-- A durable receipt. -/
structure Receipt where
  turn : Nat
  cmd : Cmd
  status : Status
  deriving DecidableEq, Repr

/-! ## 2. Paired transcripts (S1) -/

/-- Transcript items: Iter's `experience` messages. `calls` is one assistant
message with its tool calls; `stub` is a tool message whose content was
cleared and marked `[TRUNCATED]`. -/
inductive Item where
  | user (msg : Nat)
  | calls (cs : List Cmd)
  | result (id : Nat) (s : Status)
  | stub (id : Nat)
  | note (n : Nat)
  deriving Repr

/-- `chk acc t`: `acc` lists call ids still owed a result. A call message
opens a run of results which must arrive in order, carrying the calls' ids,
before any other item; a result with nothing owed is an orphan. -/
def chk : List Nat → List Item → Bool
  | [], [] => true
  | _ :: _, [] => false
  | [], .user _ :: r => chk [] r
  | [], .note _ :: r => chk [] r
  | [], .calls cs :: r => chk (cs.map Cmd.id) r
  | [], .result _ _ :: _ => false
  | [], .stub _ :: _ => false
  | i :: is, .result j _ :: r => i == j && chk is r
  | i :: is, .stub j :: r => i == j && chk is r
  | _ :: _, .user _ :: _ => false
  | _ :: _, .note _ :: _ => false
  | _ :: _, .calls _ :: _ => false

/-- S1 (result totality) as a property of a transcript: every call has
exactly one result, immediately after its call message, carrying its id, and
no result is an orphan. -/
def WellPaired (t : List Item) : Prop := chk [] t = true

def resultsOf (es : List (Cmd × Status)) : List Item :=
  es.map (fun e => .result e.1.id e.2)

/-- One response: the call message followed by its results. -/
def block (es : List (Cmd × Status)) : List Item :=
  .calls (es.map (·.1)) :: resultsOf es

theorem chk_append (u : List Item) : ∀ (t : List Item) (acc : List Nat),
    chk acc t = true → chk acc (t ++ u) = chk [] u
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [chk] at h
  | .user _ :: t, [], h => by
      simp only [List.cons_append, chk] at h ⊢; exact chk_append u t [] h
  | .note _ :: t, [], h => by
      simp only [List.cons_append, chk] at h ⊢; exact chk_append u t [] h
  | .calls _ :: t, [], h => by
      simp only [List.cons_append, chk] at h ⊢; exact chk_append u t _ h
  | .result _ _ :: _, [], h => by simp [chk] at h
  | .stub _ :: _, [], h => by simp [chk] at h
  | .result _ _ :: t, _ :: is, h => by
      simp only [chk, Bool.and_eq_true] at h
      simp only [List.cons_append, chk, h.1, chk_append u t is h.2, Bool.true_and]
  | .stub _ :: t, _ :: is, h => by
      simp only [chk, Bool.and_eq_true] at h
      simp only [List.cons_append, chk, h.1, chk_append u t is h.2, Bool.true_and]
  | .user _ :: _, _ :: _, h => by simp [chk] at h
  | .note _ :: _, _ :: _, h => by simp [chk] at h
  | .calls _ :: _, _ :: _, h => by simp [chk] at h

theorem chk_results (es : List (Cmd × Status)) :
    chk (es.map (fun e => e.1.id)) (resultsOf es) = true := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [resultsOf, chk] at ih ⊢; exact ih

theorem chk_block (es : List (Cmd × Status)) : chk [] (block es) = true := by
  have h := chk_results es
  simp only [block, chk, List.map_map]
  exact h

theorem wellPaired_append_block (t : List Item) (es : List (Cmd × Status))
    (h : WellPaired t) : WellPaired (t ++ block es) := by
  unfold WellPaired
  rw [chk_append _ t [] h]
  exact chk_block es

theorem wellPaired_append_note (t : List Item) (n : Nat) (h : WellPaired t) :
    WellPaired (t ++ [.note n]) := by
  unfold WellPaired
  rw [chk_append _ t [] h]
  rfl

theorem result_mem_block (es : List (Cmd × Status)) (e : Cmd × Status)
    (he : e ∈ es) : Item.result e.1.id e.2 ∈ block es := by
  simp only [block, resultsOf, List.mem_cons, List.mem_map]
  exact Or.inr ⟨e, he, rfl⟩

/-! ## 3. Effect safety -/

/-- `safeRun dep before ran`: no executed effect depends (per `dep c d`, "the
later `c` needs the result of the earlier `d`") on a call executed earlier in
the same response. `before` is what already ran in this response. -/
def safeRun (dep : Cmd → Cmd → Bool) : List Cmd → List Cmd → Bool
  | _, [] => true
  | before, c :: rest =>
      (!c.kind.isEffect || !before.any (dep c)) && safeRun dep (before ++ [c]) rest

def EffectSafe (dep : Cmd → Cmd → Bool) (ran : List Cmd) : Prop :=
  safeRun dep [] ran = true

/-- Every unobserved result may matter: the precommitment no-go of
`FeedbackSensitiveBatch` and `ActThenObserve`. Needs no trusted classification. -/
def blindDep : Cmd → Cmd → Bool := fun _ _ => true

/-- Only an unobserved effect blocks a later effect: the within-response
reading of `AdmissionFrontier.blocker` (`:39`), under which a missing read
does not block a mutation (`:188`). -/
def frontierDep : Cmd → Cmd → Bool := fun _ d => d.kind.isEffect

theorem safeRun_mono (dep dep' : Cmd → Cmd → Bool)
    (h : ∀ c d, dep' c d = true → dep c d = true) :
    ∀ (ran before : List Cmd), safeRun dep before ran = true →
      safeRun dep' before ran = true
  | [], _, _ => rfl
  | c :: rest, before, hs => by
      simp only [safeRun, Bool.and_eq_true] at hs ⊢
      refine ⟨?_, safeRun_mono dep dep' h rest _ hs.2⟩
      have hd := hs.1
      cases he : c.kind.isEffect
      · rfl
      · rw [he] at hd
        simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true',
          List.any_eq_false] at hd ⊢
        intro d hd' hdep
        exact hd d hd' (h c d hdep)

/-- Safety against `blindDep` implies safety against every dependency
relation, in particular the true, unknown one. -/
theorem safe_of_blind_safe (dep : Cmd → Cmd → Bool) (ran : List Cmd)
    (h : EffectSafe blindDep ran) : EffectSafe dep ran :=
  safeRun_mono blindDep dep (fun _ _ _ => rfl) ran [] h

theorem safeRun_observations (dep : Cmd → Cmd → Bool) :
    ∀ (ran before : List Cmd), (∀ c ∈ ran, c.kind = .observation) →
      safeRun dep before ran = true
  | [], _, _ => rfl
  | c :: rest, before, h => by
      have hc := h c (by simp)
      simp only [safeRun, hc, Kind.isEffect, Bool.not_false, Bool.true_or,
        Bool.true_and]
      exact safeRun_observations dep rest _ (fun d hd => h d (by simp [hd]))

theorem safeRun_short (dep : Cmd → Cmd → Bool) (ran : List Cmd)
    (h : ran.length ≤ 1) : safeRun dep [] ran = true := by
  match ran, h with
  | [], _ => rfl
  | [c], _ => simp [safeRun]

/-! ## 4. Iter -/

/-- `MAX_TOOL_CALLS` (`iter.py:22`). -/
def maxCalls : Nat := 10

/-- Iter accepts the first ten calls and executes every one (`:286`, `:298`). -/
def iterRan (ps : List Cmd) : List Cmd := ps.take maxCalls

def iterEntries (exec : Cmd → Outcome) (ps : List Cmd) : List (Cmd × Status) :=
  (iterRan ps).map (fun c => (c, (exec c).status))

/-- One Iter step: append the assistant message and one result per call. -/
def iterStep (exec : Cmd → Outcome) (t : List Item) (ps : List Cmd) : List Item :=
  t ++ block (iterEntries exec ps)

/-- The request: experience followed by the control message (`:275`). The
system prompt is omitted; transformations are the identity here. -/
def iterView (t : List Item) (control : Nat) : List Item := t ++ [.note control]

/-- The control message "[NO ADDITIONAL USER INPUT. CONTINUE THE CURRENT USER
TASK.]" (`:250`). -/
def continueTask : Nat := 0

/-- S1 for Iter: pairing is preserved and the appended items are the call
message and one result per accepted call, in order. -/
theorem iter_S1 (exec : Cmd → Outcome) (t : List Item) (ps : List Cmd)
    (h : WellPaired t) :
    WellPaired (iterStep exec t ps) ∧
      (iterStep exec t ps).drop t.length =
        .calls (iterRan ps) :: (iterRan ps).map (fun c => .result c.id (exec c).status) := by
  refine ⟨wellPaired_append_block t _ h, ?_⟩
  simp [iterStep, block, resultsOf, iterEntries, List.map_map, Function.comp_def]

/-- S2 for Iter: nothing accepted is deferred; every accepted call runs and its
status is an executor outcome. -/
theorem iter_S2 (exec : Cmd → Outcome) (ps : List Cmd) :
    (iterEntries exec ps).map (·.1) = iterRan ps ∧
      ∀ e ∈ iterEntries exec ps, e.2.nonRun = false := by
  refine ⟨by simp [iterEntries, List.map_map, Function.comp_def], ?_⟩
  intro e he
  simp only [iterEntries, List.mem_map] at he
  obtain ⟨c, _, rfl⟩ := he
  exact Outcome.status_nonRun _

/-- S3 for Iter: the next request contains the whole window, every call in it
has its result in it, and this step's results are there verbatim. -/
theorem iter_S3 (exec : Cmd → Outcome) (t : List Item) (ps : List Cmd)
    (h : WellPaired t) (n : Nat) :
    let t' := iterStep exec t ps
    WellPaired (iterView t' n) ∧ (∀ x ∈ t', x ∈ iterView t' n) ∧
      ∀ e ∈ iterEntries exec ps, Item.result e.1.id e.2 ∈ iterView t' n := by
  refine ⟨wellPaired_append_note _ n (wellPaired_append_block t _ h), ?_, ?_⟩
  · intro x hx; exact List.mem_append_left _ hx
  · intro e he
    exact List.mem_append_left _
      (List.mem_append_right _ (result_mem_block _ e he))

/-! ### Iter's trimming keeps pairing -/

def stubify : Item → Item
  | .result i _ => .stub i
  | x => x

/-- `RETURN_VALUE_PRESERVE_MESSAGES` (`:30`). -/
def preserveMessages : Nat := 10

/-- Tool contents outside the last ten messages become marked stubs
(`:217-225`; applied at bucket boundaries, modeled as always applicable). -/
def iterClean (t : List Item) : List Item :=
  (t.take (t.length - preserveMessages)).map stubify ++ t.drop (t.length - preserveMessages)

theorem chk_stubify_prefix (m : List Item) (l : List Item) :
    ∀ acc, chk acc (l.map stubify ++ m) = chk acc (l ++ m) := by
  induction l with
  | nil => intro acc; rfl
  | cons x l ih =>
      intro acc
      cases x <;> cases acc <;> simp [stubify, chk, ih]

theorem iter_clean_preserves_pairing (t : List Item) (h : WellPaired t) :
    WellPaired (iterClean t) := by
  unfold WellPaired iterClean
  rw [chk_stubify_prefix, List.take_append_drop]
  exact h

theorem mem_iterClean_of_recent (p s : List Item) (hs : s.length ≤ preserveMessages)
    (x : Item) (hx : x ∈ s) : x ∈ iterClean (p ++ s) := by
  unfold iterClean
  apply List.mem_append_right
  have hk : (p ++ s).length - preserveMessages ≤ p.length := by
    simp only [List.length_append]; omega
  rw [List.drop_append_of_le_length hk]
  exact List.mem_append_right _ hx

/-- Cleaning before the next request never touches the results of the step
just taken: a response has at most ten results. -/
theorem iter_clean_keeps_last_step_verbatim (exec : Cmd → Outcome) (t : List Item)
    (ps : List Cmd) :
    ∀ e ∈ iterEntries exec ps, Item.result e.1.id e.2 ∈ iterClean (iterStep exec t ps) := by
  intro e he
  have hlen : (resultsOf (iterEntries exec ps)).length ≤ preserveMessages := by
    simp only [resultsOf, iterEntries, iterRan, maxCalls, preserveMessages, List.length_map,
      List.length_take]
    exact Nat.min_le_left _ _
  have hsplit : iterStep exec t ps =
      (t ++ [.calls ((iterEntries exec ps).map (·.1))]) ++ resultsOf (iterEntries exec ps) := by
    simp [iterStep, block]
  rw [hsplit]
  apply mem_iterClean_of_recent _ _ hlen
  simp only [resultsOf, List.mem_map]
  exact ⟨e, he, rfl⟩

/-- `while experience[0].role == "tool"` (`:229-230`). -/
def dropLeadingResults : List Item → List Item
  | [] => []
  | .result _ _ :: r => dropLeadingResults r
  | .stub _ :: r => dropLeadingResults r
  | .user m :: r => .user m :: r
  | .calls cs :: r => .calls cs :: r
  | .note n :: r => .note n :: r

def maxExperience : Nat := 100
def retainExperience : Nat := 80

/-- `MAX_EXPERIENCE_SIZE` / `RETAIN_EXPERIENCE_SIZE` (`:24-25`, `:226-230`). -/
def iterTrim (t : List Item) : List Item :=
  dropLeadingResults
    (if maxExperience ≤ t.length then t.drop (t.length - retainExperience) else t)

theorem chk_dropLeading : ∀ (t : List Item) (acc : List Nat),
    chk acc t = true → chk [] (dropLeadingResults t) = true
  | [], _, _ => rfl
  | .result _ _ :: _, [], h => by simp [chk] at h
  | .stub _ :: _, [], h => by simp [chk] at h
  | .result _ _ :: t, _ :: is, h => by
      simp only [chk, Bool.and_eq_true] at h
      simp only [dropLeadingResults]
      exact chk_dropLeading t is h.2
  | .stub _ :: t, _ :: is, h => by
      simp only [chk, Bool.and_eq_true] at h
      simp only [dropLeadingResults]
      exact chk_dropLeading t is h.2
  | .user _ :: _, [], h => h
  | .note _ :: _, [], h => h
  | .calls _ :: _, [], h => h
  | .user _ :: _, _ :: _, h => by simp [chk] at h
  | .note _ :: _, _ :: _, h => by simp [chk] at h
  | .calls _ :: _, _ :: _, h => by simp [chk] at h

theorem chk_tail (x : Item) (t : List Item) (acc : List Nat)
    (h : chk acc (x :: t) = true) : ∃ acc', chk acc' t = true := by
  cases acc with
  | nil =>
      cases x with
      | user _ => exact ⟨[], h⟩
      | note _ => exact ⟨[], h⟩
      | calls cs => exact ⟨_, h⟩
      | result _ _ => simp [chk] at h
      | stub _ => simp [chk] at h
  | cons i is =>
      cases x with
      | result _ _ => simp only [chk, Bool.and_eq_true] at h; exact ⟨is, h.2⟩
      | stub _ => simp only [chk, Bool.and_eq_true] at h; exact ⟨is, h.2⟩
      | user _ => simp [chk] at h
      | note _ => simp [chk] at h
      | calls _ => simp [chk] at h

theorem chk_after_drop : ∀ (n : Nat) (t : List Item) (acc : List Nat),
    chk acc t = true → ∃ acc', chk acc' (t.drop n) = true
  | 0, _, acc, h => ⟨acc, h⟩
  | _ + 1, [], acc, h => ⟨acc, h⟩
  | n + 1, x :: t, _, h => by
      obtain ⟨a, ha⟩ := chk_tail x t _ h
      exact chk_after_drop n t a ha

/-- Iter's trimming never orphans a call or a result: dropping a prefix and
then the leading tool messages keeps the transcript paired. -/
theorem iter_trim_preserves_pairing (t : List Item) (h : WellPaired t) :
    WellPaired (iterTrim t) := by
  unfold iterTrim WellPaired
  split
  · obtain ⟨a, ha⟩ := chk_after_drop _ t [] h
    exact chk_dropLeading _ a ha
  · exact chk_dropLeading t [] h

/-! ### Iter's weaknesses -/

theorem mem_of_mem_dropLeading : ∀ (t : List Item) (x : Item),
    x ∈ dropLeadingResults t → x ∈ t
  | [], _, h => h
  | .result _ _ :: r, x, h => List.mem_cons_of_mem _ (mem_of_mem_dropLeading r x h)
  | .stub _ :: r, x, h => List.mem_cons_of_mem _ (mem_of_mem_dropLeading r x h)
  | .user _ :: _, _, h => h
  | .calls _ :: _, _, h => h
  | .note _ :: _, _, h => h

def isRequest (r : Nat) : Item → Bool
  | .user m => m == r
  | _ => false

/-- Iter keeps no other record: whatever is followed by 99 messages is gone
after the next trim, request or result alike. -/
theorem iter_trim_forgets_oldest (y : Item) (P : Item → Bool) (rest : List Item)
    (long : maxExperience ≤ rest.length + 1) (fresh : ∀ x ∈ rest, P x = false) :
    ∀ x ∈ iterTrim (y :: rest), P x = false := by
  intro x hx
  unfold iterTrim at hx
  have hlen : maxExperience ≤ (y :: rest).length := by simpa using long
  rw [if_pos hlen] at hx
  have hx' := mem_of_mem_dropLeading _ x hx
  have hk : (y :: rest).length - retainExperience =
      (rest.length + 1 - retainExperience - 1) + 1 := by
    simp only [List.length_cons]
    simp only [maxExperience, retainExperience] at long ⊢
    omega
  rw [hk, List.drop_succ_cons] at hx'
  exact fresh x (List.mem_of_mem_drop hx')

/-- S7 fails for Iter: once 99 messages follow the originating request, the
next trim removes it; nothing pins it. -/
theorem iter_trim_drops_request (r : Nat) (rest : List Item)
    (long : maxExperience ≤ rest.length + 1)
    (fresh : ∀ x ∈ rest, isRequest r x = false) :
    ∀ x ∈ iterTrim (.user r :: rest), isRequest r x = false :=
  iter_trim_forgets_oldest _ _ rest long fresh

/-- …and the following request still says "continue the current user task". -/
theorem iter_continues_without_request (r : Nat) (rest : List Item)
    (long : maxExperience ≤ rest.length + 1)
    (fresh : ∀ x ∈ rest, isRequest r x = false) :
    Item.note continueTask ∈ iterView (iterTrim (.user r :: rest)) continueTask ∧
      ∀ x ∈ iterView (iterTrim (.user r :: rest)) continueTask, isRequest r x = false := by
  refine ⟨by simp [iterView], ?_⟩
  intro x hx
  simp only [iterView, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact iter_trim_drops_request r rest long fresh x hx
  · rfl

def obs (i : Nat) : Cmd := { id := i, name := i, kind := .observation }
def eff (i : Nat) : Cmd := { id := i, name := i, kind := .effect }

/-- No effect gate: Iter executes an effect after a read whose result no
decision has seen (the search-then-claim shape of `ActThenObserve`). -/
theorem iter_runs_blind_effect :
    iterRan [obs 1, eff 2] = [obs 1, eff 2] ∧ safeRun blindDep [] [obs 1, eff 2] = false := by
  decide

/-- No admission frontier: Iter issues a second effect while the first is
returned but unobserved, which `AdmissionFrontier.returned_unobserved_effect_blocks`
(`:208`) forbids. -/
theorem iter_runs_effect_after_unobserved_effect :
    iterRan [eff 1, eff 2] = [eff 1, eff 2] ∧
      safeRun frontierDep [] [eff 1, eff 2] = false := by
  decide

/-- `FeedbackSensitiveBatch.no_precommitted_continuation_for_feedback_sensitive_step`
for Iter: the effect `w` is executed whatever the read returned, so if two read
outcomes require different effects, the executed one is wrong for one of them. -/
theorem iter_executes_precommitted_effect_wrong_somewhere {Ω : Type}
    (required : Ω → Nat) (a b : Ω) (differ : required a ≠ required b) (q w : Cmd) :
    w ∈ iterRan [q, w] ∧ ∃ o, required o ≠ w.name := by
  refine ⟨by simp [iterRan, maxCalls], ?_⟩
  by_cases h : required a = w.name
  · exact ⟨b, fun hb => differ (h.trans hb.symm)⟩
  · exact ⟨a, h⟩

def mentions (i : Nat) : Item → Bool
  | .calls cs => cs.any (·.id == i)
  | .result j _ => j == i
  | .stub j => j == i
  | _ => false

/-- An eleventh call is erased: the stored assistant message is rewritten to
ten calls (`:286`), so the transcript keeps neither the call nor a result. -/
theorem iter_erases_calls_beyond_cap :
    ((List.range 11).map obs).length = 11 ∧
      (iterStep (fun _ => .ok 0) [] ((List.range 11).map obs)).any (mentions 10) = false := by
  decide

/-- Iter's transformations rewrite the request arbitrarily (`:187-198`, `:276`,
`IterArchitecture.Transformation`); S3 holds only for transformations that
keep tool results. -/
theorem iter_S3_needs_result_preserving_transformations :
    ∃ (f : List Item → List Item) (t : List Item),
      WellPaired t ∧ Item.result 1 (.ok 0) ∈ t ∧ Item.result 1 (.ok 0) ∉ f (iterView t 0) :=
  ⟨fun _ => [], [.calls [obs 1], .result 1 (.ok 0)], rfl, by simp, by simp⟩

/-! ## 5. godelclaw since `b7e8837` -/

/-- The policy limit when every command is batchable (`loop_policy.metta:96-97`). -/
def requestedLimit : Nat := 5

/-- `strategy_host.batch_limit` (`:350-354`). -/
def godelLimit (ps : List Cmd) : Nat :=
  if ps.all (·.batchable) then requestedLimit else 1

def godelAdmitted (ps : List Cmd) : List Cmd := ps.take (godelLimit ps)
def godelDeferred (ps : List Cmd) : List Cmd := ps.drop (godelLimit ps)

/-- Admitted commands whose reservation succeeds run (`skills.pl:251-268`). -/
def godelRanNow (reserve : Cmd → Bool) (ps : List Cmd) : List Cmd :=
  (godelAdmitted ps).filter reserve

structure GState where
  turn : Nat := 0
  /-- `effect-receipts.jsonl`, append-only. -/
  ledger : List Receipt := []
  /-- `LAST_SKILL_USE_RESULTS`: the previous step's records. -/
  last : List (Cmd × Status) := []
  /-- `recent-proposals`: requests only, never results. Unclipped here. -/
  proposals : List Cmd := []
  /-- Ground truth, not shown to the model. -/
  executed : List Cmd := []
  deriving Repr

def godelRecords (reserve : Cmd → Bool) (exec : Cmd → Outcome) (ps : List Cmd) :
    List (Cmd × Status) :=
  (godelAdmitted ps).map (fun c => if reserve c then (c, (exec c).status) else (c, .notRun .withheld)) ++
    (godelDeferred ps).map (fun c => (c, .notRun .batchLimit))

/-- Executed commands get a returned receipt; the deferred suffix gets its
suffix receipt (`skills.pl:102-106`); withheld commands get none (`:251-254`). -/
def godelReceipts (reserve : Cmd → Bool) (exec : Cmd → Outcome) (s : GState)
    (ps : List Cmd) : List Receipt :=
  (godelRanNow reserve ps).map (fun c => ⟨s.turn, c, (exec c).status⟩) ++
    (godelDeferred ps).map (fun c => ⟨s.turn, c, .notRun .batchLimit⟩)

def godelStep (reserve : Cmd → Bool) (exec : Cmd → Outcome) (s : GState) (ps : List Cmd) :
    GState :=
  { turn := s.turn + 1
    ledger := s.ledger ++ godelReceipts reserve exec s ps
    last := godelRecords reserve exec ps
    proposals := s.proposals ++ ps
    executed := s.executed ++ godelRanNow reserve ps }

def godelRun (reserve : Cmd → Bool) (exec : Cmd → Outcome) (s : GState)
    (pss : List (List Cmd)) : GState :=
  pss.foldl (godelStep reserve exec) s

/-- The last `n` items. -/
def lastN {α : Type} (n : Nat) (l : List α) : List α := l.drop (l.length - n)

/-- `effect_receipts._VIEW_RECORDS` (`:19`). The 14,000-character tail
(`context_sources.py:35`) is tighter: two to four results in practice. -/
def receiptWindow : Nat := 18

structure GView where
  last : List (Cmd × Status)
  receipts : List Receipt
  proposals : List Cmd

def gview (s : GState) : GView := ⟨s.last, lastN receiptWindow s.ledger, s.proposals⟩

/-- The view holds an executed result for call `i`. -/
def GView.hasResult (v : GView) (i : Nat) : Bool :=
  v.last.any (fun r => r.1.id == i && !r.2.nonRun) ||
    v.receipts.any (fun r => r.cmd.id == i && !r.status.nonRun)

/-- The view holds any record (result or non-run) for call `i`. -/
def GView.hasRecord (v : GView) (i : Nat) : Bool :=
  v.last.any (fun r => r.1.id == i) || v.receipts.any (fun r => r.cmd.id == i)

def ledgerHasResult (L : List Receipt) (i : Nat) : Bool :=
  L.any (fun r => r.cmd.id == i && !r.status.nonRun)

/-- External S2 for one step, both clauses: every proposed call executed, or
it has an explicit non-run record in the next view *and* a ledger entry. -/
def stepS2 (proposed ranNow : List Cmd) (records : List (Cmd × Status))
    (receipts : List Receipt) : Bool :=
  proposed.all fun c => ranNow.any (·.id == c.id) ||
    (records.any (fun r => r.1.id == c.id && r.2.nonRun) &&
      receipts.any (fun r => r.cmd.id == c.id && r.status.nonRun))

/-! ### Strength: deferral never breaks admission or effect safety -/

/-- Any batch containing a command outside `INDEPENDENT_READS` runs at most one
command. -/
theorem godel_runs_at_most_one (reserve : Cmd → Bool) (ps : List Cmd)
    (h : ps.all (·.batchable) = false) : (godelRanNow reserve ps).length ≤ 1 := by
  unfold godelRanNow godelAdmitted godelLimit
  rw [if_neg (by simp [h])]
  exact Nat.le_trans (List.length_filter_le _ _)
    (by rw [List.length_take]; exact Nat.min_le_left _ _)

/-- godelclaw is effect safe for *every* dependency relation, assuming its
batchable reads are observations (`INDEPENDENT_READS` "only inspect host state",
`strategy_host.py:33-34`). -/
theorem godel_effect_safe (reserve : Cmd → Bool) (dep : Cmd → Cmd → Bool) (ps : List Cmd)
    (readsOnly : ∀ c ∈ ps, c.batchable = true → c.kind = .observation) :
    EffectSafe dep (godelRanNow reserve ps) := by
  unfold EffectSafe
  by_cases h : ps.all (·.batchable) = true
  · apply safeRun_observations
    intro c hc
    simp only [godelRanNow, godelAdmitted, List.mem_filter] at hc
    have hps := List.mem_of_mem_take hc.1
    exact readsOnly c hps (List.all_eq_true.mp h c hps)
  · exact safeRun_short dep _ (godel_runs_at_most_one reserve ps (by simpa using h))

/-- Every command that runs passed the broker's reservation, which includes the
admission frontier (`strategy_host.py:449-453`). -/
theorem godel_admission_respected (reserve : Cmd → Bool) (ps : List Cmd) :
    ∀ c ∈ godelRanNow reserve ps, reserve c = true := by
  intro c hc
  simp only [godelRanNow, List.mem_filter] at hc
  exact hc.2

/-! ### Failures -/

/-- The 00:25 and 01:00 traces were all `query`, `ls-tree`, `mailbox-status`,
`tmux-peek`: observations (`admission_frontier.py:33-42`) but not batchable. -/
def lsTree : Cmd := { id := 1, name := 201, kind := .observation }
def mailboxStatus : Cmd := { id := 2, name := 202, kind := .observation }
def queryA : Cmd := { id := 3, name := 203, kind := .observation }

/-- The prompt states the policy limit ("at most 5 command(s)",
`loop.metta:51-53`); the effective limit is applied afterwards. -/
def promptStatedLimit : Nat := requestedLimit

theorem godel_prompt_overstates_limit :
    promptStatedLimit = 5 ∧ godelLimit [lsTree, mailboxStatus, queryA] = 1 := by
  decide

/-- Turn 1308: a batch of three reads runs one; the hybrid runs all three
(`hybrid_runs_all_reads_1308`). -/
theorem godel_limit_throttles_pure_reads :
    godelRanNow (fun _ => true) [lsTree, mailboxStatus, queryA] = [lsTree] := by
  decide

/-- S2 fails: a command whose reservation fails (turn 1314's `tmux-peek`
after new input) is not executed and gets no effect receipt. Its
`COMMAND_WITHHELD` text is in the next view only, and inside the batch's
strategy-ledger payload string (`strategy_host.py:480-483`,
`observed_strategy.py:454-464`), which no later prompt shows unless the model
pages `command-receipts`; there is no per-call entry. -/
theorem godel_S2_fails :
    let peek : Cmd := { id := 6, name := 206, kind := .observation }
    stepS2 [peek] (godelRanNow (fun _ => false) [peek])
      (godelRecords (fun _ => false) (fun _ => .ok 0) [peek])
      (godelReceipts (fun _ => false) (fun _ => .ok 0) {} [peek]) = false := by
  decide

/-- Honest positive: a pure deferral is recorded once, in the next view and in
the ledger. The failure is what happens to that record afterwards. -/
theorem godel_S2_holds_when_reserved (exec : Cmd → Outcome) (s : GState) (ps : List Cmd) :
    stepS2 ps (godelRanNow (fun _ => true) ps) (godelRecords (fun _ => true) exec ps)
      (godelReceipts (fun _ => true) exec s ps) = true := by
  unfold stepS2
  rw [List.all_eq_true]
  intro c hc
  rw [← List.take_append_drop (godelLimit ps) ps, List.mem_append] at hc
  rcases hc with hc | hc
  · have : (godelRanNow (fun _ => true) ps).any (·.id == c.id) = true := by
      rw [List.any_eq_true]
      exact ⟨c, by simpa [godelRanNow, godelAdmitted] using hc, by simp⟩
    simp [this]
  · have h1 : (godelRecords (fun _ => true) exec ps).any
        (fun r => r.1.id == c.id && r.2.nonRun) = true := by
      rw [List.any_eq_true]
      refine ⟨(c, .notRun .batchLimit), ?_, by simp [Status.nonRun]⟩
      simp only [godelRecords, List.mem_append, List.mem_map]
      exact Or.inr ⟨c, hc, rfl⟩
    have h2 : (godelReceipts (fun _ => true) exec s ps).any
        (fun r => r.cmd.id == c.id && r.status.nonRun) = true := by
      rw [List.any_eq_true]
      refine ⟨⟨s.turn, c, .notRun .batchLimit⟩, ?_, by simp [Status.nonRun]⟩
      simp only [godelReceipts, List.mem_append, List.mem_map]
      exact Or.inr ⟨c, hc, rfl⟩
    simp [h1, h2]

def readSteps (n : Nat) : List (List Cmd) := (List.range n).map (fun i => [obs i])

/-- S3 fails: after nineteen single-result steps the first result is still in
the ledger but in neither the last results nor the receipts tail. -/
theorem godel_S3_fails :
    let s := godelRun (fun _ => true) (fun c => .ok c.id) {} (readSteps 19)
    ledgerHasResult s.ledger 0 = true ∧ (gview s).hasResult 0 = false := by
  decide

/-- The view shows a proposal with no record at all: turn 1314's withheld
`tmux-peek`, two steps later. -/
theorem godel_view_has_unpaired_proposal :
    let peek : Cmd := { id := 6, name := 206, kind := .observation }
    let s := godelRun (fun c => c.id != 6) (fun _ => .ok 0) {} [[peek], [obs 7]]
    (gview s).proposals.any (·.id == 6) = true ∧ (gview s).hasRecord 6 = false := by
  decide

/-! ### The 10-13 00:25–00:27 failure, isomorphic -/

def q1 : Cmd := { id := 11, name := 301, kind := .observation }
/-- `write-file` into the sibling's mailbox inbox. -/
def wr : Cmd := { id := 12, name := 302, kind := .effect }
def s1 : Cmd := { id := 13, name := 303, kind := .effect }
def q2 : Cmd := { id := 14, name := 304, kind := .observation }
def rest1 : Cmd := { id := 15, name := 305, kind := .effect }
def peek : Cmd := { id := 16, name := 306, kind := .observation }
def q3 : Cmd := { id := 17, name := 304, kind := .observation }
/-- `send` asserting the note had been placed: it claims `wr`'s content. -/
def s2 : Cmd := { id := 18, name := 308, kind := .effect, claims := [302] }
def q4 : Cmd := { id := 19, name := 304, kind := .observation }
def rest2 : Cmd := { id := 20, name := 305, kind := .effect }

/-- Turns 1311 (query, write-file, send), 1312 (query, rest), 1314
(tmux-peek withheld after new input, query), before 1318. -/
def before0027 : List (List Cmd) := [[q1, wr, s1], [q2, rest1], [peek, q3]]
def claim0027 : List Cmd := [s2, q4, rest2]

/-- New input arrived before turn 1314; the reservation of `tmux-peek` failed. -/
def reserve0027 (c : Cmd) : Bool := c.id != 16

/-- The 00:27 failure: the write never runs, a send claiming it runs, and no
receipt shows the write returned. The deferral line *is* in the view at the
claim: the evidence was present, not absent; nothing gated the claim and
nothing kept the write as an open obligation. -/
theorem godel_0027_trace :
    let pre := godelRun reserve0027 (fun _ => .ok 0) {} before0027
    let post := godelStep reserve0027 (fun _ => .ok 0) pre claim0027
    post.executed.any (·.id == 18) = true ∧ s2.claims = [wr.name] ∧
      post.executed.any (·.name == wr.name) = false ∧
      post.ledger.any (fun r => r.cmd.name == wr.name && r.status.isOk) = false ∧
      (gview pre).receipts.any (fun r => r.cmd.id == 12 && r.status == .notRun .batchLimit) = true ∧
      post.ledger.any (·.cmd.id == 16) = false := by
  decide

/-- Retention fails: eighteen receipts later the deferred write has no record
in the view, never ran, and only the model's own proposal remains. -/
theorem godel_deferral_drops_out_of_view :
    let s := godelRun (fun _ => true) (fun _ => .ok 0) {}
      ([[q1, wr, s1]] ++ (List.range 18).map (fun i => [obs (100 + i)]))
    s.executed.any (·.name == wr.name) = false ∧ (gview s).hasRecord wr.id = false ∧
      (gview s).proposals.any (·.id == wr.id) = true := by
  decide

/-- S7 fails for godelclaw too: on new input the focus moves to the newest
request and every other active request is shown as its first 180 characters
(`strategy_host.py:166-172`, `observed_strategy.py:304`). -/
def summaryChars : Nat := 180

def godelRequestView (older : List (List Nat)) (newest : List Nat) : List (List Nat) :=
  older.map (·.take summaryChars) ++ [newest]

theorem godel_new_input_truncates_original (orig newer : List Nat)
    (long : summaryChars < orig.length) (differ : orig ≠ newer) :
    orig ∉ godelRequestView [orig] newer := by
  simp only [godelRequestView, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, not_or]
  refine ⟨fun h => ?_, differ, by simp⟩
  have := congrArg List.length h
  simp only [List.length_take] at this
  omega

/-! ## 6. The hybrid -/

structure Config where
  /-- Admission over the current ledger: godelclaw's reservation and the
  admission frontier, optionally a claim gate. -/
  admit : List Receipt → Cmd → Bool
  /-- Host over-approximation of "the later call needs the earlier result". -/
  dep : Cmd → Cmd → Bool
  /-- The world. -/
  exec : Cmd → Outcome

structure HState where
  /-- The originating request, pinned. -/
  request : Nat
  transcript : List Item
  ledger : List Receipt
  /-- Calls that did not run and are owed a decision. -/
  pending : List Cmd
  /-- Ground truth. -/
  executed : List Cmd
  turn : Nat

def stopAll (l : List Cmd) : List (Cmd × Status × Bool) :=
  l.map (fun d => (d, .notRun .afterStop, false))

def overCap (l : List Cmd) : List (Cmd × Status × Bool) :=
  l.map (fun d => (d, .notRun .overCap, false))

/-- Run in order and pair every call: stop at an effect that depends on a
result produced earlier in this response, at a denial, or after a failure.
Each entry is (call, status, executed). The gate sees the ledger as it grows. -/
def hrun (cfg : Config) (turn : Nat) :
    List Receipt → List Cmd → List Cmd → List (Cmd × Status × Bool)
  | _, _, [] => []
  | L, before, c :: rest =>
      if c.kind.isEffect && before.any (cfg.dep c) then
        (c, .notRun .dependsOnUnobserved, false) :: stopAll rest
      else if cfg.admit L c then
        if (cfg.exec c).failed then
          (c, (cfg.exec c).status, true) :: stopAll rest
        else
          (c, (cfg.exec c).status, true) ::
            hrun cfg turn (L ++ [⟨turn, c, (cfg.exec c).status⟩]) (before ++ [c]) rest
      else
        (c, .denied, false) :: stopAll rest

/-- Every proposed call gets an entry. Dependency and outcome boundaries,
not a numeric count, determine which calls execute. -/
def hEntries (cfg : Config) (s : HState) (ps : List Cmd) : List (Cmd × Status × Bool) :=
  hrun cfg s.turn s.ledger [] ps

def hRan (cfg : Config) (s : HState) (ps : List Cmd) : List Cmd :=
  ((hEntries cfg s ps).filter (·.2.2)).map (·.1)

def hOwed (cfg : Config) (s : HState) (ps : List Cmd) : List Cmd :=
  ((hEntries cfg s ps).filter (fun e => !e.2.2)).map (·.1)

def hStep (cfg : Config) (s : HState) (ps : List Cmd) : HState :=
  let es := hEntries cfg s ps
  { request := s.request
    transcript := s.transcript ++ block (es.map (fun e => (e.1, e.2.1)))
    ledger := s.ledger ++ es.map (fun e => ⟨s.turn, e.1, e.2.1⟩)
    pending := s.pending ++ hOwed cfg s ps
    executed := s.executed ++ hRan cfg s ps
    turn := s.turn + 1 }

/-- Iter's trim, applied to the transcript only. -/
def hTrim (s : HState) : HState := { s with transcript := iterTrim s.transcript }

structure HView where
  request : Nat
  pending : List Cmd
  transcript : List Item

def hview (s : HState) : HView := ⟨s.request, s.pending, s.transcript⟩

/-! ### Lemmas about one response -/

theorem stopAll_fst (l : List Cmd) : (stopAll l).map (·.1) = l := by
  simp [stopAll, List.map_map, Function.comp_def]

theorem stopAll_filter (l : List Cmd) : (stopAll l).filter (·.2.2) = [] := by
  simp [stopAll, List.filter_map, Function.comp_def]

theorem overCap_filter (l : List Cmd) : (overCap l).filter (·.2.2) = [] := by
  simp [overCap, List.filter_map, Function.comp_def]

theorem not_and_bool (a b : Bool) (h : ¬ (a && b) = true) : (!a || !b) = true := by
  cases a <;> cases b <;> simp_all

theorem hrun_fst (cfg : Config) (turn : Nat) :
    ∀ (L : List Receipt) (before l : List Cmd), (hrun cfg turn L before l).map (·.1) = l
  | _, _, [] => rfl
  | L, before, c :: rest => by
      unfold hrun
      split
      · simp [stopAll_fst]
      · split
        · split
          · simp [stopAll_fst]
          · simp [hrun_fst cfg turn _ _ rest]
        · simp [stopAll_fst]

/-- Truthful statuses: an entry is executed exactly when its status is an
executor outcome. -/
theorem hrun_truthful (cfg : Config) (turn : Nat) :
    ∀ (L : List Receipt) (before l : List Cmd), ∀ e ∈ hrun cfg turn L before l,
      (e.2.2 = true ∧ e.2.1.nonRun = false) ∨ (e.2.2 = false ∧ e.2.1.nonRun = true)
  | _, _, [], e, he => by simp [hrun] at he
  | L, before, c :: rest, e, he => by
      have stop : ∀ e ∈ stopAll rest,
          (e.2.2 = true ∧ e.2.1.nonRun = false) ∨ (e.2.2 = false ∧ e.2.1.nonRun = true) := by
        intro e he
        simp only [stopAll, List.mem_map] at he
        obtain ⟨d, _, rfl⟩ := he
        exact Or.inr ⟨rfl, rfl⟩
      unfold hrun at he
      split at he
      · rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr ⟨rfl, rfl⟩
        · exact stop e he
      · split at he
        · split at he
          · rcases List.mem_cons.mp he with rfl | he
            · exact Or.inl ⟨rfl, Outcome.status_nonRun _⟩
            · exact stop e he
          · rcases List.mem_cons.mp he with rfl | he
            · exact Or.inl ⟨rfl, Outcome.status_nonRun _⟩
            · exact hrun_truthful cfg turn _ _ rest e he
        · rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr ⟨rfl, rfl⟩
          · exact stop e he

/-- Effect safety of one response, for the configured dependency relation. -/
theorem hrun_safe (cfg : Config) (turn : Nat) :
    ∀ (L : List Receipt) (before l : List Cmd),
      safeRun cfg.dep before (((hrun cfg turn L before l).filter (·.2.2)).map (·.1)) = true
  | _, _, [] => rfl
  | L, before, c :: rest => by
      unfold hrun
      split
      · simp [stopAll_filter, safeRun]
      · rename_i hdep
        have hc := not_and_bool _ _ hdep
        split
        · split
          · simp [stopAll_filter, safeRun, hc]
          · simp only [List.filter_cons, List.map_cons, ite_true, safeRun, hc, Bool.true_and]
            exact hrun_safe cfg turn _ _ rest
        · simp [stopAll_filter, safeRun]

/-- Admission: every executed call passed the gate on a ledger that extends the
ledger the response started from. -/
theorem hrun_admitted (cfg : Config) (turn : Nat) :
    ∀ (L : List Receipt) (before l : List Cmd), ∀ e ∈ hrun cfg turn L before l,
      e.2.2 = true → ∃ L', L <+: L' ∧ cfg.admit L' e.1 = true
  | _, _, [], e, he, _ => by simp [hrun] at he
  | L, before, c :: rest, e, he, hx => by
      have stop : ∀ e ∈ stopAll rest, e.2.2 = false := by
        intro e he
        simp only [stopAll, List.mem_map] at he
        obtain ⟨d, _, rfl⟩ := he
        rfl
      unfold hrun at he
      split at he
      · rcases List.mem_cons.mp he with rfl | he
        · simp at hx
        · simp [stop e he] at hx
      · split at he
        · rename_i hadm
          split at he
          · rcases List.mem_cons.mp he with rfl | he
            · exact ⟨L, List.prefix_refl L, hadm⟩
            · simp [stop e he] at hx
          · rcases List.mem_cons.mp he with rfl | he
            · exact ⟨L, List.prefix_refl L, hadm⟩
            · obtain ⟨L', hp, ha⟩ := hrun_admitted cfg turn _ _ rest e he hx
              exact ⟨L', List.IsPrefix.trans (List.prefix_append L _) hp, ha⟩
        · rcases List.mem_cons.mp he with rfl | he
          · simp at hx
          · simp [stop e he] at hx

theorem hEntries_fst (cfg : Config) (s : HState) (ps : List Cmd) :
    (hEntries cfg s ps).map (·.1) = ps := by
  exact hrun_fst cfg s.turn s.ledger [] ps

theorem hRan_eq (cfg : Config) (s : HState) (ps : List Cmd) :
    hRan cfg s ps = ((hrun cfg s.turn s.ledger [] ps).filter (·.2.2)).map (·.1) := rfl

theorem hEntries_truthful (cfg : Config) (s : HState) (ps : List Cmd) :
    ∀ e ∈ hEntries cfg s ps,
      (e.2.2 = true ∧ e.2.1.nonRun = false) ∨ (e.2.2 = false ∧ e.2.1.nonRun = true) := by
  exact hrun_truthful cfg s.turn s.ledger [] ps

/-! ### The headline -/

/-- **Headline.** For every admission gate, dependency relation, world, model
proposal and paired starting state, one hybrid step satisfies together:

* S1: the transcript stays paired, and the step's call message lists every
  proposed call, each followed by exactly one result carrying its id;
* S2: each proposed call either executed (its status is an executor outcome)
  or carries an explicit `denied`/`notRun` status, a durable receipt and a
  pending entry;
* S3: the next view contains the whole window, in particular this step's
  results;
* S7: the originating request is in the next view;
* `EffectSafe`: no executed effect depends on a result produced earlier in the
  same response;
* admission: every executed call passed the gate on the current ledger. -/
theorem hybrid_grounded_and_safe (cfg : Config) (s : HState) (ps : List Cmd)
    (paired : WellPaired s.transcript) :
    let s' := hStep cfg s ps
    let es := hEntries cfg s ps
    (WellPaired s'.transcript ∧
      s'.transcript.drop s.transcript.length = block (es.map (fun e => (e.1, e.2.1))) ∧
      es.map (·.1) = ps) ∧
    (∀ e ∈ es, Receipt.mk s.turn e.1 e.2.1 ∈ s'.ledger ∧
      ((e.2.2 = true ∧ e.2.1.nonRun = false) ∨
        (e.2.2 = false ∧ e.2.1.nonRun = true ∧ e.1 ∈ s'.pending))) ∧
    ((hview s').transcript = s'.transcript ∧
      ∀ e ∈ es, Item.result e.1.id e.2.1 ∈ (hview s').transcript) ∧
    (hview s').request = s.request ∧
    EffectSafe cfg.dep (hRan cfg s ps) ∧
    (∀ e ∈ es, e.2.2 = true → ∃ L, s.ledger <+: L ∧ cfg.admit L e.1 = true) := by
  refine ⟨⟨wellPaired_append_block _ _ paired, by simp [hStep], hEntries_fst cfg s ps⟩,
    ?_, ⟨rfl, ?_⟩, rfl, ?_, ?_⟩
  · intro e he
    refine ⟨List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩), ?_⟩
    rcases hEntries_truthful cfg s ps e he with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.1, h.2, List.mem_append_right _ ?_⟩
      simp only [hOwed, List.mem_map, List.mem_filter]
      exact ⟨e, ⟨he, by simp [h.1]⟩, rfl⟩
  · intro e he
    apply List.mem_append_right
    have := result_mem_block (((hEntries cfg s ps)).map (fun e => (e.1, e.2.1)))
      (e.1, e.2.1) (List.mem_map.mpr ⟨e, he, rfl⟩)
    exact this
  · unfold EffectSafe
    rw [hRan_eq]
    exact hrun_safe cfg s.turn _ _ _
  · intro e he hx
    exact hrun_admitted cfg s.turn _ _ _ e he hx

/-- With `blindDep` the hybrid is effect safe against every dependency
relation, including the true one, without trusting any classification. -/
theorem hybrid_blind_safe_for_every_dependency (admit : List Receipt → Cmd → Bool)
    (exec : Cmd → Outcome) (s : HState) (ps : List Cmd) (dep : Cmd → Cmd → Bool) :
    EffectSafe dep (hRan ⟨admit, blindDep, exec⟩ s ps) := by
  apply safe_of_blind_safe
  unfold EffectSafe
  rw [hRan_eq]
  exact hrun_safe ⟨admit, blindDep, exec⟩ s.turn _ _ _

/-- Trimming keeps S1, the pin, the pending list and the ledger. -/
theorem hybrid_trim_preserves (s : HState) (h : WellPaired s.transcript) :
    WellPaired (hTrim s).transcript ∧ (hview (hTrim s)).request = s.request ∧
      (hTrim s).pending = s.pending ∧ (hTrim s).ledger = s.ledger :=
  ⟨iter_trim_preserves_pairing _ h, rfl, rfl, rfl⟩

/-! ### Over any run -/

inductive Ev where
  | step (ps : List Cmd)
  | trim

def hApply (cfg : Config) (s : HState) : Ev → HState
  | .step ps => hStep cfg s ps
  | .trim => hTrim s

def hRunEvs (cfg : Config) (s : HState) (evs : List Ev) : HState :=
  evs.foldl (hApply cfg) s

/-- Pairing, the pin and the ledger survive every interleaving of model steps
and trims. -/
theorem hybrid_invariants_forever (cfg : Config) :
    ∀ (evs : List Ev) (s : HState), WellPaired s.transcript →
      WellPaired (hRunEvs cfg s evs).transcript ∧
        (hRunEvs cfg s evs).request = s.request ∧ s.ledger <+: (hRunEvs cfg s evs).ledger
  | [], s, h => ⟨h, rfl, List.prefix_refl _⟩
  | .step ps :: evs, s, h => by
      have h' : WellPaired (hStep cfg s ps).transcript := wellPaired_append_block _ _ h
      obtain ⟨a, b, c⟩ := hybrid_invariants_forever cfg evs (hStep cfg s ps) h'
      exact ⟨a, b, List.IsPrefix.trans (List.prefix_append _ _) c⟩
  | .trim :: evs, s, h => by
      have h' : WellPaired (hTrim s).transcript := iter_trim_preserves_pairing _ h
      exact hybrid_invariants_forever cfg evs (hTrim s) h'

/-- Multi-step S2: a pending call stays pending, hence in every later view,
until an explicit resolution outside this execution model. Equal command
content never discharges an earlier occurrence by itself. -/
theorem hybrid_nonrun_resolved_or_visible (cfg : Config) (p : Cmd) :
    ∀ (evs : List Ev) (s : HState),
      (p ∈ s.pending ∨ ∃ c ∈ s.executed, c.name = p.name) →
      p ∈ (hview (hRunEvs cfg s evs)).pending ∨
        ∃ c ∈ (hRunEvs cfg s evs).executed, c.name = p.name
  | [], _, h => h
  | .trim :: evs, s, h => hybrid_nonrun_resolved_or_visible cfg p evs (hTrim s) h
  | .step ps :: evs, s, h => by
      apply hybrid_nonrun_resolved_or_visible cfg p evs
      rcases h with hp | ⟨c, hc, hn⟩
      · exact Or.inl (List.mem_append_left _ hp)
      · exact Or.inr ⟨c, List.mem_append_left _ hc, hn⟩

/-- **No silent deferral, ever.** A call that did not run in a step is, after
any later steps and trims, still pending in the view, or a call with the same
content has executed. -/
theorem hybrid_no_silent_deferral (cfg : Config) (s : HState) (ps : List Cmd)
    (paired : WellPaired s.transcript) (e : Cmd × Status × Bool)
    (he : e ∈ hEntries cfg s ps) (notRan : e.2.2 = false) (evs : List Ev) :
    e.1 ∈ (hview (hRunEvs cfg (hStep cfg s ps) evs)).pending ∨
      ∃ c ∈ (hRunEvs cfg (hStep cfg s ps) evs).executed, c.name = e.1.name := by
  apply hybrid_nonrun_resolved_or_visible
  have h := ((hybrid_grounded_and_safe cfg s ps paired).2.1 e he).2
  rcases h with h | h
  · rw [notRan] at h; exact absurd h.1 (by decide)
  · exact Or.inl h.2.2

/-- Running later commands cannot silently resolve an earlier pending occurrence. -/
theorem hybrid_pending_survives_step (cfg : Config) (s : HState) (ps : List Cmd)
    (p : Cmd) (h : p ∈ s.pending) : p ∈ (hStep cfg s ps).pending :=
  List.mem_append_left _ h

#print axioms hybrid_pending_survives_step

/-! ### Thoroughness: never less than godelclaw -/

theorem hrun_all_observations (cfg : Config) (turn : Nat)
    (hadm : ∀ L c, cfg.admit L c = true) (hok : ∀ c, (cfg.exec c).failed = false) :
    ∀ (L : List Receipt) (before l : List Cmd), (∀ c ∈ l, c.kind = .observation) →
      ((hrun cfg turn L before l).filter (·.2.2)).map (·.1) = l
  | _, _, [], _ => rfl
  | L, before, c :: rest, h => by
      have hc := h c (by simp)
      have ih := hrun_all_observations cfg turn hadm hok
        (L ++ [⟨turn, c, (cfg.exec c).status⟩]) (before ++ [c]) rest
        (fun d hd => h d (by simp [hd]))
      simp only [hrun, hc, Kind.isEffect, Bool.false_and, hadm, hok, if_true]
      simp [ih]

/-- When the gate admits and nothing fails, everything godelclaw runs in a step,
the hybrid (with the same gate, any dependency relation) runs too, as a prefix. -/
theorem hybrid_dominates_godel (cfg : Config) (s : HState) (ps : List Cmd)
    (hadm : ∀ L c, cfg.admit L c = true) (hok : ∀ c, (cfg.exec c).failed = false)
    (readsOnly : ∀ c ∈ ps, c.batchable = true → c.kind = .observation) :
    godelRanNow (cfg.admit s.ledger) ps <+: hRan cfg s ps := by
  rw [hRan_eq]
  have hfilter : godelRanNow (cfg.admit s.ledger) ps = godelAdmitted ps := by
    simp [godelRanNow, hadm]
  rw [hfilter]
  by_cases hb : ps.all (·.batchable) = true
  · have hobs : ∀ c ∈ ps, c.kind = .observation := fun c hc =>
      readsOnly c hc (List.all_eq_true.mp hb c hc)
    rw [hrun_all_observations cfg s.turn hadm hok _ _ _ hobs]
    have : godelAdmitted ps = ps.take requestedLimit := by
      simp [godelAdmitted, godelLimit, hb]
    rw [this]
    exact List.take_prefix _ _
  · have h1 : godelAdmitted ps = ps.take 1 := by
      simp [godelAdmitted, godelLimit, hb]
    rw [h1]
    match ps with
    | [] => simp [hrun]
    | c :: rest =>
        simp only [List.take, maxCalls, hrun, List.any_nil, Bool.and_false, hadm, hok,
          if_true, Bool.false_eq_true, if_false]
        simp

/-- Successful admitted observations have no numerical batch ceiling.
The host must still justify its observation and dependency declarations. -/
theorem hybrid_all_observations (cfg : Config) (s : HState) (ps : List Cmd)
    (hadm : ∀ L c, cfg.admit L c = true)
    (hok : ∀ c, (cfg.exec c).failed = false)
    (hobs : ∀ c ∈ ps, c.kind = .observation) : hRan cfg s ps = ps := by
  exact hrun_all_observations cfg s.turn hadm hok s.ledger [] ps hobs

#print axioms hybrid_all_observations

/-- The trade-off of stopping at the first failure: when a batchable read
fails, godelclaw still runs the next read and the hybrid does not (it is
`notRun` and pending). Dominance needs the no-failure hypothesis. -/
theorem hybrid_stops_reads_after_failure :
    let r1 : Cmd := { id := 1, name := 1, kind := .observation, batchable := true }
    let r2 : Cmd := { id := 2, name := 2, kind := .observation, batchable := true }
    let cfg : Config := ⟨fun _ _ => true, blindDep, fun c => if c.id == 1 then .error 0 else .ok 0⟩
    godelRanNow (fun _ => true) [r1, r2] = [r1, r2] ∧
      hRan cfg ⟨0, [], [], [], [], 0⟩ [r1, r2] = [r1] := by
  decide

/-! ### The 00:27 shape under the hybrid -/

/-- A declared claim is backed when the ledger holds a successful receipt for
the claimed content. -/
def claimsBacked (L : List Receipt) (c : Cmd) : Bool :=
  c.claims.all (fun n => L.any (fun r => r.cmd.name == n && r.status.isOk))

/-- godelclaw's gate on this trace (the reservation that withheld `tmux-peek`). -/
def gate0027 (_ : List Receipt) (c : Cmd) : Bool := reserve0027 c

def hybrid0027 : Config := ⟨gate0027, blindDep, fun _ => .ok 0⟩
def hybrid0027Claims : Config :=
  ⟨fun L c => gate0027 L c && claimsBacked L c, blindDep, fun _ => .ok 0⟩

def h0 : HState := ⟨0, [.user 0], [], [], [], 1311⟩

def hsteps (cfg : Config) (s : HState) (pss : List (List Cmd)) : HState :=
  pss.foldl (hStep cfg) s

/-- Turn 1308 under the hybrid: all three reads run. -/
theorem hybrid_runs_all_reads_1308 :
    hRan hybrid0027 h0 [lsTree, mailboxStatus, queryA] = [lsTree, mailboxStatus, queryA] := by
  decide

/-- At the claim decision the write is a pending, visible obligation, with its
`notRun` result paired in the transcript and the originating request pinned. -/
theorem hybrid_0027_pending_visible :
    let pre := hsteps hybrid0027 h0 before0027
    (hview pre).pending.any (·.id == wr.id) = true ∧
      pre.executed.any (·.name == wr.name) = false ∧
      (hview pre).request = 0 ∧
      pre.ledger.any (fun r => r.cmd.id == wr.id && r.status == .notRun .dependsOnUnobserved) = true := by
  decide

/-- With a claim gate in the admission slot (the shape of the context core's
claim gate) the claiming send is denied. -/
theorem hybrid_0027_claim_gate_blocks :
    let post := hStep hybrid0027Claims (hsteps hybrid0027Claims h0 before0027) claim0027
    post.executed.any (·.id == s2.id) = false ∧ post.pending.any (·.id == s2.id) = true := by
  decide

/-- Honest limit: without a claim gate the hybrid still executes the claiming
send. Pairing, pending and the pin make the evidence prominent; they do not
make the model truthful. -/
theorem hybrid_without_claim_gate_admits_claim :
    let post := hStep hybrid0027 (hsteps hybrid0027 h0 before0027) claim0027
    post.executed.any (·.id == s2.id) = true ∧ post.executed.any (·.name == wr.name) = false := by
  decide

end IterGrounding

/-! ## Axiom audit -/
#print axioms IterGrounding.iter_S1
#print axioms IterGrounding.iter_S2
#print axioms IterGrounding.iter_S3
#print axioms IterGrounding.iter_clean_preserves_pairing
#print axioms IterGrounding.iter_clean_keeps_last_step_verbatim
#print axioms IterGrounding.iter_trim_preserves_pairing
#print axioms IterGrounding.iter_trim_forgets_oldest
#print axioms IterGrounding.iter_trim_drops_request
#print axioms IterGrounding.iter_continues_without_request
#print axioms IterGrounding.iter_runs_blind_effect
#print axioms IterGrounding.iter_runs_effect_after_unobserved_effect
#print axioms IterGrounding.iter_executes_precommitted_effect_wrong_somewhere
#print axioms IterGrounding.iter_erases_calls_beyond_cap
#print axioms IterGrounding.iter_S3_needs_result_preserving_transformations
#print axioms IterGrounding.godel_runs_at_most_one
#print axioms IterGrounding.godel_effect_safe
#print axioms IterGrounding.godel_admission_respected
#print axioms IterGrounding.godel_prompt_overstates_limit
#print axioms IterGrounding.godel_limit_throttles_pure_reads
#print axioms IterGrounding.godel_S2_fails
#print axioms IterGrounding.godel_S2_holds_when_reserved
#print axioms IterGrounding.godel_S3_fails
#print axioms IterGrounding.godel_view_has_unpaired_proposal
#print axioms IterGrounding.godel_0027_trace
#print axioms IterGrounding.godel_deferral_drops_out_of_view
#print axioms IterGrounding.godel_new_input_truncates_original
#print axioms IterGrounding.hybrid_grounded_and_safe
#print axioms IterGrounding.hybrid_blind_safe_for_every_dependency
#print axioms IterGrounding.hybrid_trim_preserves
#print axioms IterGrounding.hybrid_invariants_forever
#print axioms IterGrounding.hybrid_nonrun_resolved_or_visible
#print axioms IterGrounding.hybrid_no_silent_deferral
#print axioms IterGrounding.hybrid_dominates_godel
#print axioms IterGrounding.hybrid_stops_reads_after_failure
#print axioms IterGrounding.hybrid_runs_all_reads_1308
#print axioms IterGrounding.hybrid_0027_pending_visible
#print axioms IterGrounding.hybrid_0027_claim_gate_blocks
#print axioms IterGrounding.hybrid_without_claim_gate_admits_claim
