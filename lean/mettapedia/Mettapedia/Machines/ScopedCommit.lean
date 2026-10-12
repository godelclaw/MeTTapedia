import Mathlib.Data.List.Basic

/-!
# Delimited commitment in finite equation search

This executable core separates branch-local bindings from a world which is
threaded through backtracking. A scope saves its failure continuation. A commit
discards the alternatives accumulated since that delimiter, preserving both
the current world and the successful branch's remaining computation. Choices
created later remain available until another commit removes them.

The evaluator uses a chosen depth-first traversal of finite alternatives. This
is an operational policy, not an assertion that equation meaning has a first
answer. Primitive computations are total functions in this finite model;
divergence, concurrent cancellation and native memory ownership are separate
obligations. A `choose` operation snapshots its finite alternatives when run.

`scope_locality` derives an exact law for the retained outside continuation,
including its effects. The answer-stream section keeps that continuation as a
residual: a bounded selection pauses, and resuming the residual where the pause
left the world loses and repeats nothing (`select_then_resume`). The token controls distinguish actual cancellation from
merely requiring a one-shot token at selected program points. No token scheme
or public MeTTa syntax is identified with delimited commitment by definition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCommit

universe u v r t

/-- A finite search plan. `scope body next` delimits commitments in `body`;
on a success, `next` resumes in the caller's scope. -/
inductive Body (Local : Type u) (World : Type v) where
  | done
  | fail
  | choice (left right : Body Local World)
  | choose (alternatives : Local → World → List Local) (next : Body Local World)
  | effect (action : Local → World → Local × World) (next : Body Local World)
  | branch (test : Local → World → Bool) (yes no : Body Local World)
  | commit (next : Body Local World)
  | scope (body next : Body Local World)

abbrev Failure (World : Type v) (Result : Type r) := World → Result

abbrev Success (Local : Type u) (World : Type v) (Result : Type r) :=
  Local → Failure World Result → World → Result

variable {Local : Type u} {World : Type v} {Result : Type r} {Target : Type t}

/-- `failure` is the currently pending search; `saved` is the failure
continuation captured by the nearest scope. A failure continuation receives
the current world, so abandoning an alternative does not undo its effects. -/
def eval : Body Local World → Local → Success Local World Result →
    Failure World Result → Failure World Result → World → Result
  | .done, s, success, failure, _, world => success s failure world
  | .fail, _, _, failure, _, world => failure world
  | .choice left right, s, success, failure, saved, world =>
      eval left s success (fun w => eval right s success failure saved w) saved world
  | .choose alternatives next, s, success, failure, saved, world =>
      ((alternatives s world).foldr
        (fun t rest => fun w => eval next t success rest saved w) failure) world
  | .effect action next, s, success, failure, saved, world =>
      let result := action s world
      eval next result.1 success failure saved result.2
  | .branch test yes no, s, success, failure, saved, world =>
      if test s world then eval yes s success failure saved world
      else eval no s success failure saved world
  | .commit next, s, success, _, saved, world =>
      eval next s success saved saved world
  | .scope body next, s, success, failure, saved, world =>
      eval body s
        (fun t alternatives w => eval next t success alternatives saved w)
        failure failure world

/-- Sequencing preserves existing inner delimiters. In particular it appends
to a scope's caller continuation, not to the body inside that scope. -/
def andThen : Body Local World → Body Local World → Body Local World
  | .done, next => next
  | .fail, _ => .fail
  | .choice left right, next => .choice (andThen left next) (andThen right next)
  | .choose alternatives body, next => .choose alternatives (andThen body next)
  | .effect action body, next => .effect action (andThen body next)
  | .branch test yes no, next => .branch test (andThen yes next) (andThen no next)
  | .commit body, next => .commit (andThen body next)
  | .scope body continuation, next => .scope body (andThen continuation next)

/-- A first-answer delimiter for this finite operational policy. The encoding
does not assert equality with every equational theory of scoped effects. -/
def once (body : Body Local World) : Body Local World :=
  .scope (andThen body (.commit .done)) .done

/-- Structural result transport. Only the local success algebra is assumed to
commute with the transport; the whole-program property follows by induction. -/
theorem eval_natural (transform : Result → Target) (body : Body Local World)
    (s : Local) (success : Success Local World Result)
    (success' : Success Local World Target)
    (failure saved : Failure World Result) (world : World)
    (compatible : ∀ s failure world,
      success' s (fun w => transform (failure w)) world =
        transform (success s failure world)) :
    eval body s success' (fun w => transform (failure w))
      (fun w => transform (saved w)) world =
      transform (eval body s success failure saved world) := by
  induction body generalizing s success success' failure saved world with
  | done => exact compatible s failure world
  | fail => rfl
  | choice left right ihLeft ihRight =>
      simp only [eval]
      rw [show (fun w =>
        eval right s success' (fun w => transform (failure w))
          (fun w => transform (saved w)) w) =
          (fun w => transform (eval right s success failure saved w)) by
        funext w
        exact ihRight s success success' failure saved w compatible]
      exact ihLeft _ _ _ _ _ _ compatible
  | choose alternatives next ih =>
      simp only [eval]
      have folded : ∀ values : List Local,
          values.foldr (fun t rest => fun w =>
            eval next t success' rest (fun w => transform (saved w)) w)
            (fun w => transform (failure w)) =
          (fun w => transform ((values.foldr
            (fun t rest => fun w => eval next t success rest saved w) failure) w)) := by
        intro values
        induction values with
        | nil => rfl
        | cons value values ihValues =>
            simp only [List.foldr_cons, ihValues]
            funext w
            exact ih _ _ _ _ _ _ compatible
      rw [folded]
  | effect action next ih => exact ih _ _ _ _ _ _ compatible
  | branch test yes no ihYes ihNo =>
      simp only [eval]
      cases test s world
      · exact ihNo _ _ _ _ _ _ compatible
      · exact ihYes _ _ _ _ _ _ compatible
  | commit next ih => exact ih _ _ _ _ _ _ compatible
  | scope body next ihBody ihNext =>
      simp only [eval]
      apply ihBody
      intro t alternatives w
      exact ihNext t success success' alternatives saved w compatible

/-- The structural sequencing construction agrees with success-continuation
composition, retaining the caller's delimiter when a nested scope returns. -/
theorem eval_andThen (body next : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (andThen body next) s success failure saved world =
      eval body s (fun t alternatives w => eval next t success alternatives saved w)
        failure saved world := by
  induction body generalizing s success failure saved world with
  | done => rfl
  | fail => rfl
  | choice left right ihLeft ihRight => simp only [andThen, eval, ihLeft, ihRight]
  | choose alternatives body ih =>
      simp only [andThen, eval, ih]
  | effect action body ih => exact ih _ _ _ _ _
  | branch test yes no ihYes ihNo => simp only [andThen, eval, ihYes, ihNo]
  | commit body ih =>
      -- The commit updates the delimiter to the same saved continuation, so
      -- the appended computation still sees the original enclosing scope.
      exact ih _ _ _ _ _
  | scope body continuation ihBody ihContinuation =>
      simp only [andThen, eval]
      congr 1
      funext t alternatives w
      exact ihContinuation _ _ _ _ _

/-- The first success discards its own residual operand search and receives
only the outside failure continuation. This is a local operational equation. -/
theorem eval_once (body : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (once body) s success failure saved world =
      eval body s (fun value _ w => success value failure w) failure failure world := by
  change eval (andThen body (.commit .done)) s success failure failure world = _
  rw [eval_andThen]
  rfl

abbrev Observation (Local : Type u) (World : Type v) := List Local × World

def collect : Success Local World (Observation Local World) :=
  fun value failure world =>
    let rest := failure world
    (value :: rest.1, rest.2)

def finish : Failure World (Observation Local World) := fun world => ([], world)

/-- All answers under this finite traversal policy, plus the final world. -/
def run (body : Body Local World) (s : Local) (world : World) :
    Observation Local World :=
  eval body s collect finish finish world

/-- Execute the remaining outer search in the world left by the inner search.
The retained local binding of that outside search is supplied by its closure. -/
def appendObservation (earlier : Observation Local World)
    (later : Failure World (Observation Local World)) : Observation Local World :=
  let rest := later earlier.2
  (earlier.1 ++ rest.1, rest.2)

/-- A delimited finite search invokes its outside search exactly once on the
world it leaves. Answer multiplicity and outside effects remain observable. -/
theorem eval_with_suffix (body : Body Local World) (s : Local)
    (outside : Failure World (Observation Local World)) (world : World) :
    eval body s collect outside outside world =
      appendObservation (run body s world) outside := by
  have natural := eval_natural (fun result => appendObservation result outside)
    body s collect collect finish finish world (by
      intro t failure w
      simp [collect, appendObservation])
  simpa [run, finish, appendObservation] using natural

/-- A nested delimiter cannot discard its caller's alternative. Even if the
inner search commits, the outside program runs after it in the resulting world. -/
theorem scope_locality (body outside : Body Local World) (s : Local) (world : World) :
    run (.choice (.scope body .done) outside) s world =
      appendObservation (run body s world) (fun w => run outside s w) := by
  exact eval_with_suffix body s (fun w => run outside s w) world

/-- Cutting twice with no intervening choice is idempotent in every context. -/
theorem adjacent_commits (body : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (.commit (.commit body)) s success failure saved world =
      eval (.commit body) s success failure saved world := rfl

/-- A commit discards alternatives already pending; a choice in its retained
continuation is installed afterwards and remains available. -/
theorem commit_then_choice (left right : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (.commit (.choice left right)) s success failure saved world =
      eval left s success (fun w => eval right s success saved saved w) saved world := rfl

/-- The first selected local binding commits the choices preceding the point.
This equation describes the chosen traversal, not an order-independent observer. -/
theorem choose_then_commit (alternatives : Local → World → List Local)
    (body : Body Local World) (s : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (.choose alternatives (.commit body)) s success failure saved world =
      match alternatives s world with
      | [] => failure world
      | first :: _ => eval body first success saved saved world := by
  simp only [eval]
  cases alternatives s world <;> rfl

/-- Effects performed before commitment are kept, rather than restored from a
scope checkpoint. -/
theorem effect_before_commit (action : Local → World → Local × World)
    (body : Body Local World) (s : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (.effect action (.commit body)) s success failure saved world =
      eval body (action s world).1 success saved saved (action s world).2 := rfl

namespace Controls

abbrev TestBody := Body Nat (Nat × Bool)

def answer (value : Nat) : TestBody := .effect (fun _ w => (value, w)) .done

def touch (next : TestBody) : TestBody :=
  .effect (fun s w => (s, (w.1 + 1, w.2))) next

/-- A real consumable token in the world. This operation does not cancel any
other search task merely because the token becomes unavailable. -/
def takeToken (next : TestBody) : TestBody :=
  .branch (fun _ w => w.2)
    (.effect (fun s w => (s, (w.1, false))) next) .fail

/-- A winner's subsequent acquire is treated as a no-op. This candidate keeps
the winner alive, but cannot implement a later cut of new alternatives. -/
def reacquireWinner (next : TestBody) : TestBody :=
  .effect (fun s w => (s, (w.1, false))) next

theorem cut_cancels_uncommitted_sibling :
    run (.choice (.commit (answer 1)) (answer 2)) 0 (0, true) = ([1], (0, true)) := by
  decide

theorem token_leaves_uncommitted_sibling :
    run (.choice (takeToken (answer 1)) (answer 2)) 0 (0, true) =
      ([1, 2], (0, false)) := by
  decide

theorem winner_continuation_keeps_choices :
    run (.choice (.commit (.choice (answer 1) (answer 2))) (answer 3))
      0 (0, true) = ([1, 2], (0, true)) := by
  decide

theorem requiring_token_again_loses_winner :
    run (takeToken (.choice (takeToken (answer 1)) (takeToken (answer 2))))
      0 (0, true) = ([], (0, false)) := by
  decide

theorem repeated_commit_keeps_execution :
    run (.commit (.commit (answer 1))) 0 (0, true) = ([1], (0, true)) ∧
      run (takeToken (takeToken (answer 1))) 0 (0, true) = ([], (0, false)) := by
  decide

/-- Idempotence of adjacent cuts does not make a later cut a permanent no-op. -/
theorem second_commit_prunes_new_choices :
    run (.commit (.choice (.commit (answer 1)) (answer 2)))
      0 (0, true) = ([1], (0, true)) ∧
    run (takeToken (.choice (reacquireWinner (answer 1)) (answer 2)))
      0 (0, true) = ([1, 2], (0, false)) := by
  decide

theorem inner_scope_preserves_outer_choice :
    run (.choice (.scope (.commit (answer 1)) .done) (answer 2))
      0 (0, true) = ([1, 2], (0, true)) := by
  decide

theorem nested_scopes_preserve_both_callers :
    run (.choice
      (.scope (.choice (.scope (.commit (answer 1)) .done) (answer 2)) .done)
      (answer 3)) 0 (0, true) = ([1, 2, 3], (0, true)) := by
  decide

/-- Correct lexical sequencing leaves a continuation cut in the caller scope. -/
theorem sequencing_does_not_capture_continuation :
    run (.choice (andThen (.scope (answer 1) .done) (.commit .done)) (answer 2))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choice (.scope (andThen (answer 1) (.commit .done)) .done) (answer 2))
      0 (0, true) = ([1, 2], (0, true)) := by
  decide

/-- Gate every answer with a token and the answer list happens to agree here;
the losing alternative's preceding effect still occurs. A cut cancels it. -/
theorem token_gating_does_not_cancel_effects :
    run (.choice (.commit (answer 1)) (touch (.commit (answer 2))))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choice (takeToken (answer 1)) (touch (takeToken (answer 2))))
      0 (0, true) = ([1], (1, false)) := by
  decide

theorem performed_effect_is_not_rolled_back :
    run (.choice (touch .fail) (.commit (answer 1)))
      0 (0, true) = ([1], (1, true)) := by
  decide

theorem traversal_changes_committed_answer :
    run (.choose (fun _ _ => [1, 2]) (.commit .done))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choose (fun _ _ => [2, 1]) (.commit .done))
      0 (0, true) = ([2], (0, true)) := by
  decide

/-- The losing operand is never run; merely taking the head after collecting
would instead retain its effect. -/
theorem once_stops_before_losing_effect :
    run (once (.choice (answer 1) (touch (answer 2))))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choice (answer 1) (touch (answer 2)))
      0 (0, true) = ([1, 2], (1, true)) := by
  decide

end Controls

/-! ## Answer streams: bounded selection, pausing and resumption

`run` gathers every answer.  A consumer that asks for a bounded prefix also
needs the search it has not yet performed.  An `Answers` stream keeps it: each
answer comes with the world in which it was produced and its residual search,
the failure continuation, which can be resumed in any world.  Nothing after an
answer is performed until its residual is resumed.

* `observe_stream`: the stream observes exactly what `run` observes.
* `select_then_resume`: taking `k` answers and resuming the residual in the
  world of the pause gives the uninterrupted run: every answer once, in order,
  and the same final world, so no world effect is performed twice.
* `run_once_eq_select`: `once` is the selection of one answer with the
  residual discarded.
* `stream_stationary`: a read-only search never moves the world.
* `resumeIfCurrent_contextual`: if a residual is resumed only in the world it
  paused in, two read-only searches with the same run in every world give the
  same observation to every observer that pauses after `k` answers, lets the
  world change, and resumes.

The controls show that each hypothesis is needed: restarting instead of
resuming repeats an answer and an effect; resuming in a changed world
separates two read-only searches with equal runs; and a pause observes the
intermediate world of a search that writes. -/

/-- A lazy answer stream: the search stops in a world, or it yields an answer,
the world at that answer, and the residual search. -/
inductive Answers (Local : Type u) (World : Type v) : Type (max u v) where
  | stop (world : World)
  | more (value : Local) (world : World) (residual : World → Answers Local World)

namespace Answers

/-- Every answer of a stream, resuming each residual where its answer left the
world, and the world the stream ends in. -/
def observe : Answers Local World → Observation Local World
  | .stop world => ([], world)
  | .more value world residual =>
      let rest := observe (residual world)
      (value :: rest.1, rest.2)

/-- The first answer with the world at it, or the world where the search stopped. -/
def first : Answers Local World → Observation Local World
  | .stop world => ([], world)
  | .more value world _ => ([value], world)

/-- Every answer lies in `world`, and every residual resumed in `world` stays there. -/
inductive Stationary (world : World) : Answers Local World → Prop
  | stop : Stationary world (.stop world)
  | more {value : Local} {residual : World → Answers Local World} :
      Stationary world (residual world) → Stationary world (.more value world residual)

theorem Stationary.observe_world {world : World} {answers : Answers Local World}
    (h : answers.Stationary world) : answers.observe.2 = world := by
  induction h with
  | stop => rfl
  | more _ ih => exact ih

end Answers

/-- Produce one answer and keep the residual search. -/
def yieldAnswer : Success Local World (Answers Local World) :=
  fun value residual world => .more value world residual

/-- The search has no alternative left. -/
def stopAnswers : Failure World (Answers Local World) := fun world => .stop world

/-- The answer stream of a search plan. -/
def stream (body : Body Local World) (s : Local) (world : World) : Answers Local World :=
  eval body s yieldAnswer stopAnswers stopAnswers world

/-- The stream observes exactly what `run` observes. -/
theorem observe_stream (body : Body Local World) (s : Local) (world : World) :
    (stream body s world).observe = run body s world :=
  (eval_natural Answers.observe body s yieldAnswer collect stopAnswers stopAnswers world
    (fun _ _ _ => rfl)).symm

/-- Resume a residual search in a world and observe everything it then does. -/
def resume (search : World → Answers Local World) (world : World) : Observation Local World :=
  (search world).observe

/-- Run a resumable search from `world` until `k` answers have been produced.
The result keeps the answers, the world of the pause, and the residual search.
A search that stops early leaves the empty residual. -/
def selectFrom : Nat → (World → Answers Local World) → World →
    List Local × World × (World → Answers Local World)
  | 0, search, world => ([], world, search)
  | k + 1, search, world =>
      match search world with
      | .stop final => ([], final, stopAnswers)
      | .more value here residual =>
          let paused := selectFrom k residual here
          (value :: paused.1, paused.2.1, paused.2.2)

/-- Pausing after `k` answers and resuming the residual where the pause left
the world observes exactly the uninterrupted search. -/
theorem selectFrom_resume (k : Nat) (search : World → Answers Local World) (world : World) :
    ((selectFrom k search world).1 ++
        (resume (selectFrom k search world).2.2 (selectFrom k search world).2.1).1,
      (resume (selectFrom k search world).2.2 (selectFrom k search world).2.1).2) =
      resume search world := by
  induction k generalizing search world with
  | zero => rfl
  | succ k ih =>
      simp only [selectFrom, resume]
      cases h : search world with
      | stop final => rfl
      | more value here residual =>
          have step := ih residual here
          simp only [resume] at step
          simp only [Answers.observe, List.cons_append]
          rw [← step]

/-- **Pausing loses and repeats nothing.**  Taking `k` answers of a search plan
and resuming its residual in the world of the pause observes the uninterrupted
run: the same answers in the same order and the same final world, so no world
effect is performed twice. -/
theorem select_then_resume (body : Body Local World) (s : Local) (k : Nat) (world : World) :
    ((selectFrom k (stream body s) world).1 ++
        (resume (selectFrom k (stream body s) world).2.2
          (selectFrom k (stream body s) world).2.1).1,
      (resume (selectFrom k (stream body s) world).2.2
          (selectFrom k (stream body s) world).2.1).2) =
      run body s world := by
  rw [selectFrom_resume]
  exact observe_stream body s world

/-- `once` observes the first answer of the stream and the world at it. -/
theorem run_once (body : Body Local World) (s : Local) (world : World) :
    run (once body) s world = (stream body s world).first := by
  unfold run
  rw [eval_once]
  exact eval_natural Answers.first body s yieldAnswer
    (fun value _ w => collect value finish w) stopAnswers stopAnswers world
    (fun _ _ _ => rfl)

/-- **`once` is selection of one answer with the residual discarded.**  Its
answers and world are those of `selectFrom 1`; the residual that `selectFrom`
keeps is what `once` drops. -/
theorem run_once_eq_select (body : Body Local World) (s : Local) (world : World) :
    run (once body) s world =
      ((selectFrom 1 (stream body s) world).1, (selectFrom 1 (stream body s) world).2.1) := by
  rw [run_once]
  simp only [selectFrom]
  cases stream body s world with
  | stop final => rfl
  | more value here residual => rfl

/-! ### Read-only searches and currency-checked resumption -/

/-- A search plan whose world effects only read the world. -/
def ReadOnly : Body Local World → Prop
  | .done => True
  | .fail => True
  | .choice left right => ReadOnly left ∧ ReadOnly right
  | .choose _ next => ReadOnly next
  | .effect action next => (∀ s world, (action s world).2 = world) ∧ ReadOnly next
  | .branch _ yes no => ReadOnly yes ∧ ReadOnly no
  | .commit next => ReadOnly next
  | .scope body next => ReadOnly body ∧ ReadOnly next

/-- A read-only plan, run with continuations that stay in `world`, stays in `world`. -/
theorem eval_stationary (body : Body Local World) (readOnly : ReadOnly body) (world : World) :
    ∀ (s : Local) (success : Success Local World (Answers Local World))
      (failure saved : Failure World (Answers Local World)),
      (∀ value residual, (residual world).Stationary world →
          (success value residual world).Stationary world) →
      (failure world).Stationary world →
      (saved world).Stationary world →
      (eval body s success failure saved world).Stationary world := by
  induction body with
  | done =>
      intro s success failure saved hSuccess hFailure _
      exact hSuccess s failure hFailure
  | fail =>
      intro s success failure saved _ hFailure _
      exact hFailure
  | choice left right ihLeft ihRight =>
      intro s success failure saved hSuccess hFailure hSaved
      exact ihLeft readOnly.1 s success _ saved hSuccess
        (ihRight readOnly.2 s success failure saved hSuccess hFailure hSaved) hSaved
  | choose alternatives next ih =>
      intro s success failure saved hSuccess hFailure hSaved
      simp only [eval]
      induction alternatives s world with
      | nil => exact hFailure
      | cons first others ihOthers =>
          exact ih readOnly first success _ saved hSuccess ihOthers hSaved
  | effect action next ih =>
      intro s success failure saved hSuccess hFailure hSaved
      simp only [eval]
      rw [readOnly.1 s world]
      exact ih readOnly.2 _ success failure saved hSuccess hFailure hSaved
  | branch test yes no ihYes ihNo =>
      intro s success failure saved hSuccess hFailure hSaved
      simp only [eval]
      cases test s world
      · exact ihNo readOnly.2 s success failure saved hSuccess hFailure hSaved
      · exact ihYes readOnly.1 s success failure saved hSuccess hFailure hSaved
  | commit next ih =>
      intro s success _ saved hSuccess _ hSaved
      exact ih readOnly s success saved saved hSuccess hSaved hSaved
  | scope body next ihBody ihNext =>
      intro s success failure saved hSuccess hFailure hSaved
      exact ihBody readOnly.1 s _ failure failure
        (fun value residual hResidual =>
          ihNext readOnly.2 value success residual saved hSuccess hResidual hSaved)
        hFailure hFailure

/-- **A read-only search never moves the world.** -/
theorem stream_stationary (body : Body Local World) (readOnly : ReadOnly body)
    (s : Local) (world : World) : (stream body s world).Stationary world :=
  eval_stationary body readOnly world s yieldAnswer stopAnswers stopAnswers
    (fun _ _ h => .more h) .stop .stop

/-- In a stationary search, the pause is in the starting world, the prefix is the
first `k` answers, and the residual resumed there gives the remaining answers. -/
theorem selectFrom_stationary (k : Nat) (search : World → Answers Local World) (world : World)
    (stationary : (search world).Stationary world) :
    (selectFrom k search world).2.1 = world ∧
    (selectFrom k search world).1 = ((resume search world).1).take k ∧
    resume (selectFrom k search world).2.2 world =
      (((resume search world).1).drop k, world) := by
  induction k generalizing search with
  | zero =>
      refine ⟨rfl, rfl, ?_⟩
      simp only [selectFrom, resume, List.drop_zero]
      exact Prod.ext rfl stationary.observe_world
  | succ k ih =>
      cases h : search world with
      | stop final =>
          rw [h] at stationary
          cases stationary
          simp [selectFrom, resume, h, Answers.observe, stopAnswers]
      | more value here residual =>
          rw [h] at stationary
          cases stationary with
          | more rest =>
              obtain ⟨hWorld, hTake, hDrop⟩ := ih residual rest
              simp only [selectFrom, resume, h, Answers.observe, List.take_succ_cons,
                List.drop_succ_cons]
              simp only [resume] at hTake hDrop
              exact ⟨hWorld, by rw [hTake], hDrop⟩

/-- Resume a paused search only if the world is still the world of the pause;
otherwise refuse.  The prefix is observed either way. -/
def resumeIfCurrent [DecidableEq World]
    (paused : List Local × World × (World → Answers Local World)) (now : World) :
    List Local × Option (Observation Local World) :=
  (paused.1, if now = paused.2.1 then some (resume paused.2.2 now) else none)

/-- **Currency-checked resumption is determined by the uninterrupted run** for
read-only searches. -/
theorem resumeIfCurrent_determined [DecidableEq World] (body : Body Local World)
    (readOnly : ReadOnly body) (s : Local) (k : Nat) (world now : World) :
    resumeIfCurrent (selectFrom k (stream body s) world) now =
      ((run body s world).1.take k,
        if now = world then some ((run body s world).1.drop k, world) else none) := by
  obtain ⟨hWorld, hTake, hDrop⟩ :=
    selectFrom_stationary k (stream body s) world (stream_stationary body readOnly s world)
  simp only [resume] at hTake hDrop
  rw [observe_stream] at hTake hDrop
  unfold resumeIfCurrent
  rw [hTake, hWorld]
  by_cases hNow : now = world
  · subst hNow
    simp only [if_true, resume, hDrop]
  · simp only [hNow, if_false]

/-- **Contextual equality suffices under currency-checked resumption.**  Two
read-only searches that have the same uninterrupted run in every world give the
same observation to every observer that takes `k` answers, lets the world
become `now`, and resumes only if `now` is still the world of the pause. -/
theorem resumeIfCurrent_contextual [DecidableEq World] (left right : Body Local World)
    (leftReadOnly : ReadOnly left) (rightReadOnly : ReadOnly right) (s : Local)
    (sameRun : ∀ world, run left s world = run right s world) (k : Nat) (world now : World) :
    resumeIfCurrent (selectFrom k (stream left s) world) now =
      resumeIfCurrent (selectFrom k (stream right s) world) now := by
  rw [resumeIfCurrent_determined left leftReadOnly, resumeIfCurrent_determined right rightReadOnly,
    sameRun world]

namespace StreamControls

open Controls

/-- Read the world's counter into the local value. -/
def readCounter (next : TestBody) : TestBody := .effect (fun _ w => (w.1, w)) next

/-- Read once, then answer twice. -/
def readOnce : TestBody := readCounter (.choice .done .done)

/-- Read again for each answer. -/
def readEach : TestBody := .choice (readCounter .done) (readCounter .done)

theorem readOnce_readOnly : ReadOnly readOnce :=
  ⟨fun _ _ => rfl, trivial, trivial⟩

theorem readEach_readOnly : ReadOnly readEach :=
  ⟨⟨fun _ _ => rfl, trivial⟩, ⟨fun _ _ => rfl, trivial⟩⟩

/-- The two searches have the same uninterrupted run in every world. -/
theorem readOnce_readEach_sameRun (world : Nat × Bool) :
    run readOnce 0 world = run readEach 0 world := rfl

/-- A resumption in a changed world separates them: the first resumes with the
value it read before the pause, the second reads the new world. -/
theorem late_world_separates :
    resume (selectFrom 1 (stream readOnce 0) (0, true)).2.2 (5, true) = ([0], (5, true)) ∧
    resume (selectFrom 1 (stream readEach 0) (0, true)).2.2 (5, true) = ([5], (5, true)) := by
  decide

/-- The currency check refuses both resumptions in the changed world. -/
theorem currency_check_refuses_changed_world :
    resumeIfCurrent (selectFrom 1 (stream readOnce 0) (0, true)) (5, true) = ([0], none) ∧
    resumeIfCurrent (selectFrom 1 (stream readEach 0) (0, true)) (5, true) = ([0], none) := by
  decide

/-- Count, then answer twice. -/
def countThenTwo : TestBody := touch (.choice (answer 1) (answer 2))

/-- Resuming performs the count once; restarting the plan in the world of the
pause repeats the first answer and the count. -/
theorem restart_repeats_effect :
    ((selectFrom 1 (stream countThenTwo 0) (0, true)).1 ++
        (resume (selectFrom 1 (stream countThenTwo 0) (0, true)).2.2
          (selectFrom 1 (stream countThenTwo 0) (0, true)).2.1).1,
      (resume (selectFrom 1 (stream countThenTwo 0) (0, true)).2.2
          (selectFrom 1 (stream countThenTwo 0) (0, true)).2.1).2) = ([1, 2], (1, true)) ∧
    ((selectFrom 1 (stream countThenTwo 0) (0, true)).1 ++
        (run countThenTwo 0 (selectFrom 1 (stream countThenTwo 0) (0, true)).2.1).1,
      (run countThenTwo 0 (selectFrom 1 (stream countThenTwo 0) (0, true)).2.1).2) =
      ([1, 1, 2], (2, true)) := by
  decide

/-- Write before the first answer, or between the two answers. -/
def writeFirst : TestBody := touch (.choice (answer 1) (answer 2))
def writeBetween : TestBody := .choice (answer 1) (touch (answer 2))

/-- The two writers have the same uninterrupted run in every world. -/
theorem writers_sameRun (world : Nat × Bool) :
    run writeFirst 0 world = run writeBetween 0 world := rfl

/-- A pause observes the intermediate world, which tells them apart. -/
theorem pause_observes_write_order :
    (selectFrom 1 (stream writeFirst 0) (0, true)).2.1 = (1, true) ∧
    (selectFrom 1 (stream writeBetween 0) (0, true)).2.1 = (0, true) := by
  decide

end StreamControls

end Mettapedia.Machines.ScopedCommit
