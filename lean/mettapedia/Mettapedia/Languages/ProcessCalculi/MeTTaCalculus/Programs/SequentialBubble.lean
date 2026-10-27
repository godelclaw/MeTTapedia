import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Success

/-!
# Sequential code as a bubble

The fabric is a fibration: commitments and guarantees fibred over spaces, contexts and theories. A
region is a bubble; carving one out is comprehension; a modality is an operator inside a fibre. A
bubble is observers, commitments and verdict guarantees, carved inside the strongest foundation,
and its good properties are theorems about the bubble, never restrictions of the foundation.

Here the foundation is the reactive semantics of the interaction basis: any enabled commit may fire,
under any scheduler. **The sequential bubble** (`SequentialBubble`) is carved out of it by a
predicate on a program's capability structure:

* **commitments**: one process per stage, threaded by a private continuation token (each stage's
  continuation is the token its last step makes; `Chain`); tokens apart from the data, so no other
  process takes or makes them (`TokenFree`, `EffectApart`; beside others, `TokenNeutral`); a fixed
  strategy, whose run today is executable (`strategy`);
* **observer**: the value test, "the value appears" (`value`, `Success.Barb`);
* **verdicts** (`SequentialBubble.verdicts`):
  * determinism: every maximal run is the chain, and the reactive system is conflict-free;
  * the direct sequential evaluator refines the reactive semantics: what it computes is the only
    outcome of every scheduler, so the fast path is the bubble's implementation, not a second
    semantics;
  * the value test is must-passed whenever the direct evaluator shows the value.

Beside other processes (`SequentialBubble.Beside`) that neither take nor make its tokens, the
bubble keeps its order and taking its token cancels it for good
(`SequentialBubble.Beside.order_and_cancel`). Determinism of the whole system then needs the other
processes' regions to be safe and each process determinate on its own (`determinate_of_safe`).

**Which kind of carve-out.** The bubble is the comprehension of a predicate on programs and their
capability structure: a sub-fibre of the fibre of programs, not a modality. Nothing in the fibre of
programs is changed by an operator; programs that fail the predicate stay programs, outside the
bubble (`Controls.outside_the_bubble`).

## Map to the type theory (pointers, no new type theory)

* **Call-by-push-value** (Levy): the sequential bubble is CBPV's computation side with explicit
  continuations. A continuation token is a stack, a stage is a computation, and a waiting form
  (`await`) is a guarded thunk: a suspended computation that a commit forces when its guard holds.
  Reading a thunk never forces it (`inspect_keeps_step` in `TopLevel`; `Reflection.DataLaw`).
* **Sessions and linear logic**: once-linear programs and the session encoding are the typed
  fragment of channel-like regions (`InteractionTypes.OnceLinearPrograms`, deadlock freedom exactly
  when prioritized, `deadlockFree_iff_prioritized`; `InteractionTypes.SessionEncoding`,
  `encode_onceLinear`, `encode_deadlockFree_iff_prioritized`).
* **Graded comonad and effects**: facets as coeffects (`InteractionTypes.ObservationComonad`,
  `ofGrade_iff_factors`, `run_ofGrade`), footprints as effects (`InteractionTypes.FootprintTypes`,
  `duplicable_iff`, `snapshot_iff_serial`). The facet classifier of `Determinacy` is a predicate on
  grades: which pairs of grades held by different processes may coexist.
* **The trinity, per construct**: operationally, the agenda and its commits (`Chain`, `TopLevel`);
  intensionally, footprint, session and facet types (the modules above, and `SafeAt` in `Determinacy`);
  extensionally, behaviour up to bisimulation and testing (`OccurrenceCommits.Equivalence`, and the
  may and must tests of `Success`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uO uR

section Bubble

variable {O : Type uO} [DecidableEq O] {R : Type uR}

/-- **The sequential bubble**: the commitments of a sequential program, and its observer. -/
structure SequentialBubble (label : O → R) where
  /-- The private continuation tokens. -/
  tok : ℕ → O
  injective : Function.Injective tok
  /-- The data the program starts from. -/
  initial : Finset O
  /-- The effects of the fixed strategy, in order. -/
  effects : List (Commit O R)
  free : TokenFree tok initial
  apart : ∀ e ∈ effects, EffectApart label tok e
  /-- The fixed strategy's run is executable today. -/
  strategy : Executable label initial effects
  /-- The observer: the value test. -/
  value : R → Bool

variable {label : O → R}

namespace SequentialBubble

variable (B : SequentialBubble label)

/-- The reactive semantics of the bubble's program: its chain, under any scheduler. -/
def reactive : Commit O R → Prop := fun c => c ∈ chain B.tok 0 B.effects

/-- Where the reactive semantics starts. -/
def start : Finset O := insert (B.tok 0) B.initial

/-- What the direct sequential evaluator computes: the effects fired in order. -/
def direct : Finset O := fireList B.initial B.effects

/-- **The verdicts of the sequential bubble.** Every maximal run is the chain; the reactive system
is conflict-free; every maximal run ends at the direct evaluator's store with the last token; and
the value test is must-passed when the direct evaluator shows the value. -/
theorem verdicts :
    (∀ run, Maximal label B.reactive B.start run ↔ run = chain B.tok 0 B.effects) ∧
      ConflictFree label B.reactive B.start ∧
      (∀ run, Maximal label B.reactive B.start run →
        fireList B.start run = insert (B.tok B.effects.length) B.direct) ∧
      (Barb label B.value B.direct → MustPass label B.reactive B.value B.start) := by
  refine ⟨maximal_chain_iff B.injective B.free B.apart B.strategy, chain_conflictFree B.injective
    B.free B.apart, fun run maximal => ?_, chain_mustPass B.injective B.free B.apart B.strategy⟩
  rw [(maximal_chain_iff B.injective B.free B.apart B.strategy run).mp maximal]
  simpa [SequentialBubble.start, SequentialBubble.direct] using fireList_chain (j := 0) B.free B.apart

/-- **The bubble beside other processes**: they neither take nor make its tokens, and a process
tag tells its steps apart. Cancelling commits take a token and make none. -/
structure Beside (B : SequentialBubble label) where
  others : Commit O R → Prop
  cancels : Commit O R → Prop
  neutral : ∀ c, others c → TokenNeutral B.tok c
  cancelling : ∀ c, cancels c → Cancels B.tok c
  tag : Commit O R → Bool
  tagChain : ∀ c ∈ chain B.tok 0 B.effects, tag c = true
  tagOthers : ∀ c, others c → tag c = false
  tagCancels : ∀ c, cancels c → tag c = false

/-- **Beside others, the bubble keeps its order, and cancellation is for good.** -/
theorem Beside.order_and_cancel {B : SequentialBubble label} (E : B.Beside)
    {run : List (Commit O R)}
    (isRun : IsRun label (beside B.tok B.effects E.others E.cancels) B.start run) :
    (run.filter E.tag) <+: chain B.tok 0 B.effects ∧
      ∀ pre c post, run = pre ++ c :: post → E.cancels c → post.filter E.tag = [] := by
  have := chain_order_cancel E.neutral E.cancelling E.tag E.tagOthers E.tagCancels B.injective B.apart
    E.tagChain run 0 B.initial B.free isRun
  simpa using this

end SequentialBubble

end Bubble

/-! ## Controls -/

namespace Controls

/-- Labels are identities. -/
def selfLabel (o : ℕ) : ℕ := o

/-- The value test: identity `3` appears. -/
def isThree (r : ℕ) : Bool := r == 3

/-- Read `1`, make `2`; then take `1`, make `3`. -/
def bubbleRead : Commit ℕ ℕ := ⟨∅, {1}, {2}, []⟩
def bubbleTake : Commit ℕ ℕ := ⟨{1}, ∅, {3}, []⟩

/-- **Positive control**: the two-step program, with tokens `100, 101, 102`, is in the bubble. -/
def twoSteps : SequentialBubble selfLabel where
  tok := tok
  injective := tok_injective
  initial := {1}
  effects := [bubbleRead, bubbleTake]
  free := fun i h => tok_ne i 1 (by norm_num) (Finset.mem_singleton.mp h)
  apart := by
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨fun i h => by simp [bubbleRead] at h,
        fun i h => tok_ne i 1 (by norm_num) (Finset.mem_singleton.mp h),
        fun i h => tok_ne i 2 (by norm_num) (Finset.mem_singleton.mp h),
        fun _ member => by simp [bubbleRead] at member⟩
    · exact ⟨fun i h => tok_ne i 1 (by norm_num) (Finset.mem_singleton.mp h),
        fun i h => by simp [bubbleTake] at h,
        fun i h => tok_ne i 3 (by norm_num) (Finset.mem_singleton.mp h),
        fun _ member => by simp [bubbleTake] at member⟩
  strategy := .cons (by decide) (.cons (by decide) (.nil _))
  value := isThree

/-- The direct evaluator shows the value. -/
theorem twoSteps_shows_value : Barb selfLabel isThree twoSteps.direct :=
  ⟨3, by decide, rfl⟩

/-- **The bubble's verdicts on the two-step program**: one maximal run, conflict-free, ending with
the direct evaluator's store, and the value test must-passed. -/
theorem twoSteps_verdicts :
    (∀ run, Maximal selfLabel twoSteps.reactive twoSteps.start run ↔
        run = chain tok 0 [bubbleRead, bubbleTake]) ∧
      MustPass selfLabel twoSteps.reactive isThree twoSteps.start := by
  obtain ⟨unique, _, _, must⟩ := twoSteps.verdicts
  exact ⟨unique, must twoSteps_shows_value⟩

/-- **Negative control, outside the bubble.** The same effects without the continuation tokens are
still a program, but not in the bubble, and its verdict fails: two maximal runs end at different
stores, and one of them never shows the value. -/
theorem outside_the_bubble :
    Maximal selfLabel (fun c => c = bubbleRead ∨ c = bubbleTake) {1} [bubbleTake] ∧
      Maximal selfLabel (fun c => c = bubbleRead ∨ c = bubbleTake) {1} [bubbleRead, bubbleTake] ∧
      fireList ({1} : Finset ℕ) [bubbleTake] ≠ fireList ({1} : Finset ℕ) [bubbleRead, bubbleTake] ∧
      ¬ Barb selfLabel (fun r => r == 2) (fireList ({1} : Finset ℕ) [bubbleTake]) := by
  refine ⟨⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩,
    ⟨⟨.cons (by decide) (.cons (by decide) (.nil _)), by simp⟩, ?_⟩, by decide, ?_⟩
  · rintro c (rfl | rfl) <;> decide
  · rintro c (rfl | rfl) <;> decide
  · rintro ⟨o, inStore, isTwo⟩
    have : o = 3 := by simpa [bubbleTake, fire] using inStore
    subst this
    simp [selfLabel] at isTwo

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
