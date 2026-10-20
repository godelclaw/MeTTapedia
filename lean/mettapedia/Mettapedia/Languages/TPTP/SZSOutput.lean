import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# SZS output events and completion evidence

This is the event protocol surrounding a TPTP payload, not the logic of that
payload. Status words stay open strings. A block completes only through a
matching end event. Raw-line recognition and native implementation refinement
are separate obligations; the protocol does not certify a prover's claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TPTP.SZSOutput

inductive Event where
  | line (text : String)
  | status (word raw : String)
  | start (form : String)
  | stop (form : String)
  deriving DecidableEq, Repr

structure Block where
  form : String
  reversedLines : List String
  deriving DecidableEq, Repr

abbrev Statuses := List (String × String)

inductive State where
  | outside (statuses : Statuses) (blocks : List Block)
  | inside (statuses : Statuses) (blocks : List Block)
      (form : String) (reversedLines : List String)
  deriving DecidableEq, Repr

def step : State -> Event -> Option State
  | .outside ss bs, .line _ => some (.outside ss bs)
  | .outside ss bs, .status word raw => some (.outside ((word, raw) :: ss) bs)
  | .inside ss bs form lines, .status word raw =>
      some (.inside ((word, raw) :: ss) bs form lines)
  | .outside ss bs, .start form => some (.inside ss bs form [])
  | .inside ss bs form lines, .line text => some (.inside ss bs form (text :: lines))
  | .inside ss bs form lines, .stop closing =>
      if form = closing then some (.outside ss (⟨form, lines⟩ :: bs)) else none
  | _, _ => none

/-- Independent transition judgment for the admitted event protocol. -/
inductive Step : State -> Event -> State -> Prop where
  | outsideLine (ss : Statuses) (bs : List Block) (text : String) :
      Step (.outside ss bs) (.line text) (.outside ss bs)
  | outsideStatus (ss : Statuses) (bs : List Block) (word raw : String) :
      Step (.outside ss bs) (.status word raw) (.outside ((word, raw) :: ss) bs)
  | insideStatus (ss : Statuses) (bs : List Block) (form : String)
      (lines : List String) (word raw : String) :
      Step (.inside ss bs form lines) (.status word raw)
        (.inside ((word, raw) :: ss) bs form lines)
  | start (ss : Statuses) (bs : List Block) (form : String) :
      Step (.outside ss bs) (.start form) (.inside ss bs form [])
  | insideLine (ss : Statuses) (bs : List Block) (form : String)
      (lines : List String) (text : String) :
      Step (.inside ss bs form lines) (.line text) (.inside ss bs form (text :: lines))
  | stop (ss : Statuses) (bs : List Block) (form : String) (lines : List String) :
      Step (.inside ss bs form lines) (.stop form) (.outside ss (⟨form, lines⟩ :: bs))

theorem step_sound {before after : State} {event : Event}
    (h : Step before event after) : step before event = some after := by
  cases h <;> simp [step]

theorem step_complete {before after : State} {event : Event}
    (h : step before event = some after) : Step before event after := by
  cases before <;> cases event <;> simp only [step] at h
  all_goals try { contradiction }
  all_goals try { cases h; constructor }
  split at h
  · rename_i same
    subst_vars
    cases h
    constructor
  · cases h

theorem step_iff {before after : State} {event : Event} :
    step before event = some after <-> Step before event after :=
  ⟨step_complete, step_sound⟩

def run : State -> List Event -> Option State
  | state, [] => some state
  | state, event :: rest => (step state event).bind fun next => run next rest

theorem run_append (state : State) (first second : List Event) :
    run state (first ++ second) = (run state first).bind (fun next => run next second) := by
  induction first generalizing state with
  | nil => rfl
  | cons event rest ih =>
      cases h : step state event <;> simp [run, h, ih]

inductive Trace : State -> List Event -> State -> Prop where
  | nil (state : State) : Trace state [] state
  | cons {before middle after : State} {event : Event} {rest : List Event} :
      Step before event middle -> Trace middle rest after -> Trace before (event :: rest) after

theorem run_iff_trace (before after : State) (events : List Event) :
    run before events = some after <-> Trace before events after := by
  induction events generalizing before with
  | nil =>
      constructor
      · intro h; cases h; exact .nil _
      · intro h; cases h; rfl
  | cons event rest ih =>
      constructor
      · intro h
        cases hs : step before event with
        | none => simp [run, hs] at h
        | some middle =>
            have tail : run middle rest = some after := by simpa [run, hs] using h
            exact .cons (step_complete hs) ((ih middle).mp tail)
      · intro h
        cases h with
        | cons first tail =>
            simp [run, step_sound first, (ih _).mpr tail]

theorem completion_requires_matching_end
    (ss ss' : Statuses) (bs bs' : List Block) (form : String)
    (lines : List String) (event : Event)
    (h : step (.inside ss bs form lines) event = some (.outside ss' bs')) :
    event = .stop form ∧ bs' = ⟨form, lines⟩ :: bs := by
  have legal := step_complete h
  cases legal
  exact ⟨rfl, rfl⟩

theorem mismatched_end_refused (ss : Statuses) (bs : List Block)
    (form closing : String) (lines : List String) (different : form ≠ closing) :
    step (.inside ss bs form lines) (.stop closing) = none := by
  simp [step, different]

theorem status_cannot_finish_block (ss : Statuses) (bs : List Block)
    (form word raw : String) (lines : List String) :
    step (.inside ss bs form lines) (.status word raw) =
      some (.inside ((word, raw) :: ss) bs form lines) := by
  rfl

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- The finite authored event vocabulary, independent of the raw-line lexer. -/
def language : LanguageDef := languageDef! {
  name : "SZSOutputProtocolV1"
  types { ![str] as SZSWord ![str] as SZSText SZSEvent SZSLines SZSStatuses SZSBlocks SZSState }
  terms {
    «szs:line». text:SZSText |- "szs:line" text : SZSEvent;
    «szs:status». word:SZSWord, raw:SZSText |- "szs:status" word raw : SZSEvent;
    «szs:start». form:SZSWord |- "szs:start" form : SZSEvent;
    «szs:end». form:SZSWord |- "szs:end" form : SZSEvent;
    «szs:lines-nil». |- "szs:lines-nil" : SZSLines;
    «szs:lines-cons». text:SZSText, tail:SZSLines |- "szs:lines-cons" text tail : SZSLines;
    «szs:statuses-nil». |- "szs:statuses-nil" : SZSStatuses;
    «szs:statuses-cons». word:SZSWord, raw:SZSText, tail:SZSStatuses |-
      "szs:statuses-cons" word raw tail : SZSStatuses;
    «szs:blocks-nil». |- "szs:blocks-nil" : SZSBlocks;
    «szs:blocks-cons». form:SZSWord, lines:SZSLines, tail:SZSBlocks |-
      "szs:blocks-cons" form lines tail : SZSBlocks;
    «szs:outside». statuses:SZSStatuses, blocks:SZSBlocks |-
      "szs:outside" statuses blocks : SZSState;
    «szs:inside». statuses:SZSStatuses, blocks:SZSBlocks, form:SZSWord, lines:SZSLines |-
      "szs:inside" statuses blocks form lines : SZSState;
    «szs:step». event:SZSEvent, state:SZSState |- "szs:step" event state : SZSState;
  }
  equations {
    «outside-line». text:SZSText, ss:SZSStatuses, bs:SZSBlocks |-
      "szs:step"("szs:line"(text), "szs:outside"(ss, bs)) = "szs:outside"(ss, bs);
    «outside-status». word:SZSWord, raw:SZSText, ss:SZSStatuses, bs:SZSBlocks |-
      "szs:step"("szs:status"(word, raw), "szs:outside"(ss, bs)) =
        "szs:outside"("szs:statuses-cons"(word, raw, ss), bs);
    «inside-status». word:SZSWord, raw:SZSText, ss:SZSStatuses, bs:SZSBlocks,
      form:SZSWord, lines:SZSLines |-
      "szs:step"("szs:status"(word, raw), "szs:inside"(ss, bs, form, lines)) =
        "szs:inside"("szs:statuses-cons"(word, raw, ss), bs, form, lines);
    «start». form:SZSWord, ss:SZSStatuses, bs:SZSBlocks |-
      "szs:step"("szs:start"(form), "szs:outside"(ss, bs)) =
        "szs:inside"(ss, bs, form, "szs:lines-nil"());
    «inside-line». text:SZSText, ss:SZSStatuses, bs:SZSBlocks, form:SZSWord, lines:SZSLines |-
      "szs:step"("szs:line"(text), "szs:inside"(ss, bs, form, lines)) =
        "szs:inside"(ss, bs, form, "szs:lines-cons"(text, lines));
    «end». form:SZSWord, ss:SZSStatuses, bs:SZSBlocks, lines:SZSLines |-
      "szs:step"("szs:end"(form), "szs:inside"(ss, bs, form, lines)) =
        "szs:outside"(ss, "szs:blocks-cons"(form, lines, bs));
  }
  rewrites {}
}

example : run (.outside [] []) [.start "Proof", .line "p", .stop "Proof"] =
    some (.outside [] [⟨"Proof", ["p"]⟩]) := by decide
example : run (.outside [] []) [.status "Theorem" "% SZS status Theorem"] =
    some (.outside [("Theorem", "% SZS status Theorem")] []) := by decide
example : run (.outside [] []) [.start "Proof", .stop "Model"] = none := by decide

end Mettapedia.Languages.TPTP.SZSOutput
