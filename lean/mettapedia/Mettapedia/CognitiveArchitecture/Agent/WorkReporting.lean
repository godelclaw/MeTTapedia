import Std

/-!
# Public work reporting

A small interface for machine-generated activity and model-written public
commentary.  A summary receives the two sources separately; its text cannot
replace or manufacture the activity records.  Activity retains order and
multiplicity.  Its metadata projection excludes tool arguments and results.

Metadata is assumed to have passed the caller's validation.  A status such as
`returned` describes a receipt, not success; the information-loss result is in
`EffectReceiptProjection.disposition_only_cannot_decide_completion`.

The publication switch models serialized operations: off drops new entries,
toggles preserve retained history, and an epoch rejects observations prepared
before a toggle.  There is no queue of rejected entries.

This is an interface contract, not a refinement proof of a particular observer,
JSON parser, filesystem or LLM.  In particular, a plain-text prefix is not an
authenticated source tag, and no theorem here certifies commentary as true.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.WorkReporting

structure Activity where
  tool : String
  status : String
deriving Repr, DecidableEq

/-- Only the admitted metadata is public; the payload may contain arguments,
results or other material that this reporting channel does not consume. -/
structure ToolRecord (Payload : Type) where
  tool : String
  status : String
  payload : Payload

def observe {Payload : Type} (record : ToolRecord Payload) : Activity :=
  ⟨record.tool, record.status⟩

theorem observation_ignores_payload {Payload : Type} (tool status : String)
    (first second : Payload) :
    observe ⟨tool, status, first⟩ = observe ⟨tool, status, second⟩ := rfl

inductive Entry where
  | activity (observation : Activity)
  | commentary (text : String)
deriving Repr, DecidableEq

/-- Structured input to an arbitrary public-summary writer.  Source identity
comes from the constructors, not from interpreting the text of a note. -/
structure SummaryInput where
  activities : List Activity
  commentary : List String
deriving Repr, DecidableEq

def prepare : List Entry → SummaryInput
  | [] => ⟨[], []⟩
  | .activity item :: rest =>
      let tail := prepare rest
      { tail with activities := item :: tail.activities }
  | .commentary text :: rest =>
      let tail := prepare rest
      { tail with commentary := text :: tail.commentary }

theorem activity_order_and_multiplicity (items : List Activity) :
    (prepare (items.map Entry.activity)).activities = items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [prepare, ih]

/-- Even commentary that looks like machine output remains commentary. -/
theorem commentary_preserves_activity (before after : List Entry) (text : String) :
    (prepare (before ++ .commentary text :: after)).activities =
      (prepare (before ++ after)).activities := by
  induction before with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simpa [prepare] using ih

def withSummary (write : SummaryInput → String) (entries : List Entry) : List Entry :=
  entries ++ [.commentary (write (prepare entries))]

/-- The writer can be an LLM or any other function.  Its output cannot alter
the observation stream supplied to it. -/
theorem summary_preserves_activity (write : SummaryInput → String)
    (entries : List Entry) :
    (prepare (withSummary write entries)).activities = (prepare entries).activities := by
  simpa [withSummary] using
    commentary_preserves_activity entries [] (write (prepare entries))

structure Display where
  enabled : Bool
  epoch : Nat
  retained : List Entry
deriving Repr, DecidableEq

/-- Every switch operation advances the epoch, even if the value is unchanged. -/
def toggle (display : Display) (enabled : Bool) : Display :=
  { display with enabled := enabled, epoch := display.epoch + 1 }

/-- An absent epoch is a direct publication; an observer supplies the epoch
under which it prepared the entry.  Publication and toggling are serialized. -/
def publish (display : Display) (expected : Option Nat) (entry : Entry) : Display :=
  if display.enabled = true ∧ (expected = none ∨ expected = some display.epoch) then
    { display with retained := display.retained ++ [entry] }
  else display

theorem toggle_preserves_history (display : Display) (enabled : Bool) :
    (toggle display enabled).retained = display.retained := rfl

theorem off_drops_entry (display : Display) (expected : Option Nat) (entry : Entry) :
    publish (toggle display false) expected entry = toggle display false := by
  simp [publish, toggle]

theorem current_publication_appends (display : Display) (entry : Entry)
    (enabled : display.enabled = true) :
    (publish display (some display.epoch) entry).retained = display.retained ++ [entry] := by
  simp [publish, enabled]

/-- Turning sharing off and on cannot revive an observation from the old epoch. -/
theorem resume_rejects_stale_entry (display : Display) (entry : Entry) :
    let resumed := toggle (toggle display false) true
    publish resumed (some display.epoch) entry = resumed := by
  simp [publish, toggle]
  omega

/-- Dropping an entry while off leaves nothing to replay on resume.  Old
retained entries remain available. -/
theorem resume_does_not_replay_dropped_entry (display : Display)
    (expected : Option Nat) (entry : Entry) :
    (toggle (publish (toggle display false) expected entry) true).retained =
      display.retained := by
  rw [off_drops_entry]
  rfl

#print axioms observation_ignores_payload
#print axioms activity_order_and_multiplicity
#print axioms commentary_preserves_activity
#print axioms summary_preserves_activity
#print axioms toggle_preserves_history
#print axioms off_drops_entry
#print axioms current_publication_appends
#print axioms resume_rejects_stale_entry
#print axioms resume_does_not_replay_dropped_entry

end Mettapedia.CognitiveArchitecture.Agent.WorkReporting
