import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.GSLT.Logic.HennessyMilnerTransport

/-!
# Recorded execution with a dormant backup

A recording contains inputs and their previously computed successor states.
The player reads that table without calling the transition function. A backup
player follows the table while inputs agree and switches permanently to live
computation at the first disagreement, or when the table is exhausted.

Validity is proved against the independently supplied transition function.
For every valid starting state, the backup preserves every input continuation,
not just the recorded one. Nevertheless, its transition component is unused
along the recorded run. An intervention on that component can therefore
distinguish the backup from direct execution while ordinary inputs cannot.

The construction is an abstract operational model of the dormant-machinery
challenge in Tim Maudlin, *Computation and Consciousness* (1989),
https://doi.org/10.2307/2026650 . It establishes neither physical realizability
nor a consciousness assignment. Its activity labels are declared evaluator
calls and table reads, not measurements of physical causal activity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ScriptedBackup

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.PrivilegedView

universe u v w

variable {State : Type u} {Input : Type v}

/-- A table of input symbols and previously computed successor states. -/
abbrev Script (State : Type u) (Input : Type v) := List (Input × State)

/-- Validate every table entry from its declared predecessor. -/
def Valid (step : State → Input → State) : State → Script State Input → Prop
  | _, [] => True
  | source, (input, target) :: rest =>
      target = step source input ∧ Valid step target rest

/-- Construct a recording by executing the supplied transition function. -/
def record (step : State → Input → State) : State → List Input → Script State Input
  | _, [] => []
  | source, input :: rest =>
      let target := step source input
      (input, target) :: record step target rest

theorem record_valid (step : State → Input → State) (source : State) (inputs : List Input) :
    Valid step source (record step source inputs) := by
  induction inputs generalizing source with
  | nil => trivial
  | cons input rest ih => exact ⟨rfl, ih _⟩

theorem record_inputs (step : State → Input → State) (source : State) (inputs : List Input) :
    (record step source inputs).map Prod.fst = inputs := by
  induction inputs generalizing source with
  | nil => rfl
  | cons input rest ih => simp [record, ih]

/-- Independently evaluate each row, compare its printed result, and reject
the first disagreement. The transition function belongs to the checker, not
to the passive recording. Subsequent rows use the newly computed state. -/
def verifyRun? [DecidableEq State] (step : State → Input → State) :
    State → Script State Input → Option State
  | source, [] => some source
  | source, (input, printed) :: rest =>
      let computed := step source input
      if computed = printed then verifyRun? step computed rest else none

theorem verifyRun?_isSome_iff [DecidableEq State] (step : State → Input → State)
    (source : State) (script : Script State Input) :
    (verifyRun? step source script).isSome = true ↔ Valid step source script := by
  induction script generalizing source with
  | nil => simp [verifyRun?, Valid]
  | cons entry rest ih =>
      rcases entry with ⟨input, printed⟩
      by_cases equal : step source input = printed
      · simp only [verifyRun?, equal, ↓reduceIte, ih, Valid]
        simp
      · simp [verifyRun?, equal, Valid, Ne.symm equal]

/-- The checked protocol produces the independent executor's result for
the script's input sequence. This is conditional on actually checking all
rows; mere possession of a recording does not perform those transitions. -/
theorem verifyRun?_valid_result [DecidableEq State] (step : State → Input → State)
    {source : State} {script : Script State Input} (valid : Valid step source script) :
    verifyRun? step source script = some ((script.map Prod.fst).foldl step source) := by
  induction script generalizing source with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨input, printed⟩
      have equal : step source input = printed := valid.1.symm
      simp only [verifyRun?, equal, ↓reduceIte, List.map_cons, List.foldl_cons]
      exact ih valid.2

/-- Table position and represented state are operational state, not an
implicit external oracle. `live` records the permanent switch to evaluation. -/
structure Player (State : Type u) (Input : Type v) where
  current : State
  remaining : Script State Input
  live : Bool
  deriving Repr, DecidableEq

/-- Which component supplies one successor. -/
inductive Activity where
  | tableRead
  | evaluate
  deriving DecidableEq, Repr

variable [DecidableEq Input]

/-- The table branch does not evaluate `step`. -/
def advance (step : State → Input → State) (player : Player State Input)
    (input : Input) : Player State Input × Activity :=
  if player.live then
    (⟨step player.current input, [], true⟩, .evaluate)
  else match player.remaining with
    | [] => (⟨step player.current input, [], true⟩, .evaluate)
    | (expected, target) :: rest =>
        if input = expected then (⟨target, rest, false⟩, .tableRead)
        else (⟨step player.current input, [], true⟩, .evaluate)

def backupStep (step : State → Input → State) (player : Player State Input)
    (input : Input) : Player State Input := (advance step player input).1

/-- Only the unconsumed table requires validation; live execution ignores it. -/
def Coherent (step : State → Input → State) (player : Player State Input) : Prop :=
  player.live = false → Valid step player.current player.remaining

theorem advance_current (step : State → Input → State)
    {player : Player State Input} (valid : Coherent step player) (input : Input) :
    (backupStep step player input).current = step player.current input := by
  rcases player with ⟨source, script, live⟩
  cases live
  · have valid' := valid rfl
    cases script with
    | nil => rfl
    | cons entry rest =>
        rcases entry with ⟨expected, target⟩
        by_cases same : input = expected
        · subst input
          simpa [backupStep, advance] using valid'.1
        · simp [backupStep, advance, same]
  · rfl

theorem advance_coherent (step : State → Input → State)
    {player : Player State Input} (valid : Coherent step player) (input : Input) :
    Coherent step (backupStep step player input) := by
  rcases player with ⟨source, script, live⟩
  cases live
  · have valid' := valid rfl
    cases script with
    | nil => simp [Coherent, backupStep, advance]
    | cons entry rest =>
        rcases entry with ⟨expected, target⟩
        by_cases same : input = expected
        · simp [Coherent, backupStep, advance, same]
          exact valid'.2
        · simp [Coherent, backupStep, advance, same]
  · simp [Coherent, backupStep, advance]

/-- Every admitted input word has the independently specified abstract result. -/
theorem run_current (step : State → Input → State) (inputs : List Input)
    {player : Player State Input} (valid : Coherent step player) :
    (inputs.foldl (backupStep step) player).current =
      inputs.foldl step player.current := by
  induction inputs generalizing player with
  | nil => rfl
  | cons input rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (advance_coherent step valid input),
        advance_current step valid input]

theorem all_input_futures (step : State → Input → State) {Output : Type w}
    (observe : State → Output) {player : Player State Input} (valid : Coherent step player) :
    wordBehaviour (backupStep step) (fun player => observe player.current) player =
      wordBehaviour step observe player.current := by
  funext inputs
  exact congrArg observe (run_current step inputs valid)

/-- Retain the actual component use at every tick. -/
def activities (step : State → Input → State) : Player State Input → List Input → List Activity
  | _, [] => []
  | player, input :: rest =>
      (advance step player input).2 :: activities step (backupStep step player input) rest

/-- On the recorded run the backup evaluator is dormant at every tick. -/
theorem recorded_activities (step : State → Input → State) (source : State)
    (inputs : List Input) :
    activities step ⟨source, record step source inputs, false⟩ inputs =
      List.replicate inputs.length .tableRead := by
  induction inputs generalizing source with
  | nil => rfl
  | cons input rest ih =>
      simp [record, activities, backupStep, advance, ih, List.replicate_succ]

theorem recorded_run (step : State → Input → State) (source : State) (inputs : List Input) :
    inputs.foldl (backupStep step) ⟨source, record step source inputs, false⟩ =
      ⟨inputs.foldl step source, [], false⟩ := by
  induction inputs generalizing source with
  | nil => rfl
  | cons input rest ih => simpa [record, backupStep, advance] using ih (step source input)

/-- Replace the evaluator while keeping the already-written table fixed.
Along its recorded inputs the backup still reads exactly the old run. -/
theorem fixed_record_run (baseline alternative : State → Input → State)
    (source : State) (inputs : List Input) :
    inputs.foldl (backupStep alternative) ⟨source, record baseline source inputs, false⟩ =
      ⟨inputs.foldl baseline source, [], false⟩ := by
  induction inputs generalizing source with
  | nil => rfl
  | cons input rest ih =>
      simpa [record, backupStep, advance] using ih (baseline source input)

theorem fixed_record_activities (baseline alternative : State → Input → State)
    (source : State) (inputs : List Input) :
    activities alternative ⟨source, record baseline source inputs, false⟩ inputs =
      List.replicate inputs.length Activity.tableRead := by
  induction inputs generalizing source with
  | nil => rfl
  | cons input rest ih =>
      simp [record, activities, backupStep, advance, ih, List.replicate_succ]

/-- The next tick after exhaustion uses the evaluator rather than stuttering. -/
theorem exhausted_evaluates (step : State → Input → State) (source : State) (input : Input) :
    advance step ⟨source, [], false⟩ input =
      (⟨step source input, [], true⟩, .evaluate) := rfl

theorem deviation_evaluates (step : State → Input → State) (source target : State)
    (expected input : Input) (rest : Script State Input) (different : input ≠ expected) :
    advance step ⟨source, (expected, target) :: rest, false⟩ input =
      (⟨step source input, [], true⟩, .evaluate) := by
  simp [advance, different]

/-- Intervening on the transition component alone leaves an agreed table
read unchanged. The stored target is held fixed during this intervention. -/
theorem table_read_ignores_evaluator (first second : State → Input → State)
    (source target : State) (input : Input) (rest : Script State Input) :
    advance first ⟨source, (input, target) :: rest, false⟩ input =
      advance second ⟨source, (input, target) :: rest, false⟩ input := by
  simp [advance]

/-- The same component intervention changes direct execution whenever its
replacement gives a different successor. -/
theorem direct_execution_separates_evaluators (first second : State → Input → State)
    (source : State) (input : Input) (different : first source input ≠ second source input) :
    (advance first ⟨source, [], true⟩ input).1.current ≠
      (advance second ⟨source, [], true⟩ input).1.current := different

/-- A player without backup ignores the supplied input, and stutters after
its recording is exhausted. -/
def replayStep (player : Player State Input) (_input : Input) : Player State Input :=
  match player.remaining with
  | [] => player
  | (_, target) :: rest => ⟨target, rest, false⟩

omit [DecidableEq Input] in
theorem replay_recorded_run (step : State → Input → State) (source : State)
    (inputs : List Input) :
    inputs.foldl replayStep ⟨source, record step source inputs, false⟩ =
      ⟨inputs.foldl step source, [], false⟩ := by
  induction inputs generalizing source with
  | nil => rfl
  | cons input rest ih => simpa [record, replayStep] using ih (step source input)

/-! ## The existing modal comparison, at the declared input boundary -/

section Modal

variable {State Input : Type} [DecidableEq Input]

/-- The endpoint GSLT of an input-driven machine. The separate modal labels
retain which input caused a transition. -/
def theory (step : State → Input → State) : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ input, target = step source input
  rewrites_resp_left := by
    intro source source' target equal event
    subst source'
    exact ⟨target, event, rfl⟩
  rewrites_resp_right := by
    intro source target target' event equal
    subst target'
    exact event

def observed {Output : Type} (step : State → Input → State) (observe : State → Output) :
    System (theory step) where
  Atom := Output
  observes value state := observe state = value
  observes_resp := by intro value left right equal; cases equal; exact Iff.rfl
  Label := Input
  act input source target := target = step source input
  act_resp_left := by
    intro input source source' target equal event
    subst source'
    exact ⟨target, event, rfl⟩
  act_resp_right := by
    intro input source target target' event equal
    subst target'
    exact event

/-- Invalid recordings are excluded by an earned invariant, not by assuming
the desired simulation law. -/
abbrev CheckedPlayer (step : State → Input → State) :=
  {player : Player State Input // Coherent step player}

def checkedStep (step : State → Input → State) (player : CheckedPlayer step)
    (input : Input) : CheckedPlayer step :=
  ⟨backupStep step player.val input, advance_coherent step player.property input⟩

/-- Every abstract input transition lifts to a checked player transition.
Thus all formulas of the declared input/observation language are covered. -/
def inputCover {Output : Type} (step : State → Input → State) (observe : State → Output) :
    SystemCover (observed (checkedStep step) (fun player => observe player.val.current))
      (observed step observe) where
  mapTerm player := player.val.current
  mapAtom := id
  mapLabel := id
  mapEquiv := by intro left right equal; cases equal; rfl
  observes_iff _ _ := Iff.rfl
  mapAct := by
    intro input source target event
    change target = checkedStep step source input at event
    subst target
    exact advance_current step source.property input
  liftAct := by
    intro input source target event
    exact ⟨checkedStep step source input, rfl,
      (advance_current step source.property input).trans event.symm⟩

theorem modal_iff {Output : Type} (step : State → Input → State) (observe : State → Output)
    (formula : Formula Output Input) (player : CheckedPlayer step) :
    (observed (checkedStep step) (fun player => observe player.val.current)).sat formula player ↔
      (observed step observe).sat formula player.val.current := by
  simpa [inputCover, observed] using ((inputCover step observe).sat_map formula player).symm

end Modal

/-! ## Separating controls -/

namespace Controls

def write (_state input : Bool) : Bool := input

def recordedFalse : Player Bool Bool := ⟨false, record write false [false], false⟩

theorem replay_agrees_on_recorded_input :
    (replayStep recordedFalse false).current = write false false := rfl

theorem replay_fails_on_changed_input :
    (replayStep recordedFalse true).current ≠ write false true := by decide

theorem backup_handles_changed_input :
    advance write recordedFalse true = (⟨true, [], true⟩, .evaluate) := by decide

theorem backup_passes_every_input_future :
    wordBehaviour (backupStep write) Player.current recordedFalse =
      wordBehaviour write id false :=
  all_input_futures write id (record_valid write false [false] |> fun h => fun _ => h)

/-- A corrupt table is rejected, although replay would still read it. -/
theorem corrupt_record_invalid : ¬ Valid write false [(false, true)] := by
  simp [Valid, write]

theorem checked_protocol_accepts_and_rejects :
    verifyRun? write false (record write false [true, false, true]) = some true ∧
      verifyRun? write false [(false, true)] = none := by decide

/-- Boundary input agreement coexists with a separating internal intervention. -/
theorem dormant_backup_distinction :
    wordBehaviour (backupStep write) Player.current recordedFalse =
      wordBehaviour write id false ∧
    activities write recordedFalse [false] = [.tableRead] ∧
    advance write recordedFalse false = advance (fun _ _ => true) recordedFalse false ∧
    write false false ≠ (fun (_ _ : Bool) => true) false false := by
  exact ⟨backup_passes_every_input_future, rfl,
    table_read_ignores_evaluator write (fun _ _ => true) false false false [], by decide⟩

end Controls

end Mettapedia.GSLT.ScriptedBackup
