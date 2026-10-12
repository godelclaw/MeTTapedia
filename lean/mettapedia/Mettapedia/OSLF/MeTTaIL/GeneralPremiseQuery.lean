import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryFrames
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCorrectness

/-!
# Interruptible structural relation queries

Rows, arguments and matcher alternatives advance through retained frames.
Each answer retains a checked occurrence trace and the independent relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def matchingRequest (request : Request) (index : Nat) (assignment : Assignment)
    (schema value : Pattern) : GeneralScopedMatchMachine.Request where
  rule := request.context.rule
  spec := request.context.spec
  ambient := request.context.bound.length
  site := request.context.site index
  path := []
  depth := 0
  initial := assignment
  schema := schema
  target := value

def expandArguments (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request) :
    Scheduler.Expansion (Task environment request) (Answer environment request) Obligation :=
  match schemasFound : frame.schemas, valuesFound : frame.values, modesFound : frame.modes with
  | [], [], [] =>
      if checked : checkTypedAssignment environment request.context frame.assignment then
        let held : TracedArgumentsHold request.context frame.index frame.assignment
            frame.schemas frame.values frame.modes frame.assignment [] := by
          rw [schemasFound, valuesFound, modesFound]
          exact .nil
        { answers := [⟨frame.rowIndex, frame.assignment, frame.origins,
            by simpa using frame.finish _ [] held (checkTypedAssignment_sound checked)⟩] }
      else {}
  | schema :: schemas, value :: values, mode :: modes =>
      match mode with
      | .input =>
          match interpreted : instantiateAt? request.context.rule request.context.spec
              request.context.bound.length (request.context.site frame.index) [] 0
              frame.assignment schema with
          | none => { unresolved := [.inputUnavailable frame.rowIndex frame.index] }
          | some actual =>
              if same : actual == value then
                let held : ArgumentHolds request.context frame.index .input
                    frame.assignment schema value frame.assignment :=
                  .input (by simpa only [beq_iff_eq.mp same] using interpreted)
                { tasks := [.arguments {
                    rowIndex := frame.rowIndex
                    index := frame.index + 1
                    assignment := frame.assignment
                    schemas := schemas
                    values := values
                    modes := modes
                    origins := frame.origins ++ [(frame.index, [])]
                    finish := fun final traces tail typed => by
                      have traced : TracedArgumentsHold request.context frame.index frame.assignment
                          frame.schemas frame.values frame.modes final ((frame.index, []) :: traces) := by
                        rw [schemasFound, valuesFound, modesFound]
                        cases held with
                        | input interpreted => exact .input interpreted tail
                      simpa only [List.append_assoc, List.singleton_append] using
                        frame.finish final ((frame.index, []) :: traces) traced typed }] }
              else {}
      | .output =>
          let query := matchingRequest request frame.index frame.assignment schema value
          { tasks := [.matcher {
              rowIndex := frame.rowIndex
              argumentIndex := frame.index
              schemas := schemas
              values := values
              modes := modes
              origins := frame.origins
              query := query
              state := GeneralScopedMatchMachine.start query
              reachable := .start
              cursor := 0
              finish := fun answer valid final traces tail typed => by
                have traced : TracedArgumentsHold request.context frame.index frame.assignment
                    frame.schemas frame.values frame.modes final ((frame.index, answer.trace) :: traces) := by
                  rw [schemasFound, valuesFound, modesFound]
                  exact .output valid tail
                simpa only [List.append_assoc, List.singleton_append] using
                  frame.finish final ((frame.index, answer.trace) :: traces) traced typed }] }
  | _, _, _ => { unresolved := [.argumentShape frame.rowIndex frame.index] }

def expandMatcher (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request) :
    Scheduler.Expansion (Task environment request) (Answer environment request) Obligation :=
  match found : frame.state.answers[frame.cursor]? with
  | some answer =>
      have valid : GeneralScopedMatchMachine.Answer.Valid frame.query answer :=
        GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found)
      { tasks := [
          .arguments {
            rowIndex := frame.rowIndex
            index := frame.argumentIndex + 1
            assignment := answer.assignment
            schemas := frame.schemas
            values := frame.values
            modes := frame.modes
            origins := frame.origins ++ [(frame.argumentIndex, answer.trace)]
            finish := frame.finish answer valid },
          .matcher { frame with cursor := frame.cursor + 1 }] }
  | none =>
      if GeneralScopedMatchMachine.complete frame.state then {}
      else
        { tasks := [.matcher { frame with
            state := GeneralScopedMatchMachine.tick frame.query frame.state
            reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable }] }

def expand (environment : Environment) (request : Request) : Task environment request →
    Scheduler.Expansion (Task environment request) (Answer environment request) Obligation
  | .start =>
      match found : signature? environment.provider request.relation request.arguments.length with
      | none => { unresolved := [.signatureUnavailable request.relation request.arguments.length] }
      | some signature => { tasks := [.rows ⟨signature, found, 0⟩] }
  | .rows frame =>
      match found : environment.provider.rows[frame.cursor]? with
      | none => {}
      | some row =>
          let tail := Task.rows { frame with cursor := frame.cursor + 1 }
          if checked : checkRow environment.language environment.free request.context.bound
              frame.signature row then
            { tasks := [.arguments {
                rowIndex := frame.cursor
                index := 0
                assignment := request.initial
                schemas := request.arguments
                values := row.values
                modes := frame.signature.modes
                origins := []
                finish := fun final traces held typed => by
                  simpa using TracedQuery.row found frame.signatureFound (checkRow_sound checked) held typed }, tail] }
          else { tasks := [tail] }
  | .arguments frame => expandArguments environment request frame
  | .matcher frame => expandMatcher environment request frame

def start (environment : Environment) (request : Request) : State environment request :=
  { agenda := [.start] }

def tick (environment : Environment) (request : Request) (state : State environment request) :
    State environment request := Scheduler.tick (expand environment request) state

def run (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request) : State environment request :=
  Scheduler.run (expand environment request) fuel state

def complete (environment : Environment) (request : Request) (state : State environment request) :
    Bool := Scheduler.complete state

theorem emitted_sound (environment : Environment) (request : Request)
    (state : State environment request) (answer : Answer environment request)
    (_member : answer ∈ state.answers) :
    QueryHolds environment request.context request.relation request.arguments request.initial
      answer.rowIndex answer.assignment := answer.valid.readout

theorem emitted_extension (environment : Environment) (request : Request)
    (answer : Answer environment request) : Extension request.initial answer.assignment :=
  answer.valid.readout.extension

theorem run_add (environment : Environment) (request : Request) (first second : Nat)
    (state : State environment request) :
    run environment request (first + second) state =
      run environment request second (run environment request first state) :=
  Scheduler.run_add _ _ _ _

theorem receipts_prefix (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request) :
    Scheduler.Prefix state.answers (run environment request fuel state).answers :=
  Scheduler.run_answers_prefix _ _ _

theorem work_add (environment : Environment) (request : Request) (first second : Nat)
    (state : State environment request) :
    Scheduler.spent (expand environment request) (first + second) state =
      Scheduler.spent (expand environment request) first state +
      Scheduler.spent (expand environment request) second (run environment request first state) :=
  Scheduler.spent_add _ _ _ _

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
