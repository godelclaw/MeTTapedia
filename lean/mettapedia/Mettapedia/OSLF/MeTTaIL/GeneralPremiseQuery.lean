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

def expandArguments {matcher : MatchingExecution} (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request matcher) :
    Scheduler.Expansion (Task environment request matcher) (Answer environment request matcher) Obligation :=
  match schemasFound : frame.schemas, valuesFound : frame.values, modesFound : frame.modes with
  | [], [], [] =>
      if checked : checkTypedAssignment environment request.context frame.assignment then
        let held : Interpreted.TracedArgumentsHold matcher.meaning request.context frame.index frame.assignment
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
              if same : matcher.acceptsInput (matchingRequest request frame.index frame.assignment schema value) actual then
                { tasks := [.arguments {
                    rowIndex := frame.rowIndex
                    index := frame.index + 1
                    assignment := frame.assignment
                    schemas := schemas
                    values := values
                    modes := modes
                    origins := frame.origins ++ [(frame.index, [])]
                    finish := fun final traces tail typed => by
                      have traced : Interpreted.TracedArgumentsHold matcher.meaning request.context frame.index frame.assignment
                          frame.schemas frame.values frame.modes final ((frame.index, []) :: traces) := by
                        rw [schemasFound, valuesFound, modesFound]
                        exact .input (matcher.input_sound interpreted same) tail
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
              state := matcher.start query
              reachable := matcher.start_reachable query
              cursor := 0
              finish := fun answer valid final traces tail typed => by
                have traced : Interpreted.TracedArgumentsHold matcher.meaning request.context frame.index frame.assignment
                    frame.schemas frame.values frame.modes final ((frame.index, (matcher.trace answer)) :: traces) := by
                  rw [schemasFound, valuesFound, modesFound]
                  exact .output valid tail
                simpa only [List.append_assoc, List.singleton_append] using
                  frame.finish final ((frame.index, (matcher.trace answer)) :: traces) traced typed }] }
  | _, _, _ => { unresolved := [.argumentShape frame.rowIndex frame.index] }

def expandMatcher {matcher : MatchingExecution} (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request matcher) :
    Scheduler.Expansion (Task environment request matcher) (Answer environment request matcher) Obligation :=
  match found : (matcher.answers frame.state)[frame.cursor]? with
  | some answer =>
      have valid : matcher.meaning.Matches frame.query (matcher.trace answer) (matcher.assignment answer) :=
        matcher.answers_sound frame.reachable (List.mem_of_getElem? found)
      { tasks := [
          .arguments {
            rowIndex := frame.rowIndex
            index := frame.argumentIndex + 1
            assignment := (matcher.assignment answer)
            schemas := frame.schemas
            values := frame.values
            modes := frame.modes
            origins := frame.origins ++ [(frame.argumentIndex, (matcher.trace answer))]
            finish := frame.finish answer valid },
          .matcher { frame with cursor := frame.cursor + 1 }] }
  | none =>
      if matcher.complete frame.state then {}
      else
        { tasks := [.matcher { frame with
            state := matcher.tick frame.query frame.state
            reachable := matcher.tick_reachable frame.reachable }] }

def expandDynamicInputs (environment : Environment) (request : Request)
    (frame : DynamicInputsFrame environment request) (matcher : MatchingExecution := MatchingExecution.ordinary) :
    Scheduler.Expansion (Task environment request matcher) (Answer environment request matcher) Obligation :=
  match schemasFound : frame.schemas, modesFound : frame.modes with
  | [], [] =>
      let held : DynamicInputs request.context frame.index request.initial frame.schemas frame.modes [] := by
        rw [schemasFound, modesFound]
        exact .nil
      let inputs : DynamicInputs request.context 0 request.initial request.arguments
          frame.signature.modes frame.resolvedRev.reverse := by
        simpa only [List.append_nil] using frame.finish [] held
      match computed : environment.dynamic.rows? request.relation frame.resolvedRev.reverse with
      | none => { unresolved := [.dynamicUnavailable request.relation] }
      | some rows =>
          { tasks := [.dynamicRows {
              signature := frame.signature
              signatureFound := frame.signatureFound
              registered := frame.registered
              resolved := frame.resolvedRev.reverse
              inputs := inputs
              rows := rows
              source := (environment.dynamic.rows_exact _ _ _).mp computed
              cursor := 0 }] }
  | schema :: schemas, .input :: modes =>
      match interpreted : instantiateAt? request.context.rule request.context.spec
          request.context.bound.length (request.context.site frame.index) [] 0 request.initial schema with
      | none => { unresolved := [.dynamicInputUnavailable frame.index] }
      | some value =>
          { tasks := [.dynamicInputs {
              signature := frame.signature
              signatureFound := frame.signatureFound
              registered := frame.registered
              index := frame.index + 1
              schemas := schemas
              modes := modes
              resolvedRev := value :: frame.resolvedRev
              finish := fun values tail => by
                have whole : DynamicInputs request.context frame.index request.initial
                    frame.schemas frame.modes (value :: values) := by
                  rw [schemasFound, modesFound]
                  exact .input interpreted tail
                simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
                  frame.finish (value :: values) whole }] }
  | schema :: schemas, .output :: modes =>
      { tasks := [.dynamicInputs {
          signature := frame.signature
          signatureFound := frame.signatureFound
          registered := frame.registered
          index := frame.index + 1
          schemas := schemas
          modes := modes
          resolvedRev := schema :: frame.resolvedRev
          finish := fun values tail => by
            have whole : DynamicInputs request.context frame.index request.initial
                frame.schemas frame.modes (schema :: values) := by
              rw [schemasFound, modesFound]
              exact .output tail
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
              frame.finish (schema :: values) whole }] }
  | _, _ => { unresolved := [.dynamicArgumentShape frame.index] }

def expandDynamicRows (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) (matcher : MatchingExecution := MatchingExecution.ordinary) :
    Scheduler.Expansion (Task environment request matcher) (Answer environment request matcher) Obligation :=
  match selected : frame.rows[frame.cursor]? with
  | none => {}
  | some values =>
      let tail := Task.dynamicRows { frame with cursor := frame.cursor + 1 }
      if checked : checkRow environment.language environment.free request.context.bound
          frame.signature ⟨request.relation, values⟩ then
        { tasks := [.arguments {
            rowIndex := environment.provider.rows.length + frame.cursor
            index := 0
            assignment := request.initial
            schemas := request.arguments
            values := values
            modes := frame.signature.modes
            origins := []
            finish := fun final traces held typed => by
              simpa only [List.nil_append] using
                Interpreted.TracedQuery.dynamicRow frame.registered frame.signatureFound frame.inputs frame.source
                  selected (checkRow_sound checked) held typed }, tail] }
      else { tasks := [tail] }

def expand {matcher : MatchingExecution} (environment : Environment) (request : Request) : Task environment request matcher →
    Scheduler.Expansion (Task environment request matcher) (Answer environment request matcher) Obligation
  | .start =>
      match found : signature? environment.provider request.relation request.arguments.length with
      | none => { unresolved := [.signatureUnavailable request.relation request.arguments.length] }
      | some signature =>
          if registered : request.relation ∈ environment.provider.dynamicRelations then
            { tasks := [.rows ⟨signature, found, 0⟩, .dynamicInputs {
                signature := signature
                signatureFound := found
                registered := registered
                index := 0
                schemas := request.arguments
                modes := signature.modes
                resolvedRev := []
                finish := fun values held => by simpa only [List.reverse_nil, List.nil_append] using held }] }
          else { tasks := [.rows ⟨signature, found, 0⟩] }
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
                  simpa using Interpreted.TracedQuery.row found frame.signatureFound (checkRow_sound checked) held typed }, tail] }
          else { tasks := [tail] }
  | .dynamicInputs frame => expandDynamicInputs environment request frame matcher
  | .dynamicRows frame => expandDynamicRows environment request frame matcher
  | .arguments frame => expandArguments environment request frame
  | .matcher frame => expandMatcher environment request frame

def start (environment : Environment) (request : Request)
    (matcher : MatchingExecution := MatchingExecution.ordinary) : State environment request matcher :=
  { agenda := [.start] }

def tick {matcher : MatchingExecution} (environment : Environment) (request : Request) (state : State environment request matcher) :
    State environment request matcher := Scheduler.tick (expand environment request) state

def run {matcher : MatchingExecution} (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request matcher) : State environment request matcher :=
  Scheduler.run (expand environment request) fuel state

def complete {matcher : MatchingExecution} (environment : Environment) (request : Request) (state : State environment request matcher) :
    Bool := Scheduler.complete state

theorem emitted_sound (environment : Environment) (request : Request)
    (state : State environment request) (answer : Answer environment request)
    (_member : answer ∈ state.answers) :
    QueryHolds environment request.context request.relation request.arguments request.initial
      answer.rowIndex answer.assignment := answer.valid.readout

theorem emitted_extension (environment : Environment) (request : Request)
    (answer : Answer environment request) : Extension request.initial answer.assignment :=
  answer.valid.readout.extension

theorem run_add {matcher : MatchingExecution} (environment : Environment) (request : Request) (first second : Nat)
    (state : State environment request matcher) :
    run environment request (first + second) state =
      run environment request second (run environment request first state) :=
  Scheduler.run_add _ _ _ _

theorem receipts_prefix {matcher : MatchingExecution} (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request matcher) :
    Scheduler.Prefix state.answers (run environment request fuel state).answers :=
  Scheduler.run_answers_prefix _ _ _

theorem work_add {matcher : MatchingExecution} (environment : Environment) (request : Request) (first second : Nat)
    (state : State environment request matcher) :
    Scheduler.spent (expand (matcher := matcher) environment request) (first + second) state =
      Scheduler.spent (expand (matcher := matcher) environment request) first state +
      Scheduler.spent (expand (matcher := matcher) environment request) second (run environment request first state) :=
  Scheduler.spent_add _ _ _ _

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
