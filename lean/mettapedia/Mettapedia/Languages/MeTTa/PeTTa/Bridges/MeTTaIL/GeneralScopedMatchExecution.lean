import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.Tasks

/-!
# Native execution of the original general scoped matcher

The task machine preserves ordered answers and each physical bag-choice
history. Its closed finite source support transports the original machine
operations into the common scoped program before premise execution.
-/
section MatcherScheduler
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue
private abbrev MatcherScheduler_taskValue (task : GeneralScopedMatchMachine.Task) : Atom := encoded (matcherTaskTerm task)
private abbrev MatcherScheduler_tasksValue (tasks : List GeneralScopedMatchMachine.Task) : Atom := encoded (encodeList matcherTaskTerm tasks)
private abbrev MatcherScheduler_workValue (work : GeneralScopedMatchMachine.Work) : Atom := encoded (matcherWorkTerm work)
private abbrev MatcherScheduler_worksValue (works : List GeneralScopedMatchMachine.Work) : Atom := encoded (encodeList matcherWorkTerm works)
private abbrev MatcherScheduler_traceValue (trace : List GeneralScopedMatchMachine.BagChoice) : Atom := encoded (traceTerm trace)

private theorem MatcherScheduler_append_encoded_returns {α : Type} (element : α → Term) (caller : Subst) (state : State)
    (left right : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (encodeList element left), encoded (encodeList element right)]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state
      (encoded (encodeList element (left ++ right))) := by
  have captured' : [one, two].map (applySubst caller) =
      [encoded (encodeList id (left.map element)), encoded (encodeList id (right.map element))] := by
    simpa only [encodeList_map, Function.id_comp] using captured
  have returned := matcher_append_captured_returns caller state (left.map element) (right.map element) one two captured'
  change PureReturns program caller state (a "gslt:automata:append" [one, two]) state
    (encoded (encodeList id (left.map element ++ right.map element))) at returned
  rw [← List.map_append, encodeList_map] at returned
  simpa only [Function.id_comp] using returned
private def MatcherScheduler_branchesResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", v "more-tasks", v "more-trace"], v "more"]
private def MatcherScheduler_branchesBody : Atom :=
  a "let*" [.expression
    [.expression [v "more-tasks", a "gslt:automata:append" [v "branch-tasks", v "tasks"]],
      .expression [v "more-trace", a "gslt:automata:append" [v "trace", v "branch-trace"]],
      .expression [v "more", a Helper.branches.head [v "rest", v "tasks", v "trace"]]], MatcherScheduler_branchesResult]
private def MatcherScheduler_branchesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "ScopedMatcherWork" [v "assignment", v "branch-tasks", v "branch-trace"], v "rest"], MatcherScheduler_branchesBody)]
private theorem MatcherScheduler_branches_shape : (equation .branches).body =
    a "case" [v "branches", .expression (MatcherScheduler_branchesCases.map fun row => .expression [row.1, row.2])] := by rfl
private theorem MatcherScheduler_branches_template : PureData.Template program MatcherScheduler_branchesResult := by
  unfold MatcherScheduler_branchesResult
  wire_template

def matcherAdvanceBranchesTerm (branches : List GeneralScopedMatchMachine.Work)
    (tasks : List GeneralScopedMatchMachine.Task) (trace : List GeneralScopedMatchMachine.BagChoice) : Term :=
  .application Helper.branches.head [encodeList matcherWorkTerm branches, encodeList matcherTaskTerm tasks, traceTerm trace]

theorem matcher_advance_branches_returns (state : State) (branches : List GeneralScopedMatchMachine.Work)
    (tasks : List GeneralScopedMatchMachine.Task) (trace : List GeneralScopedMatchMachine.BagChoice) :
    PureReturns program [] state (encoded (matcherAdvanceBranchesTerm branches tasks trace)) state
      (MatcherScheduler_worksValue (branches.map fun branch => ({ assignment := branch.assignment, tasks := branch.tasks ++ tasks, trace := trace ++ branch.trace } : GeneralScopedMatchMachine.Work))) := by
  change PureReturns program [] state (a Helper.branches.head [MatcherScheduler_worksValue branches, MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace]) state _
  induction branches with
  | nil =>
      let caller := environment .branches [MatcherScheduler_worksValue [], MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace]
      apply helper_call .branches [] state _ [MatcherScheduler_worksValue [], MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherScheduler_branches_shape]
      apply case_returns program caller caller state state state (v "branches") (.symbol "LNil")
        (.symbol "LNil") _ _ MatcherScheduler_branchesCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, MatcherScheduler_worksValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "branches"
      · simp [MatcherScheduler_branchesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons branch branches ih =>
      let caller := environment .branches [MatcherScheduler_worksValue (branch :: branches), MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace]
      let selected := ("rest", MatcherScheduler_worksValue branches) :: ("branch-trace", MatcherScheduler_traceValue branch.trace) ::
        ("branch-tasks", MatcherScheduler_tasksValue branch.tasks) :: ("assignment", assignmentValue branch.assignment) :: caller
      let taskBound := ("more-tasks", MatcherScheduler_tasksValue (branch.tasks ++ tasks)) :: selected
      let traceBound := ("more-trace", MatcherScheduler_traceValue (trace ++ branch.trace)) :: taskBound
      let continued := branches.map fun branch => ({ assignment := branch.assignment, tasks := branch.tasks ++ tasks, trace := trace ++ branch.trace } : GeneralScopedMatchMachine.Work)
      let final := ("more", MatcherScheduler_worksValue continued) :: traceBound
      apply helper_call .branches [] state _ [MatcherScheduler_worksValue (branch :: branches), MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherScheduler_branches_shape]
      apply case_returns program caller selected state state state (v "branches") (MatcherScheduler_worksValue (branch :: branches))
        MatcherScheduler_branchesBody _ _ MatcherScheduler_branchesCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "branches"
      · simp [MatcherScheduler_branchesCases, MatcherScheduler_worksValue, matcherWorkTerm, traceTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold MatcherScheduler_branchesBody
        apply PureData.let_bindings_return (final := final)
          (pairs := [(v "more-tasks", a "gslt:automata:append" [v "branch-tasks", v "tasks"]),
            (v "more-trace", a "gslt:automata:append" [v "trace", v "branch-trace"]),
            (v "more", a Helper.branches.head [v "rest", v "tasks", v "trace"])])
        · apply PureData.BindingsReturn.cons (bound := taskBound)
          · apply MatcherScheduler_append_encoded_returns matcherTaskTerm selected state branch.tasks tasks
            simp [selected, caller, environment, Helper.names, MatcherScheduler_tasksValue, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, taskBound, selected, caller,
              environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := traceBound)
            · apply MatcherScheduler_append_encoded_returns bagChoiceTerm taskBound state trace branch.trace
              simp [taskBound, selected, caller, environment, Helper.names, MatcherScheduler_traceValue, traceTerm, applySubst, Subst.lookup]
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, traceBound, taskBound, selected, caller,
                environment, Helper.names, Subst.lookup, traceTerm]
            · apply PureData.BindingsReturn.cons (bound := final)
              · apply helper_capture .branches traceBound state [v "rest", v "tasks", v "trace"]
                  [MatcherScheduler_worksValue branches, MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace] _ rfl
                  (by simp [traceBound, taskBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                exact ih
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, traceBound, taskBound,
                  selected, caller, environment, Helper.names, Subst.lookup, continued]
              · exact .nil _ _
        · simpa [MatcherScheduler_branchesResult, MatcherScheduler_worksValue, matcherWorkTerm, traceTerm, List.map_cons,
            continued, final, traceBound, taskBound, selected, caller, environment, Helper.names,
            MatcherScheduler_tasksValue, MatcherScheduler_traceValue, applySubst, applySubst.applySubstList, Subst.lookup,
            encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program final state MatcherScheduler_branchesResult MatcherScheduler_branches_template

theorem matcher_advance_branches_captured_returns (caller : Subst) (state : State)
    (branches : List GeneralScopedMatchMachine.Work) (tasks : List GeneralScopedMatchMachine.Task)
    (trace : List GeneralScopedMatchMachine.BagChoice) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [MatcherScheduler_worksValue branches, MatcherScheduler_tasksValue tasks, MatcherScheduler_traceValue trace]) :
    PureReturns program caller state (a Helper.branches.head arguments) state
      (MatcherScheduler_worksValue (branches.map fun branch => ({ assignment := branch.assignment, tasks := branch.tasks ++ tasks, trace := trace ++ branch.trace } : GeneralScopedMatchMachine.Work))) :=
  helper_capture .branches caller state arguments _ _ rfl captured (matcher_advance_branches_returns state branches tasks trace)


private def MatcherScheduler_advanceBody : Atom :=
  a "let" [v "branches", a Helper.expand.head [v "request", v "assignment", v "task"],
    a Helper.branches.head [v "branches", v "rest", v "trace"]]
private def MatcherScheduler_advanceTasksCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "task", v "rest"], MatcherScheduler_advanceBody)]
private def MatcherScheduler_advanceCases : SpaceSemantics.Cases :=
  [(a "ScopedMatcherWork" [v "assignment", v "tasks", v "trace"],
    a "case" [v "tasks", .expression (MatcherScheduler_advanceTasksCases.map fun row => .expression [row.1, row.2])])]
private theorem MatcherScheduler_advance_shape : (equation .advance).body =
    a "case" [v "work", .expression (MatcherScheduler_advanceCases.map fun row => .expression [row.1, row.2])] := by rfl

def matcherAdvanceTerm (request : GeneralScopedMatchMachine.Request) (work : GeneralScopedMatchMachine.Work) : Term :=
  .application Helper.advance.head [matcherRequestTerm request, matcherWorkTerm work]

theorem matcher_advance_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (work : GeneralScopedMatchMachine.Work) :
    PureReturns program [] state (encoded (matcherAdvanceTerm request work)) state
      (MatcherScheduler_worksValue (GeneralScopedMatchMachine.advance request work)) := by
  let caller := environment .advance [requestValue request, MatcherScheduler_workValue work]
  let picked := ("trace", MatcherScheduler_traceValue work.trace) :: ("tasks", MatcherScheduler_tasksValue work.tasks) ::
    ("assignment", assignmentValue work.assignment) :: caller
  change PureReturns program [] state (a Helper.advance.head [requestValue request, MatcherScheduler_workValue work]) state _
  apply helper_call .advance [] state _ [requestValue request, MatcherScheduler_workValue work] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [MatcherScheduler_advance_shape]
  apply case_returns program caller picked state state state (v "work") (MatcherScheduler_workValue work)
    (a "case" [v "tasks", .expression (MatcherScheduler_advanceTasksCases.map fun row => .expression [row.1, row.2])])
    _ _ MatcherScheduler_advanceCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "work"
  · simp [MatcherScheduler_advanceCases, MatcherScheduler_workValue, matcherWorkTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, environment, Helper.names, Subst.lookup]
  · cases tasksFound : work.tasks with
    | nil =>
        apply case_returns program picked picked state state state (v "tasks") (.symbol "LNil")
          (.symbol "LNil") _ _ MatcherScheduler_advanceTasksCases (read_cases_encoded _)
        · simpa [picked, tasksFound, MatcherScheduler_tasksValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
            variable_returns program picked state "tasks"
        · simp [MatcherScheduler_advanceTasksCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa only [GeneralScopedMatchMachine.advance, tasksFound, MatcherScheduler_worksValue, encodeList, CettaWireAtom.encode] using
            symbol_returns program picked state "LNil"
    | cons task tasks =>
        let selected := ("rest", MatcherScheduler_tasksValue tasks) :: ("task", MatcherScheduler_taskValue task) :: picked
        let branches := GeneralScopedMatchMachine.expand request work.assignment task
        let branchBound := ("branches", MatcherScheduler_worksValue branches) :: selected
        apply case_returns program picked selected state state state (v "tasks") (MatcherScheduler_tasksValue (task :: tasks))
          MatcherScheduler_advanceBody _ _ MatcherScheduler_advanceTasksCases (read_cases_encoded _)
        · simpa [picked, tasksFound, applySubst, Subst.lookup] using variable_returns program picked state "tasks"
        · simp [MatcherScheduler_advanceTasksCases, MatcherScheduler_tasksValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, selected, picked, caller, environment, Helper.names, Subst.lookup]
        · unfold MatcherScheduler_advanceBody
          apply named_let_returns selected state "branches" _ (MatcherScheduler_worksValue branches)
          · simp [selected, picked, caller, environment, Helper.names, Subst.lookup]
          · apply matcher_expand_captured_returns selected state request work.assignment task
            simp [selected, picked, caller, environment, Helper.names, applySubst, Subst.lookup]
          · have returned := matcher_advance_branches_captured_returns branchBound state branches tasks work.trace
              [v "branches", v "rest", v "trace"]
              (by simp [branchBound, selected, picked, caller, environment, Helper.names, applySubst, Subst.lookup])
            simpa only [GeneralScopedMatchMachine.advance, tasksFound, branches] using returned

theorem matcher_advance_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (work : GeneralScopedMatchMachine.Work) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [requestValue request, MatcherScheduler_workValue work]) :
    PureReturns program caller state (a Helper.advance.head arguments) state
      (MatcherScheduler_worksValue (GeneralScopedMatchMachine.advance request work)) :=
  helper_capture .advance caller state arguments _ _ rfl captured (matcher_advance_returns state request work)


private abbrev MatcherScheduler_answersValue (answers : List GeneralScopedMatchMachine.Answer) : Atom := encoded (encodeList matcherAnswerTerm answers)
private def MatcherScheduler_tickEmitResult : Atom := a "ScopedMatcherState" [v "rest", v "more-answers"]
private def MatcherScheduler_tickEmitBody : Atom :=
  a "let" [v "more-answers", a "gslt:automata:append"
    [v "answers", a "LCons" [a "ScopedMatcherAnswer" [v "assignment", v "trace"], .symbol "LNil"]], MatcherScheduler_tickEmitResult]
private def MatcherScheduler_tickContinueResult : Atom := a "ScopedMatcherState" [v "more", v "answers"]
private def MatcherScheduler_tickContinueBody : Atom :=
  a "let" [v "branches", a Helper.advance.head
    [v "request", a "ScopedMatcherWork" [v "assignment", v "tasks", v "trace"]],
      a "let" [v "more", a "gslt:automata:append" [v "branches", v "rest"], MatcherScheduler_tickContinueResult]]
private def MatcherScheduler_tickTasksCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", MatcherScheduler_tickEmitBody), (a "LCons" [v "task", v "tail"], MatcherScheduler_tickContinueBody)]
private def MatcherScheduler_tickAgendaCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "state"),
    (a "LCons" [a "ScopedMatcherWork" [v "assignment", v "tasks", v "trace"], v "rest"],
      a "case" [v "tasks", .expression (MatcherScheduler_tickTasksCases.map fun row => .expression [row.1, row.2])])]
private def MatcherScheduler_tickCases : SpaceSemantics.Cases :=
  [(a "ScopedMatcherState" [v "agenda", v "answers"],
    a "case" [v "agenda", .expression (MatcherScheduler_tickAgendaCases.map fun row => .expression [row.1, row.2])])]
private theorem MatcherScheduler_tick_shape : (equation .tick).body =
    a "case" [v "state", .expression (MatcherScheduler_tickCases.map fun row => .expression [row.1, row.2])] := by rfl
private theorem MatcherScheduler_tick_emit_template : PureData.Template program MatcherScheduler_tickEmitResult := by
  unfold MatcherScheduler_tickEmitResult
  wire_template
private theorem MatcherScheduler_tick_continue_template : PureData.Template program MatcherScheduler_tickContinueResult := by
  unfold MatcherScheduler_tickContinueResult
  wire_template

theorem matcher_tick_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) :
    PureReturns program [] state (encoded (matcherTickTerm request machine)) state
      (stateValue (GeneralScopedMatchMachine.tick request machine)) := by
  let caller := environment .tick [requestValue request, stateValue machine]
  let picked := ("answers", MatcherScheduler_answersValue machine.answers) :: ("agenda", MatcherScheduler_worksValue machine.agenda) :: caller
  change PureReturns program [] state (a Helper.tick.head [requestValue request, stateValue machine]) state _
  apply helper_call .tick [] state _ [requestValue request, stateValue machine] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [MatcherScheduler_tick_shape]
  apply case_returns program caller picked state state state (v "state") (stateValue machine)
    (a "case" [v "agenda", .expression (MatcherScheduler_tickAgendaCases.map fun row => .expression [row.1, row.2])])
    _ _ MatcherScheduler_tickCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "state"
  · simp [MatcherScheduler_tickCases, matcherStateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, environment, Helper.names, Subst.lookup]
  · cases agendaFound : machine.agenda with
    | nil =>
        apply case_returns program picked picked state state state (v "agenda") (.symbol "LNil")
          (v "state") _ _ MatcherScheduler_tickAgendaCases (read_cases_encoded _)
        · simpa [picked, agendaFound, MatcherScheduler_worksValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
            variable_returns program picked state "agenda"
        · simp [MatcherScheduler_tickAgendaCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [GeneralScopedMatchMachine.tick, agendaFound, picked, caller, environment, Helper.names,
            applySubst, Subst.lookup] using variable_returns program picked state "state"
    | cons work agenda =>
        let selected := ("rest", MatcherScheduler_worksValue agenda) :: ("trace", MatcherScheduler_traceValue work.trace) ::
          ("tasks", MatcherScheduler_tasksValue work.tasks) :: ("assignment", assignmentValue work.assignment) :: picked
        apply case_returns program picked selected state state state (v "agenda") (MatcherScheduler_worksValue (work :: agenda))
          (a "case" [v "tasks", .expression (MatcherScheduler_tickTasksCases.map fun row => .expression [row.1, row.2])])
          _ _ MatcherScheduler_tickAgendaCases (read_cases_encoded _)
        · simpa [picked, agendaFound, applySubst, Subst.lookup] using variable_returns program picked state "agenda"
        · simp [MatcherScheduler_tickAgendaCases, MatcherScheduler_worksValue, matcherWorkTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, selected, picked, caller, environment, Helper.names, Subst.lookup]
        · cases tasksFound : work.tasks with
          | nil =>
              let answer : GeneralScopedMatchMachine.Answer := { assignment := work.assignment, trace := work.trace }
              let final := ("more-answers", MatcherScheduler_answersValue (machine.answers ++ [answer])) :: selected
              apply case_returns program selected selected state state state (v "tasks") (.symbol "LNil")
                MatcherScheduler_tickEmitBody _ _ MatcherScheduler_tickTasksCases (read_cases_encoded _)
              · simpa [selected, tasksFound, MatcherScheduler_tasksValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
                  variable_returns program selected state "tasks"
              · simp [MatcherScheduler_tickTasksCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · unfold MatcherScheduler_tickEmitBody
                apply named_let_returns selected state "more-answers" _ (MatcherScheduler_answersValue (machine.answers ++ [answer]))
                · simp [selected, picked, caller, environment, Helper.names, Subst.lookup]
                · apply MatcherScheduler_append_encoded_returns matcherAnswerTerm selected state machine.answers [answer]
                  simp [selected, picked, caller, environment, Helper.names, MatcherScheduler_answersValue,
                    answer, matcherAnswerTerm, MatcherScheduler_traceValue, applySubst, applySubst.applySubstList, Subst.lookup,
                    encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
                · simpa [MatcherScheduler_tickEmitResult, GeneralScopedMatchMachine.tick, agendaFound, tasksFound, answer,
                    matcherStateTerm, final, selected, picked, caller, environment, Helper.names,
                    MatcherScheduler_answersValue, MatcherScheduler_worksValue, applySubst, applySubst.applySubstList, Subst.lookup,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    PureData.template_return program final state MatcherScheduler_tickEmitResult MatcherScheduler_tick_emit_template
          | cons task tasks =>
              let taskBound := ("tail", MatcherScheduler_tasksValue tasks) :: ("task", MatcherScheduler_taskValue task) :: selected
              let branches := GeneralScopedMatchMachine.advance request work
              let branchBound := ("branches", MatcherScheduler_worksValue branches) :: taskBound
              let final := ("more", MatcherScheduler_worksValue (branches ++ agenda)) :: branchBound
              apply case_returns program selected taskBound state state state (v "tasks") (MatcherScheduler_tasksValue (task :: tasks))
                MatcherScheduler_tickContinueBody _ _ MatcherScheduler_tickTasksCases (read_cases_encoded _)
              · simpa [selected, tasksFound, applySubst, Subst.lookup] using variable_returns program selected state "tasks"
              · simp [MatcherScheduler_tickTasksCases, MatcherScheduler_tasksValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, taskBound, selected, picked, caller, environment, Helper.names, Subst.lookup]
              · unfold MatcherScheduler_tickContinueBody
                apply named_let_returns taskBound state "branches" _ (MatcherScheduler_worksValue branches)
                · simp [taskBound, selected, picked, caller, environment, Helper.names, Subst.lookup]
                · apply matcher_advance_captured_returns taskBound state request work
                  simp [taskBound, selected, picked, caller, environment, Helper.names, MatcherScheduler_workValue, matcherWorkTerm,
                    MatcherScheduler_tasksValue, MatcherScheduler_traceValue, applySubst, applySubst.applySubstList, Subst.lookup,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany]
                · apply named_let_returns branchBound state "more" _ (MatcherScheduler_worksValue (branches ++ agenda))
                  · simp [branchBound, taskBound, selected, picked, caller, environment, Helper.names, Subst.lookup]
                  · apply MatcherScheduler_append_encoded_returns matcherWorkTerm branchBound state branches agenda
                    simp [branchBound, taskBound, selected, picked, caller, environment, Helper.names,
                      MatcherScheduler_worksValue, applySubst, Subst.lookup]
                  · simpa [MatcherScheduler_tickContinueResult, GeneralScopedMatchMachine.tick, agendaFound, tasksFound, branches,
                      matcherStateTerm, final, branchBound, taskBound, selected, picked, caller, environment, Helper.names,
                      MatcherScheduler_answersValue, MatcherScheduler_worksValue, applySubst, applySubst.applySubstList, Subst.lookup,
                      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return program final state MatcherScheduler_tickContinueResult MatcherScheduler_tick_continue_template

theorem matcher_tick_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (machine : GeneralScopedMatchMachine.State) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [requestValue request, stateValue machine]) :
    PureReturns program caller state (a Helper.tick.head arguments) state
      (stateValue (GeneralScopedMatchMachine.tick request machine)) :=
  helper_capture .tick caller state arguments _ _ rfl captured (matcher_tick_returns state request machine)


private def MatcherScheduler_runBody : Atom :=
  a "let" [v "next", a Helper.tick.head [v "request", v "state"],
    a "let" [v "remaining", a "-" [v "fuel", number 1], a Helper.run.head [v "request", v "remaining", v "next"]]]
private theorem MatcherScheduler_run_shape : (equation .run).body =
    a "if" [a "==" [v "fuel", number 0], v "state", MatcherScheduler_runBody] := by rfl

theorem matcher_run_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (fuel : Nat) (machine : GeneralScopedMatchMachine.State) :
    PureReturns program [] state (encoded (matcherRunTerm request fuel machine)) state
      (stateValue (GeneralScopedMatchMachine.run request fuel machine)) := by
  change PureReturns program [] state (a Helper.run.head [requestValue request, number fuel, stateValue machine]) state _
  induction fuel generalizing machine with
  | zero =>
      let caller := environment .run [requestValue request, number 0, stateValue machine]
      apply helper_call .run [] state _ [requestValue request, number 0, stateValue machine] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherScheduler_run_shape]
      have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural 0) (.natural 0)
        (v "fuel") (number 0) (by decide +kernel) (by decide +kernel)
        (by simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "fuel")
        (grounded_returns program caller state (.int 0))
      simp only [decide_true] at tested
      apply bool_if_returns caller state _ true _ _ _ tested
      simpa [GeneralScopedMatchMachine.run, caller, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns program caller state "state"
  | succ fuel ih =>
      let caller := environment .run [requestValue request, number (fuel + 1), stateValue machine]
      let nextMachine := GeneralScopedMatchMachine.tick request machine
      let next := ("next", stateValue nextMachine) :: caller
      let remaining := ("remaining", number fuel) :: next
      apply helper_call .run [] state _ [requestValue request, number (fuel + 1), stateValue machine] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherScheduler_run_shape]
      have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural (fuel + 1)) (.natural 0)
        (v "fuel") (number 0) (by decide +kernel) (by decide +kernel)
        (by simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "fuel")
        (grounded_returns program caller state (.int 0))
      simp only [Term.natural.injEq, Nat.add_one_ne_zero, decide_false] at tested
      apply bool_if_returns caller state _ false _ _ _ tested
      change PureReturns program caller state MatcherScheduler_runBody state _
      unfold MatcherScheduler_runBody
      apply named_let_returns caller state "next" _ (stateValue nextMachine)
      · simp [caller, environment, Helper.names, Subst.lookup]
      · apply matcher_tick_captured_returns caller state request machine
        simp [caller, environment, Helper.names, applySubst, Subst.lookup]
      · apply named_let_returns next state "remaining" _ (number fuel)
        · simp [next, caller, environment, Helper.names, Subst.lookup]
        · apply native_binary_call_returns program next state state state state "-"
            (v "fuel") (number 1) (number (fuel + 1)) (number 1) (number fuel)
            (by decide) (by decide) (by decide +kernel) (by decide +kernel)
          · simpa [next, caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program next state "fuel"
          · exact grounded_returns program next state (.int 1)
          · change (Except.ok (state, [Atom.grounded (.int (((fuel + 1 : Nat) : Int) - 1))]) : Effects.Result) =
                Except.ok (state, [.grounded (.int (fuel : Int))])
            simp
          · decide
        · apply helper_capture .run remaining state [v "request", v "remaining", v "next"]
            [requestValue request, number fuel, stateValue nextMachine] _ rfl
            (by simp [remaining, next, caller, environment, Helper.names, applySubst, Subst.lookup])
          exact ih nextMachine

theorem matcher_run_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (fuel : Nat) (machine : GeneralScopedMatchMachine.State)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [requestValue request, number fuel, stateValue machine]) :
    PureReturns program caller state (a Helper.run.head arguments) state
      (stateValue (GeneralScopedMatchMachine.run request fuel machine)) :=
  helper_capture .run caller state arguments _ _ rfl captured (matcher_run_returns state request fuel machine)

theorem matcher_tick_completed_iff (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel { state := state, control := .evaluate [] (encoded (matcherTickTerm request machine)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [stateValue (GeneralScopedMatchMachine.tick request machine)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (matcher_tick_returns state request machine) after answers input output

theorem matcher_run_completed_iff (state : State) (request : GeneralScopedMatchMachine.Request)
    (fuel : Nat) (machine : GeneralScopedMatchMachine.State) (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run program evaluatorFuel { state := state, control := .evaluate [] (encoded (matcherRunTerm request fuel machine)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [stateValue (GeneralScopedMatchMachine.run request fuel machine)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (matcher_run_returns state request fuel machine) after answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherScheduler


section MatcherTransport
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.MachineTransport

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

def executionHeadNames : List String :=
  ["+",
   "-",
   "<",
   "==",
   ">=",
   "BagChoice",
   "Binding",
   "Congruence",
   "ContextualValue",
   "FVar",
   "ForAll",
   "Freshness",
   "LCons",
   "LNil",
   "None",
   "OccurrenceAssignment",
   "PApp",
   "PCollection",
   "PLam",
   "PMultiLam",
   "PSubst",
   "RNone",
   "RSome",
   "RecoveryAssignment",
   "RelationQuery",
   "RuleBindingSpec",
   "RuleDependency",
   "RuleLeft",
   "RuleOccurrence",
   "RulePremise",
   "RuleRight",
   "ScopedMatcherAnswer",
   "ScopedMatcherArguments",
   "ScopedMatcherBag",
   "ScopedMatcherBagSelect",
   "ScopedMatcherRequest",
   "ScopedMatcherRestCapture",
   "ScopedMatcherSplit",
   "ScopedMatcherState",
   "ScopedMatcherTree",
   "ScopedMatcherWork",
   "ScopedRewriteRuleV1",
   "ScopedStep",
   "Some",
   "Var",
   "case",
   "gslt:automata:append",
   "gslt:automata:binding",
   "gslt:automata:length",
   "gslt:automata:member",
   "gslt:rule:lift-bvars",
   "gslt:rule:lift-bvars-list",
   "gslt:rule:row-at",
   "gslt:rule:scope-assign",
   "gslt:rule:scope-assignment",
   "gslt:rule:scope-index",
   "gslt:rule:scope-instantiate-value",
   "gslt:rule:scope-match-erase-at",
   "gslt:rule:scope-matcher-advance",
   "gslt:rule:scope-matcher-advance-branches",
   "gslt:rule:scope-matcher-capture",
   "gslt:rule:scope-matcher-captured-work",
   "gslt:rule:scope-matcher-complete",
   "gslt:rule:scope-matcher-expand",
   "gslt:rule:scope-matcher-expand-tree",
   "gslt:rule:scope-matcher-run",
   "gslt:rule:scope-matcher-split-at",
   "gslt:rule:scope-matcher-start",
   "gslt:rule:scope-matcher-tick",
   "gslt:rule:scope-metadata-arguments",
   "gslt:rule:scope-metadata-dependencies",
   "gslt:rule:scope-metadata-dependency-rows",
   "gslt:rule:scope-metadata-occurrence-declared",
   "gslt:rule:scope-metadata-occurrence-name",
   "gslt:rule:scope-metadata-occurrence-rows",
   "gslt:rule:scope-metadata-premise-pattern",
   "gslt:rule:scope-metadata-quantified-body",
   "gslt:rule:scope-metadata-site-pattern",
   "gslt:rule:scope-metadata-site-premise",
   "gslt:rule:scope-recover-value",
   "gslt:rule:scope-substitute",
   "gslt:rule:scope-substitute-list",
   "gslt:rule:scope-variable-spine",
   "gslt:rule:scope-well-scoped",
   "gslt:rule:scope-well-scoped-list",
   "if",
   "let",
   "let*"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

theorem program_closed : ProgramClosed executionHeads program := by
  constructor
  · rfl
  · intro equation member supported
    have checked : program.equations.all (fun equation =>
        !executionHeads equation.head || codeWithin executionHeads equation.body) = true := by rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row


theorem matcher_start_variables_returns_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (name : String)
    (captured : applySubst caller (v name) = requestValue request) :
    PureReturns target caller state (a Helper.start.head [v name]) state
      (stateValue (GeneralScopedMatchMachine.start request)) :=
  path_of_closed_agreement program_closed agreement ⟨by rfl, rfl⟩
    (matcher_start_captured_returns caller state request (v name) captured)

theorem matcher_complete_variables_returns_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (machine : GeneralScopedMatchMachine.State) (name : String)
    (captured : applySubst caller (v name) = stateValue machine) :
    PureReturns target caller state (a Helper.complete.head [v name]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) :=
  path_of_closed_agreement program_closed agreement ⟨by rfl, rfl⟩
    (matcher_complete_captured_returns caller state machine (v name) captured)

theorem matcher_expand_variables_returns_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (assignment : Assignment) (task : GeneralScopedMatchMachine.Task)
    (requestName assignmentName taskName : String)
    (captured : [v requestName, v assignmentName, v taskName].map (applySubst caller) =
      [requestValue request, assignmentValue assignment, encoded (matcherTaskTerm task)]) :
    PureReturns target caller state (a Helper.expand.head [v requestName, v assignmentName, v taskName]) state
      (encoded (encodeList matcherWorkTerm (GeneralScopedMatchMachine.expand request assignment task))) :=
  path_of_closed_agreement program_closed agreement ⟨by rfl, rfl⟩
    (matcher_expand_captured_returns caller state request assignment task _ captured)

theorem matcher_tick_variables_returns_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (machine : GeneralScopedMatchMachine.State)
    (requestName stateName : String)
    (captured : [v requestName, v stateName].map (applySubst caller) = [requestValue request, stateValue machine]) :
    PureReturns target caller state (a Helper.tick.head [v requestName, v stateName]) state
      (stateValue (GeneralScopedMatchMachine.tick request machine)) :=
  path_of_closed_agreement program_closed agreement ⟨by rfl, rfl⟩
    (matcher_tick_captured_returns caller state request machine _ captured)

theorem matcher_run_variables_returns_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (fuel : Nat) (machine : GeneralScopedMatchMachine.State)
    (requestName fuelName stateName : String)
    (captured : [v requestName, v fuelName, v stateName].map (applySubst caller) =
      [requestValue request, number fuel, stateValue machine]) :
    PureReturns target caller state (a Helper.run.head [v requestName, v fuelName, v stateName]) state
      (stateValue (GeneralScopedMatchMachine.run request fuel machine)) :=
  path_of_closed_agreement program_closed agreement ⟨by rfl, rfl⟩
    (matcher_run_captured_returns caller state request fuel machine _ captured)

theorem matcher_start_variables_completed_iff_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (name : String)
    (captured : applySubst caller (v name) = requestValue request)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run target fuel { state := state, control := .evaluate caller (a Helper.start.head [v name]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [stateValue (GeneralScopedMatchMachine.start request)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (matcher_start_variables_returns_in_extension target agreement caller state request name captured) after answers input output

theorem matcher_complete_variables_completed_iff_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (machine : GeneralScopedMatchMachine.State) (name : String)
    (captured : applySubst caller (v name) = stateValue machine)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run target fuel { state := state, control := .evaluate caller (a Helper.complete.head [v name]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [Effects.boolean (GeneralScopedMatchMachine.complete machine)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (matcher_complete_variables_returns_in_extension target agreement caller state machine name captured) after answers input output

theorem matcher_expand_variables_completed_iff_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (assignment : Assignment) (task : GeneralScopedMatchMachine.Task)
    (requestName assignmentName taskName : String)
    (captured : [v requestName, v assignmentName, v taskName].map (applySubst caller) =
      [requestValue request, assignmentValue assignment, encoded (matcherTaskTerm task)])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run target fuel { state := state, control := .evaluate caller (a Helper.expand.head [v requestName, v assignmentName, v taskName]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeList matcherWorkTerm (GeneralScopedMatchMachine.expand request assignment task))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (matcher_expand_variables_returns_in_extension target agreement caller state request assignment task
      requestName assignmentName taskName captured) after answers input output

theorem matcher_tick_variables_completed_iff_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (machine : GeneralScopedMatchMachine.State)
    (requestName stateName : String)
    (captured : [v requestName, v stateName].map (applySubst caller) = [requestValue request, stateValue machine])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run target fuel { state := state, control := .evaluate caller (a Helper.tick.head [v requestName, v stateName]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [stateValue (GeneralScopedMatchMachine.tick request machine)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (matcher_tick_variables_returns_in_extension target agreement caller state request machine
      requestName stateName captured) after answers input output

theorem matcher_run_variables_completed_iff_in_extension (target : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program target) (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (fuel : Nat) (machine : GeneralScopedMatchMachine.State)
    (requestName fuelName stateName : String)
    (captured : [v requestName, v fuelName, v stateName].map (applySubst caller) =
      [requestValue request, number fuel, stateValue machine])
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run target evaluatorFuel { state := state, control := .evaluate caller (a Helper.run.head [v requestName, v fuelName, v stateName]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [stateValue (GeneralScopedMatchMachine.run request fuel machine)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (matcher_run_variables_returns_in_extension target agreement caller state request fuel machine
      requestName fuelName stateName captured) after answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.MachineTransport
end MatcherTransport


section MatcherMechanical
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.Mechanical

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval GeneralScopedMatchExecution MachineProofs

abbrev termListValue (values : List Term) : Atom := encoded (encodeList id values)

private inductive MatcherMechanical_Operation where | row | length | append | start | tick | complete

private def MatcherMechanical_Operation.head : MatcherMechanical_Operation → String
  | .row => "gslt:rule:row-at"
  | .length => "gslt:automata:length"
  | .append => "gslt:automata:append"
  | .start => "gslt:rule:scope-matcher-start"
  | .tick => "gslt:rule:scope-matcher-tick"
  | .complete => "gslt:rule:scope-matcher-complete"

private def MatcherMechanical_Operation.names : MatcherMechanical_Operation → List String
  | .row => ["index", "values"]
  | .length => ["values"]
  | .append => ["left", "right"]
  | .start => ["request"]
  | .tick => ["request", "state"]
  | .complete => ["state"]

private theorem MatcherMechanical_operation_supported (operation : MatcherMechanical_Operation) :
    RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads operation.head = true := by
  cases operation <;> decide

private theorem MatcherMechanical_transport_captured (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (operation : MatcherMechanical_Operation) (first caller : Subst) (state : State) (arguments : List Atom) (answer : Atom)
    (captured : (operation.names.map v).map (applySubst first) = arguments.map (applySubst caller))
    (returned : PureReturns GeneralScopedMatchExecution.program first state
      (a operation.head (operation.names.map v)) state answer) :
    PureReturns runtime caller state (a operation.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime first caller state state operation.head
    (operation.names.map v) arguments answer
  · rw [← agreement.dispatch operation.head (MatcherMechanical_operation_supported operation)]
    cases operation <;> decide +kernel
  · intro index bounded
    rw [← agreement.demand operation.head index (MatcherMechanical_operation_supported operation)]
    cases operation <;> simp only [MatcherMechanical_Operation.names, List.length_map, List.length_cons, List.length_nil] at bounded
    all_goals
      have small : index = 0 ∨ index = 1 := by omega
      rcases small with rfl | rfl <;> first | omega | decide +kernel
  · cases operation <;> decide
  · exact captured
  · apply path_of_closed_agreement
      RuleInstantiationExecution.GeneralExecution.MachineTransport.program_closed agreement _ returned
    constructor
    · change codeWithin RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
        (a operation.head (operation.names.map v)) = true
      cases operation <;> decide
    · rfl

theorem row_returns_in_extension (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (caller : Subst) (state : State) (index : Nat) (values : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, termListValue values]) :
    PureReturns runtime caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption id values[index]?)) := by
  let first : Subst := [("values", termListValue values), ("index", number index)]
  apply MatcherMechanical_transport_captured runtime agreement .row first caller state [one, two]
  · simpa [MatcherMechanical_Operation.names, first, v, applySubst, Subst.lookup] using captured.symm
  · have computed := RuleInstantiationExecution.GeneralExecution.matcher_row_captured_returns first state index values
      (v "index") (v "values") (by simp [first, applySubst, Subst.lookup])
    have same : MatchAutomataBindingExecution.payloadOptionTerm values[index]? = encodeOption id values[index]? := by
      cases values[index]? <;> rfl
    simpa only [same, MatcherMechanical_Operation.head, MatcherMechanical_Operation.names, List.map_cons, List.map_nil] using computed

theorem length_returns_in_extension (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (caller : Subst) (state : State) (values : List Term) (input : Atom)
    (captured : applySubst caller input = termListValue values) :
    PureReturns runtime caller state (a "gslt:automata:length" [input]) state (number values.length) := by
  let first : Subst := [("values", termListValue values)]
  apply MatcherMechanical_transport_captured runtime agreement .length first caller state [input]
  · simp [MatcherMechanical_Operation.names, first, v, applySubst, Subst.lookup, captured]
  · exact RuleInstantiationExecution.GeneralExecution.matcher_length_captured_returns first state values
      (v "values") (by simp [first, applySubst, Subst.lookup])

theorem append_returns_in_extension (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (caller : Subst) (state : State) (left right : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [termListValue left, termListValue right]) :
    PureReturns runtime caller state (a "gslt:automata:append" [one, two]) state (termListValue (left ++ right)) := by
  let first : Subst := [("right", termListValue right), ("left", termListValue left)]
  apply MatcherMechanical_transport_captured runtime agreement .append first caller state [one, two]
  · simpa [MatcherMechanical_Operation.names, first, v, applySubst, Subst.lookup] using captured.symm
  · exact RuleInstantiationExecution.GeneralExecution.matcher_append_captured_returns first state left right
      (v "left") (v "right") (by simp [first, v, applySubst, Subst.lookup])

theorem start_returns_in_extension (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request) (input : Atom)
    (captured : applySubst caller input = requestValue request) :
    PureReturns runtime caller state (a "gslt:rule:scope-matcher-start" [input]) state
      (stateValue (GeneralScopedMatchMachine.start request)) := by
  let first : Subst := [("request", requestValue request)]
  apply MatcherMechanical_transport_captured runtime agreement .start first caller state [input]
  · simp [MatcherMechanical_Operation.names, first, v, applySubst, Subst.lookup, captured]
  · exact RuleInstantiationExecution.GeneralExecution.matcher_start_captured_returns first state request
      (v "request") (by simp [first, applySubst, Subst.lookup])

theorem tick_returns_in_extension (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [requestValue request, stateValue machine]) :
    PureReturns runtime caller state (a "gslt:rule:scope-matcher-tick" [one, two]) state
      (stateValue (GeneralScopedMatchMachine.tick request machine)) := by
  let first : Subst := [("state", stateValue machine), ("request", requestValue request)]
  apply MatcherMechanical_transport_captured runtime agreement .tick first caller state [one, two]
  · simpa [MatcherMechanical_Operation.names, first, v, applySubst, Subst.lookup] using captured.symm
  · exact RuleInstantiationExecution.GeneralExecution.matcher_tick_captured_returns first state request machine
      [v "request", v "state"] (by simp [first, v, applySubst, Subst.lookup])

theorem complete_returns_in_extension (runtime : Program)
    (agreement : ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program runtime)
    (caller : Subst) (state : State) (machine : GeneralScopedMatchMachine.State) (input : Atom)
    (captured : applySubst caller input = stateValue machine) :
    PureReturns runtime caller state (a "gslt:rule:scope-matcher-complete" [input]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  let first : Subst := [("state", stateValue machine)]
  apply MatcherMechanical_transport_captured runtime agreement .complete first caller state [input]
  · simp [MatcherMechanical_Operation.names, first, v, applySubst, Subst.lookup, captured]
  · exact RuleInstantiationExecution.GeneralExecution.matcher_complete_captured_returns first state machine
      (v "state") (by simp [first, applySubst, Subst.lookup])


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.Mechanical
end MatcherMechanical


section MatcherAssembly
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.Mechanical

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

theorem matcher_retained_equations :
    GeneralScopedMatchExecution.program.equations.filter
      (fun equation => RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter
      (fun equation => RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads equation.head) := by
  rfl

theorem matcher_retained_declarations :
    GeneralScopedMatchExecution.program.declarations.filter
      (retainedCallDeclaration RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter
      (retainedCallDeclaration RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads) := by
  rfl

theorem matcher_agreement :
    ProgramAgreementOn RuleInstantiationExecution.GeneralExecution.MachineTransport.executionHeads
      GeneralScopedMatchExecution.program RuleExecutionProgram.scopedMachineProgram :=
  programAgreementOn_of_retained_rows _ _ _ matcher_retained_equations matcher_retained_declarations

theorem row_returns (caller : Subst) (state : State) (index : Nat) (values : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, termListValue values]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption id values[index]?)) :=
  row_returns_in_extension RuleExecutionProgram.scopedMachineProgram matcher_agreement caller state index values one two captured

theorem length_returns (caller : Subst) (state : State) (values : List Term) (input : Atom)
    (captured : applySubst caller input = termListValue values) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:length" [input]) state (number values.length) :=
  length_returns_in_extension RuleExecutionProgram.scopedMachineProgram matcher_agreement caller state values input captured

theorem append_returns (caller : Subst) (state : State) (left right : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [termListValue left, termListValue right]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:append" [one, two]) state (termListValue (left ++ right)) :=
  append_returns_in_extension RuleExecutionProgram.scopedMachineProgram matcher_agreement caller state left right one two captured

theorem start_returns (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request) (input : Atom)
    (captured : applySubst caller input = requestValue request) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-matcher-start" [input]) state
      (stateValue (GeneralScopedMatchMachine.start request)) :=
  start_returns_in_extension RuleExecutionProgram.scopedMachineProgram matcher_agreement caller state request input captured

theorem tick_returns (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [requestValue request, stateValue machine]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-matcher-tick" [one, two]) state
      (stateValue (GeneralScopedMatchMachine.tick request machine)) :=
  tick_returns_in_extension RuleExecutionProgram.scopedMachineProgram matcher_agreement caller state request machine one two captured

theorem complete_returns (caller : Subst) (state : State) (machine : GeneralScopedMatchMachine.State) (input : Atom)
    (captured : applySubst caller input = stateValue machine) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-matcher-complete" [input]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) :=
  complete_returns_in_extension RuleExecutionProgram.scopedMachineProgram matcher_agreement caller state machine input captured


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.Mechanical
end MatcherAssembly


section MatcherCompletedAssembly
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.Mechanical
open Eval

theorem matcher_completed_retained_equations :
    GeneralScopedMatchExecution.program.equations.filter
      (fun equation => MachineTransport.executionHeads equation.head) =
    RuleExecutionProgram.scopedProgram.equations.filter
      (fun equation => MachineTransport.executionHeads equation.head) := by rfl

theorem matcher_completed_retained_declarations :
    GeneralScopedMatchExecution.program.declarations.filter
      (retainedCallDeclaration MachineTransport.executionHeads) =
    RuleExecutionProgram.scopedProgram.declarations.filter
      (retainedCallDeclaration MachineTransport.executionHeads) := by rfl

theorem matcher_completed_agreement :
    ProgramAgreementOn MachineTransport.executionHeads
      GeneralScopedMatchExecution.program RuleExecutionProgram.scopedProgram :=
  programAgreementOn_of_retained_rows _ _ _
    matcher_completed_retained_equations matcher_completed_retained_declarations
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.Mechanical
end MatcherCompletedAssembly
