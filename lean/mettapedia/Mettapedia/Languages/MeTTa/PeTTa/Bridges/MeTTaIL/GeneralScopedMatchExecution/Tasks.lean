import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.Tree

/-! # Argument, bag-selection and residual tasks of the original scoped matcher -/
section MatcherTasks
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
private abbrev MatcherTasks_pathValue (path : List Nat) : Atom := encoded (encodeList Term.natural path)
private abbrev MatcherTasks_taskValue (task : GeneralScopedMatchMachine.Task) : Atom := encoded (matcherTaskTerm task)
private abbrev MatcherTasks_worksValue (works : List GeneralScopedMatchMachine.Work) : Atom := encoded (encodeList matcherWorkTerm works)
private def MatcherTasks_taskCases : SpaceSemantics.Cases :=
  match (equation .expand).body with
  | .expression [.symbol "case", _, .expression [.expression [_, .expression [.symbol "case", _, .expression rows]]]] =>
      (readCases rows).getD []
  | _ => []
private def MatcherTasks_taskBody (index : Nat) : Atom := (MatcherTasks_taskCases[index]?).map Prod.snd |>.getD (.symbol "LNil")
private theorem MatcherTasks_task_cases : MatcherTasks_taskCases =
    [(a "ScopedMatcherTree" [v "path", v "depth", v "pattern", v "value"], MatcherTasks_taskBody 0),
      (a "ScopedMatcherArguments" [v "path", v "depth", v "index", v "patterns", v "targets"], MatcherTasks_taskBody 1),
      (a "ScopedMatcherBag" [v "path", v "depth", v "index", v "patterns", v "rest", v "kind", v "targets"], MatcherTasks_taskBody 2),
      (a "ScopedMatcherBagSelect" [v "path", v "depth", v "index", v "pattern", v "tail", v "rest", v "kind", v "targets", v "selected"], MatcherTasks_taskBody 3),
      (a "ScopedMatcherRestCapture" [v "path", v "depth", v "name", v "kind", v "targets"], MatcherTasks_taskBody 4)] := by rfl
private def MatcherTasks_requestNames : List String :=
  ["rule", "spec", "ambient", "site", "request-path", "request-depth", "initial", "schema", "target"]
private def MatcherTasks_expandCaller (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (task : GeneralScopedMatchMachine.Task) : Subst :=
  environment .expand [requestValue request, assignmentValue assignment, MatcherTasks_taskValue task]
private def MatcherTasks_requestCaller (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (task : GeneralScopedMatchMachine.Task) : Subst :=
  ("target", patternValue request.target) :: ("schema", patternValue request.schema) ::
    ("initial", assignmentValue request.initial) :: ("request-depth", number request.depth) ::
    ("request-path", MatcherTasks_pathValue request.path) ::
    ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm request.site)) :: ("ambient", number request.ambient) ::
    ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec)) ::
    ("rule", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule)) :: MatcherTasks_expandCaller request assignment task
private theorem MatcherTasks_expand_shape : (equation .expand).body =
    a "case" [v "request", .expression [.expression
      [a "ScopedMatcherRequest" (MatcherTasks_requestNames.map v),
        a "case" [v "task", .expression (MatcherTasks_taskCases.map fun row => .expression [row.1, row.2])]]]] := by
  decide +kernel

private theorem MatcherTasks_expand_case_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (task : GeneralScopedMatchMachine.Task) (selected : Subst) (body answer : Atom)
    (selection : SpaceSemantics.selectCase (MatcherTasks_requestCaller request assignment task) (MatcherTasks_taskValue task) MatcherTasks_taskCases =
      some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a Helper.expand.head [requestValue request, assignmentValue assignment, MatcherTasks_taskValue task])
      state answer := by
  let caller := MatcherTasks_expandCaller request assignment task
  apply helper_call .expand [] state _ [requestValue request, assignmentValue assignment, MatcherTasks_taskValue task] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [MatcherTasks_expand_shape]
  apply case_returns program caller (MatcherTasks_requestCaller request assignment task) state state state (v "request")
    (requestValue request) (a "case" [v "task", .expression (MatcherTasks_taskCases.map fun row => .expression [row.1, row.2])])
    _ _ [(a "ScopedMatcherRequest" (MatcherTasks_requestNames.map v),
      a "case" [v "task", .expression (MatcherTasks_taskCases.map fun row => .expression [row.1, row.2])])]
    (read_cases_encoded _)
  · simpa [caller, MatcherTasks_expandCaller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "request"
  · simp [MatcherTasks_requestNames, matcherRequestTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, MatcherTasks_requestCaller, caller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
  · apply case_returns program (MatcherTasks_requestCaller request assignment task) selected state state state (v "task")
      (MatcherTasks_taskValue task) body answer _ MatcherTasks_taskCases (read_cases_encoded _) _ selection returned
    simpa [MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (MatcherTasks_requestCaller request assignment task) state "task"

private def MatcherTasks_bagSelectResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment",
    a "LCons" [a "ScopedMatcherTree" [v "nested", v "depth", v "pattern", v "value"],
      a "LCons" [a "ScopedMatcherBag" [v "path", v "depth", v "next", v "tail", v "rest", v "kind", v "remaining"], .symbol "LNil"]],
    a "LCons" [a "BagChoice" [v "nested", v "selected"], .symbol "LNil"]],
    a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
      [a "ScopedMatcherBagSelect" [v "path", v "depth", v "index", v "pattern", v "tail", v "rest", v "kind", v "targets", v "later"], .symbol "LNil"],
      .symbol "LNil"], .symbol "LNil"]]
private def MatcherTasks_bagSelectBindings : List Atom :=
  [.expression [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]]],
    .expression [v "next", a "+" [v "index", number 1]],
    .expression [v "remaining", a "gslt:rule:scope-match-erase-at" [v "selected", v "targets"]],
    .expression [v "later", a "+" [v "selected", number 1]]]
private def MatcherTasks_bagSelectSomeBody : Atom := a "let*" [.expression MatcherTasks_bagSelectBindings, MatcherTasks_bagSelectResult]
private def MatcherTasks_bagSelectCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "value"], MatcherTasks_bagSelectSomeBody)]
private theorem MatcherTasks_bag_select_shape : MatcherTasks_taskBody 3 =
    a "case" [a "gslt:rule:row-at" [v "selected", v "targets"],
      .expression (MatcherTasks_bagSelectCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem MatcherTasks_bag_select_template : PureData.Template program MatcherTasks_bagSelectResult := by
  unfold MatcherTasks_bagSelectResult
  wire_template

private theorem MatcherTasks_appended_path_wire (path : List Nat) (index : Nat) :
    encodeList id (path.map Term.natural ++ [Term.natural index]) =
      encodeList Term.natural (path ++ [index]) := by
  have mapped : path.map Term.natural ++ [Term.natural index] = (path ++ [index]).map Term.natural := by
    simp only [List.map_append, List.map_cons, List.map_nil]
  rw [mapped, encodeList_map]
  rfl

theorem matcher_expand_bag_select_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth index : Nat) (pattern : Pattern)
    (patterns : List Pattern) (rest : Option String) (kind : CollType) (targets : List Pattern) (selected : Nat) :
    PureReturns program [] state (a Helper.expand.head [requestValue request, assignmentValue assignment,
      MatcherTasks_taskValue (.bagSelect path depth index pattern patterns rest kind targets selected)]) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment
        (.bagSelect path depth index pattern patterns rest kind targets selected))) := by
  let task : GeneralScopedMatchMachine.Task := .bagSelect path depth index pattern patterns rest kind targets selected
  let caller := MatcherTasks_requestCaller request assignment task
  let picked := ("selected", number selected) :: ("targets", patternsValue targets) ::
    ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
    ("tail", patternsValue patterns) :: ("pattern", patternValue pattern) :: ("index", number index) ::
    ("depth", number depth) :: ("path", MatcherTasks_pathValue path) :: caller
  apply MatcherTasks_expand_case_returns state request assignment task picked (MatcherTasks_taskBody 3) _
  · simp [MatcherTasks_task_cases, task, MatcherTasks_taskValue, matcherTaskTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
  · rw [MatcherTasks_bag_select_shape]
    have rowReturned := matcher_row_captured_returns picked state selected
      (targets.map InferenceCettaWire.encodePattern) (v "selected") (v "targets")
      (by simp [picked, applySubst, Subst.lookup, InferenceCettaWire.encodePatterns_eq_encodeList,
        CettaWire.encodeList_map])
    cases found : targets[selected]? with
    | none =>
        apply case_returns program picked picked state state state
          (a "gslt:rule:row-at" [v "selected", v "targets"]) (.symbol "None")
          (.symbol "LNil") _ _ MatcherTasks_bagSelectCases (read_cases_encoded _)
        · simpa [List.getElem?_map, found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using rowReturned
        · simp [MatcherTasks_bagSelectCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [GeneralScopedMatchMachine.expand, task, found, MatcherTasks_worksValue, encodeList, CettaWireAtom.encode] using
            symbol_returns program picked state "LNil"
    | some target =>
        let valued := ("value", patternValue target) :: picked
        let nested := ("nested", MatcherTasks_pathValue (path ++ [index])) :: valued
        let next := ("next", number (index + 1)) :: nested
        let remaining := ("remaining", patternsValue (targets.eraseIdx selected)) :: next
        let later := ("later", number (selected + 1)) :: remaining
        apply case_returns program picked valued state state state
          (a "gslt:rule:row-at" [v "selected", v "targets"]) (a "Some" [patternValue target])
          MatcherTasks_bagSelectSomeBody _ _ MatcherTasks_bagSelectCases (read_cases_encoded _)
        · simpa [List.getElem?_map, found, MatchAutomataBindingExecution.payloadOptionTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using rowReturned
        · simp [MatcherTasks_bagSelectCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, valued, picked, caller,
            MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
        · unfold MatcherTasks_bagSelectSomeBody
          apply PureData.let_bindings_return (final := later)
            (pairs := [(v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]]),
              (v "next", a "+" [v "index", number 1]),
              (v "remaining", a "gslt:rule:scope-match-erase-at" [v "selected", v "targets"]),
              (v "later", a "+" [v "selected", number 1])])
          · apply PureData.BindingsReturn.cons (bound := nested)
            · apply matcher_append_captured_returns valued state (path.map Term.natural) [Term.natural index]
              simp [valued, picked, MatcherTasks_pathValue, applySubst, applySubst.applySubstList, Subst.lookup,
                encodeList_map, CettaWireAtom.encode, encodeList]
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, nested, valued,
                picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup,
                MatcherTasks_appended_path_wire]
            · apply PureData.BindingsReturn.cons (bound := next)
              · apply matcher_add_returns nested state index 1
                · simpa [nested, valued, picked, applySubst, Subst.lookup] using variable_returns program nested state "index"
                · exact grounded_returns program nested state (.int 1)
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, next, nested,
                  valued, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := remaining)
                · have erased := matcher_erase_captured_returns next state selected
                    (targets.map InferenceCettaWire.encodePattern) (v "selected") (v "targets")
                    (by simp [next, nested, valued, picked, applySubst, Subst.lookup,
                      InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map])
                  have mapped : (targets.map InferenceCettaWire.encodePattern).eraseIdx selected =
                      (targets.eraseIdx selected).map InferenceCettaWire.encodePattern := by
                    simp only [List.eraseIdx_eq_take_drop_succ, List.map_append, List.map_take, List.map_drop]
                  rw [mapped] at erased
                  simpa only [patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList,
                    encodeList_map, Function.id_comp] using erased
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, remaining, next,
                    nested, valued, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup,
                    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map]
                · apply PureData.BindingsReturn.cons (bound := later)
                  · apply matcher_add_returns remaining state selected 1
                    · simpa [remaining, next, nested, valued, picked, applySubst, Subst.lookup] using
                        variable_returns program remaining state "selected"
                    · exact grounded_returns program remaining state (.int 1)
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, later, remaining,
                      next, nested, valued, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
                  · exact .nil _ _
          · simpa [MatcherTasks_bagSelectResult, GeneralScopedMatchMachine.expand, task, found, MatcherTasks_worksValue, matcherWorkTerm,
              matcherTaskTerm, traceTerm, bagChoiceTerm, later, remaining, next, nested, valued, picked, caller,
              MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, MatcherTasks_pathValue,
              applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program later state MatcherTasks_bagSelectResult MatcherTasks_bag_select_template


private theorem MatcherTasks_rest_capture_shape : MatcherTasks_taskBody 4 =
    a "let" [v "captured", a Helper.capture.head
      [v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "name",
        a "PCollection" [v "kind", v "targets", .symbol "RNone"]],
      a Helper.capturedWork.head [v "captured"]] := by decide +kernel

theorem matcher_expand_rest_capture_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (name : String)
    (kind : CollType) (targets : List Pattern) :
    PureReturns program [] state (a Helper.expand.head [requestValue request, assignmentValue assignment,
      MatcherTasks_taskValue (.restCapture path depth name kind targets)]) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment (.restCapture path depth name kind targets))) := by
  let task : GeneralScopedMatchMachine.Task := .restCapture path depth name kind targets
  let caller := MatcherTasks_requestCaller request assignment task
  let picked := ("targets", patternsValue targets) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) ::
    ("name", encoded (.string name)) :: ("depth", number depth) :: ("path", MatcherTasks_pathValue path) :: caller
  let result := ScopedRuleMatching.captureRest? request.rule request.spec request.ambient depth request.site path assignment name kind targets
  let final := ("captured", encoded (ScopedCapture.scopedAssignmentOptionTerm result)) :: picked
  apply MatcherTasks_expand_case_returns state request assignment task picked (MatcherTasks_taskBody 4) _
  · simp [MatcherTasks_task_cases, task, MatcherTasks_taskValue, matcherTaskTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
  · rw [MatcherTasks_rest_capture_shape]
    apply named_let_returns picked state "captured" _ (encoded (ScopedCapture.scopedAssignmentOptionTerm result))
    · simp [picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
    · exact matcher_capture_captured_returns picked state request path depth assignment name (.collection kind targets none) _
        (by simp [picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, MatcherTasks_pathValue,
          applySubst, applySubst.applySubstList, Subst.lookup,
          InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany])
    · simpa only [GeneralScopedMatchMachine.expand, result, MatcherTasks_worksValue] using
        matcher_captured_work_captured_returns final state result (v "captured")
          (by simp [final, applySubst, Subst.lookup])


private def MatcherTasks_emptyWorkResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", .symbol "LNil", .symbol "LNil"], .symbol "LNil"]
private theorem MatcherTasks_empty_work_template : PureData.Template program MatcherTasks_emptyWorkResult := by
  unfold MatcherTasks_emptyWorkResult
  wire_template
private def MatcherTasks_argumentsResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment",
    a "LCons" [a "ScopedMatcherTree" [v "nested", v "depth", v "pattern", v "value"],
      a "LCons" [a "ScopedMatcherArguments" [v "path", v "depth", v "next", v "tail", v "remaining"], .symbol "LNil"]],
    .symbol "LNil"], .symbol "LNil"]
private def MatcherTasks_argumentsSomeBody : Atom :=
  a "let*" [.expression
    [.expression [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]]],
      .expression [v "next", a "+" [v "index", number 1]]], MatcherTasks_argumentsResult]
private def MatcherTasks_argumentsCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", .symbol "LNil"], MatcherTasks_emptyWorkResult),
    (.expression [a "LCons" [v "pattern", v "tail"], a "LCons" [v "value", v "remaining"]], MatcherTasks_argumentsSomeBody),
    (v "other", .symbol "LNil")]
private theorem MatcherTasks_arguments_shape : MatcherTasks_taskBody 1 =
    a "case" [.expression [v "patterns", v "targets"],
      .expression (MatcherTasks_argumentsCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem MatcherTasks_arguments_template : PureData.Template program MatcherTasks_argumentsResult := by
  unfold MatcherTasks_argumentsResult
  wire_template
private def MatcherTasks_argumentsPicked (caller : Subst) : List Pattern → List Pattern → Subst
  | [], [] => caller
  | pattern :: patterns, target :: targets =>
      ("remaining", patternsValue targets) :: ("value", patternValue target) ::
        ("tail", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
  | patterns, targets => ("other", .expression [patternsValue patterns, patternsValue targets]) :: caller
private def MatcherTasks_argumentsCode : List Pattern → List Pattern → Atom
  | [], [] => MatcherTasks_emptyWorkResult
  | _ :: _, _ :: _ => MatcherTasks_argumentsSomeBody
  | _, _ => .symbol "LNil"
private theorem MatcherTasks_arguments_case_returns (caller : Subst) (state : State) (patterns targets : List Pattern)
    (answer : Atom)
    (captured : [v "patterns", v "targets"].map (applySubst caller) = [patternsValue patterns, patternsValue targets])
    (fresh : ∀ name ∈ ["pattern", "tail", "value", "remaining", "other"], Subst.lookup caller name = none)
    (continued : PureReturns program (MatcherTasks_argumentsPicked caller patterns targets) state
      (MatcherTasks_argumentsCode patterns targets) state answer) :
    PureReturns program caller state (MatcherTasks_taskBody 1) state answer := by
  rw [MatcherTasks_arguments_shape]
  apply case_returns program caller (MatcherTasks_argumentsPicked caller patterns targets) state state state
    (.expression [v "patterns", v "targets"]) (.expression [patternsValue patterns, patternsValue targets])
    (MatcherTasks_argumentsCode patterns targets) answer _ MatcherTasks_argumentsCases (read_cases_encoded _) _ _ continued
  · have returned := PureData.variables_return program caller state ["patterns", "targets"]
    have captured' : ["patterns", "targets"].map (fun name => applySubst caller (.var name)) =
        [patternsValue patterns, patternsValue targets] := by
      simpa only [v, List.map_cons, List.map_nil] using captured
    rw [captured'] at returned
    exact returned
  · have patternFresh := fresh "pattern" (by decide)
    have tailFresh := fresh "tail" (by decide)
    have valueFresh := fresh "value" (by decide)
    have remainingFresh := fresh "remaining" (by decide)
    have otherFresh := fresh "other" (by decide)
    unfold Subst.lookup at patternFresh tailFresh valueFresh remainingFresh otherFresh
    cases patterns <;> cases targets <;>
      simp [MatcherTasks_argumentsPicked, MatcherTasks_argumentsCode, MatcherTasks_argumentsCases, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
        patternFresh, tailFresh, valueFresh, remainingFresh, otherFresh]

theorem matcher_expand_arguments_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth index : Nat) (patterns targets : List Pattern) :
    PureReturns program [] state (a Helper.expand.head [requestValue request, assignmentValue assignment,
      MatcherTasks_taskValue (.arguments path depth index patterns targets)]) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment (.arguments path depth index patterns targets))) := by
  let task : GeneralScopedMatchMachine.Task := .arguments path depth index patterns targets
  let caller := MatcherTasks_requestCaller request assignment task
  let picked := ("targets", patternsValue targets) :: ("patterns", patternsValue patterns) ::
    ("index", number index) :: ("depth", number depth) :: ("path", MatcherTasks_pathValue path) :: caller
  apply MatcherTasks_expand_case_returns state request assignment task picked (MatcherTasks_taskBody 1) _
  · simp [MatcherTasks_task_cases, task, MatcherTasks_taskValue, matcherTaskTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
  · apply MatcherTasks_arguments_case_returns picked state patterns targets _
    · simp [picked, applySubst, Subst.lookup]
    · intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp [picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
    · cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simpa [MatcherTasks_argumentsPicked, MatcherTasks_argumentsCode, GeneralScopedMatchMachine.expand, MatcherTasks_worksValue, MatcherTasks_emptyWorkResult,
                matcherWorkTerm, traceTerm, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names,
                applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return program picked state MatcherTasks_emptyWorkResult MatcherTasks_empty_work_template
          | cons target targets =>
              exact symbol_returns program _ state "LNil"
      | cons pattern patterns =>
          cases targets with
          | nil => exact symbol_returns program _ state "LNil"
          | cons target targets =>
              let valued := MatcherTasks_argumentsPicked picked (pattern :: patterns) (target :: targets)
              let nested := ("nested", MatcherTasks_pathValue (path ++ [index])) :: valued
              let next := ("next", number (index + 1)) :: nested
              unfold MatcherTasks_argumentsCode MatcherTasks_argumentsSomeBody
              apply PureData.let_bindings_return (final := next)
                (pairs := [(v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]]),
                  (v "next", a "+" [v "index", number 1])])
              · apply PureData.BindingsReturn.cons (bound := nested)
                · apply matcher_append_captured_returns valued state (path.map Term.natural) [Term.natural index]
                  simp [valued, MatcherTasks_argumentsPicked, picked, MatcherTasks_pathValue, applySubst, applySubst.applySubstList, Subst.lookup,
                    encodeList_map, CettaWireAtom.encode, encodeList]
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, nested, valued,
                    MatcherTasks_argumentsPicked, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names,
                    Subst.lookup, MatcherTasks_appended_path_wire]
                · apply PureData.BindingsReturn.cons (bound := next)
                  · apply matcher_add_returns nested state index 1
                    · simpa [nested, valued, MatcherTasks_argumentsPicked, picked, applySubst, Subst.lookup] using
                        variable_returns program nested state "index"
                    · exact grounded_returns program nested state (.int 1)
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, next, nested,
                      valued, MatcherTasks_argumentsPicked, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment,
                      Helper.names, Subst.lookup]
                  · exact .nil _ _
              · simpa [MatcherTasks_argumentsResult, GeneralScopedMatchMachine.expand, MatcherTasks_worksValue, matcherWorkTerm, matcherTaskTerm,
                  traceTerm, next, nested, valued, MatcherTasks_argumentsPicked, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller,
                  environment, Helper.names, MatcherTasks_pathValue, applySubst, applySubst.applySubstList, Subst.lookup,
                  encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return program next state MatcherTasks_argumentsResult MatcherTasks_arguments_template


private def MatcherTasks_bagConsResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherBagSelect" [v "path", v "depth", v "index", v "pattern", v "tail", v "rest", v "kind", v "targets", number 0],
      .symbol "LNil"], .symbol "LNil"], .symbol "LNil"]
private def MatcherTasks_bagRestResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherRestCapture" [v "nested", v "depth", v "name", v "kind", v "targets"], .symbol "LNil"],
      .symbol "LNil"], .symbol "LNil"]
private def MatcherTasks_bagRestBody : Atom :=
  a "let" [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]], MatcherTasks_bagRestResult]
private def MatcherTasks_bagTargetsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", MatcherTasks_emptyWorkResult), (v "other", .symbol "LNil")]
private def MatcherTasks_bagRestCases : SpaceSemantics.Cases :=
  [(.symbol "RNone", a "case" [v "targets", .expression (MatcherTasks_bagTargetsCases.map fun row => .expression [row.1, row.2])]),
    (a "RSome" [v "name"], MatcherTasks_bagRestBody)]
private def MatcherTasks_bagCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "case" [v "rest", .expression (MatcherTasks_bagRestCases.map fun row => .expression [row.1, row.2])]),
    (a "LCons" [v "pattern", v "tail"], MatcherTasks_bagConsResult)]
private theorem MatcherTasks_bag_shape : MatcherTasks_taskBody 2 =
    a "case" [v "patterns", .expression (MatcherTasks_bagCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem MatcherTasks_bag_cons_template : PureData.Template program MatcherTasks_bagConsResult := by
  unfold MatcherTasks_bagConsResult
  wire_template
private theorem MatcherTasks_bag_rest_template : PureData.Template program MatcherTasks_bagRestResult := by
  unfold MatcherTasks_bagRestResult
  wire_template

theorem matcher_expand_bag_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth index : Nat) (patterns : List Pattern)
    (rest : Option String) (kind : CollType) (targets : List Pattern) :
    PureReturns program [] state (a Helper.expand.head [requestValue request, assignmentValue assignment,
      MatcherTasks_taskValue (.bag path depth index patterns rest kind targets)]) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment (.bag path depth index patterns rest kind targets))) := by
  let task : GeneralScopedMatchMachine.Task := .bag path depth index patterns rest kind targets
  let caller := MatcherTasks_requestCaller request assignment task
  let picked := ("targets", patternsValue targets) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) ::
    ("rest", encoded (InferenceCettaWire.encodeRest rest)) :: ("patterns", patternsValue patterns) ::
    ("index", number index) :: ("depth", number depth) :: ("path", MatcherTasks_pathValue path) :: caller
  apply MatcherTasks_expand_case_returns state request assignment task picked (MatcherTasks_taskBody 2) _
  · simp [MatcherTasks_task_cases, task, MatcherTasks_taskValue, matcherTaskTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
  · rw [MatcherTasks_bag_shape]
    cases patterns with
    | nil =>
        apply case_returns program picked picked state state state (v "patterns") (.symbol "LNil")
          (a "case" [v "rest", .expression (MatcherTasks_bagRestCases.map fun row => .expression [row.1, row.2])])
          _ _ MatcherTasks_bagCases (read_cases_encoded _)
        · simpa [picked, applySubst, Subst.lookup, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
            variable_returns program picked state "patterns"
        · simp [MatcherTasks_bagCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · cases rest with
          | none =>
              apply case_returns program picked picked state state state (v "rest") (.symbol "RNone")
                (a "case" [v "targets", .expression (MatcherTasks_bagTargetsCases.map fun row => .expression [row.1, row.2])])
                _ _ MatcherTasks_bagRestCases (read_cases_encoded _)
              · simpa [picked, applySubst, Subst.lookup, InferenceCettaWire.encodeRest, CettaWireAtom.encode] using
                  variable_returns program picked state "rest"
              · simp [MatcherTasks_bagRestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · cases targets with
                | nil =>
                    apply case_returns program picked picked state state state (v "targets") (.symbol "LNil")
                      MatcherTasks_emptyWorkResult _ _ MatcherTasks_bagTargetsCases (read_cases_encoded _)
                    · simpa [picked, applySubst, Subst.lookup, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
                        variable_returns program picked state "targets"
                    · simp [MatcherTasks_bagTargetsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                    · simpa [MatcherTasks_emptyWorkResult, GeneralScopedMatchMachine.expand, task, MatcherTasks_worksValue, matcherWorkTerm,
                        traceTerm, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names,
                        applySubst, applySubst.applySubstList, Subst.lookup, encodeList, CettaWireAtom.encode,
                        CettaWireAtom.encodeMany] using
                        PureData.template_return program picked state MatcherTasks_emptyWorkResult MatcherTasks_empty_work_template
                | cons target targets =>
                    let failed := ("other", patternsValue (target :: targets)) :: picked
                    apply case_returns program picked failed state state state (v "targets") (patternsValue (target :: targets))
                      (.symbol "LNil") _ _ MatcherTasks_bagTargetsCases (read_cases_encoded _)
                    · simpa [picked, applySubst, Subst.lookup] using variable_returns program picked state "targets"
                    · simp [MatcherTasks_bagTargetsCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, failed, picked, caller,
                        MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
                    · exact symbol_returns program failed state "LNil"
          | some name =>
              let named := ("name", encoded (.string name)) :: picked
              let nested := ("nested", MatcherTasks_pathValue (path ++ [index])) :: named
              apply case_returns program picked named state state state (v "rest") (encoded (InferenceCettaWire.encodeRest (some name)))
                MatcherTasks_bagRestBody _ _ MatcherTasks_bagRestCases (read_cases_encoded _)
              · simpa [picked, applySubst, Subst.lookup] using variable_returns program picked state "rest"
              · simp [MatcherTasks_bagRestCases, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, named, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
              · unfold MatcherTasks_bagRestBody
                apply named_let_returns named state "nested" _ (MatcherTasks_pathValue (path ++ [index]))
                · simp [named, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
                · have appended := matcher_append_captured_returns named state (path.map Term.natural) [Term.natural index]
                    (v "path") (a "LCons" [v "index", .symbol "LNil"])
                    (by simp [named, picked, MatcherTasks_pathValue, applySubst, applySubst.applySubstList, Subst.lookup,
                      encodeList_map, CettaWireAtom.encode, encodeList])
                  change PureReturns program named state
                    (a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]]) state
                    (encoded (encodeList id (path.map Term.natural ++ [Term.natural index]))) at appended
                  simpa only [MatcherTasks_pathValue, MatcherTasks_appended_path_wire] using appended
                · simpa [MatcherTasks_bagRestResult, GeneralScopedMatchMachine.expand, task, MatcherTasks_worksValue, matcherWorkTerm, matcherTaskTerm,
                    traceTerm, nested, named, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names,
                    MatcherTasks_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany] using
                    PureData.template_return program nested state MatcherTasks_bagRestResult MatcherTasks_bag_rest_template
    | cons pattern patterns =>
        let valued := ("tail", patternsValue patterns) :: ("pattern", patternValue pattern) :: picked
        apply case_returns program picked valued state state state (v "patterns") (patternsValue (pattern :: patterns))
          MatcherTasks_bagConsResult _ _ MatcherTasks_bagCases (read_cases_encoded _)
        · simpa [picked, applySubst, Subst.lookup] using variable_returns program picked state "patterns"
        · simp [MatcherTasks_bagCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, valued, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
        · simpa [MatcherTasks_bagConsResult, GeneralScopedMatchMachine.expand, task, MatcherTasks_worksValue, matcherWorkTerm, matcherTaskTerm,
            traceTerm, valued, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names,
            MatcherTasks_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany] using
            PureData.template_return program valued state MatcherTasks_bagConsResult MatcherTasks_bag_cons_template


private theorem MatcherTasks_tree_task_shape : MatcherTasks_taskBody 0 = a Helper.tree.head
    [v "rule", v "spec", v "ambient", v "site", v "assignment", v "path", v "depth", v "pattern", v "value"] := by rfl

theorem matcher_expand_tree_task_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (schema target : Pattern) :
    PureReturns program [] state (a Helper.expand.head [requestValue request, assignmentValue assignment,
      MatcherTasks_taskValue (.tree path depth schema target)]) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth schema target))) := by
  let task : GeneralScopedMatchMachine.Task := .tree path depth schema target
  let caller := MatcherTasks_requestCaller request assignment task
  let picked := ("value", patternValue target) :: ("pattern", patternValue schema) ::
    ("depth", number depth) :: ("path", MatcherTasks_pathValue path) :: caller
  apply MatcherTasks_expand_case_returns state request assignment task picked (MatcherTasks_taskBody 0) _
  · simp [MatcherTasks_task_cases, task, MatcherTasks_taskValue, matcherTaskTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, Subst.lookup]
  · rw [MatcherTasks_tree_task_shape]
    apply matcher_expand_tree_captured_returns picked state request assignment path depth schema target
    simp [picked, caller, MatcherTasks_requestCaller, MatcherTasks_expandCaller, environment, Helper.names, MatcherTasks_pathValue, applySubst, Subst.lookup]
    rfl

def matcherExpandTerm (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (task : GeneralScopedMatchMachine.Task) : Term :=
  .application Helper.expand.head [matcherRequestTerm request, ScopedCapture.scopedAssignmentTerm assignment,
    matcherTaskTerm task]

theorem matcher_expand_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (task : GeneralScopedMatchMachine.Task) :
    PureReturns program [] state (encoded (matcherExpandTerm request assignment task)) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment task)) := by
  cases task with
  | tree path depth schema target => exact matcher_expand_tree_task_returns state request assignment path depth schema target
  | arguments path depth index schemas targets => exact matcher_expand_arguments_returns state request assignment path depth index schemas targets
  | bag path depth index schemas rest kind targets => exact matcher_expand_bag_returns state request assignment path depth index schemas rest kind targets
  | bagSelect path depth index schema schemas rest kind targets selected =>
      exact matcher_expand_bag_select_returns state request assignment path depth index schema schemas rest kind targets selected
  | restCapture path depth name kind targets => exact matcher_expand_rest_capture_returns state request assignment path depth name kind targets

theorem matcher_expand_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (assignment : Assignment) (task : GeneralScopedMatchMachine.Task)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [requestValue request, assignmentValue assignment, MatcherTasks_taskValue task]) :
    PureReturns program caller state (a Helper.expand.head arguments) state
      (MatcherTasks_worksValue (GeneralScopedMatchMachine.expand request assignment task)) :=
  helper_capture .expand caller state arguments _ _ rfl captured (matcher_expand_returns state request assignment task)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherTasks
