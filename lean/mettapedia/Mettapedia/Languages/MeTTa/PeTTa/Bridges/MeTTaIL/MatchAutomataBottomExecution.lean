import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataCompilationExecution

/-!
# The retained bottom-up matcher executes its finite state transitions

The source transition consumes the already computed child states. Its
inventory membership, constructor tests and counters are related to the
independent bottom-up machine. Data encoding does not evaluate the contents
of a captured constructor head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBottomExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire OrderedPatternMatrixCompilation BottomUpMatchAutomaton
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval MatchAutomataProgram
open MatchAutomataSourceExecution (listValue)
open MatchAutomataCompilationExecution (shapeTerm subjectTerm)
open MatchAutomataDerivativeExecution (positionTerm locationTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : Term) : Atom := CettaWireAtom.encode value
private abbrev shapesValue (patterns : List (Pattern Term)) : Atom :=
  listValue (patterns.map shapeTerm)

mutual
  /-- The source carries both inspection and inventory-test counts. -/
  def stateTerm (inventorySize : Nat) : StateTree Term → Term
    | .node (matchedPatterns, reads) children => .application "MState"
        [encodeList shapeTerm matchedPatterns, encodeList id (stateTerms inventorySize children),
          .natural reads, .natural (reads * inventorySize)]

  def stateTerms (inventorySize : Nat) : List (StateTree Term) → List Term
    | [] => []
    | first :: rest => stateTerm inventorySize first :: stateTerms inventorySize rest
end

@[simp] theorem stateTerms_eq_map (inventorySize : Nat) (states : List (StateTree Term)) :
    stateTerms inventorySize states = states.map (stateTerm inventorySize) := by
  induction states with
  | nil => rfl
  | cons first rest ih => simp only [stateTerms, List.map_cons, ih]

@[simp] theorem stateTerm_node (inventorySize reads : Nat) (matchedPatterns : List (Pattern Term))
    (children : List (StateTree Term)) :
    stateTerm inventorySize (.node (matchedPatterns, reads) children) = .application "MState"
      [encodeList shapeTerm matchedPatterns, encodeList (stateTerm inventorySize) children,
        .natural reads, .natural (reads * inventorySize)] := by
  simp [stateTerm]

private abbrev statesValue (inventorySize : Nat) (states : List (StateTree Term)) : Atom :=
  listValue (states.map (stateTerm inventorySize))

private inductive Helper where | child | accept | transition | counts | states

private def Helper.head : Helper → String
  | .child => "gslt:automata:child-accept"
  | .accept => "gslt:automata:accept"
  | .transition => "gslt:automata:transition"
  | .counts => "gslt:automata:state-counts"
  | .states => "gslt:automata:bottom-states"

private def Helper.names : Helper → List String
  | .child => ["patterns", "states"]
  | .accept => ["head", "states", "pattern"]
  | .transition => ["inventory", "head", "states"]
  | .counts => ["states"]
  | .states => ["inventory", "children"]

attribute [local simp] a v encoded shapesValue statesValue Helper.head Helper.names

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)

private def environment (helper : Helper) (values : List Term) : Subst :=
  (helper.names.zip (values.map encoded)).reverse

private theorem helper_clause (helper : Helper) (values : List Term)
    (length : values.length = helper.names.length) :
    clauses program helper.head (values.map encoded) =
      [.evaluate (environment helper values) (equation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  have unique : equations helper.head = [equation helper] := by cases helper <;> rfl
  have formals : (equation helper).arguments = helper.names.map v := by
    cases helper <;> decide +kernel
  rw [unique]
  cases helper with
  | child =>
      obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp length
      simp [formals, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
  | accept =>
      obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp length
      simp [formals, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
  | transition =>
      obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp length
      simp [formals, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
  | counts =>
      obtain ⟨first, rfl⟩ := List.length_eq_one_iff.mp length
      simp [formals, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
  | states =>
      obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp length
      simp [formals, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

private theorem helper_call (helper : Helper) (bindings : Subst) (state : State)
    (values : List Term) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst bindings) = values.map encoded)
    (length : values.length = helper.names.length)
    (body : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program bindings state (a helper.head arguments) state answer := by
  have count : arguments.length = helper.names.length := by
    simpa [length] using congrArg List.length captured
  apply PureData.raw_authored_call_return program bindings (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide) (by cases helper <;> decide +kernel) _ _ body
  · intro index bounded
    rw [count] at bounded
    cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
    all_goals
      have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases small with rfl | rfl | rfl <;> first | decide +kernel | omega
  · rw [captured]
    exact helper_clause helper values length

private theorem member_captured (bindings : Subst) (state : State) (value : Term)
    (values : List Term) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) = [encoded value, listValue values]) :
    PureReturns program bindings state (a "gslt:automata:member" arguments) state
      (Effects.boolean (decide (value ∈ values))) := by
  apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:member"
    [encoded value, listValue values] arguments _ (by decide +kernel) _ (by decide) _
    (MatchAutomataSourceExecution.member_returns state value values)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simpa using captured.symm

private def childCons : Atom :=
  a "if" [a "gslt:automata:member" [v "p", v "matches"],
    a "gslt:automata:child-accept" [v "ps", v "ss"], Effects.boolean false]
private def childCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", .symbol "LNil"], Effects.boolean true),
   (.expression [a "LCons" [v "p", v "ps"],
      a "LCons" [a "MState" [v "matches", v "children", v "reads", v "tests"], v "ss"]], childCons),
   (v "bad", Effects.boolean false)]

private theorem child_shape : (equation .child).body =
    a "case" [.expression [v "patterns", v "states"],
      .expression (childCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

theorem child_body_returns (state : State) (inventorySize : Nat)
    (patterns : List (Pattern Term)) (states : List (StateTree Term)) :
    PureReturns program (environment .child
      [encodeList shapeTerm patterns, encodeList (stateTerm inventorySize) states]) state
      (equation .child).body state
      (Effects.boolean (childAccept patterns (states.map BottomUpMatchAutomaton.state))) := by
  induction patterns generalizing states with
  | nil =>
      cases states with
      | nil =>
          let bindings := environment .child [encodeList shapeTerm [], encodeList (stateTerm inventorySize) []]
          rw [child_shape]
          apply case_returns program bindings bindings state state state _
            (.expression [.symbol "LNil", .symbol "LNil"]) (Effects.boolean true) _ _
            childCases (read_cases_encoded _) _ _ (grounded_returns program bindings state (.bool true))
          · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
              tuple_variables_return program bindings state ["patterns", "states"]
          · simp [childCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom]
      | cons first rest =>
          let bindings := environment .child [encodeList shapeTerm [], encodeList (stateTerm inventorySize) (first :: rest)]
          let selected := ("bad", .expression [shapesValue [], statesValue inventorySize (first :: rest)]) :: bindings
          rw [child_shape]
          apply case_returns program bindings selected state state state _
            (.expression [shapesValue [], statesValue inventorySize (first :: rest)])
            (Effects.boolean false) _ _ childCases (read_cases_encoded _) _ _
            (grounded_returns program selected state (.bool false))
          · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
              tuple_variables_return program bindings state ["patterns", "states"]
          · simp [selected, shapesValue, statesValue, childCases, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, environment, Helper.names]
  | cons p ps ih =>
      cases states with
      | nil =>
          let bindings := environment .child [encodeList shapeTerm (p :: ps), encodeList (stateTerm inventorySize) []]
          let selected := ("bad", .expression [shapesValue (p :: ps), statesValue inventorySize []]) :: bindings
          rw [child_shape]
          apply case_returns program bindings selected state state state _
            (.expression [shapesValue (p :: ps), statesValue inventorySize []])
            (Effects.boolean false) _ _ childCases (read_cases_encoded _) _ _
            (grounded_returns program selected state (.bool false))
          · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
              tuple_variables_return program bindings state ["patterns", "states"]
          · simp [selected, shapesValue, statesValue, childCases, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, environment, Helper.names]
      | cons first rest =>
          cases first with
          | node label children =>
              obtain ⟨matchedPatterns, reads⟩ := label
              let bindings := environment .child [encodeList shapeTerm (p :: ps),
                encodeList (stateTerm inventorySize) (.node (matchedPatterns, reads) children :: rest)]
              let selected := ("ss", statesValue inventorySize rest) ::
                ("tests", encoded (.natural (reads * inventorySize))) ::
                ("reads", encoded (.natural reads)) :: ("children", statesValue inventorySize children) ::
                ("matches", shapesValue matchedPatterns) :: ("ps", shapesValue ps) :: ("p", encoded (shapeTerm p)) :: bindings
              have tested := member_captured selected state (shapeTerm p) (matchedPatterns.map shapeTerm)
                [v "p", v "matches"] (by simp [selected, applySubst, Subst.lookup])
              have memberExact : decide (shapeTerm p ∈ matchedPatterns.map shapeTerm) = decide (p ∈ matchedPatterns) := by
                simp [List.mem_map, MatchAutomataCompilationExecution.shapeTerm_injective.eq_iff]
              rw [memberExact] at tested
              rw [child_shape]
              apply case_returns program bindings selected state state state _
                (.expression [shapesValue (p :: ps), statesValue inventorySize (.node (matchedPatterns, reads) children :: rest)])
                childCons _ _ childCases (read_cases_encoded _) _ _ _
              · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
                  tuple_variables_return program bindings state ["patterns", "states"]
              · simp [selected, shapesValue, statesValue, childCases, encodeList, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany, stateTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, environment, Helper.names]
              · apply if_returns program selected state state state _ _ _ _ _ tested
                by_cases present : p ∈ matchedPatterns
                · have recursive := helper_call .child selected state
                    [encodeList shapeTerm ps, encodeList (stateTerm inventorySize) rest]
                    [v "ps", v "ss"] _ (by simp [selected, applySubst, Subst.lookup]) rfl (ih rest)
                  simpa [childCons, childAccept, BottomUpMatchAutomaton.state, present, Effects.boolean] using recursive
                · simpa [childCons, childAccept, BottomUpMatchAutomaton.state, present, Effects.boolean] using
                    grounded_returns program selected state (.bool false)

theorem child_accept_returns (state : State) (inventorySize : Nat)
    (patterns : List (Pattern Term)) (states : List (StateTree Term)) :
    PureReturns program [] state (a "gslt:automata:child-accept"
      [shapesValue patterns, statesValue inventorySize states]) state
      (Effects.boolean (childAccept patterns (states.map BottomUpMatchAutomaton.state))) := by
  apply helper_call .child [] state
    [encodeList shapeTerm patterns, encodeList (stateTerm inventorySize) states] _ _
    (by simp) rfl (child_body_returns state inventorySize patterns states)

private def acceptNode : Atom :=
  a "if" [a "==" [v "head", v "expected"],
    a "gslt:automata:child-accept" [v "children", v "states"], Effects.boolean false]
private def acceptCases : SpaceSemantics.Cases :=
  [(.symbol "MAny", Effects.boolean true), (a "MNode" [v "expected", v "children"], acceptNode)]

private theorem accept_shape : (equation .accept).body =
    a "case" [v "pattern", .expression (acceptCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem accept_body_returns (state : State) (inventorySize : Nat) (head : Term)
    (states : List (StateTree Term)) (pattern : Pattern Term) :
    PureReturns program (environment .accept
      [head, encodeList (stateTerm inventorySize) states, shapeTerm pattern]) state
      (equation .accept).body state
      (Effects.boolean (accepts head (states.map BottomUpMatchAutomaton.state) pattern)) := by
  cases pattern with
  | wildcard =>
      let bindings := environment .accept [head, encodeList (stateTerm inventorySize) states, .symbol "MAny"]
      rw [accept_shape]
      apply case_returns program bindings bindings state state state (v "pattern") (.symbol "MAny")
        (Effects.boolean true) _ _ acceptCases (read_cases_encoded _) _ _
        (grounded_returns program bindings state (.bool true))
      · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup, CettaWireAtom.encode] using
          variable_returns program bindings state "pattern"
      · simp [acceptCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  | node expected children =>
      let bindings := environment .accept [head, encodeList (stateTerm inventorySize) states,
        shapeTerm (.node expected children)]
      let selected := ("children", shapesValue children) :: ("expected", encoded expected) :: bindings
      have tested : PureReturns program selected state (a "==" [v "head", v "expected"]) state
          (Effects.boolean (decide (head = expected))) := by
        have comparison : (encoded head == encoded expected) = decide (head = expected) := by
          apply Bool.eq_iff_iff.mpr
          simp [CettaWireAtom.encode_eq_encode]
        apply native_variable_call_returns program selected state state "==" ["head", "expected"] _
          (by decide) (by decide) _ (by decide)
        simp [selected, bindings, environment, Helper.names, applySubst, Subst.lookup,
          StdLib.structural_equality, comparison]
      rw [accept_shape]
      apply case_returns program bindings selected state state state (v "pattern")
        (encoded (shapeTerm (.node expected children))) acceptNode _ _ acceptCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program bindings state "pattern"
      · simp [acceptCases, MatchAutomataCompilationExecution.shapeTerm, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, bindings, environment, Helper.names]
      · apply if_returns program selected state state state _ _ _ _ _ tested
        by_cases same : head = expected
        · have recursive := helper_call .child selected state
            [encodeList shapeTerm children, encodeList (stateTerm inventorySize) states]
            [v "children", v "states"] _
            (by simp [selected, bindings, environment, Helper.names, applySubst, Subst.lookup]) rfl
            (child_body_returns state inventorySize children states)
          simpa [acceptNode, accepts, same, Effects.boolean] using recursive
        · simpa [acceptNode, accepts, same, Ne.symm same, Effects.boolean] using
            grounded_returns program selected state (.bool false)

theorem accept_returns (state : State) (inventorySize : Nat) (head : Term)
    (states : List (StateTree Term)) (pattern : Pattern Term) :
    PureReturns program [] state (a "gslt:automata:accept"
      [encoded head, statesValue inventorySize states, encoded (shapeTerm pattern)]) state
      (Effects.boolean (accepts head (states.map BottomUpMatchAutomaton.state) pattern)) := by
  apply helper_call .accept [] state
    [head, encodeList (stateTerm inventorySize) states, shapeTerm pattern] _ _
    (by simp) rfl (accept_body_returns state inventorySize head states pattern)

private def transitionRetained : Atom := a "LCons" [v "p", v "tail"]
private def transitionCons : Atom :=
  a "let" [v "tail", a "gslt:automata:transition" [v "ps", v "head", v "states"],
    a "if" [a "gslt:automata:accept" [v "head", v "states", v "p"], transitionRetained, v "tail"]]
private def transitionCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "p", v "ps"], transitionCons)]

private theorem transition_shape : (equation .transition).body =
    a "case" [v "inventory", .expression (transitionCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem transition_template : PureData.Template program transitionRetained := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

theorem transition_body_returns (state : State) (inventorySize : Nat)
    (patterns : List (Pattern Term)) (head : Term) (states : List (StateTree Term)) :
    PureReturns program (environment .transition
      [encodeList shapeTerm patterns, head, encodeList (stateTerm inventorySize) states]) state
      (equation .transition).body state
      (shapesValue (transition patterns head (states.map BottomUpMatchAutomaton.state))) := by
  induction patterns with
  | nil =>
      let bindings := environment .transition
        [encodeList shapeTerm [], head, encodeList (stateTerm inventorySize) states]
      rw [transition_shape]
      apply case_returns program bindings bindings state state state (v "inventory") (.symbol "LNil")
        (.symbol "LNil") _ _ transitionCases (read_cases_encoded _) _ _
        (symbol_returns program bindings state "LNil")
      · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program bindings state "inventory"
      · simp [transitionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  | cons p ps ih =>
      let bindings := environment .transition
        [encodeList shapeTerm (p :: ps), head, encodeList (stateTerm inventorySize) states]
      let selected := ("ps", shapesValue ps) :: ("p", encoded (shapeTerm p)) :: bindings
      let tail := transition ps head (states.map BottomUpMatchAutomaton.state)
      let bound := ("tail", shapesValue tail) :: selected
      have recursive := helper_call .transition selected state
        [encodeList shapeTerm ps, head, encodeList (stateTerm inventorySize) states]
        [v "ps", v "head", v "states"] _
        (by simp [selected, bindings, environment, Helper.names, applySubst, Subst.lookup]) rfl ih
      have tested := helper_call .accept bound state
        [head, encodeList (stateTerm inventorySize) states, shapeTerm p]
        [v "head", v "states", v "p"] _
        (by simp [bound, selected, bindings, environment, Helper.names, applySubst, Subst.lookup]) rfl
        (accept_body_returns state inventorySize head states p)
      rw [transition_shape]
      apply case_returns program bindings selected state state state (v "inventory") (shapesValue (p :: ps))
        transitionCons _ _ transitionCases (read_cases_encoded _) _ _ _
      · simpa [bindings, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program bindings state "inventory"
      · simp [transitionCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, environment, Helper.names]
      · apply let_returns program selected bound state state state (v "tail") _ _ _ _ recursive _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, bindings, environment, Helper.names, tail]
        · apply if_returns program bound state state state _ _ _ _ _ tested
          cases accepted : accepts head (states.map BottomUpMatchAutomaton.state) p with
          | false =>
              simpa [transition, List.filter_cons, accepted, Effects.boolean, tail,
                bound, applySubst, Subst.lookup] using variable_returns program bound state "tail"
          | true =>
              simpa [transition, List.filter_cons, accepted, Effects.boolean, tail,
                transitionRetained, shapesValue, listValue, encodeList,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, bound, selected,
                applySubst, applySubst.applySubstList, Subst.lookup] using
                PureData.template_return program bound state _ transition_template

/-- The actual transition filters the interned inventory exactly once per
pattern, using the independently computed child match states. -/
theorem transition_returns (state : State) (inventorySize : Nat)
    (patterns : List (Pattern Term)) (head : Term) (states : List (StateTree Term)) :
    PureReturns program [] state (a "gslt:automata:transition"
      [shapesValue patterns, encoded head, statesValue inventorySize states]) state
      (shapesValue (transition patterns head (states.map BottomUpMatchAutomaton.state))) := by
  apply helper_call .transition [] state
    [encodeList shapeTerm patterns, head, encodeList (stateTerm inventorySize) states] _ _
    (by simp) rfl (transition_body_returns state inventorySize patterns head states)

/-- Completion reflects the independent transition, including store and I/O. -/
theorem transition_completed_iff (state : State) (inventorySize : Nat)
    (patterns : List (Pattern Term)) (head : Term) (states : List (StateTree Term))
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (a "gslt:automata:transition"
      [shapesValue patterns, encoded head, statesValue inventorySize states]) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [shapesValue (transition patterns head (states.map BottomUpMatchAutomaton.state))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (transition_returns state inventorySize patterns head states) after answers input output

private abbrev number (value : Nat) : Atom := encoded (.natural value)

private theorem addition_returns (bindings : Subst) (state : State)
    (left right : Nat) (leftName rightName : String)
    (leftCaptured : applySubst bindings (v leftName) = number left)
    (rightCaptured : applySubst bindings (v rightName) = number right) :
    PureReturns program bindings state (a "+" [v leftName, v rightName]) state
      (number (left + right)) := by
  apply native_variable_call_returns program bindings state state "+" [leftName, rightName] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

def countsTerm (inventorySize : Nat) (states : List (StateTree Term)) : Term :=
  .application "Counts" [.natural ((states.map inspections).sum),
    .natural ((states.map inspections).sum * inventorySize)]

private def countsResult : Atom :=
  a "Counts" [a "+" [v "reads", v "tail-reads"], a "+" [v "tests", v "tail-tests"]]
private def countsResultCases : SpaceSemantics.Cases :=
  [(a "Counts" [v "tail-reads", v "tail-tests"], countsResult)]
private def countsCons : Atom :=
  a "case" [a "gslt:automata:state-counts" [v "rest"],
    .expression (countsResultCases.map fun row => .expression [row.1, row.2])]
private def countsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Counts" [number 0, number 0]),
   (a "LCons" [a "MState" [v "matches", v "children", v "reads", v "tests"], v "rest"], countsCons)]

private theorem counts_shape : (equation .counts).body =
    a "case" [v "states", .expression (countsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem counts_body_returns (state : State) (inventorySize : Nat) (states : List (StateTree Term)) :
    PureReturns program (environment .counts [encodeList (stateTerm inventorySize) states]) state
      (equation .counts).body state (encoded (countsTerm inventorySize states)) := by
  induction states with
  | nil =>
      let bindings := environment .counts [encodeList (stateTerm inventorySize) []]
      rw [counts_shape]
      apply case_returns program bindings bindings state state state (v "states") (.symbol "LNil")
        (a "Counts" [number 0, number 0]) _ _ countsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "states"
      · simp [countsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have built := PureData.constructor_return program bindings state "Counts"
          [number 0, number 0] [number 0, number 0] (by decide +kernel) (by decide)
          (.cons (grounded_returns program bindings state (.int 0))
            (.cons (grounded_returns program bindings state (.int 0)) .nil))
        simpa [countsTerm, number, CettaWireAtom.encode] using built
  | cons first rest ih =>
      cases first with
      | node label children =>
          obtain ⟨matchedPatterns, reads⟩ := label
          let bindings := environment .counts
            [encodeList (stateTerm inventorySize) (.node (matchedPatterns, reads) children :: rest)]
          let selected := ("rest", statesValue inventorySize rest) ::
            ("tests", number (reads * inventorySize)) :: ("reads", number reads) ::
            ("children", statesValue inventorySize children) :: ("matches", shapesValue matchedPatterns) :: bindings
          let tailReads := (rest.map inspections).sum
          let bound := ("tail-tests", number (tailReads * inventorySize)) ::
            ("tail-reads", number tailReads) :: selected
          have recursive := helper_call .counts selected state [encodeList (stateTerm inventorySize) rest]
            [v "rest"] _ (by simp [selected, applySubst, Subst.lookup]) rfl ih
          have readAdded := addition_returns bound state reads tailReads "reads" "tail-reads"
            (by simp [bound, selected, applySubst, Subst.lookup]) (by simp [bound, applySubst, Subst.lookup])
          have testsAdded := addition_returns bound state (reads * inventorySize) (tailReads * inventorySize)
            "tests" "tail-tests" (by simp [bound, selected, applySubst, Subst.lookup])
            (by simp [bound, applySubst, Subst.lookup])
          rw [counts_shape]
          apply case_returns program bindings selected state state state (v "states")
            (statesValue inventorySize (.node (matchedPatterns, reads) children :: rest)) countsCons _ _
            countsCases (read_cases_encoded _) _ _ _
          · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "states"
          · simp [countsCases, stateTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, bindings, environment]
          · apply case_returns program selected bound state state state _
              (a "Counts" [number tailReads, number (tailReads * inventorySize)]) countsResult _ _
              countsResultCases (read_cases_encoded _) _ _ _
            · simpa [countsTerm, tailReads, CettaWireAtom.encode, CettaWireAtom.encodeMany] using recursive
            · simp [countsResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                bound, selected, bindings, environment]
            · have built := PureData.constructor_return program bound state "Counts"
                [a "+" [v "reads", v "tail-reads"], a "+" [v "tests", v "tail-tests"]]
                [number (reads + tailReads), number (reads * inventorySize + tailReads * inventorySize)]
                (by decide +kernel) (by decide) (.cons readAdded (.cons testsAdded .nil))
              simpa [countsResult, countsTerm, inspections, tailReads, Nat.add_mul, number,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using built

/-- Summing the actual source counters retains all children. Inventory tests
equal inspections times the interned inventory size. -/
theorem state_counts_returns (state : State) (inventorySize : Nat) (states : List (StateTree Term)) :
    PureReturns program [] state (a "gslt:automata:state-counts" [statesValue inventorySize states]) state
      (encoded (countsTerm inventorySize states)) := by
  apply helper_call .counts [] state [encodeList (stateTerm inventorySize) states] _ _
    (by simp) rfl (counts_body_returns state inventorySize states)

private def bottomStateEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:bottom-state")[0]'(by decide +kernel)
private def bottomStateEnv (patterns : List (Pattern Term)) (head : Term)
    (children : List (Subject Term)) : Subst :=
  [("children", listValue (children.map subjectTerm)), ("head", encoded head),
    ("inventory", shapesValue patterns)]
private def bottomResult : Atom :=
  a "MState" [v "matches", v "states", a "+" [number 1, v "reads"],
    a "+" [v "tests", v "child-tests"]]
private def bottomCases : SpaceSemantics.Cases :=
  [(a "Counts" [v "reads", v "child-tests"], bottomResult)]
private def bottomBody : Atom :=
  a "let*" [.expression
    [.expression [v "states", a "gslt:automata:bottom-states" [v "inventory", v "children"]],
     .expression [v "matches", a "gslt:automata:transition" [v "inventory", v "head", v "states"]],
     .expression [v "counts", a "gslt:automata:state-counts" [v "states"]],
     .expression [v "tests", a "gslt:automata:length" [v "inventory"]]],
    a "case" [v "counts", .expression (bottomCases.map fun row => .expression [row.1, row.2])]]
private theorem bottom_shape : bottomStateEquation.body = bottomBody := by decide +kernel

private theorem bottom_state_call (bindings : Subst) (state : State)
    (patterns : List (Pattern Term)) (head : Term) (children : List (Subject Term))
    (one two answer : Atom)
    (firstCaptured : applySubst bindings one = shapesValue patterns)
    (secondCaptured : applySubst bindings two = encoded (subjectTerm (.node head children)))
    (body : PureReturns program (bottomStateEnv patterns head children) state
      bottomStateEquation.body state answer) :
    PureReturns program bindings state (a "gslt:automata:bottom-state" [one, two]) state answer := by
  apply PureData.raw_authored_call_return program bindings (bottomStateEnv patterns head children)
    state state "gslt:automata:bottom-state" [one, two] bottomStateEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [clauses_use_only_the_named_equations]
    change (equations "gslt:automata:bottom-state").filterMap _ = _
    rw [show equations "gslt:automata:bottom-state" = [bottomStateEquation] from rfl]
    have formals : bottomStateEquation.arguments = [v "inventory", a "MNode" [v "head", v "children"]] := by
      decide +kernel
    simp [formals, firstCaptured, secondCaptured, bottomStateEnv,
      MatchAutomataCompilationExecution.subjectTerm, listValue,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def bottomStatesCons : Atom :=
  a "let*" [.expression
    [.expression [v "head", a "gslt:automata:bottom-state" [v "inventory", v "child"]],
     .expression [v "tail", a "gslt:automata:bottom-states" [v "inventory", v "rest"]]],
    a "LCons" [v "head", v "tail"]]
private def bottomStatesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "child", v "rest"], bottomStatesCons)]
private theorem bottom_states_shape : (equation .states).body =
    a "case" [v "children", .expression (bottomStatesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

mutual
  theorem bottom_state_body_returns (state : State) (patterns : List (Pattern Term))
      (head : Term) (children : List (Subject Term)) :
      PureReturns program (bottomStateEnv patterns head children) state bottomStateEquation.body state
        (encoded (stateTerm patterns.length (analyze patterns (.node head children)))) := by
    let bindings := bottomStateEnv patterns head children
    let states := analyzeList patterns children
    let statesBound := ("states", statesValue patterns.length states) :: bindings
    let matchedPatterns := transition patterns head (states.map BottomUpMatchAutomaton.state)
    let matchesBound := ("matches", shapesValue matchedPatterns) :: statesBound
    let countsBound := ("counts", encoded (countsTerm patterns.length states)) :: matchesBound
    let testsBound := ("tests", number patterns.length) :: countsBound
    let reads := (states.map inspections).sum
    let selected := ("child-tests", number (reads * patterns.length)) :: ("reads", number reads) :: testsBound
    have childrenReturned := helper_call .states bindings state
      [encodeList shapeTerm patterns, encodeList subjectTerm children]
      [v "inventory", v "children"] _
      (by simp [bindings, bottomStateEnv, applySubst, Subst.lookup]) rfl
      (bottom_states_body_returns state patterns children)
    have transitionReturned := helper_call .transition statesBound state
      [encodeList shapeTerm patterns, head, encodeList (stateTerm patterns.length) states]
      [v "inventory", v "head", v "states"] _
      (by simp [statesBound, bindings, bottomStateEnv, applySubst, Subst.lookup]) rfl
      (transition_body_returns state patterns.length patterns head states)
    have countsReturned := helper_call .counts matchesBound state
      [encodeList (stateTerm patterns.length) states] [v "states"] _
      (by simp [matchesBound, statesBound, applySubst, Subst.lookup]) rfl
      (counts_body_returns state patterns.length states)
    have lengthReturned : PureReturns program countsBound state
        (a "gslt:automata:length" [v "inventory"]) state (number patterns.length) := by
      simpa using MatchAutomataSourceExecution.length_captured_returns countsBound state
        (patterns.map shapeTerm) (v "inventory")
        (by simp [countsBound, matchesBound, statesBound, bindings, bottomStateEnv, applySubst, Subst.lookup])
    rw [bottom_shape]
    unfold bottomBody
    apply PureData.let_bindings_return (final := testsBound) (middle := state)
      (pairs := [(v "states", a "gslt:automata:bottom-states" [v "inventory", v "children"]),
        (v "matches", a "gslt:automata:transition" [v "inventory", v "head", v "states"]),
        (v "counts", a "gslt:automata:state-counts" [v "states"]),
        (v "tests", a "gslt:automata:length" [v "inventory"])])
    · refine .cons childrenReturned ?_ (.cons transitionReturned ?_ (.cons countsReturned ?_
        (.cons lengthReturned ?_ (.nil testsBound state))))
      all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, testsBound, countsBound,
        matchesBound, statesBound, bindings, bottomStateEnv, states, matchedPatterns]
    · apply case_returns program testsBound selected state state state (v "counts")
        (a "Counts" [number reads, number (reads * patterns.length)]) bottomResult _ _
        bottomCases (read_cases_encoded _) _ _ _
      · simpa [testsBound, countsBound, countsTerm, reads, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, Subst.lookup] using variable_returns program testsBound state "counts"
      · simp [bottomCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, testsBound, countsBound, matchesBound, statesBound, bindings, bottomStateEnv]
      · have readAdded : PureReturns program selected state (a "+" [number 1, v "reads"]) state
            (number (1 + reads)) := by
          apply native_binary_call_returns program selected state state state state "+"
            _ _ (number 1) (number reads) _ (by decide) (by decide) (by decide)
            (by decide) (grounded_returns program selected state (.int 1)) _ _ (by decide)
          · simpa [selected, applySubst, Subst.lookup] using variable_returns program selected state "reads"
          · simpa [number, CettaWireAtom.encode, Int.natCast_add] using
              StdLib.integer_addition state (1 : Int) (reads : Int)
        have testAdded := addition_returns selected state patterns.length (reads * patterns.length)
          "tests" "child-tests"
          (by simp [selected, testsBound, applySubst, Subst.lookup])
          (by simp [selected, applySubst, Subst.lookup])
        have built := PureData.constructor_return program selected state "MState"
          [v "matches", v "states", a "+" [number 1, v "reads"], a "+" [v "tests", v "child-tests"]]
          [shapesValue matchedPatterns, statesValue patterns.length states,
            number (1 + reads), number (patterns.length + reads * patterns.length)]
          (by decide +kernel) (by decide)
          (.cons (by simpa [selected, testsBound, countsBound, matchesBound, applySubst, Subst.lookup] using
            variable_returns program selected state "matches")
            (.cons (by simpa [selected, testsBound, countsBound, matchesBound, statesBound, applySubst, Subst.lookup] using
              variable_returns program selected state "states") (.cons readAdded (.cons testAdded .nil))))
        simpa [bottomResult, stateTerm, analyze, states, matchedPatterns, reads, Nat.add_mul,
          number, listValue, encodeList_map, CettaWireAtom.encode, CettaWireAtom.encodeMany] using built
  termination_by (sizeOf children, 1)

  theorem bottom_states_body_returns (state : State) (patterns : List (Pattern Term))
      (children : List (Subject Term)) :
      PureReturns program (environment .states [encodeList shapeTerm patterns, encodeList subjectTerm children]) state
        (equation .states).body state (statesValue patterns.length (analyzeList patterns children)) := by
    cases children with
    | nil =>
        let bindings := environment .states [encodeList shapeTerm patterns, encodeList subjectTerm []]
        rw [bottom_states_shape]
        apply case_returns program bindings bindings state state state (v "children")
          (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _ bottomStatesCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "children"
        · simp [bottomStatesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program _ state "LNil"
    | cons first rest =>
        cases first with
        | node head children =>
            let bindings := environment .states
              [encodeList shapeTerm patterns, encodeList subjectTerm (.node head children :: rest)]
            let selected := ("rest", listValue (rest.map subjectTerm)) ::
              ("child", encoded (subjectTerm (.node head children))) :: bindings
            let headValue := encoded (stateTerm patterns.length (analyze patterns (.node head children)))
            let headBound := ("head", headValue) :: selected
            let tailValue := statesValue patterns.length (analyzeList patterns rest)
            let tailBound := ("tail", tailValue) :: headBound
            have firstReturned := bottom_state_call selected state patterns head children (v "inventory") (v "child") _
              (by simp [selected, bindings, environment, applySubst, Subst.lookup])
              (by simp [selected, applySubst, Subst.lookup]) (bottom_state_body_returns state patterns head children)
            have restReturned := helper_call .states headBound state
              [encodeList shapeTerm patterns, encodeList subjectTerm rest] [v "inventory", v "rest"] _
              (by simp [headBound, selected, bindings, environment, applySubst, Subst.lookup]) rfl
              (bottom_states_body_returns state patterns rest)
            rw [bottom_states_shape]
            apply case_returns program bindings selected state state state (v "children")
              (listValue ((.node head children :: rest).map subjectTerm)) bottomStatesCons _ _
              bottomStatesCases (read_cases_encoded _) _ _ _
            · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "children"
            · simp [bottomStatesCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, selected, bindings, environment]
            · unfold bottomStatesCons
              apply PureData.let_bindings_return (final := tailBound) (middle := state)
                (pairs := [(v "head", a "gslt:automata:bottom-state" [v "inventory", v "child"]),
                  (v "tail", a "gslt:automata:bottom-states" [v "inventory", v "rest"])])
              · refine .cons firstReturned ?_ (.cons restReturned ?_ (.nil _ _))
                all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                  tailBound, headBound, headValue, tailValue, selected, bindings, environment]
              · have built := constructor_variables_return program tailBound state "LCons" ["head", "tail"]
                  (by decide +kernel) (by decide)
                simpa [analyzeList, stateTerm, statesValue, listValue, encodeList, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany, tailBound, tailValue, headBound, headValue,
                  applySubst, Subst.lookup] using built
  termination_by (sizeOf children, 0)
end

/-- The executed source constructs the independently computed bottom-up state,
including its constructor-inspection and inventory-test counters. -/
theorem bottom_state_returns (state : State) (patterns : List (Pattern Term)) (subject : Subject Term) :
    PureReturns program [] state (a "gslt:automata:bottom-state"
      [shapesValue patterns, encoded (subjectTerm subject)]) state
      (encoded (stateTerm patterns.length (analyze patterns subject))) := by
  cases subject with
  | node head children =>
      exact bottom_state_call [] state patterns head children _ _ _ (by simp) (by simp)
        (bottom_state_body_returns state patterns head children)

theorem bottom_state_captured_returns (bindings : Subst) (state : State)
    (patterns : List (Pattern Term)) (subject : Subject Term) (one two : Atom)
    (captured : [one, two].map (applySubst bindings) =
      [shapesValue patterns, encoded (subjectTerm subject)]) :
    PureReturns program bindings state (a "gslt:automata:bottom-state" [one, two]) state
      (encoded (stateTerm patterns.length (analyze patterns subject))) := by
  apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:bottom-state"
    [shapesValue patterns, encoded (subjectTerm subject)] [one, two] _ (by decide +kernel) _ (by decide) _
    (bottom_state_returns state patterns subject)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simpa [listValue, encodeList_map] using captured.symm

theorem bottom_states_returns (state : State) (patterns : List (Pattern Term)) (subjects : List (Subject Term)) :
    PureReturns program [] state (a "gslt:automata:bottom-states"
      [shapesValue patterns, listValue (subjects.map subjectTerm)]) state
      (statesValue patterns.length (analyzeList patterns subjects)) := by
  exact helper_call .states [] state [encodeList shapeTerm patterns, encodeList subjectTerm subjects]
    _ _ (by simp) rfl (bottom_states_body_returns state patterns subjects)

private inductive CounterHelper where | select | locations
private def CounterHelper.head : CounterHelper → String
  | .select => "gslt:automata:select"
  | .locations => "gslt:automata:bottom-locations-list"
private def CounterHelper.names : CounterHelper → List String
  | .select => ["patterns", "matches", "path", "next"]
  | .locations => ["patterns", "children", "path", "next"]
private def counterEquation (helper : CounterHelper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def counterEnvironment (helper : CounterHelper) (values : List Term) : Subst :=
  (helper.names.zip (values.map encoded)).reverse

private theorem counter_call (helper : CounterHelper) (bindings : Subst) (state : State)
    (one two three : Term) (next : Nat) (first second third last answer : Atom)
    (captured : [first, second, third].map (applySubst bindings) = [encoded one, encoded two, encoded three])
    (lastReturned : PureReturns program bindings state last state (number next))
    (body : PureReturns program (counterEnvironment helper [one, two, three, .natural next]) state
      (counterEquation helper).body state answer) :
    PureReturns program bindings state (a helper.head [first, second, third, last]) state answer := by
  apply PureData.raw_prefix_authored_call_return program bindings
    (counterEnvironment helper [one, two, three, .natural next]) state state state helper.head
    [first, second, third] [encoded one, encoded two, encoded three] last (number next)
    (counterEquation helper).body answer (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) (by cases helper <;> decide) _
    (by change argumentIsRaw program helper.head 3 = false; cases helper <;> decide +kernel)
    captured lastReturned _ body
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl <;> cases helper <;> decide +kernel
  · rw [clauses_use_only_the_named_equations]
    change (equations helper.head).filterMap _ = _
    rw [show equations helper.head = [counterEquation helper] from by cases helper <;> rfl]
    have formals : (counterEquation helper).arguments = helper.names.map v := by cases helper <;> decide +kernel
    cases helper <;> simp [formals, CounterHelper.names,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      counterEnvironment]

private theorem increment_returns (bindings : Subst) (state : State) (next : Nat)
    (captured : applySubst bindings (v "next") = number next) :
    PureReturns program bindings state (a "+" [v "next", number 1]) state (number (next + 1)) := by
  apply native_binary_call_returns program bindings state state state state "+"
    _ _ (number next) (number 1) _ (by decide) (by decide) (by decide) (by decide) _
    (grounded_returns program bindings state (.int 1)) _ (by decide)
  · simpa [captured] using variable_returns program bindings state "next"
  · simpa [number, CettaWireAtom.encode, Int.natCast_add] using StdLib.integer_addition state (next : Int) 1

private abbrev locationsValue (locations : List SubtermMatching.Location) : Atom :=
  listValue (locations.map locationTerm)
private def selectCons : Atom :=
  a "let" [v "tail", a "gslt:automata:select" [v "ps", v "matches", v "path", a "+" [v "next", number 1]],
    a "if" [a "gslt:automata:member" [v "p", v "matches"],
      a "LCons" [a "At" [v "path", v "next"], v "tail"], v "tail"]]
private def selectCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "p", v "ps"], selectCons)]
private theorem select_shape : (counterEquation .select).body =
    a "case" [v "patterns", .expression (selectCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem location_template : PureData.Template program (a "LCons" [a "At" [v "path", v "next"], v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "At" _ (by decide +kernel) (by decide)
    intro field member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

theorem select_body_returns (state : State) (patterns matchedPatterns : List (Pattern Term))
    (path : SubtermMatching.Position) (next : Nat) :
    PureReturns program (counterEnvironment .select
      [encodeList shapeTerm patterns, encodeList shapeTerm matchedPatterns, positionTerm path, .natural next]) state
      (counterEquation .select).body state
      (locationsValue ((SubtermMatching.select (fun pattern => decide (pattern ∈ matchedPatterns)) next patterns).map
        (fun occurrence => ⟨path, occurrence⟩))) := by
  induction patterns generalizing next with
  | nil =>
      let bindings := counterEnvironment .select
        [encodeList shapeTerm [], encodeList shapeTerm matchedPatterns, positionTerm path, .natural next]
      rw [select_shape]
      apply case_returns program bindings bindings state state state (v "patterns") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ selectCases (read_cases_encoded _) _ _ _
      · simpa [bindings, counterEnvironment, CounterHelper.names, applySubst, Subst.lookup] using
          variable_returns program bindings state "patterns"
      · simp [selectCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons pattern rest ih =>
      let bindings := counterEnvironment .select
        [encodeList shapeTerm (pattern :: rest), encodeList shapeTerm matchedPatterns, positionTerm path, .natural next]
      let selected := ("ps", shapesValue rest) :: ("p", encoded (shapeTerm pattern)) :: bindings
      let tail := locationsValue ((SubtermMatching.select (fun pattern => decide (pattern ∈ matchedPatterns)) (next + 1) rest).map
        (fun occurrence => ⟨path, occurrence⟩))
      let bound := ("tail", tail) :: selected
      have recursive := counter_call .select selected state (encodeList shapeTerm rest)
        (encodeList shapeTerm matchedPatterns) (positionTerm path) (next + 1)
        (v "ps") (v "matches") (v "path") (a "+" [v "next", number 1]) _
        (by simp [selected, bindings, counterEnvironment, CounterHelper.names, applySubst, Subst.lookup])
        (increment_returns selected state next
          (by simp [selected, bindings, counterEnvironment, CounterHelper.names, applySubst, Subst.lookup]))
        (ih (next + 1))
      have tested := member_captured bound state (shapeTerm pattern) (matchedPatterns.map shapeTerm)
        [v "p", v "matches"]
        (by simp [bound, selected, bindings, counterEnvironment, CounterHelper.names, applySubst, Subst.lookup])
      have equivalent : decide (shapeTerm pattern ∈ matchedPatterns.map shapeTerm) = decide (pattern ∈ matchedPatterns) := by
        congr 1
        exact propext (List.mem_map_of_injective MatchAutomataCompilationExecution.shapeTerm_injective)
      rw [equivalent] at tested
      rw [select_shape]
      apply case_returns program bindings selected state state state (v "patterns")
        (shapesValue (pattern :: rest)) selectCons _ _ selectCases (read_cases_encoded _) _ _ _
      · simpa [bindings, counterEnvironment, CounterHelper.names, applySubst, Subst.lookup] using
          variable_returns program bindings state "patterns"
      · simp [selectCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, counterEnvironment, CounterHelper.names]
      · apply let_returns program selected bound state state state (v "tail") _ _ _ _ recursive _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, bindings,
            counterEnvironment, CounterHelper.names, tail]
        · apply if_returns program bound state state state _ _ _ _ _ tested
          by_cases member : pattern ∈ matchedPatterns
          · simpa [SubtermMatching.select, member, Effects.boolean, locationsValue, locationTerm,
              positionTerm, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              bound, selected, bindings, counterEnvironment, CounterHelper.names, tail,
              applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return program bound state _ location_template
          · simpa [SubtermMatching.select, member, Effects.boolean, locationsValue,
              bound, tail, applySubst, Subst.lookup] using variable_returns program bound state "tail"

/-- Authored occurrence selection retains order and duplicate pattern rows. -/
theorem select_returns (state : State) (patterns matchedPatterns : List (Pattern Term))
    (path : SubtermMatching.Position) (next : Nat) :
    PureReturns program [] state (a "gslt:automata:select"
      [shapesValue patterns, shapesValue matchedPatterns, encoded (positionTerm path), number next]) state
      (locationsValue ((SubtermMatching.select (fun pattern => decide (pattern ∈ matchedPatterns)) next patterns).map
        (fun occurrence => ⟨path, occurrence⟩))) :=
  counter_call .select [] state (encodeList shapeTerm patterns) (encodeList shapeTerm matchedPatterns)
    (positionTerm path) next _ _ _ _ _ (by simp) (grounded_returns program [] state (.int next))
    (select_body_returns state patterns matchedPatterns path next)

private def locationsAt (patterns : List (Pattern Term)) (tree : StateTree Term)
    (path : SubtermMatching.Position) : List SubtermMatching.Location :=
  (SubtermMatching.positions tree).flatMap fun entry =>
    (SubtermMatching.select (fun pattern => decide (pattern ∈ BottomUpMatchAutomaton.state entry.2)) 0 patterns).map
      (fun occurrence => ⟨path ++ entry.1, occurrence⟩)

private def locationsBelow (patterns : List (Pattern Term)) (children : List (StateTree Term))
    (path : SubtermMatching.Position) (next : Nat) : List SubtermMatching.Location :=
  (SubtermMatching.positionsList next children).flatMap fun entry =>
    (SubtermMatching.select (fun pattern => decide (pattern ∈ BottomUpMatchAutomaton.state entry.2)) 0 patterns).map
      (fun occurrence => ⟨path ++ entry.1, occurrence⟩)

private theorem locations_node (patterns matchedPatterns : List (Pattern Term)) (reads : Nat)
    (children : List (StateTree Term)) (path : SubtermMatching.Position) :
    locationsAt patterns (.node (matchedPatterns, reads) children) path =
      (SubtermMatching.select (fun pattern => decide (pattern ∈ matchedPatterns)) 0 patterns).map
        (fun occurrence => ⟨path, occurrence⟩) ++ locationsBelow patterns children path 0 := by
  simp [locationsAt, locationsBelow, SubtermMatching.positions, BottomUpMatchAutomaton.state]
  rfl

private theorem locations_children_cons (patterns : List (Pattern Term)) (child : StateTree Term)
    (children : List (StateTree Term)) (path : SubtermMatching.Position) (next : Nat) :
    locationsBelow patterns (child :: children) path next =
      locationsAt patterns child (path ++ [next]) ++ locationsBelow patterns children path (next + 1) := by
  simp [locationsBelow, locationsAt, SubtermMatching.positionsList, List.flatMap_map, List.append_assoc]

private theorem append_captured (bindings : Subst) (state : State) (left right : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst bindings) = [listValue left, listValue right]) :
    PureReturns program bindings state (a "gslt:automata:append" [one, two]) state (listValue (left ++ right)) := by
  apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:append"
    [listValue left, listValue right] [one, two] _ (by decide +kernel) _ (by decide) _
    (MatchAutomataSourceExecution.append_returns state left right)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simpa using captured.symm

private def locationsEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:bottom-locations")[0]'(by decide +kernel)
private def locationsEnv (inventorySize : Nat) (patterns matchedPatterns : List (Pattern Term))
    (reads : Nat) (children : List (StateTree Term)) (path : SubtermMatching.Position) : Subst :=
  [("path", encoded (positionTerm path)), ("tests", number (reads * inventorySize)), ("reads", number reads),
    ("children", statesValue inventorySize children), ("matches", shapesValue matchedPatterns),
    ("patterns", shapesValue patterns)]
private def locationsBody : Atom :=
  a "let*" [.expression
    [.expression [v "here", a "gslt:automata:select" [v "patterns", v "matches", v "path", number 0]],
     .expression [v "below", a "gslt:automata:bottom-locations-list" [v "patterns", v "children", v "path", number 0]]],
    a "gslt:automata:append" [v "here", v "below"]]
private theorem locations_shape : locationsEquation.body = locationsBody := by decide +kernel

private theorem locations_call (bindings : Subst) (state : State) (inventorySize : Nat)
    (patterns matchedPatterns : List (Pattern Term)) (reads : Nat) (children : List (StateTree Term))
    (path : SubtermMatching.Position) (one two three answer : Atom)
    (captured : [one, two, three].map (applySubst bindings) =
      [shapesValue patterns, encoded (stateTerm inventorySize (.node (matchedPatterns, reads) children)),
        encoded (positionTerm path)])
    (returned : PureReturns program (locationsEnv inventorySize patterns matchedPatterns reads children path) state
      locationsEquation.body state answer) :
    PureReturns program bindings state (a "gslt:automata:bottom-locations" [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program bindings
    (locationsEnv inventorySize patterns matchedPatterns reads children path) state state
    "gslt:automata:bottom-locations" [one, two, three] locationsEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured, clauses_use_only_the_named_equations]
    change (equations "gslt:automata:bottom-locations").filterMap _ = _
    rw [show equations "gslt:automata:bottom-locations" = [locationsEquation] from rfl]
    have formals : locationsEquation.arguments =
        [v "patterns", a "MState" [v "matches", v "children", v "reads", v "tests"], v "path"] := by decide +kernel
    simp [formals, stateTerm, listValue, encodeList_map, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, locationsEnv]

private def locationsListCons : Atom :=
  a "let*" [.expression
    [.expression [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [v "next", .symbol "LNil"]]],
     .expression [v "head", a "gslt:automata:bottom-locations" [v "patterns", v "child", v "child-path"]],
     .expression [v "tail", a "gslt:automata:bottom-locations-list" [v "patterns", v "rest", v "path", a "+" [v "next", number 1]]]],
    a "gslt:automata:append" [v "head", v "tail"]]
private def locationsListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "child", v "rest"], locationsListCons)]
private theorem locations_list_shape : (counterEquation .locations).body =
    a "case" [v "children", .expression (locationsListCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

mutual
  theorem bottom_locations_body_returns (state : State) (inventorySize : Nat)
      (patterns matchedPatterns : List (Pattern Term)) (reads : Nat) (children : List (StateTree Term))
      (path : SubtermMatching.Position) :
      PureReturns program (locationsEnv inventorySize patterns matchedPatterns reads children path) state
        locationsEquation.body state (locationsValue (locationsAt patterns (.node (matchedPatterns, reads) children) path)) := by
    let bindings := locationsEnv inventorySize patterns matchedPatterns reads children path
    let here := (SubtermMatching.select (fun pattern => decide (pattern ∈ matchedPatterns)) 0 patterns).map
      (fun occurrence => (⟨path, occurrence⟩ : SubtermMatching.Location))
    let hereBound := ("here", locationsValue here) :: bindings
    let below := locationsBelow patterns children path 0
    let belowBound := ("below", locationsValue below) :: hereBound
    have hereReturned := counter_call .select bindings state (encodeList shapeTerm patterns)
      (encodeList shapeTerm matchedPatterns) (positionTerm path) 0
      (v "patterns") (v "matches") (v "path") (number 0) _
      (by simp [bindings, locationsEnv, applySubst, Subst.lookup])
      (grounded_returns program bindings state (.int 0)) (select_body_returns state patterns matchedPatterns path 0)
    have belowReturned := counter_call .locations hereBound state (encodeList shapeTerm patterns)
      (encodeList (stateTerm inventorySize) children) (positionTerm path) 0
      (v "patterns") (v "children") (v "path") (number 0) _
      (by simp [hereBound, bindings, locationsEnv, applySubst, Subst.lookup])
      (grounded_returns program hereBound state (.int 0))
      (bottom_locations_list_body_returns state inventorySize patterns children path 0)
    rw [locations_shape]
    unfold locationsBody
    apply PureData.let_bindings_return (final := belowBound) (middle := state)
      (pairs := [(v "here", a "gslt:automata:select" [v "patterns", v "matches", v "path", number 0]),
        (v "below", a "gslt:automata:bottom-locations-list" [v "patterns", v "children", v "path", number 0])])
    · refine .cons hereReturned ?_ (.cons belowReturned ?_ (.nil belowBound state))
      all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, belowBound, below,
        hereBound, here, bindings, locationsEnv]
    · rw [locations_node]
      simpa [locationsValue, List.map_append, here, below] using append_captured belowBound state
        (here.map locationTerm) (below.map locationTerm) (v "here") (v "below")
        (by simp [belowBound, hereBound, locationsValue, applySubst, Subst.lookup])
  termination_by (sizeOf children, 1)

  theorem bottom_locations_list_body_returns (state : State) (inventorySize : Nat)
      (patterns : List (Pattern Term)) (children : List (StateTree Term))
      (path : SubtermMatching.Position) (next : Nat) :
      PureReturns program (counterEnvironment .locations
        [encodeList shapeTerm patterns, encodeList (stateTerm inventorySize) children, positionTerm path, .natural next]) state
        (counterEquation .locations).body state (locationsValue (locationsBelow patterns children path next)) := by
    cases children with
    | nil =>
        let bindings := counterEnvironment .locations
          [encodeList shapeTerm patterns, encodeList (stateTerm inventorySize) [], positionTerm path, .natural next]
        rw [locations_list_shape]
        apply case_returns program bindings bindings state state state (v "children") (.symbol "LNil")
          (.symbol "LNil") (.symbol "LNil") _ locationsListCases (read_cases_encoded _) _ _ _
        · simpa [bindings, counterEnvironment, CounterHelper.names, applySubst, Subst.lookup] using
            variable_returns program bindings state "children"
        · simp [locationsListCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program _ state "LNil"
    | cons first rest =>
        cases first with
        | node label children =>
            obtain ⟨matchedPatterns, reads⟩ := label
            let child : StateTree Term := .node (matchedPatterns, reads) children
            let bindings := counterEnvironment .locations
              [encodeList shapeTerm patterns, encodeList (stateTerm inventorySize) (child :: rest), positionTerm path, .natural next]
            let selected := ("rest", statesValue inventorySize rest) :: ("child", encoded (stateTerm inventorySize child)) :: bindings
            let childPath := encoded (positionTerm (path ++ [next]))
            let pathBound := ("child-path", childPath) :: selected
            let head := locationsAt patterns child (path ++ [next])
            let headBound := ("head", locationsValue head) :: pathBound
            let tail := locationsBelow patterns rest path (next + 1)
            let tailBound := ("tail", locationsValue tail) :: headBound
            have pathReturned := append_captured selected state (path.map Term.natural) [.natural next]
              (v "path") (a "LCons" [v "next", .symbol "LNil"])
              (by simp [selected, bindings, counterEnvironment, CounterHelper.names,
                positionTerm, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup])
            have headReturned := locations_call pathBound state inventorySize patterns matchedPatterns reads children
              (path ++ [next]) (v "patterns") (v "child") (v "child-path") _
              (by simp [pathBound, childPath, selected, child, bindings, counterEnvironment, CounterHelper.names,
                applySubst, Subst.lookup])
              (bottom_locations_body_returns state inventorySize patterns matchedPatterns reads children (path ++ [next]))
            have tailReturned := counter_call .locations headBound state (encodeList shapeTerm patterns)
              (encodeList (stateTerm inventorySize) rest) (positionTerm path) (next + 1)
              (v "patterns") (v "rest") (v "path") (a "+" [v "next", number 1]) _
              (by simp [headBound, pathBound, selected, bindings, counterEnvironment, CounterHelper.names,
                applySubst, Subst.lookup])
              (increment_returns headBound state next
                (by simp [headBound, pathBound, selected, bindings, counterEnvironment, CounterHelper.names,
                  applySubst, Subst.lookup]))
              (bottom_locations_list_body_returns state inventorySize patterns rest path (next + 1))
            rw [locations_list_shape]
            apply case_returns program bindings selected state state state (v "children")
              (statesValue inventorySize (child :: rest)) locationsListCons _ _ locationsListCases
              (read_cases_encoded _) _ _ _
            · simpa [bindings, counterEnvironment, CounterHelper.names, child, applySubst, Subst.lookup] using
                variable_returns program bindings state "children"
            · simp [locationsListCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, selected, bindings, counterEnvironment, CounterHelper.names]
            · unfold locationsListCons
              apply PureData.let_bindings_return (final := tailBound) (middle := state)
                (pairs := [(v "child-path", a "gslt:automata:append" [v "path", a "LCons" [v "next", .symbol "LNil"]]),
                  (v "head", a "gslt:automata:bottom-locations" [v "patterns", v "child", v "child-path"]),
                  (v "tail", a "gslt:automata:bottom-locations-list" [v "patterns", v "rest", v "path", a "+" [v "next", number 1]])])
              · refine .cons (value := childPath) ?_ ?_
                  (.cons headReturned ?_ (.cons tailReturned ?_ (.nil tailBound state)))
                · rw [show path.map Term.natural ++ [.natural next] = (path ++ [next]).map Term.natural from by simp]
                    at pathReturned
                  simpa only [childPath, positionTerm, listValue, encodeList_map, Function.id_comp] using pathReturned
                all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, tail,
                  headBound, head, child, pathBound, childPath, selected, bindings, counterEnvironment, CounterHelper.names]
              · rw [locations_children_cons]
                simpa [locationsValue, child, head, tail, List.map_append] using append_captured tailBound state
                  (head.map locationTerm) (tail.map locationTerm) (v "head") (v "tail")
                  (by simp [tailBound, headBound, locationsValue, applySubst, Subst.lookup])
  termination_by (sizeOf children, 0)
end

/-- Source observation of an analyzed state equals the generic machine's
canonical occurrence-location list. -/
theorem bottom_locations_returns (state : State) (patterns : List (Pattern Term)) (subject : Subject Term) :
    PureReturns program [] state (a "gslt:automata:bottom-locations"
      [shapesValue patterns, encoded (stateTerm (inventory patterns).length (analyze (inventory patterns) subject)),
        encoded (positionTerm [])]) state (locationsValue (BottomUpMatchAutomaton.run patterns subject)) := by
  cases analyzed : analyze (inventory patterns) subject with
  | node label children =>
      obtain ⟨matchedPatterns, reads⟩ := label
      have returned := locations_call [] state (inventory patterns).length patterns matchedPatterns reads children []
        (shapesValue patterns) (encoded (stateTerm (inventory patterns).length (.node (matchedPatterns, reads) children)))
        (encoded (positionTerm [])) _ (by simp)
        (bottom_locations_body_returns state (inventory patterns).length patterns matchedPatterns reads children [])
      simpa [BottomUpMatchAutomaton.run, analyzed, locationsAt] using returned

theorem bottom_locations_captured_returns (bindings : Subst) (state : State)
    (patterns : List (Pattern Term)) (subject : Subject Term) (one two three : Atom)
    (captured : [one, two, three].map (applySubst bindings) =
      [shapesValue patterns, encoded (stateTerm (inventory patterns).length (analyze (inventory patterns) subject)),
        encoded (positionTerm [])]) :
    PureReturns program bindings state (a "gslt:automata:bottom-locations" [one, two, three]) state
      (locationsValue (BottomUpMatchAutomaton.run patterns subject)) := by
  apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:bottom-locations"
    [shapesValue patterns, encoded (stateTerm (inventory patterns).length (analyze (inventory patterns) subject)),
      encoded (positionTerm [])] [one, two, three] _ (by decide +kernel) _ (by decide) _
    (bottom_locations_returns state patterns subject)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · simpa [listValue, encodeList_map] using captured.symm

#print axioms child_accept_returns
#print axioms accept_returns
#print axioms transition_completed_iff
#print axioms state_counts_returns
#print axioms bottom_state_returns
#print axioms select_returns
#print axioms bottom_locations_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBottomExecution
