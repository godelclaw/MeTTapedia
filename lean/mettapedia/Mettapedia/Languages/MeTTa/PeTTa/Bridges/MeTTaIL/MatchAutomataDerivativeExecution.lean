import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataSourceExecution

/-!
# The position derivative executes in the retained PeTTa source

The theorem quantifies over every observation and finite obligation list on
the shared wire carrier. Consuming, retaining and refusing obligations are
proved by composing the actual equation, native equality, first-match cases
and recursive calls. There is no primitive that asks the Lean derivative for
its result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataDerivativeExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire OrderedPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval MatchAutomataProgram
open MatchAutomataSourceExecution (listValue)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

def positionTerm (position : SubtermMatching.Position) : Term := encodeList Term.natural position
def keyTerm (key : ConstructorKey Term) : Term := .application "MKey" [key.head, .natural key.arity]
def obligationTerm (obligation : TopDownMatchDerivatives.Obligation Term) : Term :=
  .application "Observe" [positionTerm obligation.position, keyTerm obligation.key]
def optionTerm : Option (List (TopDownMatchDerivatives.Obligation Term)) → Term
  | none => .symbol "None"
  | some residual => .application "Some" [encodeList obligationTerm residual]

private theorem positionTerm_injective : Function.Injective positionTerm := by
  intro left right same
  induction left generalizing right with
  | nil => cases right <;> simp_all [positionTerm, encodeList]
  | cons first rest ih =>
      cases right with
      | nil => simp [positionTerm, encodeList] at same
      | cons other tail =>
          have arguments := (Term.application.inj same).2
          have heads := (List.cons.inj arguments).1
          have tails := (List.cons.inj (List.cons.inj arguments).2).1
          exact congrArg₂ List.cons (Term.natural.inj heads) (ih tails)

private theorem keyTerm_injective : Function.Injective keyTerm := by
  intro left right same
  obtain ⟨head, arity⟩ := left
  obtain ⟨other, count⟩ := right
  have arguments := (Term.application.inj same).2
  have heads := (List.cons.inj arguments).1
  have arities := (List.cons.inj (List.cons.inj arguments).2).1
  exact congrArg₂ ConstructorKey.mk heads (Term.natural.inj arities)

private def deriveEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:derive")[0]'(by decide +kernel)

private def recursiveCall : Atom := a "gslt:automata:derive" [a "Observe" [v "position", v "key"], v "rest"]
private def retained : Atom := a "Some" [a "LCons" [a "Observe" [v "expected-position", v "expected-key"], v "tail"]]
private def resultCases : SpaceSemantics.Cases :=
  [(a "Some" [v "tail"], retained), (.symbol "None", .symbol "None")]
private def consBody : Atom :=
  a "if" [a "==" [v "position", v "expected-position"],
    a "if" [a "==" [v "key", v "expected-key"], recursiveCall, .symbol "None"],
    a "case" [recursiveCall, .expression (resultCases.map fun row => .expression [row.1, row.2])]]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [.symbol "LNil"]),
    (a "LCons" [a "Observe" [v "expected-position", v "expected-key"], v "rest"], consBody)]

private theorem shape : deriveEquation.body =
    a "case" [v "pending", .expression (cases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def environment (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) : Subst :=
  [("pending", listValue (pending.map obligationTerm)),
    ("key", CettaWireAtom.encode (keyTerm observation.key)),
    ("position", CettaWireAtom.encode (positionTerm observation.position))]

private theorem clause (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    clauses program "gslt:automata:derive"
      [CettaWireAtom.encode (obligationTerm observation), listValue (pending.map obligationTerm)] =
      [.evaluate (environment observation pending) deriveEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:derive").filterMap _ = _
  rw [show equations "gslt:automata:derive" = [deriveEquation] from rfl]
  have formals : deriveEquation.arguments = [a "Observe" [v "position", v "key"], v "pending"] := by
    decide +kernel
  simp [formals, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

private theorem call (bindings : Subst) (state : State)
    (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [CettaWireAtom.encode (obligationTerm observation), listValue (pending.map obligationTerm)])
    (length : arguments.length = 2)
    (body : PureReturns program (environment observation pending) state deriveEquation.body state
      (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation pending)))) :
    PureReturns program bindings state (a "gslt:automata:derive" arguments) state
      (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation pending))) := by
  apply PureData.raw_authored_call_return program bindings (environment observation pending) state state
    "gslt:automata:derive" arguments deriveEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact clause observation pending

private theorem nil_template : PureData.Template program (a "Some" [.symbol "LNil"]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact .symbol _

private theorem retained_template : PureData.Template program retained := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Observe" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

theorem body_returns (state : State) (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program (environment observation pending) state deriveEquation.body state
      (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation pending))) := by
  induction pending with
  | nil =>
      rw [shape]
      apply case_returns program (environment observation []) (environment observation []) state state state
        (v "pending") (.symbol "LNil") (a "Some" [.symbol "LNil"])
        (a "Some" [.symbol "LNil"]) _ cases (read_cases_encoded _) _ _ _
      · simpa [environment, applySubst, Subst.lookup, listValue, encodeList, CettaWireAtom.encode] using
          variable_returns program (environment observation []) state "pending"
      · simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact PureData.template_return program (environment observation []) state _ nil_template
  | cons first rest ih =>
      let bindings := environment observation (first :: rest)
      let selected := ("rest", listValue (rest.map obligationTerm)) ::
        ("expected-key", CettaWireAtom.encode (keyTerm first.key)) ::
        ("expected-position", CettaWireAtom.encode (positionTerm first.position)) :: bindings
      have recursive : PureReturns program selected state recursiveCall state
          (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation rest))) := by
        apply call selected state observation rest _ _ rfl ih
        simp [selected, bindings, environment, applySubst, applySubst.applySubstList,
          Subst.lookup, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      have positionTest : PureReturns program selected state
          (a "==" [v "position", v "expected-position"]) state
          (Effects.boolean (decide (observation.position = first.position))) := by
        have computed := CettaWireAtom.equality_captured_returns program selected state
          (positionTerm observation.position)
          (positionTerm first.position) "position" "expected-position"
          (by simp [selected, bindings, environment, applySubst, Subst.lookup])
          (by simp [selected, applySubst, Subst.lookup])
        have exactness : positionTerm observation.position = positionTerm first.position ↔
            observation.position = first.position := positionTerm_injective.eq_iff
        simpa only [exactness] using computed
      rw [shape]
      apply case_returns program bindings selected state state state (v "pending")
        (listValue ((first :: rest).map obligationTerm)) consBody
        (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation (first :: rest))))
        _ cases (read_cases_encoded _) _ _ _
      · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "pending"
      · simp [cases, listValue, encodeList, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, environment]
      · apply if_returns program selected state state state _ _ _ _ _ positionTest
        by_cases samePosition : observation.position = first.position
        · simp only [samePosition, decide_true, Effects.boolean, BEq.beq]
          have keyTest : PureReturns program selected state (a "==" [v "key", v "expected-key"]) state
              (Effects.boolean (decide (observation.key = first.key))) := by
            have computed := CettaWireAtom.equality_captured_returns program selected state
              (keyTerm observation.key) (keyTerm first.key)
              "key" "expected-key"
              (by simp [selected, bindings, environment, applySubst, Subst.lookup])
              (by simp [selected, applySubst, Subst.lookup])
            simpa only [keyTerm_injective.eq_iff] using computed
          apply if_returns program selected state state state _ _ _ _ _ keyTest
          by_cases sameKey : observation.key = first.key
          · simpa [Effects.boolean, sameKey, samePosition, TopDownMatchDerivatives.derive] using recursive
          · simpa [Effects.boolean, sameKey, Ne.symm sameKey, samePosition, TopDownMatchDerivatives.derive,
              optionTerm, CettaWireAtom.encode] using symbol_returns program selected state "None"
        · have reverse : first.position ≠ observation.position := Ne.symm samePosition
          simp only [samePosition, decide_false, Effects.boolean]
          cases result : TopDownMatchDerivatives.derive observation rest with
          | none =>
              have completed : PureReturns program selected state recursiveCall state (.symbol "None") := by
                simpa [result, optionTerm, CettaWireAtom.encode] using recursive
              apply case_returns program selected selected state state state recursiveCall (.symbol "None")
                (.symbol "None") _ _ resultCases (read_cases_encoded _) completed _ _
              · simp [resultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [TopDownMatchDerivatives.derive, reverse, result, optionTerm, CettaWireAtom.encode] using
                  symbol_returns program selected state "None"
          | some residual =>
              let bound := ("tail", listValue (residual.map obligationTerm)) :: selected
              have completed : PureReturns program selected state recursiveCall state
                  (a "Some" [listValue (residual.map obligationTerm)]) := by
                simpa [result, optionTerm, listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using recursive
              apply case_returns program selected bound state state state recursiveCall
                (a "Some" [listValue (residual.map obligationTerm)]) retained _ _ resultCases
                (read_cases_encoded _) completed _ _
              · simp [resultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                  bound, selected, bindings, environment]
              · simpa [retained, TopDownMatchDerivatives.derive, reverse, result, optionTerm,
                  obligationTerm, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  applySubst, applySubst.applySubstList, Subst.lookup, bound, selected, bindings, environment]
                  using PureData.template_return program bound state _ retained_template

/-- The actual MeTTa derivative preserves and reflects the Lean transition
result, for all represented observation/obligation vectors. -/
theorem derive_returns (state : State) (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program [] state
      (a "gslt:automata:derive" [CettaWireAtom.encode (obligationTerm observation),
        listValue (pending.map obligationTerm)]) state
      (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation pending))) :=
  call [] state observation pending _ (by simp) rfl (body_returns state observation pending)

/-- Captured arguments use the same actual source body as a top-level call. -/
theorem derive_captured_returns (bindings : Subst) (state : State)
    (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [CettaWireAtom.encode (obligationTerm observation), listValue (pending.map obligationTerm)]) :
    PureReturns program bindings state (a "gslt:automata:derive" arguments) state
      (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation pending))) := by
  have length : arguments.length = 2 := by
    simpa using congrArg List.length captured
  exact call bindings state observation pending arguments captured length
    (body_returns state observation pending)

def locationTerm (location : SubtermMatching.Location) : Term :=
  .application "At" [positionTerm location.position, .natural location.occurrence]

def goalTerm (goal : TopDownMatchDerivatives.Goal Term) : Term :=
  .application "MGoal" [locationTerm goal.location, encodeList obligationTerm goal.pending]

private def goalsEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:derive-goals")[0]'(by decide +kernel)
private def goalsRecursive : Atom := a "gslt:automata:derive-goals" [v "observation", v "rest"]
private def goalsRetained : Atom := a "LCons" [a "MGoal" [v "location", v "remaining"], v "tail"]
private def goalsResultCases : SpaceSemantics.Cases :=
  [(a "Some" [v "remaining"], goalsRetained), (.symbol "None", v "tail")]
private def goalsCons : Atom :=
  a "let" [v "tail", goalsRecursive,
    a "case" [a "gslt:automata:derive" [v "observation", v "pending"],
      .expression (goalsResultCases.map fun row => .expression [row.1, row.2])]]
private def goalsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "MGoal" [v "location", v "pending"], v "rest"], goalsCons)]

private theorem goals_shape : goalsEquation.body =
    a "case" [v "goals", .expression (goalsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def goalsEnvironment (observation : TopDownMatchDerivatives.Observation Term)
    (goals : List (TopDownMatchDerivatives.Goal Term)) : Subst :=
  [("goals", listValue (goals.map goalTerm)), ("observation", CettaWireAtom.encode (obligationTerm observation))]

private theorem goals_clause (observation : TopDownMatchDerivatives.Observation Term)
    (goals : List (TopDownMatchDerivatives.Goal Term)) :
    clauses program "gslt:automata:derive-goals"
      [CettaWireAtom.encode (obligationTerm observation), listValue (goals.map goalTerm)] =
      [.evaluate (goalsEnvironment observation goals) goalsEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:derive-goals").filterMap _ = _
  rw [show equations "gslt:automata:derive-goals" = [goalsEquation] from rfl]
  have formals : goalsEquation.arguments = [v "observation", v "goals"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, goalsEnvironment]

private theorem goals_call (bindings : Subst) (state : State)
    (observation : TopDownMatchDerivatives.Observation Term)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [CettaWireAtom.encode (obligationTerm observation), listValue (goals.map goalTerm)])
    (body : PureReturns program (goalsEnvironment observation goals) state goalsEquation.body state
      (listValue ((TopDownMatchDerivatives.deriveGoals observation goals).map goalTerm))) :
    PureReturns program bindings state (a "gslt:automata:derive-goals" arguments) state
      (listValue ((TopDownMatchDerivatives.deriveGoals observation goals).map goalTerm)) := by
  have length : arguments.length = 2 := by simpa using congrArg List.length captured
  apply PureData.raw_authored_call_return program bindings (goalsEnvironment observation goals) state state
    "gslt:automata:derive-goals" arguments goalsEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact goals_clause observation goals

private theorem goals_retained_template : PureData.Template program goalsRetained := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "MGoal" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

theorem goals_body_returns (state : State) (observation : TopDownMatchDerivatives.Observation Term)
    (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program (goalsEnvironment observation goals) state goalsEquation.body state
      (listValue ((TopDownMatchDerivatives.deriveGoals observation goals).map goalTerm)) := by
  induction goals with
  | nil =>
      rw [goals_shape]
      apply case_returns program (goalsEnvironment observation []) (goalsEnvironment observation [])
        state state state (v "goals") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil")
        _ goalsCases (read_cases_encoded _) _ _ _
      · simpa [goalsEnvironment, applySubst, Subst.lookup, listValue, encodeList, CettaWireAtom.encode]
          using variable_returns program (goalsEnvironment observation []) state "goals"
      · simp [goalsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program (goalsEnvironment observation []) state "LNil"
  | cons first rest ih =>
      let bindings := goalsEnvironment observation (first :: rest)
      let selected := ("rest", listValue (rest.map goalTerm)) ::
        ("pending", listValue (first.pending.map obligationTerm)) ::
        ("location", CettaWireAtom.encode (locationTerm first.location)) :: bindings
      let after := TopDownMatchDerivatives.deriveGoals observation rest
      let tailBound := ("tail", listValue (after.map goalTerm)) :: selected
      have recursive : PureReturns program selected state goalsRecursive state (listValue (after.map goalTerm)) := by
        apply goals_call selected state observation rest _ _ ih
        simp [selected, bindings, goalsEnvironment, applySubst, Subst.lookup]
      have derivative : PureReturns program tailBound state
          (a "gslt:automata:derive" [v "observation", v "pending"]) state
          (CettaWireAtom.encode (optionTerm (TopDownMatchDerivatives.derive observation first.pending))) := by
        apply derive_captured_returns
        simp [tailBound, selected, bindings, goalsEnvironment, applySubst, Subst.lookup]
      rw [goals_shape]
      apply case_returns program bindings selected state state state (v "goals")
        (listValue ((first :: rest).map goalTerm)) goalsCons _ _ goalsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, goalsEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "goals"
      · simp [goalsCases, listValue, encodeList, goalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, goalsEnvironment]
      · apply let_returns program selected tailBound state state state (v "tail") goalsRecursive _
          (listValue (after.map goalTerm)) _ recursive _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings,
            goalsEnvironment, tailBound]
        · cases result : TopDownMatchDerivatives.derive observation first.pending with
          | none =>
              have completed : PureReturns program tailBound state
                  (a "gslt:automata:derive" [v "observation", v "pending"]) state (.symbol "None") := by
                simpa [result, optionTerm, CettaWireAtom.encode] using derivative
              apply case_returns program tailBound tailBound state state state _ (.symbol "None")
                (v "tail") _ _ goalsResultCases (read_cases_encoded _) completed _ _
              · simp [goalsResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [TopDownMatchDerivatives.deriveGoals, result, after, tailBound,
                  applySubst, Subst.lookup] using variable_returns program tailBound state "tail"
          | some residual =>
              let bound := ("remaining", listValue (residual.map obligationTerm)) :: tailBound
              have completed : PureReturns program tailBound state
                  (a "gslt:automata:derive" [v "observation", v "pending"]) state
                  (a "Some" [listValue (residual.map obligationTerm)]) := by
                simpa [result, optionTerm, listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using derivative
              apply case_returns program tailBound bound state state state _
                (a "Some" [listValue (residual.map obligationTerm)]) goalsRetained _ _ goalsResultCases
                (read_cases_encoded _) completed _ _
              · simp [goalsResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                  bound, tailBound, selected, bindings, goalsEnvironment]
              · simpa [goalsRetained, TopDownMatchDerivatives.deriveGoals, result, goalTerm,
                  after, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  bound, tailBound, selected, bindings, goalsEnvironment,
                  applySubst, applySubst.applySubstList, Subst.lookup]
                  using PureData.template_return program bound state _ goals_retained_template

/-- Every authored goal occurrence retains its identity. Conflicting goals
are removed; surviving duplicates stay in their original order. -/
theorem deriveGoals_returns (state : State) (observation : TopDownMatchDerivatives.Observation Term)
    (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program [] state
      (a "gslt:automata:derive-goals" [CettaWireAtom.encode (obligationTerm observation),
        listValue (goals.map goalTerm)]) state
      (listValue ((TopDownMatchDerivatives.deriveGoals observation goals).map goalTerm)) :=
  goals_call [] state observation goals _ (by simp) (goals_body_returns state observation goals)

def finishedTerm (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat) : Term :=
  .application "MFinished" [encodeList goalTerm goals, .natural dispatches]

private abbrev number (count : Nat) : Atom := CettaWireAtom.encode (.natural count)
private def executeEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:execute")[0]'(by decide +kernel)
private def executePairs : List Atom :=
  [.expression [v "count", a "gslt:automata:length" [v "goals"]],
    .expression [v "next", a "gslt:automata:derive-goals" [v "observation", v "goals"]]]
private def executeRecursive : Atom :=
  a "gslt:automata:execute" [v "rest", v "next", a "+" [v "dispatches", v "count"]]
private def executeCons : Atom := a "let*" [.expression executePairs, executeRecursive]
private def executeNil : Atom := a "MFinished" [v "goals", v "dispatches"]
private def executeCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", executeNil), (a "LCons" [v "observation", v "rest"], executeCons)]

private theorem execute_shape : executeEquation.body =
    a "case" [v "observations", .expression (executeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def executeEnvironment (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat) : Subst :=
  [("dispatches", number dispatches), ("goals", listValue (goals.map goalTerm)),
    ("observations", listValue (observations.map obligationTerm))]

private theorem execute_clause (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat) :
    clauses program "gslt:automata:execute"
      [listValue (observations.map obligationTerm), listValue (goals.map goalTerm), number dispatches] =
      [.evaluate (executeEnvironment observations goals dispatches) executeEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:execute").filterMap _ = _
  rw [show equations "gslt:automata:execute" = [executeEquation] from rfl]
  have formals : executeEquation.arguments = [v "observations", v "goals", v "dispatches"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, executeEnvironment]

private theorem execute_call (bindings : Subst) (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat)
    (observationArg goalArg dispatchArg : Atom)
    (observationsCaptured : applySubst bindings observationArg = listValue (observations.map obligationTerm))
    (goalsCaptured : applySubst bindings goalArg = listValue (goals.map goalTerm))
    (dispatchComputed : PureReturns program bindings state dispatchArg state (number dispatches))
    (body : PureReturns program (executeEnvironment observations goals dispatches) state executeEquation.body state
      (CettaWireAtom.encode (finishedTerm (TopDownMatchDerivatives.executeCounted observations goals).1
        (dispatches + (TopDownMatchDerivatives.executeCounted observations goals).2)))) :
    PureReturns program bindings state (a "gslt:automata:execute" [observationArg, goalArg, dispatchArg]) state
      (CettaWireAtom.encode (finishedTerm (TopDownMatchDerivatives.executeCounted observations goals).1
        (dispatches + (TopDownMatchDerivatives.executeCounted observations goals).2))) := by
  apply call_returns program bindings state state "gslt:automata:execute" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "gslt:automata:execute" observationArg _ [] 0 _
    (by decide +kernel)
  simp only [observationsCaptured, List.nil_append]
  apply raw_argument_answers program bindings state state "gslt:automata:execute" goalArg _ _ 1 _
    (by decide +kernel)
  simp only [goalsCaptured, List.singleton_append]
  apply evaluated_argument_returns program bindings state state state (.function "gslt:automata:execute")
    dispatchArg (number dispatches) _ [] _ 2 (by decide +kernel) dispatchComputed
  simpa using authored_function_arguments_return program bindings
    (executeEnvironment observations goals dispatches) state state "gslt:automata:execute"
    _ 3 executeEquation.body _ (by decide) (by decide) (execute_clause observations goals dispatches) body

private theorem execute_nil_template : PureData.Template program executeNil := by
  apply PureData.Template.constructor "MFinished" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

theorem execute_body_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat) :
    PureReturns program (executeEnvironment observations goals dispatches) state executeEquation.body state
      (CettaWireAtom.encode (finishedTerm (TopDownMatchDerivatives.executeCounted observations goals).1
        (dispatches + (TopDownMatchDerivatives.executeCounted observations goals).2))) := by
  induction observations generalizing goals dispatches with
  | nil =>
      rw [execute_shape]
      apply case_returns program (executeEnvironment [] goals dispatches) (executeEnvironment [] goals dispatches)
        state state state (v "observations") (.symbol "LNil") executeNil _ _ executeCases (read_cases_encoded _) _ _ _
      · simpa [executeEnvironment, applySubst, Subst.lookup, listValue, encodeList, CettaWireAtom.encode]
          using variable_returns program (executeEnvironment [] goals dispatches) state "observations"
      · simp [executeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [executeNil, executeEnvironment, TopDownMatchDerivatives.executeCounted, finishedTerm,
          listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup]
          using PureData.template_return program (executeEnvironment [] goals dispatches) state _ execute_nil_template
  | cons first rest ih =>
      let bindings := executeEnvironment (first :: rest) goals dispatches
      let selected := ("rest", listValue (rest.map obligationTerm)) ::
        ("observation", CettaWireAtom.encode (obligationTerm first)) :: bindings
      let countBound := ("count", number goals.length) :: selected
      let next := TopDownMatchDerivatives.deriveGoals first goals
      let nextBound := ("next", listValue (next.map goalTerm)) :: countBound
      have counted : PureReturns program selected state (a "gslt:automata:length" [v "goals"]) state
          (number goals.length) := by
        simpa using MatchAutomataSourceExecution.length_captured_returns selected state (goals.map goalTerm)
          (v "goals") (by simp [selected, bindings, executeEnvironment, applySubst, Subst.lookup])
      have derived : PureReturns program countBound state
          (a "gslt:automata:derive-goals" [v "observation", v "goals"]) state
          (listValue (next.map goalTerm)) := by
        apply goals_call countBound state first goals _ _ (goals_body_returns state first goals)
        simp [countBound, selected, bindings, executeEnvironment, applySubst, Subst.lookup]
      have added : PureReturns program nextBound state (a "+" [v "dispatches", v "count"]) state
          (number (dispatches + goals.length)) := by
        apply native_variable_call_returns program nextBound state state "+" ["dispatches", "count"] _
          (by decide) (by decide) _ (by decide)
        simpa [nextBound, countBound, selected, bindings, executeEnvironment, applySubst, Subst.lookup,
          number, CettaWireAtom.encode, Int.natCast_add] using
          StdLib.integer_addition state (dispatches : Int) (goals.length : Int)
      rw [execute_shape]
      apply case_returns program bindings selected state state state (v "observations")
        (listValue ((first :: rest).map obligationTerm)) executeCons _ _ executeCases (read_cases_encoded _) _ _ _
      · simpa [bindings, executeEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "observations"
      · simp [executeCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, executeEnvironment]
      · apply let_star_returns program selected state state executePairs executeRecursive
          (a "let" [v "count", a "gslt:automata:length" [v "goals"],
            a "let" [v "next", a "gslt:automata:derive-goals" [v "observation", v "goals"], executeRecursive]])
          _ rfl
        apply let_returns program selected countBound state state state (v "count") _ _ _ _ counted _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            countBound, selected, bindings, executeEnvironment]
        · apply let_returns program countBound nextBound state state state (v "next") _ _ _ _ derived _ _
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, countBound, selected, bindings, executeEnvironment]
          · have recursive := execute_call nextBound state rest next (dispatches + goals.length)
              (v "rest") (v "next") (a "+" [v "dispatches", v "count"])
              (by simp [nextBound, countBound, selected, applySubst, Subst.lookup])
              (by simp [nextBound, applySubst, Subst.lookup]) added (ih next (dispatches + goals.length))
            simpa [executeRecursive, TopDownMatchDerivatives.executeCounted, next, Nat.add_assoc] using recursive

/-- Arbitrary observation streams execute with their exact surviving goal
occurrences and live-candidate dispatch count. Source fuel is not target fuel. -/
theorem execute_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat) :
    PureReturns program [] state
      (a "gslt:automata:execute" [listValue (observations.map obligationTerm),
        listValue (goals.map goalTerm), number dispatches]) state
      (CettaWireAtom.encode (finishedTerm (TopDownMatchDerivatives.executeCounted observations goals).1
        (dispatches + (TopDownMatchDerivatives.executeCounted observations goals).2))) :=
  execute_call [] state observations goals dispatches _ _ _ (by simp) (by simp)
    (grounded_returns program [] state (.int dispatches))
    (execute_body_returns state observations goals dispatches)

/-- Preservation and reflection include answers, store, unread input and
printed output, for every completed run of the retained source loop. -/
theorem execute_completed_iff (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (dispatches : Nat)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (a "gslt:automata:execute"
          [listValue (observations.map obligationTerm), listValue (goals.map goalTerm), number dispatches]) }
      (.complete after answers input output) ↔
      after = state ∧
      answers = [CettaWireAtom.encode (finishedTerm (TopDownMatchDerivatives.executeCounted observations goals).1
        (dispatches + (TopDownMatchDerivatives.executeCounted observations goals).2))] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (execute_returns state observations goals dispatches) after answers input output

private def completedEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:completed")[0]'(by decide +kernel)
private def completedRetained : Atom := a "LCons" [v "location", v "tail"]
private def completedCons : Atom :=
  a "let" [v "tail", a "gslt:automata:completed" [v "rest"],
    a "if" [a "==" [v "pending", .symbol "LNil"], completedRetained, v "tail"]]
private def completedCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "MGoal" [v "location", v "pending"], v "rest"], completedCons)]

private theorem completed_shape : completedEquation.body =
    a "case" [v "goals", .expression (completedCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def completedEnvironment (goals : List (TopDownMatchDerivatives.Goal Term)) : Subst :=
  [("goals", listValue (goals.map goalTerm))]

private theorem completed_clause (goals : List (TopDownMatchDerivatives.Goal Term)) :
    clauses program "gslt:automata:completed" [listValue (goals.map goalTerm)] =
      [.evaluate (completedEnvironment goals) completedEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:completed").filterMap _ = _
  rw [show equations "gslt:automata:completed" = [completedEquation] from rfl]
  have formals : completedEquation.arguments = [v "goals"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, completedEnvironment]

private theorem completed_call (bindings : Subst) (state : State)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = listValue (goals.map goalTerm))
    (body : PureReturns program (completedEnvironment goals) state completedEquation.body state
      (listValue ((TopDownMatchDerivatives.completed goals).map locationTerm))) :
    PureReturns program bindings state (a "gslt:automata:completed" [argument]) state
      (listValue ((TopDownMatchDerivatives.completed goals).map locationTerm)) := by
  apply PureData.raw_authored_call_return program bindings (completedEnvironment goals) state state
    "gslt:automata:completed" [argument] completedEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · simpa [captured] using completed_clause goals

private theorem completed_retained_template : PureData.Template program completedRetained := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

theorem completed_body_returns (state : State) (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program (completedEnvironment goals) state completedEquation.body state
      (listValue ((TopDownMatchDerivatives.completed goals).map locationTerm)) := by
  induction goals with
  | nil =>
      rw [completed_shape]
      apply case_returns program (completedEnvironment []) (completedEnvironment []) state state state
        (v "goals") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil")
        _ completedCases (read_cases_encoded _) _ _ _
      · simpa [completedEnvironment, applySubst, Subst.lookup, listValue, encodeList, CettaWireAtom.encode]
          using variable_returns program (completedEnvironment []) state "goals"
      · simp [completedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program (completedEnvironment []) state "LNil"
  | cons first rest ih =>
      let bindings := completedEnvironment (first :: rest)
      let selected := ("rest", listValue (rest.map goalTerm)) ::
        ("pending", listValue (first.pending.map obligationTerm)) ::
        ("location", CettaWireAtom.encode (locationTerm first.location)) :: bindings
      let tail := TopDownMatchDerivatives.completed rest
      let bound := ("tail", listValue (tail.map locationTerm)) :: selected
      have recursive : PureReturns program selected state (a "gslt:automata:completed" [v "rest"]) state
          (listValue (tail.map locationTerm)) := by
        apply completed_call selected state rest _ _ ih
        simp [selected, applySubst, Subst.lookup]
      have emptyTest : PureReturns program bound state (a "==" [v "pending", .symbol "LNil"]) state
          (Effects.boolean first.pending.isEmpty) := by
        apply native_binary_call_returns program bound state state state state "==" _ _
          (listValue (first.pending.map obligationTerm)) (.symbol "LNil") _
          (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
        · simpa [bound, selected, applySubst, Subst.lookup] using variable_returns program bound state "pending"
        · exact symbol_returns program bound state "LNil"
        · rw [StdLib.structural_equality]
          have comparison : (listValue (first.pending.map obligationTerm) == .symbol "LNil") =
              first.pending.isEmpty := by
            cases first.pending with
            | nil => simp [listValue, encodeList, CettaWireAtom.encode]
            | cons first rest =>
                apply Bool.eq_false_iff.mpr
                simp [listValue, encodeList, CettaWireAtom.encode]
          rw [comparison]
      rw [completed_shape]
      apply case_returns program bindings selected state state state (v "goals")
        (listValue ((first :: rest).map goalTerm)) completedCons _ _ completedCases (read_cases_encoded _) _ _ _
      · simpa [bindings, completedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "goals"
      · simp [completedCases, listValue, encodeList, goalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, completedEnvironment]
      · apply let_returns program selected bound state state state (v "tail") _ _ _ _ recursive _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            bound, selected, bindings, completedEnvironment]
        · apply if_returns program bound state state state _ _ _ _ _ emptyTest
          by_cases empty : first.pending.isEmpty = true
          · have noPending : first.pending = [] := by simpa using empty
            simpa [Effects.boolean, noPending, TopDownMatchDerivatives.completed, List.filterMap_cons,
              completedRetained, tail, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              bound, selected, bindings, completedEnvironment, applySubst, applySubst.applySubstList, Subst.lookup]
              using PureData.template_return program bound state _ completed_retained_template
          · have nonempty : first.pending.isEmpty = false := Bool.eq_false_iff.mpr empty
            have stillPending : first.pending ≠ [] := by simpa using empty
            simpa [Effects.boolean, nonempty, stillPending, TopDownMatchDerivatives.completed, List.filterMap_cons,
              tail, bound, applySubst, Subst.lookup] using variable_returns program bound state "tail"

/-- Only goals with no residual obligation become completed locations.
Completing a duplicate does not erase its distinct occurrence. -/
theorem completed_returns (state : State) (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program [] state (a "gslt:automata:completed" [listValue (goals.map goalTerm)]) state
      (listValue ((TopDownMatchDerivatives.completed goals).map locationTerm)) :=
  completed_call [] state goals _ (by simp) (completed_body_returns state goals)

/-- This query composes the retained stream executor and completion filter.
It is source syntax over the existing operations, not a new evaluator. -/
def completedQuery (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) : Atom :=
  a "case" [a "gslt:automata:execute" [listValue (observations.map obligationTerm),
      listValue (goals.map goalTerm), number 0],
    .expression [.expression [a "MFinished" [v "remaining", v "dispatches"],
      a "gslt:automata:completed" [v "remaining"]]]]

theorem completedQuery_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program [] state (completedQuery observations goals) state
      (listValue ((TopDownMatchDerivatives.completed (TopDownMatchDerivatives.execute observations goals)).map
        locationTerm)) := by
  let executed := TopDownMatchDerivatives.executeCounted observations goals
  let bound : Subst := [("dispatches", number executed.2), ("remaining", listValue (executed.1.map goalTerm))]
  let rows : SpaceSemantics.Cases :=
    [(a "MFinished" [v "remaining", v "dispatches"], a "gslt:automata:completed" [v "remaining"])]
  apply case_returns program [] bound state state state _
    (a "MFinished" [listValue (executed.1.map goalTerm), number executed.2])
    (a "gslt:automata:completed" [v "remaining"]) _ _ rows (read_cases_encoded _) _ _ _
  · simpa [executed, finishedTerm, listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      execute_returns state observations goals 0
  · simp [rows, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound]
  · rw [← TopDownMatchDerivatives.executeCounted_result]
    apply completed_call bound state executed.1 _ _ (completed_body_returns state executed.1)
    simp [bound, applySubst, Subst.lookup]

/-- The operational query accepts exactly the independently satisfied
obligation vectors. Missing positions and conflicts cannot become matches;
the original goal order and duplicate occurrences are retained. -/
theorem completedQuery_valid_iff (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term))
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (completedQuery observations goals) }
      (.complete after answers input output) ↔
      after = state ∧
      answers = [listValue ((goals.filterMap fun goal =>
        if TopDownMatchDerivatives.valid (TopDownMatchDerivatives.lookup observations) goal.pending
        then some goal.location else none).map locationTerm)] ∧
      input = [] ∧ output = [] := by
  have exactness := pure_returns_derivation_iff program [] state state _ _
    (completedQuery_returns state observations goals) after answers input output
  simpa only [TopDownMatchDerivatives.completed_execute, TopDownMatchDerivatives.finish_eq_valid] using exactness

#print axioms derive_returns
#print axioms deriveGoals_returns
#print axioms execute_returns
#print axioms execute_completed_iff
#print axioms completed_returns
#print axioms completedQuery_valid_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataDerivativeExecution
