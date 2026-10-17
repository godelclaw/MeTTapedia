import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremSignatureExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.RecursiveMatchExecution
import Mettapedia.Languages.MM0.MeTTa.Kernel.Application

/-!
# Chronological expression allocation in the original binary frontend

Allocation IDs, source variable IDs and saved-heap positions are independent.
The history below is a proposition about the original expression atoms, used
only to track the entries actually constructed by the source.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MM0.MeTTa.MMBAllocationExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue)
open Kernel (Preterm)

abbrev program := MMBExecution.program

def variableEntry (allocation index : Nat) : Atom :=
  expressionValue allocation (Data.preterm (.var index))
    (.expression [.symbol "MM0:MMBVariable", natural index])

def applicationEntry (allocation binary identifier : Nat) (arguments : List Atom)
    (values : List Preterm) : Atom :=
  expressionValue allocation (Data.preterm (Preterm.applyArgs (.term identifier) values))
    (.expression [.symbol "MM0:MMBApplication", natural binary, listValue arguments])

/-- The complete original entry occurs at its allocation position in the
chronological construction history. This is distinct from saved-heap lookup. -/
def AuthorizedExpression (history : List Atom) (entry : Atom) : Prop :=
  ∃ allocation value node,
    entry = expressionValue allocation value node ∧ history[allocation]? = some entry

/-- Recorded proofs and conversions retain authorized expression entries;
this predicate does not validate their proof witnesses. -/
inductive AuthorizedEntry (history : List Atom) : Atom → Prop where
  | expression (entry : Atom) (authorized : AuthorizedExpression history entry) :
      AuthorizedEntry history entry
  | proved (witness target : Atom) (authorized : AuthorizedExpression history target) :
      AuthorizedEntry history (provedValue witness target)
  | conversion (witness left right : Atom)
      (leftAuthorized : AuthorizedExpression history left)
      (rightAuthorized : AuthorizedExpression history right) :
      AuthorizedEntry history (.expression [.symbol "MM0:MMBConversion", witness, left, right])

/-- Every chronological position carries that same allocation ID. -/
def HistoryCoherent (history : List Atom) : Prop :=
  ∀ allocation entry, history[allocation]? = some entry →
    ∃ value node, entry = expressionValue allocation value node

/-- Coherence of the original stack, saved heap and hypothesis list. Saved
witness validation remains an independent kernel obligation. -/
def StateCoherent (history stack heap hypotheses : List Atom) : Prop :=
  HistoryCoherent history ∧
    (∀ entry ∈ stack, AuthorizedEntry history entry) ∧
    (∀ entry ∈ heap, AuthorizedEntry history entry) ∧
    (∀ entry ∈ hypotheses, AuthorizedExpression history entry)

theorem authorized_pointer_unique (history : List Atom) (allocation : Nat)
    (firstValue firstNode secondValue secondNode : Atom)
    (first : AuthorizedExpression history (expressionValue allocation firstValue firstNode))
    (second : AuthorizedExpression history (expressionValue allocation secondValue secondNode)) :
    firstValue = secondValue ∧ firstNode = secondNode := by
  obtain ⟨firstIndex, value, node, shape, found⟩ := first
  obtain ⟨secondIndex, otherValue, otherNode, otherShape, otherFound⟩ := second
  have index : firstIndex = allocation := by
    simp only [expressionValue, Atom.expression.injEq, List.cons.injEq] at shape
    have equal := shape.2.1
    exact (Data.natural_injective equal).symm
  have otherIndex : secondIndex = allocation := by
    simp only [expressionValue, Atom.expression.injEq, List.cons.injEq] at otherShape
    have equal := otherShape.2.1
    exact (Data.natural_injective equal).symm
  subst firstIndex
  subst secondIndex
  have equal := Option.some.inj (found.symm.trans otherFound)
  simp only [expressionValue, Atom.expression.injEq, List.cons.injEq] at equal
  exact ⟨equal.2.2.1, equal.2.2.2.1⟩

theorem AuthorizedExpression.append {history suffix : List Atom} {entry : Atom}
    (authorized : AuthorizedExpression history entry) :
    AuthorizedExpression (history ++ suffix) entry := by
  obtain ⟨allocation, value, node, shape, found⟩ := authorized
  refine ⟨allocation, value, node, shape, ?_⟩
  rw [List.getElem?_append_left]
  · exact found
  · exact (getElem?_eq_some_iff.mp found).choose

theorem AuthorizedEntry.append {history suffix : List Atom} {entry : Atom}
    (authorized : AuthorizedEntry history entry) :
    AuthorizedEntry (history ++ suffix) entry := by
  cases authorized with
  | expression entry proof => exact .expression entry proof.append
  | proved witness target proof => exact .proved witness target proof.append
  | conversion witness left right first second =>
      exact .conversion witness left right first.append second.append

theorem HistoryCoherent.append_fresh (history : List Atom) (value node : Atom)
    (coherent : HistoryCoherent history) :
    HistoryCoherent (history ++ [expressionValue history.length value node]) := by
  intro allocation entry found
  by_cases earlier : allocation < history.length
  · rw [List.getElem?_append_left earlier] at found
    exact coherent allocation entry found
  · have bound := (getElem?_eq_some_iff.mp found).choose
    have atEnd : allocation = history.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst allocation
    rw [List.getElem?_append_right (by omega)] at found
    simp only [Nat.sub_self, List.getElem?_cons_zero] at found
    exact ⟨value, node, (Option.some.inj found).symm⟩

theorem fresh_authorized (history : List Atom) (value node : Atom) :
    AuthorizedExpression (history ++ [expressionValue history.length value node])
      (expressionValue history.length value node) := by
  refine ⟨history.length, value, node, rfl, ?_⟩
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

def variableEntries (index count : Nat) : List Atom :=
  (List.range' index count).map fun index => variableEntry index index

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD
    ⟨"", [], .symbol "None"⟩
private def variablesEquation := sourceEquation "mm0:mmb:proof-variables"
private def variablesMore := match variablesEquation.body with | .expression [_, _, body, _] => body | _ => .symbol "None"
private def variablesEnvironment (index arity count : Nat) (heap : List Atom) : Subst :=
  [("heap", listValue heap), ("hypothesisCount", natural count), ("arity", natural arity), ("index", natural index)]
private theorem variables_unique : program.equations.filter (·.head == "mm0:mmb:proof-variables") = [variablesEquation] := by decide +kernel
private theorem variables_formals : variablesEquation.arguments =
    [.var "index", .var "arity", .var "hypothesisCount", .var "heap"] := by decide
private theorem variables_shape : variablesEquation.body =
    .expression [.symbol "if", .expression [.symbol "<", .var "index", .var "arity"], variablesMore,
      .expression [.symbol "MM0:MMBPState", .var "arity", .var "arity", .var "hypothesisCount",
        .expression [.symbol "MM0:L", .expression []], .var "heap",
        .expression [.symbol "MM0:L", .expression []],
        .expression [.symbol "MM0:L", .expression []],
        .expression [.symbol "MM0:L", .expression []]]] := by decide
private theorem variables_more_shape : variablesMore =
    .expression [.symbol "let*", .expression [
      .expression [.var "variable", .expression [.symbol "mm0:make-var", .var "index"]],
      .expression [.var "entry", .expression [.symbol "MM0:MMBExpression", .var "index", .var "variable",
        .expression [.symbol "MM0:MMBVariable", .var "index"]]],
      .expression [.var "next", .expression [.symbol "mm0:mmb:snoc", .var "heap", .var "entry"]]],
      .expression [.symbol "mm0:mmb:proof-variables", .expression [.symbol "+", .var "index", natural 1],
        .var "arity", .var "hypothesisCount", .var "next"]] := by decide
private theorem variables_clause (index arity count : Nat) (heap : List Atom) :
    clauses program "mm0:mmb:proof-variables" [natural index, natural arity, natural count, listValue heap] =
      [.evaluate (variablesEnvironment index arity count heap) variablesEquation.body] := by
  rw [clauses_use_only_the_named_equations, variables_unique]
  simp [variables_formals, variablesEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem make_var_captured_returns (bindings : Subst) (state : State) (index : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural index) :
    PureReturns program bindings state (.expression [.symbol "mm0:make-var", .var name]) state
      (Data.preterm (.var index)) := by
  have original := MMBProofRunExecution.checker_returns (by
      simp only [codeWithin, atomsWithin, expressionHeadWithin, natural]
      decide +kernel)
    (Data.make_var_returns [] state index)
  apply captured_call_returns program [] bindings state state "mm0:make-var" [natural index] [.var name] _
    (by decide +kernel) (by decide) _ _ _ original
  · intro offset argument found
    have zero : offset = 0 := by have bound := (getElem?_eq_some_iff.mp found).choose; simp only [List.length_singleton] at bound; omega
    subst offset
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst argument
    right
    rfl
  · intro offset argument found
    have zero : offset = 0 := by have bound := (getElem?_eq_some_iff.mp found).choose; simp only [List.length_singleton] at bound; omega
    subst offset
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst argument
    right
    rfl
  · change [applySubst [] (natural index)] = [applySubst bindings (.var name)]
    rw [captured]
    rfl

private theorem increment_returns (bindings : Subst) (state : State) (position : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural position) :
    PureReturns program bindings state (.expression [.symbol "+", .var name, natural 1]) state (natural (position + 1)) := by
  apply native_binary_call_returns program bindings state state state state "+" (.var name) (natural 1)
    (natural position) (natural 1) (natural (position + 1))
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · simpa [captured] using variable_returns program bindings state name
  · exact grounded_returns program bindings state (.int 1)
  · change (.ok (state, [.grounded (.int ((position : Int) + 1))]) : Effects.Result) = .ok (state, [natural (position + 1)])
    simp [natural]

private theorem variables_call_from_body (bindings : Subst) (state : State) (index arity count : Nat) (heap : List Atom)
    (indexArgument : Atom) (arityName countName heapName : String) (answer : Atom)
    (indexReturned : PureReturns program bindings state indexArgument state (natural index))
    (arityCaptured : applySubst bindings (.var arityName) = natural arity)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (heapCaptured : applySubst bindings (.var heapName) = listValue heap)
    (body : PureReturns program (variablesEnvironment index arity count heap) state variablesEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-variables", indexArgument,
      .var arityName, .var countName, .var heapName]) state answer := by
  apply call_returns program bindings state state "mm0:mmb:proof-variables" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:proof-variables")
    indexArgument (natural index) _ _ [] 0 (by decide +kernel) indexReturned
  have returned := authored_function_arguments_return program bindings (variablesEnvironment index arity count heap)
    state state "mm0:mmb:proof-variables" [natural index, natural arity, natural count, listValue heap] 4
    variablesEquation.body answer (by decide +kernel) (by decide) (variables_clause index arity count heap) body
  apply variable_arguments_return program bindings state state (.function "mm0:mmb:proof-variables")
    [arityName, countName, heapName] [natural index] 1 answer
  simpa [arityCaptured, countCaptured, heapCaptured] using returned

private theorem variables_body_returns (state : State) (remaining index arity count : Nat) (heap : List Atom)
    (remainingEq : arity = index + remaining) :
    PureReturns program (variablesEnvironment index arity count heap) state variablesEquation.body state
      (stateValue arity arity count [] (heap ++ variableEntries index remaining) [] [] []) := by
  induction remaining generalizing index heap with
  | zero =>
      let bindings := variablesEnvironment index arity count heap
      have same : arity = index := by omega
      rw [variables_shape]
      apply if_returns program bindings state state state _ (boolean false) _ _ _
      · apply native_variable_call_returns program bindings state state "<" ["index", "arity"]
          (boolean false) (by decide) (by decide) _ (by decide)
        change (.ok (state, [boolean ((index : Int) < (arity : Int))]) : Effects.Result) = .ok (state, [boolean false])
        simp [same, boolean]
      · simp only [boolean]
        apply data_call_returns program bindings state state "MM0:MMBPState" _ _ (by decide +kernel) _ (by decide)
        apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBPState")
          (.symbol "MM0:MMBPState") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBPState")
        apply evaluated_argument_returns program bindings state state state .data (.var "arity") (natural arity)
          _ _ [.symbol "MM0:MMBPState"] 1 rfl (variable_returns program bindings state "arity")
        apply evaluated_argument_returns program bindings state state state .data (.var "arity") (natural arity)
          _ _ _ 2 rfl (variable_returns program bindings state "arity")
        apply evaluated_argument_returns program bindings state state state .data (.var "hypothesisCount") (natural count)
          _ _ _ 3 rfl (variable_returns program bindings state "hypothesisCount")
        apply evaluated_argument_returns program bindings state state state .data (.expression [.symbol "MM0:L", .expression []])
          (listValue []) _ _ _ 4 rfl (empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide))
        apply evaluated_argument_returns program bindings state state state .data (.var "heap") (listValue heap)
          _ _ _ 5 rfl (variable_returns program bindings state "heap")
        apply evaluated_argument_returns program bindings state state state .data (.expression [.symbol "MM0:L", .expression []])
          (listValue []) _ _ _ 6 rfl (empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide))
        apply evaluated_argument_returns program bindings state state state .data (.expression [.symbol "MM0:L", .expression []])
          (listValue []) _ _ _ 7 rfl (empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide))
        apply evaluated_argument_returns program bindings state state state .data (.expression [.symbol "MM0:L", .expression []])
          (listValue []) _ [] _ 8 rfl (empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide))
        simpa [bindings, variablesEnvironment, applySubst, Subst.lookup, stateValue, variableEntries, listValue] using
          data_arguments_values_return program bindings state
            [.symbol "MM0:MMBPState", natural arity, natural arity, natural count,
              listValue [], listValue heap, listValue [], listValue [], listValue []] 9
  | succ remaining ih =>
      let bindings := variablesEnvironment index arity count heap
      let created := ("variable", Data.preterm (.var index)) :: bindings
      let entry := variableEntry index index
      let slotted := ("entry", entry) :: created
      let next := heap ++ [entry]
      let appended := ("next", listValue next) :: slotted
      rw [variables_shape]
      apply if_returns program bindings state state state _ (boolean true) _ _ _
      · apply native_variable_call_returns program bindings state state "<" ["index", "arity"]
          (boolean true) (by decide) (by decide) _ (by decide)
        change (.ok (state, [boolean ((index : Int) < (arity : Int))]) : Effects.Result) = .ok (state, [boolean true])
        have less : (index : Int) < (arity : Int) := by omega
        simp [less, boolean]
      · simp only [boolean]
        rw [variables_more_shape]
        apply let_star_returns program bindings state state _ _ _ _ rfl
        apply let_returns program bindings created state state state (.var "variable") _ _ (Data.preterm (.var index)) _
        · exact make_var_captured_returns bindings state index "index" rfl
        · simp [SpaceSemantics.matchValue, matchAtom, created, bindings, variablesEnvironment, Subst.lookup]
        · apply let_returns program created slotted state state state (.var "entry") _ _ entry _
          · apply data_call_returns program created state state "MM0:MMBExpression" _ _ (by decide +kernel) _ (by decide)
            apply evaluated_argument_returns program created state state state .data (.symbol "MM0:MMBExpression")
              (.symbol "MM0:MMBExpression") _ _ [] 0 rfl (symbol_returns program created state "MM0:MMBExpression")
            apply evaluated_argument_returns program created state state state .data (.var "index") (natural index)
              _ _ [.symbol "MM0:MMBExpression"] 1 rfl (variable_returns program created state "index")
            apply evaluated_argument_returns program created state state state .data (.var "variable") (Data.preterm (.var index))
              _ _ _ 2 rfl (variable_returns program created state "variable")
            apply evaluated_argument_returns program created state state state .data
              (.expression [.symbol "MM0:MMBVariable", .var "index"])
              (.expression [.symbol "MM0:MMBVariable", natural index]) _ [] _ 3 rfl
            · simpa [created, bindings, variablesEnvironment, applySubst, Subst.lookup] using
                unary_constructor_returns program created state "MM0:MMBVariable" "index" (by decide +kernel) (by decide)
            · simpa [entry, variableEntry, expressionValue, created, bindings, variablesEnvironment, applySubst, Subst.lookup] using
                data_arguments_values_return program created state
                  [.symbol "MM0:MMBExpression", natural index, Data.preterm (.var index),
                    .expression [.symbol "MM0:MMBVariable", natural index]] 4
          · simp [SpaceSemantics.matchValue, matchAtom, slotted, created, bindings, variablesEnvironment, Subst.lookup]
          · apply let_returns program slotted appended state state state (.var "next") _ _ (listValue next) _
            · exact MMBProofRunExecution.snoc_returns slotted state heap entry "heap" "entry" rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, appended, slotted, created, bindings, variablesEnvironment, Subst.lookup]
            · have tail := variables_call_from_body appended state (index + 1) arity count next
                (.expression [.symbol "+", .var "index", natural 1]) "arity" "hypothesisCount" "next" _
                (increment_returns appended state index "index" rfl) rfl rfl rfl
                (ih (index + 1) next (by omega))
              simpa [next, entry, variableEntries, List.range'_succ, List.append_assoc] using tail

/-- The actual initializer creates ordered, distinct complete variable entries.
Existing heap entries are retained without being confused with allocation IDs. -/
theorem variables_returns (bindings : Subst) (state : State) (index remaining arity count : Nat)
    (heap : List Atom) (remainingEq : arity = index + remaining)
    (indexName arityName countName heapName : String)
    (indexCaptured : applySubst bindings (.var indexName) = natural index)
    (arityCaptured : applySubst bindings (.var arityName) = natural arity)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (heapCaptured : applySubst bindings (.var heapName) = listValue heap) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-variables",
      .var indexName, .var arityName, .var countName, .var heapName]) state
      (stateValue arity arity count [] (heap ++ variableEntries index remaining) [] [] []) := by
  exact variables_call_from_body bindings state index arity count heap (.var indexName)
    arityName countName heapName _
    (by simpa [indexCaptured] using variable_returns program bindings state indexName)
    arityCaptured countCaptured heapCaptured (variables_body_returns state remaining index arity count heap remainingEq)


private def initialEquation := sourceEquation "mm0:mmb:proof-initial"
private def initialEnvironment (context : List Atom) (count : Nat) : Subst :=
  [("hypothesisCount", natural count), ("context", .expression context)]
private theorem initial_unique : program.equations.filter (·.head == "mm0:mmb:proof-initial") = [initialEquation] := by decide +kernel
private theorem initial_formals : initialEquation.arguments =
    [.expression [.symbol "MM0:L", .var "context"], .var "hypothesisCount"] := by decide
private theorem initial_shape : initialEquation.body =
    .expression [.symbol "mm0:mmb:proof-variables", natural 0,
      .expression [.symbol "size-atom", .var "context"], .var "hypothesisCount",
      .expression [.symbol "MM0:L", .expression []]] := by decide
private theorem initial_clause (context : List Atom) (count : Nat) :
    clauses program "mm0:mmb:proof-initial" [listValue context, natural count] =
      [.evaluate (initialEnvironment context count) initialEquation.body] := by
  rw [clauses_use_only_the_named_equations, initial_unique]
  simp [initial_formals, initialEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem initial_body_returns (state : State) (context : List Atom) (count : Nat) :
    PureReturns program (initialEnvironment context count) state initialEquation.body state
      (stateValue context.length context.length count [] (variableEntries 0 context.length) [] [] []) := by
  let bindings := initialEnvironment context count
  rw [initial_shape]
  apply call_returns program bindings state state "mm0:mmb:proof-variables" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:proof-variables")
    (natural 0) (natural 0) _ _ [] 0 (by decide +kernel) (grounded_returns program bindings state (.int 0))
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:proof-variables")
    (.expression [.symbol "size-atom", .var "context"]) (natural context.length) _ _ _ 1 (by decide +kernel)
  · apply native_variable_call_returns program bindings state state "size-atom" ["context"]
      (natural context.length) (by decide) (by decide) _ (by decide)
    rfl
  · apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:proof-variables")
      (.var "hypothesisCount") (natural count) _ _ _ 2 (by decide +kernel)
      (variable_returns program bindings state "hypothesisCount")
    have returned := authored_function_arguments_return program bindings
      (variablesEnvironment 0 context.length count []) state state "mm0:mmb:proof-variables"
      [natural 0, natural context.length, natural count, listValue []] 4 variablesEquation.body _
      (by decide +kernel) (by decide) (variables_clause 0 context.length count [])
      (variables_body_returns state context.length 0 context.length count [] (by omega))
    apply raw_arguments_return program bindings state state "mm0:mmb:proof-variables"
      [listValue []] [natural 0, natural context.length, natural count] 3 _
      (by
        intro offset selected
        have zero : offset = 0 := by
          simp only [List.length_singleton] at selected
          omega
        subst offset
        decide +kernel)
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      listValue, applySubst, applySubst.applySubstList, List.length_singleton, List.nil_append] using returned

/-- The actual entry point earns the complete original initial proof state. -/
theorem initial_returns (bindings : Subst) (state : State) (context : List Atom) (count : Nat)
    (contextName countName : String)
    (contextCaptured : applySubst bindings (.var contextName) = listValue context)
    (countCaptured : applySubst bindings (.var countName) = natural count) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-initial",
      .var contextName, .var countName]) state
      (stateValue context.length context.length count [] (variableEntries 0 context.length) [] [] []) := by
  apply authored_variable_call_returns program bindings (initialEnvironment context count) state state
    "mm0:mmb:proof-initial" [contextName, countName] initialEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (initial_body_returns state context count) (by decide)
  simpa [contextCaptured, countCaptured] using initial_clause context count

@[simp] theorem variableEntries_length (index count : Nat) : (variableEntries index count).length = count := by
  simp [variableEntries]

theorem HistoryCoherent.append_variables (history : List Atom) (count : Nat)
    (coherent : HistoryCoherent history) :
    HistoryCoherent (history ++ variableEntries history.length count) := by
  induction count generalizing history with
  | zero => simpa [variableEntries] using coherent
  | succ count ih =>
      let entry := variableEntry history.length history.length
      have fresh : HistoryCoherent (history ++ [entry]) :=
        coherent.append_fresh _ _ _
      have tail := ih (history ++ [entry]) fresh
      simpa [variableEntries, entry, List.range'_succ, List.append_assoc] using tail

theorem HistoryCoherent.authorizes {history : List Atom} {entry : Atom}
    (coherent : HistoryCoherent history) (member : entry ∈ history) :
    AuthorizedExpression history entry := by
  obtain ⟨allocation, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨value, node, shape⟩ := coherent allocation entry found
  exact ⟨allocation, value, node, shape, found⟩

/-- Initial physical heap positions and allocation IDs agree before any proof
or unsaved-constructor entry has changed the saved-heap chronology. -/
theorem initial_coherent (arity : Nat) :
    StateCoherent (variableEntries 0 arity) [] (variableEntries 0 arity) [] := by
  have history : HistoryCoherent (variableEntries 0 arity) := by
    simpa using HistoryCoherent.append_variables [] arity (by intro index entry found; simp at found)
  refine ⟨history, ?_, ?_, ?_⟩
  · intro entry impossible; cases impossible
  · intro entry member; exact .expression entry (history.authorizes member)
  · intro entry impossible; cases impossible

/-- A fresh source entry extends allocation history independently of whether
it is appended to the saved heap. Earlier entries retain their full payload. -/
theorem allocate_coherent (history stack heap hypotheses rest : List Atom) (value node : Atom)
    (save : Bool) (coherent : StateCoherent history stack heap hypotheses)
    (retained : ∀ entry ∈ rest, entry ∈ stack) :
    StateCoherent (history ++ [expressionValue history.length value node])
      (expressionValue history.length value node :: rest)
      (if save then heap ++ [expressionValue history.length value node] else heap) hypotheses := by
  obtain ⟨historyGood, stackGood, heapGood, hypothesesGood⟩ := coherent
  refine ⟨historyGood.append_fresh _ _ _, ?_, ?_, ?_⟩
  · intro entry member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact .expression _ (fresh_authorized history value node)
    · exact (stackGood entry (retained entry member)).append
  · intro entry member
    cases save with
    | false => exact (heapGood entry member).append
    | true =>
        simp only [↓reduceIte, List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact (heapGood entry member).append
        · exact .expression _ (fresh_authorized history value node)
  · intro entry member
    exact (hypothesesGood entry member).append

private theorem allocation_result_returns (bindings : Subst) (state : State)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (dummiesName : String)
    (nextCaptured : applySubst bindings (.var "next") = natural next)
    (arityCaptured : applySubst bindings (.var "arity") = natural arity)
    (countCaptured : applySubst bindings (.var "count") = natural count)
    (stackCaptured : applySubst bindings (.var "pushed") = listValue stack)
    (heapCaptured : applySubst bindings (.var "after") = listValue heap)
    (dummiesCaptured : applySubst bindings (.var dummiesName) = listValue dummies)
    (hypothesesCaptured : applySubst bindings (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst bindings (.var "saved") = listValue saved) :
    PureReturns program bindings state (.expression [.symbol "Some", .expression [.symbol "MM0:MMBPState",
      .expression [.symbol "+", .var "next", natural 1], .var "arity", .var "count", .var "pushed",
      .var "after", .var dummiesName, .var "hyps", .var "saved"]]) state
      (optionValue (some (stateValue (next + 1) arity count stack heap dummies hypotheses saved))) := by
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply data_call_returns program bindings state state "MM0:MMBPState" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBPState")
    (.symbol "MM0:MMBPState") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBPState")
  apply evaluated_argument_returns program bindings state state state .data
    (.expression [.symbol "+", .var "next", natural 1]) (natural (next + 1))
    _ _ _ 1 rfl (increment_returns bindings state next "next" nextCaptured)
  apply variable_arguments_return program bindings state state .data
    ["arity", "count", "pushed", "after", dummiesName, "hyps", "saved"]
    [.symbol "MM0:MMBPState", natural (next + 1)] 2 _
  simpa [arityCaptured, countCaptured, stackCaptured, heapCaptured, dummiesCaptured, hypothesesCaptured,
    savedCaptured, optionValue, stateValue] using data_arguments_values_return program bindings state
      [.symbol "MM0:MMBPState", natural (next + 1), natural arity, natural count, listValue stack,
        listValue heap, listValue dummies, listValue hypotheses, listValue saved] 9

private def dummyEquation := sourceEquation "mm0:mmb:proof-dummy"
private def dummyCases : SpaceSemantics.Cases :=
  match dummyEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def dummyFound := (dummyCases[0]'(by decide)).2
private def dummyResult := match dummyFound with | .expression [_, _, body] => body | _ => .symbol "None"
private def dummyEnvironment (resolver : Atom) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (binary : Nat) : Subst :=
  [("binary", natural binary), ("saved", listValue saved), ("hyps", listValue hypotheses),
    ("dummies", .expression dummies), ("heap", listValue heap), ("stack", listValue stack),
    ("count", natural count), ("arity", natural arity), ("next", natural next), ("resolver", resolver)]
private theorem dummy_unique : program.equations.filter (·.head == "mm0:mmb:proof-dummy") = [dummyEquation] := by decide +kernel
private theorem dummy_formals : dummyEquation.arguments =
    [.var "resolver", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
      .var "stack", .var "heap", .expression [.symbol "MM0:L", .var "dummies"], .var "hyps", .var "saved"], .var "binary"] := by decide
private theorem dummy_shape : dummyEquation.body =
    .expression [.symbol "case", .expression [.symbol "mm0:mmu:sort", .var "resolver", .var "binary"],
      .expression (dummyCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem dummy_cases_shape : dummyCases =
    [(.expression [.symbol "Some", .var "sort"], dummyFound), (.var "bad", .symbol "None")] := by decide
private theorem dummy_found_shape : dummyFound =
    .expression [.symbol "let*", .expression [
      .expression [.var "index", .expression [.symbol "+", .var "arity", .expression [.symbol "size-atom", .var "dummies"]]],
      .expression [.var "variable", .expression [.symbol "mm0:make-var", .var "index"]],
      .expression [.var "entry", .expression [.symbol "MM0:MMBExpression", .var "next", .var "variable",
        .expression [.symbol "MM0:MMBVariable", .var "index"]]],
      .expression [.var "pushed", .expression [.symbol "mm0:list-cons", .var "entry", .var "stack"]],
      .expression [.var "after", .expression [.symbol "mm0:mmb:snoc", .var "heap", .var "entry"]],
      .expression [.var "extra", .expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "dummies"], .var "sort"]]], dummyResult] := by decide
private theorem dummy_result_shape : dummyResult =
    .expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .expression [.symbol "+", .var "next", natural 1],
      .var "arity", .var "count", .var "pushed", .var "after", .var "extra", .var "hyps", .var "saved"]] := by decide
private theorem dummy_clause (resolver : Atom) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (binary : Nat) :
    clauses program "mm0:mmb:proof-dummy"
      [resolver, stateValue next arity count stack heap dummies hypotheses saved, natural binary] =
      [.evaluate (dummyEnvironment resolver next arity count stack heap dummies hypotheses saved binary) dummyEquation.body] := by
  rw [clauses_use_only_the_named_equations, dummy_unique]
  simp [dummy_formals, dummyEnvironment, stateValue, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The exact source result for the current sort map, retaining arbitrary
source metadata. Kernel sort admission is a later, independent obligation. -/
def dummyResultValue (sorts : List MMUResolution.Binding) (binary next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) : Atom :=
  optionValue ((MMUResolution.lookup sorts (natural binary)).map fun sort =>
    let entry := variableEntry next (arity + dummies.length)
    stateValue (next + 1) arity count (entry :: stack) (heap ++ [entry])
      (dummies ++ [sort]) hypotheses saved)

private theorem dummy_body_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (binary next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) :
    PureReturns program
      (dummyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        next arity count stack heap dummies hypotheses saved binary)
      state dummyEquation.body state (dummyResultValue sorts binary next arity count stack heap dummies hypotheses saved) := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := dummyEnvironment resolver next arity count stack heap dummies hypotheses saved binary
  have resolved := MMBTheoremSignatureExecution.resolver_returns .sort bindings state published sorts terms theorems
    nextSort nextTerm nextTheorem images (natural binary) "resolver" "binary" rfl rfl
  simp only [MMBTheoremSignatureExecution.ResolverField.head, MMBTheoremSignatureExecution.ResolverField.entries] at resolved
  rw [dummy_shape]
  cases found : MMUResolution.lookup sorts (natural binary) with
  | none =>
      apply case_returns program bindings (("bad", .symbol "None") :: bindings) state state state _
        (.symbol "None") (.symbol "None") _ _ dummyCases (read_cases_encoded dummyCases)
      · simpa [found, optionValue] using resolved
      · simp [dummy_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, Subst.lookup, bindings, dummyEnvironment]
      · simpa [dummyResultValue, found, optionValue] using symbol_returns program _ state "None"
  | some sort =>
      let selected := ("sort", sort) :: bindings
      let index := arity + dummies.length
      let indexed := ("index", natural index) :: selected
      let valued := ("variable", Data.preterm (.var index)) :: indexed
      let entry := variableEntry next index
      let entered := ("entry", entry) :: valued
      let pushed := ("pushed", listValue (entry :: stack)) :: entered
      let stored := ("after", listValue (heap ++ [entry])) :: pushed
      let final := ("extra", listValue (dummies ++ [sort])) :: stored
      apply case_returns program bindings selected state state state _ (optionValue (some sort)) dummyFound _ _
        dummyCases (read_cases_encoded dummyCases)
      · simpa [found] using resolved
      · simp [dummy_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings,
          dummyEnvironment, optionValue]
      · rw [dummy_found_shape]
        apply let_star_returns program selected state state _ _ _ _ rfl
        apply let_returns program selected indexed state state state (.var "index") _ _ (natural index) _
        · apply native_binary_call_returns program selected state state state state "+" (.var "arity")
            (.expression [.symbol "size-atom", .var "dummies"]) (natural arity) (natural dummies.length) (natural index)
            (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
          · exact variable_returns program selected state "arity"
          · apply native_variable_call_returns program selected state state "size-atom" ["dummies"]
              (natural dummies.length) (by decide) (by decide) _ (by decide)
            rfl
          · change (.ok (state, [.grounded (.int ((arity : Int) + dummies.length))]) : Effects.Result) = .ok (state, [natural index])
            simp [natural, index]
        · simp [SpaceSemantics.matchValue, matchAtom, indexed, selected, bindings, dummyEnvironment, Subst.lookup]
        · apply let_returns program indexed valued state state state (.var "variable") _ _ (Data.preterm (.var index)) _
          · exact make_var_captured_returns indexed state index "index" rfl
          · simp [SpaceSemantics.matchValue, matchAtom, valued, indexed, selected, bindings, dummyEnvironment, Subst.lookup]
          · apply let_returns program valued entered state state state (.var "entry") _ _ entry _
            · apply data_call_returns program valued state state "MM0:MMBExpression" _ _ (by decide +kernel) _ (by decide)
              apply evaluated_argument_returns program valued state state state .data (.symbol "MM0:MMBExpression")
                (.symbol "MM0:MMBExpression") _ _ [] 0 rfl (symbol_returns program valued state "MM0:MMBExpression")
              apply evaluated_argument_returns program valued state state state .data (.var "next") (natural next)
                _ _ _ 1 rfl (variable_returns program valued state "next")
              apply evaluated_argument_returns program valued state state state .data (.var "variable") (Data.preterm (.var index))
                _ _ _ 2 rfl (variable_returns program valued state "variable")
              apply evaluated_argument_returns program valued state state state .data (.expression [.symbol "MM0:MMBVariable", .var "index"])
                (.expression [.symbol "MM0:MMBVariable", natural index]) _ [] _ 3 rfl
              · simpa [valued, indexed, selected, bindings, dummyEnvironment, applySubst, Subst.lookup] using
                  unary_constructor_returns program valued state "MM0:MMBVariable" "index" (by decide +kernel) (by decide)
              · simpa [entry, variableEntry, expressionValue, valued, indexed, selected, bindings, dummyEnvironment,
                  applySubst, Subst.lookup] using data_arguments_values_return program valued state
                    [.symbol "MM0:MMBExpression", natural next, Data.preterm (.var index),
                      .expression [.symbol "MM0:MMBVariable", natural index]] 4
            · simp [SpaceSemantics.matchValue, matchAtom, entered, valued, indexed, selected, bindings, dummyEnvironment, Subst.lookup]
            · apply let_returns program entered pushed state state state (.var "pushed") _ _ (listValue (entry :: stack)) _
              · exact MMBProofRunExecution.checker_returns (by decide +kernel)
                  (ListAccess.cons_captured_returns entered state entry stack "entry" "stack" rfl rfl)
              · simp [SpaceSemantics.matchValue, matchAtom, pushed, entered, valued, indexed, selected, bindings, dummyEnvironment, Subst.lookup]
              · apply let_returns program pushed stored state state state (.var "after") _ _ (listValue (heap ++ [entry])) _
                · exact MMBProofRunExecution.snoc_returns pushed state heap entry "heap" "entry" rfl rfl
                · simp [SpaceSemantics.matchValue, matchAtom, stored, pushed, entered, valued, indexed, selected, bindings, dummyEnvironment, Subst.lookup]
                · apply let_returns program stored final state state state (.var "extra") _ _ (listValue (dummies ++ [sort])) _
                  · let prior := ("items", listValue dummies) :: ("value", sort) :: stored
                    have returned := MMBProofRunExecution.snoc_returns prior state dummies sort "items" "value" rfl rfl
                    apply captured_call_returns program prior stored state state "mm0:mmb:snoc"
                      [.var "items", .var "value"] [.expression [.symbol "MM0:L", .var "dummies"], .var "sort"] _
                      (by decide +kernel) (by decide) _ _ _ returned
                    · intro offset argument selected
                      left
                      have bound := (getElem?_eq_some_iff.mp selected).choose
                      have cases : offset = 0 ∨ offset = 1 := by simp only [List.length_cons, List.length_nil] at bound; omega
                      rcases cases with rfl | rfl <;> decide +kernel
                    · intro offset argument selected
                      left
                      have bound := (getElem?_eq_some_iff.mp selected).choose
                      have cases : offset = 0 ∨ offset = 1 := by simp only [List.length_cons, List.length_nil] at bound; omega
                      rcases cases with rfl | rfl <;> decide +kernel
                    · simp [prior, stored, pushed, entered, valued, indexed, selected, bindings, dummyEnvironment,
                        applySubst, applySubst.applySubstList, Subst.lookup, listValue]
                  · simp [SpaceSemantics.matchValue, matchAtom, final, stored, pushed, entered, valued, indexed, selected, bindings, dummyEnvironment, Subst.lookup]
                  · rw [dummy_result_shape]
                    simpa [dummyResultValue, found, entry, index, optionValue] using
                      allocation_result_returns final state next arity count (entry :: stack) (heap ++ [entry])
                        (dummies ++ [sort]) hypotheses saved "extra" rfl rfl rfl rfl rfl rfl rfl rfl

/-- Actual sort lookup, fresh variable construction and all three original
list updates execute together; an unavailable sort returns the source refusal. -/
theorem dummy_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (binary next arity count : Nat) (stack heap dummies hypotheses saved : List Atom)
    (resolverName stateName binaryName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-dummy",
      .var resolverName, .var stateName, .var binaryName]) state
      (dummyResultValue sorts binary next arity count stack heap dummies hypotheses saved) := by
  apply authored_variable_call_returns program bindings
    (dummyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      next arity count stack heap dummies hypotheses saved binary) state state
    "mm0:mmb:proof-dummy" [resolverName, stateName, binaryName] dummyEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (dummy_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images binary next arity count
      stack heap dummies hypotheses saved) (by decide)
  simpa [resolverCaptured, stateCaptured, binaryCaptured] using dummy_clause
    (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    next arity count stack heap dummies hypotheses saved binary

/-- A successful original dummy allocation extends the pointer history, while
its variable index follows original arity and dummy chronology. -/
theorem dummy_coherent (history stack heap dummies hypotheses : List Atom) (arity : Nat)
    (coherent : StateCoherent history stack heap hypotheses) :
    let entry := variableEntry history.length (arity + dummies.length)
    StateCoherent (history ++ [entry]) (entry :: stack) (heap ++ [entry]) hypotheses := by
  exact allocate_coherent history stack heap hypotheses stack _ _ true coherent (by intro entry member; exact member)


private def termEquation := sourceEquation "mm0:mmb:proof-term"
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def termCase := match termEquation.body with | .expression [_, _, body] => body | _ => .symbol "None"
private def termCases := casesOf termCase
private def termFound := (termCases[0]'(by decide)).2
private def termPopCases := casesOf termFound
private def termPopped := (termPopCases[0]'(by decide)).2
private def termValueCases := casesOf termPopped
private def termValues := (termValueCases[0]'(by decide)).2
private def termResult := match termValues with | .expression [_, _, body] => body | _ => .symbol "None"
private def termEnvironment (resolver tableSorts tableTheorems : Atom) (tableTerms : List Atom)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (binary : Nat) (save : Bool) : Subst :=
  [("save", boolean save), ("binary", natural binary), ("saved", listValue saved), ("hyps", listValue hypotheses),
    ("dummies", listValue dummies), ("heap", listValue heap), ("stack", listValue stack),
    ("count", natural count), ("arity", natural arity), ("next", natural next),
    ("theorems", tableTheorems), ("terms", listValue tableTerms), ("sorts", tableSorts), ("resolver", resolver)]
private theorem term_unique : program.equations.filter (·.head == "mm0:mmb:proof-term") = [termEquation] := by decide +kernel
private theorem term_formals : termEquation.arguments =
    [.var "resolver", .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
      .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count", .var "stack", .var "heap",
        .var "dummies", .var "hyps", .var "saved"], .var "binary", .var "save"] := by decide
private theorem term_shape : termEquation.body =
    .expression [.symbol "let*", .expression [
      .expression [.var "found", .expression [.symbol "mm0:mmu:term", .var "resolver", .var "binary"]],
      .expression [.var "entry", .expression [.symbol "mm0:data-at", .var "terms", .var "binary"]]], termCase] := by decide
private theorem term_case_shape : termCase =
    .expression [.symbol "case", .expression [.var "found", .var "entry"],
      .expression (termCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_cases_shape : termCases =
    [(.expression [.expression [.symbol "Some", .var "id"],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBTerm", .var "sort",
        .expression [.symbol "MM0:L", .var "args"], .var "ret", .var "value"]]], termFound),
      (.var "bad", .symbol "None")] := by decide
private theorem term_found_shape : termFound =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:pop-many", .symbol "MM0:MMBExpressions",
      .expression [.symbol "size-atom", .var "args"], .var "stack"],
      .expression (termPopCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_pop_cases_shape : termPopCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBPopped", .var "arguments", .var "rest"]],
      termPopped), (.var "bad", .symbol "None")] := by decide
private theorem term_popped_shape : termPopped =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:expression-values", .var "arguments"],
      .expression (termValueCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_value_cases_shape : termValueCases =
    [(.expression [.symbol "Some", .var "values"], termValues), (.var "bad", .symbol "None")] := by decide
private theorem term_values_shape : termValues =
    .expression [.symbol "let*", .expression [
      .expression [.var "term", .expression [.symbol "mm0:make-term", .var "id"]],
      .expression [.var "expression", .expression [.symbol "mm0:apply-args", .var "term", .var "values"]],
      .expression [.var "result", .expression [.symbol "MM0:MMBExpression", .var "next", .var "expression",
        .expression [.symbol "MM0:MMBApplication", .var "binary", .var "arguments"]]],
      .expression [.var "pushed", .expression [.symbol "mm0:list-cons", .var "result", .var "rest"]],
      .expression [.var "after", .expression [.symbol "if", .var "save",
        .expression [.symbol "mm0:mmb:snoc", .var "heap", .var "result"], .var "heap"]]], termResult] := by decide
private theorem term_result_shape : termResult =
    .expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .expression [.symbol "+", .var "next", natural 1],
      .var "arity", .var "count", .var "pushed", .var "after", .var "dummies", .var "hyps", .var "saved"]] := by decide
private theorem term_clause (resolver tableSorts tableTheorems : Atom) (tableTerms : List Atom)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (binary : Nat) (save : Bool) :
    clauses program "mm0:mmb:proof-term"
      [resolver, .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems],
        stateValue next arity count stack heap dummies hypotheses saved, natural binary, boolean save] =
      [.evaluate (termEnvironment resolver tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
        termEquation.body] := by
  rw [clauses_use_only_the_named_equations, term_unique]
  simp [term_formals, termEnvironment, stateValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem make_term_captured_returns (bindings : Subst) (state : State) (index : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural index) :
    PureReturns program bindings state (.expression [.symbol "mm0:make-term", .var name]) state
      (Data.preterm (.term index)) := by
  have original := MMBProofRunExecution.checker_returns (by
      simp only [codeWithin, atomsWithin, expressionHeadWithin, natural]
      decide +kernel) (Data.make_term_returns [] state index)
  apply captured_call_returns program [] bindings state state "mm0:make-term" [natural index] [.var name] _
    (by decide +kernel) (by decide) _ _ _ original
  · intro offset argument found
    have zero : offset = 0 := by have bound := (getElem?_eq_some_iff.mp found).choose; simp only [List.length_singleton] at bound; omega
    subst offset
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst argument
    right
    rfl
  · intro offset argument found
    have zero : offset = 0 := by have bound := (getElem?_eq_some_iff.mp found).choose; simp only [List.length_singleton] at bound; omega
    subst offset
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst argument
    right
    rfl
  · change [applySubst [] (natural index)] = [applySubst bindings (.var name)]
    rw [captured]
    rfl

private theorem computed_pop_returns (bindings : Subst) (state : State) (formalArguments stack arguments rest : List Atom)
    (argsCaptured : applySubst bindings (.var "args") = .expression formalArguments)
    (stackCaptured : applySubst bindings (.var "stack") = listValue stack)
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest))) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:pop-many", .symbol "MM0:MMBExpressions",
      .expression [.symbol "size-atom", .var "args"], .var "stack"]) state
      (MMBTheoremCommandExecution.poppedValue (some (arguments, rest))) := by
  let prior : Subst := [("kind", .symbol "MM0:MMBExpressions"), ("number", natural formalArguments.length), ("items", listValue stack)]
  have original := MMBTheoremCommandExecution.pop_many_returns prior state .expressions formalArguments.length stack
    (some (arguments, rest)) "kind" "number" "items" rfl rfl rfl popped
  have finished := captured_function_arguments_returns program prior bindings state state "mm0:mmb:pop-many"
    [.var "kind", .var "number", .var "items"] 3 _ (by decide +kernel) (by decide)
    (by intro offset argument selected; have bound := (getElem?_eq_some_iff.mp selected).choose
        have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 := by simp only [List.length_cons, List.length_nil] at bound; omega
        rcases positions with rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) original
  apply call_returns program bindings state state "mm0:mmb:pop-many" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:pop-many" (.symbol "MM0:MMBExpressions")
    [.expression [.symbol "size-atom", .var "args"], .var "stack"] [] 0 [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:pop-many")
    (.expression [.symbol "size-atom", .var "args"]) (natural formalArguments.length) _ _ _ 1 (by decide +kernel)
  · apply native_variable_call_returns program bindings state state "size-atom" ["args"]
      (natural formalArguments.length) (by decide) (by decide) _ (by decide)
    change StdLib.apply state "size-atom" [applySubst bindings (.var "args")] = .ok (state, [natural formalArguments.length])
    rw [argsCaptured]
    rfl
  · apply variable_arguments_return program bindings state state (.function "mm0:mmb:pop-many")
      ["stack"] [.symbol "MM0:MMBExpressions", natural formalArguments.length] 2 _
    change (theory program).MultiStep
      { state, control := .arguments bindings (.function "mm0:mmb:pop-many") [] [.symbol "MM0:MMBExpressions", natural formalArguments.length, applySubst bindings (.var "stack")] 3 }
      (Eval.finished state [MMBTheoremCommandExecution.poppedValue (some (arguments, rest))] [] [])
    rw [stackCaptured]
    simpa [prior, applySubst, Subst.lookup] using finished

private theorem term_body_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images tableSorts tableTheorems : Atom)
    (tableTerms formalArguments : List Atom) (sort ret value : Atom)
    (binary identifier next arity count : Nat) (stack heap dummies hypotheses saved arguments rest : List Atom)
    (values : List Preterm) (save : Bool)
    (resolved : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest)))
    (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)) :
    PureReturns program
      (termEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
      state termEquation.body state
      (optionValue (some (stateValue (next + 1) arity count
        (applicationEntry next binary identifier arguments values :: rest)
        (if save then heap ++ [applicationEntry next binary identifier arguments values] else heap)
        dummies hypotheses saved))) := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := termEnvironment resolver tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save
  let found := ("found", optionValue (some (natural identifier))) :: bindings
  let declaration : Atom := .expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]
  let entered := ("entry", optionValue (some declaration)) :: found
  let selected := ("value", value) :: ("ret", ret) :: ("args", .expression formalArguments) :: ("sort", sort) :: ("id", natural identifier) :: entered
  let consumed := ("rest", listValue rest) :: ("arguments", listValue arguments) :: selected
  let valued := ("values", listValue (values.map Data.preterm)) :: consumed
  let termed := ("term", Data.preterm (.term identifier)) :: valued
  let expression := Preterm.applyArgs (.term identifier) values
  let applied := ("expression", Data.preterm expression) :: termed
  let result := applicationEntry next binary identifier arguments values
  let produced := ("result", result) :: applied
  let pushed := ("pushed", listValue (result :: rest)) :: produced
  let stored := ("after", listValue (if save then heap ++ [result] else heap)) :: pushed
  rw [term_shape]
  apply let_star_returns program bindings state state _ _ _ _ rfl
  apply let_returns program bindings found state state state (.var "found") _ _ (optionValue (some (natural identifier))) _
  · simpa only [MMBTheoremSignatureExecution.ResolverField.head, MMBTheoremSignatureExecution.ResolverField.entries, resolved] using
      MMBTheoremSignatureExecution.resolver_returns .term bindings state published sorts terms theorems
        nextSort nextTerm nextTheorem images (natural binary) "resolver" "binary" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, found, bindings, termEnvironment, Subst.lookup]
  · apply let_returns program found entered state state state (.var "entry") _ _ (optionValue (some declaration)) _
    · simpa only [declared] using MMBProofRunExecution.checker_returns (by decide +kernel)
        (ListAccess.data_at_list_returns found state tableTerms binary "terms" "binary" rfl rfl)
    · simp [SpaceSemantics.matchValue, matchAtom, entered, found, bindings, termEnvironment, Subst.lookup]
    · rw [term_case_shape]
      apply case_returns program entered selected state state state (.expression [.var "found", .var "entry"])
        (.expression [optionValue (some (natural identifier)), optionValue (some declaration)]) termFound _ _
        termCases (read_cases_encoded termCases)
      · simpa [entered, found, bindings, termEnvironment, applySubst, Subst.lookup] using
          tuple_variables_return program entered state ["found", "entry"]
      · simp [term_cases_shape, declaration, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, entered, found,
          bindings, termEnvironment, optionValue, listValue]
      · rw [term_found_shape]
        apply case_returns program selected consumed state state state _
          (MMBTheoremCommandExecution.poppedValue (some (arguments, rest))) termPopped _ _
          termPopCases (read_cases_encoded termPopCases)
        · exact computed_pop_returns selected state formalArguments stack arguments rest rfl rfl popped
        · simp [term_pop_cases_shape, MMBTheoremCommandExecution.poppedValue, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
            consumed, selected, entered, found, bindings, termEnvironment, optionValue]
        · rw [term_popped_shape]
          apply case_returns program consumed valued state state state _
            (optionValue (some (listValue (values.map Data.preterm)))) termValues _ _
            termValueCases (read_cases_encoded termValueCases)
          · exact MMBProofRunExecution.expression_values_returns consumed state arguments (values.map Data.preterm)
              (.var "arguments") rfl projected
          · simp [term_value_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, valued, consumed, selected, entered, found, bindings, termEnvironment, optionValue]
          · rw [term_values_shape]
            apply let_star_returns program valued state state _ _ _ _ rfl
            apply let_returns program valued termed state state state (.var "term") _ _ (Data.preterm (.term identifier)) _
            · exact make_term_captured_returns valued state identifier "id" rfl
            · simp [SpaceSemantics.matchValue, matchAtom, termed, valued, consumed, selected, entered, found, bindings, termEnvironment, Subst.lookup]
            · apply let_returns program termed applied state state state (.var "expression") _ _ (Data.preterm expression) _
              · exact MMBProofRunExecution.checker_returns (by decide +kernel)
                  (Application.captured_returns termed state (.term identifier) values "term" "values" rfl rfl)
              · simp [SpaceSemantics.matchValue, matchAtom, applied, termed, valued, consumed, selected, entered, found, bindings, termEnvironment, Subst.lookup]
              · apply let_returns program applied produced state state state (.var "result") _ _ result _
                · apply data_call_returns program applied state state "MM0:MMBExpression" _ _ (by decide +kernel) _ (by decide)
                  apply evaluated_argument_returns program applied state state state .data (.symbol "MM0:MMBExpression")
                    (.symbol "MM0:MMBExpression") _ _ [] 0 rfl (symbol_returns program applied state "MM0:MMBExpression")
                  apply evaluated_argument_returns program applied state state state .data (.var "next") (natural next)
                    _ _ _ 1 rfl (variable_returns program applied state "next")
                  apply evaluated_argument_returns program applied state state state .data (.var "expression") (Data.preterm expression)
                    _ _ _ 2 rfl (variable_returns program applied state "expression")
                  apply evaluated_argument_returns program applied state state state .data
                    (.expression [.symbol "MM0:MMBApplication", .var "binary", .var "arguments"])
                    (.expression [.symbol "MM0:MMBApplication", natural binary, listValue arguments]) _ [] _ 3 rfl
                  · simpa [applied, termed, valued, consumed, selected, entered, found, bindings, termEnvironment,
                      applySubst, Subst.lookup] using constructor_variables_return program applied state "MM0:MMBApplication"
                        ["binary", "arguments"] (by decide +kernel) (by decide)
                  · simpa [result, applicationEntry, expressionValue, expression, applied, termed, valued, consumed,
                      selected, entered, found, bindings, termEnvironment, applySubst, Subst.lookup] using
                      data_arguments_values_return program applied state
                        [.symbol "MM0:MMBExpression", natural next, Data.preterm expression,
                          .expression [.symbol "MM0:MMBApplication", natural binary, listValue arguments]] 4
                · simp [SpaceSemantics.matchValue, matchAtom, produced, applied, termed, valued, consumed, selected, entered, found, bindings, termEnvironment, Subst.lookup]
                · apply let_returns program produced pushed state state state (.var "pushed") _ _ (listValue (result :: rest)) _
                  · exact MMBProofRunExecution.checker_returns (by decide +kernel)
                      (ListAccess.cons_captured_returns produced state result rest "result" "rest" rfl rfl)
                  · simp [SpaceSemantics.matchValue, matchAtom, pushed, produced, applied, termed, valued, consumed, selected, entered, found, bindings, termEnvironment, Subst.lookup]
                  · apply let_returns program pushed stored state state state (.var "after") _ _
                      (listValue (if save then heap ++ [result] else heap)) _
                    · apply if_returns program pushed state state state (.var "save") (boolean save) _ _ _
                      · exact variable_returns program pushed state "save"
                      · cases save with
                        | false => exact variable_returns program pushed state "heap"
                        | true => exact MMBProofRunExecution.snoc_returns pushed state heap result "heap" "result" rfl rfl
                    · simp [SpaceSemantics.matchValue, matchAtom, stored, pushed, produced, applied, termed, valued, consumed, selected, entered, found, bindings, termEnvironment, Subst.lookup]
                    · rw [term_result_shape]
                      exact allocation_result_returns stored state next arity count (result :: rest)
                        (if save then heap ++ [result] else heap) dummies hypotheses saved "dummies"
                        rfl rfl rfl rfl rfl rfl rfl rfl

/-- Actual constructor allocation joins current resolver/table lookup,
ordered argument consumption, original preterm application and optional save.
The source binary constructor index and resolved logical identifier remain distinct. -/
theorem term_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images tableSorts tableTheorems : Atom)
    (tableTerms formalArguments : List Atom) (sort ret value : Atom)
    (binary identifier next arity count : Nat) (stack heap dummies hypotheses saved arguments rest : List Atom)
    (values : List Preterm) (save : Bool)
    (resolverName tablesName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save)
    (resolved : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest)))
    (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-term",
      .var resolverName, .var tablesName, .var stateName, .var binaryName, .var saveName]) state
      (optionValue (some (stateValue (next + 1) arity count
        (applicationEntry next binary identifier arguments values :: rest)
        (if save then heap ++ [applicationEntry next binary identifier arguments values] else heap)
        dummies hypotheses saved))) := by
  apply authored_variable_call_returns program bindings
    (termEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save) state state
    "mm0:mmb:proof-term" [resolverName, tablesName, stateName, binaryName, saveName] termEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (term_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
      tableTerms formalArguments sort ret value binary identifier next arity count stack heap dummies hypotheses saved arguments rest values save
      resolved declared popped projected) (by decide)
  simpa [resolverCaptured, tablesCaptured, stateCaptured, binaryCaptured, saveCaptured] using term_clause
    (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save

theorem term_coherent (history stack heap hypotheses arguments rest : List Atom)
    (binary identifier count : Nat) (values : List Preterm) (save : Bool)
    (coherent : StateCoherent history stack heap hypotheses)
    (popped : MMBTheoremCommandExecution.Pops .expressions count stack (some (arguments, rest))) :
    let entry := applicationEntry history.length binary identifier arguments values
    StateCoherent (history ++ [entry]) (entry :: rest)
      (if save then heap ++ [entry] else heap) hypotheses := by
  apply allocate_coherent history stack heap hypotheses rest _ _ save coherent
  intro entry member
  rw [popped.ordered.2]
  exact List.mem_append_right _ member


/-- A construction genealogy over the original atoms, retaining the actual
ordered source children and their original preterm projections. -/
inductive ConstructedHistory : List Atom → Prop where
  | empty : ConstructedHistory []
  | variableNode {history : List Atom} (built : ConstructedHistory history) (index : Nat) :
      ConstructedHistory (history ++ [variableEntry history.length index])
  | application {history : List Atom} (built : ConstructedHistory history) (binary identifier : Nat)
      (arguments : List Atom) (values : List Preterm)
      (authorized : ∀ argument ∈ arguments, AuthorizedExpression history argument)
      (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)) :
      ConstructedHistory (history ++ [applicationEntry history.length binary identifier arguments values])

theorem ConstructedHistory.coherent {history : List Atom} (built : ConstructedHistory history) :
    HistoryCoherent history := by
  induction built with
  | empty => intro index entry impossible; simp at impossible
  | variableNode _ _ ih => exact ih.append_fresh _ _ _
  | application _ _ _ _ _ _ _ ih => exact ih.append_fresh _ _ _

theorem ConstructedHistory.variables (index count : Nat) :
    ConstructedHistory (variableEntries 0 index) →
    ConstructedHistory (variableEntries 0 (index + count)) := by
  intro built
  induction count generalizing index with
  | zero => simpa using built
  | succ count ih =>
      have initial : ConstructedHistory (variableEntries 0 (index + 1)) := by
        have appended := ConstructedHistory.variableNode built index
        simpa [variableEntries, List.range'_concat] using appended
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (index + 1) initial

theorem ConstructedHistory.initial (arity : Nat) : ConstructedHistory (variableEntries 0 arity) := by
  have initialEmpty : ConstructedHistory (variableEntries 0 0) := by simpa [variableEntries] using ConstructedHistory.empty
  simpa using ConstructedHistory.variables 0 arity initialEmpty

theorem AuthorizedExpression.allocated {history : List Atom} {allocation : Nat} {value node : Atom}
    (authorized : AuthorizedExpression history (expressionValue allocation value node)) :
    allocation < history.length := by
  obtain ⟨index, originalValue, originalNode, shape, found⟩ := authorized
  have same : index = allocation := by
    simp only [expressionValue, Atom.expression.injEq, List.cons.injEq] at shape
    exact (Data.natural_injective shape.2.1).symm
  subst index
  exact (getElem?_eq_some_iff.mp found).choose

theorem future_pointer_unauthorized (history : List Atom) (allocation : Nat) (value node : Atom)
    (future : history.length ≤ allocation) :
    ¬ AuthorizedExpression history (expressionValue allocation value node) := by
  intro authorized
  have before := authorized.allocated
  omega

theorem StateCoherent.reference {history stack heap hypotheses : List Atom} {entry : Atom}
    (coherent : StateCoherent history stack heap hypotheses) (member : entry ∈ heap) :
    StateCoherent history (entry :: stack) heap hypotheses := by
  refine ⟨coherent.1, ?_, coherent.2.2.1, coherent.2.2.2⟩
  intro value found
  simp only [List.mem_cons] at found
  rcases found with rfl | found
  · exact coherent.2.2.1 _ member
  · exact coherent.2.1 value found

theorem StateCoherent.save {history rest heap hypotheses : List Atom} {entry : Atom}
    (coherent : StateCoherent history (entry :: rest) heap hypotheses) :
    StateCoherent history (entry :: rest) (heap ++ [entry]) hypotheses := by
  have authorized : AuthorizedEntry history entry := coherent.2.1 entry (by simp)
  refine ⟨coherent.1, coherent.2.1, ?_, coherent.2.2.2⟩
  intro value found
  simp only [List.mem_append, List.mem_singleton] at found
  rcases found with found | rfl
  · exact coherent.2.2.1 value found
  · exact authorized

theorem AuthorizedEntry.expression_authorized {history : List Atom} {allocation : Nat} {value node : Atom}
    (authorized : AuthorizedEntry history (expressionValue allocation value node)) :
    AuthorizedExpression history (expressionValue allocation value node) := by
  generalize equal : expressionValue allocation value node = target at authorized
  cases authorized with
  | expression entry proof => exact proof
  | proved witness target proof => simp [expressionValue, provedValue] at equal
  | conversion witness left right first second => simp [expressionValue] at equal

theorem StateCoherent.hypothesis {history rest heap hypotheses : List Atom}
    {allocation : Nat} {value node witness : Atom}
    (coherent : StateCoherent history (expressionValue allocation value node :: rest) heap hypotheses) :
    let target := expressionValue allocation value node
    StateCoherent history rest (heap ++ [provedValue witness target]) (hypotheses ++ [target]) := by
  have target : AuthorizedExpression history (expressionValue allocation value node) :=
    AuthorizedEntry.expression_authorized (coherent.2.1 (expressionValue allocation value node) (by simp))
  refine ⟨coherent.1, ?_, ?_, ?_⟩
  · intro entry member; exact coherent.2.1 entry (by simp [member])
  · intro entry member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact coherent.2.2.1 entry member
    · exact .proved witness _ target
  · intro entry member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact coherent.2.2.2 entry member
    · exact target

/-- Original reference execution and complete entry authorization are joined;
repeated physical heap copies retain the same original pointer and payload. -/
theorem reference_authorized_returns (bindings : Subst) (state : State) (next arity count : Nat)
    (history stack heap dummies hypotheses saved : List Atom) (index : Nat) (entry : Atom)
    (stateName indexName : String)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity count stack heap dummies hypotheses saved)
    (indexCaptured : applySubst bindings (.var indexName) = natural index)
    (found : heap[index]? = some entry) (reusable : MMBProofRunExecution.ReusableEntry entry)
    (coherent : StateCoherent history stack heap hypotheses) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-reference", .var stateName, .var indexName]) state
      (optionValue (some (stateValue next arity count (entry :: stack) heap dummies hypotheses saved))) ∧
    StateCoherent history (entry :: stack) heap hypotheses := by
  exact ⟨MMBProofRunExecution.reference_returns bindings state next arity count stack heap dummies hypotheses saved index entry
    stateName indexName stateCaptured indexCaptured found reusable,
    coherent.reference (List.mem_of_getElem? found)⟩

/-- Every projected source argument retains its complete authorized entry. -/
theorem ExpressionClaims.authorized {history stack heap hypotheses arguments claims rest : List Atom} {count : Nat}
    (projected : MMBProofRunExecution.ExpressionClaims arguments claims)
    (coherent : StateCoherent history stack heap hypotheses)
    (popped : MMBTheoremCommandExecution.Pops .expressions count stack (some (arguments, rest))) :
    ∀ argument ∈ arguments, AuthorizedExpression history argument := by
  have members : ∀ argument ∈ arguments, AuthorizedEntry history argument := by
    intro argument member
    apply coherent.2.1 argument
    rw [popped.ordered.2]
    exact List.mem_append_left rest (List.mem_reverse.mpr member)
  clear popped coherent
  induction projected with
  | nil => intro argument impossible; cases impossible
  | cons allocation value node _ ih =>
      intro argument member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (members _ (by simp)).expression_authorized
      · apply ih (fun child childMember => members child (by simp [childMember])) argument member

/-- The chronological genealogy is extended by exactly the children and
preterms consumed by the original constructor, without losing duplicates. -/
theorem ConstructedHistory.term {history stack heap hypotheses arguments rest : List Atom}
    {count : Nat} (built : ConstructedHistory history) (binary identifier : Nat) (values : List Preterm)
    (coherent : StateCoherent history stack heap hypotheses)
    (popped : MMBTheoremCommandExecution.Pops .expressions count stack (some (arguments, rest)))
    (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)) :
    ConstructedHistory (history ++ [applicationEntry history.length binary identifier arguments values]) := by
  exact .application built binary identifier arguments values
    (ExpressionClaims.authorized projected coherent popped) projected


/-- Every authorized entry comes from an original variable/application
constructor and has the existing kernel preterm as its value field. -/
theorem ConstructedHistory.preterms {history : List Atom} (built : ConstructedHistory history) :
    ∀ entry ∈ history, ∃ allocation expression node,
      entry = expressionValue allocation (Data.preterm expression) node := by
  induction built with
  | empty => intro entry impossible; cases impossible
  | @variableNode history built index ih =>
      intro entry member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih entry member
      · exact ⟨history.length, .var index, _, rfl⟩
  | @application history built binary identifier arguments values authorized projected ih =>
      intro entry member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih entry member
      · exact ⟨history.length, Preterm.applyArgs (.term identifier) values, _, rfl⟩

/-- The original recursive assertion matcher receives its entry-shape
refinement from chronological construction, including all shared children. -/
theorem ConstructedHistory.shapes {history : List Atom} (built : ConstructedHistory history) :
    ∀ entry ∈ history, MMBRecursiveMatchExecution.ExpressionEntry entry := by
  induction built with
  | empty => intro entry impossible; cases impossible
  | @variableNode history built index ih =>
      intro entry member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih entry member
      · exact .entry history.length (Data.preterm (.var index)) _ (.variableNode index)
  | @application history built binary identifier arguments values authorized projected ih =>
      intro entry member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih entry member
      · apply MMBRecursiveMatchExecution.ExpressionEntry.entry history.length _ _
        apply MMBRecursiveMatchExecution.ExpressionNode.application binary arguments
        intro child member
        obtain ⟨allocation, value, node, shape, found⟩ := authorized child member
        exact ih child (List.mem_of_getElem? found)

theorem AuthorizedExpression.shape {history : List Atom} {entry : Atom}
    (authorized : AuthorizedExpression history entry) (built : ConstructedHistory history) :
    MMBRecursiveMatchExecution.ExpressionEntry entry := by
  obtain ⟨allocation, value, node, shape, found⟩ := authorized
  exact built.shapes entry (List.mem_of_getElem? found)

theorem AuthorizedExpression.preterm {history : List Atom} {allocation : Nat} {value node : Atom}
    (authorized : AuthorizedExpression history (expressionValue allocation value node))
    (built : ConstructedHistory history) : ∃ expression, value = Data.preterm expression := by
  obtain ⟨pointer, originalValue, originalNode, shape, found⟩ := authorized
  obtain ⟨index, expression, constructionNode, constructed⟩ := built.preterms _ (List.mem_of_getElem? found)
  simp only [expressionValue, Atom.expression.injEq, List.cons.injEq] at constructed
  exact ⟨expression, constructed.2.2.1⟩

/-- A forged value under an existing allocation ID cannot be authorized by
this history. The original matcher may compare IDs only; this law earns the
missing complete-entry authority before that comparison is used logically. -/
theorem changed_payload_unauthorized (history : List Atom) (allocation : Nat)
    (value node changedValue changedNode : Atom)
    (authorized : AuthorizedExpression history (expressionValue allocation value node))
    (different : value ≠ changedValue ∨ node ≠ changedNode) :
    ¬ AuthorizedExpression history (expressionValue allocation changedValue changedNode) := by
  intro forged
  obtain ⟨sameValue, sameNode⟩ := authorized_pointer_unique history allocation value node changedValue changedNode authorized forged
  rcases different with different | different
  · exact different sameValue
  · exact different sameNode

/-- A completed original initialization earns its allocation genealogy and
complete stack/heap authority; arbitrary context contents are not evaluated. -/
theorem initial_authorized_returns (bindings : Subst) (state : State) (context : List Atom) (count : Nat)
    (contextName countName : String)
    (contextCaptured : applySubst bindings (.var contextName) = listValue context)
    (countCaptured : applySubst bindings (.var countName) = natural count) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-initial",
      .var contextName, .var countName]) state
      (stateValue context.length context.length count [] (variableEntries 0 context.length) [] [] []) ∧
    ConstructedHistory (variableEntries 0 context.length) ∧
    StateCoherent (variableEntries 0 context.length) [] (variableEntries 0 context.length) [] := by
  exact ⟨initial_returns bindings state context count contextName countName contextCaptured countCaptured,
    ConstructedHistory.initial _, initial_coherent _⟩


/-- The current sort map authorizes source dummy allocation, and the source
transition earns fresh complete-entry coherence and construction genealogy.
It does not assert kernel validity of the resolver's sort metadata. -/
theorem dummy_authorized_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (binary arity count : Nat) (history stack heap dummies hypotheses saved : List Atom) (sort : Atom)
    (resolverName stateName binaryName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue history.length arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (resolved : MMUResolution.lookup sorts (natural binary) = some sort)
    (built : ConstructedHistory history) (coherent : StateCoherent history stack heap hypotheses) :
    let entry := variableEntry history.length (arity + dummies.length)
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-dummy",
      .var resolverName, .var stateName, .var binaryName]) state
      (optionValue (some (stateValue (history.length + 1) arity count (entry :: stack) (heap ++ [entry])
        (dummies ++ [sort]) hypotheses saved))) ∧
    ConstructedHistory (history ++ [entry]) ∧
    StateCoherent (history ++ [entry]) (entry :: stack) (heap ++ [entry]) hypotheses := by
  refine ⟨?_, .variableNode built _, dummy_coherent history stack heap dummies hypotheses arity coherent⟩
  simpa [dummyResultValue, resolved, optionValue] using
    dummy_returns bindings state published sorts terms theorems nextSort nextTerm nextTheorem images binary history.length arity count
      stack heap dummies hypotheses saved resolverName stateName binaryName resolverCaptured stateCaptured binaryCaptured

/-- The complete original constructor transition earns a fresh chronological
entry from the original consumed, authorized arguments. The physical heap
may retain the new entry or omit it according to the source save flag. -/
theorem term_authorized_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images tableSorts tableTheorems : Atom)
    (tableTerms formalArguments : List Atom) (sort ret value : Atom)
    (binary identifier arity count : Nat) (history stack heap dummies hypotheses saved arguments rest : List Atom)
    (values : List Preterm) (save : Bool)
    (resolverName tablesName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (stateCaptured : applySubst bindings (.var stateName) = stateValue history.length arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save)
    (resolved : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest)))
    (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm))
    (built : ConstructedHistory history) (coherent : StateCoherent history stack heap hypotheses) :
    let entry := applicationEntry history.length binary identifier arguments values
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-term",
      .var resolverName, .var tablesName, .var stateName, .var binaryName, .var saveName]) state
      (optionValue (some (stateValue (history.length + 1) arity count (entry :: rest)
        (if save then heap ++ [entry] else heap) dummies hypotheses saved))) ∧
    ConstructedHistory (history ++ [entry]) ∧
    StateCoherent (history ++ [entry]) (entry :: rest)
      (if save then heap ++ [entry] else heap) hypotheses := by
  exact ⟨term_returns bindings state published sorts terms theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
    tableTerms formalArguments sort ret value binary identifier history.length arity count stack heap dummies hypotheses saved
      arguments rest values save resolverName tablesName stateName binaryName saveName resolverCaptured tablesCaptured
      stateCaptured binaryCaptured saveCaptured resolved declared popped projected,
    built.term binary identifier values coherent popped projected,
    term_coherent history stack heap hypotheses arguments rest binary identifier formalArguments.length values save coherent popped⟩

end Mettapedia.Languages.MM0.MeTTa.MMBAllocationExecution
