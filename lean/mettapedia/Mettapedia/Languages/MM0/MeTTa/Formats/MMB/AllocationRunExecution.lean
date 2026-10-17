import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AllocationResolution

/-!
# Original MMB allocation commands in the recursive proof driver

This module extends qualified assertion-mode source execution through term
and dummy allocations. It keeps the original state atoms, resolver lookups,
stack projections, code intervals and refusal suffix. Theorem application and
conversion commands remain separate source qualification obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MM0.MeTTa.MMBAllocationRunExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom applySubst_nil)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue SupportedStep)
open MMBAllocationExecution
open MMBAllocationResolution
open Kernel (Preterm)

abbrev program := MMBAllocationExecution.program

/-- Chronological evidence for the complete original state atom. Saved proof
witness validity is independent of expression allocation authority. -/
def StateAuthority (history : List Atom) (before : Atom) : Prop :=
  ∃ arity count stack heap dummies hypotheses saved,
    before = stateValue history.length arity count stack heap dummies hypotheses saved ∧
    StateCoherent history stack heap hypotheses

theorem StateAuthority.mk {history stack heap dummies hypotheses saved : List Atom} (arity count : Nat)
    (coherent : StateCoherent history stack heap hypotheses) :
    StateAuthority history (stateValue history.length arity count stack heap dummies hypotheses saved) :=
  ⟨arity, count, stack, heap, dummies, hypotheses, saved, rfl, coherent⟩

theorem StateAuthority.fields {history stack heap dummies hypotheses saved : List Atom}
    {next arity count : Nat}
    (authorized : StateAuthority history (stateValue next arity count stack heap dummies hypotheses saved)) :
    next = history.length ∧ StateCoherent history stack heap hypotheses := by
  obtain ⟨originalArity, originalCount, originalStack, originalHeap, originalDummies, originalHypotheses, originalSaved, same, coherent⟩ := authorized
  simp only [stateValue, listValue, Atom.expression.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨nextSame, _, _, stackSame, heapSame, _, hypothesesSame, _⟩ := same
  exact ⟨Data.natural_injective nextSame, by simpa only [stackSame, heapSame, hypothesesSame] using coherent⟩

/-- Existing qualified commands retain the same chronological authority.
Their source guards and refusal results are unchanged. -/
theorem retained_authority {history : List Atom} {before : Atom} {opcode data : Nat} {result : Option Atom}
    (trace : SupportedStep before opcode data result) (authorized : StateAuthority history before) :
    ∀ after, result = some after → StateAuthority history after := by
  cases trace with
  | @reference next arity count stack heap dummies hypotheses saved index entry found reusable =>
      intro after accepted
      cases accepted
      obtain ⟨rfl, coherent⟩ := authorized.fields
      exact StateAuthority.mk arity count (coherent.reference (List.mem_of_getElem? found))
  | missingReference => intro after impossible; simp at impossible
  | @save next arity count rest heap dummies hypotheses saved entry data reusable =>
      intro after accepted
      cases accepted
      obtain ⟨rfl, coherent⟩ := authorized.fields
      exact StateAuthority.mk arity count coherent.save
  | refusePop => intro after impossible; simp at impossible
  | @hypothesis next arity count rest heap dummies hypotheses saved pointer data expression node =>
      intro after accepted
      unfold MMBProofRunExecution.hypothesisResult at accepted
      split at accepted
      · cases accepted
        obtain ⟨rfl, coherent⟩ := authorized.fields
        exact StateAuthority.mk arity count coherent.hypothesis
      · cases accepted

/-- Evidence for original source allocation commands and the already earned
reference/save/hypothesis fragment. It stores no runtime state or algorithm. -/
inductive Command (terms : List MMUResolution.Binding) (resolver tables : Atom) :
    List Atom → Atom → Nat → Nat → Option (List Atom × Atom) → Prop where
  | retained {history : List Atom} {before : Atom} {opcode data : Nat} {result : Option Atom}
      (trace : SupportedStep before opcode data result) :
      Command terms resolver tables history before opcode data (result.map fun after => (history, after))
  | term {published images tableSorts tableTheorems sort ret value : Atom}
      {sorts theorems : List MMUResolution.Binding} {nextSort nextTerm nextTheorem binary identifier arity count : Nat}
      {tableTerms formalArguments history stack heap dummies hypotheses saved arguments rest : List Atom}
      {values : List Preterm} (save : Bool)
      (resolverShape : resolver = MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (tablesShape : tables = .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
      (lookup : MMUResolution.lookup terms (natural binary) = some (natural identifier))
      (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
      (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest)))
      (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)) :
      Command terms resolver tables history (stateValue history.length arity count stack heap dummies hypotheses saved)
        (if save then 17 else 16) binary
        (some (history ++ [applicationEntry history.length binary identifier arguments values],
          stateValue (history.length + 1) arity count (applicationEntry history.length binary identifier arguments values :: rest)
            (if save then heap ++ [applicationEntry history.length binary identifier arguments values] else heap) dummies hypotheses saved))
  | dummy {published images sort : Atom} {sorts theorems : List MMUResolution.Binding}
      {nextSort nextTerm nextTheorem binary arity count : Nat} {history stack heap dummies hypotheses saved : List Atom}
      (resolverShape : resolver = MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (lookup : MMUResolution.lookup sorts (natural binary) = some sort) :
      Command terms resolver tables history (stateValue history.length arity count stack heap dummies hypotheses saved) 19 binary
        (some (history ++ [variableEntry history.length (arity + dummies.length)],
          stateValue (history.length + 1) arity count (variableEntry history.length (arity + dummies.length) :: stack)
            (heap ++ [variableEntry history.length (arity + dummies.length)]) (dummies ++ [sort]) hypotheses saved))
  | missingDummy {published images : Atom} {sorts theorems : List MMUResolution.Binding}
      {nextSort nextTerm nextTheorem binary arity count : Nat} {history stack heap dummies hypotheses saved : List Atom}
      (resolverShape : resolver = MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (lookup : MMUResolution.lookup sorts (natural binary) = none) :
      Command terms resolver tables history (stateValue history.length arity count stack heap dummies hypotheses saved) 19 binary none

/-- Successful original expression pops from a constructed coherent stack
supply their actual kernel-preterm fields, including every ordered duplicate.
No supplied expression-projection correctness premise is needed here. -/
theorem popped_expression_claims {history stack arguments rest : List Atom} {count : Nat}
    (built : ConstructedHistory history)
    (authorized : ∀ entry ∈ stack, AuthorizedEntry history entry)
    (popped : MMBTheoremCommandExecution.Pops .expressions count stack (some (arguments, rest))) :
    ∃ values : List Preterm, MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm) := by
  generalize resultEq : some (arguments, rest) = result at popped
  induction popped generalizing arguments rest with
  | zero stack => cases resultEq; exact ⟨[], .nil⟩
  | empty => cases resultEq
  | wrong => cases resultEq
  | failed => cases resultEq
  | @next count first tail earlier leftover accepted popped ih =>
      cases Option.some.inj resultEq
      obtain ⟨values, projected⟩ := ih (fun entry member => authorized entry (by simp [member])) rfl
      have firstAuthorized := authorized first (by simp)
      have fields : ∃ pointer expression node, first = expressionValue pointer (Data.preterm expression) node := by
        cases firstAuthorized with
        | expression entry authority =>
            obtain ⟨pointer, value, node, rfl, found⟩ := authority
            obtain ⟨expression, represented⟩ := (show AuthorizedExpression history (expressionValue pointer value node) from
              ⟨pointer, value, node, rfl, found⟩).preterm built
            exact ⟨pointer, expression, node, by rw [represented]⟩
        | proved witness target authority =>
            simp [MMBTheoremCommandExecution.StackKind.accepts, provedValue] at accepted
        | conversion witness left right leftAuthority rightAuthority =>
            simp [MMBTheoremCommandExecution.StackKind.accepts] at accepted
      obtain ⟨pointer, expression, node, rfl⟩ := fields
      refine ⟨values ++ [expression], ?_⟩
      rw [List.map_append]
      exact projected.append (.cons pointer (Data.preterm expression) node .nil)

/-- Chronological authority earns the exact expression projection used by the
constructor dispatcher. Original lookup, declaration and pop admission remain
explicit at this preparation boundary. -/
theorem Command.term_from_authority {terms : List MMUResolution.Binding} {resolver tables : Atom}
    {published images tableSorts tableTheorems sort ret value : Atom}
    {sorts theorems : List MMUResolution.Binding} {nextSort nextTerm nextTheorem binary identifier arity count : Nat}
    {tableTerms formalArguments history stack heap dummies hypotheses saved arguments rest : List Atom}
    (save : Bool)
    (resolverShape : resolver = MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesShape : tables = .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (lookup : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (built : ConstructedHistory history) (coherent : StateCoherent history stack heap hypotheses)
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest))) :
    ∃ values : List Preterm,
      Command terms resolver tables history (stateValue history.length arity count stack heap dummies hypotheses saved)
        (if save then 17 else 16) binary
        (some (history ++ [applicationEntry history.length binary identifier arguments values],
          stateValue (history.length + 1) arity count (applicationEntry history.length binary identifier arguments values :: rest)
            (if save then heap ++ [applicationEntry history.length binary identifier arguments values] else heap) dummies hypotheses saved)) := by
  obtain ⟨values, projected⟩ := popped_expression_claims built coherent.2.1 popped
  exact ⟨values, .term save resolverShape tablesShape lookup declared popped projected⟩

/-- Every successful allocation command extends its original history exactly;
retained commands leave that history unchanged. -/
theorem Command.authority {terms : List MMUResolution.Binding} {resolver tables : Atom}
    {history : List Atom} {before : Atom} {opcode data : Nat} {result : Option (List Atom × Atom)}
    (trace : Command terms resolver tables history before opcode data result)
    (built : ConstructedHistory history) (resolved : ResolvedHistory terms history) (authorized : StateAuthority history before) :
    ∀ afterHistory after, result = some (afterHistory, after) →
      ConstructedHistory afterHistory ∧ ResolvedHistory terms afterHistory ∧ StateAuthority afterHistory after := by
  cases trace with
  | @retained history before opcode data result trace =>
      intro afterHistory after accepted
      cases result with
      | none => simp at accepted
      | some value =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact ⟨built, resolved, retained_authority trace authorized value rfl⟩
  | @term published images tableSorts tableTheorems sort ret value sorts theorems nextSort nextTerm nextTheorem binary identifier arity count tableTerms formalArguments history stack heap dummies hypotheses saved arguments rest values save resolverShape tablesShape lookup declared popped projected =>
      intro afterHistory after accepted
      cases accepted
      have coherent := authorized.fields.2
      exact ⟨built.term data identifier values coherent popped projected,
        resolved.application data identifier arguments values lookup,
        by simpa only [List.length_append, List.length_singleton] using
          (StateAuthority.mk arity count (term_coherent history stack heap hypotheses arguments rest data identifier formalArguments.length values save coherent popped))⟩
  | @dummy published images sort sorts theorems nextSort nextTerm nextTheorem binary arity count history stack heap dummies hypotheses saved resolverShape lookup =>
      intro afterHistory after accepted
      cases accepted
      exact ⟨.variableNode built _, resolved.variable _,
        by simpa only [List.length_append, List.length_singleton] using
          (StateAuthority.mk arity count (dummy_coherent history stack heap dummies hypotheses arity authorized.fields.2))⟩
  | missingDummy => intro afterHistory after impossible; simp at impossible

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD ⟨"", [], .symbol "None"⟩
private def stepEquation := sourceEquation "mm0:mmb:proof-step"
private def stepCondition : Atom :=
  .expression [.symbol "or", .expression [.symbol "==", .var "mode", .symbol "MM0:MMBAssertion"],
    .expression [.symbol "and", .expression [.symbol "==", .var "mode", .symbol "MM0:MMBDefinition"],
      .expression [.symbol "is-member", .var "opcode", .expression [natural 16, natural 17, natural 18, natural 19, natural 31]]]]
private def stepCases : SpaceSemantics.Cases :=
  match stepEquation.body with
  | .expression [_, _, .expression [_, _, .expression rows], _] => (readCases rows).getD []
  | _ => []
private def stepEnvironment (resolver tables formal before : Atom) (opcode data start after : Nat) : Subst :=
  [("after", natural after), ("start", natural start), ("data", natural data), ("opcode", natural opcode),
    ("state", before), ("mode", .symbol "MM0:MMBAssertion"), ("formal", formal), ("tables", tables), ("resolver", resolver)]
private theorem step_unique : program.equations.filter (·.head == "mm0:mmb:proof-step") = [stepEquation] := by decide +kernel
private theorem step_formals : stepEquation.arguments =
    [.var "resolver", .var "tables", .var "formal", .var "mode", .var "state",
      .expression [.symbol "MM0:MMBCode", .var "opcode", .var "data", .var "start", .var "after"]] := by decide
private theorem step_shape : stepEquation.body =
    .expression [.symbol "if", stepCondition,
      .expression [.symbol "case", .var "opcode", .expression (stepCases.map fun row => .expression [row.1, row.2])], .symbol "None"] := by decide
private theorem stepCases_shape : stepCases =
  [(natural 16, .expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean false]),
   (natural 17, .expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean true]),
   (natural 18, .expression [.symbol "mm0:mmb:proof-reference", .var "state", .var "data"]),
   (natural 19, .expression [.symbol "mm0:mmb:proof-dummy", .var "resolver", .var "state", .var "data"]),
   (natural 20, .expression [.symbol "mm0:mmb:proof-theorem", .var "resolver", .var "tables", .var "formal", .var "state", .var "data", boolean false]),
   (natural 21, .expression [.symbol "mm0:mmb:proof-theorem", .var "resolver", .var "tables", .var "formal", .var "state", .var "data", boolean true]),
   (natural 22, .expression [.symbol "mm0:mmb:proof-hypothesis", .var "state"]),
   (natural 23, .expression [.symbol "mm0:mmb:proof-conversion", .var "state"]),
   (natural 24, .expression [.symbol "mm0:mmb:proof-reflexivity", .var "state"]),
   (natural 25, .expression [.symbol "mm0:mmb:proof-symmetry", .var "state"]),
   (natural 26, .expression [.symbol "mm0:mmb:proof-congruence", .var "resolver", .var "state"]),
   (natural 27, .expression [.symbol "mm0:mmb:proof-unfold", .var "resolver", .var "tables", .var "formal", .var "state"]),
   (natural 28, .expression [.symbol "mm0:mmb:proof-cut", .var "state"]),
   (natural 30, .expression [.symbol "mm0:mmb:proof-save", .var "state", boolean true]),
   (natural 31, .expression [.symbol "mm0:mmb:proof-save", .var "state", boolean false]), (.var "bad", .symbol "None")] := by decide
private theorem step_clause (resolver tables formal before : Atom) (opcode data start after : Nat) :
    clauses program "mm0:mmb:proof-step" [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, MMBExecution.commandValue opcode data start after] =
      [.evaluate (stepEnvironment resolver tables formal before opcode data start after) stepEquation.body] := by
  rw [clauses_use_only_the_named_equations, step_unique]
  simp [step_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, stepEnvironment, MMBExecution.commandValue]

private theorem step_condition_returns (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (supported : opcode = 16 ∨ opcode = 17 ∨ opcode = 19) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state stepCondition state (boolean true) := by
  apply completed_run_has_path program 100 _ state [boolean true] [] []
  rcases supported with rfl | rfl | rfl <;> rfl

private theorem step_body_from_call (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (call result : Atom)
    (supported : opcode = 16 ∨ opcode = 17 ∨ opcode = 19)
    (selected : SpaceSemantics.selectCase (stepEnvironment resolver tables formal before opcode data start after) (natural opcode) stepCases =
      some (stepEnvironment resolver tables formal before opcode data start after, call))
    (computed : PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state call state result) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state stepEquation.body state result := by
  rw [step_shape]
  apply if_returns program _ state state state _ (boolean true) _ _ _
    (step_condition_returns state resolver tables formal before opcode data start after supported)
  simp only [boolean, beq_self_eq_true, ↓reduceIte]
  exact case_returns program _ _ state state state (.var "opcode") (natural opcode) call _ _ stepCases
    (read_cases_encoded stepCases) (variable_returns program _ state "opcode") selected computed

private theorem step_raw_from_body (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Atom)
    (resolverName tablesName formalName modeName stateName codeName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (codeCaptured : applySubst bindings (.var codeName) = MMBExecution.commandValue opcode data start after)
    (body : PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state stepEquation.body state result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-step", .var resolverName, .var tablesName,
      .var formalName, .var modeName, .var stateName, .var codeName]) state result := by
  apply authored_variable_call_returns program bindings (stepEnvironment resolver tables formal before opcode data start after)
    state state "mm0:mmb:proof-step" [resolverName, tablesName, formalName, modeName, stateName, codeName] stepEquation.body result
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ body (by decide)
  simpa [resolverCaptured, tablesCaptured, formalCaptured, modeCaptured, stateCaptured, codeCaptured] using
    step_clause resolver tables formal before opcode data start after


private theorem term_literal_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images tableSorts tableTheorems : Atom)
    (tableTerms formalArguments : List Atom) (sort ret value : Atom)
    (binary identifier next arity count : Nat) (stack heap dummies hypotheses saved arguments rest : List Atom)
    (values : List Preterm) (save : Bool)
    (resolverCaptured : applySubst bindings (.var "resolver") =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var "tables") =
      .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (stateCaptured : applySubst bindings (.var "state") = stateValue next arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var "data") = natural binary)
    (resolved : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest)))
    (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-term",
      .var "resolver", .var "tables", .var "state", .var "data", boolean save]) state
      (optionValue (some (stateValue (next + 1) arity count
        (applicationEntry next binary identifier arguments values :: rest)
        (if save then heap ++ [applicationEntry next binary identifier arguments values] else heap)
        dummies hypotheses saved))) := by
  let prior : Subst := [("r", MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images),
    ("t", .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems]),
    ("s", stateValue next arity count stack heap dummies hypotheses saved), ("b", natural binary), ("v", boolean save)]
  have original := term_returns prior state published sorts terms theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
    tableTerms formalArguments sort ret value binary identifier next arity count stack heap dummies hypotheses saved arguments rest values save
    "r" "t" "s" "b" "v" rfl rfl rfl rfl rfl resolved declared popped projected
  apply captured_call_returns program prior bindings state state "mm0:mmb:proof-term"
    [.var "r", .var "t", .var "s", .var "b", .var "v"]
    [.var "resolver", .var "tables", .var "state", .var "data", boolean save] _
    (by decide +kernel) (by decide) _ _ _ original
  · intro offset argument selected
    have member := List.mem_of_getElem? selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr rfl
  · intro offset argument selected
    have member := List.mem_of_getElem? selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals exact Or.inr (by cases save <;> rfl)
  · simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, stateCaptured, binaryCaptured]
    cases save <;> rfl

/-- The original dispatcher executes every qualified allocation command.
The allocation history is proof evidence; the target answer is the unchanged
original optional state atom. -/
theorem Command.step_returns {terms : List MMUResolution.Binding} {history : List Atom}
    (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Option (List Atom × Atom))
    (resolverName tablesName formalName modeName stateName codeName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (codeCaptured : applySubst bindings (.var codeName) = MMBExecution.commandValue opcode data start after)
    (trace : Command terms resolver tables history before opcode data result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-step", .var resolverName, .var tablesName,
      .var formalName, .var modeName, .var stateName, .var codeName]) state (optionValue (result.map Prod.snd)) := by
  cases trace with
  | @retained history before opcode data result trace =>
      have projection : (result.map fun after => (history, after)).map Prod.snd = result := by cases result <;> rfl
      rw [projection]
      exact MMBProofRunExecution.step_returns bindings state resolver tables formal before opcode data start after result
          resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured trace
  | @term published images tableSorts tableTheorems sort ret value sorts theorems nextSort nextTerm nextTheorem binary identifier arity count tableTerms formalArguments history stack heap dummies hypotheses saved arguments rest values save resolverShape tablesShape lookup declared popped projected =>
      apply step_raw_from_body bindings state resolver tables formal _ _ _ start after _
        resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured
      cases save with
      | false =>
          apply step_body_from_call state resolver tables formal _ 16 data start after (.expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean false]) _ (Or.inl rfl)
          · simp [stepCases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
          · apply term_literal_returns _ state published sorts terms theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
              tableTerms formalArguments sort ret value data identifier history.length arity count stack heap dummies hypotheses saved arguments rest values false
              _ _ rfl rfl lookup declared popped projected
            · change resolver = _; exact resolverShape
            · change tables = _; exact tablesShape
      | true =>
          apply step_body_from_call state resolver tables formal _ 17 data start after (.expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean true]) _ (Or.inr (Or.inl rfl))
          · simp [stepCases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
          · apply term_literal_returns _ state published sorts terms theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
              tableTerms formalArguments sort ret value data identifier history.length arity count stack heap dummies hypotheses saved arguments rest values true
              _ _ rfl rfl lookup declared popped projected
            · change resolver = _; exact resolverShape
            · change tables = _; exact tablesShape
  | @dummy published images sort sorts theorems nextSort nextTerm nextTheorem binary arity count history stack heap dummies hypotheses saved resolverShape lookup =>
      apply step_raw_from_body bindings state resolver tables formal _ 19 data start after _
        resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured
      apply step_body_from_call state resolver tables formal _ 19 data start after (.expression [.symbol "mm0:mmb:proof-dummy", .var "resolver", .var "state", .var "data"]) _ (Or.inr (Or.inr rfl))
      · simp [stepCases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · have executed := dummy_returns (stepEnvironment resolver tables formal _ 19 data start after) state published sorts terms theorems
          nextSort nextTerm nextTheorem images data history.length arity count stack heap dummies hypotheses saved
          "resolver" "state" "data" (by change resolver = _; exact resolverShape) rfl rfl
        simpa only [dummyResultValue, lookup, Option.map_some, stateValue] using executed
  | @missingDummy published images sorts theorems nextSort nextTerm nextTheorem binary arity count history stack heap dummies hypotheses saved resolverShape lookup =>
      apply step_raw_from_body bindings state resolver tables formal _ 19 data start after _
        resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured
      apply step_body_from_call state resolver tables formal _ 19 data start after (.expression [.symbol "mm0:mmb:proof-dummy", .var "resolver", .var "state", .var "data"]) _ (Or.inr (Or.inr rfl))
      · simp [stepCases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · have executed := dummy_returns (stepEnvironment resolver tables formal _ 19 data start after) state published sorts terms theorems
          nextSort nextTerm nextTheorem images data history.length arity count stack heap dummies hypotheses saved
          "resolver" "state" "data" (by change resolver = _; exact resolverShape) rfl rfl
        simpa only [dummyResultValue, lookup, Option.map_none, stateValue] using executed


/-- Arbitrary finite original assertion runs in the earned allocation,
reference, save and hypothesis fragment. A refusal leaves its suffix unread. -/
inductive Run (terms : List MMUResolution.Binding) (resolver tables : Atom) :
    List Atom → Atom → List Atom → Option (List Atom × Atom) → Prop where
  | done (history : List Atom) (before : Atom) : Run terms resolver tables history before [] (some (history, before))
  | next {history middleHistory : List Atom} {before middle : Atom} {opcode data start after : Nat}
      {rest : List Atom} {result : Option (List Atom × Atom)}
      (advanced : Command terms resolver tables history before opcode data (some (middleHistory, middle)))
      (continued : Run terms resolver tables middleHistory middle rest result) :
      Run terms resolver tables history before (MMBExecution.commandValue opcode data start after :: rest) result
  | refused {history : List Atom} {before : Atom} {opcode data start after : Nat} (rest : List Atom)
      (stopped : Command terms resolver tables history before opcode data none) :
      Run terms resolver tables history before (MMBExecution.commandValue opcode data start after :: rest) none

/-- Every previously qualified original run embeds in the allocation-aware
contract without adding runtime allocation or changing its source result. -/
theorem Run.of_supported {terms : List MMUResolution.Binding} {resolver tables : Atom}
    (history : List Atom) {before : Atom} {commands : List Atom} {result : Option Atom}
    (supported : MMBProofRunExecution.SupportedRun before commands result) :
    Run terms resolver tables history before commands (result.map fun after => (history, after)) := by
  induction supported with
  | done before => exact .done history before
  | next advanced continued ih => exact .next (.retained advanced) ih
  | refused rest stopped => exact .refused rest (.retained stopped)

/-- Chronological allocation and fixed-map authorization survive every
successful original run, without validating arbitrary stored proof witnesses. -/
theorem Run.authority {terms : List MMUResolution.Binding} {resolver tables : Atom}
    {history commands : List Atom} {before : Atom} {result : Option (List Atom × Atom)}
    (trace : Run terms resolver tables history before commands result)
    (built : ConstructedHistory history) (resolved : ResolvedHistory terms history) (authorized : StateAuthority history before) :
    ∀ afterHistory after, result = some (afterHistory, after) →
      ConstructedHistory afterHistory ∧ ResolvedHistory terms afterHistory ∧ StateAuthority afterHistory after := by
  induction trace with
  | done history before =>
      intro afterHistory after accepted
      cases accepted
      exact ⟨built, resolved, authorized⟩
  | next advanced continued ih =>
      obtain ⟨middleBuilt, middleResolved, middleAuthorized⟩ := advanced.authority built resolved authorized _ _ rfl
      exact ih middleBuilt middleResolved middleAuthorized
  | refused rest stopped => intro afterHistory after impossible; simp at impossible

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def runEquation := sourceEquation "mm0:mmb:proof-run"
private def runCases := casesOf runEquation.body
private def runCons := (runCases[1]'(by decide)).2
private def runConsCases := casesOf runCons
private def runTail := (runConsCases[0]'(by decide)).2
private def runEnvironment (resolver tables formal before : Atom) (commands : List Atom) : Subst :=
  [("codes", .expression commands), ("state", before), ("mode", .symbol "MM0:MMBAssertion"),
    ("formal", formal), ("tables", tables), ("resolver", resolver)]
private theorem run_unique : program.equations.filter (·.head == "mm0:mmb:proof-run") = [runEquation] := by decide +kernel
private theorem run_formals : runEquation.arguments =
    [.var "resolver", .var "tables", .var "formal", .var "mode", .var "state",
      .expression [.symbol "MM0:L", .var "codes"]] := by decide
private theorem run_shape : runEquation.body =
    .expression [.symbol "case", .var "codes",
      .expression (runCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem run_cases_shape : runCases =
    [(.expression [], .expression [.symbol "Some", .var "state"]),
     (.expression [.symbol "cons", .var "first", .var "rest"], runCons),
     (.var "bad", .symbol "None")] := by decide
private theorem run_cons_shape : runCons =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:proof-step", .var "resolver", .var "tables", .var "formal",
      .var "mode", .var "state", .var "first"],
      .expression (runConsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem run_cons_cases_shape : runConsCases =
    [(.expression [.symbol "Some", .var "after"], runTail), (.var "bad", .symbol "None")] := by decide
private theorem run_tail_shape : runTail =
    .expression [.symbol "mm0:mmb:proof-run", .var "resolver", .var "tables", .var "formal", .var "mode",
      .var "after", .expression [.symbol "MM0:L", .var "rest"]] := by decide
private theorem run_clause (resolver tables formal before : Atom) (commands : List Atom) :
    clauses program "mm0:mmb:proof-run"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands] =
      [.evaluate (runEnvironment resolver tables formal before commands) runEquation.body] := by
  rw [clauses_use_only_the_named_equations, run_unique]
  simp [run_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, runEnvironment, listValue]

private theorem raw_run_from_body (bindings : Subst) (state : State)
    (resolver tables formal before : Atom) (commands : List Atom) (result : Option Atom)
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands])
    (body : PureReturns program (runEnvironment resolver tables formal before commands)
      state runEquation.body state (optionValue result)) :
    PureReturns program bindings state (.expression (.symbol "mm0:mmb:proof-run" :: arguments))
      state (optionValue result) := by
  have length : arguments.length = 6 := by
    have sizes := congrArg List.length captured
    simpa using sizes
  apply raw_call_returns program bindings state state "mm0:mmb:proof-run" arguments _
    (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    rw [length] at bounded
    have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured, length]
    exact authored_function_arguments_return program bindings
      (runEnvironment resolver tables formal before commands) state state "mm0:mmb:proof-run"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands] 6
      runEquation.body _ (by decide) (by decide) (run_clause resolver tables formal before commands) body

private theorem run_body_returns {terms : List MMUResolution.Binding} {history : List Atom} (state : State) (resolver tables formal : Atom)
    {before : Atom} {commands : List Atom} {result : Option (List Atom × Atom)}
    (supported : Run terms resolver tables history before commands result) :
    PureReturns program (runEnvironment resolver tables formal before commands)
      state runEquation.body state (optionValue (result.map Prod.snd)) := by
  induction supported with
  | done history before =>
      let bindings := runEnvironment resolver tables formal before []
      rw [run_shape]
      apply case_returns program bindings bindings state state state (.var "codes")
        (.expression []) (.expression [.symbol "Some", .var "state"]) _ _
        runCases (read_cases_encoded runCases)
      · exact variable_returns program bindings state "codes"
      · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · simpa [bindings, runEnvironment, applySubst, Subst.lookup, optionValue] using
          unary_constructor_returns program bindings state "Some" "state" (by decide +kernel) (by decide)
  | @next history middleHistory before middle opcode data start after rest result advanced continued ih =>
      let command := MMBExecution.commandValue opcode data start after
      let bindings := runEnvironment resolver tables formal before (command :: rest)
      let bound := ("rest", .expression rest) :: ("first", command) :: bindings
      let resumed := ("after", middle) :: bound
      rw [run_shape]
      apply case_returns program bindings bound state state state (.var "codes")
        (.expression (command :: rest)) runCons _ _ runCases (read_cases_encoded runCases)
      · exact variable_returns program bindings state "codes"
      · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, bound, bindings, runEnvironment]
      · rw [run_cons_shape]
        apply case_returns program bound resumed state state state _ (optionValue (some middle)) runTail
          _ _ runConsCases (read_cases_encoded runConsCases)
        · apply Command.step_returns bound state resolver tables formal before opcode data start after (some (middleHistory, middle))
            "resolver" "tables" "formal" "mode" "state" "first" _ _ _ _ _ rfl advanced
          all_goals simp [bound, bindings, runEnvironment, applySubst, Subst.lookup]
        · simp [run_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, resumed, bound,
            bindings, runEnvironment, optionValue]
        · rw [run_tail_shape]
          apply raw_run_from_body resumed state resolver tables formal middle rest (result.map Prod.snd) _ _ ih
          simp [resumed, bound, bindings, runEnvironment, applySubst, applySubst.applySubstList,
            Subst.lookup, listValue]
  | @refused history before opcode data start after rest stopped =>
      let command := MMBExecution.commandValue opcode data start after
      let bindings := runEnvironment resolver tables formal before (command :: rest)
      let bound := ("rest", .expression rest) :: ("first", command) :: bindings
      let refused := ("bad", .symbol "None") :: bound
      rw [run_shape]
      apply case_returns program bindings bound state state state (.var "codes")
        (.expression (command :: rest)) runCons _ _ runCases (read_cases_encoded runCases)
      · exact variable_returns program bindings state "codes"
      · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, bound, bindings, runEnvironment]
      · rw [run_cons_shape]
        apply case_returns program bound refused state state state _ (.symbol "None") (.symbol "None")
          _ _ runConsCases (read_cases_encoded runConsCases)
        · apply Command.step_returns bound state resolver tables formal before opcode data start after none
            "resolver" "tables" "formal" "mode" "state" "first" _ _ _ _ _ rfl stopped
          all_goals simp [bound, bindings, runEnvironment, applySubst, Subst.lookup]
        · simp [run_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            matchAtom, Subst.lookup, refused, bound, bindings, runEnvironment]
        · exact symbol_returns program refused state "None"


/-- The original recursive proof program returns the original state readout
for arbitrary finite runs of the earned command fragment. -/
theorem run_returns {terms : List MMUResolution.Binding} {history : List Atom}
    (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (commands : List Atom) (result : Option (List Atom × Atom))
    (resolverName tablesName formalName modeName stateName commandsName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (commandsCaptured : applySubst bindings (.var commandsName) = listValue commands)
    (supported : Run terms resolver tables history before commands result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-run", .var resolverName, .var tablesName, .var formalName,
        .var modeName, .var stateName, .var commandsName]) state (optionValue (result.map Prod.snd)) := by
  apply raw_run_from_body bindings state resolver tables formal before commands (result.map Prod.snd) _ _
    (run_body_returns state resolver tables formal supported)
  simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, formalCaptured,
    modeCaptured, stateCaptured, commandsCaptured]

/-- Arbitrary completed runs have sufficient evaluator fuel and retain their
ordered one-result observation at every greater fuel. -/
theorem run_sufficient_fuel {terms : List MMUResolution.Binding} {history : List Atom}
    (state : State) (resolver tables formal before : Atom)
    (commands : List Atom) (result : Option (List Atom × Atom))
    (supported : Run terms resolver tables history before commands result) :
    ∃ fuel, ∀ extra, Eval.run program (fuel + extra)
      { state, control := .evaluate [] (.expression [.symbol "mm0:mmb:proof-run", resolver,
        tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands]) } =
      .complete state [optionValue (result.map Prod.snd)] [] [] := by
  have returned := raw_run_from_body [] state resolver tables formal before commands (result.map Prod.snd)
    [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands]
    (by simp only [List.map_cons, List.map_nil, applySubst_nil])
    (run_body_returns state resolver tables formal supported)
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program [] state state _ _ returned
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [optionValue (result.map Prod.snd)] [] [] completed⟩


/-- The original completed observation cannot acquire a different state,
answer multiplicity or I/O suffix at another evaluator fuel. -/
theorem run_completed_exact {terms : List MMUResolution.Binding} {history : List Atom}
    (state : State) (resolver tables formal before : Atom)
    (commands : List Atom) (result : Option (List Atom × Atom))
    (supported : Run terms resolver tables history before commands result)
    (fuel : Nat) (observedState : State) (answers input output : List Atom)
    (completed : Eval.run program fuel
      { state, control := .evaluate [] (.expression [.symbol "mm0:mmb:proof-run", resolver,
        tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands]) } =
      .complete observedState answers input output) :
    observedState = state ∧ answers = [optionValue (result.map Prod.snd)] ∧ input = [] ∧ output = [] := by
  obtain ⟨enough, computed⟩ := run_sufficient_fuel state resolver tables formal before commands result supported
  obtain ⟨stateSame, answersSame, inputSame, outputSame⟩ := completed_result_unique program enough fuel _
    state observedState [optionValue (result.map Prod.snd)] [] [] answers input output (by simpa using computed 0) completed
  exact ⟨stateSame.symm, answersSame.symm, inputSame.symm, outputSame.symm⟩

end Mettapedia.Languages.MM0.MeTTa.MMBAllocationRunExecution
