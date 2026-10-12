import Mettapedia.Languages.HOLLight.MeTTa.Representation
import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Typed binder lookup in the authored HOL Light library

Nearest-binder lookup executes the quoted source equation and agrees with
the shared HOL positional elaboration. Typed names are reflected through
the admitted context, so equal spellings at distinct types remain distinct.
The source context and the initial positional offset are both retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.ContextLookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (sourceVariableAtom registeredOperatorAtom)

def contextAtom (context : List SourceVar) : Atom :=
  Premises.keys (context.map (sourceVariableAtom registeredOperatorAtom))

def indexAnswer (offset : Nat) (index : Option Nat) : Atom :=
  Lookup.answer (index.map fun position => .grounded (.int (offset + position)))

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:bound-index"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def increment : Atom := .expression [.symbol "+", .var "index", .grounded (.int 1)]

private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "variable", .var "binder"],
  .expression [.symbol "Some", .var "index"],
  .expression [.symbol "hol-light:bound-index", .var "variable", .var "rest", increment]]

private def environment (needle : SourceVar) (context : List SourceVar) (offset : Nat) : Subst :=
  [("index", .grounded (.int offset)), ("context", contextAtom context),
    ("variable", sourceVariableAtom registeredOperatorAtom needle)]

private def boundEnvironment (needle binder : SourceVar) (rest : List SourceVar) (offset : Nat) : Subst :=
  [("rest", contextAtom rest), ("binder", sourceVariableAtom registeredOperatorAtom binder)] ++
    environment needle (binder :: rest) offset

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:bound-index") = [equation] := by rfl

private theorem formals : equation.arguments = [.var "variable", .var "context", .var "index"] := by decide

private theorem body_shape : equation.body = .expression [.symbol "case", .var "context",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", .symbol "None"),
     (.expression [.symbol "HOL:Cons", .var "binder", .var "rest"], consBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (needle : SourceVar) (context : List SourceVar) (offset : Nat) :
    clauses program "hol-light:bound-index"
      [sourceVariableAtom registeredOperatorAtom needle, contextAtom context, .grounded (.int offset)] =
      [.evaluate (environment needle context offset) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_certificate (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment needle context offset) state equation.body state
      (indexAnswer offset (boundIndex needle context)) := by
  classical
  induction context generalizing offset with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment needle [] offset) (environment needle [] offset) state state state
        (.var "context") (.symbol "HOL:Nil") (.symbol "None") _ _ cases (read_cases_encoded cases)
      · simpa [environment, contextAtom, Premises.keys, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment needle [] offset) state "context"
      · simp [cases_shape, environment, contextAtom, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.symbol_returns program _ state "None"
  | cons binder rest ih =>
      have binderFormed := contextFormed binder (by simp)
      have restFormed := fun other (member : other ∈ rest) => contextFormed other (by simp [member])
      have equality : (sourceVariableAtom registeredOperatorAtom needle ==
          sourceVariableAtom registeredOperatorAtom binder) = decide (needle = binder) := by
        simp only [beq_eq_decide, Representation.registered_sourceVariableAtom_eq_iff
          theory needle binder needleFormed binderFormed]
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment needle (binder :: rest) offset)
        (boundEnvironment needle binder rest offset) state state state
        (.var "context") (contextAtom (binder :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "context"
      · simp [cases_shape, environment, boundEnvironment, contextAtom, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.if_returns program (boundEnvironment needle binder rest offset) state state state _
          (boolean (decide (needle = binder))) _ _ _
        · apply BoundCalls.CorePath.native_variable_call_returns program (boundEnvironment needle binder rest offset)
            state state "==" ["variable", "binder"] _ (by decide) (by decide) _ (by decide)
          simp [StdLib.structural_equality, boundEnvironment, environment, applySubst, Subst.lookup, equality]
        · by_cases same : needle = binder
          · simp only [same, decide_true, boolean, BEq.rfl, ↓reduceIte]
            simpa [indexAnswer, boundIndex, same, Lookup.answer, boundEnvironment,
              environment, applySubst, Subst.lookup] using
              BoundCalls.CorePath.unary_constructor_returns program (boundEnvironment needle binder rest offset)
                state "Some" "index" (by decide) (by decide)
          · simp only [same, decide_false, boolean]
            have recursive := ih restFormed (offset + 1)
            have answerSame : indexAnswer (offset + 1) (boundIndex needle rest) =
                indexAnswer offset (boundIndex needle (binder :: rest)) := by
              simp only [boundIndex, sourceVarSame_eq_true_iff, same, ↓reduceIte]
              cases boundIndex needle rest <;> simp [indexAnswer, Lookup.answer]
              omega
            rw [← answerSame]
            apply BoundCalls.CorePath.call_returns program (boundEnvironment needle binder rest offset) state state
              "hol-light:bound-index" [.var "variable", .var "rest", increment] _ (by decide) _ (by decide)
            apply BoundCalls.CorePath.evaluated_argument_returns program (boundEnvironment needle binder rest offset) state state state
              (.function "hol-light:bound-index") (.var "variable") _ _
              [.var "rest", increment] [] 0 (by decide)
              (BoundCalls.CorePath.variable_returns program _ state "variable")
            apply BoundCalls.CorePath.evaluated_argument_returns program (boundEnvironment needle binder rest offset) state state state
              (.function "hol-light:bound-index") (.var "rest") _ _ [increment] [_] 1 (by decide)
              (BoundCalls.CorePath.variable_returns program _ state "rest")
            apply BoundCalls.CorePath.evaluated_argument_returns program (boundEnvironment needle binder rest offset) state state state
              (.function "hol-light:bound-index") increment (.grounded (.int (offset + 1))) _
              [] [_, _] 2 (by decide) _ _
            · unfold increment
              apply BoundCalls.CorePath.native_binary_call_returns program (boundEnvironment needle binder rest offset)
                state state state state "+" (.var "index") (.grounded (.int 1))
                (.grounded (.int offset)) (.grounded (.int 1)) (.grounded (.int (offset + 1)))
                (by decide) (by decide) (by decide) (by decide) _
                (BoundCalls.CorePath.grounded_returns program _ state _) _ (by decide)
              · simpa [boundEnvironment, environment, applySubst, Subst.lookup] using
                  BoundCalls.CorePath.variable_returns program (boundEnvironment needle binder rest offset) state "index"
              · simp [StdLib.integer_addition]
            · apply BoundCalls.CorePath.authored_function_arguments_return program (boundEnvironment needle binder rest offset)
                (environment needle rest (offset + 1)) state state "hol-light:bound-index"
                [_, _, .grounded (.int (offset + 1))] 3 equation.body _
                (by decide) (by decide) _ recursive
              simpa [boundEnvironment, environment, applySubst, Subst.lookup] using clause needle rest (offset + 1)

/-- The authored binder lookup agrees with shared positional elaboration on
arbitrary admitted contexts, including absent and shadowed typed names. -/
theorem authored_bound_index_certificate (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (bindings : Subst) (state : State) (needleKey contextKey indexKey : String)
    (capturedNeedle : applySubst bindings (.var needleKey) = sourceVariableAtom registeredOperatorAtom needle)
    (capturedContext : applySubst bindings (.var contextKey) = contextAtom context)
    (capturedIndex : applySubst bindings (.var indexKey) = .grounded (.int offset)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:bound-index", .var needleKey, .var contextKey, .var indexKey]) state
      (indexAnswer offset (boundIndex needle context)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment needle context offset) state state
    "hol-light:bound-index" [needleKey, contextKey, indexKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_certificate theory needle needleFormed context contextFormed offset state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedNeedle, capturedContext, capturedIndex] using
    clause needle context offset

/-- Computed source values and a literal initial offset use the same authored
lookup, retaining the nearest typed binder and the supplied context. -/
private theorem body_returns (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (state : State) :
    PureReturns program (environment needle context offset) state equation.body state
      (indexAnswer offset (boundIndex needle context)) :=
  (body_certificate theory needle needleFormed context contextFormed offset state).original

theorem authored_bound_index_computed_return (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (bindings : Subst) (state : State) (needleExpr contextExpr indexExpr : Atom)
    (needleComputed : PureReturns program bindings state needleExpr state (sourceVariableAtom registeredOperatorAtom needle))
    (contextComputed : PureReturns program bindings state contextExpr state (contextAtom context))
    (indexComputed : PureReturns program bindings state indexExpr state (.grounded (.int offset))) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:bound-index", needleExpr, contextExpr, indexExpr]) state
      (indexAnswer offset (boundIndex needle context)) := by
  apply call_returns program bindings state state "hol-light:bound-index" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:bound-index")
    needleExpr _ _ [contextExpr, indexExpr] [] 0 (by decide) needleComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:bound-index")
    contextExpr _ _ [indexExpr] [_] 1 (by decide) contextComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:bound-index")
    indexExpr _ _ [] [_, _] 2 (by decide) indexComputed
  exact authored_function_arguments_return program bindings (environment needle context offset) state state
    "hol-light:bound-index" [_, _, _] 3 equation.body _ (by decide) (by decide)
    (clause needle context offset) (body_returns theory needle needleFormed context contextFormed offset state)

theorem authored_bound_index_return (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (bindings : Subst) (state : State) (needleKey contextKey indexKey : String)
    (capturedNeedle : applySubst bindings (.var needleKey) = sourceVariableAtom registeredOperatorAtom needle)
    (capturedContext : applySubst bindings (.var contextKey) = contextAtom context)
    (capturedIndex : applySubst bindings (.var indexKey) = .grounded (.int offset)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:bound-index", .var needleKey, .var contextKey, .var indexKey]) state
      (indexAnswer offset (boundIndex needle context)) :=
  (authored_bound_index_certificate theory needle needleFormed context contextFormed offset bindings state needleKey contextKey indexKey capturedNeedle capturedContext capturedIndex).original

theorem authored_bound_index_bound_return (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (bindings : Subst) (state : State) (needleKey contextKey indexKey : String)
    (capturedNeedle : applySubst bindings (.var needleKey) = sourceVariableAtom registeredOperatorAtom needle)
    (capturedContext : applySubst bindings (.var contextKey) = contextAtom context)
    (capturedIndex : applySubst bindings (.var indexKey) = .grounded (.int offset)) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:bound-index", .var needleKey, .var contextKey, .var indexKey]) state
      (indexAnswer offset (boundIndex needle context)) :=
  (authored_bound_index_certificate theory needle needleFormed context contextFormed offset bindings state needleKey contextKey indexKey capturedNeedle capturedContext capturedIndex).extended

theorem authored_bound_index_computed_certificate (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (bindings : Subst) (state : State) (needleExpr contextExpr indexExpr : Atom)
    (needleComputed : BoundCalls.CorePath.PureReturns program bindings state needleExpr state (sourceVariableAtom registeredOperatorAtom needle))
    (contextComputed : BoundCalls.CorePath.PureReturns program bindings state contextExpr state (contextAtom context))
    (indexComputed : BoundCalls.CorePath.PureReturns program bindings state indexExpr state (.grounded (.int offset))) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:bound-index", needleExpr, contextExpr, indexExpr]) state
      (indexAnswer offset (boundIndex needle context)) := by
  apply BoundCalls.CorePath.call_returns program bindings state state "hol-light:bound-index" _ _ (by decide) _ (by decide)
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:bound-index")
    needleExpr _ _ [contextExpr, indexExpr] [] 0 (by decide) needleComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:bound-index")
    contextExpr _ _ [indexExpr] [_] 1 (by decide) contextComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:bound-index")
    indexExpr _ _ [] [_, _] 2 (by decide) indexComputed
  exact BoundCalls.CorePath.authored_function_arguments_return program bindings (environment needle context offset) state state
    "hol-light:bound-index" [_, _, _] 3 equation.body _ (by decide) (by decide)
    (clause needle context offset) (body_certificate theory needle needleFormed context contextFormed offset state)


end Mettapedia.Languages.HOLLight.MeTTa.ContextLookup
