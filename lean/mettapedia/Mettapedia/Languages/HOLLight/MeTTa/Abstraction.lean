import Mettapedia.Languages.HOLLight.MeTTa.FreeVariables
import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution

/-!
# Executed closing of a typed free variable

The quoted source traversal is connected to the shared canonical binding
operation on checked terms. Its depth is the number of active binders. The
new variable is placed after those binders, while existing bound occurrences
keep both their positions and their contextual type annotations.

Registered type identities make comparison of free variables faithful. A
variable with the same printed name at a different type remains free. This
traversal does not admit theorem records or discharge hypothesis freshness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Abstraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (termAtom variableAtom registeredOperatorAtom)
open TypeSubstitution (typeAtom nameAtom)
open SignatureFormation

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:abstract"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def freeBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "variable", .var "term"],
  .expression [.symbol "HOL:Bound", .var "depth", .var "type"], .var "term"]
private def boundBody : Atom := .expression [.symbol "if",
  .expression [.symbol ">=", .var "index", .var "depth"],
  .expression [.symbol "HOL:Bound", .expression [.symbol "+", .var "index", .grounded (.int 1)],
    .var "type"], .var "term"]
private def increment : Atom := .expression [.symbol "+", .var "depth", .grounded (.int 1)]
private def lambdaBody : Atom := .expression [.symbol "HOL:Lam", .var "type",
  .expression [.symbol "hol-light:abstract", .var "variable", increment, .var "body"]]
private def applicationBody : Atom := .expression [.symbol "HOL:App",
  .expression [.symbol "hol-light:abstract", .var "variable", .var "depth", .var "function"],
  .expression [.symbol "hol-light:abstract", .var "variable", .var "depth", .var "argument"]]
private def environment (constants : Const → Atom) (needle : SourceVar)
    (positions : List Ty) (term : DBTerm) : Subst :=
  [("term", termAtom registeredOperatorAtom constants positions term),
   ("depth", .grounded (.int positions.length)), ("variable", variableAtom registeredOperatorAtom needle)]
private theorem shape : equation.body = .expression [.symbol "case", .var "term",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.expression [.symbol "HOL:Free", .var "name", .var "type"], freeBody),
     (.expression [.symbol "HOL:Bound", .var "index", .var "type"], boundBody),
     (.expression [.symbol "HOL:C", .var "identity", .var "type"], .var "term"),
     (.expression [.symbol "HOL:Lam", .var "type", .var "body"], lambdaBody),
     (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem clause (constants : Const → Atom) (needle : SourceVar)
    (positions : List Ty) (term : DBTerm) :
    clauses program "hol-light:abstract" [variableAtom registeredOperatorAtom needle,
      .grounded (.int positions.length), termAtom registeredOperatorAtom constants positions term] =
      [.evaluate (environment constants needle positions term) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:abstract") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "variable", .var "depth", .var "term"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem computed_call_return (constants : Const → Atom) (needle : SourceVar)
    (positions : List Ty) (term : DBTerm) (bindings : Subst) (state : State)
    (needleExpr depthExpr termExpr answer : Atom)
    (needleReturned : PureReturns program bindings state needleExpr state (variableAtom registeredOperatorAtom needle))
    (depthReturned : PureReturns program bindings state depthExpr state (.grounded (.int positions.length)))
    (termReturned : PureReturns program bindings state termExpr state (termAtom registeredOperatorAtom constants positions term))
    (bodyReturned : PureReturns program (environment constants needle positions term) state equation.body state answer) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:abstract", needleExpr, depthExpr, termExpr]) state answer := by
  apply call_returns program bindings state state "hol-light:abstract" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:abstract")
    needleExpr _ _ [depthExpr, termExpr] [] 0 (by decide) needleReturned
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:abstract")
    depthExpr _ _ [termExpr] [_] 1 (by decide) depthReturned
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:abstract")
    termExpr _ _ [] [_, _] 2 (by decide) termReturned
  exact authored_function_arguments_return program bindings (environment constants needle positions term)
    state state "hol-light:abstract" [_, _, _] 3 equation.body _
    (by decide) (by decide) (clause constants needle positions term) bodyReturned

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (term : DBTerm) (positions : List Ty) (type : Ty)
    (formed : AnnotationsFormed world.signature term) (typed : term.inferType positions = some type)
    (state : State) :
    PureReturns program (environment constants needle positions term) state equation.body state
      (termAtom registeredOperatorAtom constants (positions ++ [needle.ty])
        (DBTerm.closeFreeAt needle positions.length term)) := by
  induction term generalizing positions type with
  | free sourceVar =>
      cases formed with
      | free sourceFormed =>
          let before := environment constants needle positions (.free sourceVar)
          let bound := [("type", typeAtom registeredOperatorAtom sourceVar.ty),
            ("name", nameAtom sourceVar.name)] ++ before
          have equality : (variableAtom registeredOperatorAtom needle == variableAtom registeredOperatorAtom sourceVar) =
              sourceVarSame needle sourceVar := by
            apply Bool.eq_iff_iff.mpr
            simp only [beq_iff_eq, Representation.registered_variableAtom_eq_iff
              world needle sourceVar needleFormed sourceFormed, sourceVarSame_eq_true_iff]
          rw [shape]
          apply case_returns program before bound state state state (.var "term")
            (variableAtom registeredOperatorAtom sourceVar) freeBody _ _ cases (read_cases_encoded cases)
          · simpa [before, environment, termAtom, applySubst, Subst.lookup] using variable_returns program before state "term"
          · simp [cases_shape, bound, before, environment, termAtom, variableAtom,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · unfold freeBody
            apply if_returns program bound state state state _ (boolean (sourceVarSame needle sourceVar)) _ _ _
            · apply native_variable_call_returns program bound state state "==" ["variable", "term"] _
                (by decide) (by decide) _ (by decide)
              simp [StdLib.structural_equality, bound, before, environment, termAtom, applySubst, Subst.lookup, equality]
            · by_cases same : needle = sourceVar
              · subst sourceVar
                have sameVariable : sourceVarSame needle needle = true := (sourceVarSame_eq_true_iff _ _).mpr rfl
                simp only [sameVariable, boolean, BEq.rfl, ↓reduceIte,
                  DBTerm.closeFreeAt_exact, termAtom]
                rw [List.getElem?_append_right (by omega)]
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
                apply binary_constructor_returns program bound state state state "HOL:Bound" (.var "depth") (.var "type")
                  (.grounded (.int positions.length)) (typeAtom registeredOperatorAtom needle.ty) (by decide) (by decide)
                · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
                · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "type"
              · have different : sourceVarSame needle sourceVar = false :=
                  Bool.eq_false_of_not_eq_true (fun found => same ((sourceVarSame_eq_true_iff _ _).mp found))
                simpa [different, boolean, DBTerm.closeFreeAt, bound, before, environment,
                  termAtom, applySubst, Subst.lookup] using variable_returns program bound state "term"
  | bound index =>
      simp only [DBTerm.inferType] at typed
      have inRange : index < positions.length := (List.getElem?_eq_some_iff.mp typed).1
      let before := environment constants needle positions (.bound index)
      let bound := [("type", ((positions[index]?).map (typeAtom registeredOperatorAtom)).getD (.symbol "None")),
        ("index", Atom.grounded (.int index))] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom registeredOperatorAtom constants positions (.bound index)) boundBody _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold boundBody
        apply if_returns program bound state state state _ (boolean false) _ _ _
        · apply native_variable_call_returns program bound state state ">=" ["index", "depth"] _
            (by decide) (by decide) _ (by decide)
          have notGreater : ¬ (positions.length : Int) ≤ index := by omega
          simp [StdLib.greater_equal_comparison, bound, before, environment, applySubst, Subst.lookup, boolean, notGreater]
        · simpa [boolean, DBTerm.closeFreeAt, termAtom, List.getElem?_append_left inRange,
            bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "term"
  | const constant annotation =>
      let before := environment constants needle positions (.const constant annotation)
      let bound := [("type", typeAtom registeredOperatorAtom annotation), ("identity", constants constant)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "term")
        (termAtom registeredOperatorAtom constants positions (.const constant annotation)) (.var "term") _ _ cases
        (read_cases_encoded cases)
      · exact variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [DBTerm.closeFreeAt, termAtom, bound, before, environment, applySubst, Subst.lookup] using
          variable_returns program bound state "term"
  | abs domain body ih =>
      cases formed with
      | abs domainFormed bodyFormed =>
          obtain ⟨codomain, bodyTyped, typeEqual⟩ :
              ∃ codomain, body.inferType (domain :: positions) = some codomain ∧ Ty.function domain codomain = type := by
            cases checked : body.inferType (domain :: positions) <;> simp [DBTerm.inferType, checked] at typed
            exact ⟨_, rfl, typed⟩
          let before := environment constants needle positions (.abs domain body)
          let bound := [("body", termAtom registeredOperatorAtom constants (domain :: positions) body),
            ("type", typeAtom registeredOperatorAtom domain)] ++ before
          rw [shape]
          apply case_returns program before bound state state state (.var "term")
            (termAtom registeredOperatorAtom constants positions (.abs domain body)) lambdaBody _ _ cases (read_cases_encoded cases)
          · exact variable_returns program before state "term"
          · simp [cases_shape, bound, before, environment, termAtom,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · simp only [DBTerm.closeFreeAt, termAtom]
            unfold lambdaBody
            apply binary_constructor_returns program bound state state state "HOL:Lam" (.var "type") _
              (typeAtom registeredOperatorAtom domain) _ (by decide) (by decide)
            · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "type"
            · apply computed_call_return constants needle (domain :: positions) body bound state (.var "variable")
                increment (.var "body") _ _ _ _ (ih (domain :: positions) codomain bodyFormed bodyTyped)
              · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "variable"
              · unfold increment
                apply native_binary_call_returns program bound state state state state "+" (.var "depth") (.grounded (.int 1))
                  (.grounded (.int positions.length)) (.grounded (.int 1))
                  (.grounded (.int (domain :: positions).length)) (by decide) (by decide) (by decide) (by decide) _
                  (grounded_returns program bound state _) _ (by decide)
                · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
                · simp [StdLib.integer_addition]
              · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "body"
  | app function argument functionIH argumentIH =>
      cases formed with
      | app functionFormed argumentFormed =>
          obtain ⟨functionType, argumentType, functionTyped, argumentTyped⟩ :
              ∃ functionType argumentType, function.inferType positions = some functionType ∧
                argument.inferType positions = some argumentType := by
            cases hf : function.inferType positions <;> cases ha : argument.inferType positions <;>
              simp [DBTerm.inferType, hf, ha] at typed
            exact ⟨_, _, rfl, rfl⟩
          let before := environment constants needle positions (.app function argument)
          let bound := [("argument", termAtom registeredOperatorAtom constants positions argument),
            ("function", termAtom registeredOperatorAtom constants positions function)] ++ before
          rw [shape]
          apply case_returns program before bound state state state (.var "term")
            (termAtom registeredOperatorAtom constants positions (.app function argument)) applicationBody _ _ cases
            (read_cases_encoded cases)
          · exact variable_returns program before state "term"
          · simp [cases_shape, bound, before, environment, termAtom,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · simp only [DBTerm.closeFreeAt, termAtom]
            unfold applicationBody
            apply binary_constructor_returns program bound state state state "HOL:App" _ _ _ _ (by decide) (by decide)
            · apply computed_call_return constants needle positions function bound state (.var "variable") (.var "depth")
                (.var "function") _ _ _ _ (functionIH positions functionType functionFormed functionTyped)
              · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "variable"
              · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
              · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "function"
            · apply computed_call_return constants needle positions argument bound state (.var "variable") (.var "depth")
                (.var "argument") _ _ _ _ (argumentIH positions argumentType argumentFormed argumentTyped)
              · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "variable"
              · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "depth"
              · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "argument"

/-- The actual traversal closes one typed free variable beneath arbitrarily
many existing binders and preserves the checked contextual representation. -/
theorem authored_abstract_computed_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (term : DBTerm) (positions : List Ty) (type : Ty)
    (formed : AnnotationsFormed world.signature term) (typed : term.inferType positions = some type)
    (bindings : Subst) (state : State) (needleExpr depthExpr termExpr : Atom)
    (needleReturned : PureReturns program bindings state needleExpr state (variableAtom registeredOperatorAtom needle))
    (depthReturned : PureReturns program bindings state depthExpr state (.grounded (.int positions.length)))
    (termReturned : PureReturns program bindings state termExpr state (termAtom registeredOperatorAtom constants positions term)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:abstract", needleExpr, depthExpr, termExpr]) state
      (termAtom registeredOperatorAtom constants (positions ++ [needle.ty])
        (DBTerm.closeFreeAt needle positions.length term)) :=
  computed_call_return constants needle positions term bindings state needleExpr depthExpr termExpr _
    needleReturned depthReturned termReturned (body_returns world constants needle needleFormed term positions type formed typed state)

namespace Primitive

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:abs"))[0]'(by decide)
private def resultBody : Atom := .expression [.symbol "hol-light:theorem-eq", .var "hyps",
  .expression [.symbol "HOL:Lam", .var "type",
    .expression [.symbol "hol-light:abstract", .var "binder", .grounded (.int 0), .var "left"]],
  .expression [.symbol "HOL:Lam", .var "type",
    .expression [.symbol "hol-light:abstract", .var "binder", .grounded (.int 0), .var "right"]],
  .var "deps", .symbol "ABS"]
private def innerCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .expression [.symbol "HOL:Equation", .var "left", .var "right"]], resultBody),
   (.var "malformed", .symbol "None")]
private def guardBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:free-in", .var "binder", .var "hyps"], .symbol "None",
  .expression [.symbol "case", .expression [.symbol "hol-light:dest-eq", .var "conclusion"],
    .expression (innerCases.map fun row => .expression [row.1, row.2])]]
private def selected : Atom := .expression [.symbol "let", .var "binder",
  .expression [.symbol "HOL:Free", .var "name", .var "type"], guardBody]
private def outerCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Free", .var "name", .var "type"]],
    .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps", .var "conclusion", .var "deps",
      .var "origin"]]], selected), (.var "malformed", .symbol "None")]
private def environment (value premise : Atom) : Subst := [("premise", premise), ("variable", value)]
private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "variable", .var "premise"],
    .expression (outerCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (value premise : Atom) : clauses program "hol-light:abs" [value, premise] =
    [.evaluate (environment value premise) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:abs") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "variable", .var "premise"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Exact hypotheses and dependencies survive successful abstraction. -/
def result (constants : Const → Atom) (needle : SourceVar) (left right : DBTerm) (type : Ty)
    (hypotheses : List DBTerm) (dependencies : List Atom) : Atom :=
  .expression [.symbol "Some", Representation.theoremAtom constants []
    (CanonicalTerm.equalityDB (Ty.function needle.ty type)
      (.abs needle.ty (DBTerm.closeFreeAt needle 0 left)) (.abs needle.ty (DBTerm.closeFreeAt needle 0 right)))
    (hypotheses.map (termAtom registeredOperatorAtom constants [])) dependencies (.symbol "ABS")]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (left right : DBTerm) (type : Ty)
    (leftFormed : AnnotationsFormed world.signature left) (rightFormed : AnnotationsFormed world.signature right)
    (leftTyped : left.inferType [] = some type) (rightTyped : right.inferType [] = some type)
    (hypotheses : List DBTerm) (dependencies : List Atom) (origin : Atom) (state : State) :
    PureReturns program (environment (.expression [.symbol "Some", variableAtom registeredOperatorAtom needle])
      (.expression [.symbol "Some", Transitivity.theoremValue constants [] type left right
        (hypotheses.map (termAtom registeredOperatorAtom constants [])) dependencies origin])) state equation.body state
      (if FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) hypotheses
       then .symbol "None" else result constants needle left right type hypotheses dependencies) := by
  let before := environment (.expression [.symbol "Some", variableAtom registeredOperatorAtom needle])
    (.expression [.symbol "Some", Transitivity.theoremValue constants [] type left right
      (hypotheses.map (termAtom registeredOperatorAtom constants [])) dependencies origin])
  let premises := [("origin", origin), ("deps", Premises.keys dependencies),
    ("conclusion", termAtom registeredOperatorAtom constants [] (CanonicalTerm.equalityDB type left right)),
    ("hyps", Premises.keys (hypotheses.map (termAtom registeredOperatorAtom constants []))),
    ("type", typeAtom registeredOperatorAtom needle.ty), ("name", nameAtom needle.name)] ++ before
  let binder := ("binder", variableAtom registeredOperatorAtom needle) :: premises
  let operands := [("right", termAtom registeredOperatorAtom constants [] right),
    ("left", termAtom registeredOperatorAtom constants [] left)] ++ binder
  rw [shape]
  apply case_returns program before premises state state state _
    (.expression [.expression [.symbol "Some", variableAtom registeredOperatorAtom needle],
      .expression [.symbol "Some", Transitivity.theoremValue constants [] type left right
        (hypotheses.map (termAtom registeredOperatorAtom constants [])) dependencies origin]])
    selected _ _ outerCases (read_cases_encoded outerCases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["variable", "premise"]
  · simp [outerCases, premises, before, environment, Transitivity.theoremValue, variableAtom,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold selected
    apply let_returns program premises binder state state state (.var "binder") _ guardBody
      (variableAtom registeredOperatorAtom needle) _
    · apply binary_constructor_returns program premises state state state "HOL:Free" (.var "name") (.var "type")
        (nameAtom needle.name) (typeAtom registeredOperatorAtom needle.ty) (by decide) (by decide)
      · simpa [premises, applySubst, Subst.lookup] using variable_returns program premises state "name"
      · simpa [premises, applySubst, Subst.lookup] using variable_returns program premises state "type"
    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, binder, premises, before, environment, Subst.lookup]
    · unfold guardBody
      apply if_returns program binder state state state _
        (boolean (FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) hypotheses)) _ _ _
      · exact FreeVariables.Hypotheses.authored_free_in_return registeredOperatorAtom constants []
          (variableAtom registeredOperatorAtom needle) hypotheses binder state "binder" "hyps"
          (by simp [binder, applySubst, Subst.lookup]) (by simp [binder, premises, applySubst, Subst.lookup])
      · cases occurs : FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) hypotheses
        · simp only [boolean, Bool.false_eq_true, ↓reduceIte]
          apply case_returns program binder operands state state state _
            (.expression [.symbol "Some", .expression [.symbol "HOL:Equation",
              termAtom registeredOperatorAtom constants [] left, termAtom registeredOperatorAtom constants [] right]])
            resultBody _ _ innerCases (read_cases_encoded innerCases)
          · exact Equality.authored_equality_view_return constants binder state [] left right type equalityIdentity "conclusion"
              (by simp [binder, premises, applySubst, Subst.lookup])
          · simp [innerCases, operands, binder, premises, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · unfold resultBody result
            have leftClosed : (DBTerm.abs needle.ty (DBTerm.closeFreeAt needle 0 left)).inferType [] =
                some (Ty.function needle.ty type) := by
              have closed : (DBTerm.closeFreeAt needle 0 left).inferType [needle.ty] = some type := by
                simpa using DBTerm.inferType_closeFreeAt needle left [] leftTyped
              simp [DBTerm.inferType, closed]
            have rightClosed : (DBTerm.abs needle.ty (DBTerm.closeFreeAt needle 0 right)).inferType [] =
                some (Ty.function needle.ty type) := by
              have closed : (DBTerm.closeFreeAt needle 0 right).inferType [needle.ty] = some type := by
                simpa using DBTerm.inferType_closeFreeAt needle right [] rightTyped
              simp [DBTerm.inferType, closed]
            apply Equality.authored_theorem_equality_computed_return constants operands state []
              (.abs needle.ty (DBTerm.closeFreeAt needle 0 left)) (.abs needle.ty (DBTerm.closeFreeAt needle 0 right))
              (Ty.function needle.ty type) leftClosed rightClosed equalityIdentity
              (Premises.keys (hypotheses.map (termAtom registeredOperatorAtom constants [])))
              (Premises.keys dependencies) (.symbol "ABS")
            · simpa [operands, binder, premises, applySubst, Subst.lookup] using variable_returns program operands state "hyps"
            · simp only [termAtom]
              apply binary_constructor_returns program operands state state state "HOL:Lam" (.var "type") _ _ _ (by decide) (by decide)
              · simpa [operands, binder, premises, applySubst, Subst.lookup] using variable_returns program operands state "type"
              · exact authored_abstract_computed_return world constants needle needleFormed left [] type leftFormed leftTyped
                  operands state (.var "binder") (.grounded (.int 0)) (.var "left")
                  (by simpa [operands, binder, applySubst, Subst.lookup] using variable_returns program operands state "binder")
                  (grounded_returns program operands state _)
                  (by simpa [operands, applySubst, Subst.lookup] using variable_returns program operands state "left")
            · simp only [termAtom]
              apply binary_constructor_returns program operands state state state "HOL:Lam" (.var "type") _ _ _ (by decide) (by decide)
              · simpa [operands, binder, premises, applySubst, Subst.lookup] using variable_returns program operands state "type"
              · exact authored_abstract_computed_return world constants needle needleFormed right [] type rightFormed rightTyped
                  operands state (.var "binder") (.grounded (.int 0)) (.var "right")
                  (by simpa [operands, binder, applySubst, Subst.lookup] using variable_returns program operands state "binder")
                  (grounded_returns program operands state _)
                  (by simpa [operands, applySubst, Subst.lookup] using variable_returns program operands state "right")
            · simpa [operands, binder, premises, applySubst, Subst.lookup] using variable_returns program operands state "deps"
            · exact symbol_returns program operands state "ABS"
        · simp only [boolean, ↓reduceIte, BEq.rfl]
          exact symbol_returns program binder state "None"

/-- Actual abstraction runs both argument occurrences, retains exact metadata,
and either closes both checked operands or refuses the hypothesis capture. -/
theorem authored_abs_computed_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (left right : DBTerm) (type : Ty)
    (leftFormed : AnnotationsFormed world.signature left) (rightFormed : AnnotationsFormed world.signature right)
    (leftTyped : left.inferType [] = some type) (rightTyped : right.inferType [] = some type)
    (hypotheses : List DBTerm) (dependencies : List Atom) (origin : Atom)
    (bindings : Subst) (state : State) (variableExpr premiseExpr : Atom)
    (variableReturned : PureReturns program bindings state variableExpr state
      (.expression [.symbol "Some", variableAtom registeredOperatorAtom needle]))
    (premiseReturned : PureReturns program bindings state premiseExpr state
      (.expression [.symbol "Some", Transitivity.theoremValue constants [] type left right
        (hypotheses.map (termAtom registeredOperatorAtom constants [])) dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:abs", variableExpr, premiseExpr]) state
      (if FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) hypotheses
       then .symbol "None" else result constants needle left right type hypotheses dependencies) :=
  authored_binary_call_returns program bindings (environment _ _) state state state state "hol-light:abs"
    variableExpr premiseExpr _ _ equation.body _ (by decide) (by decide) (by decide) (by decide) (by decide)
    variableReturned premiseReturned (clause _ _)
    (body_returns world constants equalityIdentity needle needleFormed left right type leftFormed rightFormed
      leftTyped rightTyped hypotheses dependencies origin state) (by decide)

end Primitive

namespace Dispatcher

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:infer"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def selected : Atom := .expression [.symbol "hol-light:abs",
  .expression [.symbol "hol-light:read", .var "state", .var "variable"],
  .expression [.symbol "hol-light:known", .var "state", .var "premise"]]
private def environment (source request : Atom) : Subst := [("request", request), ("state", source)]
private theorem shape : equation.body = .expression [.symbol "case", .var "request",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (source request : Atom) : clauses program "hol-light:infer" [source, request] =
    [.evaluate (environment source request) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:infer") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "request"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem selection (source value premise : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "ABS", value, premise]))
      (.expression [.symbol "ABS", value, premise]) cases =
      some ([("premise", premise), ("variable", value)] ++
        environment source (.expression [.symbol "ABS", value, premise]), selected) := by
  have initial : cases = (cases[0]'(by decide)) :: (cases[1]'(by decide)) :: (cases[2]'(by decide)) ::
      (.expression [.symbol "ABS", .var "variable", .var "premise"], selected) :: cases.drop 4 := by decide
  have first : (cases[0]'(by decide)).1 = .expression [.symbol "REFL", .var "term"] := by decide
  have second : (cases[1]'(by decide)).1 = .expression [.symbol "TRANS", .var "first", .var "second"] := by decide
  have third : (cases[2]'(by decide)).1 = .expression [.symbol "MK_COMB", .var "first", .var "second"] := by decide
  rw [initial]
  simp only [SpaceSemantics.selectCase, first, second, third]
  simp [environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- ABS reads the typed variable in its retained signature and obtains the
premise from the real first-match cache lookup. Caller-supplied theorem data
does not replace that lookup. Hypothesis capture returns the source refusal. -/
theorem authored_infer_abs_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (resolved : TermReading.SourceResolved world.signature (.var needle.name needle.ty))
    (left right : DBTerm) (type : Ty)
    (leftFormed : AnnotationsFormed world.signature left) (rightFormed : AnnotationsFormed world.signature right)
    (leftTyped : left.inferType [] = some type) (rightTyped : right.inferType [] = some type)
    (hypotheses : List DBTerm) (dependencies : List Atom) (origin axioms receipts key : Atom)
    (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Transitivity.theoremValue constants [] type left right
      (hypotheses.map (termAtom registeredOperatorAtom constants [])) dependencies origin))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ABS", TermReading.sourceAtom (.var needle.name needle.ty), key]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (if FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) hypotheses
       then .symbol "None" else Primitive.result constants needle left right type hypotheses dependencies) := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let rawVariable := TermReading.sourceAtom (.var needle.name needle.ty)
  let request := Atom.expression [.symbol "ABS", rawVariable, key]
  let before := environment source request
  let bound := [("premise", key), ("variable", rawVariable)] ++ before
  apply authored_variable_call_returns program bindings before state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request
  · rw [shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ cases (read_cases_encoded cases)
    · exact variable_returns program before state "request"
    · exact selection source rawVariable key
    · unfold selected
      apply Primitive.authored_abs_computed_return world constants equalityIdentity needle needleFormed left right type
        leftFormed rightFormed leftTyped rightTyped hypotheses dependencies origin bound state
      · simpa only [SourceTerm.toDB, boundIndex, termAtom, variableAtom] using
          InferenceExecution.authored_state_read_return world table origins constants (.var needle.name needle.ty)
            resolved (by simpa [SourceTerm.toDB, boundIndex] using (AnnotationsFormed.free needleFormed))
            needle.ty (by simp [SourceTerm.inferType]) bound state axioms receipts cache
            "state" "variable" (by simp [bound, before, environment, source, applySubst, Subst.lookup])
            (by simp [bound, rawVariable, applySubst, Subst.lookup])
      · simpa only [found, Lookup.answer] using
          ProofLookup.authored_known_return bound state (OperatorTable.tableAtom table.operators origins)
            (DeclarationTable.tableAtom table constants) axioms receipts key cache "state" "premise"
            (by simp [bound, before, environment, source, applySubst, Subst.lookup])
            (by simp [bound, applySubst, Subst.lookup])

end Dispatcher

/-- An admitted cache premise produces the shared ABS derivation through the
actual dispatcher. Freshness is the source rule's condition; the source
hypothesis and dependency occurrence lists are retained without a union or
deduplication. This is rule preservation, not cache-history soundness. -/
theorem authored_abs_shared_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (resolved : TermReading.SourceResolved world.signature (.var needle.name needle.ty))
    (policy : AxiomPolicy) (input : Theorem) (left right : CanonicalTerm)
    (inputDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) input)
    (sameType : left.ty = right.ty)
    (equalityShape : input.sequent.concl.term = CanonicalTerm.equalityDB left.ty left.term right.term)
    (fresh : ¬ FreeInHypotheses needle input.sequent.hyp)
    (leftFormed : AnnotationsFormed world.signature left.term)
    (rightFormed : AnnotationsFormed world.signature right.term)
    (hypotheses : List CanonicalTerm) (dependencies : List Sequent)
    (hypothesisSupport : hypotheses.toFinset = input.sequent.hyp)
    (dependencySupport : dependencies.toFinset = input.axioms)
    (hypothesesFormed : ∀ term ∈ hypotheses, AnnotationsFormed world.signature term.term)
    (axiomAtom : Sequent → Atom) (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] input.sequent.concl.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) (dependencies.map axiomAtom) origin))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ABS", TermReading.sourceAtom (.var needle.name needle.ty), key]) :
    ∃ out : Theorem, InferenceRequest.Semantics (.abs needle input) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.sequent.hyp = input.sequent.hyp ∧ out.axioms = input.axioms ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", Representation.theoremAtom constants [] out.sequent.concl.term
          (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) (dependencies.map axiomAtom) (.symbol "ABS")]) ∧
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)).toFinset =
        out.sequent.hyp.image (TheoremMetadata.hypothesisAtom constants) ∧
      (dependencies.map axiomAtom).toFinset = out.axioms.image axiomAtom := by
  let equality := CanonicalTerm.equalityOfSameType (left.abstractFree needle) (right.abstractFree needle)
    (by simp [CanonicalTerm.abstractFree, sameType])
  let out := Theorem.preserveAxiomsResult input input.sequent.hyp equality
  have semantics : InferenceRequest.Semantics (.abs needle input) out := by
    refine ⟨fresh, left, right, left.abstractFree needle, right.abstractFree needle, equality,
      ⟨sameType, equalityShape⟩, rfl, rfl, ?_, rfl, rfl, rfl⟩
    exact CanonicalTerm.equalityOfSameType_semantics _ _ _
  have derives := InferenceRequest.Semantics.shared_derivation policy semantics (by
    intro premise member
    simp only [InferenceRequest.premises, List.mem_singleton] at member
    cases member
    exact inputDerives)
  have notOccurs : FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle)
      (hypotheses.map (·.term)) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro occurs
    apply fresh
    rw [← hypothesisSupport]
    exact (FreeVariables.Hypotheses.canonical_guard_iff world needle needleFormed hypotheses hypothesesFormed).mp occurs
  have rightTyped : right.term.inferType [] = some left.ty := by simpa only [sameType] using right.checked
  have encodedHypotheses : ((hypotheses.map (·.term)).map (termAtom registeredOperatorAtom constants [])) =
      hypotheses.map (TheoremMetadata.hypothesisAtom constants) := by
    simp only [List.map_map]
    rfl
  have cacheFound : cache.lookup key = some (Transitivity.theoremValue constants [] left.ty left.term right.term
      ((hypotheses.map (·.term)).map (termAtom registeredOperatorAtom constants [])) (dependencies.map axiomAtom) origin) := by
    simpa only [equalityShape, Transitivity.theoremValue, encodedHypotheses] using found
  have returned := Dispatcher.authored_infer_abs_return world table origins constants equalityIdentity needle needleFormed
    resolved left.term right.term left.ty leftFormed rightFormed left.checked rightTyped
    (hypotheses.map (·.term)) (dependencies.map axiomAtom) origin axioms receipts key cache cacheFound
    bindings state stateKey requestKey stateCaptured requestCaptured
  refine ⟨out, semantics, derives, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [notOccurs, Bool.false_eq_true, ↓reduceIte, Primitive.result, out,
      Theorem.preserveAxiomsResult, equality, CanonicalTerm.equalityOfSameType, CanonicalTerm.abstractFree,
      encodedHypotheses] using returned
  · simp only [out, Theorem.preserveAxiomsResult, List.toFinset_map, hypothesisSupport]
  · simp only [out, Theorem.preserveAxiomsResult, List.toFinset_map, dependencySupport]

namespace Controls

private def needle : SourceVar := ⟨Name.global "p", Ty.bool⟩
private theorem boolean_formed : TypeFormed SourceProfile.primitiveContext.signature Ty.bool :=
  DefinitionAdapters.ContextControls.boolean_formed.mono
    (DefinitionAdapters.ContextControls.core_includes.trans
      (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))
private def captured (hypotheses : List DBTerm) : Subst :=
  [("variable", .expression [.symbol "Some", variableAtom registeredOperatorAtom needle]),
   ("premise", .expression [.symbol "Some", Transitivity.theoremValue DeclarationTable.primitiveIdentity []
      Ty.bool (.free needle) (.free needle)
      (hypotheses.map (termAtom registeredOperatorAtom DeclarationTable.primitiveIdentity [])) [] (.symbol "REFL")])]

private theorem run (state : State) (hypotheses : List DBTerm) :
    PureReturns program (captured hypotheses) state
      (.expression [.symbol "hol-light:abs", .var "variable", .var "premise"]) state
      (if FreeVariables.Hypotheses.occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) hypotheses
       then .symbol "None" else Primitive.result DeclarationTable.primitiveIdentity needle
         (.free needle) (.free needle) Ty.bool hypotheses []) := by
  apply Primitive.authored_abs_computed_return SourceProfile.primitiveContext
    DeclarationTable.primitiveIdentity rfl needle boolean_formed (.free needle) (.free needle)
    Ty.bool (.free boolean_formed) (.free boolean_formed) (by simp [DBTerm.inferType, needle])
    (by simp [DBTerm.inferType, needle]) hypotheses [] (.symbol "REFL")
    (captured hypotheses) state (.var "variable") (.var "premise")
  · simpa [captured, applySubst, Subst.lookup] using variable_returns program (captured hypotheses) state "variable"
  · simpa [captured, applySubst, Subst.lookup] using variable_returns program (captured hypotheses) state "premise"

/-- The executed rule closes p in both operands, with no hypotheses or
axiom dependencies. Its Boolean carrier comes from the registered profile. -/
theorem closes_reflexive_variable (state : State) :
    PureReturns program (captured []) state
      (.expression [.symbol "hol-light:abs", .var "variable", .var "premise"]) state
      (Primitive.result DeclarationTable.primitiveIdentity needle (.free needle) (.free needle) Ty.bool [] []) := by
  simpa [FreeVariables.Hypotheses.occurs] using run state []

/-- The same executed rule refuses to close p when p remains in a hypothesis.
Supplying a matching equality record does not bypass the side condition. -/
theorem captured_hypothesis_refused (state : State) :
    PureReturns program (captured [.free needle]) state
      (.expression [.symbol "hol-light:abs", .var "variable", .var "premise"]) state (.symbol "None") := by
  have occurs : FreeVariables.Hypotheses.occurs registeredOperatorAtom
      (variableAtom registeredOperatorAtom needle) [.free needle] = true := by
    simp [FreeVariables.Hypotheses.occurs, FreeVariables.freeAtoms]
  simpa only [occurs, ↓reduceIte] using run state [.free needle]

end Controls

end Mettapedia.Languages.HOLLight.MeTTa.Abstraction
