import Mettapedia.Languages.HOLLight.MeTTa.Transitivity

/-!
# Equality modus ponens executed by the authored checker

The retained operation inspects its actual equality premise, compares the
left operand with the second conclusion, and checks the right carrier.
Registered identities and shared STT typing justify both source guards.
Ordered hypothesis and dependency unions are computed by the source library.
These execution laws do not authorize arbitrary proof-cache insertions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.EqualityModusPonens

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom theoremAtom)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:eq-mp"))[0]'(by decide)

private def resultBody : Atom := .expression [.symbol "Some", .expression [.symbol "HOL:Thm",
  .expression [.symbol "hol-light:union", .var "hyps1", .var "hyps2"], .var "right",
  .expression [.symbol "hol-light:union", .var "deps1", .var "deps2"], .symbol "EQ_MP"]]
private def booleanGuard : Atom := .expression [.symbol "==",
  .expression [.symbol "hol-light:term-type", .var "right"],
  .expression [.symbol "Some", .expression [.symbol "hol-light:bool"]]]
private def selected : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "left", .var "conclusion"],
  .expression [.symbol "if", booleanGuard, resultBody, .symbol "None"], .symbol "None"]
private def innerCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .expression [.symbol "HOL:Equation", .var "left", .var "right"]], selected),
   (.var "malformed", .symbol "None")]
private def innerBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:dest-eq", .var "equation"],
  .expression (innerCases.map fun row => .expression [row.1, row.2])]
private def outerCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps1",
      .var "equation", .var "deps1", .var "origin1"]],
    .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps2",
      .var "conclusion", .var "deps2", .var "origin2"]]], innerBody),
   (.var "malformed", .symbol "None")]
private def environment (first second : Atom) : Subst := [("second", second), ("first", first)]
private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "first", .var "second"],
    .expression (outerCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (first second : Atom) : clauses program "hol-light:eq-mp" [first, second] =
    [.evaluate (environment first second) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:eq-mp") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "first", .var "second"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Exact metadata and conclusion produced when both source guards pass. -/
def result (constants : Const → Atom) (positions : List Ty) (right : DBTerm)
    (hyps1 hyps2 deps1 deps2 : List Atom) : Atom :=
  .expression [.symbol "Some", theoremAtom constants positions right
    (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "EQ_MP")]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) (positions : List Ty) (rightType equalityType : Ty) (left right conclusion : DBTerm)
    (rightChecked : right.inferType positions = some rightType)
    (rightTypeFormed : SignatureFormation.TypeFormed world.signature rightType)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left)
    (conclusionFormed : SignatureFormation.AnnotationsFormed world.signature conclusion)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) :
    PureReturns program (environment
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1])
      (.expression [.symbol "Some", theoremAtom constants positions conclusion hyps2 deps2 origin2])) state equation.body state
      (if DBTerm.same left conclusion then
        if Ty.same rightType Ty.bool then result constants positions right hyps1 hyps2 deps1 deps2 else .symbol "None"
       else .symbol "None") := by
  let before := environment
    (.expression [.symbol "Some", Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1])
    (.expression [.symbol "Some", theoremAtom constants positions conclusion hyps2 deps2 origin2])
  let premises : Subst := [("origin2", origin2), ("deps2", Premises.keys deps2),
    ("conclusion", termAtom registeredOperatorAtom constants positions conclusion), ("hyps2", Premises.keys hyps2),
    ("origin1", origin1), ("deps1", Premises.keys deps1),
    ("equation", termAtom registeredOperatorAtom constants positions (CanonicalTerm.equalityDB equalityType left right)),
    ("hyps1", Premises.keys hyps1)] ++ before
  let bound := [("right", termAtom registeredOperatorAtom constants positions right),
    ("left", termAtom registeredOperatorAtom constants positions left)] ++ premises
  rw [shape]
  apply case_returns program before premises state state state _
    (.expression [.expression [.symbol "Some", Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1],
      .expression [.symbol "Some", theoremAtom constants positions conclusion hyps2 deps2 origin2]])
    innerBody _ _ outerCases (read_cases_encoded outerCases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["first", "second"]
  · simp [outerCases, premises, before, environment, Transitivity.theoremValue,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold innerBody
    apply case_returns program premises bound state state state _
      (.expression [.symbol "Some", .expression [.symbol "HOL:Equation",
        termAtom registeredOperatorAtom constants positions left, termAtom registeredOperatorAtom constants positions right]])
      selected _ _ innerCases (read_cases_encoded innerCases)
    · exact Equality.authored_equality_view_return constants premises state positions left right equalityType
        equalityIdentity "equation" (by simp [premises, applySubst, Subst.lookup])
    · simp [innerCases, bound, premises, before, environment, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold selected
      apply if_returns program bound state state state _ (boolean (DBTerm.same left conclusion)) _ _ _
      · exact Equality.authored_term_equality_test_return world constants identified bound state positions left conclusion
          leftFormed conclusionFormed "left" "conclusion"
          (by simp [bound, applySubst, Subst.lookup]) (by simp [bound, premises, applySubst, Subst.lookup])
      · cases DBTerm.same left conclusion
        · simp only [Bool.false_eq_true, ↓reduceIte, boolean]
          exact symbol_returns program bound state "None"
        · simp only [↓reduceIte, boolean, BEq.rfl]
          apply if_returns program bound state state state booleanGuard (boolean (Ty.same rightType Ty.bool)) _ _ _
          · exact Equality.authored_boolean_test_return world constants bound state positions right rightType
              rightChecked rightTypeFormed booleanFormed "right" (by simp [bound, applySubst, Subst.lookup])
          · cases Ty.same rightType Ty.bool
            · simp only [Bool.false_eq_true, ↓reduceIte, boolean]
              exact symbol_returns program bound state "None"
            · simp only [↓reduceIte, boolean, BEq.rfl]
              unfold resultBody result
              apply unary_constructor_of_returns program bound state state "Some" _ _ (by decide) (by decide)
              apply PureData.constructor_return program bound state "HOL:Thm" _ _ (by decide) (by decide)
              refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
              · exact ListOperations.Union.authored_union_return bound state hyps1 hyps2 "hyps1" "hyps2"
                  (by simp [bound, premises, applySubst, Subst.lookup]) (by simp [bound, premises, applySubst, Subst.lookup])
              · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "right"
              · exact ListOperations.Union.authored_union_return bound state deps1 deps2 "deps1" "deps2"
                  (by simp [bound, premises, applySubst, Subst.lookup]) (by simp [bound, premises, applySubst, Subst.lookup])
              · exact symbol_returns program bound state "EQ_MP"

/-- Equality modus ponens runs both actual argument occurrences and returns
exactly the source result or refusal of its matching and carrier guards. -/
theorem authored_eq_mp_computed_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (rightType equalityType : Ty)
    (left right conclusion : DBTerm) (rightChecked : right.inferType positions = some rightType)
    (rightTypeFormed : SignatureFormation.TypeFormed world.signature rightType)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left)
    (conclusionFormed : SignatureFormation.AnnotationsFormed world.signature conclusion)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 firstExpression secondExpression : Atom)
    (firstReturned : PureReturns program bindings state firstExpression state (.expression [.symbol "Some",
      Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1]))
    (secondReturned : PureReturns program bindings state secondExpression state (.expression [.symbol "Some",
      theoremAtom constants positions conclusion hyps2 deps2 origin2])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:eq-mp", firstExpression, secondExpression]) state
      (if DBTerm.same left conclusion then
        if Ty.same rightType Ty.bool then result constants positions right hyps1 hyps2 deps1 deps2 else .symbol "None"
       else .symbol "None") :=
  authored_binary_call_returns program bindings (environment _ _) state state state state "hol-light:eq-mp"
    firstExpression secondExpression _ _ equation.body _ (by decide) (by decide) (by decide) (by decide)
    (by decide) firstReturned secondReturned (clause _ _)
    (body_returns world constants identified equalityIdentity state positions rightType equalityType left right conclusion
      rightChecked rightTypeFormed booleanFormed leftFormed conclusionFormed hyps1 hyps2 deps1 deps2 origin1 origin2) (by decide)

/-- No first cache premise means refusal, even when the other argument supplies
an arbitrary record. The second occurrence is still evaluated. -/
theorem authored_eq_mp_missing_computed_return (bindings : Subst) (state : State)
    (firstExpression secondExpression second : Atom)
    (firstReturned : PureReturns program bindings state firstExpression state (.symbol "None"))
    (secondReturned : PureReturns program bindings state secondExpression state second) :
    PureReturns program bindings state (.expression [.symbol "hol-light:eq-mp", firstExpression, secondExpression]) state
      (.symbol "None") := by
  let before := environment (.symbol "None") second
  let bound := ("malformed", Atom.expression [.symbol "None", second]) :: before
  apply authored_binary_call_returns program bindings before state state state state "hol-light:eq-mp"
    firstExpression secondExpression _ _ equation.body _ (by decide) (by decide) (by decide) (by decide)
    (by decide) firstReturned secondReturned (clause _ _) _ (by decide)
  rw [shape]
  apply case_returns program before bound state state state _ (.expression [.symbol "None", second])
    (.symbol "None") _ _ outerCases (read_cases_encoded outerCases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["first", "second"]
  · simp [outerCases, before, bound, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · exact symbol_returns program bound state "None"

end Mettapedia.Languages.HOLLight.MeTTa.EqualityModusPonens
