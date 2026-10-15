import Mettapedia.Languages.HOLLight.MeTTa.Transitivity

/-!
# Authored HOL application congruence

The source operation recovers both equality operands before constructing its
two applications. Shared STT typing justifies the applications; the retained
source computes their equality, hypothesis union and dependency union.
Premise admission remains a separate proof-cache history obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Application

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State)
open Representation (registeredOperatorAtom termAtom)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:mk-comb"))[0]'(by decide)

private def resultBody : Atom := .expression [.symbol "hol-light:theorem-eq",
  .expression [.symbol "hol-light:union", .var "hyps1", .var "hyps2"],
  .expression [.symbol "HOL:App", .var "fn1", .var "arg1"],
  .expression [.symbol "HOL:App", .var "fn2", .var "arg2"],
  .expression [.symbol "hol-light:union", .var "deps1", .var "deps2"], .symbol "MK_COMB"]

private def innerCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Equation", .var "fn1", .var "fn2"]],
      .expression [.symbol "Some", .expression [.symbol "HOL:Equation", .var "arg1", .var "arg2"]]], resultBody),
    (.var "malformed", .symbol "None")]
private def innerBody : Atom := .expression [.symbol "case",
  .expression [.expression [.symbol "hol-light:dest-eq", .var "conclusion1"],
    .expression [.symbol "hol-light:dest-eq", .var "conclusion2"]],
  .expression (innerCases.map fun row => .expression [row.1, row.2])]
private def outerCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps1",
        .var "conclusion1", .var "deps1", .var "origin1"]],
      .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps2",
        .var "conclusion2", .var "deps2", .var "origin2"]]], innerBody),
    (.var "malformed", .symbol "None")]
private def environment (first second : Atom) : Subst := [("second", second), ("first", first)]

private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "first", .var "second"],
    .expression (outerCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (first second : Atom) : clauses program "hol-light:mk-comb" [first, second] =
    [.evaluate (environment first second) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:mk-comb") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "first", .var "second"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def operands (constants : Const → Atom) (positions : List Ty)
    (functionType argumentType : Ty) (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) : Subst :=
  [("arg2", termAtom registeredOperatorAtom constants positions argumentRight),
    ("arg1", termAtom registeredOperatorAtom constants positions argumentLeft),
    ("fn2", termAtom registeredOperatorAtom constants positions functionRight),
    ("fn1", termAtom registeredOperatorAtom constants positions functionLeft),
    ("origin2", origin2), ("deps2", Premises.keys deps2),
    ("conclusion2", termAtom registeredOperatorAtom constants positions
      (CanonicalTerm.equalityDB argumentType argumentLeft argumentRight)), ("hyps2", Premises.keys hyps2),
    ("origin1", origin1), ("deps1", Premises.keys deps1),
    ("conclusion1", termAtom registeredOperatorAtom constants positions
      (CanonicalTerm.equalityDB functionType functionLeft functionRight)), ("hyps1", Premises.keys hyps1)] ++
  environment
    (.expression [.symbol "Some", Transitivity.theoremValue constants positions functionType
      functionLeft functionRight hyps1 deps1 origin1])
    (.expression [.symbol "Some", Transitivity.theoremValue constants positions argumentType
      argumentLeft argumentRight hyps2 deps2 origin2])

private theorem body_return_of_result (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) (positions : List Ty) (functionType argumentType : Ty)
    (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 answer : Atom)
    (resultReturned : PureReturns program
      (operands constants positions functionType argumentType functionLeft functionRight argumentLeft argumentRight
        hyps1 hyps2 deps1 deps2 origin1 origin2) state resultBody state answer) :
    PureReturns program (environment
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions functionType
        functionLeft functionRight hyps1 deps1 origin1])
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions argumentType
        argumentLeft argumentRight hyps2 deps2 origin2])) state equation.body state answer := by
  let before := environment
    (.expression [.symbol "Some", Transitivity.theoremValue constants positions functionType
      functionLeft functionRight hyps1 deps1 origin1])
    (.expression [.symbol "Some", Transitivity.theoremValue constants positions argumentType
      argumentLeft argumentRight hyps2 deps2 origin2])
  let premises : Subst := [("origin2", origin2), ("deps2", Premises.keys deps2),
    ("conclusion2", termAtom registeredOperatorAtom constants positions
      (CanonicalTerm.equalityDB argumentType argumentLeft argumentRight)), ("hyps2", Premises.keys hyps2),
    ("origin1", origin1), ("deps1", Premises.keys deps1),
    ("conclusion1", termAtom registeredOperatorAtom constants positions
      (CanonicalTerm.equalityDB functionType functionLeft functionRight)), ("hyps1", Premises.keys hyps1)] ++ before
  let bound := operands constants positions functionType argumentType functionLeft functionRight argumentLeft argumentRight
    hyps1 hyps2 deps1 deps2 origin1 origin2
  rw [shape]
  apply case_returns program before premises state state state _
    (.expression [.expression [.symbol "Some", Transitivity.theoremValue constants positions functionType
      functionLeft functionRight hyps1 deps1 origin1], .expression [.symbol "Some",
      Transitivity.theoremValue constants positions argumentType argumentLeft argumentRight hyps2 deps2 origin2]])
    innerBody _ _ outerCases (read_cases_encoded outerCases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["first", "second"]
  · simp [outerCases, premises, before, environment, Transitivity.theoremValue, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold innerBody
    apply case_returns program premises bound state state state _ (.expression
      [.expression [.symbol "Some", .expression [.symbol "HOL:Equation",
        termAtom registeredOperatorAtom constants positions functionLeft,
        termAtom registeredOperatorAtom constants positions functionRight]],
       .expression [.symbol "Some", .expression [.symbol "HOL:Equation",
        termAtom registeredOperatorAtom constants positions argumentLeft,
        termAtom registeredOperatorAtom constants positions argumentRight]]])
      resultBody _ _ innerCases (read_cases_encoded innerCases)
    · refine .step (u := ({ state := state, control := .arguments premises .data _ [] 0 } : Configuration))
        (step_transition rfl) ?_
      apply PureData.arguments_return
      refine .cons ?_ (.cons ?_ .nil)
      · exact Equality.authored_equality_view_return constants premises state positions functionLeft functionRight functionType
          equalityIdentity "conclusion1" (by simp [premises, applySubst, Subst.lookup])
      · exact Equality.authored_equality_view_return constants premises state positions argumentLeft argumentRight argumentType
          equalityIdentity "conclusion2" (by simp [premises, applySubst, Subst.lookup])
    · simp [innerCases, bound, operands, premises, before, environment, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · exact resultReturned

private theorem body_returns (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) (positions : List Ty) (domain codomain : Ty)
    (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (functionLeftChecked : functionLeft.inferType positions = some (.function domain codomain))
    (functionRightChecked : functionRight.inferType positions = some (.function domain codomain))
    (argumentLeftChecked : argumentLeft.inferType positions = some domain)
    (argumentRightChecked : argumentRight.inferType positions = some domain)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) :
    PureReturns program (environment
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions (.function domain codomain)
        functionLeft functionRight hyps1 deps1 origin1])
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions domain
        argumentLeft argumentRight hyps2 deps2 origin2])) state equation.body state
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions codomain
        (.app functionLeft argumentLeft) (.app functionRight argumentRight)
        (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "MK_COMB")]) := by
  apply body_return_of_result constants equalityIdentity state positions (.function domain codomain) domain
    functionLeft functionRight argumentLeft argumentRight hyps1 hyps2 deps1 deps2 origin1 origin2
  let bound := operands constants positions (.function domain codomain) domain
    functionLeft functionRight argumentLeft argumentRight hyps1 hyps2 deps1 deps2 origin1 origin2
  unfold resultBody Transitivity.theoremValue
  apply Equality.authored_theorem_equality_computed_return constants bound state positions
    (.app functionLeft argumentLeft) (.app functionRight argumentRight) codomain
    (DBTerm.inferType_app_of functionLeftChecked argumentLeftChecked)
    (DBTerm.inferType_app_of functionRightChecked argumentRightChecked) equalityIdentity
    (Premises.keys (Transitivity.union hyps1 hyps2)) (Premises.keys (Transitivity.union deps1 deps2)) (.symbol "MK_COMB")
  · exact ListOperations.Union.authored_union_return bound state hyps1 hyps2 "hyps1" "hyps2"
      (by simp [bound, operands, applySubst, Subst.lookup]) (by simp [bound, operands, applySubst, Subst.lookup])
  · simpa [bound, operands, termAtom, applySubst, Subst.lookup] using
      binary_constructor_returns program bound state state state "HOL:App" (.var "fn1") (.var "arg1") _ _
        (by decide) (by decide) (variable_returns program bound state "fn1") (variable_returns program bound state "arg1")
  · simpa [bound, operands, termAtom, applySubst, Subst.lookup] using
      binary_constructor_returns program bound state state state "HOL:App" (.var "fn2") (.var "arg2") _ _
        (by decide) (by decide) (variable_returns program bound state "fn2") (variable_returns program bound state "arg2")
  · exact ListOperations.Union.authored_union_return bound state deps1 deps2 "deps1" "deps2"
      (by simp [bound, operands, applySubst, Subst.lookup]) (by simp [bound, operands, applySubst, Subst.lookup])
  · exact symbol_returns program bound state "MK_COMB"

/-- Two computed equality premises enter the actual application operation.
Both ordered source unions and the ordinary application typing are retained. -/
theorem authored_mk_comb_computed_return (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (domain codomain : Ty)
    (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (functionLeftChecked : functionLeft.inferType positions = some (.function domain codomain))
    (functionRightChecked : functionRight.inferType positions = some (.function domain codomain))
    (argumentLeftChecked : argumentLeft.inferType positions = some domain)
    (argumentRightChecked : argumentRight.inferType positions = some domain)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 firstExpression secondExpression : Atom)
    (firstReturned : PureReturns program bindings state firstExpression state (.expression [.symbol "Some",
      Transitivity.theoremValue constants positions (.function domain codomain) functionLeft functionRight hyps1 deps1 origin1]))
    (secondReturned : PureReturns program bindings state secondExpression state (.expression [.symbol "Some",
      Transitivity.theoremValue constants positions domain argumentLeft argumentRight hyps2 deps2 origin2])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:mk-comb", firstExpression, secondExpression]) state
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions codomain
        (.app functionLeft argumentLeft) (.app functionRight argumentRight)
        (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "MK_COMB")]) :=
  authored_binary_call_returns program bindings (environment _ _) state state state state "hol-light:mk-comb"
    firstExpression secondExpression _ _ equation.body _ (by decide) (by decide) (by decide) (by decide)
    (by decide) firstReturned secondReturned (clause _ _)
    (body_returns constants equalityIdentity state positions domain codomain functionLeft functionRight
      argumentLeft argumentRight functionLeftChecked functionRightChecked argumentLeftChecked argumentRightChecked
      hyps1 hyps2 deps1 deps2 origin1 origin2) (by decide)

/-- A missing first premise is refused even if the second lookup returns
arbitrary theorem-shaped data. Both source argument occurrences still run. -/
theorem authored_mk_comb_missing_computed_return (bindings : Subst) (state : State)
    (firstExpression secondExpression second : Atom)
    (firstReturned : PureReturns program bindings state firstExpression state (.symbol "None"))
    (secondReturned : PureReturns program bindings state secondExpression state second) :
    PureReturns program bindings state (.expression [.symbol "hol-light:mk-comb", firstExpression, secondExpression])
      state (.symbol "None") := by
  let before := environment (.symbol "None") second
  let bound := ("malformed", Atom.expression [.symbol "None", second]) :: before
  apply authored_binary_call_returns program bindings before state state state state "hol-light:mk-comb"
    firstExpression secondExpression _ _ equation.body _ (by decide) (by decide) (by decide) (by decide)
    (by decide) firstReturned secondReturned (clause _ _) _ (by decide)
  rw [shape]
  apply case_returns program before bound state state state _ (.expression [.symbol "None", second])
    (.symbol "None") _ _ outerCases (read_cases_encoded outerCases)
  · simpa [before, environment, applySubst, Subst.lookup] using tuple_variables_return program before state ["first", "second"]
  · simp [outerCases, before, bound, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · exact symbol_returns program bound state "None"

/-- The conclusion earned by the source operation is Boolean in shared STT;
its applications are checked at the existing function domain and codomain. -/
theorem application_conclusion_typed (positions : List Ty) (domain codomain : Ty)
    (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (functionLeftChecked : functionLeft.inferType positions = some (.function domain codomain))
    (functionRightChecked : functionRight.inferType positions = some (.function domain codomain))
    (argumentLeftChecked : argumentLeft.inferType positions = some domain)
    (argumentRightChecked : argumentRight.inferType positions = some domain) :
    (CanonicalTerm.equalityDB codomain (.app functionLeft argumentLeft)
      (.app functionRight argumentRight)).inferType positions = some Ty.bool :=
  Equality.equality_result_typed positions _ _ codomain
    (DBTerm.inferType_app_of functionLeftChecked argumentLeftChecked)
    (DBTerm.inferType_app_of functionRightChecked argumentRightChecked)

end Mettapedia.Languages.HOLLight.MeTTa.Application
