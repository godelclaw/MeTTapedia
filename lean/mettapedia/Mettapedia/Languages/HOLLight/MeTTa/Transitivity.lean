import Mettapedia.Languages.HOLLight.MeTTa.Equality
import Mettapedia.Languages.HOLLight.MeTTa.ListOperations

/-!
# Authored HOL transitivity on retained theorem data

The source operation recovers both equality operands, compares the middle
terms, and constructs its result through the already proved equality helper.
Its finite hypothesis and dependency lists retain their actual source order.
These are execution laws for the helper, not admission of caller-supplied
theorem data to the checked cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Transitivity

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom)

def union (left right : List Atom) : List Atom :=
  left.foldl (fun items item => if item ∈ items then items else item :: items) right

def theoremValue (constants : Const → Atom) (positions : List Ty) (type : Ty)
    (left right : DBTerm) (hypotheses dependencies : List Atom) (origin : Atom) : Atom :=
  Representation.theoremAtom constants positions (CanonicalTerm.equalityDB type left right)
    hypotheses dependencies origin

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:trans"))[0]'(by decide)

private def resultBody : Atom := .expression [.symbol "hol-light:theorem-eq",
  .expression [.symbol "hol-light:union", .var "hyps1", .var "hyps2"], .var "left", .var "right",
  .expression [.symbol "hol-light:union", .var "deps1", .var "deps2"], .symbol "TRANS"]

private def selected : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "middle1", .var "middle2"], resultBody, .symbol "None"]

private def innerCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Equation", .var "left", .var "middle1"]],
      .expression [.symbol "Some", .expression [.symbol "HOL:Equation", .var "middle2", .var "right"]]], selected),
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

private theorem shape : equation.body = .expression [.symbol "case",
    .expression [.var "first", .var "second"],
    .expression (outerCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem clause (first second : Atom) : clauses program "hol-light:trans" [first, second] =
    [.evaluate (environment first second) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:trans") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "first", .var "second"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) :
    PureReturns program
      (environment
        (.expression [.symbol "Some", theoremValue constants positions type left middle1 hyps1 deps1 origin1])
        (.expression [.symbol "Some", theoremValue constants positions type middle2 right hyps2 deps2 origin2]))
      state equation.body state
      (if DBTerm.same middle1 middle2 then
        .expression [.symbol "Some", theoremValue constants positions type left right
          (union hyps1 hyps2) (union deps1 deps2) (.symbol "TRANS")]
       else .symbol "None") := by
  let leftAtom := termAtom registeredOperatorAtom constants positions left
  let firstMiddle := termAtom registeredOperatorAtom constants positions middle1
  let secondMiddle := termAtom registeredOperatorAtom constants positions middle2
  let rightAtom := termAtom registeredOperatorAtom constants positions right
  let firstConclusion := termAtom registeredOperatorAtom constants positions
    (CanonicalTerm.equalityDB type left middle1)
  let secondConclusion := termAtom registeredOperatorAtom constants positions
    (CanonicalTerm.equalityDB type middle2 right)
  let before := environment
    (.expression [.symbol "Some", theoremValue constants positions type left middle1 hyps1 deps1 origin1])
    (.expression [.symbol "Some", theoremValue constants positions type middle2 right hyps2 deps2 origin2])
  let premises : Subst := [("origin2", origin2), ("deps2", Premises.keys deps2),
    ("conclusion2", secondConclusion), ("hyps2", Premises.keys hyps2),
    ("origin1", origin1), ("deps1", Premises.keys deps1),
    ("conclusion1", firstConclusion), ("hyps1", Premises.keys hyps1)] ++ before
  let operands : Subst := [("right", rightAtom), ("middle2", secondMiddle),
    ("middle1", firstMiddle), ("left", leftAtom)] ++ premises
  rw [shape]
  apply case_returns program before premises state state state _
    (.expression [(.expression [.symbol "Some", theoremValue constants positions type left middle1 hyps1 deps1 origin1]),
      (.expression [.symbol "Some", theoremValue constants positions type middle2 right hyps2 deps2 origin2])])
    innerBody _ _ outerCases (read_cases_encoded outerCases)
  · simpa [before, environment, applySubst, Subst.lookup] using
      tuple_variables_return program before state ["first", "second"]
  · simp [outerCases, premises, before, environment, theoremValue, firstConclusion, secondConclusion,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold innerBody
    apply case_returns program premises operands state state state _
      (.expression [.expression [.symbol "Some", .expression [.symbol "HOL:Equation", leftAtom, firstMiddle]],
        .expression [.symbol "Some", .expression [.symbol "HOL:Equation", secondMiddle, rightAtom]]])
      selected _ _ innerCases (read_cases_encoded innerCases)
    · let pending : List Atom := [.expression [.symbol "hol-light:dest-eq", .var "conclusion1"],
        .expression [.symbol "hol-light:dest-eq", .var "conclusion2"]]
      refine .step (u := ({ state := state, control := .arguments premises .data pending [] 0 } : Configuration))
        (step_transition rfl) ?_
      apply PureData.arguments_return
      refine .cons ?_ (.cons ?_ .nil)
      · exact Equality.authored_equality_view_return constants premises state positions left middle1 type
          equalityIdentity "conclusion1" (by simp [premises, firstConclusion, applySubst, Subst.lookup])
      · exact Equality.authored_equality_view_return constants premises state positions middle2 right type
          equalityIdentity "conclusion2" (by simp [premises, secondConclusion, applySubst, Subst.lookup])
    · simp [innerCases, operands, premises, before, environment, leftAtom, firstMiddle, secondMiddle, rightAtom,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold selected
      apply if_returns program operands state state state _ (boolean (DBTerm.same middle1 middle2)) _ _ _
      · exact Equality.authored_term_equality_test_return world constants identified operands state positions
          middle1 middle2 firstFormed secondFormed "middle1" "middle2"
          (by simp [operands, firstMiddle, applySubst, Subst.lookup])
          (by simp [operands, secondMiddle, applySubst, Subst.lookup])
      · cases DBTerm.same middle1 middle2
        · simp only [Bool.false_eq_true, ↓reduceIte, boolean]
          exact symbol_returns program operands state "None"
        · simp only [↓reduceIte, boolean, BEq.rfl]
          unfold resultBody theoremValue
          apply Equality.authored_theorem_equality_computed_return constants operands state positions
            left right type leftChecked rightChecked equalityIdentity
            (Premises.keys (union hyps1 hyps2)) (Premises.keys (union deps1 deps2)) (.symbol "TRANS")
          · exact ListOperations.Union.authored_union_return operands state hyps1 hyps2 "hyps1" "hyps2"
              (by simp [operands, premises, applySubst, Subst.lookup])
              (by simp [operands, premises, applySubst, Subst.lookup])
          · simpa [operands, leftAtom, applySubst, Subst.lookup] using variable_returns program operands state "left"
          · simpa [operands, rightAtom, applySubst, Subst.lookup] using variable_returns program operands state "right"
          · exact ListOperations.Union.authored_union_return operands state deps1 deps2 "deps1" "deps2"
              (by simp [operands, premises, applySubst, Subst.lookup])
              (by simp [operands, premises, applySubst, Subst.lookup])
          · exact symbol_returns program operands state "TRANS"

/-- Source transitivity computes exactly the structural middle-term check
and both retained list unions in the actual authored evaluation relation. -/
theorem authored_trans_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) (firstKey secondKey : String)
    (firstCaptured : applySubst bindings (.var firstKey) = .expression [.symbol "Some",
      theoremValue constants positions type left middle1 hyps1 deps1 origin1])
    (secondCaptured : applySubst bindings (.var secondKey) = .expression [.symbol "Some",
      theoremValue constants positions type middle2 right hyps2 deps2 origin2]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:trans", .var firstKey, .var secondKey]) state
      (if DBTerm.same middle1 middle2 then
        .expression [.symbol "Some", theoremValue constants positions type left right
          (union hyps1 hyps2) (union deps1 deps2) (.symbol "TRANS")]
       else .symbol "None") := by
  apply authored_variable_call_returns program bindings
    (environment
      (.expression [.symbol "Some", theoremValue constants positions type left middle1 hyps1 deps1 origin1])
      (.expression [.symbol "Some", theoremValue constants positions type middle2 right hyps2 deps2 origin2])) state state
    "hol-light:trans" [firstKey, secondKey] equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, firstCaptured, secondCaptured] using clause
      (.expression [.symbol "Some", theoremValue constants positions type left middle1 hyps1 deps1 origin1])
      (.expression [.symbol "Some", theoremValue constants positions type middle2 right hyps2 deps2 origin2])
  · exact body_returns world constants identified equalityIdentity state positions type left middle1 middle2 right
      leftChecked rightChecked firstFormed secondFormed hyps1 hyps2 deps1 deps2 origin1 origin2

/-- Computed premise lookups feed the same operation before its body runs. -/
theorem authored_trans_computed_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 firstExpression secondExpression : Atom)
    (firstComputed : PureReturns program bindings state firstExpression state (.expression [.symbol "Some",
      theoremValue constants positions type left middle1 hyps1 deps1 origin1]))
    (secondComputed : PureReturns program bindings state secondExpression state (.expression [.symbol "Some",
      theoremValue constants positions type middle2 right hyps2 deps2 origin2])) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:trans", firstExpression, secondExpression]) state
      (if DBTerm.same middle1 middle2 then
        .expression [.symbol "Some", theoremValue constants positions type left right
          (union hyps1 hyps2) (union deps1 deps2) (.symbol "TRANS")]
       else .symbol "None") := by
  exact authored_binary_call_returns program bindings
    (environment
      (.expression [.symbol "Some", theoremValue constants positions type left middle1 hyps1 deps1 origin1])
      (.expression [.symbol "Some", theoremValue constants positions type middle2 right hyps2 deps2 origin2]))
    state state state state "hol-light:trans" firstExpression secondExpression _ _ equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) firstComputed secondComputed
    (clause _ _) (body_returns world constants identified equalityIdentity state positions type left middle1 middle2 right
      leftChecked rightChecked firstFormed secondFormed hyps1 hyps2 deps1 deps2 origin1 origin2) (by decide)

/-- Reusing a printed name cannot splice distinct admitted middle terms. -/
theorem distinct_middle_refused (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (different : middle1 ≠ middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 : Atom) (firstKey secondKey : String)
    (firstCaptured : applySubst bindings (.var firstKey) = .expression [.symbol "Some",
      theoremValue constants positions type left middle1 hyps1 deps1 origin1])
    (secondCaptured : applySubst bindings (.var secondKey) = .expression [.symbol "Some",
      theoremValue constants positions type middle2 right hyps2 deps2 origin2]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:trans", .var firstKey, .var secondKey]) state (.symbol "None") := by
  have differentCheck : DBTerm.same middle1 middle2 = false := by
    apply Bool.eq_false_iff.mpr
    exact fun same => different ((DBTerm.same_eq_true_iff middle1 middle2).mp same)
  simpa only [differentCheck, Bool.false_eq_true, ↓reduceIte] using
    authored_trans_return world constants identified equalityIdentity bindings state positions type
      left middle1 middle2 right leftChecked rightChecked firstFormed secondFormed
      hyps1 hyps2 deps1 deps2 origin1 origin2 firstKey secondKey firstCaptured secondCaptured

/-- Hypothesis or axiom support descends to union, while the execution laws
retain the ordered source lists and do not identify receipts or their costs. -/
theorem union_support (item : Atom) (left right : List Atom) :
    item ∈ union left right ↔ item ∈ left ∨ item ∈ right :=
  ListOperations.Union.union_support item left right

end Mettapedia.Languages.HOLLight.MeTTa.Transitivity
