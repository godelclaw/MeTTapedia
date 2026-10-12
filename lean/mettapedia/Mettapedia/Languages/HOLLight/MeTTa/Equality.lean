import Mettapedia.Languages.HOLLight.MeTTa.Initialization
import Mettapedia.Languages.HOLLight.MeTTa.TermReflection

/-!
# Authored HOL equality construction

The retained source equation computes both operand types before constructing
the registered equality application. The result is the existing shared STT
term, not a new equality encoding or an identification with dependent Id.
These execution laws do not assert whole-checker soundness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Equality

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom)
open TypeSubstitution (typeAtom)

/-- The actual Boolean-carrier guard reflects the shared type judgment.
Registered formation prevents a different carrier from passing by spelling. -/
theorem authored_boolean_test_certificate (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State)
    (positions : List Ty) (term : DBTerm) (type : Ty)
    (typed : term.inferType positions = some type)
    (formed : SignatureFormation.TypeFormed world.signature type)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (termKey : String)
    (captured : applySubst bindings (.var termKey) = termAtom registeredOperatorAtom constants positions term) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "==", .expression [.symbol "hol-light:term-type", .var termKey],
        .expression [.symbol "Some", .expression [.symbol "hol-light:bool"]]]) state
      (boolean (Ty.same type Ty.bool)) := by
  have compared : (.expression [.symbol "Some", typeAtom registeredOperatorAtom type] ==
      Atom.expression [.symbol "Some", typeAtom registeredOperatorAtom Ty.bool]) = Ty.same type Ty.bool := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, Ty.same_eq_true_iff]
    simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true]
    constructor
    · exact fun equal => Representation.registered_typeAtom_injective world type Ty.bool formed booleanFormed equal
    · exact fun equal => congrArg (typeAtom registeredOperatorAtom) equal
  apply BoundCalls.CorePath.native_binary_call_returns program bindings state state state state "==" _ _
    (.expression [.symbol "Some", typeAtom registeredOperatorAtom type])
    (.expression [.symbol "Some", typeAtom registeredOperatorAtom Ty.bool]) _
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · exact TermJudgment.authored_term_type_certificate constants bindings state positions term type typed termKey captured
  · exact BoundCalls.CorePath.unary_constructor_of_returns program bindings state state "Some" _ _ (by decide) (by decide)
      (Initialization.authored_boolean_type_certificate bindings state)
  · simp only [StdLib.structural_equality, boolean, compared]

/-- Source structural comparison reflects the existing shared positional
term equality on registered annotations and declaration identities. -/
theorem authored_term_equality_test_certificate (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (bindings : Subst) (state : State) (positions : List Ty) (left right : DBTerm)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left)
    (rightFormed : SignatureFormation.AnnotationsFormed world.signature right)
    (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) = termAtom registeredOperatorAtom constants positions left)
    (rightCaptured : applySubst bindings (.var rightKey) = termAtom registeredOperatorAtom constants positions right) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "==", .var leftKey, .var rightKey]) state
      (boolean (DBTerm.same left right)) := by
  apply BoundCalls.CorePath.native_binary_call_returns program bindings state state state state "==" _ _
    (termAtom registeredOperatorAtom constants positions left)
    (termAtom registeredOperatorAtom constants positions right) (boolean (DBTerm.same left right))
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · simpa only [leftCaptured] using BoundCalls.CorePath.variable_returns program bindings state leftKey
  · simpa only [rightCaptured] using BoundCalls.CorePath.variable_returns program bindings state rightKey
  · by_cases same : left = right
    · subst right
      have compared : DBTerm.same left left = true := DBTerm.same_eq_true_iff left left |>.mpr rfl
      simp [StdLib.structural_equality, boolean, compared]
    · have different := TermReflection.distinct_terms_distinct_representations world constants identified
        positions left right leftFormed rightFormed same
      have compared : DBTerm.same left right = false := by
        apply Bool.eq_false_iff.mpr
        exact fun equal => same ((DBTerm.same_eq_true_iff left right).mp equal)
      simp [StdLib.structural_equality, boolean, beq_eq_decide, different, compared]

theorem authored_boolean_test_return (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State)
    (positions : List Ty) (term : DBTerm) (type : Ty)
    (typed : term.inferType positions = some type)
    (formed : SignatureFormation.TypeFormed world.signature type)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (termKey : String)
    (captured : applySubst bindings (.var termKey) = termAtom registeredOperatorAtom constants positions term) :
    PureReturns program bindings state
      (.expression [.symbol "==", .expression [.symbol "hol-light:term-type", .var termKey],
        .expression [.symbol "Some", .expression [.symbol "hol-light:bool"]]]) state
      (boolean (Ty.same type Ty.bool)) :=
  (authored_boolean_test_certificate world constants bindings state positions term type typed formed booleanFormed termKey captured).original

theorem authored_term_equality_test_return (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (bindings : Subst) (state : State) (positions : List Ty) (left right : DBTerm)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left)
    (rightFormed : SignatureFormation.AnnotationsFormed world.signature right)
    (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) = termAtom registeredOperatorAtom constants positions left)
    (rightCaptured : applySubst bindings (.var rightKey) = termAtom registeredOperatorAtom constants positions right) :
    PureReturns program bindings state (.expression [.symbol "==", .var leftKey, .var rightKey]) state
      (boolean (DBTerm.same left right)) :=
  (authored_term_equality_test_certificate world constants identified bindings state positions left right leftFormed rightFormed leftKey rightKey leftCaptured rightCaptured).original

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:equation"))[0]'(by decide)

private def environment (left right : Atom) : Subst := [("right", right), ("left", left)]

private def construction : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:App", .expression [.symbol "HOL:App",
    .expression [.symbol "HOL:C", .expression [.symbol "HOL:Primitive", .grounded (.string "=")],
      .expression [.symbol "hol-light:eq-type", .var "type"]], .var "left"], .var "right"]]

private def selected : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .expression [.symbol "hol-light:term-type", .var "right"],
    .expression [.symbol "Some", .var "type"]], construction, .symbol "None"]

private def cases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "type"], selected), (.var "malformed", .symbol "None")]

private theorem body_shape : equation.body = .expression [.symbol "case",
    .expression [.symbol "hol-light:term-type", .var "left"],
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem clause (left right : Atom) :
    clauses program "hol-light:equation" [left, right] =
      [.evaluate (environment left right) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:equation") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "left", .var "right"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem construction_returns (bindings : Subst) (state : State)
    (constants : Const → Atom) (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftCaptured : applySubst bindings (.var "left") = termAtom registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var "right") = termAtom registeredOperatorAtom constants context right)
    (typeCaptured : applySubst bindings (.var "type") = typeAtom registeredOperatorAtom type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality) :
    BoundCalls.CorePath.PureReturns program bindings state construction state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants context
        (CanonicalTerm.equalityDB type left right)]) := by
  simp only [construction, CanonicalTerm.equalityDB, termAtom, equalityIdentity]
  apply BoundCalls.CorePath.constructor_return program bindings state "Some" _ _ (by decide) (by decide)
  refine .cons ?_ .nil
  apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:App" _ _ _ _ (by decide) (by decide)
  · apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:App" _ _ _ _ (by decide) (by decide)
    · apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:C" _ _ _ _ (by decide) (by decide)
      · apply BoundCalls.CorePath.literal_return
        apply PureData.Literal.constructor "HOL:Primitive" _ (by decide) (by decide)
        intro child member
        simp only [List.mem_singleton] at member
        subst child
        exact .grounded _
      · exact Initialization.authored_equality_type_certificate bindings state (.var "type") type
          (by simpa only [typeCaptured] using BoundCalls.CorePath.variable_returns program bindings state "type")
    · simpa only [leftCaptured] using BoundCalls.CorePath.variable_returns program bindings state "left"
  · simpa only [rightCaptured] using BoundCalls.CorePath.variable_returns program bindings state "right"

private theorem body_returns (constants : Const → Atom) (context : List Ty)
    (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) :
    BoundCalls.CorePath.PureReturns program (environment (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right)) state equation.body state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants context
        (CanonicalTerm.equalityDB type left right)]) := by
  let before := environment (termAtom registeredOperatorAtom constants context left)
    (termAtom registeredOperatorAtom constants context right)
  let bound := ("type", typeAtom registeredOperatorAtom type) :: before
  rw [body_shape]
  apply BoundCalls.CorePath.case_returns program before bound state state state _
    (.expression [.symbol "Some", typeAtom registeredOperatorAtom type]) selected _ _ cases
    (read_cases_encoded cases)
  · exact TermJudgment.authored_term_type_certificate constants before state context left type leftChecked "left"
      (by simp [before, environment, applySubst, Subst.lookup])
  · simp [cases, before, bound, environment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold selected
    apply BoundCalls.CorePath.if_returns program bound state state state _ (boolean true) _ _ _ _ _
    · apply BoundCalls.CorePath.native_binary_call_returns program bound state state state state "==" _ _
        (.expression [.symbol "Some", typeAtom registeredOperatorAtom type])
        (.expression [.symbol "Some", typeAtom registeredOperatorAtom type]) (boolean true)
        (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
      · exact TermJudgment.authored_term_type_certificate constants bound state context right type rightChecked "right"
          (by simp [before, bound, environment, applySubst, Subst.lookup])
      · simpa [bound, applySubst, Subst.lookup] using
          BoundCalls.CorePath.unary_constructor_returns program bound state "Some" "type" (by decide) (by decide)
      · simp [StdLib.structural_equality, boolean]
    · exact construction_returns bound state constants context left right type
        (by simp [bound, before, environment, applySubst, Subst.lookup])
        (by simp [bound, before, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup]) equalityIdentity

/-- Running the actual source equation produces shared HOL equality, with
both operands checked in their complete positional context. -/
theorem authored_equation_certificate (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) = termAtom registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var rightKey) = termAtom registeredOperatorAtom constants context right) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:equation", .var leftKey, .var rightKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants context
        (CanonicalTerm.equalityDB type left right)]) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (environment (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right))
    state state "hol-light:equation" [leftKey, rightKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns constants context left right type leftChecked rightChecked equalityIdentity state) (by decide)
  simpa only [List.map_cons, List.map_nil, leftCaptured, rightCaptured] using
    clause (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right)

/-- Computed operands execute before the retained equality constructor.
Their typing is checked in the same positional context as captured operands. -/
theorem authored_equation_computed_certificate (constants : Const → Atom)
    (bindings : Subst) (state : State) (context : List Ty)
    (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (leftExpression rightExpression : Atom)
    (leftComputed : BoundCalls.CorePath.PureReturns program bindings state leftExpression state
      (termAtom registeredOperatorAtom constants context left))
    (rightComputed : BoundCalls.CorePath.PureReturns program bindings state rightExpression state
      (termAtom registeredOperatorAtom constants context right)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:equation", leftExpression, rightExpression]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants context
        (CanonicalTerm.equalityDB type left right)]) := by
  exact BoundCalls.CorePath.authored_binary_call_returns program bindings
    (environment (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right))
    state state state state "hol-light:equation" leftExpression rightExpression _ _ equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    leftComputed rightComputed (clause _ _)
    (body_returns constants context left right type leftChecked rightChecked equalityIdentity state)
    (by decide)

theorem authored_equation_return (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) = termAtom registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var rightKey) = termAtom registeredOperatorAtom constants context right) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:equation", .var leftKey, .var rightKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants context
        (CanonicalTerm.equalityDB type left right)]) := by
  apply authored_variable_call_returns program bindings
    (environment (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right))
    state state "hol-light:equation" [leftKey, rightKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns constants context left right type leftChecked rightChecked equalityIdentity state).original (by decide)
  simpa only [List.map_cons, List.map_nil, leftCaptured, rightCaptured] using
    clause (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right)

/-- The produced application independently satisfies the shared STT typing
judgment, including open positional contexts. -/
theorem equality_result_typed (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type) :
    (CanonicalTerm.equalityDB type left right).inferType context = some Ty.bool := by
  simp [CanonicalTerm.equalityDB, DBTerm.inferType, Ty.equality, Ty.function,
    TypeOp.function, Ty.destFunction?, leftChecked, rightChecked]

/-- Different admitted operand types are refused by the actual equation;
their source representation cannot erase the difference. -/
theorem authored_wrong_type_refused (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (left right : DBTerm) (leftType rightType : Ty)
    (leftChecked : left.inferType context = some leftType)
    (rightChecked : right.inferType context = some rightType)
    (leftFormed : SignatureFormation.TypeFormed theory.signature leftType)
    (rightFormed : SignatureFormation.TypeFormed theory.signature rightType)
    (different : rightType ≠ leftType) (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) = termAtom registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var rightKey) = termAtom registeredOperatorAtom constants context right) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:equation", .var leftKey, .var rightKey]) state (.symbol "None") := by
  let before := environment (termAtom registeredOperatorAtom constants context left)
    (termAtom registeredOperatorAtom constants context right)
  let bound := ("type", typeAtom registeredOperatorAtom leftType) :: before
  have encodedDifferent : typeAtom registeredOperatorAtom rightType ≠ typeAtom registeredOperatorAtom leftType :=
    fun equal => different (Representation.registered_typeAtom_injective theory rightType leftType
      rightFormed leftFormed equal)
  apply authored_variable_call_returns program bindings before state state
    "hol-light:equation" [leftKey, rightKey] equation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, leftCaptured, rightCaptured] using
      clause (termAtom registeredOperatorAtom constants context left)
        (termAtom registeredOperatorAtom constants context right)
  · rw [body_shape]
    apply case_returns program before bound state state state _
      (.expression [.symbol "Some", typeAtom registeredOperatorAtom leftType]) selected _ _ cases
      (read_cases_encoded cases)
    · exact TermJudgment.authored_term_type_return constants before state context left leftType leftChecked "left"
        (by simp [before, environment, applySubst, Subst.lookup])
    · simp [cases, before, bound, environment, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold selected
      apply if_returns program bound state state state _ (boolean false) _ _ _ _ _
      · apply native_binary_call_returns program bound state state state state "==" _ _
          (.expression [.symbol "Some", typeAtom registeredOperatorAtom rightType])
          (.expression [.symbol "Some", typeAtom registeredOperatorAtom leftType]) (boolean false)
          (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
        · exact TermJudgment.authored_term_type_return constants bound state context right rightType rightChecked "right"
            (by simp [before, bound, environment, applySubst, Subst.lookup])
        · simpa [bound, applySubst, Subst.lookup] using
            unary_constructor_returns program bound state "Some" "type" (by decide) (by decide)
        · simp [StdLib.structural_equality, boolean, encodedDifferent]
      · exact symbol_returns program bound state "None"

private def viewEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:dest-eq"))[0]'(by decide)

private def viewBody : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:Equation", .var "left", .var "right"]]

private def viewCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "HOL:App", .expression [.symbol "HOL:App",
      .expression [.symbol "HOL:C", .expression [.symbol "HOL:Primitive", .grounded (.string "=")],
        .var "type"], .var "left"], .var "right"], viewBody),
    (.var "malformed", .symbol "None")]

private theorem view_shape : viewEquation.body = .expression [.symbol "case", .var "term",
    .expression (viewCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem view_clause (term : Atom) :
    clauses program "hol-light:dest-eq" [term] =
      [.evaluate [("term", term)] viewEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:dest-eq") = [viewEquation] := by rfl
  rw [unique]
  have formals : viewEquation.arguments = [.var "term"] := by decide
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The source equality view recovers the exact operands of the constructed
shared equality term. It does not reinterpret dependent identity evidence. -/
theorem authored_equality_view_return (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (left right : DBTerm) (type : Ty)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (key : String) (captured : applySubst bindings (.var key) =
      termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:dest-eq", .var key]) state
      (.expression [.symbol "Some", .expression [.symbol "HOL:Equation",
        termAtom registeredOperatorAtom constants context left,
        termAtom registeredOperatorAtom constants context right]]) := by
  let term := termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right)
  let before : Subst := [("term", term)]
  let bound : Subst := [("right", termAtom registeredOperatorAtom constants context right),
    ("left", termAtom registeredOperatorAtom constants context left),
    ("type", typeAtom registeredOperatorAtom (Ty.equality type))] ++ before
  apply authored_variable_call_returns program bindings before state state "hol-light:dest-eq" [key]
    viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, captured] using view_clause term
  · rw [view_shape]
    apply case_returns program before bound state state state (.var "term") term viewBody _ _ viewCases
      (read_cases_encoded viewCases)
    · exact variable_returns program before state "term"
    · have registered : constants Const.equality =
          .expression [.symbol "HOL:Primitive", .grounded (.string "=")] := equalityIdentity.trans rfl
      simp only [viewCases, bound, before, term, CanonicalTerm.equalityDB, termAtom]
      rw [registered]
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold viewBody
      apply PureData.constructor_return program bound state "Some" _ _ (by decide) (by decide)
      refine .cons ?_ .nil
      apply binary_constructor_returns program bound state state state "HOL:Equation" _ _ _ _ (by decide) (by decide)
      · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "left"
      · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "right"

/-- A defined constant named '=' is still a different declaration. The
actual source equality view refuses its application despite that spelling. -/
theorem authored_defined_equality_refused (bindings : Subst) (state : State)
    (schema definition type left right : Atom) (key : String)
    (captured : applySubst bindings (.var key) = .expression [.symbol "HOL:App",
      .expression [.symbol "HOL:App", .expression [.symbol "HOL:C",
        .expression [.symbol "HOL:Defined", .grounded (.string "="), schema, definition], type], left], right]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:dest-eq", .var key]) state
      (.symbol "None") := by
  let term : Atom := .expression [.symbol "HOL:App", .expression [.symbol "HOL:App",
    .expression [.symbol "HOL:C", .expression [.symbol "HOL:Defined", .grounded (.string "="),
      schema, definition], type], left], right]
  let before : Subst := [("term", term)]
  let bound : Subst := ("malformed", term) :: before
  apply authored_variable_call_returns program bindings before state state "hol-light:dest-eq" [key]
    viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, captured] using view_clause term
  · rw [view_shape]
    apply case_returns program before bound state state state (.var "term") term (.symbol "None") _ _ viewCases
      (read_cases_encoded viewCases)
    · exact variable_returns program before state "term"
    · simp [viewCases, bound, before, term, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · exact symbol_returns program bound state "None"

private def theoremEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:theorem-eq"))[0]'(by decide)

private def theoremBody : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:Thm", .var "hyps", .var "equation", .var "dependencies", .var "origin"]]

private def theoremCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "equation"], theoremBody), (.var "malformed", .symbol "None")]

private def theoremEnvironment (hypotheses left right dependencies origin : Atom) : Subst :=
  [("origin", origin), ("dependencies", dependencies), ("right", right), ("left", left), ("hyps", hypotheses)]

private theorem theorem_shape : theoremEquation.body = .expression [.symbol "case",
    .expression [.symbol "hol-light:equation", .var "left", .var "right"],
    .expression (theoremCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem theorem_clause (hypotheses left right dependencies origin : Atom) :
    clauses program "hol-light:theorem-eq" [hypotheses, left, right, dependencies, origin] =
      [.evaluate (theoremEnvironment hypotheses left right dependencies origin) theoremEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:theorem-eq") = [theoremEquation] := by rfl
  rw [unique]
  have formals : theoremEquation.arguments =
      [.var "hyps", .var "left", .var "right", .var "dependencies", .var "origin"] := by decide
  simp [formals, theoremEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem theorem_body_return (constants : Const → Atom) (state : State)
    (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (hypotheses dependencies origin : Atom) :
    BoundCalls.CorePath.PureReturns program
      (theoremEnvironment hypotheses (termAtom registeredOperatorAtom constants context left)
        (termAtom registeredOperatorAtom constants context right) dependencies origin)
      state theoremEquation.body state
      (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", hypotheses,
        termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right),
        dependencies, origin]]) := by
  let before := theoremEnvironment hypotheses (termAtom registeredOperatorAtom constants context left)
    (termAtom registeredOperatorAtom constants context right) dependencies origin
  let equality := termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right)
  let bound := ("equation", equality) :: before
  rw [theorem_shape]
  apply BoundCalls.CorePath.case_returns program before bound state state state _
    (.expression [.symbol "Some", equality]) theoremBody _ _ theoremCases (read_cases_encoded theoremCases)
  · exact authored_equation_certificate constants before state context left right type leftChecked rightChecked
      equalityIdentity "left" "right"
      (by simp [before, theoremEnvironment, applySubst, Subst.lookup])
      (by simp [before, theoremEnvironment, applySubst, Subst.lookup])
  · simp [theoremCases, before, bound, theoremEnvironment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold theoremBody
    apply BoundCalls.CorePath.constructor_return program bound state "Some" _ _ (by decide) (by decide)
    refine .cons ?_ .nil
    simpa [before, bound, theoremEnvironment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.constructor_variables_return program bound state "HOL:Thm"
        ["hyps", "equation", "dependencies", "origin"] (by decide) (by decide)

/-- Computed hypotheses and dependencies enter the same authored constructor.
Argument evaluation precedes its equation body; no cached result is assumed. -/
theorem authored_theorem_equality_computed_certificate (constants : Const → Atom)
    (bindings : Subst) (state : State) (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (hypotheses dependencies origin hypothesesExpression leftExpression rightExpression
      dependenciesExpression originExpression : Atom)
    (hypothesesComputed : BoundCalls.CorePath.PureReturns program bindings state hypothesesExpression state hypotheses)
    (leftComputed : BoundCalls.CorePath.PureReturns program bindings state leftExpression state
      (termAtom registeredOperatorAtom constants context left))
    (rightComputed : BoundCalls.CorePath.PureReturns program bindings state rightExpression state
      (termAtom registeredOperatorAtom constants context right))
    (dependenciesComputed : BoundCalls.CorePath.PureReturns program bindings state dependenciesExpression state dependencies)
    (originComputed : BoundCalls.CorePath.PureReturns program bindings state originExpression state origin) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:theorem-eq", hypothesesExpression, leftExpression,
        rightExpression, dependenciesExpression, originExpression]) state
      (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", hypotheses,
        termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right),
        dependencies, origin]]) := by
  apply BoundCalls.CorePath.call_returns program bindings state state "hol-light:theorem-eq" _ _ (by decide) _ (by decide)
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    hypothesesExpression hypotheses _ _ [] 0 (by decide) hypothesesComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    leftExpression (termAtom registeredOperatorAtom constants context left) _ _ [_] 1 (by decide) leftComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    rightExpression (termAtom registeredOperatorAtom constants context right) _ _ [_, _] 2 (by decide) rightComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    dependenciesExpression dependencies _ _ [_, _, _] 3 (by decide) dependenciesComputed
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    originExpression origin _ [] [_, _, _, _] 4 (by decide) originComputed
  exact BoundCalls.CorePath.authored_function_arguments_return program bindings
    (theoremEnvironment hypotheses (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right) dependencies origin)
    state state "hol-light:theorem-eq" _ 5 theoremEquation.body _
    (by decide) (by decide) (theorem_clause _ _ _ _ _)
    (theorem_body_return constants state context left right type leftChecked rightChecked
      equalityIdentity hypotheses dependencies origin)

theorem authored_theorem_equality_computed_return (constants : Const → Atom)
    (bindings : Subst) (state : State) (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (hypotheses dependencies origin hypothesesExpression leftExpression rightExpression
      dependenciesExpression originExpression : Atom)
    (hypothesesComputed : PureReturns program bindings state hypothesesExpression state hypotheses)
    (leftComputed : PureReturns program bindings state leftExpression state
      (termAtom registeredOperatorAtom constants context left))
    (rightComputed : PureReturns program bindings state rightExpression state
      (termAtom registeredOperatorAtom constants context right))
    (dependenciesComputed : PureReturns program bindings state dependenciesExpression state dependencies)
    (originComputed : PureReturns program bindings state originExpression state origin) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:theorem-eq", hypothesesExpression, leftExpression,
        rightExpression, dependenciesExpression, originExpression]) state
      (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", hypotheses,
        termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right),
        dependencies, origin]]) := by
  apply call_returns program bindings state state "hol-light:theorem-eq" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    hypothesesExpression hypotheses _ _ [] 0 (by decide) hypothesesComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    leftExpression (termAtom registeredOperatorAtom constants context left) _ _ [_] 1 (by decide) leftComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    rightExpression (termAtom registeredOperatorAtom constants context right) _ _ [_, _] 2 (by decide) rightComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    dependenciesExpression dependencies _ _ [_, _, _] 3 (by decide) dependenciesComputed
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:theorem-eq")
    originExpression origin _ [] [_, _, _, _] 4 (by decide) originComputed
  exact authored_function_arguments_return program bindings
    (theoremEnvironment hypotheses (termAtom registeredOperatorAtom constants context left)
      (termAtom registeredOperatorAtom constants context right) dependencies origin)
    state state "hol-light:theorem-eq" _ 5 theoremEquation.body _
    (by decide) (by decide) (theorem_clause _ _ _ _ _)
    (theorem_body_return constants state context left right type leftChecked rightChecked
      equalityIdentity hypotheses dependencies origin).original

/-- The internal theorem constructor executes the proved equality operation
and retains the exact hypotheses, dependencies and origin supplied by its
caller. Calling this constructor alone does not admit a theorem to the cache. -/
theorem authored_theorem_equality_return (constants : Const → Atom) (bindings : Subst) (state : State)
    (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (hypotheses dependencies origin : Atom) (hypothesesKey leftKey rightKey dependenciesKey originKey : String)
    (hypothesesCaptured : applySubst bindings (.var hypothesesKey) = hypotheses)
    (leftCaptured : applySubst bindings (.var leftKey) = termAtom registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var rightKey) = termAtom registeredOperatorAtom constants context right)
    (dependenciesCaptured : applySubst bindings (.var dependenciesKey) = dependencies)
    (originCaptured : applySubst bindings (.var originKey) = origin) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:theorem-eq", .var hypothesesKey, .var leftKey,
        .var rightKey, .var dependenciesKey, .var originKey]) state
      (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", hypotheses,
        termAtom registeredOperatorAtom constants context (CanonicalTerm.equalityDB type left right), dependencies, origin]]) := by
  let before := theoremEnvironment hypotheses (termAtom registeredOperatorAtom constants context left)
    (termAtom registeredOperatorAtom constants context right) dependencies origin
  apply authored_variable_call_returns program bindings before state state "hol-light:theorem-eq"
    [hypothesesKey, leftKey, rightKey, dependenciesKey, originKey] theoremEquation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, hypothesesCaptured, leftCaptured, rightCaptured,
      dependenciesCaptured, originCaptured] using theorem_clause hypotheses
        (termAtom registeredOperatorAtom constants context left)
        (termAtom registeredOperatorAtom constants context right) dependencies origin
  · exact (theorem_body_return constants state context left right type leftChecked rightChecked
      equalityIdentity hypotheses dependencies origin).original

end Mettapedia.Languages.HOLLight.MeTTa.Equality
