import Mettapedia.Languages.HOLLight.MeTTa.Transitivity

/-!
# The authored hypothesis-freshness test

The free-variable collection executes the retained source body, including its
ordered unions. Membership reflects the shared calculus's exact typed variable
identity in a registered signature. The list test retains every hypothesis
occurrence; its logical support is the existing finite-hypothesis condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.FreeVariables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (termAtom variableAtom registeredOperatorAtom)
open SignatureFormation

/-- The exact ordered variable list returned by the authored traversal. -/
def freeAtoms (operators : TypeOp → Atom) : DBTerm → List Atom
  | .free sourceVar => [variableAtom operators sourceVar]
  | .bound _ | .const _ _ => []
  | .abs _ body => freeAtoms operators body
  | .app function argument => Transitivity.union (freeAtoms operators function) (freeAtoms operators argument)

private theorem union_nil_iff (left right : List Atom) :
    Transitivity.union left right = [] ↔ left = [] ∧ right = [] := by
  constructor
  · intro empty
    cases left with
    | nil => exact ⟨rfl, empty⟩
    | cons first rest =>
        have member : first ∈ Transitivity.union (first :: rest) right :=
          (Transitivity.union_support first (first :: rest) right).mpr (Or.inl List.mem_cons_self)
        rw [empty] at member
        cases member
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual ordered traversal is empty exactly when the shared canonical
term has no free term variables. It does not erase bound annotations. -/
theorem free_atoms_nil_iff (operators : TypeOp → Atom) (term : DBTerm) :
    freeAtoms operators term = [] ↔ term.HasNoFreeVariables := by
  induction term with
  | free sourceVar =>
      constructor
      · intro impossible
        simp [freeAtoms] at impossible
      · intro impossible
        cases impossible
  | bound index => simp [freeAtoms, DBTerm.HasNoFreeVariables.bound]
  | const constant type => simp [freeAtoms, DBTerm.HasNoFreeVariables.const]
  | abs domain body ih =>
      rw [freeAtoms, ih]
      constructor
      · exact DBTerm.HasNoFreeVariables.abs
      · intro closed
        cases closed with
        | abs bodyClosed => exact bodyClosed
  | app function argument functionIH argumentIH =>
      rw [freeAtoms, union_nil_iff, functionIH, argumentIH]
      constructor
      · rintro ⟨functionClosed, argumentClosed⟩
        exact .app functionClosed argumentClosed
      · intro closed
        cases closed with
        | app functionClosed argumentClosed => exact ⟨functionClosed, argumentClosed⟩

/-- Registered typed identities make the source membership guard faithful.
The variable's spelling alone is not used as an occurrence test. -/
theorem registered_member_iff (world : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (term : DBTerm) (formed : AnnotationsFormed world.signature term) :
    variableAtom registeredOperatorAtom needle ∈ freeAtoms registeredOperatorAtom term ↔
      DBTerm.FreeOccurrence needle term := by
  induction term with
  | free sourceVar =>
      cases formed with
      | free typeFormed =>
          rw [freeAtoms, List.mem_singleton, Representation.registered_variableAtom_eq_iff
            world needle sourceVar needleFormed typeFormed]
          constructor
          · intro same; subst sourceVar; exact .here
          · intro occurs; cases occurs; rfl
  | bound index =>
      constructor
      · simp [freeAtoms]
      · intro occurs; cases occurs
  | const constant type =>
      constructor
      · simp [freeAtoms]
      · intro occurs; cases occurs
  | abs domain body ih =>
      cases formed with
      | abs domainFormed bodyFormed =>
          rw [freeAtoms, ih bodyFormed]
          constructor
          · exact DBTerm.FreeOccurrence.absBody
          · intro occurs; cases occurs with | absBody found => exact found
  | app function argument functionIH argumentIH =>
      cases formed with
      | app functionFormed argumentFormed =>
          rw [freeAtoms, Transitivity.union_support, functionIH functionFormed, argumentIH argumentFormed]
          constructor
          · intro occurs; exact occurs.elim DBTerm.FreeOccurrence.appFunction DBTerm.FreeOccurrence.appArgument
          · intro occurs
            cases occurs with
            | appFunction found => exact Or.inl found
            | appArgument found => exact Or.inr found

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:free-vars"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def freeBody : Atom := .expression [.symbol "HOL:Cons", .var "term", .symbol "HOL:Nil"]
private def lambdaBody : Atom := .expression [.symbol "hol-light:free-vars", .var "body"]
private def applicationBody : Atom := .expression [.symbol "hol-light:union",
  .expression [.symbol "hol-light:free-vars", .var "function"],
  .expression [.symbol "hol-light:free-vars", .var "argument"]]
private def environment (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (term : DBTerm) : Subst := [("term", termAtom operators constants positions term)]
private theorem shape : equation.body = .expression [.symbol "case", .var "term",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.expression [.symbol "HOL:Free", .var "name", .var "type"], freeBody),
     (.expression [.symbol "HOL:Bound", .var "index", .var "type"], .symbol "HOL:Nil"),
     (.expression [.symbol "HOL:C", .var "identity", .var "type"], .symbol "HOL:Nil"),
     (.expression [.symbol "HOL:Lam", .var "type", .var "body"], lambdaBody),
     (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
     (.var "malformed", .symbol "None")] := by decide
private theorem clause (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (term : DBTerm) :
    clauses program "hol-light:free-vars" [termAtom operators constants positions term] =
      [.evaluate (environment operators constants positions term) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:free-vars") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "term"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (operators : TypeOp → Atom) (constants : Const → Atom)
    (term : DBTerm) (positions : List Ty) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment operators constants positions term) state equation.body state
      (Premises.keys (freeAtoms operators term)) := by
  induction term generalizing positions with
  | free sourceVar =>
      let before := environment operators constants positions (.free sourceVar)
      let bound := [("type", TypeSubstitution.typeAtom operators sourceVar.ty),
        ("name", TypeSubstitution.nameAtom sourceVar.name)] ++ before
      rw [shape]
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (variableAtom operators sourceVar) freeBody _ _ cases (read_cases_encoded cases)
      · simpa [before, environment, termAtom, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom, variableAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold freeBody
        apply BoundCalls.CorePath.constructor_return program bound state "HOL:Cons" _ _ (by decide) (by decide)
        refine .cons ?_ (.cons (BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil") .nil)
        simpa [freeAtoms, Premises.keys, bound, before, environment, termAtom, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program bound state "term"
  | bound index =>
      let before := environment operators constants positions (.bound index)
      let bound := [("type", ((positions[index]?).map (TypeSubstitution.typeAtom operators)).getD (.symbol "None")),
        ("index", Atom.grounded (.int index))] ++ before
      rw [shape]
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (termAtom operators constants positions (.bound index)) (.symbol "HOL:Nil") _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · exact BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil"
  | const constant type =>
      let before := environment operators constants positions (.const constant type)
      let bound := [("type", TypeSubstitution.typeAtom operators type), ("identity", constants constant)] ++ before
      rw [shape]
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (termAtom operators constants positions (.const constant type)) (.symbol "HOL:Nil") _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · exact BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil"
  | abs domain body ih =>
      let before := environment operators constants positions (.abs domain body)
      let bound := [("body", termAtom operators constants (domain :: positions) body),
        ("type", TypeSubstitution.typeAtom operators domain)] ++ before
      rw [shape]
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (termAtom operators constants positions (.abs domain body)) lambdaBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold lambdaBody
        apply BoundCalls.CorePath.authored_variable_call_returns program bound (environment operators constants (domain :: positions) body)
          state state "hol-light:free-vars" ["body"] equation.body _
          (by decide) (by decide) (by decide) _ (ih (domain :: positions)) (by decide)
        simpa [bound, applySubst, Subst.lookup] using clause operators constants (domain :: positions) body
  | app function argument functionIH argumentIH =>
      let before := environment operators constants positions (.app function argument)
      let bound := [("argument", termAtom operators constants positions argument),
        ("function", termAtom operators constants positions function)] ++ before
      rw [shape]
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (termAtom operators constants positions (.app function argument)) applicationBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [cases_shape, bound, before, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold applicationBody
        apply ListOperations.Union.authored_union_computed_certificate bound state
          (freeAtoms operators function) (freeAtoms operators argument)
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound (environment operators constants positions function)
            state state "hol-light:free-vars" ["function"] equation.body _
            (by decide) (by decide) (by decide) _ (functionIH positions) (by decide)
          simpa [bound, applySubst, Subst.lookup] using clause operators constants positions function
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound (environment operators constants positions argument)
            state state "hol-light:free-vars" ["argument"] equation.body _
            (by decide) (by decide) (by decide) _ (argumentIH positions) (by decide)
          simpa [bound, applySubst, Subst.lookup] using clause operators constants positions argument

/-- Every represented term's free variables are obtained by the actual source
traversal. This does not require treating a theorem record as admitted evidence. -/
theorem authored_free_vars_certificate (operators : TypeOp → Atom) (constants : Const → Atom)
    (term : DBTerm) (positions : List Ty) (bindings : Subst) (state : State) (key : String)
    (captured : applySubst bindings (.var key) = termAtom operators constants positions term) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:free-vars", .var key]) state
      (Premises.keys (freeAtoms operators term)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment operators constants positions term)
    state state "hol-light:free-vars" [key] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns operators constants term positions state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using clause operators constants positions term

theorem authored_free_vars_return (operators : TypeOp → Atom) (constants : Const → Atom)
    (term : DBTerm) (positions : List Ty) (bindings : Subst) (state : State) (key : String)
    (captured : applySubst bindings (.var key) = termAtom operators constants positions term) :
    PureReturns program bindings state (.expression [.symbol "hol-light:free-vars", .var key]) state
      (Premises.keys (freeAtoms operators term)) :=
  (authored_free_vars_certificate operators constants term positions bindings state key captured).original

namespace Hypotheses

def occurs (operators : TypeOp → Atom) (needle : Atom) (terms : List DBTerm) : Bool :=
  terms.any fun term => decide (needle ∈ freeAtoms operators term)

/-- Logical support of the exact source guard is the shared occurrence
predicate, with every represented term's annotations accounted for. -/
theorem registered_occurs_iff (world : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (terms : List DBTerm) (formed : ∀ term ∈ terms, AnnotationsFormed world.signature term) :
    occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) terms = true ↔
      ∃ term ∈ terms, DBTerm.FreeOccurrence needle term := by
  simp only [occurs, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨term, member, found⟩
    exact ⟨term, member, (registered_member_iff world needle needleFormed term (formed term member)).mp found⟩
  · rintro ⟨term, member, found⟩
    exact ⟨term, member, (registered_member_iff world needle needleFormed term (formed term member)).mpr found⟩

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:free-in"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:member", .var "variable", .expression [.symbol "hol-light:free-vars", .var "first"]],
  boolean true, .expression [.symbol "hol-light:free-in", .var "variable", .var "rest"]]
private def environment (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (needle : Atom) (terms : List DBTerm) : Subst :=
  [("terms", Premises.keys (terms.map (termAtom operators constants positions))), ("variable", needle)]
private theorem shape : equation.body = .expression [.symbol "case", .var "terms",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", boolean false),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", boolean true)] := by decide
private theorem clause (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (needle : Atom) (terms : List DBTerm) :
    clauses program "hol-light:free-in" [needle, Premises.keys (terms.map (termAtom operators constants positions))] =
      [.evaluate (environment operators constants positions needle terms) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:free-in") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "variable", .var "terms"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (needle : Atom) (terms : List DBTerm) (state : State) :
    PureReturns program (environment operators constants positions needle terms) state equation.body state
      (boolean (occurs operators needle terms)) := by
  induction terms with
  | nil =>
      rw [shape]
      apply case_returns program (environment operators constants positions needle [])
        (environment operators constants positions needle []) state state state (.var "terms")
        (.symbol "HOL:Nil") (boolean false) _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          variable_returns program (environment operators constants positions needle []) state "terms"
      · simp [cases_shape, environment, Premises.keys, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program _ state _
  | cons first rest ih =>
      let before := environment operators constants positions needle (first :: rest)
      let bound := [("rest", Premises.keys (rest.map (termAtom operators constants positions))),
        ("first", termAtom operators constants positions first)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "terms")
        (Premises.keys ((first :: rest).map (termAtom operators constants positions))) consBody _ _ cases (read_cases_encoded cases)
      · exact variable_returns program before state "terms"
      · simp [cases_shape, before, bound, environment, Premises.keys, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply if_returns program bound state state state _ (boolean (decide (needle ∈ freeAtoms operators first))) _ _ _
        · apply ListOperations.Membership.authored_member_computed_return bound state needle (freeAtoms operators first)
          · simpa [bound, before, environment, applySubst, Subst.lookup] using variable_returns program bound state "variable"
          · exact authored_free_vars_return operators constants first positions bound state "first"
              (by simp [bound, applySubst, Subst.lookup])
        · by_cases found : needle ∈ freeAtoms operators first
          · simp only [found, decide_true, boolean, BEq.rfl, ↓reduceIte]
            simpa [occurs, found] using grounded_returns program bound state (.bool true)
          · simp only [found, decide_false, boolean]
            apply authored_variable_call_returns program bound (environment operators constants positions needle rest)
              state state "hol-light:free-in" ["variable", "rest"] equation.body _
              (by decide) (by decide) (by decide) _ _ (by decide)
            · simpa [bound, before, environment, applySubst, Subst.lookup] using clause operators constants positions needle rest
            · simpa [occurs, found, boolean] using ih

/-- Exact execution of the source list guard, including repeated hypotheses. -/
theorem authored_free_in_return (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (needle : Atom) (terms : List DBTerm) (bindings : Subst) (state : State)
    (needleKey termsKey : String) (needleCaptured : applySubst bindings (.var needleKey) = needle)
    (termsCaptured : applySubst bindings (.var termsKey) = Premises.keys (terms.map (termAtom operators constants positions))) :
    PureReturns program bindings state (.expression [.symbol "hol-light:free-in", .var needleKey, .var termsKey]) state
      (boolean (occurs operators needle terms)) := by
  apply authored_variable_call_returns program bindings (environment operators constants positions needle terms) state state
    "hol-light:free-in" [needleKey, termsKey] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns operators constants positions needle terms state) (by decide)
  simpa only [List.map_cons, List.map_nil, needleCaptured, termsCaptured] using clause operators constants positions needle terms

/-- The authoring representation's guard is exactly the existing shared HOL
freshness condition over a finite hypothesis set. -/
theorem canonical_guard_iff (world : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (hypotheses : List CanonicalTerm)
    (formed : ∀ term ∈ hypotheses, AnnotationsFormed world.signature term.term) :
    occurs registeredOperatorAtom (variableAtom registeredOperatorAtom needle) (hypotheses.map (·.term)) = true ↔
      FreeInHypotheses needle hypotheses.toFinset := by
  have mappedFormed : ∀ term ∈ hypotheses.map (·.term), AnnotationsFormed world.signature term := by
    intro term member
    have selected : ∃ hypothesis : CanonicalTerm, hypothesis ∈ hypotheses ∧ hypothesis.term = term :=
      List.mem_map.mp member
    obtain ⟨hypothesis, hypothesisMember, equal⟩ := selected
    rw [← equal]
    exact formed hypothesis hypothesisMember
  simpa [FreeInHypotheses] using registered_occurs_iff world needle needleFormed
    (hypotheses.map (·.term)) mappedFormed

end Hypotheses

end Mettapedia.Languages.HOLLight.MeTTa.FreeVariables
