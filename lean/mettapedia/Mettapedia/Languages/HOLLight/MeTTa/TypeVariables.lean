import Mettapedia.Languages.HOLLight.MeTTa.FreeVariables

/-!
# Actual type-parameter collectors and the shared signature support

The authored collectors traverse type syntax and retain their ordered union
results. Their logical support is the existing set of type parameters, with
the existing injective name representation. Operator and definition payloads
remain opaque. Bound term annotations are handled with their source context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeVariables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval (clauses clauses_use_only_the_named_equations read_cases_encoded)
open Effects (State)
open TypeSubstitution (nameAtom typeAtom)

mutual
  def typeAtoms : Ty → List Atom
    | .var name => [nameAtom name]
    | .op _ arguments => typesAtoms arguments
  termination_by type => sizeOf type

  def typesAtoms : List Ty → List Atom
    | [] => []
    | first :: rest => Transitivity.union (typeAtoms first) (typesAtoms rest)
  termination_by types => sizeOf types
end

theorem union_nodup (left right : List Atom) (distinct : right.Nodup) :
    (Transitivity.union left right).Nodup := by
  unfold Transitivity.union
  induction left generalizing right with
  | nil => exact distinct
  | cons first rest ih =>
      simp only [List.foldl_cons]
      apply ih
      by_cases present : first ∈ right
      · simpa only [if_pos present] using distinct
      · simpa only [if_neg present, List.nodup_cons] using And.intro present distinct

theorem types_atoms_nodup (types : List Ty) : (typesAtoms types).Nodup := by
  induction types with
  | nil => simp [typesAtoms]
  | cons first rest ih => simpa only [typesAtoms] using union_nodup (typeAtoms first) (typesAtoms rest) ih

theorem type_atoms_nodup (type : Ty) : (typeAtoms type).Nodup := by
  cases type with
  | var name => simp [typeAtoms]
  | op operator arguments => simpa only [typeAtoms] using types_atoms_nodup arguments

private theorem union_support (left right : List Atom) :
    (Transitivity.union left right).toFinset = left.toFinset ∪ right.toFinset := by
  apply Finset.ext
  intro value
  simp only [List.mem_toFinset, Finset.mem_union, Transitivity.union_support]

mutual
  theorem type_atoms_support (type : Ty) :
      (typeAtoms type).toFinset = type.typeVariables.image nameAtom := by
    cases type with
    | var name => simp [typeAtoms, Ty.typeVariables]
    | op operator arguments =>
        simpa only [typeAtoms, Ty.typeVariables] using types_atoms_support arguments
  termination_by sizeOf type

  theorem types_atoms_support (types : List Ty) :
      (typesAtoms types).toFinset = (Ty.typeVariablesList types).image nameAtom := by
    cases types with
    | nil => simp [typesAtoms, Ty.typeVariablesList]
    | cons first rest =>
        rw [typesAtoms, union_support, type_atoms_support first, types_atoms_support rest,
          Ty.typeVariablesList, Finset.image_union]
  termination_by sizeOf types
end

theorem mem_type_atoms (name : Name) (type : Ty) :
    nameAtom name ∈ typeAtoms type ↔ name ∈ type.typeVariables := by
  rw [← List.mem_toFinset, type_atoms_support]
  constructor
  · intro member
    obtain ⟨candidate, present, same⟩ := Finset.mem_image.mp member
    have equal := TypeSubstitution.nameAtom_injective same
    subst candidate
    exact present
  · intro member
    exact Finset.mem_image.mpr ⟨name, member, rfl⟩

/-- Exact name identity makes the source list-inclusion guard equivalent to
the existing type-parameter side condition. No parameter ordering is invented. -/
theorem type_atoms_subset_iff (left right : Ty) :
    typeAtoms left ⊆ typeAtoms right ↔ left.typeVariables ⊆ right.typeVariables := by
  constructor
  · intro included name member
    exact (mem_type_atoms name right).mp (included ((mem_type_atoms name left).mpr member))
  · intro included atom member
    have imageMember : atom ∈ left.typeVariables.image nameAtom := by
      rw [← type_atoms_support]
      exact List.mem_toFinset.mpr member
    obtain ⟨name, parameter, rfl⟩ := Finset.mem_image.mp imageMember
    exact (mem_type_atoms name right).mpr (included parameter)

/-- Ordered annotation parameters in a represented term. A missing context
entry has no represented type; execution laws require an actually typed term
and therefore never use that branch as a successful source collector result. -/
def termAtoms (positions : List Ty) : DBTerm → List Atom
  | .free sourceVariable => typeAtoms sourceVariable.ty
  | .const _ type => typeAtoms type
  | .bound index => ((positions[index]?).map typeAtoms).getD []
  | .abs domain body => Transitivity.union (typeAtoms domain) (termAtoms (domain :: positions) body)
  | .app function argument => Transitivity.union (termAtoms positions function) (termAtoms positions argument)

theorem term_atoms_nodup (positions : List Ty) (term : DBTerm) : (termAtoms positions term).Nodup := by
  induction term generalizing positions with
  | free sourceVariable => exact type_atoms_nodup sourceVariable.ty
  | const constant type => exact type_atoms_nodup type
  | bound index =>
      cases found : positions[index]? with
      | none => simp [termAtoms, found]
      | some type => simpa [termAtoms, found] using type_atoms_nodup type
  | abs domain body ih => exact union_nodup (typeAtoms domain) _ (ih (domain :: positions))
  | app function argument _ ih => exact union_nodup _ _ (ih positions)

def annotationVariables (positions : List Ty) : DBTerm → Finset Name
  | .free sourceVariable => sourceVariable.ty.typeVariables
  | .const _ type => type.typeVariables
  | .bound index => ((positions[index]?).map Ty.typeVariables).getD ∅
  | .abs domain body => domain.typeVariables ∪ annotationVariables (domain :: positions) body
  | .app function argument => annotationVariables positions function ∪ annotationVariables positions argument

theorem term_atoms_support (positions : List Ty) (term : DBTerm) :
    (termAtoms positions term).toFinset = (annotationVariables positions term).image nameAtom := by
  induction term generalizing positions with
  | free sourceVariable =>
      simpa only [termAtoms, annotationVariables] using type_atoms_support sourceVariable.ty
  | const constant type =>
      simpa only [termAtoms, annotationVariables] using type_atoms_support type
  | bound index =>
      cases found : positions[index]? with
      | none => simp [termAtoms, annotationVariables, found]
      | some type => simpa [termAtoms, annotationVariables, found] using type_atoms_support type
  | abs domain body ih =>
      rw [termAtoms, union_support, type_atoms_support domain, ih (domain :: positions),
        annotationVariables, Finset.image_union]
  | app function argument functionIH argumentIH =>
      rw [termAtoms, union_support, functionIH positions, argumentIH positions,
        annotationVariables, Finset.image_union]

private theorem selected_type_mem (positions : List Ty) (index : Nat) (type : Ty)
    (found : positions[index]? = some type) : type ∈ positions := by
  induction positions generalizing index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero =>
          have equal : first = type := by simpa using found
          subst type
          exact List.mem_cons_self
      | succ index =>
          exact List.mem_cons_of_mem _ (ih index (by simpa using found))

/-- Context annotations can add only parameters of the current binder
context. Every parameter already displayed in the canonical term remains. -/
theorem annotation_variables_bounds (positions : List Ty) (term : DBTerm) :
    term.typeVariables ⊆ annotationVariables positions term ∧
      annotationVariables positions term ⊆ term.typeVariables ∪ Ty.typeVariablesList positions := by
  induction term generalizing positions with
  | free sourceVariable =>
      simp only [DBTerm.typeVariables, annotationVariables]
      exact ⟨Finset.Subset.refl _, Finset.subset_union_left⟩
  | const constant type =>
      simp only [DBTerm.typeVariables, annotationVariables]
      exact ⟨Finset.Subset.refl _, Finset.subset_union_left⟩
  | bound index =>
      simp only [DBTerm.typeVariables]
      refine ⟨Finset.empty_subset _, ?_⟩
      cases found : positions[index]? with
      | none => simp [annotationVariables, found]
      | some type =>
          intro name member
          have inType : name ∈ type.typeVariables := by
            simpa [annotationVariables, found] using member
          apply Finset.mem_union_right
          exact (SignatureFormation.mem_typeVariablesList name positions).mpr
            ⟨type, selected_type_mem positions index type found, inType⟩
  | abs domain body ih =>
      simp only [DBTerm.typeVariables, annotationVariables]
      obtain ⟨retained, bounded⟩ := ih (domain :: positions)
      constructor
      · intro name member
        rcases Finset.mem_union.mp member with inDomain | inBody
        · exact Finset.mem_union_left _ inDomain
        · exact Finset.mem_union_right _ (retained inBody)
      · intro name member
        rcases Finset.mem_union.mp member with inDomain | inBody
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ inDomain)
        · rcases Finset.mem_union.mp (bounded inBody) with inTerm | inContext
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ inTerm)
          · rw [Ty.typeVariablesList] at inContext
            rcases Finset.mem_union.mp inContext with inDomain | inOuter
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ inDomain)
            · exact Finset.mem_union_right _ inOuter
  | app function argument functionIH argumentIH =>
      simp only [DBTerm.typeVariables, annotationVariables]
      obtain ⟨functionRetained, functionBounded⟩ := functionIH positions
      obtain ⟨argumentRetained, argumentBounded⟩ := argumentIH positions
      constructor
      · intro name member
        rcases Finset.mem_union.mp member with inFunction | inArgument
        · exact Finset.mem_union_left _ (functionRetained inFunction)
        · exact Finset.mem_union_right _ (argumentRetained inArgument)
      · intro name member
        rcases Finset.mem_union.mp member with inFunction | inArgument
        · rcases Finset.mem_union.mp (functionBounded inFunction) with inTerm | inContext
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ inTerm)
          · exact Finset.mem_union_right _ inContext
        · rcases Finset.mem_union.mp (argumentBounded inArgument) with inTerm | inContext
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ inTerm)
          · exact Finset.mem_union_right _ inContext

/-- A closed representation accounts for all bound-annotation parameters in
its binder domains. Their support is precisely the shared definition guard. -/
theorem closed_annotation_variables (term : DBTerm) :
    annotationVariables [] term = term.typeVariables := by
  obtain ⟨retained, bounded⟩ := annotation_variables_bounds [] term
  apply Finset.Subset.antisymm
  · simpa [Ty.typeVariablesList] using bounded
  · exact retained

theorem closed_term_atoms_subset_iff (term : DBTerm) (schema : Ty) :
    termAtoms [] term ⊆ typeAtoms schema ↔ term.typeVariables ⊆ schema.typeVariables := by
  have support : (termAtoms [] term).toFinset = term.typeVariables.image nameAtom := by
    rw [term_atoms_support, closed_annotation_variables]
  constructor
  · intro included name member
    have represented : nameAtom name ∈ termAtoms [] term := by
      apply List.mem_toFinset.mp
      rw [support]
      exact Finset.mem_image.mpr ⟨name, member, rfl⟩
    exact (mem_type_atoms name schema).mp (included represented)
  · intro included atom member
    have represented : atom ∈ term.typeVariables.image nameAtom := by
      rw [← support]
      exact List.mem_toFinset.mpr member
    obtain ⟨name, parameter, rfl⟩ := Finset.mem_image.mp represented
    exact (mem_type_atoms name schema).mpr (included parameter)

private def typeEquation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:type-vars"))[0]'(by decide)
private def listEquation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:type-vars-list"))[0]'(by decide)
private def variableBody : Atom := .expression [.symbol "HOL:Cons", .var "name", .symbol "HOL:Nil"]
private def operatorBody : Atom := .expression [.symbol "hol-light:type-vars-list", .var "arguments"]
private def listBody : Atom := .expression [.symbol "hol-light:union",
  .expression [.symbol "hol-light:type-vars", .var "first"],
  .expression [.symbol "hol-light:type-vars-list", .var "rest"]]
private def typeCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Tyvar", .var "name"], variableBody),
   (.expression [.symbol "Tyapp", .var "operator", .var "arguments"], operatorBody),
   (.var "malformed", .symbol "None")]
private def listCases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .symbol "HOL:Nil"),
   (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], listBody),
   (.var "malformed", .symbol "None")]
private def typeEnvironment (operators : TypeOp → Atom) (type : Ty) : Subst :=
  [("type", typeAtom operators type)]
private def listEnvironment (operators : TypeOp → Atom) (types : List Ty) : Subst :=
  [("types", Premises.keys (types.map (typeAtom operators)))]

private theorem type_shape : typeEquation.body = .expression [.symbol "case", .var "type",
    .expression (typeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem list_shape : listEquation.body = .expression [.symbol "case", .var "types",
    .expression (listCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem type_clause (operators : TypeOp → Atom) (type : Ty) :
    clauses program "hol-light:type-vars" [typeAtom operators type] =
      [.evaluate (typeEnvironment operators type) typeEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:type-vars") = [typeEquation] := rfl
  rw [unique]
  have formals : typeEquation.arguments = [.var "type"] := by decide
  simp [formals, typeEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem list_clause (operators : TypeOp → Atom) (types : List Ty) :
    clauses program "hol-light:type-vars-list" [Premises.keys (types.map (typeAtom operators))] =
      [.evaluate (listEnvironment operators types) listEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:type-vars-list") = [listEquation] := rfl
  rw [unique]
  have formals : listEquation.arguments = [.var "types"] := by decide
  simp [formals, listEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

mutual
  private theorem type_body_certificate (operators : TypeOp → Atom) (type : Ty) (state : State) :
      BoundCalls.CorePath.PureReturns program (typeEnvironment operators type)
        state typeEquation.body state (Premises.keys (typeAtoms type)) := by
    rw [type_shape]
    cases type with
    | var name =>
        let before := typeEnvironment operators (.var name)
        let bound := ("name", nameAtom name) :: before
        apply BoundCalls.CorePath.case_returns program before bound state state state (.var "type")
          (typeAtom operators (.var name)) variableBody _ _ typeCases (read_cases_encoded typeCases)
        · exact BoundCalls.CorePath.variable_returns program before state "type"
        · simp [typeCases, before, bound, typeEnvironment, typeAtom, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold variableBody
          simp only [typeAtoms, Premises.keys]
          apply BoundCalls.CorePath.constructor_return program bound state "HOL:Cons" _ _
            (by decide) (by decide)
          refine .cons ?_ (.cons (BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil") .nil)
          simpa [typeAtoms, bound, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program bound state "name"
    | op operator arguments =>
        let before := typeEnvironment operators (.op operator arguments)
        let bound := [("arguments", Premises.keys (arguments.map (typeAtom operators))),
          ("operator", operators operator)] ++ before
        apply BoundCalls.CorePath.case_returns program before bound state state state (.var "type")
          (typeAtom operators (.op operator arguments)) operatorBody _ _ typeCases (read_cases_encoded typeCases)
        · exact BoundCalls.CorePath.variable_returns program before state "type"
        · simp [typeCases, before, bound, typeEnvironment, typeAtom, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold operatorBody
          simp only [typeAtoms]
          apply BoundCalls.CorePath.authored_variable_call_returns program bound (listEnvironment operators arguments)
            state state "hol-light:type-vars-list" ["arguments"] listEquation.body _
            (by decide) (by decide) (by decide) _
            (list_body_certificate operators arguments state) (by decide)
          simpa [bound, applySubst, Subst.lookup] using list_clause operators arguments
  termination_by sizeOf type

  private theorem list_body_certificate (operators : TypeOp → Atom) (types : List Ty) (state : State) :
      BoundCalls.CorePath.PureReturns program (listEnvironment operators types)
        state listEquation.body state (Premises.keys (typesAtoms types)) := by
    rw [list_shape]
    cases types with
    | nil =>
        apply BoundCalls.CorePath.case_returns program (listEnvironment operators []) (listEnvironment operators [])
          state state state (.var "types") (.symbol "HOL:Nil") (.symbol "HOL:Nil") _ _ listCases
          (read_cases_encoded listCases)
        · exact BoundCalls.CorePath.variable_returns program _ state "types"
        · simp [listCases, listEnvironment, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa only [typesAtoms, Premises.keys] using
            BoundCalls.CorePath.symbol_returns program (listEnvironment operators []) state "HOL:Nil"
    | cons first rest =>
        let before := listEnvironment operators (first :: rest)
        let bound := [("rest", Premises.keys (rest.map (typeAtom operators))),
          ("first", typeAtom operators first)] ++ before
        apply BoundCalls.CorePath.case_returns program before bound state state state (.var "types")
          (Premises.keys ((first :: rest).map (typeAtom operators))) listBody _ _ listCases
          (read_cases_encoded listCases)
        · exact BoundCalls.CorePath.variable_returns program before state "types"
        · simp [listCases, before, bound, listEnvironment, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold listBody
          simp only [typesAtoms, Transitivity.union]
          apply ListOperations.Union.authored_union_computed_certificate bound state
            (typeAtoms first) (typesAtoms rest)
          · apply BoundCalls.CorePath.authored_variable_call_returns program bound (typeEnvironment operators first)
              state state "hol-light:type-vars" ["first"] typeEquation.body _
              (by decide) (by decide) (by decide) _ (type_body_certificate operators first state) (by decide)
            simpa [bound, applySubst, Subst.lookup] using type_clause operators first
          · apply BoundCalls.CorePath.authored_variable_call_returns program bound (listEnvironment operators rest)
              state state "hol-light:type-vars-list" ["rest"] listEquation.body _
              (by decide) (by decide) (by decide) _ (list_body_certificate operators rest state) (by decide)
            simpa [bound, applySubst, Subst.lookup] using list_clause operators rest
  termination_by sizeOf types
end

/-- A certificate for the actual type collector composes with captured
authored helpers as well as with the original source execution relation. -/
theorem authored_type_vars_certificate (operators : TypeOp → Atom) (type : Ty)
    (bindings : Subst) (state : State) (key : String)
    (captured : applySubst bindings (.var key) = typeAtom operators type) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-vars", .var key]) state (Premises.keys (typeAtoms type)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (typeEnvironment operators type)
    state state "hol-light:type-vars" [key] typeEquation.body _
    (by decide) (by decide) (by decide) _ (type_body_certificate operators type state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using type_clause operators type

theorem authored_types_vars_certificate (operators : TypeOp → Atom) (types : List Ty)
    (bindings : Subst) (state : State) (key : String)
    (captured : applySubst bindings (.var key) = Premises.keys (types.map (typeAtom operators))) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-vars-list", .var key]) state (Premises.keys (typesAtoms types)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (listEnvironment operators types)
    state state "hol-light:type-vars-list" [key] listEquation.body _
    (by decide) (by decide) (by decide) _ (list_body_certificate operators types state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using list_clause operators types

private def termEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:term-type-vars"))[0]'(by decide)
private def annotationBody : Atom := .expression [.symbol "hol-light:type-vars", .var "type"]
private def lambdaBody : Atom := .expression [.symbol "hol-light:union",
  .expression [.symbol "hol-light:type-vars", .var "type"],
  .expression [.symbol "hol-light:term-type-vars", .var "body"]]
private def applicationBody : Atom := .expression [.symbol "hol-light:union",
  .expression [.symbol "hol-light:term-type-vars", .var "function"],
  .expression [.symbol "hol-light:term-type-vars", .var "argument"]]
private def termCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "HOL:Free", .var "name", .var "type"], annotationBody),
   (.expression [.symbol "HOL:Bound", .var "index", .var "type"], annotationBody),
   (.expression [.symbol "HOL:C", .var "identity", .var "type"], annotationBody),
   (.expression [.symbol "HOL:Lam", .var "type", .var "body"], lambdaBody),
   (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
   (.var "malformed", .symbol "None")]
private def termEnvironment (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (term : DBTerm) : Subst :=
  [("term", Representation.termAtom operators constants positions term)]

private theorem term_shape : termEquation.body = .expression [.symbol "case", .var "term",
    .expression (termCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_clause (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (term : DBTerm) :
    clauses program "hol-light:term-type-vars" [Representation.termAtom operators constants positions term] =
      [.evaluate (termEnvironment operators constants positions term) termEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:term-type-vars") = [termEquation] := rfl
  rw [unique]
  have formals : termEquation.arguments = [.var "term"] := by decide
  simp [formals, termEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem term_body_certificate (operators : TypeOp → Atom) (constants : Const → Atom)
    (term : DBTerm) (positions : List Ty) (type : Ty)
    (checked : term.inferType positions = some type) (state : State) :
    BoundCalls.CorePath.PureReturns program (termEnvironment operators constants positions term)
      state termEquation.body state (Premises.keys (termAtoms positions term)) := by
  rw [term_shape]
  cases term with
  | free sourceVariable =>
      let before := termEnvironment operators constants positions (.free sourceVariable)
      let bound := [("type", typeAtom operators sourceVariable.ty),
        ("name", nameAtom sourceVariable.name)] ++ before
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (Representation.termAtom operators constants positions (.free sourceVariable))
        annotationBody _ _ termCases (read_cases_encoded termCases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [termCases, before, bound, termEnvironment, Representation.termAtom,
          Representation.variableAtom, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [annotationBody, termAtoms] using
          authored_type_vars_certificate operators sourceVariable.ty bound state "type"
            (by simp [bound, applySubst, Subst.lookup])
  | bound index =>
      have found : positions[index]? = some type := by simpa using checked
      let before := termEnvironment operators constants positions (.bound index)
      let bound := [("type", typeAtom operators type), ("index", Atom.grounded (.int index))] ++ before
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (Representation.termAtom operators constants positions (.bound index))
        annotationBody _ _ termCases (read_cases_encoded termCases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [termCases, before, bound, termEnvironment, Representation.termAtom, found,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [annotationBody, termAtoms, found] using
          authored_type_vars_certificate operators type bound state "type"
            (by simp [bound, applySubst, Subst.lookup])
  | const constant annotation =>
      let before := termEnvironment operators constants positions (.const constant annotation)
      let bound := [("type", typeAtom operators annotation), ("identity", constants constant)] ++ before
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (Representation.termAtom operators constants positions (.const constant annotation))
        annotationBody _ _ termCases (read_cases_encoded termCases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [termCases, before, bound, termEnvironment, Representation.termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [annotationBody, termAtoms] using
          authored_type_vars_certificate operators annotation bound state "type"
            (by simp [bound, applySubst, Subst.lookup])
  | abs domain body =>
      obtain ⟨codomain, bodyChecked, rfl⟩ := DBTerm.inferType_abs_eq_some_iff.mp checked
      let before := termEnvironment operators constants positions (.abs domain body)
      let bound := [("body", Representation.termAtom operators constants (domain :: positions) body),
        ("type", typeAtom operators domain)] ++ before
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (Representation.termAtom operators constants positions (.abs domain body))
        lambdaBody _ _ termCases (read_cases_encoded termCases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [termCases, before, bound, termEnvironment, Representation.termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold lambdaBody
        simp only [termAtoms, Transitivity.union]
        apply ListOperations.Union.authored_union_computed_certificate bound state
          (typeAtoms domain) (termAtoms (domain :: positions) body)
        · exact authored_type_vars_certificate operators domain bound state "type"
            (by simp [bound, applySubst, Subst.lookup])
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound
            (termEnvironment operators constants (domain :: positions) body) state state
            "hol-light:term-type-vars" ["body"] termEquation.body _
            (by decide) (by decide) (by decide) _
            (term_body_certificate operators constants body (domain :: positions) codomain bodyChecked state) (by decide)
          simpa [bound, applySubst, Subst.lookup] using term_clause operators constants (domain :: positions) body
  | app function argument =>
      obtain ⟨domain, functionChecked, argumentChecked⟩ := DBTerm.inferType_app_eq_some_iff.mp checked
      let before := termEnvironment operators constants positions (.app function argument)
      let bound := [("argument", Representation.termAtom operators constants positions argument),
        ("function", Representation.termAtom operators constants positions function)] ++ before
      apply BoundCalls.CorePath.case_returns program before bound state state state (.var "term")
        (Representation.termAtom operators constants positions (.app function argument))
        applicationBody _ _ termCases (read_cases_encoded termCases)
      · exact BoundCalls.CorePath.variable_returns program before state "term"
      · simp [termCases, before, bound, termEnvironment, Representation.termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold applicationBody
        simp only [termAtoms, Transitivity.union]
        apply ListOperations.Union.authored_union_computed_certificate bound state
          (termAtoms positions function) (termAtoms positions argument)
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound
            (termEnvironment operators constants positions function) state state
            "hol-light:term-type-vars" ["function"] termEquation.body _
            (by decide) (by decide) (by decide) _
            (term_body_certificate operators constants function positions (.function domain type) functionChecked state) (by decide)
          simpa [bound, applySubst, Subst.lookup] using term_clause operators constants positions function
        · apply BoundCalls.CorePath.authored_variable_call_returns program bound
            (termEnvironment operators constants positions argument) state state
            "hol-light:term-type-vars" ["argument"] termEquation.body _
            (by decide) (by decide) (by decide) _
            (term_body_certificate operators constants argument positions domain argumentChecked state) (by decide)
          simpa [bound, applySubst, Subst.lookup] using term_clause operators constants positions argument

/-- Actual term-annotation collection for every typed positional term. The
typing premise supplies genuine bound annotations and does not admit declarations. -/
theorem authored_term_type_vars_certificate (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (term : DBTerm) (type : Ty)
    (checked : term.inferType positions = some type) (bindings : Subst) (state : State) (key : String)
    (captured : applySubst bindings (.var key) = Representation.termAtom operators constants positions term) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type-vars", .var key]) state
      (Premises.keys (termAtoms positions term)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (termEnvironment operators constants positions term) state state
    "hol-light:term-type-vars" [key] termEquation.body _
    (by decide) (by decide) (by decide) _
    (term_body_certificate operators constants term positions type checked state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using term_clause operators constants positions term

/-- The authored definition guard computes exactly the existing hidden-type
parameter condition, while executing both retained collectors and inclusion. -/
theorem authored_hidden_parameters_certificate (operators : TypeOp → Atom) (constants : Const → Atom)
    (term : DBTerm) (schema : Ty) (checked : term.inferType [] = some schema)
    (bindings : Subst) (state : State) (bodyKey schemaKey : String)
    (bodyCaptured : applySubst bindings (.var bodyKey) = Representation.termAtom operators constants [] term)
    (schemaCaptured : applySubst bindings (.var schemaKey) = typeAtom operators schema) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:subset",
        .expression [.symbol "hol-light:term-type-vars", .var bodyKey],
        .expression [.symbol "hol-light:type-vars", .var schemaKey]]) state
      (Effects.boolean (decide (term.typeVariables ⊆ schema.typeVariables))) := by
  have collected := ListOperations.Subset.authored_subset_computed_certificate bindings state
    (termAtoms [] term) (typeAtoms schema) _ _
    (authored_term_type_vars_certificate operators constants [] term schema checked bindings state bodyKey bodyCaptured)
    (authored_type_vars_certificate operators schema bindings state schemaKey schemaCaptured)
  simpa only [closed_term_atoms_subset_iff] using collected

/-- The preceding closed-body check evaluates the actual free-variable
collector and compares its complete result with the empty source list. -/
theorem authored_closed_body_certificate (operators : TypeOp → Atom) (constants : Const → Atom)
    (positions : List Ty) (term : DBTerm) (bindings : Subst) (state : State) (bodyKey : String)
    (bodyCaptured : applySubst bindings (.var bodyKey) = Representation.termAtom operators constants positions term) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "==", .expression [.symbol "hol-light:free-vars", .var bodyKey], .symbol "HOL:Nil"])
      state (Effects.boolean (decide (FreeVariables.freeAtoms operators term = []))) := by
  apply BoundCalls.CorePath.native_binary_call_returns program bindings state state state state "==" _ _
    (Premises.keys (FreeVariables.freeAtoms operators term)) (.symbol "HOL:Nil") _
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · exact FreeVariables.authored_free_vars_certificate operators constants term positions bindings state bodyKey bodyCaptured
  · exact BoundCalls.CorePath.symbol_returns program bindings state "HOL:Nil"
  · cases FreeVariables.freeAtoms operators term <;> simp [Premises.keys, StdLib.structural_equality, Effects.boolean]

/-- A closed, typed application can still hide a parameter absent from its
result type. Declaration formation does not replace the definition guard. -/
def hiddenParameterTerm (parameter : Name) (function argument : Const) : DBTerm :=
  .app (.const function (.function (.var parameter) .bool)) (.const argument (.var parameter))

theorem hidden_parameter_typed (parameter : Name) (function argument : Const) :
    (hiddenParameterTerm parameter function argument).inferType [] = some Ty.bool := by
  simp [hiddenParameterTerm, DBTerm.inferType, Ty.function, Ty.destFunction?, TypeOp.function]

theorem hidden_parameter_closed (parameter : Name) (function argument : Const) :
    (hiddenParameterTerm parameter function argument).HasNoFreeVariables :=
  .app .const .const

theorem hidden_parameter_refused (parameter : Name) (function argument : Const) :
    ¬ (hiddenParameterTerm parameter function argument).typeVariables ⊆ Ty.bool.typeVariables := by
  simp [hiddenParameterTerm, DBTerm.typeVariables, Ty.typeVariables, Ty.typeVariablesList, Ty.function, Ty.bool]

theorem identity_parameters_admitted (parameter : Name) :
    (DBTerm.abs (.var parameter) (.bound 0)).typeVariables ⊆
      (Ty.function (.var parameter) (.var parameter)).typeVariables := by
  simp [DBTerm.typeVariables, Ty.typeVariables, Ty.typeVariablesList, Ty.function]

end Mettapedia.Languages.HOLLight.MeTTa.TypeVariables
