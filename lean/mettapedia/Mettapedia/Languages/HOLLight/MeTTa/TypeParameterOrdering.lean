import Mettapedia.Languages.HOLLight.MeTTa.NameSorting

/-!
# Constructed parameters of an authored type-definition event

For the HOL Light string-name fragment, the actual annotation collector,
native sorting and type-parameter constructor produce a distinct list with
exactly the predicate's parameters. Scoped private names are not silently
converted to strings. The retained source representation supplies the order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeParameterOrdering

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval (clauses clauses_use_only_the_named_equations read_cases_encoded)
open Effects (State)
open TypeSubstitution (nameAtom typeAtom)

def globalParameters (term : DBTerm) : Prop :=
  ∀ name ∈ term.typeVariables, ∃ text, name = Name.global text

private theorem string_list_of_members (atoms : List Atom)
    (strings : ∀ atom ∈ atoms, ∃ text, atom = .grounded (.string text)) :
    ∃ texts, atoms = StdLib.stringAtoms texts := by
  induction atoms with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨text, rfl⟩ := strings first List.mem_cons_self
      obtain ⟨texts, represented⟩ := ih (fun atom member => strings atom (List.mem_cons_of_mem _ member))
      exact ⟨text :: texts, by simp [StdLib.stringAtoms, represented]⟩

/-- A string list is constructed from the actual collector output and its
scope condition; no hypothetical successful source collector is assumed. -/
theorem collector_string_list (term : DBTerm) (global : globalParameters term) :
    ∃ texts, TypeVariables.termAtoms [] term = StdLib.stringAtoms texts ∧ texts.Nodup ∧
      (texts.map Name.global).toFinset = term.typeVariables := by
  have support : (TypeVariables.termAtoms [] term).toFinset = term.typeVariables.image nameAtom := by
    rw [TypeVariables.term_atoms_support, TypeVariables.closed_annotation_variables]
  have stringMembers : ∀ atom ∈ TypeVariables.termAtoms [] term, ∃ text, atom = .grounded (.string text) := by
    intro atom member
    have imageMember : atom ∈ term.typeVariables.image nameAtom := by
      rw [← support]
      exact List.mem_toFinset.mpr member
    obtain ⟨name, parameter, rfl⟩ := Finset.mem_image.mp imageMember
    obtain ⟨text, rfl⟩ := global name parameter
    exact ⟨text, rfl⟩
  obtain ⟨texts, represented⟩ := string_list_of_members _ stringMembers
  refine ⟨texts, represented, ?_, ?_⟩
  · have distinct := TypeVariables.term_atoms_nodup [] term
    rw [represented] at distinct
    exact List.Nodup.of_map _ distinct
  · apply Finset.image_injective TypeSubstitution.nameAtom_injective
    rw [← support, represented]
    simp only [StdLib.stringAtoms, List.toFinset_map, Finset.image_image]
    rfl

namespace Parameters

def atoms (texts : List String) : List Atom :=
  texts.map fun text => typeAtom Representation.registeredOperatorAtom (.var (Name.global text))

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:type-parameters"))[0]'(by decide)
private def consBody : Atom := .expression [.symbol "HOL:Cons", .expression [.symbol "Tyvar", .var "name"],
  .expression [.symbol "hol-light:type-parameters", .var "rest"]]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .symbol "HOL:Nil"),
   (.expression [.symbol "HOL:Cons", .var "name", .var "rest"], consBody),
   (.var "malformed", .symbol "None")]
private def environment (texts : List String) : Subst := [("names", Premises.keys (StdLib.stringAtoms texts))]
private def consEnvironment (text : String) (rest : List String) : Subst :=
  [("rest", Premises.keys (StdLib.stringAtoms rest)), ("name", .grounded (.string text))] ++ environment (text :: rest)
private theorem shape : equation.body = .expression [.symbol "case", .var "names",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (texts : List String) :
    clauses program "hol-light:type-parameters" [Premises.keys (StdLib.stringAtoms texts)] =
      [.evaluate (environment texts) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:type-parameters") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.var "names"] := by decide
  simp [List.filterMap, formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (texts : List String) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment texts) state equation.body state (Premises.keys (atoms texts)) := by
  induction texts with
  | nil =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment []) (environment []) state state state
        (.var "names") (.symbol "HOL:Nil") (.symbol "HOL:Nil") _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "names"
      · simp [cases, environment, StdLib.stringAtoms, Premises.keys, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.symbol_returns program _ state "HOL:Nil"
  | cons text rest ih =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment (text :: rest)) (consEnvironment text rest)
        state state state (.var "names") (Premises.keys (StdLib.stringAtoms (text :: rest))) consBody _ _ cases
        (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "names"
      · simp [cases, consEnvironment, environment, StdLib.stringAtoms, Premises.keys, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.binary_constructor_returns program (consEnvironment text rest) state state state
          "HOL:Cons" (.expression [.symbol "Tyvar", .var "name"])
          (.expression [.symbol "hol-light:type-parameters", .var "rest"])
          (typeAtom Representation.registeredOperatorAtom (.var (Name.global text))) (Premises.keys (atoms rest))
          (by decide) (by decide)
        · simpa [consEnvironment, typeAtom, nameAtom, Name.global, applySubst, Subst.lookup] using
            BoundCalls.CorePath.unary_constructor_returns program (consEnvironment text rest) state "Tyvar" "name"
              (by decide) (by decide)
        · apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment text rest)
            (environment rest) state state "hol-light:type-parameters" ["rest"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [consEnvironment, applySubst, Subst.lookup] using clause rest

theorem authored_certificate (bindings : Subst) (state : State) (texts : List String) (expression : Atom)
    (returned : BoundCalls.CorePath.PureReturns program bindings state expression state (Premises.keys (StdLib.stringAtoms texts))) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:type-parameters", expression]) state (Premises.keys (atoms texts)) :=
  BoundCalls.CorePath.authored_unary_call_returns program bindings (environment texts) state state state
    "hol-light:type-parameters" expression (Premises.keys (StdLib.stringAtoms texts)) equation.body _
    (by decide) (by decide) (by decide) (by decide) returned (clause texts) (body_returns texts state) (by decide)

end Parameters

/-- The complete authored parameter path constructs the exact ordered list
used by registered HOL Light admission, including its source provenance. -/
theorem authored_admission_parameters (constants : Const → Atom) (body : CheckedSourceTerm)
    (global : globalParameters body.canonical.term)
    (bindings : Subst) (state : State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants [] body.canonical.term) :
    ∃ texts, texts.map Name.global = DefinitionAdapters.sortedParameters body.source ∧
      BoundCalls.CorePath.PureReturns program bindings state
        (.expression [.symbol "hol-light:type-parameters", .expression [.symbol "hol-light:sorted-names",
          .expression [.symbol "hol-light:term-type-vars", .var termKey]]]) state
        (Premises.keys (Parameters.atoms texts)) := by
  obtain ⟨texts, represented, distinct, support⟩ := collector_string_list body.canonical.term global
  refine ⟨NameSorting.sorted texts, ?_, ?_⟩
  · exact DefinitionAdapters.sortedParameters_of_global_strings body.source texts distinct support
  · apply Parameters.authored_certificate
    apply NameSorting.authored_sorted_certificate
    have collected := TypeVariables.authored_term_type_vars_certificate Representation.registeredOperatorAtom constants
      [] body.canonical.term body.ty body.canonical.checked bindings state termKey captured
    simpa only [represented] using collected

/-- The actual source collector, sort and parameter constructor produce
the same distinct parameter support required by shared type admission. -/
theorem authored_parameters_constructed (constants : Const → Atom) (term : DBTerm) (type : Ty)
    (typed : term.inferType [] = some type) (global : globalParameters term)
    (bindings : Subst) (state : State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants [] term) :
    ∃ texts, (texts.map Name.global).Nodup ∧ (texts.map Name.global).toFinset = term.typeVariables ∧
      BoundCalls.CorePath.PureReturns program bindings state
        (.expression [.symbol "hol-light:type-parameters", .expression [.symbol "hol-light:sorted-names",
          .expression [.symbol "hol-light:term-type-vars", .var termKey]]]) state (Premises.keys (Parameters.atoms texts)) := by
  obtain ⟨texts, represented, distinct, support⟩ := collector_string_list term global
  refine ⟨NameSorting.sorted texts, ?_, ?_, ?_⟩
  · exact (NameSorting.sorted_nodup texts distinct).map
      (by intro left right equal; exact congrArg Name.component equal)
  · simpa only [List.toFinset_map, NameSorting.sorted_support] using support
  · apply Parameters.authored_certificate
    apply NameSorting.authored_sorted_certificate
    have collected := TypeVariables.authored_term_type_vars_certificate Representation.registeredOperatorAtom constants
      [] term type typed bindings state termKey captured
    simpa only [represented] using collected

end Mettapedia.Languages.HOLLight.MeTTa.TypeParameterOrdering
