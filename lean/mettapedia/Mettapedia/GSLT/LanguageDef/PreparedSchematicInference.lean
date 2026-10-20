import Mettapedia.GSLT.LanguageDef.SortedFirstOrderAdmission

/-!
# Prepared, scoped schematic inference

Rule formals are numbered once when a rule is installed. An invocation supplies
one typed argument vector, and the checker substitutes it into every premise
and the conclusion. This is the existing many-sorted inference judgment with
a different instantiation algorithm, not an additional rule of inference.

Arguments may contain variables from the ambient context. A two-sided unifier,
one-sided matcher, or explicit author can produce them; none is trusted merely
because it supplied a vector. The checker verifies sorts, scope and agreement
with the supplied premise judgments. This module does not impose a search
strategy or certify that a producer enumerated every possible instance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PreparedSchematicInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open SortedFirstOrderRules WellSorted

/-- Installed templates use positions rather than run-time metavariable names. -/
structure PreparedRule where
  arity : Nat
  variableTypes : List TypeExpr
  premises : List Pattern
  conclusion : Pattern
  deriving Repr

def prepare (rule : Rule) : PreparedRule where
  arity := rule.row.vars.length
  variableTypes := rule.variableTypes
  premises := rule.row.premises.map (numbered rule.row.vars)
  conclusion := numbered rule.row.vars rule.row.conclusion

def prepare? (language : LanguageDef) (judgments : List String) (rule : Rule) :
    Option PreparedRule :=
  if rule.check language judgments then some (prepare rule) else none

theorem prepare?_iff (language : LanguageDef) (judgments : List String) (rule : Rule) :
    prepare? language judgments rule = some (prepare rule) ↔ rule.WellFormed language judgments := by
  simp [prepare?, Rule.check_iff]

def instantiatePremises (rule : PreparedRule) (arguments : List Pattern) : List Pattern :=
  substituteList (argumentAt arguments) rule.premises

def instantiateConclusion (rule : PreparedRule) (arguments : List Pattern) : Pattern :=
  substitute (argumentAt arguments) rule.conclusion

/-- Only the installed rule and the caller's scoped data are used. The provided
premises can be conclusions of retained theorem handles or checked DAG nodes. -/
def apply? (language : LanguageDef) (context : List TypeExpr)
    (rule : PreparedRule) (arguments premises : List Pattern) : Option Pattern :=
  if arguments.length = rule.arity ∧
      checkArgumentTypes language context arguments rule.variableTypes = true ∧
      premises = instantiatePremises rule arguments then
    some (instantiateConclusion rule arguments)
  else none

/-- The source rule-instance relation, using its authored named templates. -/
def Instance (language : LanguageDef) (context : List TypeExpr) (rule : Rule)
    (arguments premises : List Pattern) (conclusion : Pattern) : Prop :=
  arguments.length = rule.row.vars.length ∧
    List.Forall₂ (fun argument type =>
      HasType language FreeTypeContext.empty context argument type)
      arguments rule.variableTypes ∧
    (∀ argument ∈ arguments, isMatchCorrectAux argument = true) ∧
    premises = rule.row.instPremises arguments ∧
    conclusion = rule.row.instConclusion arguments

theorem prepared_premises {language : LanguageDef} {judgments : List String} {rule : Rule}
    (formed : rule.WellFormed language judgments) (arguments : List Pattern)
    (arity : arguments.length = rule.row.vars.length) :
    instantiatePremises (prepare rule) arguments = rule.row.instPremises arguments :=
  (formed.instPremises_numbered arguments arity).symm

theorem prepared_conclusion {language : LanguageDef} {judgments : List String} {rule : Rule}
    (formed : rule.WellFormed language judgments) (arguments : List Pattern)
    (arity : arguments.length = rule.row.vars.length) :
    instantiateConclusion (prepare rule) arguments = rule.row.instConclusion arguments :=
  (formed.instConclusion_numbered arguments arity).symm

/-- Exact local checking: precompilation changes neither accepted instances nor
their ordered premises, including repeated premise occurrences. -/
theorem apply?_iff {language : LanguageDef} {judgments : List String} {rule : Rule}
    (formed : rule.WellFormed language judgments) (context : List TypeExpr)
    (arguments premises : List Pattern) (conclusion : Pattern) :
    apply? language context (prepare rule) arguments premises = some conclusion ↔
      Instance language context rule arguments premises conclusion := by
  unfold apply? Instance
  constructor
  · intro accepted
    split at accepted
    · next good =>
        obtain ⟨arity, typed, samePremises⟩ := good
        obtain ⟨typed, fragment⟩ := (checkArgumentTypes_iff _ _ _ _).mp typed
        exact ⟨arity, typed, fragment,
          samePremises.trans (prepared_premises formed arguments arity),
          (Option.some.inj accepted).symm.trans (prepared_conclusion formed arguments arity)⟩
    · contradiction
  · rintro ⟨arity, typed, fragment, samePremises, sameConclusion⟩
    have checked := (checkArgumentTypes_iff language context arguments rule.variableTypes).mpr
      ⟨typed, fragment⟩
    simp only [prepare, arity, checked, true_and]
    change (if premises = instantiatePremises (prepare rule) arguments then
      some (instantiateConclusion (prepare rule) arguments) else none) = some conclusion
    rw [prepared_premises formed arguments arity, prepared_conclusion formed arguments arity]
    simp [samePremises, sameConclusion]

theorem Instance.derives {language : LanguageDef} {rules : List Rule}
    {context : List TypeExpr} {hypotheses : List Pattern} {rule : Rule}
    {arguments premises : List Pattern} {conclusion : Pattern}
    (instance' : Instance language context rule arguments premises conclusion)
    (installed : rule ∈ rules)
    (children : ∀ premise ∈ premises, Derives language rules context hypotheses premise) :
    Derives language rules context hypotheses conclusion := by
  obtain ⟨arity, typed, fragment, rfl, rfl⟩ := instance'
  exact .rule installed arguments arity typed fragment children

theorem accepted_derives {language : LanguageDef} {judgments : List String}
    {rules : List Rule} {rule : Rule} (formed : rule.WellFormed language judgments)
    {context : List TypeExpr} {hypotheses arguments premises : List Pattern}
    {conclusion : Pattern}
    (accepted : apply? language context (prepare rule) arguments premises = some conclusion)
    (installed : rule ∈ rules)
    (children : ∀ premise ∈ premises, Derives language rules context hypotheses premise) :
    Derives language rules context hypotheses conclusion :=
  ((apply?_iff formed _ _ _ _).mp accepted).derives installed children

theorem argumentAt_wellScoped {context types : List TypeExpr} {arguments : List Pattern}
    {language : LanguageDef}
    (typed : List.Forall₂ (fun argument type =>
      HasType language FreeTypeContext.empty context argument type) arguments types) :
    WellScopedAssignment arguments.length context.length (argumentAt arguments) := by
  intro index bound
  induction typed generalizing index with
  | nil => simp at bound
  | @cons argument type arguments types first rest ih =>
      cases index with
      | zero => simpa [argumentAt] using first.isWellScopedAt
      | succ index =>
          have inTail : index < arguments.length := by simpa using bound
          simpa [argumentAt, List.getElem?_eq_getElem inTail] using ih index inTail

/-- No ambient variable can escape the supplied context through a prepared
conclusion. The proof uses the same substitution law as scoped object terms. -/
theorem Instance.conclusion_scoped {language : LanguageDef} {judgments : List String}
    {rule : Rule} (formed : rule.WellFormed language judgments)
    {context : List TypeExpr} {arguments premises : List Pattern} {conclusion : Pattern}
    (instance' : Instance language context rule arguments premises conclusion) :
    conclusion.isWellScopedAt context.length = true := by
  obtain ⟨arity, typed, _, _, rfl⟩ := instance'
  rw [formed.instConclusion_numbered arguments arity]
  obtain ⟨_, _, conclusionTyped⟩ := formed.conclusion
  apply substitute_wellScoped (source := rule.variableTypes.length)
  · have scopeOK := argumentAt_wellScoped typed
    simpa [arity, formed.arity] using scopeOK
  · exact conclusionTyped.isWellScopedAt

/-- Repeated premises are not deduplicated by installation. -/
theorem prepare_premise_count (rule : Rule) :
    (prepare rule).premises.length = rule.row.premises.length := by
  simp [prepare]

namespace Controls

private def constructor (name sort : String) (inputs : List (String × String)) : GrammarRule :=
  { label := name, category := sort,
    params := inputs.map (fun (argument, input) =>
      .simple argument (.base input)), syntaxPattern := [] }

def language : LanguageDef :=
  { name := "ScopedApplicativeInference"
    types := [TypeDecl.plain "term", TypeDecl.plain "type", TypeDecl.plain "judgment"]
    terms := [constructor "a" "term" [], constructor "A" "type" [], constructor "B" "type" [],
      constructor "arrow" "type" [("domain", "type"), ("result", "type")],
      constructor "app" "term" [("function", "term"), ("argument", "term")],
      constructor "hasType" "judgment" [("value", "term"), ("type", "type")]]
    equations := [], rewrites := [] }

def hasType (term type : Pattern) : Pattern := .apply "hasType" [term, type]
def arrow (domain result : Pattern) : Pattern := .apply "arrow" [domain, result]
def a : Pattern := .apply "a" []
def A : Pattern := .apply "A" []
def B : Pattern := .apply "B" []

def application : Rule where
  row :=
    { id := "application"
      vars := ["f", "x", "A", "B"]
      premises := [hasType (.fvar "f") (arrow (.fvar "A") (.fvar "B")),
        hasType (.fvar "x") (.fvar "A")]
      conclusion := hasType (.apply "app" [.fvar "f", .fvar "x"]) (.fvar "B") }
  variableTypes := [.base "term", .base "term", .base "type", .base "type"]

theorem application_formed : application.WellFormed language ["judgment"] :=
  (Rule.check_iff _ _ _).mp (by
    simp [Rule.check, application, language, constructor, checkBaseType,
      LanguageDef.typeNames, TypeDecl.plain, checkSchemas, checkSchema, checkStatement,
      numbered, numberedBindings, applyBindings, hasType, arrow,
      checkHasType, checkArgumentsHaveTypes, usesBareCollection?,
      parameterType?, matchesParameterRepresentation?, List.range_succ])

theorem application_prepares : prepare? language ["judgment"] application = some (prepare application) :=
  (prepare?_iff _ _ _).mpr application_formed

/-- An ambient variable is permitted; it need not be closed or freshly invented. -/
theorem scoped_application : apply? language [.base "term"] (prepare application) [.bvar 0, a, A, B]
    [hasType (.bvar 0) (arrow A B), hasType a A] =
      some (hasType (.apply "app" [.bvar 0, a]) B) := by
  simp [apply?, prepare, application, language, constructor, checkArgumentTypes,
    checkHasType, checkArgumentsHaveTypes, usesBareCollection?, a, A, B, hasType, arrow,
    instantiatePremises, instantiateConclusion, numbered, numberedBindings, applyBindings,
    substituteList, substitute, argumentAt, List.range_succ, isMatchCorrectAux, isMatchCorrectListAux]

/-- A forged variable outside that same context is refused. -/
theorem out_of_scope_refused : apply? language [.base "term"] (prepare application) [.bvar 1, a, A, B]
    [hasType (.bvar 1) (arrow A B), hasType a A] = none := by decide

/-- The two premises must use the same supplied domain. -/
theorem inconsistent_domain_refused : apply? language [.base "term"] (prepare application) [.bvar 0, a, A, B]
    [hasType (.bvar 0) (arrow A B), hasType a B] = none := by
  simp [apply?, prepare, application, language, constructor, checkArgumentTypes,
    checkHasType, checkArgumentsHaveTypes, usesBareCollection?, a, A, B, hasType, arrow,
    instantiatePremises, numbered, numberedBindings, applyBindings, substituteList, substitute,
    argumentAt, List.range_succ, isMatchCorrectAux, isMatchCorrectListAux]

theorem reordered_premises_refused : apply? language [.base "term"] (prepare application) [.bvar 0, a, A, B]
    [hasType a A, hasType (.bvar 0) (arrow A B)] = none := by
  simp [apply?, prepare, application, language, constructor, checkArgumentTypes,
    checkHasType, checkArgumentsHaveTypes, usesBareCollection?, a, A, B, hasType, arrow,
    instantiatePremises, numbered, numberedBindings, applyBindings, substituteList, substitute,
    argumentAt, List.range_succ, isMatchCorrectAux, isMatchCorrectListAux]

theorem ill_sorted_argument_refused : apply? language [] (prepare application) [A, a, A, B]
    [hasType A (arrow A B), hasType a A] = none := by decide

end Controls

#print axioms apply?_iff
#print axioms accepted_derives
#print axioms Instance.conclusion_scoped

end Mettapedia.GSLT.LanguageDef.PreparedSchematicInference
