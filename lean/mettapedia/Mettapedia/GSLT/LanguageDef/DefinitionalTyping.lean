import Mettapedia.GSLT.LanguageDef.DefinitionalNormalForms
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution

/-!
# Unfolding a definition preserves typing

A definition is typed in a language when exactly one constructor
declaration carries its head, that declaration has ordinary term parameters,
one per formal and each of a declared sort, and the body has the
declaration's sort when the formals have the parameter sorts. Then replacing
an application of the head by the body keeps every typing derivation, in
every bound context and beneath every binder.

The instance of the body at an argument vector is the positional
substitution that instantiates inference rules, so the existing typing
theorem for that substitution applies unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefinitionalEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-- Every parameter is an ordinary term position of the listed type. -/
def SimpleParameters (parameters : List TermParam) (types : List TypeExpr) : Prop :=
  List.Forall₂ (fun parameter type => ∃ name, parameter = TermParam.simple name type)
    parameters types

theorem SimpleParameters.arguments {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {parameters : List TermParam} {types : List TypeExpr}
    (simple : SimpleParameters parameters types) :
    ∀ {arguments : List Pattern},
      ArgumentsHaveTypes language free bound arguments parameters →
        List.Forall₂ (HasType language free bound) arguments types := by
  induction simple with
  | nil =>
    intro arguments typed
    cases typed
    exact .nil
  | cons shape _ inductionHypothesis =>
    intro arguments typed
    obtain ⟨name, rfl⟩ := shape
    cases arguments with
    | nil => cases typed
    | cons argument arguments =>
      obtain ⟨first, rest⟩ := ArgumentsHaveTypes.simple_cons_inv typed
      exact .cons first (inductionHypothesis rest)

/-- The declaration and the formal sorts at which a definition is typed.
Exactly one declaration row carries the head. Its parameters are ordinary
term positions, one per formal and each of a declared sort. The body has the
declared result sort when the formals have the parameter sorts. -/
structure Row.TypedAt (language : LanguageDef) (row : Row) (declaration : GrammarRule)
    (types : List TypeExpr) : Prop where
  declared : language.terms.filter (fun rule => rule.label == row.head) = [declaration]
  simple : SimpleParameters declaration.params types
  arity : types.length = row.formals.length
  sorts : ∀ type ∈ types, ∃ name, type = .base name ∧ name ∈ language.typeNames
  body : HasType language FreeTypeContext.empty types (numbered row.formals row.body)
    (.base declaration.category)

namespace Row.TypedAt

variable {language : LanguageDef} {row : Row} {declaration : GrammarRule}
  {types : List TypeExpr}

theorem mem_filter (typedAt : row.TypedAt language declaration types) :
    declaration ∈ language.terms.filter (fun rule => rule.label == row.head) := by
  rw [typedAt.declared]
  simp

theorem mem (typedAt : row.TypedAt language declaration types) :
    declaration ∈ language.terms :=
  (List.mem_filter.mp typedAt.mem_filter).1

theorem label_eq (typedAt : row.TypedAt language declaration types) :
    declaration.label = row.head := by
  simpa using (List.mem_filter.mp typedAt.mem_filter).2

/-- No other declaration carries the head. -/
theorem unique (typedAt : row.TypedAt language declaration types) {other : GrammarRule}
    (member : other ∈ language.terms) (label : other.label = row.head) :
    other = declaration := by
  have inFilter : other ∈ language.terms.filter (fun rule => rule.label == row.head) :=
    List.mem_filter.mpr ⟨member, by simpa using label⟩
  rw [typedAt.declared] at inFilter
  simpa using inFilter

end Row.TypedAt

/-- The definition is typed in the language. -/
def Row.Typed (language : LanguageDef) (row : Row) : Prop :=
  ∃ (declaration : GrammarRule) (types : List TypeExpr), row.TypedAt language declaration types

theorem forall₂_getElem? {α β : Type} {relation : α → β → Prop} {first : List α}
    {second : List β} (pointwise : List.Forall₂ relation first second) :
    ∀ {index : Nat} {value : β}, second[index]? = some value →
      ∃ source, first[index]? = some source ∧ relation source value := by
  induction pointwise with
  | nil => intro index value lookup; simp at lookup
  | cons related _ inductionHypothesis =>
    intro index value lookup
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst lookup
      exact ⟨_, by simp, related⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at lookup
      obtain ⟨source, found, holds⟩ := inductionHypothesis lookup
      exact ⟨source, by simpa using found, holds⟩

theorem hasType_argumentAt {language : LanguageDef} {free : FreeTypeContext}
    {target : List TypeExpr} {arguments : List Pattern} {types : List TypeExpr}
    (pointwise : List.Forall₂ (HasType language free target) arguments types)
    {index : Nat} {type : TypeExpr} (lookup : types[index]? = some type) :
    HasType language free target (argumentAt arguments index) type := by
  obtain ⟨argument, found, typed⟩ := forall₂_getElem? pointwise lookup
  simpa [argumentAt, found] using typed

theorem matchesParameterRepresentation_unfoldOne (row : Row) (parameter : TermParam)
    (pattern : Pattern) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter (unfoldOne row pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binder body type =>
    cases pattern <;> simp [MatchesParameterRepresentation]
    case lambda binderName body => cases binderName <;> simp
  | multiAbstractionNamed binders body type =>
    cases pattern <;> simp [MatchesParameterRepresentation]
    case multiLambda arity binderNames body =>
      cases binderNames <;> simp

mutual
  /-- **Subject reduction.** Unfolding a typed definition preserves the type
  of every pattern, in every bound context. -/
  theorem hasType_unfoldOne {language : LanguageDef} {row : Row} (formed : row.WellFormed)
      (typedRow : row.Typed language) {bound : List TypeExpr} {pattern : Pattern}
      {type : TypeExpr}
      (typed : HasType language FreeTypeContext.empty bound pattern type) :
      HasType language FreeTypeContext.empty bound (unfoldOne row pattern) type := by
    cases typed with
    | bvar lookup => simpa using HasType.bvar (free := FreeTypeContext.empty) lookup
    | fvar lookup => simpa using HasType.fvar (bound := bound) lookup
    | @constructor _ rule arguments member ordinary argumentsTyped =>
      have unfolded := argumentsHaveTypes_unfoldOne formed typedRow argumentsTyped
      rw [unfoldOne_apply]
      split
      · rename_i saturated
        obtain ⟨declaration, types, typedAt⟩ := typedRow
        have same : rule = declaration := typedAt.unique member saturated.1
        subst same
        have pointwise := typedAt.simple.arguments unfolded
        have arity : (arguments.map (unfoldOne row)).length = row.formals.length := by
          rw [List.length_map]
          exact saturated.2
        rw [formed.schema.instantiate_numbered formed.distinct _ arity]
        exact HasType.substituteBound
          ⟨argumentAt (arguments.map (unfoldOne row)),
            fun lookup => hasType_argumentAt pointwise lookup⟩ typedAt.body
      · exact HasType.constructor member ordinary unfolded
    | lambda body =>
      simpa using HasType.lambda (hasType_unfoldOne formed typedRow body)
    | multiLambda body =>
      simpa using HasType.multiLambda (hasType_unfoldOne formed typedRow body)
    | subst body replacement =>
      simpa using HasType.subst (hasType_unfoldOne formed typedRow body)
        (hasType_unfoldOne formed typedRow replacement)
    | collection elements =>
      simpa using HasType.collection (elementsHaveType_unfoldOne formed typedRow elements)
    | collectionConstructor member shape elements =>
      simpa using HasType.collectionConstructor member shape
        (elementsHaveType_unfoldOne formed typedRow elements)

  theorem argumentsHaveTypes_unfoldOne {language : LanguageDef} {row : Row}
      (formed : row.WellFormed) (typedRow : row.Typed language) {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language FreeTypeContext.empty bound arguments parameters) :
      ArgumentsHaveTypes language FreeTypeContext.empty bound
        (arguments.map (unfoldOne row)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped rest =>
      exact .cons (matchesParameterRepresentation_unfoldOne row _ _ representation)
        parameterType (hasType_unfoldOne formed typedRow argumentTyped)
        (argumentsHaveTypes_unfoldOne formed typedRow rest)

  theorem elementsHaveType_unfoldOne {language : LanguageDef} {row : Row}
      (formed : row.WellFormed) (typedRow : row.Typed language) {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language FreeTypeContext.empty bound elements elementType) :
      ElementsHaveType language FreeTypeContext.empty bound
        (elements.map (unfoldOne row)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped rest =>
      exact .cons (hasType_unfoldOne formed typedRow elementTyped)
        (elementsHaveType_unfoldOne formed typedRow rest)
end

/-- Full unfolding preserves typing. -/
theorem hasType_expand {language : LanguageDef} :
    ∀ rows : List Row, (∀ row ∈ rows, row.WellFormed ∧ row.Typed language) →
      ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
        HasType language FreeTypeContext.empty bound pattern type →
          HasType language FreeTypeContext.empty bound (expand rows pattern) type
  | [], _, _, _, _, typed => typed
  | row :: rows, every, _, _, _, typed => by
      obtain ⟨formed, typedRow⟩ := every row (by simp)
      exact hasType_unfoldOne formed typedRow
        (hasType_expand rows (fun other member => every other (by simp [member])) typed)

/-! ## Definitional languages -/

/-- A language whose authored equations state the rows, one each and in
order, where the rows are typed definitions that are acyclic in that order,
and which has no collection laws. -/
structure DefinitionalLanguage (language : LanguageDef) (rows : List Row) : Prop where
  authored : List.Forall₂ Defines language.equations rows
  acyclic : Acyclic rows
  typed : ∀ row ∈ rows, row.Typed language
  noBags : language.usesCollection .hashBag = false
  noSets : language.usesCollection .hashSet = false
  noAlgebra : language.hasAlgebraDeclarations = false

namespace DefinitionalLanguage

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {base : BasePremiseEvaluator} {language : LanguageDef} {rows : List Row}

theorem presents (definitional : DefinitionalLanguage language rows) : Presents language rows :=
  presents_of_forall₂ definitional.authored

/-- The language's equation theory is equality of full unfoldings. -/
theorem equationEquiv_iff (definitional : DefinitionalLanguage language rows)
    (left right : Pattern) :
    EquationEquiv base language left right ↔ expand rows left = expand rows right :=
  equationEquiv_iff_expand_eq definitional.acyclic definitional.presents definitional.noBags
    definitional.noSets definitional.noAlgebra left right

theorem equationEquiv_expand (definitional : DefinitionalLanguage language rows)
    (pattern : Pattern) : EquationEquiv base language pattern (expand rows pattern) :=
  DefinitionalEquations.equationEquiv_expand rows
    (fun row member => ⟨definitional.acyclic.wellFormed row member,
      definitional.presents.authored row member⟩) pattern

/-- A full unfolding is already fully unfolded. -/
theorem expand_expand (definitional : DefinitionalLanguage language rows) (pattern : Pattern) :
    expand rows (expand rows pattern) = expand rows pattern :=
  ((definitional.equationEquiv_iff (base := fun _ _ _ => []) pattern (expand rows pattern)).mp
    (definitional.equationEquiv_expand pattern)).symm

theorem hasType_expand (definitional : DefinitionalLanguage language rows)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty bound pattern type) :
    HasType language FreeTypeContext.empty bound (expand rows pattern) type :=
  DefinitionalEquations.hasType_expand rows
    (fun row member => ⟨definitional.acyclic.wellFormed row member,
      definitional.typed row member⟩) typed

end DefinitionalLanguage

end Mettapedia.GSLT.LanguageDef.DefinitionalEquations
