import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

/-!
# Independent grammar origins of inferred rule contexts

The judgments below describe a grammar head and a descent to one actual
metavariable site without referring to the inference algorithm. Successful
context inference retains an independently derived grammar location, including
the full binder prefix and the collection type at remainder positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem unique?_member {α : Type} [DecidableEq α] {items : List α} {item : α}
    (found : unique? items = some item) : item ∈ items := by
  unfold unique? at found
  split at found
  next candidate same =>
    cases Option.some.inj found
    exact List.mem_eraseDups.mp (same ▸ (by simp))
  next => contradiction

theorem constructor?_origin {language : LanguageDef} {label : String} {declaration : GrammarRule}
    (found : constructor? language label = some declaration) :
    declaration ∈ language.terms ∧ declaration.label = label := by
  unfold constructor? at found
  split at found
  next candidate same =>
    cases Option.some.inj found
    have member : declaration ∈ language.terms.filter (fun row => row.label == label) := by
      rw [same]
      simp
    exact (List.mem_filter.mp member).imp_right beq_iff_eq.mp
  next => contradiction

theorem lookupType_origin {context : List (String × TypeExpr)} {name : String} {type : TypeExpr}
    (found : lookupType context name = some type) : (name, type) ∈ context := by
  have member := unique?_member found
  obtain ⟨entry, declared, matching⟩ := List.mem_filterMap.mp member
  split at matching
  next named =>
    have nameEq := beq_iff_eq.mp named
    have typeEq := Option.some.inj matching
    simpa only [← nameEq, ← typeEq, Prod.mk.eta] using declared
  next => contradiction

inductive Head (language : LanguageDef) (context : List (String × TypeExpr)) :
    List TypeExpr → Pattern → TypeExpr → Prop where
  | free {bound name type} : (name, type) ∈ context → Head language context bound (.fvar name) type
  | bound {bound index type} : bound[index]? = some type → Head language context bound (.bvar index) type
  | constructor {bound declaration arguments} : declaration ∈ language.terms →
      Head language context bound (.apply declaration.label arguments) (.base declaration.category)
  | collection {bound declaration kind elements tail element} : declaration ∈ language.terms →
      bareCollectionElementType? declaration kind (.base declaration.category) = some element →
      Head language context bound (.collection kind elements tail) (.base declaration.category)
  | substitution {bound body replacement domain expected} :
      Head language context bound replacement domain →
      Head language context (domain :: bound) body expected →
      Head language context bound (.subst body replacement) expected

theorem headType?_sound {language : LanguageDef} {context : List (String × TypeExpr)}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (found : headType? language context bound pattern = some expected) :
    Head language context bound pattern expected := by
  cases pattern with
  | fvar name => exact .free (lookupType_origin found)
  | bvar index => exact .bound found
  | apply label arguments =>
      obtain ⟨declaration, selected, same⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨declared, labelEq⟩ := constructor?_origin selected
      subst expected
      rw [← labelEq]
      exact .constructor declared
  | collection kind elements tail =>
      have member := unique?_member found
      obtain ⟨declaration, declared, typed⟩ := List.mem_filterMap.mp member
      split at typed
      next element selected =>
        cases Option.some.inj typed
        exact .collection declared selected
      next => contradiction
  | subst body replacement =>
      obtain ⟨domain, replacementTyped, bodyTyped⟩ := Option.bind_eq_some_iff.mp found
      exact .substitution (headType?_sound replacementTyped) (headType?_sound bodyTyped)
  | lambda _ _ | multiLambda _ _ _ => cases found
termination_by sizeOf pattern

inductive Location (language : LanguageDef) (context : List (String × TypeExpr)) :
    List TypeExpr → TypeExpr → Pattern → List Nat → List TypeExpr → TypeExpr → Prop where
  | free {bound expected name} :
      Location language context bound expected (.fvar name) [] bound expected
  | constructor {bound expected declaration arguments index path parameter argument parameterType localBound result} :
      declaration ∈ language.terms → expected = .base declaration.category →
      ¬ UsesBareCollection declaration → declaration.params[index]? = some parameter →
      arguments[index]? = some argument → MatchesParameterRepresentation parameter argument →
      parameterType? parameter = some parameterType →
      Location language context bound parameterType argument path localBound result →
      Location language context bound expected (.apply declaration.label arguments)
        (index :: path) localBound result
  | binder {bound domain codomain binder body path localBound result} :
      Location language context (domain :: bound) codomain body path localBound result →
      Location language context bound (.arrow domain codomain) (.lambda binder body)
        (0 :: path) localBound result
  | binders {bound domain codomain arity binders body path localBound result} :
      Location language context (List.replicate arity domain ++ bound) codomain body path localBound result →
      Location language context bound (.arrow (.multiBinder domain) codomain)
        (.multiLambda arity binders body) (0 :: path) localBound result
  | substitutionBody {bound expected body replacement domain path localBound result} :
      Head language context bound replacement domain →
      Location language context (domain :: bound) expected body path localBound result →
      Location language context bound expected (.subst body replacement) (0 :: path) localBound result
  | substitutionReplacement {bound expected body replacement domain path localBound result} :
      Head language context bound replacement domain →
      Location language context bound domain replacement path localBound result →
      Location language context bound expected (.subst body replacement) (1 :: path) localBound result
  | collectionElement {bound expected kind elements tail index path elementType element localBound result} :
      (expected = .collection kind elementType ∨ ∃ declaration ∈ language.terms,
        bareCollectionElementType? declaration kind expected = some elementType) →
      index < elements.length → elements[index]? = some element →
      Location language context bound elementType element path localBound result →
      Location language context bound expected (.collection kind elements tail)
        (index :: path) localBound result
  | collectionTail {bound expected kind elements name elementType} :
      (expected = .collection kind elementType ∨ ∃ declaration ∈ language.terms,
        bareCollectionElementType? declaration kind expected = some elementType) →
      Location language context bound expected (.collection kind elements (some name))
        [elements.length] bound (.collection kind elementType)

theorem collectionElement?_origin {language : LanguageDef} {kind : CollType}
    {expected elementType : TypeExpr}
    (found : collectionElement? language kind expected = some elementType) :
    expected = .collection kind elementType ∨ ∃ declaration ∈ language.terms,
      bareCollectionElementType? declaration kind expected = some elementType := by
  have member := unique?_member found
  rcases List.mem_append.mp member with direct | authored
  · cases expected <;> simp_all [collectionElement?]
  · obtain ⟨declaration, declared, selected⟩ := List.mem_filterMap.mp authored
    exact Or.inr ⟨declaration, declared, selected⟩

theorem contextAt?_sound {language : LanguageDef} {context : List (String × TypeExpr)}
    {bound localBound : List TypeExpr} {expected result : TypeExpr} {pattern : Pattern} {path : List Nat}
    (found : contextAt? language context bound expected pattern path = some (localBound, result)) :
    Location language context bound expected pattern path localBound result := by
  cases pattern <;> cases path <;> try (simp only [contextAt?] at found) <;> try contradiction
  case fvar.nil name =>
    cases Option.some.inj found
    exact .free
  case apply.cons label arguments index path =>
    obtain ⟨declaration, selected, _, expectedEq, _, ordinary, parameter, parameterSelected,
      argument, argumentSelected, _, represented, argumentType, argumentTyped, nested⟩ :=
      by simpa only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard,
        Option.pure_def, Bool.not_eq_true', beq_iff_eq] using found
    obtain ⟨declared, labelEq⟩ := constructor?_origin selected
    have expectedEqual : expected = .base declaration.category := by
      split at expectedEq <;> simp_all
    have notBare : usesBareCollection? declaration = false := by
      split at ordinary <;> simp_all
    have representation : matchesParameterRepresentation? parameter argument = true := by
      split at represented <;> simp_all
    rw [← labelEq]
    exact .constructor declared expectedEqual
      (fun bare => by rw [(usesBareCollection?_eq_true_iff _).mpr bare] at notBare; cases notBare)
      parameterSelected argumentSelected
      ((matchesParameterRepresentation?_eq_true_iff _ _).mp representation)
      argumentTyped (contextAt?_sound nested)
  case lambda.cons binder body index path =>
    cases index <;> try (simp only [contextAt?] at found)
    all_goals try contradiction
    cases expected <;> try (simp only [contextAt?] at found)
    all_goals try contradiction
    exact .binder (contextAt?_sound found)
  case multiLambda.cons arity binders body index path =>
    cases index <;> try (simp only [contextAt?] at found)
    all_goals try contradiction
    cases expected <;> try (simp only [contextAt?] at found) <;> try contradiction
    case arrow domain codomain =>
      cases domain <;> simp only [contextAt?] at found <;> try contradiction
      exact .binders (contextAt?_sound found)
  case subst.cons body replacement index path =>
    cases index with
    | zero =>
      simp only [contextAt?] at found
      obtain ⟨domain, typed, nested⟩ := Option.bind_eq_some_iff.mp found
      exact .substitutionBody (headType?_sound typed) (contextAt?_sound nested)
    | succ index =>
      cases index <;> try (simp only [contextAt?] at found) <;> try contradiction
      simp only [Nat.zero_add, contextAt?] at found
      obtain ⟨domain, typed, nested⟩ := Option.bind_eq_some_iff.mp found
      exact .substitutionReplacement (headType?_sound typed) (contextAt?_sound nested)
  case collection.cons kind elements tail index path =>
    obtain ⟨elementType, elementTyped, remainder⟩ := Option.bind_eq_some_iff.mp found
    have origin := collectionElement?_origin elementTyped
    split at remainder
    next before =>
      obtain ⟨element, selected, nested⟩ := Option.bind_eq_some_iff.mp remainder
      exact .collectionElement origin before selected (contextAt?_sound nested)
    next =>
      split at remainder
      next atTail =>
        obtain ⟨first, present⟩ := Bool.and_eq_true_iff.mp atTail
        obtain ⟨indexEq, empty⟩ := Bool.and_eq_true_iff.mp first
        have actualIndex := beq_iff_eq.mp indexEq
        have emptyPath := List.isEmpty_iff.mp empty
        have endpoints := Option.some.inj remainder
        cases endpoints
        cases tail with
        | none => cases present
        | some name =>
          subst index
          subst path
          exact .collectionTail origin
      next => contradiction
termination_by path.length

#print axioms contextAt?_sound
#print axioms headType?_sound

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
