import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Static formers, decided at the term

Some formers say nothing about steps: what a term is, how it is built, its type, its collections and its binders. In a
language with no equations an object is equivalent only to itself, so these formers are decided at the term itself,
whatever the term's region (`staticEval`):

- `is` and its dual compare the term; `typed` and its dual run the well-sortedness checker, which is exact on objects;
- `built`, `single`, `empty` and `body`, with their duals, read the term's head and recurse into its parts, member or
  body; `bound` and its dual read a bound variable;
- conjunction and disjunction combine; every other former is left to the other strategies.

The evaluation is exact where it answers (`staticEval_exact`), so it is a certified decider (`staticDecider`), which the
front door consults for a question its search leaves open: a static fact about a term whose region never closes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern FreeTypeContext)

variable (language : LanguageDef)

mutual
/-- **A static former, evaluated at the term**; none for a former that reads steps or variables. -/
def staticEval : {n : ℕ} → Formula n → Pattern → Option Bool
  | _, .top, _ => some true
  | _, .bot, _ => some false
  | _, .and left right, term =>
    match staticEval left term, staticEval right term with
    | some first, some second => some (first && second)
    | _, _ => none
  | _, .or left right, term =>
    match staticEval left term, staticEval right term with
    | some first, some second => some (first || second)
    | _, _ => none
  | _, .is target, term => some (isObjectPattern term && term == target)
  | _, .isNot target, term => some !(isObjectPattern term && term == target)
  | _, .typed type, term =>
    some (isObjectPattern term && checkCarrierTyped language type term)
  | _, .untyped type, term =>
    some !(isObjectPattern term && checkCarrierTyped language type term)
  | _, .empty kind, term => some (isObjectPattern term && term == .collection kind [] none)
  | _, .nonEmpty kind, term => some !(isObjectPattern term && term == .collection kind [] none)
  | _, .bound index, term => some (isObjectPattern term && term == .bvar index)
  | _, .notBound index, term => some !(isObjectPattern term && term == .bvar index)
  | _, .built constructor parts, term =>
    if isObjectPattern term then
      match term with
      | .apply label arguments => if label = constructor then staticAll parts arguments else some false
      | _ => some false
    else some false
  | _, .everyBuilt constructor parts, term =>
    if isObjectPattern term then
      match term with
      | .apply label arguments => if label = constructor then staticSome parts arguments else some true
      | _ => some true
    else some true
  | _, .single kind inner, term =>
    if isObjectPattern term then
      match term with
      | .collection kind' [member] none => if kind' = kind then staticEval inner member else some false
      | _ => some false
    else some false
  | _, .everySingle kind inner, term =>
    if isObjectPattern term then
      match term with
      | .collection kind' [member] none => if kind' = kind then staticEval inner member else some true
      | _ => some true
    else some true
  | _, .body inner, term =>
    if isObjectPattern term then
      match term with
      | .lambda _ body => staticEval inner body
      | _ => some false
    else some false
  | _, .everyBody inner, term =>
    if isObjectPattern term then
      match term with
      | .lambda _ body => staticEval inner body
      | _ => some true
    else some true
  | _, _, _ => none

/-- Every formula of a list at the corresponding part, the lengths agreeing. -/
def staticAll : {n : ℕ} → Formulas n → List Pattern → Option Bool
  | _, .nil, [] => some true
  | _, .cons formula formulas, part :: parts =>
    match staticEval formula part, staticAll formulas parts with
    | some first, some second => some (first && second)
    | _, _ => none
  | _, _, _ => some false

/-- Some formula of a list at the corresponding part, or the lengths disagree. -/
def staticSome : {n : ℕ} → Formulas n → List Pattern → Option Bool
  | _, .nil, [] => some false
  | _, .cons formula formulas, part :: parts =>
    match staticEval formula part, staticSome formulas parts with
    | some first, some second => some (first || second)
    | _, _ => none
  | _, _, _ => some true
end

variable {relEnv : RelationEnv} {language}

section Exact

theorem named_iff (free : language.isEquationFree = true) {element target : Pattern} :
    (referenceStructure relEnv language).named element target ↔ (isObjectPattern element && element == target) = true := by
  change (IsObject element ∧ ObjectEquivalent relEnv language .syntax element target) ↔ _
  rw [objectEquivalent_iff_eq_of_isEquationFree free]
  simp [IsObject]

theorem typed_iff (free : language.isEquationFree = true) {element : Pattern} {type : TypeExpr} :
    (referenceStructure relEnv language).typed element type ↔
      (isObjectPattern element && checkCarrierTyped language type element) = true := by
  change (IsObject element ∧ ∃ representative, ObjectEquivalent relEnv language .syntax element representative ∧
    CarrierTyped language type representative) ↔ _
  simp only [objectEquivalent_iff_eq_of_isEquationFree free, exists_eq_left', Bool.and_eq_true,
    checkCarrierTyped_eq_true_iff, IsObject]

theorem shape_iff (free : language.isEquationFree = true) {element shape : Pattern} :
    (IsObject element ∧ ObjectEquivalent relEnv language .syntax element shape) ↔
      isObjectPattern element = true ∧ element = shape := by
  rw [objectEquivalent_iff_eq_of_isEquationFree free]

mutual
/-- **The static evaluation is exact where it answers.** -/
theorem staticEval_exact (free : language.isEquationFree = true) : ∀ {n : ℕ} (env : Env Pattern n) (formula : Formula n) (term : Pattern) {answer : Bool},
    staticEval language formula term = some answer →
      ((referenceStructure relEnv language).sat env formula term ↔ answer = true)
  | _, _, .top, _, _, evaluated => by cases evaluated; exact iff_of_true trivial rfl
  | _, _, .bot, _, _, evaluated => by cases evaluated; exact iff_of_false id Bool.false_ne_true
  | _, env, .and left right, term, _, evaluated => by
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i first second leftEvaluated rightEvaluated
      cases evaluated
      change ((referenceStructure relEnv language).sat env left term ∧
        (referenceStructure relEnv language).sat env right term) ↔ _
      rw [staticEval_exact free env left term leftEvaluated, staticEval_exact free env right term rightEvaluated,
        Bool.and_eq_true]
    · cases evaluated
  | _, env, .or left right, term, _, evaluated => by
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i first second leftEvaluated rightEvaluated
      cases evaluated
      change ((referenceStructure relEnv language).sat env left term ∨
        (referenceStructure relEnv language).sat env right term) ↔ _
      rw [staticEval_exact free env left term leftEvaluated, staticEval_exact free env right term rightEvaluated,
        Bool.or_eq_true]
    · cases evaluated
  | _, _, .is target, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    exact named_iff free
  | _, _, .isNot target, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    change ¬ (referenceStructure relEnv language).named term target ↔ _
    rw [named_iff free]
    cases isObjectPattern term <;> simp
  | _, _, .typed type, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    exact typed_iff free
  | _, _, .untyped type, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    change ¬ (referenceStructure relEnv language).typed term type ↔ _
    rw [typed_iff free]
    cases isObjectPattern term <;> simp
  | _, _, .empty kind, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    change (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.collection kind [] none)) ↔ _
    rw [shape_iff free]
    simp
  | _, _, .nonEmpty kind, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    change ¬ (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.collection kind [] none)) ↔ _
    rw [shape_iff free]
    cases isObjectPattern term <;> simp
  | _, _, .bound index, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    change (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.bvar index)) ↔ _
    rw [shape_iff free]
    simp
  | _, _, .notBound index, term, _, evaluated => by
    simp only [staticEval, Option.some.injEq] at evaluated
    subst evaluated
    change ¬ (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.bvar index)) ↔ _
    rw [shape_iff free]
    cases isObjectPattern term <;> simp
  | _, env, .built constructor parts, term, _, evaluated => by
    change (∃ arguments, (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.apply constructor arguments)) ∧
      (referenceStructure relEnv language).satAll env parts arguments) ↔ _
    simp only [shape_iff free]
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i object
      split at evaluated
      · rename_i label arguments
        split at evaluated
        · rename_i same
          subst same
          rw [← staticAll_exact free env parts arguments evaluated]
          constructor
          · rintro ⟨arguments', ⟨-, equal⟩, holds⟩
            cases equal
            exact holds
          · intro holds
            exact ⟨arguments, ⟨object, rfl⟩, holds⟩
        · rename_i different
          cases evaluated
          exact iff_of_false (fun ⟨_, ⟨_, equal⟩, _⟩ => different (by cases equal; rfl)) Bool.false_ne_true
      · rename_i notApply
        cases evaluated
        exact iff_of_false (fun ⟨arguments, ⟨_, equal⟩, _⟩ => notApply constructor arguments equal) Bool.false_ne_true
    · rename_i notObject
      cases evaluated
      exact iff_of_false (fun ⟨_, ⟨object, _⟩, _⟩ => notObject object) Bool.false_ne_true
  | _, env, .everyBuilt constructor parts, term, _, evaluated => by
    change (∀ arguments, (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.apply constructor arguments)) →
      (referenceStructure relEnv language).satSome env parts arguments) ↔ _
    simp only [shape_iff free]
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i object
      split at evaluated
      · rename_i label arguments
        split at evaluated
        · rename_i same
          subst same
          rw [← staticSome_exact free env parts arguments evaluated]
          constructor
          · intro every
            exact every arguments ⟨object, rfl⟩
          · rintro holds arguments' ⟨-, equal⟩
            cases equal
            exact holds
        · rename_i different
          cases evaluated
          exact iff_of_true (fun _ ⟨_, equal⟩ => absurd (by cases equal; rfl) different) rfl
      · rename_i notApply
        cases evaluated
        exact iff_of_true (fun arguments ⟨_, equal⟩ => absurd equal (notApply constructor arguments)) rfl
    · rename_i notObject
      cases evaluated
      exact iff_of_true (fun _ ⟨object, _⟩ => absurd object notObject) rfl
  | _, env, .single kind inner, term, _, evaluated => by
    change (∃ member, (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.collection kind [member] none)) ∧
      (referenceStructure relEnv language).sat env inner member) ↔ _
    simp only [shape_iff free]
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i object
      split at evaluated
      · rename_i kind' member
        split at evaluated
        · rename_i same
          subst same
          rw [← staticEval_exact free env inner member evaluated]
          constructor
          · rintro ⟨member', ⟨-, equal⟩, holds⟩
            cases equal
            exact holds
          · intro holds
            exact ⟨member, ⟨object, rfl⟩, holds⟩
        · rename_i different
          cases evaluated
          exact iff_of_false (fun ⟨_, ⟨_, equal⟩, _⟩ => different (by cases equal; rfl)) Bool.false_ne_true
      · rename_i notSingle
        cases evaluated
        exact iff_of_false (fun ⟨member, ⟨_, equal⟩, _⟩ => notSingle kind member equal) Bool.false_ne_true
    · rename_i notObject
      cases evaluated
      exact iff_of_false (fun ⟨_, ⟨object, _⟩, _⟩ => notObject object) Bool.false_ne_true
  | _, env, .everySingle kind inner, term, _, evaluated => by
    change (∀ member, (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.collection kind [member] none)) →
      (referenceStructure relEnv language).sat env inner member) ↔ _
    simp only [shape_iff free]
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i object
      split at evaluated
      · rename_i kind' member
        split at evaluated
        · rename_i same
          subst same
          rw [← staticEval_exact free env inner member evaluated]
          constructor
          · intro every
            exact every member ⟨object, rfl⟩
          · rintro holds member' ⟨-, equal⟩
            cases equal
            exact holds
        · rename_i different
          cases evaluated
          exact iff_of_true (fun _ ⟨_, equal⟩ => absurd (by cases equal; rfl) different) rfl
      · rename_i notSingle
        cases evaluated
        exact iff_of_true (fun member ⟨_, equal⟩ => absurd equal (notSingle kind member)) rfl
    · rename_i notObject
      cases evaluated
      exact iff_of_true (fun _ ⟨object, _⟩ => absurd object notObject) rfl
  | _, env, .body inner, term, _, evaluated => by
    change (∃ body, (IsObject term ∧ ∃ name, ObjectEquivalent relEnv language .syntax term (.lambda name body)) ∧
      (referenceStructure relEnv language).sat env inner body) ↔ _
    simp only [objectEquivalent_iff_eq_of_isEquationFree free]
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i object
      split at evaluated
      · rename_i name body
        rw [← staticEval_exact free env inner body evaluated]
        constructor
        · rintro ⟨body', ⟨-, name', equal⟩, holds⟩
          cases equal
          exact holds
        · intro holds
          exact ⟨body, ⟨object, name, rfl⟩, holds⟩
      · rename_i notLambda
        cases evaluated
        exact iff_of_false (fun ⟨body, ⟨_, name, equal⟩, _⟩ => notLambda name body equal) Bool.false_ne_true
    · rename_i notObject
      cases evaluated
      exact iff_of_false (fun ⟨_, ⟨object, _⟩, _⟩ => notObject object) Bool.false_ne_true
  | _, env, .everyBody inner, term, _, evaluated => by
    change (∀ body, (IsObject term ∧ ∃ name, ObjectEquivalent relEnv language .syntax term (.lambda name body)) →
      (referenceStructure relEnv language).sat env inner body) ↔ _
    simp only [objectEquivalent_iff_eq_of_isEquationFree free]
    simp only [staticEval] at evaluated
    split at evaluated
    · rename_i object
      split at evaluated
      · rename_i name body
        rw [← staticEval_exact free env inner body evaluated]
        constructor
        · intro every
          exact every body ⟨object, name, rfl⟩
        · rintro holds body' ⟨-, name', equal⟩
          cases equal
          exact holds
      · rename_i notLambda
        cases evaluated
        exact iff_of_true (fun body ⟨_, name, equal⟩ => absurd equal (notLambda name body)) rfl
    · rename_i notObject
      cases evaluated
      exact iff_of_true (fun _ ⟨object, _⟩ => absurd object notObject) rfl
  | _, _, .var _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .mu _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .nu _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .possibly _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .necessarily _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .sometimeBefore _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .alwaysBefore _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .atLeast _ _ _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .allButFewer _ _ _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .split _ _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .everySplit _ _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .multiBody _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .everyMultiBody _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .mapsAll _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .mapsSome _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .someOf _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .everyOf _ _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .inRelation _, _, _, evaluated => by simp [staticEval] at evaluated
  | _, _, .notInRelation _, _, _, evaluated => by simp [staticEval] at evaluated

theorem staticAll_exact (free : language.isEquationFree = true) : ∀ {n : ℕ} (env : Env Pattern n) (formulas : Formulas n) (parts : List Pattern) {answer : Bool},
    staticAll language formulas parts = some answer →
      ((referenceStructure relEnv language).satAll env formulas parts ↔ answer = true)
  | _, _, .nil, [], _, evaluated => by cases evaluated; exact iff_of_true trivial rfl
  | _, env, .cons formula formulas, part :: parts, _, evaluated => by
    simp only [staticAll] at evaluated
    split at evaluated
    · rename_i first second headEvaluated restEvaluated
      cases evaluated
      change ((referenceStructure relEnv language).sat env formula part ∧
        (referenceStructure relEnv language).satAll env formulas parts) ↔ _
      rw [staticEval_exact free env formula part headEvaluated, staticAll_exact free env formulas parts restEvaluated,
        Bool.and_eq_true]
    · cases evaluated
  | _, _, .nil, _ :: _, _, evaluated => by
    simp only [staticAll, Option.some.injEq] at evaluated
    subst evaluated
    exact iff_of_false id Bool.false_ne_true
  | _, _, .cons _ _, [], _, evaluated => by
    simp only [staticAll, Option.some.injEq] at evaluated
    subst evaluated
    exact iff_of_false id Bool.false_ne_true

theorem staticSome_exact (free : language.isEquationFree = true) : ∀ {n : ℕ} (env : Env Pattern n) (formulas : Formulas n) (parts : List Pattern) {answer : Bool},
    staticSome language formulas parts = some answer →
      ((referenceStructure relEnv language).satSome env formulas parts ↔ answer = true)
  | _, _, .nil, [], _, evaluated => by cases evaluated; exact iff_of_false id Bool.false_ne_true
  | _, env, .cons formula formulas, part :: parts, _, evaluated => by
    simp only [staticSome] at evaluated
    split at evaluated
    · rename_i first second headEvaluated restEvaluated
      cases evaluated
      change ((referenceStructure relEnv language).sat env formula part ∨
        (referenceStructure relEnv language).satSome env formulas parts) ↔ _
      rw [staticEval_exact free env formula part headEvaluated, staticSome_exact free env formulas parts restEvaluated,
        Bool.or_eq_true]
    · cases evaluated
  | _, _, .nil, _ :: _, _, evaluated => by
    simp only [staticSome, Option.some.injEq] at evaluated
    subst evaluated
    exact iff_of_true trivial rfl
  | _, _, .cons _ _, [], _, evaluated => by
    simp only [staticSome, Option.some.injEq] at evaluated
    subst evaluated
    exact iff_of_true trivial rfl
end

end Exact

/-- **The static decider** of a language with no equations. -/
def staticDecider (free : language.isEquationFree = true) : Decider relEnv language where
  decide formula term := staticEval language formula term
  exact decided := staticEval_exact free Env.closed _ _ decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
