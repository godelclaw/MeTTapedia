import Mathlib.Logic.Equiv.Defs
import Mettapedia.GSLT.LanguageDef.DefinitionalTyping
import Mettapedia.GSLT.LanguageDef.ConstructorSublanguage

/-!
# The base language of a definitional language

Removing the defined constructors, and the equations that define them,
leaves the base language. It has no equations, so its equation theory is
syntactic equality.

Full unfolding sends every typed term of the definitional language to a
typed term of the base language, of the same sort. It fixes the typed terms
of the base language. Two typed terms are equal in the equation theory
exactly when they unfold to the same base term. So the typed terms of a
sort, modulo the definitions, are the typed base terms of that sort.

A constructor is primitive when no definition defines it. Statements about
the constructors of a pattern use the constructor-support predicate of the
language-definition layer, at the alphabet of primitive constructors.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefinitionalEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-- A constructor that no definition defines. -/
def Primitive (rows : List Row) (label : String) : Prop :=
  ∀ row ∈ rows, label ≠ row.head

/-- Executable form of `Primitive`. -/
def checkPrimitive (rows : List Row) (label : String) : Bool :=
  rows.all (fun row => label != row.head)

theorem checkPrimitive_iff (rows : List Row) (label : String) :
    checkPrimitive rows label = true ↔ Primitive rows label := by
  simp [checkPrimitive, Primitive]

/-- The language without the defined constructors and without equations. -/
def baseLanguage (language : LanguageDef) (rows : List Row) : LanguageDef :=
  { language with
    terms := language.terms.filter (fun rule => checkPrimitive rows rule.label)
    equations := [] }

theorem mem_baseLanguage_terms {language : LanguageDef} {rows : List Row} (rule : GrammarRule) :
    rule ∈ (baseLanguage language rows).terms ↔
      rule ∈ language.terms ∧ Primitive rows rule.label := by
  simp only [baseLanguage, List.mem_filter, checkPrimitive_iff]

/-! ## Unfolding and the constructors of a pattern -/

/-- Unfolding a definition changes nothing in a pattern that does not
mention its head. -/
theorem unfoldOne_eq_self {row : Row} {pattern : Pattern} (absent : Avoids row.head pattern) :
    unfoldOne row pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => exact unfoldOne_bvar row index
  | hfvar name => exact unfoldOne_fvar row name
  | happly name arguments inductionHypothesis =>
    rw [unfoldOne_apply, if_neg (fun both => absent.1 both.1)]
    congr 1
    exact (List.map_congr_left (g := id) (fun argument member =>
      inductionHypothesis argument member (absent.2.of_mem member))).trans (List.map_id _)
  | hlambda name body inductionHypothesis =>
    rw [unfoldOne_lambda, inductionHypothesis absent]
  | hmultiLambda arity names body inductionHypothesis =>
    rw [unfoldOne_multiLambda, inductionHypothesis absent]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
    rw [unfoldOne_subst, bodyHypothesis absent.1, replacementHypothesis absent.2]
  | hcollection kind elements rest inductionHypothesis =>
    rw [unfoldOne_collection]
    congr 1
    exact (List.map_congr_left (g := id) (fun element member =>
      inductionHypothesis element member
        (ConstructorListWithin.of_mem absent member))).trans (List.map_id _)

/-- Full unfolding changes nothing in a pattern that mentions no defined
constructor. -/
theorem expand_eq_self :
    ∀ (rows : List Row) {pattern : Pattern},
      (∀ row ∈ rows, Avoids row.head pattern) → expand rows pattern = pattern
  | [], _, _ => rfl
  | row :: rows, pattern, absent => by
      rw [expand_cons,
        expand_eq_self rows (fun other member => absent other (List.mem_cons_of_mem _ member)),
        unfoldOne_eq_self (absent row (by simp))]

/-- A pattern that mentions none of the defined heads is over the primitive
constructors. -/
theorem constructorsWithin_primitive {rows : List Row} {pattern : Pattern}
    (absent : ∀ row ∈ rows, Avoids row.head pattern) :
    ConstructorsWithin (Primitive rows) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => trivial
  | hfvar name => trivial
  | happly name arguments inductionHypothesis =>
    refine ⟨fun row member => (absent row member).1, ?_⟩
    rw [constructorListWithin_iff_forall]
    intro argument member
    exact inductionHypothesis argument member
      (fun row rowMember => (absent row rowMember).2.of_mem member)
  | hlambda name body inductionHypothesis => exact inductionHypothesis absent
  | hmultiLambda arity names body inductionHypothesis => exact inductionHypothesis absent
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
    exact ⟨bodyHypothesis (fun row member => (absent row member).1),
      replacementHypothesis (fun row member => (absent row member).2)⟩
  | hcollection kind elements rest inductionHypothesis =>
    change ConstructorListWithin (Primitive rows) elements
    rw [constructorListWithin_iff_forall]
    intro element member
    exact inductionHypothesis element member
      (fun row rowMember => ConstructorListWithin.of_mem (absent row rowMember) member)

theorem avoids_of_primitive {rows : List Row} {pattern : Pattern}
    (within : ConstructorsWithin (Primitive rows) pattern) {row : Row} (member : row ∈ rows) :
    Avoids row.head pattern :=
  within.mono (fun _ primitive => primitive row member)

theorem SimpleParameters.length_eq {parameters : List TermParam} {types : List TypeExpr}
    (simple : SimpleParameters parameters types) : parameters.length = types.length :=
  List.Forall₂.length_eq simple

mutual
  /-- Unfolding a typed definition keeps a typed pattern inside every
  constructor alphabet that contains the body and, apart from the defined
  head, the pattern. Typing supplies the arity of each application of the
  head, so each one is replaced. -/
  theorem constructorsWithin_unfoldOne {language : LanguageDef} {row : Row}
      {allowed : String → Prop} (typedRow : row.Typed language)
      (bodyWithin : ConstructorsWithin allowed row.body)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type)
      (within : ConstructorsWithin (fun label => allowed label ∨ label = row.head) pattern) :
      ConstructorsWithin allowed (unfoldOne row pattern) := by
    cases typed with
    | bvar _ =>
      rw [unfoldOne_bvar]
      trivial
    | fvar _ =>
      rw [unfoldOne_fvar]
      trivial
    | @constructor _ rule arguments member ordinary argumentsTyped =>
      have unfolded : ConstructorListWithin allowed (arguments.map (unfoldOne row)) :=
        constructorListWithin_unfoldOne_arguments typedRow bodyWithin argumentsTyped within.2
      rw [unfoldOne_apply]
      split
      · refine constructorsWithin_applyBindings bodyWithin ?_
        rintro ⟨name, value⟩ entryMember
        exact unfolded.of_mem (List.of_mem_zip entryMember).2
      · rename_i unsaturated
        refine ⟨?_, unfolded⟩
        rcases within.1 with isAllowed | isHead
        · exact isAllowed
        · exfalso
          obtain ⟨declaration, types, typedAt⟩ := typedRow
          have same : rule = declaration := typedAt.unique member isHead
          subst same
          exact unsaturated
            ⟨isHead, by rw [argumentsTyped.length_eq, typedAt.simple.length_eq, typedAt.arity]⟩
    | lambda body =>
      rw [unfoldOne_lambda]
      exact constructorsWithin_unfoldOne typedRow bodyWithin body within
    | multiLambda body =>
      rw [unfoldOne_multiLambda]
      exact constructorsWithin_unfoldOne typedRow bodyWithin body within
    | subst body replacement =>
      rw [unfoldOne_subst]
      exact ⟨constructorsWithin_unfoldOne typedRow bodyWithin body within.1,
        constructorsWithin_unfoldOne typedRow bodyWithin replacement within.2⟩
    | collection elements =>
      rw [unfoldOne_collection]
      exact constructorListWithin_unfoldOne_elements typedRow bodyWithin elements within
    | collectionConstructor _ _ elements =>
      rw [unfoldOne_collection]
      exact constructorListWithin_unfoldOne_elements typedRow bodyWithin elements within

  theorem constructorListWithin_unfoldOne_arguments {language : LanguageDef} {row : Row}
      {allowed : String → Prop} (typedRow : row.Typed language)
      (bodyWithin : ConstructorsWithin allowed row.body)
      {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (within : ConstructorListWithin (fun label => allowed label ∨ label = row.head)
        arguments) :
      ConstructorListWithin allowed (arguments.map (unfoldOne row)) := by
    cases typed with
    | nil => trivial
    | cons _ _ argumentTyped rest =>
      exact ⟨constructorsWithin_unfoldOne typedRow bodyWithin argumentTyped within.1,
        constructorListWithin_unfoldOne_arguments typedRow bodyWithin rest within.2⟩

  theorem constructorListWithin_unfoldOne_elements {language : LanguageDef} {row : Row}
      {allowed : String → Prop} (typedRow : row.Typed language)
      (bodyWithin : ConstructorsWithin allowed row.body)
      {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (within : ConstructorListWithin (fun label => allowed label ∨ label = row.head)
        elements) :
      ConstructorListWithin allowed (elements.map (unfoldOne row)) := by
    cases typed with
    | nil => trivial
    | cons elementTyped rest =>
      exact ⟨constructorsWithin_unfoldOne typedRow bodyWithin elementTyped within.1,
        constructorListWithin_unfoldOne_elements typedRow bodyWithin rest within.2⟩
end

/-- **Normal forms are over the primitive constructors.** The full unfolding
of a typed pattern mentions no defined constructor. -/
theorem constructorsWithin_expand {language : LanguageDef} :
    ∀ {rows : List Row}, Acyclic rows → (∀ row ∈ rows, row.Typed language) →
      ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
        HasType language FreeTypeContext.empty bound pattern type →
          ConstructorsWithin (Primitive rows) (expand rows pattern)
  | [], _, _, _, _, _, _ => constructorsWithin_primitive (by simp)
  | row :: rows, acyclic, typedRows, _, pattern, _, typed => by
      obtain ⟨-, ownHead, laterHeads⟩ := acyclic.first
      have laterTyped : ∀ other ∈ rows, other.Typed language :=
        fun other member => typedRows other (List.mem_cons_of_mem _ member)
      have inner := constructorsWithin_expand acyclic.tail laterTyped typed
      have innerTyped := hasType_expand rows
        (fun other member => ⟨acyclic.tail.wellFormed other member, laterTyped other member⟩)
        typed
      have bodyWithin : ConstructorsWithin (Primitive (row :: rows)) row.body := by
        apply constructorsWithin_primitive
        intro other member
        rcases List.mem_cons.mp member with same | later
        · rw [same]
          exact ownHead
        · exact laterHeads other later
      rw [expand_cons]
      refine constructorsWithin_unfoldOne (typedRows row (by simp)) bodyWithin innerTyped
        (inner.mono ?_)
      intro label primitive
      by_cases isHead : label = row.head
      · exact Or.inr isHead
      · refine Or.inl ?_
        intro other member
        rcases List.mem_cons.mp member with same | later
        · rw [same]
          exact isHead
        · exact primitive other later

/-! ## Typing in the base language -/

/-- A constructor whose representation is a bare collection is never a
defined head: the formals of a definition have declared sorts. -/
theorem primitive_of_usesBareCollection {language : LanguageDef} {rows : List Row}
    (typedRows : ∀ row ∈ rows, row.Typed language) {rule : GrammarRule}
    (member : rule ∈ language.terms) (bare : UsesBareCollection rule) :
    Primitive rows rule.label := by
  intro row rowMember isHead
  obtain ⟨declaration, types, typedAt⟩ := typedRows row rowMember
  have same : rule = declaration := typedAt.unique member isHead
  subst same
  obtain ⟨parameterName, collectionType, elementType, shape⟩ := bare
  have simple := typedAt.simple
  rw [shape] at simple
  cases simple with
  | cons first rest =>
    obtain ⟨name, sameParameter⟩ := first
    cases sameParameter
    cases rest
    obtain ⟨sortName, impossible, -⟩ :=
      typedAt.sorts (.collection collectionType elementType) (by simp)
    cases impossible

/-- A typed pattern over the primitive constructors is typed in the base
language. -/
theorem hasType_base_of_primitive {language : LanguageDef} {rows : List Row}
    (typedRows : ∀ row ∈ rows, row.Typed language) {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (within : ConstructorsWithin (Primitive rows) pattern) :
    HasType (baseLanguage language rows) free bound pattern type :=
  (typed.withConstructors within
    (fun _ member bare => primitive_of_usesBareCollection typedRows member bare)).toSublanguage
    (fun rule member primitive => (mem_baseLanguage_terms rule).mpr ⟨member, primitive⟩)

/-- A typing derivation of the base language uses primitive declarations of
the definitional language. -/
theorem hasTypeWithConstructors_of_base {language : LanguageDef} {rows : List Row}
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType (baseLanguage language rows) free bound pattern type) :
    HasTypeWithConstructors language (Primitive rows) free bound pattern type :=
  typed.ofSublanguage (fun rule member => (mem_baseLanguage_terms rule).mp member)

/-- A typed term of the base language is a typed term of the definitional
language. -/
theorem hasType_of_base {language : LanguageDef} {rows : List Row}
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType (baseLanguage language rows) free bound pattern type) :
    HasType language free bound pattern type :=
  (hasTypeWithConstructors_of_base typed).toHasType

/-- Full unfolding fixes the typed terms of the base language. -/
theorem expand_eq_self_of_base {language : LanguageDef} {rows : List Row}
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType (baseLanguage language rows) free bound pattern type) :
    expand rows pattern = pattern :=
  expand_eq_self rows (fun _ member =>
    avoids_of_primitive (hasTypeWithConstructors_of_base typed).constructorsWithin member)

/-- The base language has the sorts of the definitional language. -/
theorem baseLanguage_typeNames (language : LanguageDef) (rows : List Row) :
    (baseLanguage language rows).typeNames = language.typeNames := rfl

theorem any_filter_eq_false {α : Type} {items : List α} {test keep : α → Bool}
    (none : items.any test = false) : (items.filter keep).any test = false := by
  rw [List.any_eq_false] at none ⊢
  intro item member
  exact none item (List.mem_filter.mp member).1

namespace DefinitionalLanguage

variable {base : BasePremiseEvaluator} {language : LanguageDef} {rows : List Row}

/-- The base language generates no equations. -/
theorem baseLanguage_isEquationFree (definitional : DefinitionalLanguage language rows) :
    (baseLanguage language rows).isEquationFree = true := by
  have noBags : (baseLanguage language rows).usesCollection .hashBag = false :=
    any_filter_eq_false definitional.noBags
  have noSets : (baseLanguage language rows).usesCollection .hashSet = false :=
    any_filter_eq_false definitional.noSets
  have noAlgebra : (baseLanguage language rows).hasAlgebraDeclarations = false :=
    any_filter_eq_false definitional.noAlgebra
  have noEquations : (baseLanguage language rows).equations = [] := rfl
  simp [LanguageDef.isEquationFree, noEquations, noBags, noSets, noAlgebra]

/-- The equation theory of the base language is syntactic equality. -/
theorem base_equationEquiv_iff (definitional : DefinitionalLanguage language rows)
    (left right : Pattern) :
    EquationEquiv base (baseLanguage language rows) left right ↔ left = right :=
  equationEquiv_iff_eq_of_no_generators definitional.baseLanguage_isEquationFree left right

/-- Full unfolding sends typed terms to typed terms of the base language,
of the same sort. -/
theorem hasType_base_expand (definitional : DefinitionalLanguage language rows)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty bound pattern type) :
    HasType (baseLanguage language rows) FreeTypeContext.empty bound (expand rows pattern)
      type :=
  hasType_base_of_primitive definitional.typed (definitional.hasType_expand typed)
    (constructorsWithin_expand definitional.acyclic definitional.typed typed)

end DefinitionalLanguage

/-! ## Typed terms modulo the definitions -/

/-- The typed terms of a sort in a context. -/
def TypedTerm (language : LanguageDef) (context : List TypeExpr) (type : TypeExpr) : Type :=
  { pattern : Pattern // HasType language FreeTypeContext.empty context pattern type }

/-- Typed terms identified by the language's equation theory. -/
def typedSetoid (base : BasePremiseEvaluator) (language : LanguageDef)
    (context : List TypeExpr) (type : TypeExpr) : Setoid (TypedTerm language context type) where
  r first second := EquationEquiv base language first.1 second.1
  iseqv :=
    ⟨fun term => Relation.EqvGen.refl term.1,
      fun related => Relation.EqvGen.symm _ _ related,
      fun first second => Relation.EqvGen.trans _ _ _ first second⟩

/-- **Typed terms modulo the definitions are the typed base terms.** Full
unfolding is the bijection, and inclusion of base terms is its inverse. -/
def typedQuotientEquiv (base : BasePremiseEvaluator) {language : LanguageDef}
    {rows : List Row} (definitional : DefinitionalLanguage language rows)
    (context : List TypeExpr) (type : TypeExpr) :
    Quotient (typedSetoid base language context type) ≃
      TypedTerm (baseLanguage language rows) context type where
  toFun := Quotient.lift
    (fun term => ⟨expand rows term.1, definitional.hasType_base_expand term.2⟩)
    (fun _ _ related => Subtype.ext ((definitional.equationEquiv_iff _ _).mp related))
  invFun term := Quotient.mk _ ⟨term.1, hasType_of_base term.2⟩
  left_inv := by
    intro wrapped
    induction wrapped using Quotient.inductionOn with
    | _ term =>
      exact Quotient.sound
        (Relation.EqvGen.symm _ _ (definitional.equationEquiv_expand term.1))
  right_inv term := Subtype.ext (expand_eq_self_of_base term.2)

end Mettapedia.GSLT.LanguageDef.DefinitionalEquations
