import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetForms

/-!
# Hereditary sets

A set language whose sets hold terms of their own sort has sets of sets: the hereditary terms are its atoms and the
sets of hereditary terms. With no atoms they are the hereditarily finite sets.

- **Hereditary terms** (`Hereditary`, decided by `hereditary`): typed at the carrier's sort, closed object terms.
- **Canonical forms** (`hereditary_canonical`): every set sorted without repetition, bottom up
  (`BagForms.sortBags`). A hereditary term is equivalent to its canonical form: the inner sets first, through their
  contexts, then the outer set by its permutation and repetition laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)

variable {relEnv : RelationEnv} {language : LanguageDef} {carrier : GrammarRule} {sort : String}

/-! ## Hereditary terms -/

/-- **Hereditary terms of a sort**: its atoms, and sets of hereditary terms. -/
inductive Hereditary (language : LanguageDef) (sort : String) : Pattern → Prop
  | atom {label : String} : AtomOf language sort label → Hereditary language sort (token label)
  | members {values : List Pattern} : (∀ value ∈ values, Hereditary language sort value) →
      Hereditary language sort (set values)

mutual
/-- Whether a term is hereditary. -/
def hereditary (language : LanguageDef) (sort : String) : Pattern → Bool
  | .collection .hashSet values none => hereditaryList language sort values
  | term => isAtom language sort term

/-- Whether every term of a list is hereditary. -/
def hereditaryList (language : LanguageDef) (sort : String) : List Pattern → Bool
  | [] => true
  | value :: values => hereditary language sort value && hereditaryList language sort values
end

theorem Hereditary.cases {term : Pattern} (holds : Hereditary language sort term) :
    (∃ label, term = token label ∧ AtomOf language sort label) ∨
      (∃ values, term = set values ∧ ∀ value ∈ values, Hereditary language sort value) := by
  cases holds with
  | atom atom => exact Or.inl ⟨_, rfl, atom⟩
  | members inside => exact Or.inr ⟨_, rfl, inside⟩

theorem hereditary_set_iff {values : List Pattern} :
    Hereditary language sort (set values) ↔ ∀ value ∈ values, Hereditary language sort value := by
  constructor
  · intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, inside⟩
    · simp [set, token] at same
    · simp only [set, Pattern.collection.injEq, true_and, and_true] at same
      exact same ▸ inside
  · exact .members

theorem hereditaryList_iff : ∀ values : List Pattern,
    (∀ value ∈ values, (hereditary language sort value = true ↔ Hereditary language sort value)) →
      (hereditaryList language sort values = true ↔ ∀ value ∈ values, Hereditary language sort value)
  | [], _ => by simp [hereditaryList]
  | value :: values, each => by
    simp only [hereditaryList, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [each value List.mem_cons_self,
      hereditaryList_iff values fun other member => each other (List.mem_cons_of_mem _ member)]

theorem hereditary_iff : ∀ term : Pattern, hereditary language sort term = true ↔ Hereditary language sort term
  | .collection .hashSet values none => by
    rw [hereditary, hereditaryList_iff values fun value member =>
      have : sizeOf value < sizeOf values := List.sizeOf_lt_of_mem member
      hereditary_iff value]
    exact hereditary_set_iff.symm
  | .collection .hashSet values (some rest) => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .collection .hashBag values rest => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .collection .vec values rest => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .apply label arguments => by
    have unfold :
        hereditary language sort (.apply label arguments) = isAtom language sort (.apply label arguments) := by
      simp only [hereditary]
    rw [unfold, isAtom_iff]
    constructor
    · rintro ⟨atomLabel, same, atom⟩
      exact same ▸ .atom atom
    · intro holds
      rcases holds.cases with ⟨atomLabel, same, atom⟩ | ⟨other, same, -⟩
      · exact ⟨atomLabel, same, atom⟩
      · simp [set] at same
  | .bvar index => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .fvar name => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .lambda binder body => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .multiLambda arity binders body => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
  | .subst body replacement => by
    simp only [hereditary, isAtom, Bool.false_eq_true, false_iff]
    intro holds
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [set, token] at same
termination_by term => sizeOf term

/-- **Hereditary terms are closed object terms of the carrier's sort.** -/
theorem Hereditary.typed (setCarrier : SetCarrier language carrier carrier.category) {term : Pattern}
    (holds : Hereditary language carrier.category term) :
    (∀ free bound, HasType language free bound term (.base carrier.category)) ∧ IsState term := by
  induction holds with
  | atom atom => exact ⟨fun _ _ => atom_hasType atom, rfl, rfl⟩
  | @members values _ inside =>
    have elements : Elements language carrier.category values := fun value member => inside value member
    obtain ⟨name, shape⟩ := setCarrier.shape
    refine ⟨fun free bound => HasType.collectionConstructor (parameterName := name)
      (elementType := .base carrier.category) setCarrier.authored ?_ ?_, elements_state elements⟩
    · rw [GrammarRule.bareParams_of_bare _ setCarrier.bare, shape]
    · exact elementsHaveType_iff.mpr fun value member => (inside value member).1 free bound

theorem Hereditary.elements (setCarrier : SetCarrier language carrier carrier.category) {values : List Pattern}
    (inside : ∀ value ∈ values, Hereditary language carrier.category value) :
    Elements language carrier.category values := fun value member => (inside value member).typed setCarrier

/-! ## Heights -/

mutual
/-- The height of a set term: one more than its members'. -/
def height : Pattern → ℕ
  | .collection _ values _ => heightList values + 1
  | .bvar _ | .fvar _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => 0

/-- The greatest height in a list. -/
def heightList : List Pattern → ℕ
  | [] => 0
  | value :: values => max (height value) (heightList values)
end

theorem height_le_heightList : ∀ {values : List Pattern} {value : Pattern}, value ∈ values → height value ≤ heightList values
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: _, _, .tail _ member => (height_le_heightList member).trans (le_max_right _ _)

/-! ## Canonical forms -/

theorem sortBags_set_values (values : List Pattern) :
    BagForms.sortBags (set values) = set (arrange .hashSet (values.map BagForms.sortBags)) := by
  simp only [set, BagForms.sortBags, BagForms.sortBagsList_eq_map]

theorem Hereditary.sortBags {term : Pattern} (holds : Hereditary language sort term) :
    Hereditary language sort (BagForms.sortBags term) := by
  induction holds with
  | atom atom => exact .atom atom
  | @members values _ inside =>
    rw [sortBags_set_values]
    refine .members fun value member => ?_
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
    exact inside original originalMember

theorem hereditary_of_sortBags : ∀ term : Pattern,
    Hereditary language sort (BagForms.sortBags term) → Hereditary language sort term
  | .collection .hashSet values none, holds => by
    rw [show Pattern.collection .hashSet values none = set values from rfl, sortBags_set_values,
      hereditary_set_iff] at holds
    refine .members fun value member => ?_
    have : sizeOf value < sizeOf values := List.sizeOf_lt_of_mem member
    exact hereditary_of_sortBags value (holds _ ((arrange_mem _).mpr (List.mem_map_of_mem member)))
  | .apply label arguments, holds => by
    rcases holds.cases with ⟨atomLabel, same, atom⟩ | ⟨other, same, -⟩
    · simp only [BagForms.sortBags, token, Pattern.apply.injEq, BagForms.sortBagsList_eq_map,
        List.map_eq_nil_iff] at same
      rw [same.1, same.2]
      exact .atom atom
    · simp [BagForms.sortBags, set] at same
  | .collection .hashSet values (some rest), holds | .collection .hashBag values rest, holds
  | .collection .vec values rest, holds | .bvar index, holds | .fvar name, holds | .lambda binder body, holds
  | .multiLambda arity binders body, holds | .subst body replacement, holds => by
    rcases holds.cases with ⟨label, same, -⟩ | ⟨other, same, -⟩ <;> simp [BagForms.sortBags, set, token] at same
termination_by term => sizeOf term

/-- **A hereditary set language**: no authored equations, no collection algebra, and a bare carrier whose sets
hold terms of its own sort. -/
structure HereditaryLanguage (language : LanguageDef) (carrier : GrammarRule) : Prop where
  noEquations : language.equations = []
  noAlgebra : language.hasAlgebraDeclarations = false
  setCarrier : SetCarrier language carrier carrier.category

/-- **A hereditary term is equivalent to its canonical form.** -/
theorem hereditary_equivalent (lang : HereditaryLanguage language carrier) {term : Pattern}
    (holds : Hereditary language carrier.category term) :
    ObjectEquivalent relEnv language .syntax term (BagForms.sortBags term) := by
  induction holds with
  | atom _ => exact Relation.EqvGen.refl _
  | @members values inside equivalent =>
    have mapObject : ∀ pattern, IsObject pattern → IsObject (BagForms.sortBags pattern) := fun pattern object => by
      show isObjectPattern _ = true
      rw [BagForms.sortBags_eq_canon, BagForms.canon_object]
      exact object
    have objects : ∀ patterns : List Pattern, (∀ pattern ∈ patterns, IsObject pattern) →
        IsObject (.collection .hashSet patterns none) := fun patterns each => by
      show isObjectPattern (.collection .hashSet patterns none) = true
      simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
      exact isObjectPatternList_iff.mpr each
    have inner := ObjectEquivalent.list_congr (relEnv := relEnv) (language := language) BagForms.sortBags mapObject
      (fun patterns => .collection .hashSet patterns none)
      (fun before after => .collection .hashSet before .hole after none) (fun _ _ _ => rfl) objects values []
      (by simp) fun value member => ⟨((inside value member).typed lang.setCarrier).2.2, equivalent value member⟩
    simp only [List.nil_append] at inner
    have outer := toArranged (relEnv := relEnv) lang.setCarrier _ (values.map BagForms.sortBags) le_rfl
      (Hereditary.elements lang.setCarrier fun value member => by
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (inside original originalMember).sortBags)
    rw [sortBags_set_values]
    exact Relation.EqvGen.trans _ _ _ inner outer

/-- **Canonical forms for a hereditary set language**: every set sorted without repetition, bottom up; the domain is
read off them. -/
theorem hereditary_canonicalDetermined (lang : HereditaryLanguage language carrier) :
    CanonicalDetermined relEnv language BagForms.sortBags (hereditary language carrier.category) where
  object admitted := (((hereditary_iff _).mp admitted).typed lang.setCarrier).2.2
  determined term := by
    apply Bool.eq_iff_iff.mpr
    rw [hereditary_iff, hereditary_iff]
    exact ⟨hereditary_of_sortBags term, Hereditary.sortBags⟩
  equivalent admitted := hereditary_equivalent lang ((hereditary_iff _).mp admitted)
  same _ equivalent := by
    rw [BagForms.sortBags_eq_canon]
    exact BagForms.canon_eq_of_equivalent lang.noEquations lang.noAlgebra equivalent
  closed _ := by
    rw [BagForms.sortBags_eq_canon]
    exact BagForms.canon_wellScoped _ 0

/-- **Canonical forms for a hereditary set language**: every set sorted without repetition, bottom up. -/
theorem hereditary_canonical (lang : HereditaryLanguage language carrier) :
    Canonical relEnv language BagForms.sortBags (hereditary language carrier.category) :=
  (hereditary_canonicalDetermined lang).canonical

/-! ## Matching flat set patterns at presentations with copies -/

section Matching

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon Same canon_idempotent canon_collection arrange_eq_of_presents)
open BagForms (BindingsSame find?_same)

theorem mergeBindings_cons (first : Bindings) (entry : String × Pattern) (entries : Bindings) :
    mergeBindings first (entry :: entries) =
      (match first.find? (fun item : String × Pattern => item.1 == entry.1) with
        | none => some (entry :: first)
        | some (_, existing) => if existing == entry.2 then some first else none).bind
        fun accumulated => mergeBindings accumulated entries := by
  obtain ⟨name, value⟩ := entry
  rfl

/-- **Merging transfers to like captures**, when captures under one name that are alike are equal. -/
theorem mergeBindings_same (pool : Bindings)
    (injective : ∀ a ∈ pool, ∀ b ∈ pool, a.1 = b.1 → Same a.2 b.2 → a.2 = b.2) :
    ∀ (second : Bindings) {first first' second' result : Bindings},
      mergeBindings first second = some result → BindingsSame first first' → BindingsSame second second' →
      (∀ entry ∈ first', entry ∈ pool) → (∀ entry ∈ second', entry ∈ pool) →
      ∃ result', mergeBindings first' second' = some result' ∧ BindingsSame result result' ∧
        ∀ entry ∈ result', entry ∈ pool
  | [], first, first', second', result, merged, sameFirst, sameSecond, firstPool, _ => by
    cases sameSecond
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged ⊢
    subst merged
    exact ⟨first', rfl, sameFirst, firstPool⟩
  | entry :: entries, first, first', second', result, merged, sameFirst, sameSecond, firstPool, secondPool => by
    cases sameSecond with
    | @cons _ entry' _ entries' heads tail =>
      have tailPool : ∀ other ∈ entries', other ∈ pool := fun other member =>
        secondPool other (List.mem_cons_of_mem _ member)
      have entryPool : entry' ∈ pool := secondPool entry' List.mem_cons_self
      rw [mergeBindings_cons] at merged
      rw [mergeBindings_cons, show entry'.1 = entry.1 from heads.1.symm]
      rcases find?_same sameFirst entry.1 with ⟨none₁, none₂⟩ |
          ⟨⟨name, existing⟩, ⟨name', existing'⟩, hit, hit', names, sameValue⟩
      · rw [none₁] at merged
        rw [none₂]
        simp only [Option.bind_some] at merged ⊢
        exact mergeBindings_same pool injective entries merged (.cons heads sameFirst) tail
          (fun other member => by
            rcases List.mem_cons.mp member with rfl | member
            · exact entryPool
            · exact firstPool other member)
          tailPool
      · rw [hit] at merged
        rw [hit']
        have equal : existing = entry.2 := by
          by_contra different
          simp [different] at merged
        simp only [equal, beq_self_eq_true, if_true, Option.bind_some] at merged
        have foundPool : (name', existing') ∈ pool := firstPool _ (List.mem_of_find?_eq_some hit')
        have foundName : name' = entry'.1 := by
          have := List.find?_some hit'
          simp only [beq_iff_eq] at this
          rw [this, heads.1]
        have equal' : existing' = entry'.2 :=
          injective _ foundPool _ entryPool foundName
            ((sameValue.symm.trans (show Same existing entry.2 from equal ▸ rfl)).trans heads.2)
        simp only [equal', beq_self_eq_true, if_true, Option.bind_some]
        exact mergeBindings_same pool injective entries merged sameFirst tail firstPool tailPool

theorem member_canonical {values : List Pattern} (canonical : BagForms.sortBags (set values) = set values) :
    ∀ value ∈ values, BagForms.sortBags value = value := by
  intro value member
  rw [sortBags_set_values] at canonical
  have same : arrange .hashSet (values.map BagForms.sortBags) = values := by simpa [set] using canonical
  rw [← same] at member
  obtain ⟨original, -, rfl⟩ := List.mem_map.mp ((arrange_mem _).mp member)
  rw [BagForms.sortBags_eq_canon, canon_idempotent]

theorem matchArgs_self : ∀ values : List Pattern, (∀ value ∈ values, MatchRel value value []) →
    MatchArgsRel values values []
  | [], _ => .nil
  | value :: values, each =>
    .cons (each value List.mem_cons_self) (matchArgs_self values fun other member => each other
      (List.mem_cons_of_mem _ member)) rfl

/-- **A hereditary term matches itself**, binding nothing. -/
theorem match_self {pattern : Pattern} (holds : Hereditary language sort pattern) : MatchRel pattern pattern [] := by
  induction holds with
  | atom _ => exact matchRel_token _
  | @members values _ each =>
    exact .collection (by decide) ((matchArgs_self values each).toMatchBagRel .hashSet)

theorem closed_bag_match : ∀ (patterns elements : List Pattern) (bindings : Bindings),
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {bindings : Bindings}, Hereditary language sort term →
      MatchRel pattern term bindings → BagForms.sortBags term = pattern ∧ bindings = []) →
    (∀ element ∈ elements, Hereditary language sort element) → MatchBagRel patterns none .hashSet elements bindings →
    (∀ value, value ∈ elements.map BagForms.sortBags ↔ value ∈ patterns) ∧ bindings = []
  | [], elements, bindings, _, _, bag => by
    cases bag
    exact ⟨fun _ => by simp, rfl⟩
  | pattern :: patterns, elements, bindings, each, elementsHold, bag => by
    cases bag with
    | cons index bound head tail merged =>
      obtain ⟨same, rfl⟩ := each pattern List.mem_cons_self (elementsHold _ (List.getElem_mem bound)) head
      obtain ⟨members, rfl⟩ := closed_bag_match patterns _ _
        (fun other member => each other (List.mem_cons_of_mem _ member))
        (fun element member => elementsHold element (List.mem_of_mem_eraseIdx member)) tail
      refine ⟨fun value => ?_, by simpa [mergeBindings] using merged.symm⟩
      have counted := count_eraseIdx (elements.map BagForms.sortBags) index (by simpa using bound) value
      rw [List.eraseIdx_map] at counted
      simp only [List.getElem_map, same] at counted
      rw [List.mem_cons, ← members value, ← List.count_pos_iff, ← List.count_pos_iff, counted]
      by_cases hit : pattern = value
      · subst hit
        simp
      · simp only [beq_iff_eq, hit, if_false, Nat.add_zero]
        constructor
        · exact Or.inr
        · rintro (rfl | positive)
          · exact absurd rfl hit
          · exact positive

/-- **A closed hereditary canonical pattern matches only presentations of itself**, binding nothing. -/
theorem closed_match {pattern : Pattern} (holds : Hereditary language sort pattern)
    (canonical : BagForms.sortBags pattern = pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, Hereditary language sort term → MatchRel pattern term bindings →
      BagForms.sortBags term = pattern ∧ bindings = [] := by
  induction holds with
  | atom atom =>
    intro term bindings _ matched
    obtain ⟨rfl, rfl⟩ := matchRel_atom matched
    exact ⟨rfl, rfl⟩
  | @members values inside ih =>
    intro term bindings termHolds matched
    have canonicalMembers := member_canonical canonical
    rcases termHolds.cases with ⟨label, rfl, -⟩ | ⟨terms, rfl, termsHold⟩
    · cases matched
    · cases matched with
      | collection _ bag =>
        obtain ⟨members, rfl⟩ := closed_bag_match values terms bindings
          (fun value member => ih value member (canonicalMembers value member)) termsHold bag
        refine ⟨?_, rfl⟩
        have arranged : arrange .hashSet values = values := by
          have := canonical
          rw [sortBags_set_values] at this
          have fixed : values.map BagForms.sortBags = values := by
            conv_rhs => rw [← List.map_id values]
            exact List.map_congr_left canonicalMembers
          simpa [set, fixed] using this
        rw [sortBags_set_values, arrange_eq_of_presents (kind := .hashSet) members, arranged]

/-! ## Closed patterns at object terms -/

/-- **Hereditary terms are object terms.** -/
theorem Hereditary.object {term : Pattern} (holds : Hereditary language sort term) : IsObject term := by
  induction holds with
  | atom _ => rfl
  | @members values _ inside =>
    show isObjectPattern (.collection .hashSet values none) = true
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
    exact isObjectPatternList_iff.mpr inside

theorem closed_bag_match_object : ∀ (patterns elements : List Pattern) (bindings : Bindings),
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {bindings : Bindings}, IsObject term →
      MatchRel pattern term bindings → BagForms.sortBags term = pattern ∧ bindings = []) →
    (∀ element ∈ elements, IsObject element) → MatchBagRel patterns none .hashSet elements bindings →
    (∀ value, value ∈ elements.map BagForms.sortBags ↔ value ∈ patterns) ∧ bindings = []
  | [], elements, bindings, _, _, bag => by
    cases bag
    exact ⟨fun _ => by simp, rfl⟩
  | pattern :: patterns, elements, bindings, each, elementsObject, bag => by
    cases bag with
    | cons index bound head tail merged =>
      obtain ⟨same, rfl⟩ := each pattern List.mem_cons_self (elementsObject _ (List.getElem_mem bound)) head
      obtain ⟨members, rfl⟩ := closed_bag_match_object patterns _ _
        (fun other member => each other (List.mem_cons_of_mem _ member))
        (fun element member => elementsObject element (List.mem_of_mem_eraseIdx member)) tail
      refine ⟨fun value => ?_, by simpa [mergeBindings] using merged.symm⟩
      have counted := count_eraseIdx (elements.map BagForms.sortBags) index (by simpa using bound) value
      rw [List.eraseIdx_map] at counted
      simp only [List.getElem_map, same] at counted
      rw [List.mem_cons, ← members value, ← List.count_pos_iff, ← List.count_pos_iff, counted]
      by_cases hit : pattern = value
      · subst hit
        simp
      · simp only [beq_iff_eq, hit, if_false, Nat.add_zero]
        constructor
        · exact Or.inr
        · rintro (rfl | positive)
          · exact absurd rfl hit
          · exact positive

/-- **A closed hereditary canonical pattern matches only presentations of itself** among object terms, binding
nothing. -/
theorem closed_match_object {pattern : Pattern} (holds : Hereditary language sort pattern)
    (canonical : BagForms.sortBags pattern = pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, IsObject term → MatchRel pattern term bindings →
      BagForms.sortBags term = pattern ∧ bindings = [] := by
  induction holds with
  | atom atom =>
    intro term bindings _ matched
    obtain ⟨rfl, rfl⟩ := matchRel_atom matched
    exact ⟨rfl, rfl⟩
  | @members values inside ih =>
    intro term bindings termObject matched
    have canonicalMembers := member_canonical canonical
    change MatchRel (.collection .hashSet values none) term bindings at matched
    cases matched with
    | @collection _ _ _ terms _ rest _ bag =>
      have parts : rest = none ∧ ∀ value ∈ terms, IsObject value := by
        simpa [IsObject, isObjectPattern, isObjectPatternList_iff, Option.isNone_iff_eq_none] using termObject
      obtain ⟨rfl, termsObject⟩ := parts
      obtain ⟨members, rfl⟩ := closed_bag_match_object values terms bindings
        (fun value member => ih value member (canonicalMembers value member)) termsObject bag
      refine ⟨?_, rfl⟩
      have arranged : arrange .hashSet values = values := by
        have := canonical
        rw [sortBags_set_values] at this
        have fixed : values.map BagForms.sortBags = values := by
          conv_rhs => rw [← List.map_id values]
          exact List.map_congr_left canonicalMembers
        simpa [set, fixed] using this
      show BagForms.sortBags (set terms) = set values
      rw [sortBags_set_values, arrange_eq_of_presents (kind := .hashSet) members, arranged]

/-- **A presentation covers another up to `width` matched copies**: its terms are canonical, and it holds each
class as often as the other does when that is at most `width` times, and more than `width` times otherwise. -/
def Covers (width : ℕ) (terms others : List Pattern) : Prop :=
  ∀ value, ((terms.map BagForms.sortBags).count value ≤ width →
      others.count value = (terms.map BagForms.sortBags).count value) ∧
    (width < (terms.map BagForms.sortBags).count value → width + 1 ≤ others.count value)

theorem Covers.erase {width : ℕ} {terms others : List Pattern} (covers : Covers (width + 1) terms others)
    {index partner : ℕ} (bound : index < terms.length) (partnerBound : partner < others.length)
    (same : others[partner] = BagForms.sortBags terms[index]) :
    Covers width (terms.eraseIdx index) (others.eraseIdx partner) := by
  intro value
  have countedTerms := count_eraseIdx (terms.map BagForms.sortBags) index (by simpa using bound) value
  rw [List.eraseIdx_map] at countedTerms
  simp only [List.getElem_map] at countedTerms
  have countedOthers := count_eraseIdx others partner partnerBound value
  rw [same] at countedOthers
  obtain ⟨low, high⟩ := covers value
  by_cases hit : BagForms.sortBags terms[index] = value
  · simp only [hit, beq_self_eq_true, if_true] at countedTerms countedOthers
    constructor
    · intro small
      have := low (by omega)
      omega
    · intro large
      by_cases small : (terms.map BagForms.sortBags).count value ≤ width + 1
      · have := low small
        omega
      · have := high (by omega)
        omega
  · simp only [beq_iff_eq, hit, if_false, Nat.add_zero] at countedTerms countedOthers
    rw [← countedTerms, ← countedOthers]
    constructor
    · intro small
      exact low (by omega)
    · intro large
      by_cases small : (terms.map BagForms.sortBags).count value ≤ width + 1
      · have := low small
        omega
      · have := high (by omega)
        omega

/-- Element patterns of a flat set rule: metavariables other than the rest, and closed hereditary canonical
terms. -/
def FlatElement (language : LanguageDef) (sort : String) (rest : Option String) (pattern : Pattern) : Prop :=
  (∃ name, pattern = .fvar name ∧ rest ≠ some name) ∨
    (Hereditary language sort pattern ∧ BagForms.sortBags pattern = pattern)

/-- Captures other than the rest are canonical, and the rest is captured at most once. -/
def CanonicalCaptures (rest : Option String) (bindings : Bindings) : Prop :=
  (∀ entry ∈ bindings, rest ≠ some entry.1 → BagForms.sortBags entry.2 = entry.2) ∧
    ∀ a ∈ bindings, ∀ b ∈ bindings, rest = some a.1 → rest = some b.1 → a = b

theorem same_of_canonical {first second : Pattern} (firstCanonical : BagForms.sortBags first = first)
    (secondCanonical : BagForms.sortBags second = second) (same : Same first second) : first = second := by
  unfold Same at same
  rw [← BagForms.sortBags_eq_canon] at same
  rw [← firstCanonical, ← secondCanonical]
  exact same

/-- **A match of a flat set pattern transfers to any canonical presentation that covers it**, with like captures. -/
theorem flat_transfer : ∀ (patterns : List Pattern) (rest : Option String) (terms others : List Pattern)
    (bindings : Bindings), (∀ pattern ∈ patterns, FlatElement language sort rest pattern) →
    (∀ term ∈ terms, Hereditary language sort term) → (∀ other ∈ others, BagForms.sortBags other = other) →
    Covers patterns.length terms others → MatchBagRel patterns rest .hashSet terms bindings →
    ∃ bindings', MatchBagRel patterns rest .hashSet others bindings' ∧ BindingsSame bindings bindings' ∧
      CanonicalCaptures rest bindings'
  | [], none, terms, others, bindings, _, _, _, covers, bag => by
    cases bag
    have empty : others = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro value member
      have := (covers value).1 (by simp)
      simp only [List.map_nil, List.count_nil] at this
      exact absurd this (Nat.pos_iff_ne_zero.mp (List.count_pos_iff.mpr member))
    subst empty
    exact ⟨[], .nilNoRest, .nil, fun _ member => by simp at member, fun _ member => by simp at member⟩
  | [], some name, terms, others, bindings, _, _, othersCanonical, covers, bag => by
    cases bag
    simp only [List.length_nil] at covers
    refine ⟨[(name, .collection .hashSet others none)], .nilRest, .cons ⟨rfl, ?_⟩ .nil,
      fun entry member notRest => ?_, fun a aMember b bMember _ _ => ?_⟩
    · unfold Same
      rw [canon_collection, canon_collection]
      congr 1
      apply arrange_eq_of_presents
      intro value
      have fixed : others.map canon = others := by
        conv_rhs => rw [← List.map_id others]
        exact List.map_congr_left fun other member => by
          rw [← BagForms.sortBags_eq_canon]
          exact othersCanonical other member
      rw [fixed, ← BagForms.sortBags_eq_canon, ← List.count_pos_iff, ← List.count_pos_iff]
      obtain ⟨low, high⟩ := covers value
      by_cases zero : (terms.map BagForms.sortBags).count value = 0
      · have := low (by omega)
        omega
      · have := high (by omega)
        omega
    · simp only [List.mem_singleton] at member
      subst member
      exact absurd rfl notRest
    · simp only [List.mem_singleton] at aMember bMember
      rw [aMember, bMember]
  | pattern :: patterns, rest, terms, others, bindings, flat, termsHold, othersCanonical, covers, bag => by
    cases bag with
    | cons index bound head tail merged =>
      rename_i headBindings tailBindings
      have present : 0 < others.count (BagForms.sortBags terms[index]) := by
        have positive : 0 < (terms.map BagForms.sortBags).count (BagForms.sortBags terms[index]) :=
          List.count_pos_iff.mpr (List.mem_map_of_mem (List.getElem_mem bound))
        obtain ⟨low, high⟩ := covers (BagForms.sortBags terms[index])
        by_cases small : (terms.map BagForms.sortBags).count (BagForms.sortBags terms[index]) ≤
            (pattern :: patterns).length
        · have := low small
          omega
        · have := high (by omega)
          omega
      obtain ⟨partner, partnerBound, partnerIs⟩ := List.getElem_of_mem (List.count_pos_iff.mp present)
      have partnerCanonical : BagForms.sortBags others[partner] = others[partner] :=
        othersCanonical _ (List.getElem_mem partnerBound)
      obtain ⟨headBindings', head', headSame, headCanonical⟩ :
          ∃ headBindings', MatchRel pattern others[partner] headBindings' ∧ BindingsSame headBindings headBindings' ∧
            ∀ entry ∈ headBindings', rest ≠ some entry.1 ∧ BagForms.sortBags entry.2 = entry.2 := by
        rcases flat pattern List.mem_cons_self with ⟨name, rfl, notRest⟩ | ⟨closed, canonical⟩
        · cases head
          refine ⟨[(name, others[partner])], .fvar, .cons ⟨rfl, ?_⟩ .nil, fun entry member => ?_⟩
          · unfold Same
            rw [partnerIs, ← BagForms.sortBags_eq_canon, BagForms.sortBags_eq_canon, canon_idempotent]
          · simp only [List.mem_singleton] at member
            subst member
            exact ⟨notRest, partnerCanonical⟩
        · obtain ⟨equal, rfl⟩ := closed_match closed canonical (termsHold _ (List.getElem_mem bound)) head
          refine ⟨[], ?_, .nil, fun _ member => by simp at member⟩
          rw [partnerIs, equal]
          exact match_self closed
      obtain ⟨tailBindings', tail', tailSame, tailCaptures⟩ := flat_transfer patterns rest (terms.eraseIdx index)
        (others.eraseIdx partner) tailBindings (fun other member => flat other (List.mem_cons_of_mem _ member))
        (fun term member => termsHold term (List.mem_of_mem_eraseIdx member))
        (fun other member => othersCanonical other (List.mem_of_mem_eraseIdx member))
        (covers.erase bound partnerBound partnerIs) tail
      have injective : ∀ a ∈ headBindings' ++ tailBindings', ∀ b ∈ headBindings' ++ tailBindings', a.1 = b.1 →
          Same a.2 b.2 → a.2 = b.2 := by
        intro a aMember b bMember names same
        by_cases restName : rest = some a.1
        · have aTail : a ∈ tailBindings' := by
            rcases List.mem_append.mp aMember with inHead | inTail
            · exact absurd restName (headCanonical a inHead).1
            · exact inTail
          have bTail : b ∈ tailBindings' := by
            rcases List.mem_append.mp bMember with inHead | inTail
            · exact absurd (names ▸ restName) (headCanonical b inHead).1
            · exact inTail
          rw [tailCaptures.2 a aTail b bTail restName (names ▸ restName)]
        · have canonicalOf : ∀ entry ∈ headBindings' ++ tailBindings', rest ≠ some entry.1 →
              BagForms.sortBags entry.2 = entry.2 := fun entry member notRest => by
            rcases List.mem_append.mp member with inHead | inTail
            · exact (headCanonical entry inHead).2
            · exact tailCaptures.1 entry inTail notRest
          exact same_of_canonical (canonicalOf a aMember restName) (canonicalOf b bMember (names ▸ restName)) same
      obtain ⟨bindings', merged', same, inPool⟩ := mergeBindings_same (headBindings' ++ tailBindings') injective
        tailBindings merged headSame tailSame (fun entry member => List.mem_append_left _ member)
        (fun entry member => List.mem_append_right _ member)
      refine ⟨bindings', .cons partner partnerBound head' tail' merged', same, fun entry member notRest => ?_,
        fun a aMember b bMember aRest bRest => ?_⟩
      · rcases List.mem_append.mp (inPool entry member) with inHead | inTail
        · exact (headCanonical entry inHead).2
        · exact tailCaptures.1 entry inTail notRest
      · have aTail : a ∈ tailBindings' := by
          rcases List.mem_append.mp (inPool a aMember) with inHead | inTail
          · exact absurd aRest (headCanonical a inHead).1
          · exact inTail
        have bTail : b ∈ tailBindings' := by
          rcases List.mem_append.mp (inPool b bMember) with inHead | inTail
          · exact absurd bRest (headCanonical b inHead).1
          · exact inTail
        exact tailCaptures.2 a aTail b bTail aRest bRest

end Matching

/-! ## Flat set languages at the front door -/

section Flat

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_idempotent)

/-- Extra copies of a list's terms: each written between none and `width` more times. -/
def copyChoices (width : ℕ) : List Pattern → List (List Pattern)
  | [] => [[]]
  | value :: values => (copyChoices width values).flatMap fun copies =>
      (List.range (width + 1)).map fun count => List.replicate count value ++ copies

theorem mem_copyChoices (width : ℕ) (extra : Pattern → ℕ) (bounded : ∀ value, extra value ≤ width) :
    ∀ values : List Pattern, values.flatMap (fun value => List.replicate (extra value) value) ∈ copyChoices width values
  | [] => by simp [copyChoices]
  | value :: values => by
    simp only [copyChoices, List.flatMap_cons, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨_, mem_copyChoices width extra bounded values, extra value, by have := bounded value; omega, rfl⟩

theorem count_copies (extra : Pattern → ℕ) : ∀ (values : List Pattern), values.Nodup → ∀ value,
    (values.flatMap fun other => List.replicate (extra other) other).count value =
      if value ∈ values then extra value else 0
  | [], _, value => by simp
  | head :: tail, distinct, value => by
    rw [List.flatMap_cons, List.count_append, count_copies extra tail (List.nodup_cons.mp distinct).2 value,
      List.count_replicate]
    by_cases hit : head = value
    · subst hit
      simp [(List.nodup_cons.mp distinct).1]
    · have hit' : ¬ value = head := fun same => hit same.symm
      by_cases inTail : value ∈ tail <;> simp [hit, hit', inTail]

/-- **Presentations with copies**: a canonical set with each member written up to `width + 1` times. -/
def copiesPresentations (width : ℕ) : Pattern → List Pattern
  | .collection .hashSet values none =>
    (copyChoices width values).map fun copies => .collection .hashSet (values ++ copies) none
  | other => [other]

/-- **A flat set language**: a hereditary set language whose rules rewrite a set at the root, matching at most
`width` members by metavariables or closed canonical terms, with no premises. -/
structure FlatSetLanguage (language : LanguageDef) (carrier : GrammarRule) (width : ℕ) : Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, ∃ patterns rest, rule.left = .collection .hashSet patterns rest ∧
    patterns.length ≤ width ∧ (∀ pattern ∈ patterns, FlatElement language carrier.category rest pattern) ∧
    rule.premises = []

variable {width : ℕ}

/-- **Coherence for flat set languages**: a step from any presentation of a canonical hereditary set is matched,
with the same labels and up to canonical form, by a step listed at a presentation with copies. -/
theorem flat_coherent (lang : FlatSetLanguage language carrier width) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (hereditary language carrier.category)
      (copiesPresentations width) := by
  intro state redex witness contractum _ admitted canonState complete before _ valid
  have canonical := hereditary_canonical (relEnv := relEnv) lang.hereditary
  have redexHolds : Hereditary language carrier.category redex :=
    (hereditary_iff _).mp (canonical.invariant admitted before)
  have redexCanon : BagForms.sortBags redex = state := ((canonical.same admitted before).symm).trans canonState
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨patterns, rest, leftIs, short, flat, noPremises⟩ := lang.rules rule (List.mem_of_getElem? found)
    rw [noPremises] at premises
    cases premises
    rw [matchPatternForRule_eq_syntactic, leftIs] at matched
    have related := matchPattern_iff_matchRel.mp matched
    cases related with
    | collection _ bag =>
      rename_i terms restTerm _ _
      obtain ⟨presented, same, termsHold⟩ : ∃ presented, Pattern.collection .hashSet terms restTerm = set presented ∧
          ∀ term ∈ presented, Hereditary language carrier.category term := by
        rcases redexHolds.cases with ⟨label, same, -⟩ | ⟨presented, same, inside⟩
        · simp [token] at same
        · exact ⟨presented, same, inside⟩
      simp only [set, Pattern.collection.injEq, true_and] at same
      obtain ⟨rfl, rfl⟩ := same
      let values := arrange .hashSet (terms.map BagForms.sortBags)
      have stateIs : state = set values := by
        rw [← redexCanon]
        exact sortBags_set_values terms
      subst stateIs
      have distinct : values.Nodup := List.nodup_dedup _
      have valuesCanonical : ∀ value ∈ values, BagForms.sortBags value = value := fun value member => by
        obtain ⟨original, -, rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
        rw [BagForms.sortBags_eq_canon, canon_idempotent]
      let extra := fun value => (if (terms.map BagForms.sortBags).count value ≤ patterns.length then
        (terms.map BagForms.sortBags).count value else patterns.length + 1) - 1
      let copies := values.flatMap fun value => List.replicate (extra value) value
      have othersCanonical : ∀ other ∈ values ++ copies, BagForms.sortBags other = other := by
        intro other member
        rcases List.mem_append.mp member with inValues | inCopies
        · exact valuesCanonical other inValues
        · obtain ⟨value, inValues, inReplicate⟩ := List.mem_flatMap.mp inCopies
          rw [List.eq_of_mem_replicate inReplicate]
          exact valuesCanonical value inValues
      have covers : Covers patterns.length terms (values ++ copies) := by
        intro value
        rw [List.count_append, count_copies extra values distinct value, distinct.count]
        have inValues : value ∈ values ↔ 0 < (terms.map BagForms.sortBags).count value := by
          rw [arrange_mem, List.count_pos_iff]
        by_cases member : value ∈ values
        · have positive := inValues.mp member
          simp only [member, if_true, extra]
          constructor
          · intro small
            simp only [small, if_true]
            omega
          · intro large
            simp only [show ¬ (terms.map BagForms.sortBags).count value ≤ patterns.length by omega, if_false]
            omega
        · have zero : (terms.map BagForms.sortBags).count value = 0 := by
            by_contra nonzero
            exact member (inValues.mpr (by omega))
          simp only [member, if_false, zero]
          exact ⟨fun _ => trivial, fun impossible => absurd impossible (Nat.not_lt_zero _)⟩
      obtain ⟨bindings', bag', sameBindings, -⟩ := flat_transfer patterns rest terms (values ++ copies) initial flat
        termsHold othersCanonical covers bag
      have matched' : bindings' ∈ matchPatternForRule language rule (.collection .hashSet (values ++ copies) none) := by
        rw [matchPatternForRule_eq_syntactic, leftIs]
        exact matchPattern_iff_matchRel.mpr (.collection (by decide) bag')
      have fired := StepValid.rule (relEnv := relEnv) found matched' (by rw [noPremises]; exact .nil _)
      have shown : Pattern.collection .hashSet (values ++ copies) none ∈ copiesPresentations width (set values) := by
        simp only [set, copiesPresentations, List.mem_map]
        exact ⟨copies, mem_copyChoices width extra (fun value => by simp only [extra]; split <;> omega) values, rfl⟩
      refine ⟨(.rule index bindings' [], applyBindingsScoped (captureSites rule) bindings' 0 rule.right),
        mem_listedAt.mpr ⟨_, shown, mem_stepsAt_of_enough (enoughAt_iff.mp complete _ shown) fired⟩,
        fun label => by cases label <;> rfl, ?_⟩
      rw [BagForms.sortBags_eq_canon]
      exact (BagForms.applyBindingsScoped_same (captureSites rule) sameBindings 0 rule.right).symm

/-- **Canonical forms for a flat set language**, for the front door. -/
def flatForms (lang : FlatSetLanguage language carrier width) (fuel : ℕ) : CanonicalForms relEnv language fuel :=
  .ofCoherent (hereditary_canonical lang.hereditary) (flat_coherent lang fuel)

end Flat

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
