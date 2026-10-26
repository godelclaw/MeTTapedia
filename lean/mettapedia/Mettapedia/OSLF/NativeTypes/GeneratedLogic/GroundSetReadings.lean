import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping
import Mathlib.Data.List.Sublists

/-!
# The three readings of ground set rules

A **ground set rule** takes atoms from a set and gives atoms back, keeping the rest:
`{a₁, …, aₖ, ...rest} ⇒ {b₁, …, bₘ, ...rest}`, with the atoms taken distinct and no premises. A language of
such rules is the set analogue of a Petri net. For it, the three readings of `SetReadings` are characterized
exactly, from a canonical set `S` of atoms, for a rule taking `P` and giving `Q` with `P ⊆ S`:
- consume steps to `(S ∖ P) ∪ Q`;
- keep steps to `S ∪ Q`;
- either steps to `(S ∖ C) ∪ Q`, for every `C ⊆ P`: the members of `P` written once in the presentation are
  consumed, the others stay.

Consequences:
- for rules taking one atom, either is consume together with keep;
- for rules taking several, either has the mixtures besides;
- consume encodes the other two, by giving back what it takes: keep is consume with each rule giving back all it
  takes, and either is consume with each rule giving back each part of it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)

/-! ## Ground set rules -/

/-- **A ground set rule**: `rule` takes the atoms `takes` from a set and gives the atoms `gives`, keeping the rest,
with the atoms taken distinct and no premises. -/
structure GroundSetRule (rule : RewriteRule) (takes gives : List String) (rest : String) : Prop where
  left : rule.left = .collection .hashSet (takes.map token) (some rest)
  right : rule.right = .collection .hashSet (gives.map token) (some rest)
  noPremises : rule.premises = []
  distinct : takes.Nodup

/-- Every rule of the language is a ground set rule. -/
def GroundRules (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.rewrites, ∃ takes gives rest, GroundSetRule rule takes gives rest

theorem count_eraseIdx : ∀ (list : List Pattern) (index : ℕ) (bound : index < list.length) (value : Pattern),
    list.count value = (list.eraseIdx index).count value + (if list[index] == value then 1 else 0)
  | _ :: _, 0, _, value => by simp [List.count_cons]
  | _ :: tail, index + 1, bound, value => by
    have recurse := count_eraseIdx tail index (by simpa using bound) value
    simp only [List.eraseIdx_cons_succ, List.count_cons, List.getElem_cons_succ]
    omega

theorem matchRel_token (label : String) : MatchRel (token label) (token label) [] := .apply .nil rfl

/-- An atom matches only itself, binding nothing. -/
theorem matchRel_atom {label : String} {value : Pattern} {bindings : Bindings}
    (matched : MatchRel (token label) value bindings) : value = token label ∧ bindings = [] := by
  cases matched with
  | apply arguments _ =>
    cases arguments
    exact ⟨rfl, rfl⟩

/-- **A set pattern of atoms, matched**: its rest holds what remains once each atom of the pattern is taken once. -/
theorem matchAtoms : ∀ {takes : List String} {rest : String} {kind : CollType} {values : List Pattern}
    {bindings : Bindings}, MatchBagRel (takes.map token) (some rest) kind values bindings →
    ∃ residual, bindings = [(rest, .collection kind residual none)] ∧
      ∀ value, values.count value = residual.count value + (takes.map token).count value
  | [], rest, kind, values, bindings, matched => by
    cases matched
    exact ⟨values, rfl, fun value => by simp⟩
  | label :: _, _, _, values, _, matched => by
    cases matched with
    | cons index bound head tail merged =>
      obtain ⟨atIndex, rfl⟩ := matchRel_atom head
      obtain ⟨residual, rfl, counted⟩ := matchAtoms tail
      simp only [mergeBindings, List.foldlM, List.find?_nil, Option.bind_eq_bind] at merged
      refine ⟨residual, by simpa using merged.symm, fun value => ?_⟩
      have erased := count_eraseIdx values index bound value
      rw [atIndex] at erased
      have tailCount := counted value
      simp only [List.map_cons, List.count_cons]
      omega

/-- **A set pattern of distinct atoms matches wherever its atoms are present.** -/
theorem matchAtoms_exists : ∀ {takes : List String} {rest : String} {kind : CollType} {values : List Pattern},
    takes.Nodup → (∀ label ∈ takes, token label ∈ values) →
    ∃ residual, MatchBagRel (takes.map token) (some rest) kind values [(rest, .collection kind residual none)] ∧
      ∀ value, values.count value = residual.count value + (takes.map token).count value
  | [], _, _, values, _, _ => ⟨values, .nilRest, fun value => by simp⟩
  | label :: takes, rest, kind, values, distinct, present => by
    obtain ⟨index, bound, atIndex⟩ := List.getElem_of_mem (present label (by simp))
    have remaining : ∀ other ∈ takes, token other ∈ values.eraseIdx index := by
      intro other otherMember
      have differ : label ≠ other := fun same => (List.nodup_cons.mp distinct).1 (same ▸ otherMember)
      have erased := count_eraseIdx values index bound (token other)
      rw [atIndex] at erased
      have positive := List.count_pos_iff.mpr (present other (by simp [otherMember]))
      have unequal : (token label == token other) = false := by simp [token, differ]
      rw [unequal] at erased
      exact List.count_pos_iff.mp (by simp at erased; omega)
    obtain ⟨residual, tail, counted⟩ := matchAtoms_exists (rest := rest) (kind := kind)
      (List.nodup_cons.mp distinct).2 remaining
    refine ⟨residual, .cons index bound (by rw [atIndex]; exact matchRel_token label) tail
      (by simp [mergeBindings]), fun value => ?_⟩
    have erased := count_eraseIdx values index bound value
    rw [atIndex] at erased
    have tailCount := counted value
    simp only [List.map_cons, List.count_cons]
    omega

variable {relEnv : RelationEnv} {language : LanguageDef}

theorem applyBindingsScoped_tokens (lhs : Pattern) (bindings : Bindings) (depth : ℕ) (labels : List String) :
    (labels.map token).map (applyBindingsScoped lhs bindings depth) = labels.map token := by
  induction labels with
  | nil => rfl
  | cons label labels recurse => simp [token, recurse]

/-- **A ground set rule fires at a presentation of atoms** whenever its atoms are present, to what it gives
followed by what remains. -/
theorem ground_fires {index : ℕ} {rule : RewriteRule} {takes gives : List String} {rest : String}
    (found : language.rewrites[index]? = some rule) (ground : GroundSetRule rule takes gives rest)
    {values : List Pattern} (present : ∀ label ∈ takes, token label ∈ values) :
    ∃ residual, (∀ value, values.count value = residual.count value + (takes.map token).count value) ∧
      StepValid relEnv language (.collection .hashSet values none)
        (.rule index [(rest, .collection .hashSet residual none)] [])
        (.collection .hashSet (gives.map token ++ residual) none) := by
  obtain ⟨residual, bag, counted⟩ := matchAtoms_exists (rest := rest) (kind := .hashSet) ground.distinct present
  refine ⟨residual, counted, ?_⟩
  have matched : [(rest, .collection .hashSet residual none)] ∈ matchPatternForRule language rule
      (.collection .hashSet values none) := by
    rw [matchPatternForRule_eq_syntactic, ground.left]
    exact matchPattern_iff_matchRel.mpr (.collection (by decide) bag)
  have fired := StepValid.rule (relEnv := relEnv) found matched (by rw [ground.noPremises]; exact .nil _)
  rw [ground.right] at fired
  simpa only [applyBindingsScoped, restSplice_keeps (by simp : List.find? (·.1 == rest)
      [(rest, Pattern.collection .hashSet residual none)] = some (rest, .collection .hashSet residual none)),
    applyBindingsScopedList_eq_map, applyBindingsScoped_tokens] using fired

/-- **Every step of a ground set language at a presentation is such a firing.** -/
theorem ground_step {witness : Witness} {values : List Pattern} {target : Pattern} (rules : GroundRules language)
    (valid : StepValid relEnv language (.collection .hashSet values none) witness target) :
    ∃ index rule takes gives rest residual, language.rewrites[index]? = some rule ∧
      GroundSetRule rule takes gives rest ∧
      (∀ value, values.count value = residual.count value + (takes.map token).count value) ∧
      witness = .rule index [(rest, .collection .hashSet residual none)] [] ∧
      target = .collection .hashSet (gives.map token ++ residual) none := by
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨takes, gives, rest, ground⟩ := rules rule (List.mem_of_getElem? found)
    rw [ground.noPremises] at premises
    cases premises
    rw [matchPatternForRule_eq_syntactic, ground.left] at matched
    have related := matchPattern_iff_matchRel.mp matched
    cases related with
    | collection _ bag =>
      obtain ⟨residual, rfl, counted⟩ := matchAtoms bag
      refine ⟨index, rule, takes, gives, rest, residual, found, ground, counted, rfl, ?_⟩
      rw [ground.right]
      simp only [applyBindingsScoped, restSplice_keeps (by simp : List.find? (·.1 == rest)
          [(rest, Pattern.collection .hashSet residual none)] = some (rest, .collection .hashSet residual none)),
        applyBindingsScopedList_eq_map, applyBindingsScoped_tokens]

/-! ## Presentations of a set of atoms -/

section Presentations

open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance SortedAt CollectionCarrierRule)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem arrange_eq_of_presents)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (sortLex sortLex_perm)

/-- An atom of the sort: a constructor of it with no parameters. -/
def AtomOf (language : LanguageDef) (sort label : String) : Prop :=
  ∃ rule ∈ language.terms, rule.label = label ∧ rule.category = sort ∧ rule.params = []

/-- **A bare carrier of sets of a sort**: an authored constructor whose one parameter is a set of that sort. -/
structure SetCarrier (language : LanguageDef) (carrier : GrammarRule) (sort : String) : Prop where
  authored : carrier ∈ language.terms
  shape : ∃ name, carrier.params = [.simple name (.collection .hashSet (.base sort))]
  bare : carrier.collectionRepresentation = .bare

/-- **A ground set language**: no authored equations and no collection algebra, a bare carrier of sets of atoms
of one sort, and ground set rules. -/
structure GroundSetLanguage (language : LanguageDef) (carrier : GrammarRule) (sort : String) : Prop where
  noEquations : language.equations = []
  noAlgebra : language.hasAlgebraDeclarations = false
  setCarrier : SetCarrier language carrier sort
  rules : GroundRules language
  atomsOfSort : ∀ rule ∈ language.rewrites, ∀ takes gives rest, GroundSetRule rule takes gives rest →
    ∀ label ∈ takes ++ gives, AtomOf language sort label

/-- Every value is an atom of the sort. -/
def Atoms (language : LanguageDef) (sort : String) (values : List Pattern) : Prop :=
  ∀ value ∈ values, ∃ label, value = token label ∧ AtomOf language sort label

/-- Every value is a closed object term of the sort. -/
def Elements (language : LanguageDef) (sort : String) (values : List Pattern) : Prop :=
  ∀ value ∈ values, (∀ free bound, HasType language free bound value (.base sort)) ∧ IsState value

variable {carrier : GrammarRule} {sort : String}

theorem Atoms.append {first second : List Pattern} (firstAtoms : Atoms language sort first)
    (secondAtoms : Atoms language sort second) : Atoms language sort (first ++ second) := by
  intro value member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact firstAtoms value inFirst
  · exact secondAtoms value inSecond

theorem Atoms.of_subset {first second : List Pattern} (atoms : Atoms language sort second)
    (inside : ∀ value ∈ first, value ∈ second) : Atoms language sort first :=
  fun value member => atoms value (inside value member)

theorem Elements.append {first second : List Pattern} (firstElements : Elements language sort first)
    (secondElements : Elements language sort second) : Elements language sort (first ++ second) := by
  intro value member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact firstElements value inFirst
  · exact secondElements value inSecond

theorem Elements.of_subset {first second : List Pattern} (elements : Elements language sort second)
    (inside : ∀ value ∈ first, value ∈ second) : Elements language sort first :=
  fun value member => elements value (inside value member)

theorem atom_hasType {label : String} (atom : AtomOf language sort label) {free : FreeTypeContext}
    {bound : List TypeExpr} : HasType language free bound (token label) (.base sort) := by
  obtain ⟨rule, member, rfl, rfl, parameters⟩ := atom
  refine HasType.constructor member ?_ (by rw [parameters]; exact .nil)
  rintro ⟨_, _, _, shape⟩
  cases representation : rule.collectionRepresentation <;>
    simp [GrammarRule.bareParams, representation, parameters] at shape

/-- Atoms are elements of their sort. -/
theorem Atoms.elements {values : List Pattern} (atoms : Atoms language sort values) : Elements language sort values := by
  intro value member
  obtain ⟨label, rfl, atom⟩ := atoms value member
  exact ⟨fun _ _ => atom_hasType atom, rfl, rfl⟩

theorem SetCarrier.rule (setCarrier : SetCarrier language carrier sort) :
    CollectionCarrierRule language carrier .hashSet := by
  obtain ⟨name, shape⟩ := setCarrier.shape
  exact ⟨setCarrier.authored, name, .base sort, shape⟩

theorem elements_sorted (setCarrier : SetCarrier language carrier sort) {values : List Pattern}
    (elements : Elements language sort values) :
    SortedAt language (.collection .hashSet values none) carrier.category := by
  obtain ⟨name, shape⟩ := setCarrier.shape
  refine ⟨FreeTypeContext.empty, [], HasType.collectionConstructor (parameterName := name)
    (elementType := .base sort) setCarrier.authored ?_ ?_⟩
  · rw [GrammarRule.bareParams_of_bare _ setCarrier.bare, shape]
  · exact elementsHaveType_iff.mpr fun value member => (elements value member).1 _ _

theorem elements_object {values : List Pattern} (elements : Elements language sort values) :
    IsObject (.collection .hashSet values none) := by
  show isObjectPattern (.collection .hashSet values none) = true
  simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
  exact isObjectPatternList_iff.mpr fun value member => (elements value member).2.2

theorem elements_wellScoped : ∀ {values : List Pattern}, Elements language sort values →
    Pattern.isWellScopedListAt 0 values = true
  | [], _ => rfl
  | value :: _, elements => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true]
    exact ⟨(elements value (by simp)).2.1, elements_wellScoped fun other member => elements other (by simp [member])⟩

theorem elements_state {values : List Pattern} (elements : Elements language sort values) :
    IsState (.collection .hashSet values none) :=
  ⟨by simpa [Pattern.isWellScopedAt] using elements_wellScoped elements, elements_object elements⟩

theorem atoms_state {values : List Pattern} (atoms : Atoms language sort values) :
    IsState (.collection .hashSet values none) :=
  elements_state atoms.elements

/-- One law step between presentations of elements. -/
theorem elementStep {first second : List Pattern}
    (firstElements : Elements language sort first) (secondElements : Elements language sort second)
    (law : DerivedInstance language (.collection .hashSet first none) (.collection .hashSet second none)) :
    ObjectEquivalent relEnv language (.collection .hashSet first none) (.collection .hashSet second none) :=
  Relation.EqvGen.rel _ _
    ⟨elements_object firstElements, elements_object secondElements, .inContext .hole (Or.inr law)⟩

theorem perm_equivalent (setCarrier : SetCarrier language carrier sort) {first second : List Pattern}
    (elements : Elements language sort first) (perm : first.Perm second) :
    ObjectEquivalent relEnv language (.collection .hashSet first none) (.collection .hashSet second none) :=
  elementStep elements (elements.of_subset fun _ member => perm.symm.subset member)
    (.setPerm_of_sorted (elements_sorted setCarrier elements) perm)

/-- **A presentation of elements is equivalent to its arrangement**, sorted without repetition. -/
theorem toArranged (setCarrier : SetCarrier language carrier sort) :
    ∀ (fuel : ℕ) (values : List Pattern), values.length ≤ fuel → Elements language sort values →
      ObjectEquivalent relEnv language (.collection .hashSet values none)
        (.collection .hashSet (arrange .hashSet values) none)
  | fuel, values, short, elements => by
    by_cases distinct : values.Nodup
    · have arranged : (arrange .hashSet values).Perm values := by
        show (sortLex values).dedup.Perm values
        rw [List.Nodup.dedup ((sortLex_perm values).nodup_iff.mpr distinct)]
        exact sortLex_perm values
      exact perm_equivalent setCarrier elements arranged.symm
    · obtain ⟨duplicate, twice⟩ : ∃ duplicate, List.Sublist [duplicate, duplicate] values := by
        by_contra none
        exact distinct (List.nodup_iff_sublist.mpr fun value sub => none ⟨value, sub⟩)
      obtain ⟨others, perm⟩ := twice.exists_perm_append
      have inside : ∀ value ∈ duplicate :: duplicate :: others, value ∈ values :=
        fun value member => perm.symm.subset member
      have twiceElements : Elements language sort (duplicate :: duplicate :: others) := elements.of_subset inside
      have onceElements : Elements language sort (duplicate :: others) :=
        twiceElements.of_subset fun value member => by
          rcases List.mem_cons.mp member with rfl | rest
          · simp
          · simp [rest]
      have toTwice := perm_equivalent (relEnv := relEnv) setCarrier elements perm
      have toOnce : ObjectEquivalent relEnv language (.collection .hashSet (duplicate :: duplicate :: others) none)
          (.collection .hashSet (duplicate :: others) none) :=
        elementStep twiceElements onceElements (.setDedup_of_sorted (elements_sorted setCarrier twiceElements))
      cases fuel with
      | zero =>
        have : values.length = 0 := by omega
        exact absurd (List.length_eq_zero_iff.mp this ▸ List.nodup_nil) distinct
      | succ fuel =>
        have shorter : (duplicate :: others).length ≤ fuel := by
          have lengths := perm.length_eq
          simp only [List.length_append, List.length_cons, List.length_nil] at lengths
          simp only [List.length_cons]
          omega
        have rest := toArranged setCarrier fuel (duplicate :: others) shorter onceElements
        have same : arrange .hashSet (duplicate :: others) = arrange .hashSet values := by
          apply arrange_eq_of_presents
          intro value
          rw [perm.mem_iff]
          simp
        rw [same] at rest
        exact Relation.EqvGen.trans _ _ _ toTwice (Relation.EqvGen.trans _ _ _ toOnce rest)

/-- **Presentations of the same elements are equivalent.** -/
theorem presentations_equivalent (setCarrier : SetCarrier language carrier sort) {first second : List Pattern}
    (firstElements : Elements language sort first) (secondElements : Elements language sort second)
    (same : ∀ value, value ∈ first ↔ value ∈ second) :
    ObjectEquivalent relEnv language (.collection .hashSet first none) (.collection .hashSet second none) := by
  have toFirst := toArranged (relEnv := relEnv) setCarrier first.length first le_rfl firstElements
  have toSecond := toArranged (relEnv := relEnv) setCarrier second.length second le_rfl secondElements
  rw [arrange_eq_of_presents (kind := .hashSet) same] at toFirst
  exact Relation.EqvGen.trans _ _ _ toFirst (Relation.EqvGen.symm _ _ toSecond)

theorem sortBags_token (label : String) : BagForms.sortBags (token label) = token label := rfl

theorem sortBags_atoms {values : List Pattern} (atoms : Atoms language sort values) :
    values.map BagForms.sortBags = values := by
  conv_rhs => rw [← List.map_id values]
  exact List.map_congr_left fun value member => by
    obtain ⟨label, rfl, -⟩ := atoms value member
    rfl

theorem sortBags_set {values : List Pattern} (atoms : Atoms language sort values) :
    BagForms.sortBags (set values) = set (arrange .hashSet values) := by
  simp only [set, BagForms.sortBags, BagForms.sortBagsList_eq_map, sortBags_atoms atoms]

/-- **A presentation of atoms is equivalent to its canonical form.** -/
theorem equivalent_sortBags (setCarrier : SetCarrier language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) :
    ObjectEquivalent relEnv language (set values) (BagForms.sortBags (set values)) := by
  rw [sortBags_set atoms]
  exact toArranged setCarrier values.length values le_rfl atoms.elements

end Presentations

/-! ## The readings, characterized -/

section Characterized

open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem arrange_eq_of_presents)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (sortLex sortLex_perm)

variable {carrier : GrammarRule} {sort : String}

theorem token_injective : Function.Injective token := by
  intro first second same
  simpa [token] using same

theorem tokens_nodup {labels : List String} (distinct : labels.Nodup) : (labels.map token).Nodup :=
  distinct.map token_injective

/-- What remains of a presentation without repetition, once distinct values are taken. -/
theorem residual_mem {values residual taken : List Pattern}
    (counted : ∀ value, values.count value = residual.count value + taken.count value) (distinct : values.Nodup)
    (takenDistinct : taken.Nodup) (value : Pattern) : value ∈ residual ↔ value ∈ values ∧ value ∉ taken := by
  have equation := counted value
  have once := List.nodup_iff_count_le_one.mp distinct value
  have takenOnce := List.nodup_iff_count_le_one.mp takenDistinct value
  rw [← List.count_pos_iff, ← List.count_pos_iff, ← List.count_eq_zero]
  constructor
  · intro positive
    omega
  · rintro ⟨positive, zero⟩
    omega

theorem canonical_nodup {values : List Pattern} (atoms : Atoms language sort values)
    (canonical : BagForms.sortBags (set values) = set values) : values.Nodup := by
  rw [sortBags_set atoms] at canonical
  have same : arrange .hashSet values = values := by simpa [set] using canonical
  rw [← same]
  exact List.nodup_dedup _

theorem tokens_of_atoms {values : List Pattern} (atoms : Atoms language sort values) :
    ∀ value ∈ values, ∃ label, value = token label := fun value member => by
  obtain ⟨label, same, -⟩ := atoms value member
  exact ⟨label, same⟩

/-- Sets of tokens with the same members have one canonical form. -/
theorem sortBags_set_congr {first second : List Pattern} (firstTokens : ∀ value ∈ first, ∃ label, value = token label)
    (secondTokens : ∀ value ∈ second, ∃ label, value = token label) (same : ∀ value, value ∈ first ↔ value ∈ second) :
    BagForms.sortBags (set first) = BagForms.sortBags (set second) := by
  have fixed : ∀ list : List Pattern, (∀ value ∈ list, ∃ label, value = token label) →
      list.map BagForms.sortBags = list := fun list tokens => by
    conv_rhs => rw [← List.map_id list]
    exact List.map_congr_left fun value member => by
      obtain ⟨label, rfl⟩ := tokens value member
      rfl
  simp only [set, BagForms.sortBags, BagForms.sortBagsList_eq_map, fixed first firstTokens, fixed second secondTokens]
  congr 1
  exact arrange_eq_of_presents same

variable {relEnv : RelationEnv}

/-- **Consume, characterized**: from a canonical set of atoms, a step takes a rule's atoms from it and gives the
rule's atoms back. -/
theorem consume_step_iff (lang : GroundSetLanguage language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) (canonical : BagForms.sortBags (set values) = set values) {target : Pattern} :
    (consumeStructure relEnv language).step (set values) .any target ↔
      ∃ (index : ℕ) (rule : RewriteRule) (takes gives : List String) (rest : String),
        language.rewrites[index]? = some rule ∧ GroundSetRule rule takes gives rest ∧
        (∀ label ∈ takes, token label ∈ values) ∧
        target = BagForms.sortBags (set (gives.map token ++ values.filter (· ∉ takes.map token))) := by
  have distinct := canonical_nodup atoms canonical
  constructor
  · rintro ⟨-, -, witness, contractum, valid, -, reached⟩
    obtain ⟨index, rule, takes, gives, rest, residual, found, ground, counted, -, rfl⟩ :=
      ground_step lang.rules valid
    refine ⟨index, rule, takes, gives, rest, found, ground, fun label member => ?_, ?_⟩
    · have := counted (token label)
      have inTaken : 0 < (takes.map token).count (token label) :=
        List.count_pos_iff.mpr (List.mem_map_of_mem member)
      exact List.count_pos_iff.mp (by omega)
    · rw [← reached]
      apply sortBags_set_congr
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · have := (residual_mem counted distinct (tokens_nodup ground.distinct) value).mp remaining
          exact tokens_of_atoms atoms value this.1
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens_of_atoms atoms value (List.mem_filter.mp remaining).1
      · intro value
        simp only [List.mem_append, List.mem_filter, decide_eq_true_eq,
          residual_mem counted distinct (tokens_nodup ground.distinct) value]
  · rintro ⟨index, rule, takes, gives, rest, found, ground, present, rfl⟩
    obtain ⟨residual, counted, fired⟩ := ground_fires (relEnv := relEnv) found ground present
    refine ⟨atoms_state atoms, ?_, _, _, fired, rfl, ?_⟩
    · have givenAtoms : Atoms language sort (gives.map token ++ values.filter (· ∉ takes.map token)) := by
        refine Atoms.append (fun value member => ?_) (atoms.of_subset fun value member => (List.mem_filter.mp member).1)
        obtain ⟨label, inGives, rfl⟩ := List.mem_map.mp member
        exact ⟨label, rfl, lang.atomsOfSort rule (List.mem_of_getElem? found) takes gives rest ground label
          (List.mem_append_right _ inGives)⟩
      rw [sortBags_set givenAtoms]
      exact atoms_state (givenAtoms.of_subset fun value member => (arrange_mem value).mp member)
    · apply sortBags_set_congr
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens_of_atoms atoms value
            ((residual_mem counted distinct (tokens_nodup ground.distinct) value).mp remaining).1
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens_of_atoms atoms value (List.mem_filter.mp remaining).1
      · intro value
        simp only [List.mem_append, List.mem_filter, decide_eq_true_eq,
          residual_mem counted distinct (tokens_nodup ground.distinct) value]

theorem count_flatMap_replicate_eq (copies : ℕ) (value : Pattern) : ∀ list : List Pattern,
    (list.flatMap (List.replicate copies)).count value = copies * list.count value
  | [] => by simp
  | head :: tail => by
    rw [List.flatMap_cons, List.count_append, List.count_replicate, count_flatMap_replicate_eq copies value tail,
      List.count_cons]
    split <;> simp [Nat.mul_add, Nat.add_comm]

theorem saturate_tokens {values : List Pattern} (tokens : ∀ value ∈ values, ∃ label, value = token label)
    (copies : ℕ) : saturate copies (set values) = set (values.flatMap (List.replicate copies)) := by
  have fixed : saturateList copies values = values := by
    rw [saturateList_eq_map]
    conv_rhs => rw [← List.map_id values]
    exact List.map_congr_left fun value member => by
      obtain ⟨label, rfl⟩ := tokens value member
      rfl
  simp [set, saturate, fixed]

/-- What remains of a presentation that writes each member `copies` times, once distinct values are taken. -/
theorem keep_residual_mem {values residual taken : List Pattern} {copies : ℕ}
    (counted : ∀ value, (values.flatMap (List.replicate copies)).count value = residual.count value + taken.count value)
    (distinct : values.Nodup) (takenDistinct : taken.Nodup) (positive : 0 < copies)
    (enough : ∀ value ∈ taken, 2 ≤ copies) (value : Pattern) : value ∈ residual ↔ value ∈ values := by
  have equation := counted value
  rw [count_flatMap_replicate_eq, distinct.count] at equation
  rw [takenDistinct.count] at equation
  rw [← List.count_pos_iff]
  by_cases inValues : value ∈ values
  · by_cases inTaken : value ∈ taken
    · have := enough value inTaken
      simp only [inValues, inTaken, if_true, Nat.mul_one] at equation
      simp only [inValues, iff_true]
      omega
    · simp only [inValues, inTaken, if_true, if_false, Nat.mul_one] at equation
      simp only [inValues, iff_true]
      omega
  · simp only [inValues, if_false, Nat.mul_zero] at equation
    simp only [inValues, iff_false]
    omega

theorem width_takes {language : LanguageDef} {rule : RewriteRule} {takes gives : List String} {rest : String}
    (member : rule ∈ language.rewrites) (ground : GroundSetRule rule takes gives rest) :
    takes.length ≤ setWidth language := by
  have := width_le member
  rw [ground.left] at this
  simp only [setPatternWidth, if_true, List.length_map] at this
  omega

/-- **Keep, characterized**: from a canonical set of atoms, a step finds a rule's atoms in it and adds the rule's
atoms. -/
theorem keep_step_iff (lang : GroundSetLanguage language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) (canonical : BagForms.sortBags (set values) = set values) {target : Pattern} :
    (keepStructure relEnv language).step (set values) .any target ↔
      ∃ (index : ℕ) (rule : RewriteRule) (takes gives : List String) (rest : String),
        language.rewrites[index]? = some rule ∧ GroundSetRule rule takes gives rest ∧
        (∀ label ∈ takes, token label ∈ values) ∧ target = BagForms.sortBags (set (gives.map token ++ values)) := by
  have distinct := canonical_nodup atoms canonical
  have tokens := tokens_of_atoms atoms
  have presented := saturate_tokens tokens (setWidth language + 1)
  constructor
  · rintro ⟨-, -, witness, contractum, valid, -, reached⟩
    rw [presented] at valid
    obtain ⟨index, rule, takes, gives, rest, residual, found, ground, counted, -, rfl⟩ :=
      ground_step lang.rules valid
    have enough : ∀ value ∈ takes.map token, 2 ≤ setWidth language + 1 := by
      intro value member
      have := width_takes (List.mem_of_getElem? found) ground
      have : 0 < takes.length := List.length_pos_of_mem (List.mem_map.mp member).choose_spec.1
      omega
    have residualMem := keep_residual_mem counted distinct (tokens_nodup ground.distinct) (Nat.succ_pos _) enough
    refine ⟨index, rule, takes, gives, rest, found, ground, fun label member => ?_, ?_⟩
    · have := counted (token label)
      rw [count_flatMap_replicate_eq] at this
      have inTaken : 0 < (takes.map token).count (token label) :=
        List.count_pos_iff.mpr (List.mem_map_of_mem member)
      apply List.count_pos_iff.mp
      by_contra none
      simp only [Nat.not_lt, Nat.le_zero] at none
      rw [none, Nat.mul_zero] at this
      omega
    · rw [← reached]
      apply sortBags_set_congr
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens value ((residualMem value).mp remaining)
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens value remaining
      · intro value
        simp only [List.mem_append, residualMem value]
  · rintro ⟨index, rule, takes, gives, rest, found, ground, present, rfl⟩
    have presentSaturated : ∀ label ∈ takes, token label ∈ values.flatMap (List.replicate (setWidth language + 1)) :=
      fun label member => List.mem_flatMap.mpr ⟨token label, present label member, by simp⟩
    obtain ⟨residual, counted, fired⟩ := ground_fires (relEnv := relEnv) found ground presentSaturated
    have enough : ∀ value ∈ takes.map token, 2 ≤ setWidth language + 1 := by
      intro value member
      have := width_takes (List.mem_of_getElem? found) ground
      have : 0 < takes.length := List.length_pos_of_mem (List.mem_map.mp member).choose_spec.1
      omega
    have residualMem := keep_residual_mem counted distinct (tokens_nodup ground.distinct) (Nat.succ_pos _) enough
    have givenAtoms : Atoms language sort (gives.map token ++ values) := by
      refine Atoms.append (fun value member => ?_) atoms
      obtain ⟨label, inGives, rfl⟩ := List.mem_map.mp member
      exact ⟨label, rfl, lang.atomsOfSort rule (List.mem_of_getElem? found) takes gives rest ground label
        (List.mem_append_right _ inGives)⟩
    refine ⟨atoms_state atoms, ?_, _, _, by rw [presented]; exact fired, rfl, ?_⟩
    · rw [sortBags_set givenAtoms]
      exact atoms_state (givenAtoms.of_subset fun value member => (arrange_mem value).mp member)
    · apply sortBags_set_congr
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens value ((residualMem value).mp remaining)
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨label, -, rfl⟩ := List.mem_map.mp given
          exact ⟨label, rfl⟩
        · exact tokens value remaining
      · intro value
        simp only [List.mem_append, residualMem value]

theorem sortBags_same (lang : GroundSetLanguage language carrier sort) {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language first second) :
    BagForms.sortBags first = BagForms.sortBags second := by
  rw [BagForms.sortBags_eq_canon]
  exact BagForms.canon_eq_of_equivalent lang.noEquations lang.noAlgebra equivalent

theorem sortBags_eq_token {pattern : Pattern} {label : String} (same : BagForms.sortBags pattern = token label) :
    pattern = token label := by
  cases pattern with
  | apply other arguments =>
    simp only [BagForms.sortBags, token, Pattern.apply.injEq, BagForms.sortBagsList_eq_map, List.map_eq_nil_iff] at same
    rw [same.1, same.2]
    rfl
  | bvar _ => simp [BagForms.sortBags, token] at same
  | fvar _ => simp [BagForms.sortBags, token] at same
  | lambda _ _ => simp [BagForms.sortBags, token] at same
  | multiLambda _ _ _ => simp [BagForms.sortBags, token] at same
  | subst _ _ => simp [BagForms.sortBags, token] at same
  | collection _ _ _ => simp [BagForms.sortBags, token] at same

/-- A term whose canonical form is a set of tokens presents those tokens. -/
theorem presentation_of_canonical {redex : Pattern} {values : List Pattern}
    (tokens : ∀ value ∈ values, ∃ label, value = token label) (same : BagForms.sortBags redex = set values) :
    ∃ presented, redex = set presented ∧ (∀ value ∈ presented, ∃ label, value = token label) ∧
      ∀ value, value ∈ presented ↔ value ∈ values := by
  cases redex with
  | collection kind elements rest =>
    simp only [BagForms.sortBags, set, Pattern.collection.injEq, BagForms.sortBagsList_eq_map] at same
    obtain ⟨rfl, arranged, rfl⟩ := same
    have elementTokens : ∀ value ∈ elements, ∃ label, value = token label := fun value member => by
      have inValues : BagForms.sortBags value ∈ values := by
        rw [← arranged, arrange_mem]
        exact List.mem_map_of_mem member
      obtain ⟨label, isToken⟩ := tokens _ inValues
      exact ⟨label, sortBags_eq_token isToken⟩
    have fixed : elements.map BagForms.sortBags = elements := by
      conv_rhs => rw [← List.map_id elements]
      exact List.map_congr_left fun value member => by
        obtain ⟨label, rfl⟩ := elementTokens value member
        rfl
    refine ⟨elements, rfl, elementTokens, fun value => ?_⟩
    rw [← arranged, arrange_mem, fixed]
  | bvar _ => simp [BagForms.sortBags, set] at same
  | fvar _ => simp [BagForms.sortBags, set] at same
  | apply _ _ => simp [BagForms.sortBags, set] at same
  | lambda _ _ => simp [BagForms.sortBags, set] at same
  | multiLambda _ _ _ => simp [BagForms.sortBags, set] at same
  | subst _ _ => simp [BagForms.sortBags, set] at same

/-- What remains of any presentation once distinct atoms are taken: a taken atom stays when the presentation wrote
it twice. -/
theorem either_residual_mem {presented residual : List Pattern} {takes : List String}
    (counted : ∀ value, presented.count value = residual.count value + (takes.map token).count value)
    (distinct : takes.Nodup) (value : Pattern) :
    value ∈ residual ↔ value ∈ presented ∧
      (value ∉ takes.map token ∨ value ∈ (takes.filter fun label => 2 ≤ presented.count (token label)).map token) := by
  have equation := counted value
  rw [(tokens_nodup distinct).count] at equation
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  by_cases inTaken : value ∈ takes.map token
  · obtain ⟨label, member, rfl⟩ := List.mem_map.mp inTaken
    simp only [inTaken, if_true] at equation
    have keptIff : token label ∈ (takes.filter fun other => 2 ≤ presented.count (token other)).map token ↔
        2 ≤ presented.count (token label) := by
      rw [List.mem_map]
      constructor
      · rintro ⟨other, otherMember, same⟩
        rw [token_injective same] at otherMember
        simpa using (List.mem_filter.mp otherMember).2
      · intro twice
        exact ⟨label, List.mem_filter.mpr ⟨member, by simpa using twice⟩, rfl⟩
    rw [keptIff]
    constructor
    · intro positive
      exact ⟨by omega, Or.inr (by omega)⟩
    · rintro ⟨-, notTaken | twice⟩
      · exact absurd inTaken notTaken
      · omega
  · simp only [inTaken, if_false, Nat.add_zero] at equation
    simp only [inTaken, not_false_eq_true, true_or, and_true]
    omega

/-- **Either, characterized, one way**: a step of the language's semantics from a canonical set of atoms takes a
rule's atoms from some presentation of it, keeps those the presentation wrote twice, and gives the rule's atoms. -/
theorem either_step_of (lang : GroundSetLanguage language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) (canonical : BagForms.sortBags (set values) = set values) {label : StepLabel}
    {target : Pattern} (step : (referenceStructure relEnv language).step (set values) label target) :
    ∃ (index : ℕ) (rule : RewriteRule) (takes gives kept : List String) (rest : String),
      language.rewrites[index]? = some rule ∧ GroundSetRule rule takes gives rest ∧
      (∀ name ∈ takes, token name ∈ values) ∧ (∀ name ∈ kept, name ∈ takes) ∧
      BagForms.sortBags target = BagForms.sortBags (set (gives.map token ++
        values.filter fun value => value ∉ takes.map token ∨ value ∈ kept.map token)) := by
  have tokens := tokens_of_atoms atoms
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := step
  have redexCanonical : BagForms.sortBags redex = set values := (sortBags_same lang before).symm.trans canonical
  obtain ⟨presented, rfl, presentedTokens, sameMembers⟩ := presentation_of_canonical tokens redexCanonical
  obtain ⟨index, rule, takes, gives, rest, residual, found, ground, counted, -, rfl⟩ := ground_step lang.rules valid
  have residualMem := either_residual_mem counted ground.distinct
  refine ⟨index, rule, takes, gives, takes.filter (fun name => 2 ≤ presented.count (token name)), rest, found, ground,
    fun name member => ?_, fun name member => (List.mem_filter.mp member).1, ?_⟩
  · have := counted (token name)
    have taken : 0 < (takes.map token).count (token name) := List.count_pos_iff.mpr (List.mem_map_of_mem member)
    exact (sameMembers _).mp (List.count_pos_iff.mp (by omega))
  · rw [← sortBags_same lang after]
    apply sortBags_set_congr
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact presentedTokens value ((residualMem value).mp remaining).1
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value (List.mem_filter.mp remaining).1
    · intro value
      simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, residualMem value, sameMembers value]

/-- **A ground set rule fires at a canonical set with some members copied**: it takes one copy of each of its
atoms, so a taken atom stays exactly when it was copied. -/
theorem fires_at_copies {values : List Pattern} (atoms : Atoms language sort values)
    (canonical : BagForms.sortBags (set values) = set values) {index : ℕ} {rule : RewriteRule}
    {takes gives : List String} {rest : String} (found : language.rewrites[index]? = some rule)
    (ground : GroundSetRule rule takes gives rest) (present : ∀ name ∈ takes, token name ∈ values)
    {copies : List Pattern} (copiesDistinct : copies.Nodup) (copiesInValues : ∀ value ∈ copies, value ∈ values) :
    ∃ residual, StepValid relEnv language (set (values ++ copies)) (.rule index [(rest, set residual)] [])
        (set (gives.map token ++ residual)) ∧
      ∀ value, value ∈ residual ↔ value ∈ values ∧ (value ∉ takes.map token ∨ value ∈ copies) := by
  have distinct := canonical_nodup atoms canonical
  obtain ⟨residual, counted, fired⟩ := ground_fires (relEnv := relEnv) found ground
    (values := values ++ copies) fun name member => List.mem_append_left _ (present name member)
  refine ⟨residual, fired, fun value => ?_⟩
  have equation := counted value
  simp only [List.count_append, distinct.count, copiesDistinct.count, (tokens_nodup ground.distinct).count]
    at equation
  rw [← List.count_pos_iff]
  by_cases inValues : value ∈ values
  · by_cases inTaken : value ∈ takes.map token
    · by_cases inCopies : value ∈ copies
      · simp only [inValues, inCopies, inTaken, if_true] at equation
        simp only [inValues, inCopies, true_and, or_true, iff_true]
        omega
      · simp only [inValues, inCopies, inTaken, if_true, if_false] at equation
        simp only [inValues, inTaken, inCopies, true_and, not_true_eq_false, or_self, iff_false]
        omega
    · by_cases inCopies : value ∈ copies
      · simp only [inValues, inCopies, inTaken, if_true, if_false] at equation
        simp only [inValues, inTaken, not_false_eq_true, true_or, and_self, iff_true]
        omega
      · simp only [inValues, inCopies, inTaken, if_true, if_false] at equation
        simp only [inValues, inTaken, not_false_eq_true, true_or, and_self, iff_true]
        omega
  · have notCopied : value ∉ copies := fun member => inValues (copiesInValues value member)
    simp only [inValues, notCopied, if_false] at equation
    simp only [inValues, false_and, iff_false]
    omega

/-- **Either, characterized, the other way**: for any part of a rule's atoms to keep, the language's semantics steps
from a canonical set of atoms holding them to the set that gives the rule's atoms and keeps that part. -/
theorem either_step_to (lang : GroundSetLanguage language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) (canonical : BagForms.sortBags (set values) = set values) {index : ℕ}
    {rule : RewriteRule} {takes gives : List String} {rest : String} (found : language.rewrites[index]? = some rule)
    (ground : GroundSetRule rule takes gives rest) (present : ∀ name ∈ takes, token name ∈ values)
    (kept : List String) :
    (referenceStructure relEnv language).step (set values) .any (BagForms.sortBags (set (gives.map token ++
      values.filter fun value => value ∉ takes.map token ∨ value ∈ kept.map token))) := by
  have tokens := tokens_of_atoms atoms
  let doubled := (takes.filter (· ∈ kept)).map token
  have doubledInValues : ∀ value ∈ doubled, value ∈ values := fun value member => by
    obtain ⟨name, nameMember, rfl⟩ := List.mem_map.mp member
    exact present name (List.mem_filter.mp nameMember).1
  have presentedAtoms : Atoms language sort (values ++ doubled) := atoms.append (atoms.of_subset doubledInValues)
  obtain ⟨residual, fired, copied⟩ := fires_at_copies (relEnv := relEnv) atoms canonical found ground present
    (tokens_nodup (ground.distinct.filter _)) doubledInValues
  have doubledIff : ∀ value, value ∈ doubled ↔ value ∈ takes.map token ∧ value ∈ kept.map token := by
    intro value
    simp only [doubled, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨name, ⟨member, keptMember⟩, rfl⟩
      exact ⟨⟨name, member, rfl⟩, ⟨name, keptMember, rfl⟩⟩
    · rintro ⟨⟨name, member, rfl⟩, ⟨other, keptMember, same⟩⟩
      rw [token_injective same] at keptMember
      exact ⟨name, ⟨member, keptMember⟩, rfl⟩
  have residualMem : ∀ value, value ∈ residual ↔
      value ∈ values ∧ (value ∉ takes.map token ∨ value ∈ kept.map token) := by
    intro value
    rw [copied value, doubledIff value]
    tauto
  have givenAtoms : Atoms language sort (gives.map token ++ residual) := by
    refine Atoms.append (fun value member => ?_) (atoms.of_subset fun value member => ((residualMem value).mp member).1)
    obtain ⟨name, inGives, rfl⟩ := List.mem_map.mp member
    exact ⟨name, rfl, lang.atomsOfSort rule (List.mem_of_getElem? found) takes gives rest ground name
      (List.mem_append_right _ inGives)⟩
  have sameTarget : BagForms.sortBags (set (gives.map token ++ residual)) = BagForms.sortBags (set (gives.map token ++
      values.filter fun value => value ∉ takes.map token ∨ value ∈ kept.map token)) := by
    apply sortBags_set_congr (tokens_of_atoms givenAtoms)
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value (List.mem_filter.mp remaining).1
    · intro value
      simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, residualMem value]
  refine ⟨atoms_state atoms, ?_, set (values ++ doubled), set (gives.map token ++ residual), _,
    presentations_equivalent lang.setCarrier atoms.elements presentedAtoms.elements fun value => ?_, atoms_state presentedAtoms, fired,
    atoms_state givenAtoms, ?_, rfl⟩
  · rw [← sameTarget, sortBags_set givenAtoms]
    exact atoms_state (givenAtoms.of_subset fun value member => (arrange_mem value).mp member)
  · simp only [List.mem_append]
    exact ⟨Or.inl, fun member => member.elim id (doubledInValues value)⟩
  · rw [← sameTarget]
    exact equivalent_sortBags lang.setCarrier givenAtoms

end Characterized

/-! ## Consequences -/

section Consequences

variable {carrier : GrammarRule} {sort : String} {relEnv : RelationEnv}

theorem GroundSetRule.unique {rule : RewriteRule} {takes gives takes' gives' : List String} {rest rest' : String}
    (first : GroundSetRule rule takes gives rest) (second : GroundSetRule rule takes' gives' rest') :
    takes = takes' ∧ gives = gives' ∧ rest = rest' := by
  have left := first.left.symm.trans second.left
  have right := first.right.symm.trans second.right
  simp only [Pattern.collection.injEq, Option.some.injEq, true_and] at left right
  exact ⟨List.map_injective_iff.mpr token_injective left.1, List.map_injective_iff.mpr token_injective right.1, left.2⟩

/-- **For rules that take one atom, either is consume together with keep**, on canonical targets. -/
theorem either_one_iff (lang : GroundSetLanguage language carrier sort)
    (single : ∀ rule ∈ language.rewrites, ∀ takes gives rest, GroundSetRule rule takes gives rest → takes.length = 1)
    {values : List Pattern} (atoms : Atoms language sort values)
    (canonical : BagForms.sortBags (set values) = set values)
    {target : Pattern} (targetCanonical : BagForms.sortBags target = target) :
    (referenceStructure relEnv language).step (set values) .any target ↔
      (consumeStructure relEnv language).step (set values) .any target ∨
        (keepStructure relEnv language).step (set values) .any target := by
  constructor
  · intro step
    obtain ⟨index, rule, takes, gives, kept, rest, found, ground, present, inside, reached⟩ :=
      either_step_of lang atoms canonical step
    rw [targetCanonical] at reached
    obtain ⟨atom, rfl⟩ := List.length_eq_one_iff.mp (single rule (List.mem_of_getElem? found) takes gives rest ground)
    by_cases keptAtom : atom ∈ kept
    · right
      refine (keep_step_iff lang atoms canonical).mpr ⟨index, rule, [atom], gives, rest, found, ground, present, ?_⟩
      have everything : (values.filter fun value => value ∉ [atom].map token ∨ value ∈ kept.map token) = values := by
        apply List.filter_eq_self.mpr
        intro value _
        by_cases same : value = token atom
        · subst same
          simp [List.mem_map_of_mem keptAtom]
        · simp [same]
      rw [reached, everything]
    · left
      refine (consume_step_iff lang atoms canonical).mpr ⟨index, rule, [atom], gives, rest, found, ground, present, ?_⟩
      have noneKept : ∀ value, value ∉ kept.map token := by
        intro value member
        obtain ⟨name, nameMember, rfl⟩ := List.mem_map.mp member
        have := inside name nameMember
        rw [List.mem_singleton] at this
        exact keptAtom (this ▸ nameMember)
      have sameFilter : (values.filter fun value => value ∉ [atom].map token ∨ value ∈ kept.map token) =
          values.filter (· ∉ [atom].map token) := by
        apply List.filter_congr
        intro value _
        simp [noneKept value]
      rw [reached, sameFilter]
  · rintro (consume | keep)
    · obtain ⟨index, rule, takes, gives, rest, found, ground, present, rfl⟩ :=
        (consume_step_iff lang atoms canonical).mp consume
      simpa using either_step_to (relEnv := relEnv) lang atoms canonical found ground present []
    · obtain ⟨index, rule, takes, gives, rest, found, ground, present, rfl⟩ :=
        (keep_step_iff lang atoms canonical).mp keep
      have everything : (values.filter fun value => value ∉ takes.map token ∨ value ∈ takes.map token) = values :=
        List.filter_eq_self.mpr fun _ _ => decide_eq_true (Classical.em _).symm
      have step := either_step_to (relEnv := relEnv) lang atoms canonical found ground present takes
      rwa [everything] at step

/-! ### Encodings in consume -/

/-- Give back what a rule takes. -/
def giveBack (rule : RewriteRule) : RewriteRule :=
  match rule.left, rule.right with
  | .collection .hashSet taken (some _), .collection .hashSet given (some rest) =>
      { rule with right := .collection .hashSet (given ++ taken) (some rest) }
  | _, _ => rule

/-- One rule for each part of what a rule takes that it gives back. -/
def keepParts (rule : RewriteRule) : List RewriteRule :=
  match rule.left, rule.right with
  | .collection .hashSet taken (some _), .collection .hashSet given (some rest) =>
      taken.sublists.map fun part => { rule with right := .collection .hashSet (given ++ part) (some rest) }
  | _, _ => [rule]

def giveBackLanguage (language : LanguageDef) : LanguageDef :=
  { language with rewrites := language.rewrites.map giveBack }

def keepPartsLanguage (language : LanguageDef) : LanguageDef :=
  { language with rewrites := language.rewrites.flatMap keepParts }

theorem giveBack_eq {rule : RewriteRule} {takes gives : List String} {rest : String}
    (ground : GroundSetRule rule takes gives rest) :
    giveBack rule = { rule with right := .collection .hashSet ((gives ++ takes).map token) (some rest) } := by
  simp only [giveBack, ground.left, ground.right, List.map_append]

theorem giveBack_ground {rule : RewriteRule} {takes gives : List String} {rest : String}
    (ground : GroundSetRule rule takes gives rest) : GroundSetRule (giveBack rule) takes (gives ++ takes) rest := by
  rw [giveBack_eq ground]
  exact ⟨ground.left, rfl, ground.noPremises, ground.distinct⟩

theorem keepParts_ground {rule : RewriteRule} {takes gives : List String} {rest : String}
    (ground : GroundSetRule rule takes gives rest) :
    keepParts rule = takes.sublists.map fun part =>
      { rule with right := .collection .hashSet ((gives ++ part).map token) (some rest) } := by
  unfold keepParts
  rw [ground.left, ground.right]
  simp [List.sublists_map]

theorem keepPart_ground {rule : RewriteRule} {takes gives part : List String} {rest : String}
    (ground : GroundSetRule rule takes gives rest) :
    GroundSetRule { rule with right := .collection .hashSet ((gives ++ part).map token) (some rest) } takes
      (gives ++ part)
      rest :=
  ⟨ground.left, rfl, ground.noPremises, ground.distinct⟩

theorem giveBack_language (lang : GroundSetLanguage language carrier sort) :
    GroundSetLanguage (giveBackLanguage language) carrier sort where
  noEquations := lang.noEquations
  noAlgebra := lang.noAlgebra
  setCarrier := ⟨lang.setCarrier.authored, lang.setCarrier.shape, lang.setCarrier.bare⟩
  rules := by
    intro rule member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨takes, gives, rest, ground⟩ := lang.rules original originalMember
    exact ⟨takes, gives ++ takes, rest, giveBack_ground ground⟩
  atomsOfSort := by
    intro rule member takes gives rest ground name nameMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨takes', gives', rest', original'⟩ := lang.rules original originalMember
    obtain ⟨rfl, rfl, rfl⟩ := (giveBack_ground original').unique ground
    have := lang.atomsOfSort original originalMember takes' gives' rest' original'
    simp only [List.mem_append] at nameMember
    exact this name (by simp only [List.mem_append]; tauto)

theorem keepParts_language (lang : GroundSetLanguage language carrier sort) :
    GroundSetLanguage (keepPartsLanguage language) carrier sort where
  noEquations := lang.noEquations
  noAlgebra := lang.noAlgebra
  setCarrier := ⟨lang.setCarrier.authored, lang.setCarrier.shape, lang.setCarrier.bare⟩
  rules := by
    intro rule member
    obtain ⟨original, originalMember, inParts⟩ := List.mem_flatMap.mp member
    obtain ⟨takes, gives, rest, ground⟩ := lang.rules original originalMember
    rw [keepParts_ground ground] at inParts
    obtain ⟨part, -, rfl⟩ := List.mem_map.mp inParts
    exact ⟨takes, gives ++ part, rest, keepPart_ground ground⟩
  atomsOfSort := by
    intro rule member takes gives rest ground name nameMember
    obtain ⟨original, originalMember, inParts⟩ := List.mem_flatMap.mp member
    obtain ⟨takes', gives', rest', original'⟩ := lang.rules original originalMember
    rw [keepParts_ground original'] at inParts
    obtain ⟨part, partMember, rfl⟩ := List.mem_map.mp inParts
    obtain ⟨rfl, rfl, rfl⟩ := (keepPart_ground original').unique ground
    have atoms := lang.atomsOfSort original originalMember takes' gives' rest' original'
    have sub : part.Sublist takes' := List.mem_sublists.mp partMember
    simp only [List.mem_append] at nameMember
    rcases nameMember with taken | given | kept
    · exact atoms name (List.mem_append_left _ taken)
    · exact atoms name (List.mem_append_right _ given)
    · exact atoms name (List.mem_append_left _ (sub.subset kept))

/-- **Keep is consume with every rule giving back what it takes.** -/
theorem keep_is_consume_giving_back (lang : GroundSetLanguage language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) (canonical : BagForms.sortBags (set values) = set values) {target : Pattern} :
    (keepStructure relEnv language).step (set values) .any target ↔
      (consumeStructure relEnv (giveBackLanguage language)).step (set values) .any target := by
  have tokens := tokens_of_atoms atoms
  rw [keep_step_iff lang atoms canonical, consume_step_iff (giveBack_language lang) atoms canonical]
  constructor
  · rintro ⟨index, rule, takes, gives, rest, found, ground, present, rfl⟩
    refine ⟨index, giveBack rule, takes, gives ++ takes, rest, by simp [giveBackLanguage, found],
      giveBack_ground ground,
      present, ?_⟩
    apply sortBags_set_congr
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value remaining
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value (List.mem_filter.mp remaining).1
    · intro value
      simp only [List.mem_append, List.map_append, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro (given | inValues)
        · exact Or.inl (Or.inl given)
        · by_cases taken : value ∈ takes.map token
          · exact Or.inl (Or.inr taken)
          · exact Or.inr ⟨inValues, taken⟩
      · rintro ((given | taken) | ⟨inValues, -⟩)
        · exact Or.inl given
        · obtain ⟨name, member, rfl⟩ := List.mem_map.mp taken
          exact Or.inr (present name member)
        · exact Or.inr inValues
  · rintro ⟨index, rule', takes, gives', rest, found', ground', present, rfl⟩
    simp only [giveBackLanguage, List.getElem?_map, Option.map_eq_some_iff] at found'
    obtain ⟨rule, found, rfl⟩ := found'
    obtain ⟨takes₀, gives, rest₀, ground⟩ := lang.rules rule (List.mem_of_getElem? found)
    obtain ⟨rfl, rfl, rfl⟩ := (giveBack_ground ground).unique ground'
    refine ⟨index, rule, takes₀, gives, rest₀, found, ground, present, ?_⟩
    apply sortBags_set_congr
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value (List.mem_filter.mp remaining).1
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value remaining
    · intro value
      simp only [List.mem_append, List.map_append, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ((given | taken) | ⟨inValues, -⟩)
        · exact Or.inl given
        · obtain ⟨name, member, rfl⟩ := List.mem_map.mp taken
          exact Or.inr (present name member)
        · exact Or.inr inValues
      · rintro (given | inValues)
        · exact Or.inl (Or.inl given)
        · by_cases taken : value ∈ takes₀.map token
          · exact Or.inl (Or.inr taken)
          · exact Or.inr ⟨inValues, taken⟩

/-- **Either is consume with one rule for each part of what a rule takes that it gives back**, on canonical
targets. -/
theorem either_is_consume_keeping_parts (lang : GroundSetLanguage language carrier sort) {values : List Pattern}
    (atoms : Atoms language sort values) (canonical : BagForms.sortBags (set values) = set values) {target : Pattern}
    (targetCanonical : BagForms.sortBags target = target) :
    (referenceStructure relEnv language).step (set values) .any target ↔
      (consumeStructure relEnv (keepPartsLanguage language)).step (set values) .any target := by
  have tokens := tokens_of_atoms atoms
  rw [consume_step_iff (keepParts_language lang) atoms canonical]
  constructor
  · intro step
    obtain ⟨index, rule, takes, gives, kept, rest, found, ground, present, inside, reached⟩ :=
      either_step_of lang atoms canonical step
    rw [targetCanonical] at reached
    let part := takes.filter (· ∈ kept)
    have partMember : part ∈ takes.sublists := List.mem_sublists.mpr List.filter_sublist
    have inEncoded : { rule with right := .collection .hashSet ((gives ++ part).map token) (some rest) } ∈
        (keepPartsLanguage language).rewrites := by
      apply List.mem_flatMap.mpr
      refine ⟨rule, List.mem_of_getElem? found, ?_⟩
      rw [keepParts_ground ground]
      exact List.mem_map_of_mem partMember
    obtain ⟨encodedIndex, encodedFound⟩ := List.mem_iff_getElem?.mp inEncoded
    refine ⟨encodedIndex, _, takes, gives ++ part, rest, encodedFound, keepPart_ground ground, present, ?_⟩
    rw [reached]
    apply sortBags_set_congr
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value (List.mem_filter.mp remaining).1
    · intro value member
      rcases List.mem_append.mp member with given | remaining
      · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
        exact ⟨name, rfl⟩
      · exact tokens value (List.mem_filter.mp remaining).1
    · intro value
      simp only [List.mem_append, List.map_append, List.mem_filter, decide_eq_true_eq, part, List.mem_map]
      constructor
      · rintro (given | ⟨inValues, notTaken | ⟨name, nameKept, rfl⟩⟩)
        · exact Or.inl (Or.inl given)
        · exact Or.inr ⟨inValues, fun ⟨name, member, same⟩ => notTaken ⟨name, member, same⟩⟩
        · exact Or.inl (Or.inr ⟨name, ⟨inside name nameKept, nameKept⟩, rfl⟩)
      · rintro ((given | ⟨name, ⟨member, nameKept⟩, rfl⟩) | ⟨inValues, notTaken⟩)
        · exact Or.inl given
        · exact Or.inr ⟨present name member, Or.inr ⟨name, nameKept, rfl⟩⟩
        · exact Or.inr ⟨inValues, Or.inl notTaken⟩
  · rintro ⟨index, rule', takes, gives', rest, found', ground', present, rfl⟩
    obtain ⟨rule, ruleMember, inParts⟩ := List.mem_flatMap.mp (List.mem_of_getElem? found')
    obtain ⟨takes₀, gives, rest₀, ground⟩ := lang.rules rule ruleMember
    rw [keepParts_ground ground] at inParts
    obtain ⟨part, partMember, rfl⟩ := List.mem_map.mp inParts
    obtain ⟨rfl, rfl, rfl⟩ := (keepPart_ground ground).unique ground'
    obtain ⟨ruleIndex, found⟩ := List.mem_iff_getElem?.mp ruleMember
    have step := either_step_to (relEnv := relEnv) lang atoms canonical found ground present part
    have sub : part.Sublist takes₀ := List.mem_sublists.mp partMember
    have same : BagForms.sortBags (set (gives.map token ++
        values.filter fun value => value ∉ takes₀.map token ∨ value ∈ part.map token)) =
        BagForms.sortBags (set ((gives ++ part).map token ++ values.filter (· ∉ takes₀.map token))) := by
      apply sortBags_set_congr
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
          exact ⟨name, rfl⟩
        · exact tokens value (List.mem_filter.mp remaining).1
      · intro value member
        rcases List.mem_append.mp member with given | remaining
        · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
          exact ⟨name, rfl⟩
        · exact tokens value (List.mem_filter.mp remaining).1
      · intro value
        simp only [List.mem_append, List.map_append, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (given | ⟨inValues, notTaken | kept⟩)
          · exact Or.inl (Or.inl given)
          · exact Or.inr ⟨inValues, notTaken⟩
          · exact Or.inl (Or.inr kept)
        · rintro ((given | kept) | ⟨inValues, notTaken⟩)
          · exact Or.inl given
          · obtain ⟨name, member, rfl⟩ := List.mem_map.mp kept
            exact Or.inr ⟨present name (sub.subset member), Or.inr (List.mem_map_of_mem member)⟩
          · exact Or.inr ⟨inValues, Or.inl notTaken⟩
    rwa [same] at step

/-! ### Keep cannot encode consume -/

theorem keepsRest_of_ground {rule : RewriteRule} {takes gives : List String} {rest : String}
    (ground : GroundSetRule rule takes gives rest) : keepsRest rule = true := by
  simp [keepsRest, ground.left, ground.right, ground.noPremises]

theorem groundRules_keepsRest (rules : GroundRules language) : language.rewrites.all keepsRest = true :=
  List.all_eq_true.mpr fun rule member => by
    obtain ⟨takes, gives, rest, ground⟩ := rules rule member
    exact keepsRest_of_ground ground

theorem useA_ground : GroundSetRule useA ["A"] ["B"] "rest" := ⟨rfl, rfl, rfl, List.nodup_singleton _⟩

/-- **The pool is a ground set language.** -/
theorem pool_ground : GroundSetLanguage pool poolRule "Atom" where
  noEquations := pool_no_equations
  noAlgebra := pool_no_algebra
  setCarrier := ⟨by simp [pool], ⟨"members", rfl⟩, rfl⟩
  rules := by
    intro rule member
    rw [show pool.rewrites = [useA] from rfl, List.mem_singleton] at member
    subst member
    exact ⟨_, _, _, useA_ground⟩
  atomsOfSort := by
    intro rule member takes gives rest ground label labelMember
    rw [show pool.rewrites = [useA] from rfl, List.mem_singleton] at member
    subst member
    obtain ⟨rfl, rfl, rfl⟩ := ground.unique useA_ground
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at labelMember
    rcases labelMember with rfl | rfl
    · exact ⟨atomRule "A", by simp [pool], rfl, rfl, rfl⟩
    · exact ⟨atomRule "B", by simp [pool], rfl, rfl, rfl⟩

theorem onlyA_atoms : Atoms pool "Atom" [token "A"] := fun value member =>
  ⟨"A", List.mem_singleton.mp member, atomRule "A", by simp [pool], rfl, rfl, rfl⟩

/-- **Keep cannot encode consume**: for no language of rules that put their rest back does the keep reading contain
the consume reading of the pool, since consume steps from `{A}` to `{B}` and keep never loses a member. -/
theorem keep_cannot_encode_consume {other : LanguageDef} (rules : other.rewrites.all keepsRest = true) :
    ¬ ∀ source target, (consumeStructure relEnv pool).step source .any target →
      (keepStructure relEnv other).step source .any target := by
  intro contains
  have consumes : (consumeStructure relEnv pool).step onlyA .any onlyB :=
    (consume_step_iff pool_ground onlyA_atoms onlyA_canonical).mpr
      ⟨0, useA, ["A"], ["B"], "rest", rfl, useA_ground, fun name member => by
        rw [List.mem_singleton.mp member]
        exact List.mem_singleton_self _, by decide +kernel⟩
  have kept := keep_runs_keep_members rules (Relation.ReflTransGen.single ⟨.any, contains _ _ consumes⟩)
    (elements := [token "A"]) rfl (fun element member => by rw [List.mem_singleton.mp member]; rfl) (token "A")
    (List.mem_singleton_self _)
  revert kept
  decide +kernel

/-! ### Mixtures -/

/-- `{A, B, ...rest} ⇒ {C, ...rest}`. -/
def useAB : RewriteRule :=
  { name := "UseAB", typeContext := [("rest", .collection .hashSet (.base "Atom"))], premises := [],
    left := .collection .hashSet [token "A", token "B"] (some "rest"),
    right := .collection .hashSet [token "C"] (some "rest"), bindings := some (restOccurrences [2]) }

def pairPool : LanguageDef :=
  { name := "SetReadings.PairPool", types := [⟨"Atom", .ast⟩, ⟨"Pool", .ast⟩],
    terms := [atomRule "A", atomRule "B", atomRule "C", poolRule], equations := [], rewrites := [useAB] }

theorem useAB_ground : GroundSetRule useAB ["A", "B"] ["C"] "rest" := ⟨rfl, rfl, rfl, by decide⟩

theorem pairPool_ground : GroundSetLanguage pairPool poolRule "Atom" where
  noEquations := rfl
  noAlgebra := by decide
  setCarrier := ⟨by simp [pairPool], ⟨"members", rfl⟩, rfl⟩
  rules := by
    intro rule member
    rw [show pairPool.rewrites = [useAB] from rfl, List.mem_singleton] at member
    subst member
    exact ⟨_, _, _, useAB_ground⟩
  atomsOfSort := by
    intro rule member takes gives rest ground label labelMember
    rw [show pairPool.rewrites = [useAB] from rfl, List.mem_singleton] at member
    subst member
    obtain ⟨rfl, rfl, rfl⟩ := ground.unique useAB_ground
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at labelMember
    rcases labelMember with rfl | rfl | rfl
    · exact ⟨atomRule "A", by simp [pairPool], rfl, rfl, rfl⟩
    · exact ⟨atomRule "B", by simp [pairPool], rfl, rfl, rfl⟩
    · exact ⟨atomRule "C", by simp [pairPool], rfl, rfl, rfl⟩

def onlyAC : Pattern := set [token "A", token "C"]

theorem bothAB_atoms : Atoms pairPool "Atom" [token "A", token "B"] := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨"A", rfl, atomRule "A", by simp [pairPool], rfl, rfl, rfl⟩
  · exact ⟨"B", rfl, atomRule "B", by simp [pairPool], rfl, rfl, rfl⟩

theorem bothAB_canonical : BagForms.sortBags bothAB = bothAB := by decide +kernel

/-- **Either has mixtures**: from `{A, B}` the rule may consume `B` and keep `A`, reaching `{A, C}`, which neither
consume nor keep reaches in one step. -/
theorem either_mixture :
    (referenceStructure relEnv pairPool).step bothAB .any onlyAC ∧
      ¬ (consumeStructure relEnv pairPool).step bothAB .any onlyAC ∧
      ¬ (keepStructure relEnv pairPool).step bothAB .any onlyAC := by
  have present : ∀ name ∈ ["A", "B"], token name ∈ [token "A", token "B"] := by decide
  refine ⟨?_, fun step => ?_, fun step => ?_⟩
  · have step := either_step_to (relEnv := relEnv) pairPool_ground bothAB_atoms bothAB_canonical (index := 0) rfl
      useAB_ground present ["A"]
    have same : BagForms.sortBags (set ((["C"] : List String).map token ++ [token "A", token "B"].filter
        fun value => value ∉ (["A", "B"] : List String).map token ∨ value ∈ (["A"] : List String).map token)) =
        onlyAC := by
      decide +kernel
    exact same ▸ step
  · obtain ⟨index, rule, takes, gives, rest, found, ground, -, reached⟩ :=
      (consume_step_iff pairPool_ground bothAB_atoms bothAB_canonical).mp step
    rw [show rule = useAB from List.mem_singleton.mp (List.mem_of_getElem? found)] at ground
    obtain ⟨rfl, rfl, rfl⟩ := ground.unique useAB_ground
    revert reached
    decide +kernel
  · obtain ⟨index, rule, takes, gives, rest, found, ground, -, reached⟩ :=
      (keep_step_iff pairPool_ground bothAB_atoms bothAB_canonical).mp step
    rw [show rule = useAB from List.mem_singleton.mp (List.mem_of_getElem? found)] at ground
    obtain ⟨rfl, rfl, rfl⟩ := ground.unique useAB_ground
    revert reached
    decide +kernel

end Consequences

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
