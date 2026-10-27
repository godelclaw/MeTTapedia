import Mettapedia.OSLF.MeTTaIL.LawNormalInstantiation
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaTyping
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# Law-normal forms keep typing

Flattening a nested collection of a flattening kind keeps typing when the kind's bare
constructor is homogeneous, `P | Q : Proc` for `P Q : Proc` (`LawsTyped.homogeneous`), and no
type that a derivation can use nests a collection of a flattening kind directly inside itself
(`NoNested`): a nested collection element is then typed by the bare constructor, at the element
type of its parent. Removing a declared unit drops an element.

- `normalize_hasType`: the law-normal form of a typed object term has the same type;
- `normalize_openPatternWellSorted`: law-normal forms of well-sorted open patterns are
  well-sorted.

`RoleAware.reduceAt` is a separate expected-type traversal. Direct collection-valued
slots retain their outer data boundary, while checked base-result algebra occurrences
may splice nested carriers and remove declared units. Its typing theorem needs only
the finite bare-homogeneity check; data slots, free types, and bound types may contain
nested collections. Constructor and substitution domains come from the existing
schema checker. This typing result does not establish source-equational reflection
or canonicality for the unrestricted kind-only law relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- No collection of a flattening kind directly inside another of the same kind. -/
def NoNested (laws : List Laws) : TypeExpr → Prop
  | .base _ => True
  | .arrow domain codomain => NoNested laws domain ∧ NoNested laws codomain
  | .multiBinder domain => NoNested laws domain
  | .collection kind element =>
      NoNested laws element ∧ (∀ law, lawFor laws kind = some law → ∀ inner, element ≠ .collection kind inner)

/-- The declared laws are typed: every bare constructor of a flattening kind is homogeneous, and
no parameter or free name has a type nesting a flattening collection in itself. -/
structure LawsTyped (laws : List Laws) (language : LanguageDef) (free : FreeTypeContext) : Prop where
  homogeneous : ∀ law kind, lawFor laws kind = some law → ∀ rule ∈ language.terms, ∀ name element,
    rule.params = [.simple name (.collection kind element)] → element = .base rule.category
  parameters : ∀ rule ∈ language.terms, ∀ parameter ∈ rule.params, ∀ type,
    parameterType? parameter = some type → NoNested laws type
  freeNames : ∀ name type, free name = some type → NoNested laws type

variable {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}

theorem LawsTyped.homogeneous_bare (admission : LawsTyped laws language free)
    (law : Laws) (kind : CollType) (found : lawFor laws kind = some law)
    (rule : GrammarRule) (declared : rule ∈ language.terms) (name : String) (element : TypeExpr)
    (parameters : rule.bareParams = [.simple name (.collection kind element)]) :
    element = .base rule.category :=
  admission.homogeneous law kind found rule declared name element
    ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2

theorem hasType_collection_inv {bound : List TypeExpr} {kind : CollType} {elements : List Pattern}
    {rest : Option String} {type : TypeExpr} (typed : HasType language free bound (.collection kind elements rest) type) :
    (∃ element, type = .collection kind element ∧ ElementsHaveType language free bound elements element) ∨
      ∃ rule name element, rule ∈ language.terms ∧ rule.bareParams = [.simple name (.collection kind element)] ∧
        type = .base rule.category ∧ ElementsHaveType language free bound elements element := by
  cases typed with
  | collection elements => exact .inl ⟨_, rfl, elements⟩
  | collectionConstructor declared parameters elements => exact .inr ⟨_, _, _, declared, parameters, rfl, elements⟩

theorem matchesParameterRepresentation_normalize {parameter : TermParam} {pattern : Pattern}
    (matched : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (normalize laws pattern) := by
  cases pattern with
  | lambda binder body =>
    rw [normalize]; cases parameter <;> cases binder <;> simp_all [MatchesParameterRepresentation]
  | multiLambda arity binders body =>
    rw [normalize]; cases parameter <;> cases binders <;> simp_all [MatchesParameterRepresentation]
  | collection kind elements rest =>
    rw [normalize_collection']; cases parameter <;> simp_all [MatchesParameterRepresentation]
  | _ => rw [normalize]; cases parameter <;> simp_all [MatchesParameterRepresentation]

/-- A nested collection element of a flattening kind, typed at the element type of its parent,
types its own elements at that element type. -/
theorem splice_typed (admission : LawsTyped laws language free) {law : Laws} {kind : CollType}
    (found : lawFor laws kind = some law) {bound : List TypeExpr} {element : TypeExpr}
    (notCollection : ∀ inner, element ≠ .collection kind inner) {piece : Pattern}
    (typed : HasType language free bound piece element) :
    ∀ item ∈ splice law piece, HasType language free bound item element := by
  have sameKind : law.kind = kind := lawFor_kind found
  intro item member
  cases piece with
  | collection actual elements rest =>
    cases rest with
    | none =>
      simp only [splice] at member
      split at member
      · rename_i isLaw
        subst sameKind
        rw [isLaw] at typed
        rcases hasType_collection_inv typed with ⟨inner, same, _⟩ | ⟨rule, name, inner, declared, parameters, same, items⟩
        · exact absurd same (notCollection inner)
        · have homogeneous := admission.homogeneous_bare law law.kind found rule declared name inner parameters
          subst homogeneous
          rw [same]
          exact elementsHaveType_iff.mp items item member
      · simp only [List.mem_singleton] at member; subst member; exact typed
    | some _ => simp only [splice, List.mem_singleton] at member; subst member; exact typed
  | apply label arguments =>
    cases arguments with
    | nil =>
      simp only [splice] at member
      split at member
      · simp at member
      · simp only [List.mem_singleton] at member; subst member; exact typed
    | cons => simp only [splice, List.mem_singleton] at member; subst member; exact typed
  | _ => simp only [splice, List.mem_singleton] at member; subst member; exact typed

mutual
  /-- **The law-normal form of a typed object term has its type.** -/
  theorem normalize_hasType (admission : LawsTyped laws language free) :
      ∀ {bound : List TypeExpr} {type : TypeExpr} (pattern : Pattern), (∀ entry ∈ bound, NoNested laws entry) →
        NoNested laws type → isObjectPattern pattern = true → HasType language free bound pattern type →
        HasType language free bound (normalize laws pattern) type
    | _, _, .bvar _, _, _, _, typed => by rw [normalize]; exact typed
    | _, _, .fvar _, _, _, _, typed => by rw [normalize]; exact typed
    | bound, _, .apply label arguments, boundOk, _, object, typed => by
      rw [normalize]
      cases typed with
      | constructor declared notBare argumentsTyped =>
        exact .constructor declared notBare (argumentsHaveTypes_normalize admission arguments boundOk
          (by simpa [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] using object)
          (fun parameter member => admission.parameters _ declared parameter member)
          argumentsTyped)
    | bound, _, .lambda binder body, boundOk, typeOk, object, typed => by
      rw [normalize]
      cases typed with
      | @lambda _ _ _ domain codomain bodyTyped =>
        exact .lambda (normalize_hasType admission body
          (fun entry member => by
            rcases List.mem_cons.mp member with rfl | inner
            · exact typeOk.1
            · exact boundOk entry inner)
          typeOk.2 (by simpa [isObjectPattern] using object) bodyTyped)
    | bound, _, .multiLambda arity binders body, boundOk, typeOk, object, typed => by
      rw [normalize]
      cases typed with
      | @multiLambda _ _ _ _ domain codomain bodyTyped =>
        exact .multiLambda (normalize_hasType admission body
          (fun entry member => by
            rcases List.mem_append.mp member with inReplicate | inner
            · rw [List.eq_of_mem_replicate inReplicate]; exact typeOk.1
            · exact boundOk entry inner)
          typeOk.2 (by simpa [isObjectPattern] using object) bodyTyped)
    | _, _, .subst _ _, _, _, object, _ => by simp [isObjectPattern] at object
    | bound, type, .collection kind elements rest, boundOk, typeOk, object, typed => by
      rw [normalize_collection']
      have objects : ∀ item ∈ elements, isObjectPattern item = true := by
        simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at object
        exact object.2
      have each : ∀ {element : TypeExpr}, NoNested laws element →
          ElementsHaveType language free bound elements element →
          ∀ item ∈ elements.map (normalize laws), HasType language free bound item element := by
        intro element elementOk items normalized member
        obtain ⟨item, inElements, rfl⟩ := List.mem_map.mp member
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem inElements; simp only [Pattern.collection.sizeOf_spec]; omega
        exact normalize_hasType admission item boundOk elementOk (objects item inElements)
          (elementsHaveType_iff.mp items item inElements)
      have spliced : ∀ {element : TypeExpr}, NoNested laws element → (∀ law, lawFor laws kind = some law →
          ∀ inner, element ≠ .collection kind inner) → ElementsHaveType language free bound elements element →
          ElementsHaveType language free bound (normalElements laws kind elements) element := by
        intro element elementOk notNested items
        apply elementsHaveType_iff.mpr
        unfold normalElements
        cases found : lawFor laws kind with
        | some law =>
          intro item member
          obtain ⟨piece, inPieces, inSplice⟩ := List.mem_flatMap.mp member
          exact splice_typed admission found (notNested law found) (each elementOk items piece inPieces) item inSplice
        | none => exact each elementOk items
      rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ | ⟨rule, name, element, declared, parameters, rfl, items⟩
      · exact .collection (spliced typeOk.1 typeOk.2 items)
      · have parameterOk := admission.parameters rule declared (.simple name (.collection kind element))
          (by rw [((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2]; exact .head _)
          (.collection kind element) rfl
        have elementOk : NoNested laws element := by unfold NoNested at parameterOk; exact parameterOk.1
        refine .collectionConstructor declared parameters (spliced elementOk ?_ items)
        intro law found inner same
        rw [admission.homogeneous_bare law kind found rule declared name element parameters] at same
        cases same
  termination_by _ _ pattern => sizeOf pattern

  theorem argumentsHaveTypes_normalize (admission : LawsTyped laws language free) :
      ∀ (arguments : List Pattern) {bound : List TypeExpr} {parameters : List TermParam},
        (∀ entry ∈ bound, NoNested laws entry) → (∀ item ∈ arguments, isObjectPattern item = true) →
        (∀ parameter ∈ parameters, ∀ type, parameterType? parameter = some type → NoNested laws type) →
        ArgumentsHaveTypes language free bound arguments parameters →
        ArgumentsHaveTypes language free bound (arguments.map (normalize laws)) parameters
    | [], _, _, _, _, _, .nil => .nil
    | argument :: arguments, _, _ :: _, boundOk, objects, parametersOk, .cons representation parameterType head tail =>
      .cons (matchesParameterRepresentation_normalize representation) parameterType
        (normalize_hasType admission argument boundOk (parametersOk _ (.head _) _ parameterType) (objects _ (.head _)) head)
        (argumentsHaveTypes_normalize admission arguments boundOk (fun item member => objects item (.tail _ member))
          (fun parameter member => parametersOk parameter (.tail _ member)) tail)
  termination_by arguments => sizeOf arguments
end

/-! ## Shape invariants -/

theorem splice_all (law : Laws) (f : Pattern → Bool)
    (onElements : ∀ kind elements, f (.collection kind elements none) = true → ∀ item ∈ elements, f item = true)
    {piece : Pattern} (holds : f piece = true) : ∀ item ∈ splice law piece, f item = true := by
  intro item member
  cases piece with
  | collection actual elements rest =>
    cases rest with
    | none =>
      simp only [splice] at member
      split at member
      · exact onElements _ _ holds item member
      · simp only [List.mem_singleton] at member; subst member; exact holds
    | some _ => simp only [splice, List.mem_singleton] at member; subst member; exact holds
  | apply label arguments =>
    cases arguments with
    | nil =>
      simp only [splice] at member
      split at member
      · simp at member
      · simp only [List.mem_singleton] at member; subst member; exact holds
    | cons => simp only [splice, List.mem_singleton] at member; subst member; exact holds
  | _ => simp only [splice, List.mem_singleton] at member; subst member; exact holds

theorem hasCanonicalBinderMetadataList_eq_all (items : List Pattern) :
    Pattern.hasCanonicalBinderMetadataList items = items.all Pattern.hasCanonicalBinderMetadata := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [Pattern.hasCanonicalBinderMetadataList, ih]

/-- The law-normal form keeps object terms. -/
theorem normalize_object : ∀ (pattern : Pattern), isObjectPattern pattern = true →
    isObjectPattern (normalize laws pattern) = true
  | .bvar _, object => by rw [normalize]; exact object
  | .fvar _, object => by rw [normalize]; exact object
  | .apply label arguments, object => by
    rw [normalize]
    simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true, List.mem_map] at object ⊢
    rintro _ ⟨item, member, rfl⟩
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact normalize_object item (object item member)
  | .lambda _ body, object => by
    rw [normalize]; simp only [isObjectPattern] at object ⊢; exact normalize_object body object
  | .multiLambda _ _ body, object => by
    rw [normalize]; simp only [isObjectPattern] at object ⊢; exact normalize_object body object
  | .subst _ _, object => by simp [isObjectPattern] at object
  | .collection kind elements rest, object => by
    rw [normalize_collection']
    simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at object ⊢
    refine ⟨object.1, ?_⟩
    have each : ∀ item ∈ elements.map (normalize laws), isObjectPattern item = true := by
      rintro _ member
      obtain ⟨item, inElements, rfl⟩ := List.mem_map.mp member
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem inElements; simp only [Pattern.collection.sizeOf_spec]; omega
      exact normalize_object item (object.2 item inElements)
    unfold normalElements
    cases lawFor laws kind with
    | some law =>
      intro item member
      obtain ⟨piece, inPieces, inSplice⟩ := List.mem_flatMap.mp member
      refine splice_all law isObjectPattern ?_ (each piece inPieces) item inSplice
      intro _ _ holds
      simpa [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] using holds
    | none => exact each
termination_by pattern => sizeOf pattern

/-- The law-normal form keeps canonical binder metadata. -/
theorem normalize_binderMetadata : ∀ (pattern : Pattern), pattern.hasCanonicalBinderMetadata = true →
    (normalize laws pattern).hasCanonicalBinderMetadata = true
  | .bvar _, holds => by rw [normalize]; exact holds
  | .fvar _, holds => by rw [normalize]; exact holds
  | .apply label arguments, holds => by
    rw [normalize]
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true,
      List.mem_map] at holds ⊢
    rintro _ ⟨item, member, rfl⟩
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact normalize_binderMetadata item (holds item member)
  | .lambda _ body, holds => by
    rw [normalize]; simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at holds ⊢
    exact ⟨holds.1, normalize_binderMetadata body holds.2⟩
  | .multiLambda _ _ body, holds => by
    rw [normalize]; simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at holds ⊢
    exact ⟨holds.1, normalize_binderMetadata body holds.2⟩
  | .subst body replacement, holds => by
    rw [normalize]; simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at holds ⊢
    exact ⟨normalize_binderMetadata body holds.1, normalize_binderMetadata replacement holds.2⟩
  | .collection kind elements rest, holds => by
    rw [normalize_collection']
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true] at holds ⊢
    have each : ∀ item ∈ elements.map (normalize laws), item.hasCanonicalBinderMetadata = true := by
      rintro _ member
      obtain ⟨item, inElements, rfl⟩ := List.mem_map.mp member
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem inElements; simp only [Pattern.collection.sizeOf_spec]; omega
      exact normalize_binderMetadata item (holds item inElements)
    unfold normalElements
    cases lawFor laws kind with
    | some law =>
      intro item member
      obtain ⟨piece, inPieces, inSplice⟩ := List.mem_flatMap.mp member
      refine splice_all law Pattern.hasCanonicalBinderMetadata ?_ (each piece inPieces) item inSplice
      intro _ _ inner
      simpa [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true] using inner
    | none => exact each
termination_by pattern => sizeOf pattern

/-- **Law-normal forms of well-sorted open patterns are well-sorted**, for typed laws and
types without nested flattening collections. -/
theorem normalize_openPatternWellSorted (admission : LawsTyped laws language free) {bound : List TypeExpr}
    {type : TypeExpr} (boundOk : ∀ entry ∈ bound, NoNested laws entry) (typeOk : NoNested laws type) {pattern : Pattern}
    (sorted : OpenPatternWellSorted language free bound type pattern) :
    OpenPatternWellSorted language free bound type (normalize laws pattern) := by
  obtain ⟨typed, metadata, object, inScope⟩ := sorted
  exact ⟨normalize_hasType admission pattern boundOk typeOk object typed, normalize_binderMetadata pattern metadata,
    normalize_object pattern object, normalize_scoped laws pattern inScope⟩

/-! ## Law moves keep typing, in both directions -/

/-- A type whose collections of a flattening kind have, as element type, the category of a bare
constructor of that kind. -/
def LawTypeOk (laws : List Laws) (language : LanguageDef) : TypeExpr → Prop
  | .base _ => True
  | .arrow domain codomain => LawTypeOk laws language domain ∧ LawTypeOk laws language codomain
  | .multiBinder domain => LawTypeOk laws language domain
  | .collection kind element =>
      (lawFor laws kind = none ∧ LawTypeOk laws language element) ∨
        ∃ rule ∈ language.terms, ∃ name, rule.bareParams = [.simple name (.collection kind (.base rule.category))] ∧
          element = .base rule.category

theorem LawTypeOk.element {kind : CollType} {element : TypeExpr}
    (ok : LawTypeOk laws language (.collection kind element)) : LawTypeOk laws language element := by
  rcases ok with ⟨_, ok⟩ | ⟨_, _, _, _, rfl⟩
  · exact ok
  · trivial

theorem LawTypeOk.lawful {kind : CollType} {law : Laws} {element : TypeExpr} (found : lawFor laws kind = some law)
    (ok : LawTypeOk laws language (.collection kind element)) :
    ∃ rule ∈ language.terms, ∃ name, rule.bareParams = [.simple name (.collection kind (.base rule.category))] ∧
      element = .base rule.category := by
  rcases ok with ⟨unlawful, _⟩ | witness
  · rw [found] at unlawful; cases unlawful
  · exact witness

/-- **Strictly typed laws**: a collection of a flattening kind is built by a homogeneous bare
constructor whose category has the declared unit as a nullary constructor, and every declared
type gives such a collection the category of its constructor as element type. -/
structure LawsTypedStrict (laws : List Laws) (language : LanguageDef) (free : FreeTypeContext) : Prop where
  homogeneous : ∀ law kind, lawFor laws kind = some law → ∀ rule ∈ language.terms, ∀ name element,
    rule.params = [.simple name (.collection kind element)] → element = .base rule.category
  units : ∀ law kind, lawFor laws kind = some law → ∀ label, law.unit = some label →
    ∀ rule ∈ language.terms, ∀ name element, rule.params = [.simple name (.collection kind element)] →
      ∃ unitRule ∈ language.terms, unitRule.label = label ∧ unitRule.params = [] ∧ unitRule.category = rule.category
  parameters : ∀ rule ∈ language.terms, ∀ parameter ∈ rule.params, ∀ type, parameterType? parameter = some type →
    LawTypeOk laws language type
  freeNames : ∀ name type, free name = some type → LawTypeOk laws language type

theorem LawsTypedStrict.homogeneous_bare (admission : LawsTypedStrict laws language free)
    (law : Laws) (kind : CollType) (found : lawFor laws kind = some law)
    (rule : GrammarRule) (declared : rule ∈ language.terms) (name : String) (element : TypeExpr)
    (parameters : rule.bareParams = [.simple name (.collection kind element)]) :
    element = .base rule.category :=
  admission.homogeneous law kind found rule declared name element
    ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2

theorem LawsTypedStrict.units_bare (admission : LawsTypedStrict laws language free)
    (law : Laws) (kind : CollType) (found : lawFor laws kind = some law)
    (label : String) (unit : law.unit = some label)
    (rule : GrammarRule) (declared : rule ∈ language.terms) (name : String) (element : TypeExpr)
    (parameters : rule.bareParams = [.simple name (.collection kind element)]) :
    ∃ unitRule ∈ language.terms, unitRule.label = label ∧ unitRule.params = [] ∧
      unitRule.category = rule.category :=
  admission.units law kind found label unit rule declared name element
    ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2

theorem LawStep.objectPattern_eq {left right : Pattern} (step : LawStep laws left right) :
    isObjectPattern left = isObjectPattern right := by
  induction step with
  | permute _ permutation =>
    simp only [isObjectPattern, isObjectPatternList_eq_all]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item (permutation.mem_iff.mpr member),
        fun all item member => all item (permutation.mem_iff.mp member)⟩)
  | members same =>
    simp only [isObjectPattern, isObjectPatternList_eq_all]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item ((same item).mpr member),
        fun all item member => all item ((same item).mp member)⟩)
  | flatten _ =>
    simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons, Option.isNone_none,
      Bool.true_and, Bool.and_assoc]
  | unit _ _ =>
    simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons, List.all_nil,
      Bool.true_and]
  | apply _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons, ih]
  | lambda _ ih => simp only [isObjectPattern, ih]
  | multiLambda _ ih => simp only [isObjectPattern, ih]
  | substBody _ _ => simp only [isObjectPattern]
  | substReplacement _ _ => simp only [isObjectPattern]
  | element _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons, ih]

theorem LawStep.matchesParameterRepresentation_iff {parameter : TermParam} {left right : Pattern}
    (step : LawStep laws left right) :
    MatchesParameterRepresentation parameter left ↔ MatchesParameterRepresentation parameter right := by
  cases step with
  | lambda _ =>
    rename_i binder _ _ _
    cases parameter <;> cases binder <;> simp [MatchesParameterRepresentation]
  | multiLambda _ =>
    rename_i binders _ _ _
    cases parameter <;> cases binders <;> simp [MatchesParameterRepresentation]
  | _ => cases parameter <;> simp [MatchesParameterRepresentation]

private theorem elementsHaveType_middle {bound : List TypeExpr} {element : TypeExpr}
    {before after : List Pattern} {x y : Pattern}
    (each : HasType language free bound x element → HasType language free bound y element) :
    ElementsHaveType language free bound (before ++ x :: after) element →
      ElementsHaveType language free bound (before ++ y :: after) element := by
  intro typed
  apply elementsHaveType_iff.mpr
  intro item member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with inBefore | rfl | inAfter
  · exact elementsHaveType_iff.mp typed item (by simp [inBefore])
  · exact each (elementsHaveType_iff.mp typed _ (by simp))
  · exact elementsHaveType_iff.mp typed item (by simp [inAfter])

private theorem argumentsHaveTypes_middle' {bound : List TypeExpr} {x y : Pattern}
    (each : ∀ {type : TypeExpr}, LawTypeOk laws language type → HasType language free bound x type →
      HasType language free bound y type)
    (shape : ∀ parameter, MatchesParameterRepresentation parameter x → MatchesParameterRepresentation parameter y) :
    ∀ {before after : List Pattern} {parameters : List TermParam},
      (∀ parameter ∈ parameters, ∀ type, parameterType? parameter = some type → LawTypeOk laws language type) →
      ArgumentsHaveTypes language free bound (before ++ x :: after) parameters →
      ArgumentsHaveTypes language free bound (before ++ y :: after) parameters
  | [], _, _ :: _, parametersOk, .cons representation parameterType head tail =>
    .cons (shape _ representation) parameterType (each (parametersOk _ (.head _) _ parameterType) head) tail
  | _ :: before, after, _ :: _, parametersOk, .cons representation parameterType head tail =>
    .cons representation parameterType head
      (argumentsHaveTypes_middle' each shape (fun parameter member => parametersOk parameter (.tail _ member)) tail)

theorem lawTypeOk_of_parameter (admission : LawsTypedStrict laws language free) {rule : GrammarRule}
    (declared : rule ∈ language.terms) :
    ∀ parameter ∈ rule.params, ∀ type, parameterType? parameter = some type → LawTypeOk laws language type :=
  admission.parameters rule declared

/-- **A law move keeps typing, in both directions**, for strictly typed laws, at types without
collections of a flattening kind. -/
theorem LawStep.hasType_iff (admission : LawsTypedStrict laws language free) {left right : Pattern}
    (step : LawStep laws left right) : ∀ {bound : List TypeExpr} {type : TypeExpr}, isObjectPattern left = true →
      (∀ entry ∈ bound, LawTypeOk laws language entry) → LawTypeOk laws language type →
      (HasType language free bound left type ↔ HasType language free bound right type) := by
  induction step with
  | permute _ permutation =>
    intro bound type _ _ _
    have perm : ∀ {element : TypeExpr} {xs ys : List Pattern}, xs.Perm ys →
        ElementsHaveType language free bound xs element → ElementsHaveType language free bound ys element :=
      fun perm typed => elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp typed item (perm.mem_iff.mpr member)
    constructor
    · intro typed
      cases typed with
      | collection elements => exact .collection (perm permutation elements)
      | collectionConstructor declared parameters elements =>
        exact .collectionConstructor declared parameters (perm permutation elements)
    · intro typed
      cases typed with
      | collection elements => exact .collection (perm permutation.symm elements)
      | collectionConstructor declared parameters elements =>
        exact .collectionConstructor declared parameters (perm permutation.symm elements)
  | members same =>
    intro bound type _ _ _
    have presents : ∀ {element : TypeExpr} {xs ys : List Pattern}, (∀ a, a ∈ xs ↔ a ∈ ys) →
        ElementsHaveType language free bound xs element → ElementsHaveType language free bound ys element :=
      fun same typed => elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp typed item ((same item).mpr member)
    constructor
    · intro typed
      cases typed with
      | collection elements => exact .collection (presents same elements)
      | collectionConstructor declared parameters elements =>
        exact .collectionConstructor declared parameters (presents same elements)
    · intro typed
      cases typed with
      | collection elements => exact .collection (presents (fun a => (same a).symm) elements)
      | collectionConstructor declared parameters elements =>
        exact .collectionConstructor declared parameters (presents (fun a => (same a).symm) elements)
  | @flatten kind law before inner after rest found =>
    intro bound type _ _ typeOk
    have flattenElements : ∀ {category : String}, ElementsHaveType language free bound
        (before ++ .collection kind inner none :: after) (.base category) →
        ElementsHaveType language free bound (before ++ inner ++ after) (.base category) := by
      intro category items
      apply elementsHaveType_iff.mpr
      intro item member
      simp only [List.mem_append] at member
      rcases member with (inBefore | inInner) | inAfter
      · exact elementsHaveType_iff.mp items item (by simp [inBefore])
      · have nested := elementsHaveType_iff.mp items (.collection kind inner none) (by simp)
        rcases hasType_collection_inv nested with ⟨_, same, _⟩ | ⟨rule', name', element', declared', parameters', same, innerItems⟩
        · cases same
        · have homogeneous' := admission.homogeneous_bare law kind found rule' declared' name' element' parameters'
          subst homogeneous'
          rw [same]
          exact elementsHaveType_iff.mp innerItems item inInner
      · exact elementsHaveType_iff.mp items item (by simp [inAfter])
    have unflattenElements : ∀ {rule : GrammarRule} {name : String}, rule ∈ language.terms →
        rule.bareParams = [.simple name (.collection kind (.base rule.category))] →
        ElementsHaveType language free bound (before ++ inner ++ after) (.base rule.category) →
        ElementsHaveType language free bound (before ++ .collection kind inner none :: after) (.base rule.category) := by
      intro rule name declared parameters items
      apply elementsHaveType_iff.mpr
      intro item member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact elementsHaveType_iff.mp items item (by simp [inBefore])
      · exact .collectionConstructor declared parameters (elementsHaveType_iff.mpr fun item member =>
          elementsHaveType_iff.mp items item (by simp [member]))
      · exact elementsHaveType_iff.mp items item (by simp [inAfter])
    constructor
    · intro typed
      rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ | ⟨rule, name, element, declared, parameters, rfl, items⟩
      · obtain ⟨_, _, _, _, rfl⟩ := typeOk.lawful found
        exact .collection (flattenElements items)
      · have homogeneous := admission.homogeneous_bare law kind found rule declared name element parameters
        subst homogeneous
        exact .collectionConstructor declared parameters (flattenElements items)
    · intro typed
      rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ | ⟨rule, name, element, declared, parameters, rfl, items⟩
      · obtain ⟨witness, witnessDeclared, witnessName, witnessParameters, rfl⟩ := typeOk.lawful found
        exact .collection (unflattenElements witnessDeclared witnessParameters items)
      · have homogeneous := admission.homogeneous_bare law kind found rule declared name element parameters
        subst homogeneous
        exact .collectionConstructor declared parameters (unflattenElements declared parameters items)
  | @unit kind law label before after rest found unit =>
    intro bound type _ _ typeOk
    have dropElements : ∀ {element : TypeExpr}, ElementsHaveType language free bound
        (before ++ .apply label [] :: after) element → ElementsHaveType language free bound (before ++ after) element :=
      fun items => elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp items item (by simp only [List.mem_append, List.mem_cons] at member ⊢; tauto)
    have insertUnit : ∀ {rule : GrammarRule} {name : String}, rule ∈ language.terms →
        rule.bareParams = [.simple name (.collection kind (.base rule.category))] →
        ElementsHaveType language free bound (before ++ after) (.base rule.category) →
        ElementsHaveType language free bound (before ++ .apply label [] :: after) (.base rule.category) := by
      intro rule name declared parameters items
      obtain ⟨unitRule, unitDeclared, unitLabel, unitParams, unitCategory⟩ :=
        admission.units_bare law kind found label unit rule declared name _ parameters
      apply elementsHaveType_iff.mpr
      intro item member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact elementsHaveType_iff.mp items item (by simp [inBefore])
      · have typedUnit := HasType.constructor (language := language) (free := free) (bound := bound)
          (rule := unitRule) (arguments := []) unitDeclared
          (fun ⟨_, _, _, bare⟩ => by
            have raw := ((GrammarRule.bareParams_cons_iff _ _ _).mp bare).2
            rw [unitParams] at raw
            cases raw) (by rw [unitParams]; exact .nil)
        rw [unitLabel, unitCategory] at typedUnit
        exact typedUnit
      · exact elementsHaveType_iff.mp items item (by simp [inAfter])
    constructor
    · intro typed
      rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ | ⟨rule, name, element, declared, parameters, rfl, items⟩
      · exact .collection (dropElements items)
      · exact .collectionConstructor declared parameters (dropElements items)
    · intro typed
      rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ | ⟨rule, name, element, declared, parameters, rfl, items⟩
      · obtain ⟨witness, witnessDeclared, witnessName, witnessParameters, rfl⟩ := typeOk.lawful found
        exact .collection (insertUnit witnessDeclared witnessParameters items)
      · have homogeneous := admission.homogeneous_bare law kind found rule declared name element parameters
        subst homogeneous
        exact .collectionConstructor declared parameters (insertUnit declared parameters items)
  | @apply label before after argument changed inner ih =>
    intro bound type object boundOk _
    have argumentObject : isObjectPattern argument = true := by
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      exact object argument (by simp)
    constructor
    · intro typed
      cases typed with
      | constructor declared notBare arguments =>
        exact .constructor declared notBare (argumentsHaveTypes_middle' (fun typeOk typed => (ih argumentObject boundOk typeOk).mp typed)
          (fun _ => (inner.matchesParameterRepresentation_iff).mp) (lawTypeOk_of_parameter admission declared)
          arguments)
    · intro typed
      cases typed with
      | constructor declared notBare arguments =>
        exact .constructor declared notBare (argumentsHaveTypes_middle' (fun typeOk typed => (ih argumentObject boundOk typeOk).mpr typed)
          (fun _ => (inner.matchesParameterRepresentation_iff).mpr) (lawTypeOk_of_parameter admission declared)
          arguments)
  | lambda _ ih =>
    intro bound type object boundOk typeOk
    simp only [isObjectPattern] at object
    constructor
    · intro typed
      cases typed with
      | lambda body =>
        exact .lambda ((ih object (fun entry member => by
          rcases List.mem_cons.mp member with rfl | inner
          · exact typeOk.1
          · exact boundOk entry inner) typeOk.2).mp body)
    · intro typed
      cases typed with
      | lambda body =>
        exact .lambda ((ih object (fun entry member => by
          rcases List.mem_cons.mp member with rfl | inner
          · exact typeOk.1
          · exact boundOk entry inner) typeOk.2).mpr body)
  | multiLambda _ ih =>
    intro bound type object boundOk typeOk
    simp only [isObjectPattern] at object
    have extended : ∀ (arity : Nat) (domain : TypeExpr), LawTypeOk laws language (.multiBinder domain) →
        ∀ entry ∈ List.replicate arity domain ++ bound, LawTypeOk laws language entry := by
      intro arity domain domainOk entry member
      rcases List.mem_append.mp member with inReplicate | inner
      · rw [List.eq_of_mem_replicate inReplicate]; exact domainOk
      · exact boundOk entry inner
    constructor
    · intro typed
      cases typed with
      | multiLambda body => exact .multiLambda ((ih object (extended _ _ typeOk.1) typeOk.2).mp body)
    · intro typed
      cases typed with
      | multiLambda body => exact .multiLambda ((ih object (extended _ _ typeOk.1) typeOk.2).mpr body)
  | substBody _ _ => intro bound type object; simp [isObjectPattern] at object
  | substReplacement _ _ => intro bound type object; simp [isObjectPattern] at object
  | @element kind before after element changed rest inner ih =>
    intro bound type object boundOk typeOk
    have elementObject : isObjectPattern element = true := by
      simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at object
      exact object.2 element (by simp)
    have elementOk : ∀ {elementType : TypeExpr}, (type = .collection kind elementType ∨
        ∃ rule name, rule ∈ language.terms ∧ rule.bareParams = [.simple name (.collection kind elementType)] ∧
          type = .base rule.category) → LawTypeOk laws language elementType := by
      intro elementType origin
      rcases origin with rfl | ⟨rule, name, declared, parameters, rfl⟩
      · exact typeOk.element
      · exact (admission.parameters rule declared _
          (by rw [((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2]; exact .head _) _ rfl).element
    constructor
    · intro typed
      rcases hasType_collection_inv typed with ⟨elementType, rfl, items⟩ | ⟨rule, name, elementType, declared, parameters, rfl, items⟩
      · exact .collection (elementsHaveType_middle (fun t => (ih elementObject boundOk (elementOk (.inl rfl))).mp t) items)
      · exact .collectionConstructor declared parameters
          (elementsHaveType_middle (fun t => (ih elementObject boundOk (elementOk (.inr ⟨rule, name, declared, parameters, rfl⟩))).mp t) items)
    · intro typed
      rcases hasType_collection_inv typed with ⟨elementType, rfl, items⟩ | ⟨rule, name, elementType, declared, parameters, rfl, items⟩
      · exact .collection (elementsHaveType_middle (fun t => (ih elementObject boundOk (elementOk (.inl rfl))).mpr t) items)
      · exact .collectionConstructor declared parameters
          (elementsHaveType_middle (fun t => (ih elementObject boundOk (elementOk (.inr ⟨rule, name, declared, parameters, rfl⟩))).mpr t) items)

theorem LawStep.binderMetadata_eq {left right : Pattern} (step : LawStep laws left right) :
    left.hasCanonicalBinderMetadata = right.hasCanonicalBinderMetadata := by
  induction step with
  | permute _ permutation =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item (permutation.mem_iff.mpr member),
        fun all item member => all item (permutation.mem_iff.mp member)⟩)
  | members same =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item ((same item).mpr member),
        fun all item member => all item ((same item).mp member)⟩)
  | flatten _ =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_append,
      List.all_cons, Bool.and_assoc]
  | unit _ _ =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_append,
      List.all_cons, Pattern.hasCanonicalBinderMetadataList, Bool.true_and]
  | apply _ ih =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_append,
      List.all_cons, ih]
  | lambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | multiLambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substBody _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substReplacement _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | element _ ih =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_append,
      List.all_cons, ih]

/-- **A law move keeps well-sortedness, in both directions.** -/
theorem LawStep.openPatternWellSorted_iff (admission : LawsTypedStrict laws language free) {left right : Pattern}
    (step : LawStep laws left right) {bound : List TypeExpr} {type : TypeExpr}
    (boundOk : ∀ entry ∈ bound, LawTypeOk laws language entry) (typeOk : LawTypeOk laws language type) :
    OpenPatternWellSorted language free bound type left ↔ OpenPatternWellSorted language free bound type right := by
  constructor
  · rintro ⟨typed, metadata, object, inScope⟩
    exact ⟨(step.hasType_iff admission object boundOk typeOk).mp typed, step.binderMetadata_eq ▸ metadata,
      step.objectPattern_eq ▸ object, by unfold ScopeSafeAt at inScope ⊢; rw [← step.wellScoped]; exact inScope⟩
  · rintro ⟨typed, metadata, object, inScope⟩
    have leftObject : isObjectPattern left = true := step.objectPattern_eq ▸ object
    exact ⟨(step.hasType_iff admission leftObject boundOk typeOk).mpr typed, step.binderMetadata_eq ▸ metadata,
      leftObject, by unfold ScopeSafeAt at inScope ⊢; rw [step.wellScoped]; exact inScope⟩

/-- **Law-equal well-sorted terms are well-sorted.** -/
theorem LawSame.openPatternWellSorted (admission : LawsTypedStrict laws language free) {left right : Pattern}
    (same : LawSame laws left right) {bound : List TypeExpr} {type : TypeExpr}
    (boundOk : ∀ entry ∈ bound, LawTypeOk laws language entry) (typeOk : LawTypeOk laws language type)
    (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  have chain : Relation.ReflTransGen (Relation.SymmGen (LawStep laws)) left right := by
    rw [Relation.EqvGen.reflTransGen_symmGen]; exact same
  clear same
  induction chain with
  | refl => exact sorted
  | tail _ step ih =>
    rcases step with forward | backward
    · exact (forward.openPatternWellSorted_iff admission boundOk typeOk).mp ih
    · exact (backward.openPatternWellSorted_iff admission boundOk typeOk).mpr ih

end Mettapedia.OSLF.MeTTaIL.CanonicalBags

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.RoleAware

set_option maxHeartbeats 1800000

open Syntax CollectionLaws
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralPremise.SchemaTyping

def checkBareHomogeneous (laws : List Laws) (language : LanguageDef) : Bool :=
  language.terms.all fun rule =>
    match rule.bareParams with
    | [.simple _ (.collection kind element)] =>
        (lawFor laws kind).isNone || element == .base rule.category
    | _ => true

theorem homogeneous_bare_of_checked {laws : List Laws} {language : LanguageDef}
    (checked : checkBareHomogeneous laws language = true)
    {law : Laws} {kind : CollType} (found : lawFor laws kind = some law)
    {rule : GrammarRule} (member : rule ∈ language.terms)
    {parameter : String} {element : TypeExpr}
    (shape : rule.bareParams = [.simple parameter (.collection kind element)]) :
    element = .base rule.category := by
  have selected := List.all_eq_true.mp checked rule member
  simpa only [shape,found,Option.isNone_some,Bool.false_or,beq_iff_eq] using selected

theorem checkBareHomogeneous_of_lawsTyped {laws : List Laws} {language : LanguageDef}
    {free : FreeTypeContext} (admission : LawsTyped laws language free) :
    checkBareHomogeneous laws language = true := by
  apply List.all_eq_true.mpr
  intro rule member
  split
  next parameter kind element shape =>
    cases found : lawFor laws kind with
    | none => simp
    | some law =>
        have same := admission.homogeneous_bare law kind found rule member parameter element shape
        simp [same]
  next => rfl

theorem splice_base_typed {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    (checked : checkBareHomogeneous laws language = true)
    {law : Laws} {kind : CollType} (found : lawFor laws kind = some law)
    {bound : List TypeExpr} {category : String} {piece : Pattern}
    (typed : HasType language free bound piece (.base category)) :
    ∀ item ∈ splice law piece, HasType language free bound item (.base category) := by
  have sameKind := lawFor_kind found
  intro item member
  cases piece with
  | collection actual elements rest =>
    cases rest with
    | none =>
      simp only [splice] at member
      split at member
      · rename_i same
        subst sameKind
        rw [same] at typed
        rcases hasType_collection_inv typed with ⟨element,impossible,_⟩ |
          ⟨rule,parameter,element,declared,parameters,categoryEq,items⟩
        · cases impossible
        · have homogeneous := homogeneous_bare_of_checked checked found declared parameters
          rw [homogeneous] at items
          rw [categoryEq]
          exact elementsHaveType_iff.mp items item member
      · simp only [List.mem_singleton] at member
        subst item
        exact typed
    | some _ =>
      simp only [splice,List.mem_singleton] at member
      subst item
      exact typed
  | apply label arguments =>
    cases arguments with
    | nil =>
      simp only [splice] at member
      split at member
      · simp at member
      · simp only [List.mem_singleton] at member
        subst item
        exact typed
    | cons =>
      simp only [splice,List.mem_singleton] at member
      subst item
      exact typed
  | _ =>
    simp only [splice,List.mem_singleton] at member
    subst item
    exact typed

def applicationRule? (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (label : String) (arguments : List Pattern) :
    Option GrammarRule :=
  language.terms.find? fun rule => rule.label == label && expected == .base rule.category &&
    !usesBareCollection? rule && checkSchemaArguments domains language free bound arguments rule.params

def collectionRule? (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (kind : CollType) (elements : List Pattern)
    (rest : Option String) : Option GrammarRule :=
  language.terms.find? fun rule =>
    match bareCollectionElementType? rule kind expected with
    | some element => checkSchemaElements domains language free bound elements element &&
        checkSchemaRest free kind element rest
    | none => false

def substitutionDomain? (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (body replacement : Pattern) : Option TypeExpr :=
  domains.find? fun domain =>
    checkSchemaType domains language free (domain :: bound) body expected &&
      checkSchemaType domains language free bound replacement domain

theorem applicationRule_isSome (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (label : String) (arguments : List Pattern) :
    (applicationRule? domains language free bound expected label arguments).isSome =
      checkSchemaType domains language free bound (.apply label arguments) expected := by
  simp only [applicationRule?,List.isSome_find?,checkSchemaType]

theorem collectionRule_base_isSome (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (category : String) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    (collectionRule? domains language free bound (.base category) kind elements rest).isSome =
      checkSchemaType domains language free bound (.collection kind elements rest) (.base category) := by
  simp only [collectionRule?,List.isSome_find?,checkSchemaType,Bool.false_or]
  rfl

theorem substitutionDomain_isSome (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (body replacement : Pattern) :
    (substitutionDomain? domains language free bound expected body replacement).isSome =
      checkSchemaType domains language free bound (.subst body replacement) expected := by
  simp only [substitutionDomain?,List.isSome_find?,checkSchemaType]

def finishAlgebra (laws : List Laws) (kind : CollType) (elements : List Pattern) : List Pattern :=
  match lawFor laws kind with
  | some law => elements.flatMap (splice law)
  | none => elements

mutual
  def reduceAt (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Pattern :=
    match pattern with
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments =>
        match applicationRule? domains language free bound expected label arguments with
        | some rule => .apply label (reduceArguments laws domains language free bound arguments rule.params)
        | none => pattern
    | .lambda binder body =>
        match expected with
        | .arrow domain codomain => .lambda binder (reduceAt laws domains language free (domain :: bound) body codomain)
        | _ => pattern
    | .multiLambda arity binders body =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            .multiLambda arity binders
              (reduceAt laws domains language free (List.replicate arity domain ++ bound) body codomain)
        | _ => pattern
    | .subst body replacement =>
        match substitutionDomain? domains language free bound expected body replacement with
        | some domain => .subst (reduceAt laws domains language free (domain :: bound) body expected)
            (reduceAt laws domains language free bound replacement domain)
        | none => pattern
    | .collection kind elements rest =>
        match expected with
        | .collection actual element =>
            if actual = kind then .collection kind (reduceElements laws domains language free bound elements element) rest
            else pattern
        | _ =>
            match collectionRule? domains language free bound expected kind elements rest with
            | none => pattern
            | some rule =>
                match bareCollectionElementType? rule kind expected with
                | none => pattern
                | some element => .collection kind
                    (finishAlgebra laws kind (reduceElements laws domains language free bound elements element)) rest
  termination_by sizeOf pattern

  def reduceArguments (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) : List Pattern → List TermParam → List Pattern
    | [], _ => []
    | argument :: arguments, parameter :: parameters =>
        match parameterType? parameter with
        | some expected => reduceAt laws domains language free bound argument expected ::
            reduceArguments laws domains language free bound arguments parameters
        | none => argument :: reduceArguments laws domains language free bound arguments parameters
    | arguments, [] => arguments
  termination_by arguments _ => sizeOf arguments

  def reduceElements (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) : List Pattern → TypeExpr → List Pattern
    | [], _ => []
    | element :: elements, expected => reduceAt laws domains language free bound element expected ::
        reduceElements laws domains language free bound elements expected
  termination_by elements _ => sizeOf elements
end

theorem reduceAt_parameter_representation (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) {parameter : TermParam} {pattern : Pattern}
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (reduceAt laws domains language free bound pattern expected) := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
      obtain ⟨body,rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp represented
      cases expected <;> simp [reduceAt,MatchesParameterRepresentation]
  | multiAbstractionNamed binders name type =>
      obtain ⟨arity,body,rfl⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mp represented
      cases expected <;> simp [reduceAt,MatchesParameterRepresentation]
      case arrow domain codomain => cases domain <;> simp [reduceAt]

theorem reduceArguments_hasTypes_of (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    {arguments : List Pattern} {parameters : List TermParam}
    (each : ∀ argument ∈ arguments, ∀ expected,
      HasType language free bound argument expected →
        HasType language free bound (reduceAt laws domains language free bound argument expected) expected)
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    ArgumentsHaveTypes language free bound (reduceArguments laws domains language free bound arguments parameters) parameters := by
  induction arguments generalizing parameters with
  | nil => cases typed; simpa only [reduceArguments] using (ArgumentsHaveTypes.nil (language := language) (free := free) (bound := bound))
  | cons argument arguments ih =>
      cases typed with
      | cons representation parameterType head tail =>
        simp only [reduceArguments,parameterType]
        exact .cons (reduceAt_parameter_representation laws domains language free bound _ representation)
          parameterType (each argument List.mem_cons_self _ head)
          (ih (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

theorem reduceElements_hasType_of (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    {elements : List Pattern} {expected : TypeExpr}
    (each : ∀ element ∈ elements,
      HasType language free bound element expected →
        HasType language free bound (reduceAt laws domains language free bound element expected) expected)
    (typed : ElementsHaveType language free bound elements expected) :
    ElementsHaveType language free bound (reduceElements laws domains language free bound elements expected) expected := by
  induction elements with
  | nil => simpa only [reduceElements] using (ElementsHaveType.nil (language := language) (free := free) bound expected)
  | cons element elements ih =>
      cases typed with
      | cons head tail =>
        simpa only [reduceElements] using ElementsHaveType.cons (each element List.mem_cons_self head)
          (ih (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

theorem applicationRule_readout {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {label : String} {arguments : List Pattern} {rule : GrammarRule}
    (selected : applicationRule? domains language free bound expected label arguments = some rule) :
    rule ∈ language.terms ∧ rule.label = label ∧ expected = .base rule.category ∧
      ¬ UsesBareCollection rule ∧ ArgumentsHaveTypes language free bound arguments rule.params := by
  have member := List.mem_of_find?_eq_some selected
  have checked := List.find?_some selected
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at checked
  obtain ⟨⟨⟨head,type⟩,notBare⟩,argumentsChecked⟩ := checked
  refine ⟨member,head,type,?_,?_⟩
  · intro bare
    have bareChecked := (usesBareCollection?_eq_true_iff rule).mpr bare
    rw [bareChecked] at notBare
    contradiction
  · exact checkSchemaArguments_sound_of (fun _ _ _ input => checkSchemaType_sound input) argumentsChecked

theorem collectionRule_readout {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {kind : CollType} {elements : List Pattern} {rest : Option String} {rule : GrammarRule}
    (selected : collectionRule? domains language free bound expected kind elements rest = some rule) :
    ∃ element, rule ∈ language.terms ∧ bareCollectionElementType? rule kind expected = some element ∧
      ElementsHaveType language free bound elements element := by
  have member := List.mem_of_find?_eq_some selected
  have checked := List.find?_some selected
  cases shape : bareCollectionElementType? rule kind expected with
  | none => simp only [shape,Bool.false_eq_true] at checked
  | some element =>
      simp only [shape,Bool.and_eq_true] at checked
      exact ⟨element,member,rfl,checkSchemaElements_sound checked.1⟩

theorem substitutionDomain_readout {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {body replacement : Pattern} {domain : TypeExpr}
    (selected : substitutionDomain? domains language free bound expected body replacement = some domain) :
    domain ∈ domains ∧ HasType language free (domain :: bound) body expected ∧
      HasType language free bound replacement domain := by
  have member := List.mem_of_find?_eq_some selected
  have checked := List.find?_some selected
  simp only [Bool.and_eq_true] at checked
  exact ⟨member,checkSchemaType_sound checked.1,checkSchemaType_sound checked.2⟩

theorem finishAlgebra_base_typed {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    (checked : checkBareHomogeneous laws language = true)
    {bound : List TypeExpr} {category : String} {kind : CollType} {elements : List Pattern}
    (typed : ElementsHaveType language free bound elements (.base category)) :
    ElementsHaveType language free bound (finishAlgebra laws kind elements) (.base category) := by
  unfold finishAlgebra
  cases found : lawFor laws kind with
  | none => exact typed
  | some law =>
      apply elementsHaveType_iff.mpr
      intro item member
      obtain ⟨piece,present,inSplice⟩ := List.mem_flatMap.mp member
      exact splice_base_typed checked found (elementsHaveType_iff.mp typed piece present) item inSplice

theorem reduceAt_hasType {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    (checked : checkBareHomogeneous laws language = true) (domains : List TypeExpr)
    {bound : List TypeExpr} {expected : TypeExpr} (pattern : Pattern)
    (typed : HasType language free bound pattern expected) :
    HasType language free bound (reduceAt laws domains language free bound pattern expected) expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index => simpa only [reduceAt] using typed
  | hfvar name => simpa only [reduceAt] using typed
  | happly label arguments ih =>
      rw [reduceAt]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => exact typed
      | some rule =>
        obtain ⟨member,head,type,notBare,argumentsTyped⟩ := applicationRule_readout selected
        rw [← head,type]
        exact .constructor member notBare
          (reduceArguments_hasTypes_of laws domains language free bound
            (fun argument present _ input => ih argument present input) argumentsTyped)
  | hlambda binder body ih =>
      cases typed with
      | lambda bodyTyped =>
          simpa only [reduceAt] using HasType.lambda (binder := binder) (ih bodyTyped)
  | hmultiLambda arity binders body ih =>
      cases typed with
      | multiLambda bodyTyped =>
          simpa only [reduceAt] using HasType.multiLambda (binders := binders) (ih bodyTyped)
  | hsubst body replacement bodyIH replacementIH =>
      rw [reduceAt]
      cases selected : substitutionDomain? domains language free bound expected body replacement with
      | none => exact typed
      | some domain =>
          obtain ⟨_,bodyTyped,replacementTyped⟩ := substitutionDomain_readout selected
          exact .subst (bodyIH bodyTyped) (replacementIH replacementTyped)
  | hcollection kind elements rest ih =>
      rcases hasType_collection_inv typed with ⟨element,rfl,items⟩ |
        ⟨sourceRule,parameter,sourceElement,sourceDeclared,sourceParameters,rfl,sourceItems⟩
      · simp only [reduceAt,↓reduceIte]
        exact .collection (reduceElements_hasType_of laws domains language free bound
          (fun element member input => ih element member input) items)
      · simp only [reduceAt]
        cases selected : collectionRule? domains language free bound (.base sourceRule.category) kind elements rest with
        | none => exact typed
        | some rule =>
          obtain ⟨element,member,shape,items⟩ := collectionRule_readout selected
          simp only [shape]
          obtain ⟨expectedEq,parameter,parameters⟩ :=
            (bareCollectionElementType?_eq_some_iff _ _ _ _).mp shape
          have normalizedItems := reduceElements_hasType_of laws domains language free bound
            (fun element present input => ih element present input) items
          have resultItems : ElementsHaveType language free bound
              (finishAlgebra laws kind (reduceElements laws domains language free bound elements element)) element := by
            cases found : lawFor laws kind with
            | none => simpa only [finishAlgebra,found] using normalizedItems
            | some law =>
                have homogeneous := homogeneous_bare_of_checked checked found member parameters
                rw [homogeneous] at normalizedItems ⊢
                exact finishAlgebra_base_typed checked normalizedItems
          rw [expectedEq]
          exact .collectionConstructor member parameters resultItems

#print axioms homogeneous_bare_of_checked
#print axioms checkBareHomogeneous_of_lawsTyped
#print axioms splice_base_typed
#print axioms reduceAt_parameter_representation
#print axioms reduceArguments_hasTypes_of
#print axioms reduceElements_hasType_of
#print axioms applicationRule_readout
#print axioms collectionRule_readout
#print axioms substitutionDomain_readout
#print axioms finishAlgebra_base_typed
#print axioms reduceAt_hasType
#print axioms applicationRule_isSome
#print axioms collectionRule_base_isSome
#print axioms substitutionDomain_isSome

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.RoleAware

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.RoleAware

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws DerivedContexts GeneralPremise.SchemaTyping
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- Source authority for the algebra row actually selected at a checked
base-result occurrence. The existing checkedAlgebra? validator can supply
each field from its literal row, parameter and authored unit inventory. -/
def SourceAlgebras (laws : List Laws) (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.terms, ∀ kind parameter law,
    rule.bareParams = [.simple parameter (.collection kind (.base rule.category))] →
    lawFor laws kind = some law →
      AlgebraRule language rule kind ⟨true, law.unit⟩

private theorem equivalent_children {relEnv : Engine.RelationEnv} {language : LanguageDef}
    (node : List Pattern → Pattern) (frame : List Pattern → List Pattern → OneHoleContext)
    (fills : ∀ before item after, (frame before after).fill item = node (before ++ item :: after)) :
    ∀ {first second : List Pattern}, List.Forall₂ (ReferenceStep.Equivalent relEnv language) first second →
      ∀ before, ReferenceStep.Equivalent relEnv language (node (before ++ first)) (node (before ++ second)) := by
  intro first second compared
  induction compared with
  | nil => intro before; exact .refl _
  | @cons first second tail otherTail head tailCompared recurse =>
      intro before
      have initial := ReferenceStep.equivalent_fill (frame before tail) head
      simp only [fills] at initial
      have later := recurse (before ++ [second])
      simp only [List.append_assoc, List.singleton_append] at later
      exact .trans _ _ _ initial later

private theorem reduceArguments_equivalent_of
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (each : ∀ argument ∈ arguments, ∀ expected, HasType language free bound argument expected →
      ReferenceStep.SourceCollections language argument →
      ReferenceStep.Equivalent relEnv language argument (reduceAt laws domains language free bound argument expected))
    (eligible : ∀ argument ∈ arguments, ReferenceStep.SourceCollections language argument)
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    List.Forall₂ (ReferenceStep.Equivalent relEnv language) arguments
      (reduceArguments laws domains language free bound arguments parameters) := by
  induction arguments generalizing parameters with
  | nil => cases typed; simpa only [reduceArguments] using (List.Forall₂.nil :
      List.Forall₂ (ReferenceStep.Equivalent relEnv language) [] [])
  | cons argument arguments recurse =>
      cases typed with
      | cons representation parameterType head tail =>
        simp only [reduceArguments, parameterType]
        exact .cons (each argument (.head _) _ head (eligible argument (.head _)))
          (recurse
            (fun argument member expected typed source => each argument (.tail _ member) expected typed source)
            (fun argument member => eligible argument (.tail _ member)) tail)

private theorem reduceElements_equivalent_of
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {expected : TypeExpr}
    (each : ∀ element ∈ elements, HasType language free bound element expected →
      ReferenceStep.SourceCollections language element →
      ReferenceStep.Equivalent relEnv language element (reduceAt laws domains language free bound element expected))
    (eligible : ∀ element ∈ elements, ReferenceStep.SourceCollections language element)
    (typed : ElementsHaveType language free bound elements expected) :
    List.Forall₂ (ReferenceStep.Equivalent relEnv language) elements
      (reduceElements laws domains language free bound elements expected) := by
  induction elements with
  | nil => simpa only [reduceElements] using (List.Forall₂.nil :
      List.Forall₂ (ReferenceStep.Equivalent relEnv language) [] [])
  | cons element elements recurse =>
      cases typed with
      | cons head tail =>
        simpa only [reduceElements] using List.Forall₂.cons
          (each element (.head _) head (eligible element (.head _)))
          (recurse
            (fun element member typed source => each element (.tail _ member) typed source)
            (fun element member => eligible element (.tail _ member)) tail)

private theorem elements_insert_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {before after middle : List Pattern} {item : Pattern}
    (typed : ElementsHaveType language free bound (before ++ item :: after) expected)
    (inserted : ElementsHaveType language free bound middle expected) :
    ElementsHaveType language free bound (before ++ middle ++ after) expected := by
  apply CanonicalBags.elementsHaveType_iff.mpr
  intro element member
  simp only [List.mem_append] at member
  rcases member with (earlier | inner) | later
  · exact CanonicalBags.elementsHaveType_iff.mp typed element (by simp [earlier])
  · exact CanonicalBags.elementsHaveType_iff.mp inserted element inner
  · exact CanonicalBags.elementsHaveType_iff.mp typed element (by simp [later])

private theorem source_splice_other {law : Laws} {pattern : Pattern}
    (notNested : ¬ ∃ items, pattern = .collection law.kind items none)
    (notUnit : ¬ ∃ label, pattern = .apply label [] ∧ law.unit = some label) :
    CollectionLaws.splice law pattern = [pattern] := by
  cases pattern with
  | collection kind elements rest =>
      cases rest with
      | none =>
          have different : kind ≠ law.kind := by
            intro same
            exact notNested ⟨elements, same ▸ rfl⟩
          simp [CollectionLaws.splice, different]
      | some => rfl
  | apply label arguments =>
      cases arguments with
      | nil =>
          have different : law.unit ≠ some label := fun same => notUnit ⟨label, rfl, same⟩
          simp [CollectionLaws.splice, different]
      | cons => rfl
  | _ => rfl

private theorem splice_source_equivalent
    {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true)
    {rule : GrammarRule} {kind : CollType} {parameter : String} {law : Laws}
    (shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))])
    (found : lawFor laws kind = some law)
    (declaration : AlgebraRule language rule kind ⟨true, law.unit⟩)
    {bound : List TypeExpr} : ∀ (todo done : List Pattern),
      ElementsHaveType language free bound (done ++ todo) (.base rule.category) →
      ReferenceStep.Equivalent relEnv language (.collection kind (done ++ todo) none)
        (.collection kind (done ++ todo.flatMap (CollectionLaws.splice law)) none)
  | [], _, _ => by simp only [List.flatMap_nil, List.append_nil]; exact .refl _
  | item :: todo, done, typed => by
      have itemTyped : HasType language free bound item (.base rule.category) :=
        CanonicalBags.elementsHaveType_iff.mp typed item (by simp)
      have splicedTyped : ElementsHaveType language free bound (CollectionLaws.splice law item) (.base rule.category) :=
        CanonicalBags.elementsHaveType_iff.mpr
          (splice_base_typed checked found itemTyped)
      have sourceTyped : HasType language free bound (.collection kind (done ++ item :: todo) none)
          (.base rule.category) := .collectionConstructor declaration.authored shape typed
      have sorted : SortedAt language (.collection kind (done ++ item :: todo) none) rule.category :=
        ⟨free, bound, sourceTyped⟩
      have kindEq := lawFor_kind found
      by_cases nested : ∃ items, item = .collection law.kind items none
      · obtain ⟨inner, rfl⟩ := nested
        have first : ReferenceStep.Equivalent relEnv language
            (.collection kind (done ++ .collection law.kind inner none :: todo) none)
            (.collection kind (done ++ inner ++ todo) none) := by
          rw [kindEq] at sorted ⊢
          exact .rel _ _ (.inContext .hole (.inr (.flatten declaration rfl sorted)))
        have inserted : ElementsHaveType language free bound inner (.base rule.category) := by
          simpa only [CollectionLaws.splice, ↓reduceIte] using splicedTyped
        have next := elements_insert_typed typed inserted
        have later := splice_source_equivalent (relEnv := relEnv) checked shape found declaration todo (done ++ inner) next
        simpa [ReferenceStep.Equivalent, CollectionLaws.splice, List.append_assoc] using Relation.EqvGen.trans _ _ _ first later
      · by_cases isUnit : ∃ label, item = .apply label [] ∧ law.unit = some label
        · obtain ⟨label, rfl, unit⟩ := isUnit
          have first : ReferenceStep.Equivalent relEnv language
              (.collection kind (done ++ .apply label [] :: todo) none)
              (.collection kind (done ++ todo) none) :=
            .rel _ _ (.inContext .hole (.inr (.unitElim declaration unit sorted)))
          have inserted : ElementsHaveType language free bound [] (.base rule.category) := .nil _ _
          have next := elements_insert_typed typed inserted
          simp only [List.append_nil] at next
          have later := splice_source_equivalent (relEnv := relEnv) checked shape found declaration todo done next
          simpa [ReferenceStep.Equivalent, CollectionLaws.splice, unit] using Relation.EqvGen.trans _ _ _ first later
        · have regrouped : done ++ item :: todo = (done ++ [item]) ++ todo := by simp
          have later := splice_source_equivalent (relEnv := relEnv) checked shape found declaration todo
            (done ++ [item]) (regrouped ▸ typed)
          simpa [source_splice_other nested isUnit, List.append_assoc] using later

/-- A base-result splicing operation is licensed by its actual algebra row,
including the unit inventory; endpoint typing alone is not that authority. -/
theorem finishAlgebra_source_equivalent
    {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    {rule : GrammarRule} (member : rule ∈ language.terms) {kind : CollType} {parameter : String}
    (shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))])
    {bound : List TypeExpr} {elements : List Pattern}
    (typed : ElementsHaveType language free bound elements (.base rule.category)) :
    ReferenceStep.Equivalent relEnv language (.collection kind elements none)
      (.collection kind (finishAlgebra laws kind elements) none) := by
  unfold finishAlgebra
  cases found : lawFor laws kind with
  | none => exact .refl _
  | some law =>
      have declaration := authorized rule member kind parameter law shape found
      simpa only [List.nil_append] using
        splice_source_equivalent (relEnv := relEnv) checked shape found declaration elements [] typed

/-- Full recursive source soundness for the actual role-aware traversal.
The independent source inventory closes collection tails; constructor slots,
binders and pending substitution scopes retain their real typed contexts.
Direct collection-data roles preserve their outer container. -/
theorem reduceAt_source_equivalent
    {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (domains : List TypeExpr) (pattern : Pattern) :
    ∀ {bound : List TypeExpr} {expected : TypeExpr}, HasType language free bound pattern expected →
      ReferenceStep.SourceCollections language pattern →
      ReferenceStep.Equivalent relEnv language pattern (reduceAt laws domains language free bound pattern expected) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro bound expected typed source; simp only [reduceAt]; exact .refl _
  | hfvar identifier => intro bound expected typed source; simp only [reduceAt]; exact .refl _
  | happly label arguments recurse =>
      intro bound expected typed source
      cases source with
      | apply eligible =>
        rw [reduceAt]
        cases selected : applicationRule? domains language free bound expected label arguments with
        | none => exact .refl _
        | some rule =>
            obtain ⟨_, _, _, _, argumentsTyped⟩ := applicationRule_readout selected
            have compared := reduceArguments_equivalent_of
              (fun argument member _ typed source => recurse argument member typed source) eligible argumentsTyped
            simpa only [List.nil_append] using equivalent_children (.apply label)
              (fun before after => .apply label before .hole after) (fun _ _ _ => rfl) compared []
  | hlambda binder body recurse =>
      intro bound expected typed source
      cases source with
      | lambda eligible =>
        cases typed with
        | lambda bodyTyped =>
            simpa only [reduceAt, OneHoleContext.fill] using
              ReferenceStep.equivalent_fill (.lambda binder .hole) (recurse bodyTyped eligible)
  | hmultiLambda arity binders body recurse =>
      intro bound expected typed source
      cases source with
      | multiLambda eligible =>
        cases typed with
        | multiLambda bodyTyped =>
            simpa only [reduceAt, OneHoleContext.fill] using
              ReferenceStep.equivalent_fill (.multiLambda arity binders .hole) (recurse bodyTyped eligible)
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected typed source
      cases source with
      | subst bodyEligible replacementEligible =>
        rw [reduceAt]
        cases selected : substitutionDomain? domains language free bound expected body replacement with
        | none => exact .refl _
        | some domain =>
            obtain ⟨_, bodyTyped, replacementTyped⟩ := substitutionDomain_readout selected
            have first := ReferenceStep.equivalent_fill (.substBody .hole replacement)
              (bodyIH bodyTyped bodyEligible)
            have second := ReferenceStep.equivalent_fill
              (.substReplacement (reduceAt laws domains language free (domain :: bound) body expected) .hole)
              (replacementIH replacementTyped replacementEligible)
            exact .trans _ _ _ first second
  | hcollection kind elements rest recurse =>
      intro bound expected typed source
      cases source with
      | collection site eligible =>
        rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ |
          ⟨sourceRule, parameter, sourceElement, sourceDeclared, sourceParameters, rfl, sourceItems⟩
        · simp only [reduceAt, ↓reduceIte]
          have compared := reduceElements_equivalent_of
            (fun element member typed source => recurse element member typed source) eligible items
          simpa only [List.nil_append] using equivalent_children
            (fun items => .collection kind items none)
            (fun before after => .collection kind before .hole after none) (fun _ _ _ => rfl) compared []
        · simp only [reduceAt]
          cases selected : collectionRule? domains language free bound (.base sourceRule.category) kind elements none with
          | none => exact .refl _
          | some rule =>
              obtain ⟨element, member, shape, items⟩ := collectionRule_readout selected
              simp only [shape]
              obtain ⟨expectedEq, selectedParameter, parameters⟩ :=
                (bareCollectionElementType?_eq_some_iff _ _ _ _).mp shape
              have compared := reduceElements_equivalent_of
                (fun element member typed source => recurse element member typed source) eligible items
              have first : ReferenceStep.Equivalent relEnv language (.collection kind elements none)
                  (.collection kind (reduceElements laws domains language free bound elements element) none) := by
                simpa only [List.nil_append] using equivalent_children
                  (fun items => .collection kind items none)
                  (fun before after => .collection kind before .hole after none) (fun _ _ _ => rfl) compared []
              cases found : lawFor laws kind with
              | none => simpa only [finishAlgebra, found] using first
              | some law =>
                  have homogeneous := homogeneous_bare_of_checked checked found member parameters
                  rw [homogeneous] at items parameters first ⊢
                  have normalizedItems := reduceElements_hasType_of laws domains language free bound
                    (fun element present typed => reduceAt_hasType checked domains element typed) items
                  have second := finishAlgebra_source_equivalent (relEnv := relEnv) checked authorized member parameters normalizedItems
                  exact .trans _ _ _ first second

#print axioms finishAlgebra_source_equivalent
#print axioms reduceAt_source_equivalent

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.RoleAware

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.RoleAware

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws DerivedContexts GeneralPremise.SchemaTyping
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The caller's actual type occurrences are licensed by declared parameter
positions. This speaks about types and declarations, independently of a
normalizer or any selected output. Vector order needs no equation witness. -/
def SourceTypeOccurrences (language : LanguageDef) (type : TypeExpr) : Prop :=
  ∀ kind element, kind ≠ .vec → CollectionTypeOccurs kind element type →
    ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
      CollectionTypeOccurs kind element parameter.typeExpr

private theorem collectionTypeOccurs_not_base {kind : CollType} {element : TypeExpr} {category : String}
    (impossible : CollectionTypeOccurs kind element (.base category)) : False := by
  cases impossible

theorem SourceTypeOccurrences.base (language : LanguageDef) (category : String) :
    SourceTypeOccurrences language (.base category) := by
  intro kind element unordered impossible
  exact False.elim (collectionTypeOccurs_not_base impossible)

theorem SourceTypeOccurrences.of_parameter {language : LanguageDef} {rule : GrammarRule}
    (declared : rule ∈ language.terms) {parameter : TermParam} (member : parameter ∈ rule.params)
    {expected : TypeExpr} (actual : parameterType? parameter = some expected) :
    SourceTypeOccurrences language expected := by
  intro kind element unordered occurs
  refine ⟨rule, declared, parameter, member, ?_⟩
  cases parameter with
  | simple identifier type =>
      simp only [parameterType?, Option.some.injEq] at actual
      cases actual
      exact occurs
  | abstractionNamed binder identifier type =>
      cases type with
      | base category =>
          simp only [parameterType?, Option.some.injEq] at actual
          cases actual
          cases occurs with
          | domain inner => exact False.elim (collectionTypeOccurs_not_base inner)
          | codomain inner => exact False.elim (collectionTypeOccurs_not_base inner)
      | arrow domain codomain =>
          simp only [parameterType?, Option.some.injEq] at actual
          cases actual
          exact occurs
      | multiBinder inner => simp only [parameterType?] at actual; cases actual
      | collection actualKind inner => simp only [parameterType?] at actual; cases actual
  | multiAbstractionNamed binders identifier type =>
      cases type with
      | base category =>
          simp only [parameterType?, Option.some.injEq] at actual
          cases actual
          cases occurs with
          | domain inner => cases inner with
            | binder impossible => exact False.elim (collectionTypeOccurs_not_base impossible)
          | codomain inner => exact False.elim (collectionTypeOccurs_not_base inner)
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              simp only [parameterType?, Option.some.injEq] at actual
              cases actual
              exact occurs
          | _ => simp only [parameterType?] at actual; cases actual
      | multiBinder inner => simp only [parameterType?] at actual; cases actual
      | collection actualKind inner => simp only [parameterType?] at actual; cases actual

private theorem reduceArguments_sourceCollections_of
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (each : ∀ argument ∈ arguments, ∀ expected, HasType language free bound argument expected →
      ReferenceStep.SourceCollections language argument → SourceTypeOccurrences language expected →
      ReferenceStep.SourceCollections language (reduceAt laws domains language free bound argument expected))
    (roles : ∀ parameter ∈ parameters, ∀ expected, parameterType? parameter = some expected →
      SourceTypeOccurrences language expected)
    (eligible : ∀ argument ∈ arguments, ReferenceStep.SourceCollections language argument)
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    ∀ argument ∈ reduceArguments laws domains language free bound arguments parameters,
      ReferenceStep.SourceCollections language argument := by
  induction arguments generalizing parameters with
  | nil => cases typed; simp only [reduceArguments, List.not_mem_nil, false_implies, implies_true]
  | cons argument arguments recurse =>
      cases typed with
      | cons representation expected head tail =>
        simp only [reduceArguments, expected]
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact each argument (.head _) _ head (eligible argument (.head _)) (roles _ (.head _) _ expected)
        · exact recurse
            (fun other member expected typed source role => each other (.tail _ member) expected typed source role)
            (fun parameter member expected actual => roles parameter (.tail _ member) expected actual)
            (fun other member => eligible other (.tail _ member)) tail value member

private theorem reduceElements_sourceCollections_of
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {expected : TypeExpr}
    (each : ∀ element ∈ elements, HasType language free bound element expected →
      ReferenceStep.SourceCollections language element → SourceTypeOccurrences language expected →
      ReferenceStep.SourceCollections language (reduceAt laws domains language free bound element expected))
    (role : SourceTypeOccurrences language expected)
    (eligible : ∀ element ∈ elements, ReferenceStep.SourceCollections language element)
    (typed : ElementsHaveType language free bound elements expected) :
    ∀ element ∈ reduceElements laws domains language free bound elements expected,
      ReferenceStep.SourceCollections language element := by
  induction elements with
  | nil => simp only [reduceElements, List.not_mem_nil, false_implies, implies_true]
  | cons element elements recurse =>
      cases typed with
      | cons head tail =>
          simp only [reduceElements]
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact each element (.head _) head (eligible element (.head _)) role
          · exact recurse (fun other member typed source role => each other (.tail _ member) typed source role)
              (fun other member => eligible other (.tail _ member)) tail value member

private theorem splice_sourceCollections {language : LanguageDef} (law : Laws) {source : Pattern}
    (eligible : ReferenceStep.SourceCollections language source) :
    ∀ item ∈ splice law source, ReferenceStep.SourceCollections language item := by
  cases source with
  | collection kind elements rest =>
      cases eligible with
      | collection site children =>
          simp only [splice]
          split
          · exact children
          · intro item member; cases List.mem_singleton.mp member; exact .collection site children
  | apply label arguments =>
      cases arguments with
      | nil =>
          simp only [splice]
          split
          · simp
          · intro item member; cases List.mem_singleton.mp member; exact eligible
      | cons head tail =>
          simp only [splice]
          intro item member; cases List.mem_singleton.mp member; exact eligible
  | _ =>
      simp only [splice]
      intro item member; cases List.mem_singleton.mp member; exact eligible

private theorem finishAlgebra_sourceCollections {language : LanguageDef} {laws : List Laws}
    {kind : CollType} {elements : List Pattern}
    (eligible : ∀ item ∈ elements, ReferenceStep.SourceCollections language item) :
    ∀ item ∈ finishAlgebra laws kind elements, ReferenceStep.SourceCollections language item := by
  unfold finishAlgebra
  cases found : lawFor laws kind with
  | none => exact eligible
  | some law =>
      intro item member
      obtain ⟨source, present, inner⟩ := List.mem_flatMap.mp member
      exact splice_sourceCollections law (eligible source present) item inner

/-- Actual output eligibility follows from the caller's declared type roles
and the selected substitution-domain inventory. Those witnesses are retained
through constructors and scope extensions; arbitrary existential source
sorting is not silently reused at a different role. -/
theorem reduceAt_sourceCollections
    {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    (checked : checkBareHomogeneous laws language = true) (domains : List TypeExpr)
    (domainRoles : ∀ domain ∈ domains, SourceTypeOccurrences language domain) (pattern : Pattern) :
    ∀ {bound : List TypeExpr} {expected : TypeExpr}, HasType language free bound pattern expected →
      ReferenceStep.SourceCollections language pattern → SourceTypeOccurrences language expected →
      ReferenceStep.SourceCollections language (reduceAt laws domains language free bound pattern expected) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro bound expected typed source roles; simpa only [reduceAt] using source
  | hfvar identifier => intro bound expected typed source roles; simpa only [reduceAt] using source
  | happly label arguments recurse =>
      intro bound expected typed source roles
      cases source with
      | apply eligible =>
          rw [reduceAt]
          cases selected : applicationRule? domains language free bound expected label arguments with
          | none => exact .apply eligible
          | some rule =>
              obtain ⟨declared, _, _, _, argumentsTyped⟩ := applicationRule_readout selected
              exact .apply (reduceArguments_sourceCollections_of
                (fun argument member expected typed source roles => recurse argument member typed source roles)
                (fun parameter member _ actual => SourceTypeOccurrences.of_parameter declared member actual)
                eligible argumentsTyped)
  | hlambda binder body recurse =>
      intro bound expected typed source roles
      cases source with
      | lambda eligible =>
          cases typed with
          | lambda bodyTyped =>
              simpa only [reduceAt] using ReferenceStep.SourceCollections.lambda
                (recurse bodyTyped eligible (fun kind element unordered occurs =>
                  roles kind element unordered (.codomain occurs)))
  | hmultiLambda arity binders body recurse =>
      intro bound expected typed source roles
      cases source with
      | multiLambda eligible =>
          cases typed with
          | multiLambda bodyTyped =>
              simpa only [reduceAt] using ReferenceStep.SourceCollections.multiLambda
                (recurse bodyTyped eligible (fun kind element unordered occurs =>
                  roles kind element unordered (.codomain occurs)))
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected typed source roles
      cases source with
      | subst bodyEligible replacementEligible =>
          rw [reduceAt]
          cases selected : substitutionDomain? domains language free bound expected body replacement with
          | none => exact .subst bodyEligible replacementEligible
          | some domain =>
              obtain ⟨present, bodyTyped, replacementTyped⟩ := substitutionDomain_readout selected
              exact .subst (bodyIH bodyTyped bodyEligible roles)
                (replacementIH replacementTyped replacementEligible (domainRoles domain present))
  | hcollection kind elements rest recurse =>
      intro bound expected typed source roles
      cases source with
      | collection site eligible =>
          rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ |
            ⟨sourceRule, parameter, sourceElement, sourceDeclared, sourceParameters, rfl, sourceItems⟩
          · simp only [reduceAt, ↓reduceIte]
            have elementRoles : SourceTypeOccurrences language element :=
              fun kind inner unordered occurs => roles kind inner unordered (.element occurs)
            have children := reduceElements_sourceCollections_of
              (fun element member typed source roles => recurse element member typed source roles)
              elementRoles eligible items
            have outputTyped := reduceElements_hasType_of laws domains language free bound
              (fun element present typed => reduceAt_hasType checked domains element typed) items
            apply ReferenceStep.SourceCollections.collection ?_ children
            by_cases vector : kind = .vec
            · exact .inl vector
            · obtain ⟨rule, member, parameter, parameterMember, occurs⟩ := roles kind element vector .here
              exact .inr ⟨rule, member, parameter, parameterMember, element, occurs,
                free, bound, HasType.collection outputTyped⟩
          · simp only [reduceAt]
            cases selected : collectionRule? domains language free bound (.base sourceRule.category) kind elements none with
            | none => exact .collection site eligible
            | some rule =>
                obtain ⟨element, declared, shape, items⟩ := collectionRule_readout selected
                simp only [shape]
                obtain ⟨expectedEq, selectedParameter, parameters⟩ :=
                  (bareCollectionElementType?_eq_some_iff _ _ _ _).mp shape
                have fullParameters := ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2
                have elementRoles : SourceTypeOccurrences language element := by
                  intro innerKind inner unordered occurs
                  exact ⟨rule, declared, .simple selectedParameter (.collection kind element),
                    by simp only [fullParameters, List.mem_singleton], .element occurs⟩
                have children := reduceElements_sourceCollections_of
                  (fun element member typed source roles => recurse element member typed source roles)
                  elementRoles eligible items
                have normalizedItems := reduceElements_hasType_of laws domains language free bound
                  (fun element present typed => reduceAt_hasType checked domains element typed) items
                have outputTyped : ElementsHaveType language free bound
                    (finishAlgebra laws kind (reduceElements laws domains language free bound elements element)) element := by
                  cases found : lawFor laws kind with
                  | none => simpa only [finishAlgebra, found] using normalizedItems
                  | some law =>
                      have homogeneous := homogeneous_bare_of_checked checked found declared parameters
                      rw [homogeneous] at normalizedItems ⊢
                      exact finishAlgebra_base_typed checked normalizedItems
                exact .collection (.inr ⟨rule, declared, .simple selectedParameter (.collection kind element),
                  by simp only [fullParameters, List.mem_singleton], element, .here,
                  free, bound, HasType.collection outputTyped⟩) (finishAlgebra_sourceCollections children)

#print axioms SourceTypeOccurrences.of_parameter
#print axioms reduceAt_sourceCollections

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.RoleAware
