import Mettapedia.OSLF.MeTTaIL.LawNormalInstantiation

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
