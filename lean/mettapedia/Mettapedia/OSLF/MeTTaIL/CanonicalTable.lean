import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
import Mettapedia.OSLF.MeTTaIL.CanonicalCompare
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# The name table of a language

A well-sorted object pattern has no binder names (`hasCanonicalBinderMetadata`), no open collection
tail (`isObjectPattern`), constructors of its language and free names with declared types, so the
constructors and the declared free names cover it (`covered_of_wellSorted`). `nameTable` lists
them once each in the order of their serializations (`nameTable_ordered`), which is what
`CanonicalCompare.cmp` needs to compare covered patterns.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare

open Syntax PatternLexOrder
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## The table -/

/-- Names in the order of their serializations. -/
def NameLe (left right : String) : Prop := strCmp left right ≠ .gt

instance : DecidableRel NameLe := fun left right => inferInstanceAs (Decidable (strCmp left right ≠ .gt))

theorem nameLe_iff {left right : String} : NameLe left right ↔ lexLe (serString left) (serString right) = true := by
  rw [NameLe, lexLe_eq, ← strCmp]
  cases strCmp left right <;> simp

instance : Std.Total NameLe :=
  ⟨fun left right => by
    rw [nameLe_iff, nameLe_iff]
    exact lexLe_total _ _⟩

instance : IsTrans String NameLe :=
  ⟨fun first second third before after => by
    rw [nameLe_iff] at before after ⊢
    exact lexLe_trans _ _ _ before after⟩

/-- Names once each, in the order of their serializations. -/
def nameTable (names : List String) : List String := names.dedup.insertionSort NameLe

theorem mem_nameTable {names : List String} {name : String} : name ∈ nameTable names ↔ name ∈ names := by
  rw [nameTable, (List.perm_insertionSort _ _).mem_iff, List.mem_dedup]

theorem nameTable_ordered (names : List String) : NameOrdered (nameTable names) := by
  have sorted := List.pairwise_insertionSort NameLe names.dedup
  have distinct : (nameTable names).Nodup := (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_dedup names)
  refine (sorted.and distinct).imp ?_
  rintro left right ⟨notGreater, different⟩
  cases ordering : strCmp left right with
  | lt => rfl
  | eq => exact absurd (strCmp_eq_iff.mp ordering) different
  | gt => exact absurd ordering notGreater


/-- The constructors of a language. -/
def labels (language : LanguageDef) : List String := language.terms.map (·.label)

/-! ## Well-sorted patterns are covered -/

theorem ArgumentsHaveTypes.typed_of_mem {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound arguments parameters →
      ∀ argument ∈ arguments, ∃ type, HasType language free bound argument type
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, _, .cons _ _ argumentTyped argumentsTyped, argument, member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, argumentTyped⟩
    · exact ArgumentsHaveTypes.typed_of_mem argumentsTyped argument later

theorem ElementsHaveType.typed_of_mem {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {elementType : TypeExpr} :
    ∀ {elements : List Pattern}, ElementsHaveType language free bound elements elementType →
      ∀ element ∈ elements, HasType language free bound element elementType
  | [], _, _, member => absurd member List.not_mem_nil
  | _ :: _, .cons elementTyped elementsTyped, element, member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact elementTyped
    · exact ElementsHaveType.typed_of_mem elementsTyped element later

theorem isObjectPatternList_mem : ∀ {patterns : List Pattern}, isObjectPatternList patterns = true →
    ∀ pattern ∈ patterns, isObjectPattern pattern = true
  | [], _, _, member => absurd member List.not_mem_nil
  | _ :: _, objects, pattern, member => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    rcases List.mem_cons.mp member with rfl | later
    · exact objects.1
    · exact isObjectPatternList_mem objects.2 pattern later

theorem metadataList_mem : ∀ {patterns : List Pattern}, Pattern.hasCanonicalBinderMetadataList patterns = true →
    ∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true
  | [], _, _, member => absurd member List.not_mem_nil
  | _ :: _, metadata, pattern, member => by
    simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at metadata
    rcases List.mem_cons.mp member with rfl | later
    · exact metadata.1
    · exact metadataList_mem metadata.2 pattern later

/-- Elements each covered: their names are covered. -/
theorem covered_namesList {table : List String} {patterns : List Pattern}
    (each : ∀ pattern ∈ patterns, Covered table pattern) : ∀ name ∈ namesList patterns, name ∈ table :=
  covered_elements.mpr each

theorem HasType.covered {language : LanguageDef} {free : FreeTypeContext} {table : List String}
    (constructors : ∀ rule ∈ language.terms, rule.label ∈ table)
    (declared : ∀ name type, free name = some type → name ∈ table) :
    ∀ (pattern : Pattern) {bound : List TypeExpr} {type : TypeExpr},
      HasType language free bound pattern type → isObjectPattern pattern = true →
      pattern.hasCanonicalBinderMetadata = true → Covered table pattern
  | .bvar _, _, _, _, _, _ => by
    intro name member
    simp [names] at member
  | .fvar name, _, _, typed, _, _ => by
    cases typed with
    | fvar lookup =>
      intro other member
      simp only [names, List.mem_singleton] at member
      subst other
      exact declared name _ lookup
  | .apply label arguments, bound, _, typed, object, metadata => by
    have objects : isObjectPatternList arguments = true := by simpa [isObjectPattern] using object
    have metadatas : Pattern.hasCanonicalBinderMetadataList arguments = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using metadata
    cases typed with
    | constructor ruleMember _ argumentsTyped =>
      have each : ∀ argument ∈ arguments, Covered table argument := fun argument member => by
        obtain ⟨_, argumentTyped⟩ := ArgumentsHaveTypes.typed_of_mem argumentsTyped argument member
        exact HasType.covered constructors declared argument argumentTyped
          (isObjectPatternList_mem objects argument member) (metadataList_mem metadatas argument member)
      intro name member
      simp only [names, List.mem_cons] at member
      rcases member with same | inside
      · rw [same]
        exact constructors _ ruleMember
      · exact covered_namesList each name inside
  | .lambda binder body, _, _, typed, object, metadata => by
    simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, Option.isNone_iff_eq_none] at metadata
    cases typed with
    | lambda bodyTyped =>
      have inner := HasType.covered constructors declared body bodyTyped (by simpa [isObjectPattern] using object)
        metadata.2
      intro name member
      simp only [names, metadata.1, Option.toList_none, List.nil_append] at member
      exact inner name member
  | .multiLambda arity binders body, _, _, typed, object, metadata => by
    simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, List.isEmpty_iff] at metadata
    cases typed with
    | multiLambda bodyTyped =>
      have inner := HasType.covered constructors declared body bodyTyped (by simpa [isObjectPattern] using object)
        metadata.2
      intro name member
      simp only [names, metadata.1, List.nil_append] at member
      exact inner name member
  | .subst _ _, _, _, _, object, _ => by
    simp [isObjectPattern] at object
  | .collection kind elements rest, _, _, typed, object, metadata => by
    have restClosed : rest = none := by
      cases rest <;> simp [isObjectPattern] at object ⊢
    have objects : isObjectPatternList elements = true := by
      subst restClosed
      simpa [isObjectPattern] using object
    have metadatas : Pattern.hasCanonicalBinderMetadataList elements = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using metadata
    have finish : ∀ {elementType : TypeExpr} {bound' : List TypeExpr},
        ElementsHaveType language free bound' elements elementType → Covered table (.collection kind elements rest) := by
      intro elementType bound' elementsTyped
      have each : ∀ element ∈ elements, Covered table element := fun element member =>
        HasType.covered constructors declared element (ElementsHaveType.typed_of_mem elementsTyped element member)
          (isObjectPatternList_mem objects element member) (metadataList_mem metadatas element member)
      intro name member
      simp only [names, restClosed, Option.toList_none, List.append_nil] at member
      exact covered_namesList each name member
    cases typed with
    | collection elementsTyped => exact finish elementsTyped
    | collectionConstructor _ _ elementsTyped => exact finish elementsTyped
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- **A well-sorted object pattern is covered** by any table holding its language's constructors
and its declared free names. -/
theorem covered_of_wellSorted {language : LanguageDef} {free : FreeTypeContext} {table : List String}
    (constructors : ∀ rule ∈ language.terms, rule.label ∈ table)
    (declared : ∀ name type, free name = some type → name ∈ table)
    {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (sorted : OpenPatternWellSorted language free bound type pattern) : Covered table pattern :=
  HasType.covered constructors declared pattern sorted.1 sorted.2.2.1 sorted.2.1

theorem covered_of_checked {language : LanguageDef} {free : FreeTypeContext} {table : List String}
    (constructors : ∀ rule ∈ language.terms, rule.label ∈ table)
    (declared : ∀ name type, free name = some type → name ∈ table)
    {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (checked : checkOpenPatternWellSorted language free bound type pattern = true) : Covered table pattern :=
  covered_of_wellSorted constructors declared (checkOpenPatternWellSorted_sound checked)

/-! ## The standard form adds no name -/

section StandardForm

open CollectionLaws Substitution

theorem names_liftBVars (pattern : Pattern) : ∀ cutoff shift, names (liftBVars cutoff shift pattern) = names pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro cutoff shift
    unfold liftBVars
    split <;> simp [names]
  | hfvar name => intro cutoff shift; simp [liftBVars, names]
  | happly label arguments ih =>
    intro cutoff shift
    have each : namesList (arguments.map (liftBVars cutoff shift)) = namesList arguments := by
      induction arguments with
      | nil => rfl
      | cons first rest restIH =>
        simp only [List.map_cons, namesList]
        rw [ih first (by simp), restIH (fun argument member => ih argument (by simp [member]))]
    simp only [liftBVars, liftBVarsList_eq_map, names, each]
  | hlambda binder body ih => intro cutoff shift; simp [liftBVars, names, ih]
  | hmultiLambda arity binders body ih => intro cutoff shift; simp [liftBVars, names, ih]
  | hsubst body replacement bodyIH replacementIH =>
    intro cutoff shift; simp [liftBVars, names, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    intro cutoff shift
    have each : namesList (elements.map (liftBVars cutoff shift)) = namesList elements := by
      induction elements with
      | nil => rfl
      | cons first others restIH =>
        simp only [List.map_cons, namesList]
        rw [ih first (by simp), restIH (fun element member => ih element (by simp [member]))]
    simp only [liftBVars, liftBVarsList_eq_map, names, each]

theorem namesList_append (left right : List Pattern) : namesList (left ++ right) = namesList left ++ namesList right := by
  induction left with
  | nil => rfl
  | cons first rest ih => simp [namesList, ih]

theorem namesList_flatMap {f : Pattern → List Pattern} {items : List Pattern} {name : String}
    (each : ∀ item ∈ items, ∀ name ∈ namesList (f item), name ∈ names item)
    (member : name ∈ namesList (items.flatMap f)) : name ∈ namesList items := by
  induction items with
  | nil => simp [namesList] at member
  | cons first rest ih =>
    rw [List.flatMap_cons, namesList_append, List.mem_append] at member
    simp only [namesList, List.mem_append]
    rcases member with here | later
    · exact Or.inl (each first (by simp) name here)
    · exact Or.inr (ih (fun item inside => each item (by simp [inside])) later)

theorem namesList_map {f : Pattern → Pattern} {items : List Pattern} {name : String}
    (each : ∀ item ∈ items, ∀ name ∈ names (f item), name ∈ names item)
    (member : name ∈ namesList (items.map f)) : name ∈ namesList items := by
  obtain ⟨changed, changedIn, named⟩ := mem_namesList.mp member
  obtain ⟨item, itemIn, rfl⟩ := List.mem_map.mp changedIn
  exact mem_namesList.mpr ⟨item, itemIn, each item itemIn name named⟩

theorem splice_names_sub (law : Laws) (pattern : Pattern) : ∀ name ∈ namesList (splice law pattern), name ∈ names pattern := by
  intro name member
  unfold splice at member
  split at member
  · split at member
    · simpa [names] using member
    · simpa [namesList] using member
  · split at member
    · simp [namesList] at member
    · simpa [namesList] using member
  · simpa [namesList] using member

theorem names_normalize (laws : List Laws) (pattern : Pattern) : ∀ name ∈ names (normalize laws pattern), name ∈ names pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [normalize, names]
  | hfvar other => simp [normalize]
  | happly label arguments ih =>
    intro name member
    simp only [normalize, names, List.mem_cons] at member ⊢
    rcases member with same | inside
    · exact Or.inl same
    · exact Or.inr (namesList_map (fun argument argumentIn => ih argument argumentIn) inside)
  | hlambda binder body ih =>
    intro name member
    simp only [normalize, names, List.mem_append] at member ⊢
    exact member.imp id (ih name)
  | hmultiLambda arity binders body ih =>
    intro name member
    simp only [normalize, names, List.mem_append] at member ⊢
    exact member.imp id (ih name)
  | hsubst body replacement bodyIH replacementIH =>
    intro name member
    simp only [normalize, names, List.mem_append] at member ⊢
    exact member.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro name member
    rw [normalize] at member
    split at member
    · rename_i law _
      simp only [names, List.mem_append] at member ⊢
      refine member.imp (fun inside => ?_) id
      exact namesList_map (fun element elementIn => ih element elementIn)
        (namesList_flatMap (fun item _ => splice_names_sub law item) inside)
    · simp only [names, List.mem_append] at member ⊢
      exact member.imp (namesList_map (fun element elementIn => ih element elementIn)) id

theorem bodyItems_names_sub (kind : CollType) (body : Pattern) : ∀ name ∈ namesList (bodyItems kind body), name ∈ names body := by
  intro name member
  unfold bodyItems at member
  split at member
  · split at member
    · simpa [names] using member
    · simpa [namesList] using member
  · simpa [namesList] using member

theorem hoist_names_sub (extrusion : Extrusion) :
    ∀ fuel done todo, ∀ name ∈ names (hoist extrusion fuel done todo), name ∈ namesList (done ++ todo)
  | 0, done, todo => by intro name member; simpa [hoist, names] using member
  | fuel + 1, done, [] => by intro name member; simpa [hoist, names] using member
  | fuel + 1, done, item :: todo => by
    intro name member
    have later := hoist_names_sub extrusion fuel
    have generic : ∀ name ∈ names (hoist extrusion fuel (done ++ [item]) todo), name ∈ namesList (done ++ item :: todo) := by
      intro name inside
      have := later _ _ name inside
      simpa [namesList_append, namesList, List.append_assoc] using this
    cases item with
    | apply label arguments =>
      cases arguments with
      | cons first others =>
        cases others with
        | nil =>
          cases first with
          | lambda display body =>
            by_cases same : label = extrusion.binder
            · simp only [hoist, same, if_true, names, namesList, List.mem_cons, List.mem_append,
                List.append_nil] at member
              rw [namesList_append, List.mem_append]
              simp only [namesList, names, List.mem_append, List.mem_cons, List.append_nil]
              rcases member with rfl | binderIn | inside
              · exact Or.inr (Or.inl (Or.inl same.symm))
              · exact Or.inr (Or.inl (Or.inr (Or.inl binderIn)))
              · have hoisted := later _ _ name inside
                rw [namesList_append, List.mem_append, namesList_append, List.mem_append] at hoisted
                rcases hoisted with fromDone | fromBody | fromTodo
                · exact Or.inl (by
                    obtain ⟨changed, changedIn, named⟩ := mem_namesList.mp fromDone
                    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp changedIn
                    exact mem_namesList.mpr ⟨original, originalIn, by rwa [names_liftBVars] at named⟩)
                · exact Or.inr (Or.inl (Or.inr (Or.inr (bodyItems_names_sub _ body name fromBody))))
                · refine Or.inr (Or.inr ?_)
                  obtain ⟨changed, changedIn, named⟩ := mem_namesList.mp fromTodo
                  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp changedIn
                  exact mem_namesList.mpr ⟨original, originalIn, by rwa [names_liftBVars] at named⟩
            · simp only [hoist, same, if_false] at member
              exact generic name member
          | _ => simp only [hoist] at member; exact generic name member
        | cons second more => simp only [hoist] at member; exact generic name member
      | nil => simp only [hoist] at member; exact generic name member
    | _ => simp only [hoist] at member; exact generic name member

theorem names_extrude (extrusions : List Extrusion) (pattern : Pattern) :
    ∀ name ∈ names (extrude extrusions pattern), name ∈ names pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [extrude, names]
  | hfvar other => simp [extrude]
  | happly label arguments ih =>
    intro name member
    simp only [extrude, names, List.mem_cons] at member ⊢
    rcases member with same | inside
    · exact Or.inl same
    · exact Or.inr (namesList_map (fun argument argumentIn => ih argument argumentIn) inside)
  | hlambda binder body ih =>
    intro name member
    simp only [extrude, names, List.mem_append] at member ⊢
    exact member.imp id (ih name)
  | hmultiLambda arity binders body ih =>
    intro name member
    simp only [extrude, names, List.mem_append] at member ⊢
    exact member.imp id (ih name)
  | hsubst body replacement bodyIH replacementIH =>
    intro name member
    simp only [extrude, names, List.mem_append] at member ⊢
    exact member.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro name member
    have inner : ∀ name ∈ namesList (elements.map (extrude extrusions)), name ∈ namesList elements :=
      fun name inside => namesList_map (fun element elementIn => ih element elementIn) inside
    cases rest with
    | some other =>
      rw [extrude] at member
      simp only [names, List.mem_append] at member ⊢
      exact member.imp (inner name) id
    | none =>
      cases found : extrusions.find? (·.kind = kind) with
      | none =>
        rw [extrude] at member
        simp only [found, names, List.mem_append] at member ⊢
        exact member.imp (inner name) id
      | some extrusion =>
        rw [extrude] at member
        simp only [found] at member
        have hoisted := hoist_names_sub extrusion _ [] _ name member
        simp only [List.nil_append] at hoisted
        simp only [names, List.mem_append]
        exact Or.inl (inner name hoisted)

/-- **The standard form adds no name.** -/
theorem names_standardForm (laws : List Laws) (extrusions : List Extrusion) (pattern : Pattern) :
    ∀ name ∈ names (standardForm laws extrusions pattern), name ∈ names pattern :=
  fun name member => names_normalize laws pattern name (names_extrude extrusions _ name member)

theorem covered_standardForm {table : List String} (laws : List Laws) (extrusions : List Extrusion) {pattern : Pattern}
    (covered : Covered table pattern) : Covered table (standardForm laws extrusions pattern) :=
  fun name member => covered name (names_standardForm laws extrusions pattern name member)

end StandardForm

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare


namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet

open Syntax Mettapedia.GSLT.LanguageDef WellSorted

variable {language : LanguageDef} {free : FreeTypeContext} {table : List String}

mutual
theorem pattern_covered {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (metadata : pattern.hasCanonicalBinderMetadata = true)
    (declarations : ∀ rule ∈ language.terms, rule.label ∈ table)
    (freeNames : ∀ name ∈ pattern.freeFvarNames, name ∈ table) :
    Covered table pattern := by
  cases typed with
  | bvar _ => simp [Covered, names]
  | fvar _ => simpa only [Covered, names, Pattern.freeFvarNames] using freeNames
  | constructor declared _ arguments =>
      intro name occurs
      rcases List.mem_cons.mp occurs with rfl | occurs
      · exact declarations _ declared
      · exact arguments_covered arguments metadata declarations
          (by simpa only [Pattern.freeFvarNames] using freeNames) name occurs
  | @lambda bound binder bodyPattern domain codomain body =>
      cases binder with
      | some name => simp [Pattern.hasCanonicalBinderMetadata] at metadata
      | none =>
          simpa only [Covered, names, Option.toList_none, List.nil_append] using
            pattern_covered body
              (by simpa only [Pattern.hasCanonicalBinderMetadata, Option.isNone_none,
                Bool.true_and] using metadata)
              declarations (by simpa only [Pattern.freeFvarNames] using freeNames)
  | multiLambda body =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, List.isEmpty_iff] at metadata
      obtain ⟨rfl, metadata⟩ := metadata
      simpa only [Covered, names, List.nil_append] using
        pattern_covered body metadata declarations (by simpa only [Pattern.freeFvarNames] using freeNames)
  | subst body replacement =>
      simp only [Pattern.freeFvarNames] at freeNames
      obtain ⟨bodyMetadata, replacementMetadata⟩ :=
        (show _ ∧ _ from (by simpa only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] using metadata))
      intro name occurs
      rcases List.mem_append.mp occurs with inBody | inReplacement
      · exact pattern_covered body bodyMetadata declarations
          (fun name member => freeNames name (List.mem_append_left _ member)) name inBody
      · exact pattern_covered replacement replacementMetadata declarations
          (fun name member => freeNames name (List.mem_append_right _ member)) name inReplacement
  | collection elements =>
      simp only [Pattern.freeFvarNames] at freeNames
      intro name occurs
      rcases List.mem_append.mp occurs with inElements | inRest
      · exact elements_covered elements metadata declarations
          (fun name member => freeNames name (List.mem_append_left _ member)) name inElements
      · exact freeNames name (List.mem_append_right _ inRest)
  | collectionConstructor _ _ elements =>
      simp only [Pattern.freeFvarNames] at freeNames
      intro name occurs
      rcases List.mem_append.mp occurs with inElements | inRest
      · exact elements_covered elements metadata declarations
          (fun name member => freeNames name (List.mem_append_left _ member)) name inElements
      · exact freeNames name (List.mem_append_right _ inRest)
termination_by sizeOf pattern

theorem arguments_covered {bound : List TypeExpr} {patterns : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound patterns parameters)
    (metadata : Pattern.hasCanonicalBinderMetadataList patterns = true)
    (declarations : ∀ rule ∈ language.terms, rule.label ∈ table)
    (freeNames : ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, name ∈ table) :
    ∀ name ∈ namesList patterns, name ∈ table := by
  cases typed with
  | nil => simp [namesList]
  | cons _ _ head tail =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at metadata
      obtain ⟨headMetadata, tailMetadata⟩ := metadata
      intro name occurs
      rcases List.mem_append.mp occurs with here | later
      · exact pattern_covered head headMetadata declarations
          (fun name member => freeNames name (List.mem_append_left _ member)) name here
      · exact arguments_covered tail tailMetadata declarations
          (fun name member => freeNames name (List.mem_append_right _ member)) name later
termination_by sizeOf patterns

theorem elements_covered {bound : List TypeExpr} {patterns : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType language free bound patterns elementType)
    (metadata : Pattern.hasCanonicalBinderMetadataList patterns = true)
    (declarations : ∀ rule ∈ language.terms, rule.label ∈ table)
    (freeNames : ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, name ∈ table) :
    ∀ name ∈ namesList patterns, name ∈ table := by
  cases typed with
  | nil => simp [namesList]
  | cons head tail =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at metadata
      obtain ⟨headMetadata, tailMetadata⟩ := metadata
      intro name occurs
      rcases List.mem_append.mp occurs with here | later
      · exact pattern_covered head headMetadata declarations
          (fun name member => freeNames name (List.mem_append_left _ member)) name here
      · exact elements_covered tail tailMetadata declarations
          (fun name member => freeNames name (List.mem_append_right _ member)) name later
termination_by sizeOf patterns
end

theorem wellSorted_covered {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : OpenPatternWellSorted language free bound type pattern)
    (declarations : ∀ rule ∈ language.terms, rule.label ∈ table)
    (freeNames : ∀ name ∈ pattern.freeFvarNames, name ∈ table) :
    Covered table pattern :=
  pattern_covered typed.1 typed.2.1 declarations freeNames

theorem nameless_binder_covered :
    Covered [] (.lambda none (.bvar 0)) := by
  apply pattern_covered (language := LanguageDef.empty "Alphabet")
    (free := fun _ => none) (bound := [])
    (type := .arrow (.base "A") (.base "A"))
    (.lambda (.bvar rfl)) (by rfl)
  · intro rule declared
    cases declared
  · simp [Pattern.freeFvarNames]

theorem named_display_has_type :
    HasType (LanguageDef.empty "Alphabet") (fun _ => none) []
      (.lambda (some "display") (.bvar 0)) (.arrow (.base "A") (.base "A")) :=
  .lambda (.bvar rfl)

theorem named_display_not_covered :
    ¬ Covered [] (.lambda (some "display") (.bvar 0)) := by
  simp [Covered, names]

theorem named_display_not_canonical :
    (.lambda (some "display") (.bvar 0) : Pattern).hasCanonicalBinderMetadata = false := rfl


end Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet

namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

open Syntax RuleBinding ScopedRuleMatching Substitution
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {table : List String}

def AssignmentCovered (table : List String) (assignment : Assignment) : Prop :=
  ∀ entry ∈ assignment, Covered table entry.2.body

def PatternsCovered (table : List String) (patterns : List Pattern) : Prop :=
  ∀ pattern ∈ patterns, Covered table pattern

private theorem covered_bvar (index : Nat) : Covered table (.bvar index) := by
  simp [Covered, names]

private theorem covered_apply {label : String} {arguments : List Pattern} :
    Covered table (.apply label arguments) ↔ label ∈ table ∧ PatternsCovered table arguments := by
  simp only [Covered, names, List.mem_cons, forall_eq_or_imp, mem_namesList]
  constructor
  · rintro ⟨label, rest⟩
    exact ⟨label, fun argument member name occurs => rest name ⟨argument, member, occurs⟩⟩
  · rintro ⟨label, rest⟩
    exact ⟨label, fun name ⟨argument, member, occurs⟩ => rest argument member name occurs⟩

private theorem covered_lambda {display : Option String} {body : Pattern} :
    Covered table (.lambda display body) ↔
      (∀ name ∈ display.toList, name ∈ table) ∧ Covered table body := by
  simp only [Covered, names, List.mem_append]
  constructor
  · intro covered
    exact ⟨fun name member => covered name (.inl member), fun name member => covered name (.inr member)⟩
  · rintro ⟨left, right⟩ name (member | member)
    · exact left name member
    · exact right name member

private theorem covered_multiLambda {arity : Nat} {display : List String} {body : Pattern} :
    Covered table (.multiLambda arity display body) ↔
      (∀ name ∈ display, name ∈ table) ∧ Covered table body := by
  simp only [Covered, names, List.mem_append]
  constructor
  · intro covered
    exact ⟨fun name member => covered name (.inl member), fun name member => covered name (.inr member)⟩
  · rintro ⟨left, right⟩ name (member | member)
    · exact left name member
    · exact right name member

private theorem covered_subst {body replacement : Pattern} :
    Covered table (.subst body replacement) ↔ Covered table body ∧ Covered table replacement := by
  simp only [Covered, names, List.mem_append]
  constructor
  · intro covered
    exact ⟨fun name member => covered name (.inl member), fun name member => covered name (.inr member)⟩
  · rintro ⟨left, right⟩ name (member | member)
    · exact left name member
    · exact right name member

private theorem covered_collection {kind : CollType} {elements : List Pattern} {rest : Option String} :
    Covered table (.collection kind elements rest) ↔
      PatternsCovered table elements ∧ (∀ name ∈ rest.toList, name ∈ table) := by
  constructor
  · intro covered
    exact ⟨covered_elements.mp (fun name occurs => covered name (List.mem_append_left _ occurs)),
      fun name occurs => covered name (List.mem_append_right _ occurs)⟩
  · rintro ⟨elements, rest⟩ name occurs
    rcases List.mem_append.mp occurs with here | later
    · exact covered_elements.mpr elements name here
    · exact rest name later

theorem liftBVars_covered {pattern : Pattern} (covered : Covered table pattern) (cutoff shift : Nat) :
    Covered table (liftBVars cutoff shift pattern) := by
  simpa only [Covered, names_liftBVars] using covered

theorem contextSubstitute_covered {body : Pattern} {assignment : ContextSubstitution.Assignment}
    (covered : Covered table body) (images : ∀ index, Covered table (assignment index)) :
    Covered table (ContextSubstitution.substitute assignment body) := by
  induction body using Pattern.inductionOn generalizing assignment with
  | hbvar index => exact images index
  | hfvar name => exact covered
  | happly label arguments ih =>
      obtain ⟨labelCovered, argumentsCovered⟩ := covered_apply.mp covered
      apply covered_apply.mpr
      refine ⟨labelCovered, ?_⟩
      intro actual member
      simp only [ContextSubstitution.substituteList_eq_map] at member
      obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
      exact ih argument argumentMember (argumentsCovered argument argumentMember) images
  | hlambda display body ih =>
      obtain ⟨displayCovered, bodyCovered⟩ := covered_lambda.mp covered
      apply covered_lambda.mpr
      refine ⟨displayCovered, ih bodyCovered ?_⟩
      intro index
      unfold ContextSubstitution.lift
      split
      · exact covered_bvar _
      · exact liftBVars_covered (images _) _ _
  | hmultiLambda arity display body ih =>
      obtain ⟨displayCovered, bodyCovered⟩ := covered_multiLambda.mp covered
      apply covered_multiLambda.mpr
      refine ⟨displayCovered, ih bodyCovered ?_⟩
      intro index
      unfold ContextSubstitution.lift
      split
      · exact covered_bvar _
      · exact liftBVars_covered (images _) _ _
  | hsubst body replacement bodyIH replacementIH =>
      obtain ⟨bodyCovered, replacementCovered⟩ := covered_subst.mp covered
      apply covered_subst.mpr
      refine ⟨bodyIH bodyCovered ?_, replacementIH replacementCovered images⟩
      intro index
      unfold ContextSubstitution.lift
      split
      · exact covered_bvar _
      · exact liftBVars_covered (images _) _ _
  | hcollection kind elements rest ih =>
      obtain ⟨elementsCovered, restCovered⟩ := covered_collection.mp covered
      apply covered_collection.mpr
      refine ⟨?_, restCovered⟩
      intro actual member
      simp only [ContextSubstitution.substituteList_eq_map] at member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember (elementsCovered element elementMember) images

theorem recoverValue_covered {dependencies : List TypeExpr} {ambient depth : Nat}
    {arguments : List Pattern} {target : Pattern} {value : ContextualValue}
    (covered : Covered table target)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    Covered table value.body := by
  unfold recoverValue? at recovered
  split at recovered <;> try contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, _, recovered⟩ := recovered
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  cases Option.some.inj recovered
  apply contextSubstitute_covered covered
  intro index
  simp only [recoveryAssignment]
  split
  · split <;> exact covered_bvar _
  · exact covered_bvar _

theorem instantiateValue_covered {value : ContextualValue} {ambient depth : Nat}
    {arguments : List Pattern} {actual : Pattern} (stored : Covered table value.body)
    (parameters : PatternsCovered table arguments)
    (instantiated : instantiateValue? value ambient depth arguments = some actual) :
    Covered table actual := by
  unfold instantiateValue? at instantiated
  split at instantiated <;> try contradiction
  split at instantiated <;> try contradiction
  split at instantiated <;> try contradiction
  split at instantiated <;> try contradiction
  dsimp only at instantiated
  split at instantiated <;> try contradiction
  rw [← Option.some.inj instantiated]
  apply contextSubstitute_covered stored
  intro index
  simp only [occurrenceAssignment]
  split
  · unfold List.getD
    cases found : arguments[index]? with
    | none => exact covered_bvar _
    | some argument => exact parameters argument (List.mem_of_getElem? found)
  · exact covered_bvar _

theorem assigned_covered {initial final : Assignment} {name : String} {value : ContextualValue}
    (before : AssignmentCovered table initial) (valueCovered : Covered table value.body)
    (assigned : assign initial name value = some final) : AssignmentCovered table final := by
  unfold assign at assigned
  cases found : lookup initial name with
  | none =>
      simp only [found, Option.some.injEq] at assigned
      subst final
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact valueCovered
      · exact before entry member
  | some previous =>
      simp only [found] at assigned
      split at assigned
      · cases assigned
        exact before
      · cases assigned

theorem capture_covered {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : Assignment} {name : String} {target : Pattern}
    (before : AssignmentCovered table initial) (targetCovered : Covered table target)
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    AssignmentCovered table final := by
  unfold capture? at captured
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, _, arguments, _, value, recovered, assigned⟩ := captured
  exact assigned_covered before (recoverValue_covered targetCovered recovered) assigned

mutual
  theorem matched_covered {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final : Assignment} {schema target : Pattern}
      (before : AssignmentCovered table initial) (targetCovered : Covered table target)
      (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final) :
      AssignmentCovered table final := by
    cases matched with
    | capture captured => exact capture_covered before targetCovered captured
    | bound => exact before
    | constructor arguments => exact matchedArguments_covered before (covered_apply.mp targetCovered).2 arguments
    | binder body => exact matched_covered before (covered_lambda.mp targetCovered).2 body
    | binders body => exact matched_covered before (covered_multiLambda.mp targetCovered).2 body
    | substitution body replacement =>
        exact matched_covered (matched_covered before (covered_subst.mp targetCovered).1 body)
          (covered_subst.mp targetCovered).2 replacement
    | bag _ bag => exact matchedBag_covered before (covered_collection.mp targetCovered).1 bag
    | vector arguments => exact matchedArguments_covered before (covered_collection.mp targetCovered).1 arguments
    | vectorRest arguments captured =>
        have elements := (covered_collection.mp targetCovered).1
        have changed := matchedArguments_covered before
          (fun target member => elements target (List.mem_of_mem_take member)) arguments
        exact capture_covered changed
          (covered_collection.mpr ⟨fun target member => elements target (List.mem_of_mem_drop member),
            by intro name member; cases member⟩) captured

  theorem matchedArguments_covered {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final : Assignment} {schemas targets : List Pattern}
      (before : AssignmentCovered table initial) (targetsCovered : PatternsCovered table targets)
      (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final) :
      AssignmentCovered table final := by
    cases matched with
    | nil => exact before
    | cons head tail =>
        exact matchedArguments_covered
          (matched_covered before (targetsCovered _ List.mem_cons_self) head)
          (fun target member => targetsCovered target (List.mem_cons_of_mem _ member)) tail

  theorem matchedBag_covered {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final : Assignment} {schemas targets : List Pattern}
      {rest : Option String} {kind : CollType}
      (before : AssignmentCovered table initial) (targetsCovered : PatternsCovered table targets)
      (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      AssignmentCovered table final := by
    cases matched with
    | nil => exact before
    | rest captured =>
        exact capture_covered before
          (covered_collection.mpr ⟨targetsCovered, by intro name member; cases member⟩) captured
    | cons selected within head tail =>
        exact matchedBag_covered
          (matched_covered before (targetsCovered _ (List.getElem_mem within)) head)
          (fun target member => targetsCovered target (List.mem_of_mem_eraseIdx member)) tail
end

theorem instantiateBVarAt_covered {body replacement : Pattern} (depth : Nat)
    (bodyCovered : Covered table body) (replacementCovered : Covered table replacement) :
    Covered table (instantiateBVarAt depth replacement body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [instantiateBVarAt]
      split
      · exact covered_bvar _
      · split
        · exact liftBVars_covered replacementCovered _ _
        · exact covered_bvar _
  | hfvar name => simpa only [instantiateBVarAt] using bodyCovered
  | happly constructor arguments ih =>
      rw [instantiateBVarAt]
      obtain ⟨labelCovered, argumentsCovered⟩ := covered_apply.mp bodyCovered
      apply covered_apply.mpr
      refine ⟨labelCovered, ?_⟩
      intro actual member
      obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
      exact ih argument argumentMember depth (argumentsCovered argument argumentMember)
  | hlambda display body ih =>
      rw [instantiateBVarAt]
      obtain ⟨displayCovered, bodyCovered⟩ := covered_lambda.mp bodyCovered
      exact covered_lambda.mpr ⟨displayCovered, ih (depth + 1) bodyCovered⟩
  | hmultiLambda arity display body ih =>
      rw [instantiateBVarAt]
      obtain ⟨displayCovered, bodyCovered⟩ := covered_multiLambda.mp bodyCovered
      exact covered_multiLambda.mpr ⟨displayCovered, ih (depth + arity) bodyCovered⟩
  | hsubst body replacement bodyIH replacementIH =>
      rw [instantiateBVarAt]
      obtain ⟨bodyCovered, nestedCovered⟩ := covered_subst.mp bodyCovered
      exact covered_subst.mpr ⟨bodyIH (depth + 1) bodyCovered, replacementIH depth nestedCovered⟩
  | hcollection kind elements rest ih =>
      rw [instantiateBVarAt]
      obtain ⟨elementsCovered, restCovered⟩ := covered_collection.mp bodyCovered
      apply covered_collection.mpr
      refine ⟨?_, restCovered⟩
      intro actual member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember depth (elementsCovered element elementMember)

mutual
  theorem instantiateWith_covered
      {operation : Pattern → Pattern → Pattern} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
      {assignment : Assignment} {schema actual : Pattern}
      (operationCovered : ∀ replacement body, Covered table replacement → Covered table body →
        Covered table (operation replacement body))
      (stored : AssignmentCovered table assignment)
      (parameters : ∀ name site path arguments, arguments? rule spec name site path = some arguments →
        PatternsCovered table arguments)
      (schemaCovered : Covered table schema)
      (read : instantiateWith? operation rule spec ambient site path depth assignment schema = some actual) :
      Covered table actual := by
    cases schema with
    | bvar index =>
        simp only [instantiateWith?, Option.some.injEq] at read
        cases read
        exact covered_bvar _
    | fvar name =>
        simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨value, found, arguments, argumentLookup, instantiated⟩ := read
        exact instantiateValue_covered (stored _ (lookup_member assignment name value found))
          (parameters name site path arguments argumentLookup) instantiated
    | apply label arguments =>
        obtain ⟨labelCovered, argumentsCovered⟩ := covered_apply.mp schemaCovered
        simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨results, completed, read⟩ := read
        cases Option.some.inj read
        exact covered_apply.mpr ⟨labelCovered,
          instantiateArgsWith_covered operationCovered stored parameters argumentsCovered completed⟩
    | lambda display body =>
        obtain ⟨displayCovered, bodyCovered⟩ := covered_lambda.mp schemaCovered
        simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨result, completed, read⟩ := read
        cases Option.some.inj read
        exact covered_lambda.mpr ⟨displayCovered,
          instantiateWith_covered operationCovered stored parameters bodyCovered completed⟩
    | multiLambda arity display body =>
        obtain ⟨displayCovered, bodyCovered⟩ := covered_multiLambda.mp schemaCovered
        simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨result, completed, read⟩ := read
        cases Option.some.inj read
        exact covered_multiLambda.mpr ⟨displayCovered,
          instantiateWith_covered operationCovered stored parameters bodyCovered completed⟩
    | subst body replacement =>
        obtain ⟨bodyCovered, replacementCovered⟩ := covered_subst.mp schemaCovered
        simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨bodyResult, bodyRead, replacementResult, replacementRead, read⟩ := read
        cases Option.some.inj read
        exact operationCovered _ _
          (instantiateWith_covered operationCovered stored parameters replacementCovered replacementRead)
          (instantiateWith_covered operationCovered stored parameters bodyCovered bodyRead)
    | collection kind elements rest =>
        obtain ⟨elementsCovered, _⟩ := covered_collection.mp schemaCovered
        simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨explicit, completed, read⟩ := read
        have explicitCovered := instantiateArgsWith_covered operationCovered stored parameters elementsCovered completed
        cases rest with
        | none =>
            cases Option.some.inj read
            exact covered_collection.mpr ⟨explicitCovered, by intro name member; cases member⟩
        | some name =>
            simp only [Option.bind_eq_some_iff] at read
            obtain ⟨value, found, arguments, argumentLookup, resolved, instantiated, read⟩ := read
            have resolvedCovered := instantiateValue_covered (stored _ (lookup_member assignment name value found))
              (parameters name site (path ++ [elements.length]) arguments argumentLookup) instantiated
            split at read <;> try cases read
            split at read <;> cases read
            apply covered_collection.mpr
            constructor
            · intro element member
              rcases List.mem_append.mp member with earlier | later
              · exact explicitCovered element earlier
              · exact (covered_collection.mp resolvedCovered).1 element later
            · intro name member
              cases member
  termination_by sizeOf schema

  theorem instantiateArgsWith_covered
      {operation : Pattern → Pattern → Pattern} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {assignment : Assignment} {schemas actuals : List Pattern}
      (operationCovered : ∀ replacement body, Covered table replacement → Covered table body →
        Covered table (operation replacement body))
      (stored : AssignmentCovered table assignment)
      (parameters : ∀ name site path arguments, arguments? rule spec name site path = some arguments →
        PatternsCovered table arguments)
      (schemasCovered : PatternsCovered table schemas)
      (read : instantiateArgsWith? operation rule spec ambient site path depth assignment index schemas = some actuals) :
      PatternsCovered table actuals := by
    cases schemas with
    | nil =>
        simp only [instantiateArgsWith?, Option.some.injEq] at read
        cases read
        intro actual member
        cases member
    | cons schema schemas =>
        simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
        obtain ⟨actual, head, tail, tailRead, read⟩ := read
        cases Option.some.inj read
        intro value member
        rcases List.mem_cons.mp member with rfl | later
        · exact instantiateWith_covered operationCovered stored parameters
            (schemasCovered schema List.mem_cons_self) head
        · exact instantiateArgsWith_covered operationCovered stored parameters
            (fun value member => schemasCovered value (List.mem_cons_of_mem _ member)) tailRead value later
  termination_by sizeOf schemas
end

def SpecificationCovered (table : List String) (spec : RuleBindingSpec) : Prop :=
  ∀ occurrence ∈ spec.occurrences, PatternsCovered table occurrence.arguments

theorem arguments_covered {rule : RewriteRule} {spec : RuleBindingSpec}
    (spines : SpecificationCovered table spec) {name : String} {site : RulePatternSite}
    {path : List Nat} {arguments : List Pattern}
    (read : arguments? rule spec name site path = some arguments) : PatternsCovered table arguments := by
  unfold arguments? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨dependencies, _, guard, _, read⟩ := read
  split at read
  · split at read <;> cases read
    intro value member
    cases member
  · rename_i row rows
    split at read <;> cases read
    have selected : row ∈ spec.occurrences.filter
        (fun candidate => candidate.name == name && candidate.site == site && candidate.path == path) := by
      rw [rows]
      exact List.mem_cons_self
    exact spines row (List.mem_filter.mp selected).1
  · cases read

theorem instantiateAt_covered {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : Assignment} {schema actual : Pattern}
    (stored : AssignmentCovered table assignment) (spines : SpecificationCovered table spec)
    (schemaCovered : Covered table schema)
    (read : instantiateAt? rule spec ambient site path depth assignment schema = some actual) :
    Covered table actual :=
  instantiateWith_covered (fun _replacement _body replacementCovered bodyCovered =>
    instantiateBVarAt_covered 0 bodyCovered replacementCovered) stored
    (fun _ _ _ _ read => arguments_covered spines read) schemaCovered read

theorem canon_names_membership (pattern : Pattern) :
    ∀ name, name ∈ names (CanonicalBags.canon pattern) ↔ name ∈ names pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [CanonicalBags.canon, names]
  | hfvar other => simp [CanonicalBags.canon]
  | happly label arguments ih =>
      intro name
      simp only [CanonicalBags.canon, names, List.mem_cons, mem_namesList]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨actual, member, occurs⟩
        obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
        exact ⟨argument, argumentMember, (ih argument argumentMember name).mp occurs⟩
      · rintro ⟨argument, argumentMember, occurs⟩
        exact ⟨CanonicalBags.canon argument, List.mem_map.mpr ⟨argument, argumentMember, rfl⟩,
          (ih argument argumentMember name).mpr occurs⟩
  | hlambda display body ih =>
      intro name
      simp only [CanonicalBags.canon, names, List.mem_append, ih]
  | hmultiLambda arity display body ih =>
      intro name
      simp only [CanonicalBags.canon, names, List.mem_append, ih]
  | hsubst body replacement bodyIH replacementIH =>
      intro name
      simp only [CanonicalBags.canon, names, List.mem_append, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
      intro name
      simp only [CanonicalBags.canon, names, List.mem_append, mem_namesList]
      apply or_congr _ Iff.rfl
      constructor
      · rintro ⟨actual, member, occurs⟩
        obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp ((CanonicalBags.arrange_mem actual).mp member)
        exact ⟨element, elementMember, (ih element elementMember name).mp occurs⟩
      · rintro ⟨element, elementMember, occurs⟩
        exact ⟨CanonicalBags.canon element,
          (CanonicalBags.arrange_mem _).mpr (List.mem_map.mpr ⟨element, elementMember, rfl⟩),
          (ih element elementMember name).mpr occurs⟩

theorem canon_covered {pattern : Pattern} (covered : Covered table pattern) :
    Covered table (CanonicalBags.canon pattern) :=
  fun name member => covered name ((canon_names_membership pattern name).mp member)

theorem same_covered {left right : Pattern} (same : CanonicalBags.Same left right)
    (covered : Covered table left) : Covered table right := by
  intro name member
  have occurs := (canon_names_membership right name).mpr member
  rw [← same] at occurs
  exact covered name ((canon_names_membership left name).mp occurs)

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

open Syntax RuleBinding

/-- Root-input inference publishes no explicit occurrence arguments. -/
theorem inferred_specification_covered (table : List String) (rule : RewriteRule) :
    SpecificationCovered table (GeneralRuleBindingInference.inferredSpec rule) := by
  intro occurrence member
  cases member

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

open Syntax RuleBinding

theorem named_display_covered : Covered ["display"] (.lambda (some "display") (.bvar 0)) := by
  simp [Covered, names]

/-- Occurrence arguments can introduce constructor names even when the stored body has none. -/
theorem instantiated_spine_adds_label :
    instantiateValue? ⟨[.base "A"], 0, .bvar 0⟩ 0 0 [.apply "Injected" []] =
      some (.apply "Injected" []) := by rfl

theorem instantiated_label_has_no_free_names :
    (.apply "Injected" [] : Pattern).freeFvarNames = [] := by simp [Pattern.freeFvarNames]

theorem stored_body_alone_does_not_cover_instantiation :
    ∃ value : ContextualValue, ∃ arguments : List Pattern, ∃ actual : Pattern,
      Covered [] value.body ∧ instantiateValue? value 0 0 arguments = some actual ∧
      actual.freeFvarNames = [] ∧ ¬ Covered [] actual := by
  refine ⟨⟨[.base "A"], 0, .bvar 0⟩, [.apply "Injected" []], .apply "Injected" [],
    by simp [Covered, names], instantiated_spine_adds_label, instantiated_label_has_no_free_names, ?_⟩
  intro covered
  exact List.not_mem_nil (covered "Injected" (by simp [names]))

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.pattern_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.arguments_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.elements_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.wellSorted_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.nameless_binder_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.named_display_has_type
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.named_display_not_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.TypedObjectAlphabet.named_display_not_canonical
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.AssignmentCovered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.PatternsCovered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.liftBVars_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.contextSubstitute_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.recoverValue_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiateValue_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.assigned_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.capture_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.matched_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.matchedArguments_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.matchedBag_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiateBVarAt_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiateWith_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiateArgsWith_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.SpecificationCovered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.arguments_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiateAt_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.canon_names_membership
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.canon_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.same_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.inferred_specification_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.named_display_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiated_spine_adds_label
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.instantiated_label_has_no_free_names
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.stored_body_alone_does_not_cover_instantiation
