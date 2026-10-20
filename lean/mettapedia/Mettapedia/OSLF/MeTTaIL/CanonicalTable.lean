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
