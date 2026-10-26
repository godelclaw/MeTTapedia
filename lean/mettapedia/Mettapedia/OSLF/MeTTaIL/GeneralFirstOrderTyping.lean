import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatch
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.RestAwareChecker
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Sorted readbacks of first-order matches

An ordinary match against a sorted first-order schema assigns every captured
variable its declared type. Constructor selection comes from the actual
validated grammar; no hand-written variable table participates in the law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted

 theorem context_ofList_lookup (context : List (String × TypeExpr)) (name : String) :
    FreeTypeContext.ofList context name = context.lookup name := by
  induction context with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    by_cases same : key = name
    · subst key
      simp [FreeTypeContext.ofList, List.lookup]
    · have tested : (name == key) = false := by simpa using Ne.symm same
      simpa only [FreeTypeContext.ofList, same, if_false, List.lookup, tested] using ih

 theorem merge_members {first second combined : Bindings}
    (merged : mergeBindings first second = some combined) :
    combined ⊆ first ++ second := by
  induction second generalizing first with
  | nil =>
    cases Option.some.inj merged
    exact List.subset_append_left _ _
  | cons pair rest ih =>
    rcases pair with ⟨name, value⟩
    simp only [mergeBindings, List.foldlM_cons] at merged
    cases found : first.find? (fun entry => entry.1 == name) with
    | none =>
      simp only [found] at merged
      have included := ih merged
      intro entry member
      rcases List.mem_append.mp (included member) with earlier | later
      · rcases List.mem_cons.mp earlier with rfl | earlier
        · exact List.mem_append_right _ (List.mem_cons_self ..)
        · exact List.mem_append_left _ earlier
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ later)
    | some entry =>
      simp only [found] at merged
      split at merged
      · have included := ih merged
        intro pair member
        rcases List.mem_append.mp (included member) with earlier | later
        · exact List.mem_append_left _ earlier
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ later)
      · simp at merged

 def CapturesTyped (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (context : List (String × TypeExpr)) (bindings : Bindings) : Prop :=
    ∀ entry ∈ bindings, ∃ expected,
      context.lookup entry.1 = some expected ∧
        OpenPatternWellSorted language free bound expected entry.2

 theorem application_typing {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply label arguments) type) :
    ∃ rule ∈ language.terms, rule.label = label ∧ .base rule.category = type ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  cases typed with
  | constructor declared _ argumentsTyped => exact ⟨_, declared, rfl, rfl, argumentsTyped⟩

mutual
/-- A first-order schema is also an object pattern; its metavariables become
ordinary free names when it is checked in the authored type context. -/
theorem FirstOrder.isObject {pattern : Pattern} (shape : FirstOrder pattern) :
    isObjectPattern pattern = true := by
  cases shape with
  | metavariable name => rfl
  | constructor label arguments shapes => exact firstOrderArguments_isObject shapes
termination_by sizeOf pattern

theorem firstOrderArguments_isObject {patterns : List Pattern}
    (shapes : ∀ pattern ∈ patterns, FirstOrder pattern) :
    isObjectPatternList patterns = true := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
    simp only [isObjectPatternList, Bool.and_eq_true]
    exact ⟨(shapes pattern (List.mem_cons_self ..)).isObject,
      firstOrderArguments_isObject (fun child member => shapes child (List.mem_cons_of_mem _ member))⟩
termination_by sizeOf patterns
end

/-- First-order subjects have one result type in their fixed caller context.
This does not assert type uniqueness for arbitrary unannotated lambdas. -/
theorem FirstOrder.type_unique {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {firstType secondType : TypeExpr}
    (shape : FirstOrder pattern) (valid : language.validate = [])
    (first : HasType language free bound pattern firstType)
    (second : HasType language free bound pattern secondType) : firstType = secondType := by
  cases shape with
  | metavariable name =>
    cases first with
    | fvar firstDeclared =>
      cases second with
      | fvar secondDeclared => exact Option.some.inj (firstDeclared.symm.trans secondDeclared)
  | constructor label arguments _ =>
    exact HasType.apply_type_unique_of_validate_eq_nil valid first second

 theorem capturesTyped_merge {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {first second combined : Bindings}
    (firstTyped : CapturesTyped language free bound context first)
    (secondTyped : CapturesTyped language free bound context second)
    (merged : mergeBindings first second = some combined) :
    CapturesTyped language free bound context combined := by
  intro entry member
  rcases List.mem_append.mp (merge_members merged member) with earlier | later
  · exact firstTyped entry earlier
  · exact secondTyped entry later

mutual
 theorem matching_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)}
    {schema target : Pattern} {type : TypeExpr} {bindings : Bindings}
    (valid : language.validate = []) (shape : FirstOrder schema)
    (matched : MatchRel schema target bindings)
    (schemaTyped : HasType language (FreeTypeContext.ofList context) [] schema type)
    (targetTyped : HasType language free bound target type)
    (canonical : target.hasCanonicalBinderMetadata = true) (object : isObjectPattern target = true) :
    CapturesTyped language free bound context bindings := by
  cases shape with
  | metavariable name =>
    cases matched
    cases schemaTyped with
    | fvar declared =>
      intro entry member
      cases List.mem_singleton.mp member
      exact ⟨type, (context_ofList_lookup context name) ▸ declared,
        targetTyped, canonical, object, targetTyped.isWellScopedAt⟩
  | constructor label arguments shapes =>
    cases matched with
    | apply argumentsMatched _ =>
      obtain ⟨schemaRule, schemaDeclared, schemaLabel, _, schemasTyped⟩ := application_typing schemaTyped
      obtain ⟨targetRule, targetDeclared, targetLabel, _, targetsTyped⟩ := application_typing targetTyped
      have same : schemaRule = targetRule :=
        List.inj_on_of_nodup_map (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
          schemaDeclared targetDeclared (schemaLabel.trans targetLabel.symm)
      subst targetRule
      exact matching_arguments_captures_typed valid shapes argumentsMatched schemasTyped targetsTyped
        canonical object
 termination_by sizeOf schema

 theorem matching_arguments_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)}
    {schemas targets : List Pattern} {parameters : List TermParam} {bindings : Bindings}
    (valid : language.validate = []) (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (matched : MatchArgsRel schemas targets bindings)
    (schemasTyped : ArgumentsHaveTypes language (FreeTypeContext.ofList context) [] schemas parameters)
    (targetsTyped : ArgumentsHaveTypes language free bound targets parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true)
    (objects : isObjectPatternList targets = true) :
    CapturesTyped language free bound context bindings := by
  cases schemas with
  | nil => cases matched; exact fun _ member => False.elim (List.not_mem_nil member)
  | cons schema schemas =>
    cases matched with
    | cons first rest merged =>
      cases schemasTyped with
      | cons _ schemaType headSchema tailSchemas =>
        cases targetsTyped with
        | cons _ targetType headTarget tailTargets =>
          have same := Option.some.inj (schemaType.symm.trans targetType)
          subst same
          simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
          simp only [isObjectPatternList, Bool.and_eq_true] at objects
          exact capturesTyped_merge
            (matching_captures_typed valid (shapes schema (by simp)) first headSchema headTarget
              canonical.1 objects.1)
            (matching_arguments_captures_typed valid
              (fun child member => shapes child (List.mem_cons_of_mem _ member)) rest tailSchemas tailTargets
              canonical.2 objects.2) merged
 termination_by sizeOf schemas
end


/-! ## Retained schema roles for recursive collection matches -/

mutual
/-- On recursive binder-free schemas the premise checker is the existing
rest-aware checker. Their substitution-domain searches are never invoked. -/
theorem binderFree_schema_checker {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {schema : Pattern} {expected : TypeExpr}
    (shape : binderFree schema = true) :
    GeneralPremise.SchemaTyping.checkSchemaType domains language free bound schema expected =
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType language free bound schema expected := by
  cases schema with
  | bvar index => rfl
  | fvar name => rfl
  | apply label schemas =>
    simp only [GeneralPremise.SchemaTyping.checkSchemaType,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType]
    apply List.any_congr rfl
    intro rule
    rw [binderFree_schema_arguments_checker shape]
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | collection kind schemas rest =>
    simp only [GeneralPremise.SchemaTyping.checkSchemaType,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType]
    congr 1
    · cases expected <;> try rfl
      rename_i actual elementType
      dsimp only
      rw [binderFree_schema_elements_checker shape]
      rfl
    · apply List.any_congr rfl
      intro rule
      cases found : bareCollectionElementType? rule kind expected with
      | none => rfl
      | some elementType =>
        dsimp only
        rw [binderFree_schema_elements_checker shape]
        rfl
termination_by sizeOf schema

theorem binderFree_schema_arguments_checker {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {schemas : List Pattern} {parameters : List TermParam}
    (shapes : binderFreeList schemas = true) :
    GeneralPremise.SchemaTyping.checkSchemaArguments domains language free bound schemas parameters =
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaArguments language free bound schemas parameters := by
  cases schemas with
  | nil => cases parameters <;> rfl
  | cons schema schemas =>
    cases parameters with
    | nil => rfl
    | cons parameter parameters =>
      obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
      simp only [GeneralPremise.SchemaTyping.checkSchemaArguments,
        Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaArguments]
      cases found : parameterType? parameter with
      | none => rfl
      | some expected =>
        dsimp only
        rw [binderFree_schema_checker headShape,binderFree_schema_arguments_checker tailShapes]
termination_by sizeOf schemas

theorem binderFree_schema_elements_checker {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {schemas : List Pattern} {expected : TypeExpr}
    (shapes : binderFreeList schemas = true) :
    GeneralPremise.SchemaTyping.checkSchemaElements domains language free bound schemas expected =
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaElements language free bound schemas expected := by
  cases schemas with
  | nil => rfl
  | cons schema schemas =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    simp only [GeneralPremise.SchemaTyping.checkSchemaElements,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaElements]
    rw [binderFree_schema_checker headShape,binderFree_schema_elements_checker tailShapes]
termination_by sizeOf schemas
end

/-- Actual accepted recursive schemas retain the existing declarative typing
of every rest, rather than merely the ordinary element typing projection. -/
theorem binderFree_schema_restAware {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {schema : Pattern} {expected : TypeExpr}
    (shape : binderFree schema = true)
    (checked : GeneralPremise.SchemaTyping.checkSchemaType domains language free bound schema expected = true) :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language free bound schema expected := by
  rw [binderFree_schema_checker shape] at checked
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound checked

#print axioms binderFree_schema_checker
#print axioms binderFree_schema_arguments_checker
#print axioms binderFree_schema_elements_checker
#print axioms binderFree_schema_restAware


private theorem elements_open {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {targets : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType language free bound targets type)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true)
    (objects : isObjectPatternList targets = true) :
    ∀ target ∈ targets,OpenPatternWellSorted language free bound type target := by
  induction targets with
  | nil => intro _ member; cases member
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      simp only [Pattern.hasCanonicalBinderMetadataList,Bool.and_eq_true] at canonical
      simp only [isObjectPatternList,Bool.and_eq_true] at objects
      intro target member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨head,canonical.1,objects.1,head.isWellScopedAt⟩
      · exact ih tail canonical.2 objects.2 target later

private theorem collection_open {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {targets : List Pattern} {type : TypeExpr} (kind : CollType)
    (openTargets : ∀ target ∈ targets,OpenPatternWellSorted language free bound type target) :
    OpenPatternWellSorted language free bound (.collection kind type) (.collection kind targets none) := by
  have parts : ElementsHaveType language free bound targets type ∧
      Pattern.hasCanonicalBinderMetadataList targets = true ∧ isObjectPatternList targets = true := by
    induction targets with
    | nil => exact ⟨.nil _ _,rfl,rfl⟩
    | cons head tail ih =>
      have first := openTargets head (List.mem_cons_self ..)
      obtain ⟨typed,canonical,objects⟩ := ih (fun target member => openTargets target (List.mem_cons_of_mem _ member))
      exact ⟨.cons first.1 typed,by simpa only [Pattern.hasCanonicalBinderMetadataList,first.2.1,Bool.true_and] using canonical,
        by simpa only [isObjectPatternList,first.2.2.1,Bool.true_and] using objects⟩
  have typed := HasType.collection (collectionType := kind) (rest := none) parts.1
  exact ⟨typed,parts.2.1,by simpa only [isObjectPattern,Option.isNone_none,Bool.true_and] using parts.2.2,
    typed.isWellScopedAt⟩

/-- A shared result fibre and the existing declaration-level collection
choice certificate select the same element role in schema and object. -/
theorem recursive_collection_element_roles {language : LanguageDef} {schemaFree targetFree : FreeTypeContext}
    {schemaBound targetBound : List TypeExpr} {kind : CollType} {schemas targets : List Pattern}
    {rest targetRest : Option String} {type : TypeExpr}
    (choices : CollectionChoiceDeterministic language)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      language schemaFree schemaBound (.collection kind schemas rest) type)
    (targetTyped : HasType language targetFree targetBound (.collection kind targets targetRest) type) :
    ∃ elementType,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType language schemaFree schemaBound schemas elementType ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType schemaFree kind elementType rest ∧
      ElementsHaveType language targetFree targetBound targets elementType := by
  cases schemaTyped with
  | collection schemasTyped restTyped =>
    rcases hasType_collection_inversion targetTyped with
      ⟨targetElement,same,targetsTyped⟩ | ⟨targetRule,targetName,targetElement,_,_,impossible,_⟩
    · cases (TypeExpr.collection.inj same).2
      exact ⟨_,schemasTyped,restTyped,targetsTyped⟩
    · cases impossible
  | collectionConstructor schemaMember schemaShape schemasTyped restTyped =>
    rcases hasType_collection_inversion targetTyped with
      ⟨targetElement,impossible,_⟩ | ⟨targetRule,targetName,targetElement,targetMember,targetShape,same,targetsTyped⟩
    · cases impossible
    · have roleSame := choices schemaMember targetMember schemaShape targetShape (TypeExpr.base.inj same)
      subst roleSame
      exact ⟨_,schemasTyped,restTyped,targetsTyped⟩

private theorem rest_capture_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {kind : CollType}
    {elementType : TypeExpr} {name : String} {targets : List Pattern}
    (restTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType
      (FreeTypeContext.ofList context) kind elementType (some name))
    (openTargets : ∀ target ∈ targets,OpenPatternWellSorted language free bound elementType target) :
    CapturesTyped language free bound context [(name,.collection kind targets none)] := by
  intro entry member
  cases List.mem_singleton.mp member
  refine ⟨.collection kind elementType,?_,collection_open kind openTargets⟩
  simpa only [Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType,context_ofList_lookup] using restTyped

mutual
/-- Literal recursive matching preserves the authored type of every capture,
including residual collections. The actual subject supplies object and scope
conditions; rest roles come from the retained schema derivation. -/
theorem matching_recursive_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)}
    {schema target : Pattern} {type : TypeExpr} {bindings : Bindings}
    (valid : language.validate = []) (choices : CollectionChoiceDeterministic language)
    (shape : binderFree schema = true) (matched : MatchRel schema target bindings)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      language (FreeTypeContext.ofList context) [] schema type)
    (targetOpen : OpenPatternWellSorted language free bound type target) :
    CapturesTyped language free bound context bindings := by
  cases schema with
  | fvar name =>
    cases matched
    cases schemaTyped with
    | fvar declared =>
      intro entry member
      cases List.mem_singleton.mp member
      exact ⟨type,(context_ofList_lookup context name) ▸ declared,targetOpen⟩
  | bvar index => cases schemaTyped with | bvar impossible => simp at impossible
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | apply label schemas =>
    cases matched with
    | apply argumentsMatched _ =>
      cases schemaTyped with
      | constructor schemaMember _ schemasTyped =>
        obtain ⟨targetRule,targetMember,targetLabel,_,targetsTyped⟩ := application_typing targetOpen.1
        have same := List.inj_on_of_nodup_map
          (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
          schemaMember targetMember targetLabel.symm
        subst targetRule
        exact matching_recursive_arguments_captures_typed valid choices shape argumentsMatched
          schemasTyped targetsTyped targetOpen.2.1 targetOpen.2.2.1
  | collection kind schemas rest =>
    cases matched with
    | collection _ bagMatched =>
      obtain ⟨elementType,schemasTyped,restTyped,targetsTyped⟩ :=
        recursive_collection_element_roles choices schemaTyped targetOpen.1
      exact matching_recursive_bag_captures_typed valid choices shape bagMatched schemasTyped restTyped
        (elements_open targetsTyped targetOpen.2.1 (Bool.and_eq_true_iff.mp targetOpen.2.2.1).2)
    | vector argumentsMatched =>
      obtain ⟨elementType,schemasTyped,_,targetsTyped⟩ :=
        recursive_collection_element_roles choices schemaTyped targetOpen.1
      exact matching_recursive_elements_captures_typed valid choices shape argumentsMatched schemasTyped
        (elements_open targetsTyped targetOpen.2.1 (Bool.and_eq_true_iff.mp targetOpen.2.2.1).2)
    | vectorRest argumentsMatched merged =>
      obtain ⟨elementType,schemasTyped,restTyped,targetsTyped⟩ :=
        recursive_collection_element_roles choices schemaTyped targetOpen.1
      have openTargets := elements_open targetsTyped targetOpen.2.1 (Bool.and_eq_true_iff.mp targetOpen.2.2.1).2
      exact capturesTyped_merge
        (matching_recursive_elements_captures_typed valid choices shape argumentsMatched schemasTyped
          (fun target member => openTargets target (List.mem_of_mem_take member)))
        (rest_capture_typed restTyped (fun target member => openTargets target (List.mem_of_mem_drop member))) merged
termination_by sizeOf schema

theorem matching_recursive_arguments_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schemas targets : List Pattern}
    {parameters : List TermParam} {bindings : Bindings}
    (valid : language.validate = []) (choices : CollectionChoiceDeterministic language)
    (shapes : binderFreeList schemas = true) (matched : MatchArgsRel schemas targets bindings)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ArgumentsHaveTypes
      language (FreeTypeContext.ofList context) [] schemas parameters)
    (targetsTyped : ArgumentsHaveTypes language free bound targets parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true)
    (objects : isObjectPatternList targets = true) :
    CapturesTyped language free bound context bindings := by
  cases matched with
  | nil => exact fun _ member => False.elim (List.not_mem_nil member)
  | cons head rest merged =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    cases schemasTyped with
    | cons _ schemaType headSchema tailSchemas =>
      cases targetsTyped with
      | cons _ targetType headTarget tailTargets =>
        have same := Option.some.inj (schemaType.symm.trans targetType)
        subst same
        simp only [Pattern.hasCanonicalBinderMetadataList,Bool.and_eq_true] at canonical
        simp only [isObjectPatternList,Bool.and_eq_true] at objects
        exact capturesTyped_merge
          (matching_recursive_captures_typed valid choices headShape head headSchema
            ⟨headTarget,canonical.1,objects.1,headTarget.isWellScopedAt⟩)
          (matching_recursive_arguments_captures_typed valid choices tailShapes rest tailSchemas tailTargets
            canonical.2 objects.2) merged
termination_by sizeOf schemas

theorem matching_recursive_elements_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schemas targets : List Pattern}
    {elementType : TypeExpr} {bindings : Bindings}
    (valid : language.validate = []) (choices : CollectionChoiceDeterministic language)
    (shapes : binderFreeList schemas = true) (matched : MatchArgsRel schemas targets bindings)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType
      language (FreeTypeContext.ofList context) [] schemas elementType)
    (openTargets : ∀ target ∈ targets,OpenPatternWellSorted language free bound elementType target) :
    CapturesTyped language free bound context bindings := by
  cases matched with
  | nil => exact fun _ member => False.elim (List.not_mem_nil member)
  | cons head rest merged =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    cases schemasTyped with
    | cons headSchema tailSchemas =>
      exact capturesTyped_merge
        (matching_recursive_captures_typed valid choices headShape head headSchema
          (openTargets _ (List.mem_cons_self ..)))
        (matching_recursive_elements_captures_typed valid choices tailShapes rest tailSchemas
          (fun target member => openTargets target (List.mem_cons_of_mem _ member))) merged
termination_by sizeOf schemas

theorem matching_recursive_bag_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schemas targets : List Pattern}
    {kind : CollType} {rest : Option String} {elementType : TypeExpr} {bindings : Bindings}
    (valid : language.validate = []) (choices : CollectionChoiceDeterministic language)
    (shapes : binderFreeList schemas = true) (matched : MatchBagRel schemas rest kind targets bindings)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType
      language (FreeTypeContext.ofList context) [] schemas elementType)
    (restTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType
      (FreeTypeContext.ofList context) kind elementType rest)
    (openTargets : ∀ target ∈ targets,OpenPatternWellSorted language free bound elementType target) :
    CapturesTyped language free bound context bindings := by
  cases matched with
  | nilNoRest => exact fun _ member => False.elim (List.not_mem_nil member)
  | nilRest => exact rest_capture_typed restTyped openTargets
  | cons selected within head tail merged =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    cases schemasTyped with
    | cons headSchema tailSchemas =>
      exact capturesTyped_merge
        (matching_recursive_captures_typed valid choices headShape head headSchema
          (openTargets _ (List.getElem_mem within)))
        (matching_recursive_bag_captures_typed valid choices tailShapes tail tailSchemas restTyped
          (fun target member => openTargets target (List.mem_of_mem_eraseIdx member))) merged
termination_by sizeOf schemas
end

#print axioms recursive_collection_element_roles
#print axioms matching_recursive_captures_typed
#print axioms matching_recursive_arguments_captures_typed
#print axioms matching_recursive_elements_captures_typed
#print axioms matching_recursive_bag_captures_typed

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
