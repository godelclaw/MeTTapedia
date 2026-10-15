import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatch
import Mettapedia.GSLT.LanguageDef.SchemaTyping

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

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
