import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping

/-!
# First-order rule substitution preserves the declared object carrier

The theorem transports a schema in its authored variable context to an
arbitrary typed caller context. The actual captured values provide both
sorting and representation evidence, including any binders inside values.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted

 theorem substituted_representation {parameter : TermParam} {schema : Pattern} {environment : Bindings}
    (shape : FirstOrder schema) (represented : MatchesParameterRepresentation parameter schema) :
    MatchesParameterRepresentation parameter (applyBindings environment schema) := by
  cases parameter with
  | simple => trivial
  | abstractionNamed => cases shape <;> simp [MatchesParameterRepresentation] at represented
  | multiAbstractionNamed => cases shape <;> simp [MatchesParameterRepresentation] at represented

mutual
 theorem substituted_open {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schema : Pattern} {type : TypeExpr}
    {environment : Bindings} (shape : FirstOrder schema)
    (schemaTyped : HasType language (FreeTypeContext.ofList context) [] schema type)
    (defined : Defined environment schema.freeFvarNames)
    (typed : CapturesTyped language free bound context environment) :
    OpenPatternWellSorted language free bound type (applyBindings environment schema) := by
  cases shape with
  | metavariable name =>
    cases schemaTyped with
    | fvar declared =>
      obtain ⟨body, read⟩ := defined name (by simp [Pattern.freeFvarNames])
      obtain ⟨expected, assigned, sorted⟩ := typed (name, body) (by
        unfold Bindings.lookup at read
        obtain ⟨entry, selected, equal⟩ := Option.map_eq_some_iff.mp read
        have key : entry.1 = name := beq_iff_eq.mp
          (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) selected)
        rcases entry with ⟨keyName, value⟩
        dsimp only at key equal
        subst keyName
        subst value
        exact List.mem_of_find?_eq_some selected)
      have same := Option.some.inj (((context_ofList_lookup context name) ▸ declared).symm.trans assigned)
      subst expected
      simpa only [apply_variable, read, Option.getD_some] using sorted
  | constructor label arguments shapes =>
    cases schemaTyped with
    | constructor declared ordinary argumentsTyped =>
      obtain ⟨transformed, canonical, objects⟩ := substituted_arguments shapes argumentsTyped
        (by simpa only [Pattern.freeFvarNames] using defined) typed
      have sorted := HasType.constructor declared ordinary transformed
      simp only [OpenPatternWellSorted, applyBindings, Pattern.hasCanonicalBinderMetadata, isObjectPattern]
      exact ⟨sorted, canonical, objects, sorted.isWellScopedAt⟩
 termination_by sizeOf schema

 theorem substituted_arguments {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)}
    {schemas : List Pattern} {parameters : List TermParam} {environment : Bindings}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (schemasTyped : ArgumentsHaveTypes language (FreeTypeContext.ofList context) [] schemas parameters)
    (defined : Defined environment (schemas.flatMap Pattern.freeFvarNames))
    (typed : CapturesTyped language free bound context environment) :
    ArgumentsHaveTypes language free bound (schemas.map (applyBindings environment)) parameters ∧
      Pattern.hasCanonicalBinderMetadataList (schemas.map (applyBindings environment)) = true ∧
      isObjectPatternList (schemas.map (applyBindings environment)) = true := by
  cases schemas with
  | nil => cases schemasTyped; exact ⟨.nil, rfl, rfl⟩
  | cons schema schemas =>
    cases schemasTyped with
    | cons represented expected headTyped tailTyped =>
      have head := substituted_open (shapes schema (by simp)) headTyped
        (fun name member => defined name (by simp [member])) typed
      obtain ⟨rest, canonical, objects⟩ := substituted_arguments
        (fun child member => shapes child (List.mem_cons_of_mem _ member)) tailTyped
        (fun name member => defined name (by simp [member])) typed
      exact ⟨.cons (substituted_representation (shapes schema (by simp)) represented) expected head.1 rest,
        by simp only [List.map_cons, Pattern.hasCanonicalBinderMetadataList, head.2.1, canonical, Bool.true_and],
        by simp only [List.map_cons, isObjectPatternList, head.2.2.1, objects, Bool.true_and]⟩
 termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
