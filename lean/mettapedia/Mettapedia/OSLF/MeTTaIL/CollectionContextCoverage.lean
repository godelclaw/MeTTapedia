import Mettapedia.OSLF.MeTTaIL.CollectionContextVariants
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceContextShape

/-!
# Canonical residual coverage for collection occurrences

An original physical occurrence can disappear when a set presentation is
canonicalized. The canonical source still supplies a selected member and a
consume-or-retain residual representing every original remaining context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

open Syntax CanonicalBags DerivedContexts GeneralTypedSites CollectionMatcherCompatibility
open Mettapedia.GSLT.LanguageDef WellSorted GeneralTypedOccurrence

theorem canonical_residual_position {kind : CollType} {items : List Pattern}
    {index : Nat} {item : Pattern} (unordered : kind ≠ .vec)
    (selected : items[index]? = some item) :
    ∃ position residual,
      (arrange kind (items.map canon))[position]? = some (canon item) ∧
      residual ∈ kindResiduals kind (arrange kind (items.map canon)) position ∧
      Presents kind residual ((items.eraseIdx index).map canon) := by
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have value := (List.getElem?_eq_some_iff.mp selected).2
  have member : canon item ∈ arrange kind (items.map canon) :=
    (arrange_mem _).mpr (List.mem_map.mpr ⟨item, List.mem_of_getElem? selected, rfl⟩)
  obtain ⟨position, inRange, atPosition⟩ := List.getElem_of_mem member
  have split : Presents kind (items.map canon) (canon item :: (items.eraseIdx index).map canon) := by
    have permuted := (List.getElem_cons_eraseIdx_perm within).map canon
    rw [value] at permuted
    cases kind with
    | vec => contradiction
    | hashBag => simpa only [Presents, List.map_cons] using permuted.symm
    | hashSet => intro candidate; simpa only [List.map_cons] using permuted.mem_iff.symm
  have before : Presents kind (arrange kind (items.map canon)) (items.map canon) :=
    presents_of_arrange_eq (arrange_eq_of_presents (presents_arrange kind _)).symm
  have reconstruction : Presents kind (arrange kind (items.map canon))
      ((arrange kind (items.map canon))[position] :: (items.eraseIdx index).map canon) := by
    rw [atPosition]
    exact presents_trans before split
  have distinct : kind = .hashSet → (arrange kind (items.map canon)).Nodup := by
    rintro rfl
    exact canonical_set_distinct _
  obtain ⟨residual, chosen, residualSame⟩ :=
    (residuals_present_exact unordered distinct inRange).mpr reconstruction
  exact ⟨position, residual, (List.getElem?_eq_some_iff.mpr ⟨inRange, atPosition⟩), chosen, residualSame⟩

/-- Canonical residual enumeration covers the replacement at any original
physical occurrence, even when set canonicalization collapsed that occurrence
with another. The statement compares every replacement, not just the source. -/
theorem canonical_residual_replacement {kind : CollType} {items : List Pattern}
    {index : Nat} {item : Pattern} (unordered : kind ≠ .vec)
    (selected : items[index]? = some item) :
    ∃ position residual,
      (arrange kind (items.map canon))[position]? = some (canon item) ∧
      residual ∈ kindResiduals kind (arrange kind (items.map canon)) position ∧
      ∀ replacement other, Same replacement other →
        Same (.collection kind (items.take index ++ replacement :: items.drop (index + 1)) none)
          (.collection kind (other :: residual) none) := by
  obtain ⟨position, residual, selected', member, sameResidual⟩ :=
    canonical_residual_position unordered selected
  refine ⟨position, residual, selected', member, ?_⟩
  intro replacement other sameReplacement
  change canon replacement = canon other at sameReplacement
  apply canon_collection_of_presents
  have commutes : Unordered kind = true := by cases kind <;> simp_all [Unordered]
  have rotate : Presents kind
      ((items.take index ++ replacement :: items.drop (index + 1)).map canon)
      (canon replacement :: (items.eraseIdx index).map canon) := by
    simpa only [List.map_cons, List.eraseIdx_eq_take_drop_succ] using
      presents_of_perm commutes (List.perm_middle.map canon)
  have residualCanon := sameResidual.map canon
  simp only [List.map_map, Function.comp_def, canon_idempotent] at residualCanon
  have reverse := presents_of_arrange_eq (arrange_eq_of_presents residualCanon).symm
  have tail := presents_cons reverse (canon replacement)
  rw [sameReplacement] at tail
  exact presents_trans (by simpa only [sameReplacement] using rotate) tail

private theorem collection_variant_member {kind : CollType} {items residual : List Pattern}
    {position : Nat} {inner : SiteData} {variant : OneHoleContext} {origin : TypingFrame}
    (unordered : kind ≠ .vec)
    (selected : items[position]? = some (inner.context.fill inner.focus))
    (nested : variant ∈ contextVariants inner.focus inner.context)
    (chosen : residual ∈ kindResiduals kind items position) :
    .collection kind [] variant residual none ∈
      contextVariants inner.focus (inner.wrapCollection origin kind items position).context := by
  have within := (List.getElem?_eq_some_iff.mp selected).1
  apply List.mem_flatMap.mpr
  refine ⟨variant, nested, ?_⟩
  simp only [unordered, ↓reduceIte]
  apply List.mem_map.mpr
  refine ⟨residual, ?_, rfl⟩
  simpa only [take_selected_drop selected, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt within)] using chosen

/-- Every licensed source occurrence has a finite residual variant over a
licensed occurrence of the canonical source. The comparison preserves every
replacement and all dependent focus/declaration data, including set contexts. -/
theorem licensed_canonical_variant {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    ∃ canonicalSite context,
      Licensed language free permissions bound expected (canon source) canonicalSite ∧
      canonicalSite.focus = canon site.focus ∧
      canonicalSite.focusBound = site.focusBound ∧ canonicalSite.focusType = site.focusType ∧
      canonicalSite.typingFrames = site.typingFrames ∧
      context ∈ contextVariants canonicalSite.focus canonicalSite.context ∧
      ContextShape site.context context ∧
      ∀ replacement other, Same replacement other →
        Same (site.context.fill replacement) (context.fill other) := by
  induction licensed with
  | @here bound expected source enabled object typed =>
    refine ⟨SiteData.here bound expected (canon source), .hole,
      .here enabled (by rw [isObjectPattern_canon]; exact object) (hasType_canon typed),
      rfl, rfl, rfl, rfl, by simp [SiteData.here, contextVariants], .hole, ?_⟩
    intro replacement other same
    exact same
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
    obtain ⟨inner', context, licensed', focus, focusBound, focusType, frames, member, contextShape, compare⟩ := ih
    refine ⟨inner'.wrapApplication declaration rule.label (arguments.map canon) index,
      .apply rule.label ((arguments.take index).map canon) context ((arguments.drop (index + 1)).map canon),
      ?_, focus, focusBound, focusType, ?_, ?_, ?_, ?_⟩
    · rw [canon_apply]
      exact .application declared ordinary (argumentsHaveTypes_canon typed) (isObjectPatternList_canon objects)
        (by simp [List.getElem?_map, selected]) parameterSelected parameterTyped permitted licensed'
    · simp only [SiteData.wrapApplication, frames]
    · simpa only [SiteData.wrapApplication, contextVariants, ← List.map_take, ← List.map_drop] using
        List.mem_map_of_mem (f := fun changed =>
          OneHoleContext.apply rule.label ((arguments.take index).map canon)
            changed ((arguments.drop (index + 1)).map canon)) member
    · exact .application contextShape
    · intro replacement other same
      exact same_apply_congr _ (List.rel_append (forall₂_same_canon _)
        (.cons (compare _ _ same) (forall₂_same_canon _)))
  | @lambda bound binder body domain codomain inner enabled innerLicensed ih =>
    obtain ⟨inner', context, licensed', focus, focusBound, focusType, frames, member, contextShape, compare⟩ := ih
    refine ⟨inner'.wrapLambda binder domain, .lambda binder context, ?_, focus,
      focusBound, focusType, ?_, ?_, ?_, ?_⟩
    · rw [canon]
      exact .lambda enabled licensed'
    · simp only [SiteData.wrapLambda, frames]
    · exact List.mem_map_of_mem member
    · exact .lambda contextShape
    · intro replacement other same
      exact same_lambda_congr binder (compare _ _ same)
  | @multiLambda bound arity binders body domain codomain inner enabled innerLicensed ih =>
    obtain ⟨inner', context, licensed', focus, focusBound, focusType, frames, member, contextShape, compare⟩ := ih
    refine ⟨inner'.wrapMultiLambda arity binders domain, .multiLambda arity binders context,
      ?_, focus, focusBound, focusType, ?_, ?_, ?_, ?_⟩
    · rw [canon]
      exact .multiLambda enabled licensed'
    · simp only [SiteData.wrapMultiLambda, frames]
    · exact List.mem_map_of_mem member
    · exact .multiLambda contextShape
    · intro replacement other same
      exact same_multiLambda_congr arity binders (compare _ _ same)
  | @directCollection bound kind elements index element elementType inner
      permitted typed objects selected innerLicensed ih =>
    obtain ⟨inner', context, licensed', focus, focusBound, focusType, frames, member, contextShape, compare⟩ := ih
    by_cases vector : kind = .vec
    · subst kind
      refine ⟨inner'.wrapCollection (.directCollection .vec) .vec (elements.map canon) index,
        .collection .vec ((elements.take index).map canon) context ((elements.drop (index + 1)).map canon) none,
        ?_, focus, focusBound, focusType, ?_, ?_, ?_, ?_⟩
      · rw [canon_collection, arrange_vec]
        exact .directCollection permitted (by
          simpa only [arrange_vec] using arrange_canon_typed (kind := .vec) typed)
          (isObjectPatternList_canon objects) (by simp [List.getElem?_map, selected]) licensed'
      · simp only [SiteData.wrapCollection, frames]
      · apply List.mem_flatMap.mpr
        exact ⟨context, member, by simp only [↓reduceIte, List.mem_singleton, ← List.map_take, ← List.map_drop]⟩
      · exact .collection contextShape
      · intro replacement other same
        exact same_collection_congr _ _ (List.rel_append (forall₂_same_canon _)
          (.cons (compare _ _ same) (forall₂_same_canon _)))
    · obtain ⟨position, residual, atPosition, chosen, replace⟩ := canonical_residual_replacement vector selected
      refine ⟨inner'.wrapCollection (.directCollection kind) kind (arrange kind (elements.map canon)) position,
        .collection kind [] context residual none, ?_, focus, focusBound, focusType, ?_, ?_, ?_, ?_⟩
      · rw [canon_collection]
        exact .directCollection permitted (arrange_canon_typed typed) (arrange_canon_objects objects)
          atPosition licensed'
      · simp only [SiteData.wrapCollection, frames]
      · apply collection_variant_member vector _ member chosen
        rw [licensed'.source_eq]
        exact atPosition
      · exact .collection contextShape
      · intro replacement other same
        exact replace _ _ (compare _ _ same)
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected innerLicensed ih =>
    obtain ⟨inner', context, licensed', focus, focusBound, focusType, frames, member, contextShape, compare⟩ := ih
    by_cases vector : kind = .vec
    · subst kind
      refine ⟨inner'.wrapCollection (.authoredCollection declaration) .vec (elements.map canon) index,
        .collection .vec ((elements.take index).map canon) context ((elements.drop (index + 1)).map canon) none,
        ?_, focus, focusBound, focusType, ?_, ?_, ?_, ?_⟩
      · rw [canon_collection, arrange_vec]
        exact .authoredCollection declared shape permitted (by
          simpa only [arrange_vec] using arrange_canon_typed (kind := .vec) typed)
          (isObjectPatternList_canon objects) (by simp [List.getElem?_map, selected]) licensed'
      · simp only [SiteData.wrapCollection, frames]
      · apply List.mem_flatMap.mpr
        exact ⟨context, member, by simp only [↓reduceIte, List.mem_singleton, ← List.map_take, ← List.map_drop]⟩
      · exact .collection contextShape
      · intro replacement other same
        exact same_collection_congr _ _ (List.rel_append (forall₂_same_canon _)
          (.cons (compare _ _ same) (forall₂_same_canon _)))
    · obtain ⟨position, residual, atPosition, chosen, replace⟩ := canonical_residual_replacement vector selected
      refine ⟨inner'.wrapCollection (.authoredCollection declaration) kind (arrange kind (elements.map canon)) position,
        .collection kind [] context residual none, ?_, focus, focusBound, focusType, ?_, ?_, ?_, ?_⟩
      · rw [canon_collection]
        exact .authoredCollection declared shape permitted (arrange_canon_typed typed) (arrange_canon_objects objects)
          atPosition licensed'
      · simp only [SiteData.wrapCollection, frames]
      · apply collection_variant_member vector _ member chosen
        rw [licensed'.source_eq]
        exact atPosition
      · exact .collection contextShape
      · intro replacement other same
        exact replace _ _ (compare _ _ same)

end Mettapedia.OSLF.MeTTaIL.CollectionSelection
