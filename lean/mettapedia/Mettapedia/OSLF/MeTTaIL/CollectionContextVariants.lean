import Mettapedia.OSLF.MeTTaIL.CollectionSelectionSites
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator
import Mathlib.Data.List.Forall2

/-!
# Finite residual variants of existing occurrence contexts

The typed occurrence generator determines the permitted hole and all binder
and constructor frames. This operation varies only the residual choices at
unordered collection frames, using the existing finite selector. A retained
set copy contains the original focused subterm. It is not a second hole.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

open Syntax CanonicalBags DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef WellSorted GeneralTypedOccurrence

theorem kindResiduals_sound {kind : CollType} {items residual : List Pattern} {selected : Nat}
    (unordered : kind ≠ .vec) (within : selected < items.length)
    (member : residual ∈ kindResiduals kind items selected) :
    Presents kind items (items[selected] :: residual) := by
  cases kind with
  | vec => contradiction
  | hashBag => exact (bag_residuals_exact within).mp ⟨residual, member, List.Perm.refl _⟩
  | hashSet => exact set_residuals_sound within member

def contextVariants (focus : Pattern) : OneHoleContext → List OneHoleContext
  | .hole => [.hole]
  | .apply label before inner after =>
      (contextVariants focus inner).map (.apply label before · after)
  | .lambda display inner => (contextVariants focus inner).map (.lambda display)
  | .multiLambda arity displays inner =>
      (contextVariants focus inner).map (.multiLambda arity displays)
  | .substBody inner replacement =>
      (contextVariants focus inner).map (.substBody · replacement)
  | .substReplacement body inner =>
      (contextVariants focus inner).map (.substReplacement body)
  | .collection kind before inner after rest =>
      (contextVariants focus inner).flatMap fun changed =>
        if kind = .vec then [.collection kind before changed after rest]
        else (kindResiduals kind (before ++ inner.fill focus :: after) before.length).map
          (fun residual => .collection kind [] changed residual rest)

theorem contextVariants_source (focus : Pattern) (context : OneHoleContext)
    {changed : OneHoleContext} (member : changed ∈ contextVariants focus context) :
    Same (context.fill focus) (changed.fill focus) := by
  induction context generalizing changed with
  | hole =>
    have same : changed = .hole := by simpa [contextVariants] using member
    subst changed
    rfl
  | apply label before inner after ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact same_apply_congr _ (List.rel_append
      (forall₂_same_of_map rfl) (.cons (ih innerMember) (forall₂_same_of_map rfl)))
  | lambda display inner ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact same_lambda_congr _ (ih innerMember)
  | multiLambda arity displays inner ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact same_multiLambda_congr _ _ (ih innerMember)
  | substBody inner replacement ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact same_subst_congr (ih innerMember) rfl
  | substReplacement body inner ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact same_subst_congr rfl (ih innerMember)
  | collection kind before inner after rest ih =>
    obtain ⟨variant, innerMember, member⟩ := List.mem_flatMap.mp member
    by_cases vector : kind = .vec
    · subst kind
      simp only [↓reduceIte, List.mem_singleton] at member
      subst changed
      exact same_collection_congr _ _ (List.rel_append
        (forall₂_same_of_map rfl) (.cons (ih innerMember) (forall₂_same_of_map rfl)))
    · simp only [vector, ↓reduceIte] at member
      obtain ⟨residual, selected, rfl⟩ := List.mem_map.mp member
      have within : before.length < (before ++ inner.fill focus :: after).length := by simp
      have reconstructs := kindResiduals_sound vector within selected
      have focused : (before ++ inner.fill focus :: after)[before.length] = inner.fill focus := by simp
      rw [focused] at reconstructs
      exact (canon_collection_of_presents kind rest (reconstructs.map canon)).trans
        (same_collection_congr kind rest (.cons (ih innerMember) (forall₂_same_of_map rfl)))

/-- Collection residual choices never change the binders crossed by the
distinguished hole. The copies in residuals are ordinary fixed payload. -/
theorem contextVariants_binders (focus : Pattern) (context : OneHoleContext)
    {changed : OneHoleContext} (member : changed ∈ contextVariants focus context) :
    OccurrenceZipperAddress.binderCount changed = OccurrenceZipperAddress.binderCount context := by
  induction context generalizing changed with
  | hole =>
    have same : changed = .hole := by simpa [contextVariants] using member
    subst changed
    rfl
  | apply label before inner after ih
  | lambda display inner ih
  | multiLambda arity displays inner ih
  | substBody inner replacement ih
  | substReplacement body inner ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    simp only [OccurrenceZipperAddress.binderCount, ih innerMember]
  | collection kind before inner after rest ih =>
    obtain ⟨variant, innerMember, member⟩ := List.mem_flatMap.mp member
    split at member
    · have same := List.mem_singleton.mp member
      subst changed
      simpa only [OccurrenceZipperAddress.binderCount] using (ih (changed := variant) innerMember)
    · obtain ⟨residual, _, rfl⟩ := List.mem_map.mp member
      simpa only [OccurrenceZipperAddress.binderCount] using (ih (changed := variant) innerMember)

/-- Change the context while retaining the exact focus typing and declaration
frames. The new address is computed from the reconstructed context. -/
def recontext (site : SiteData) (context : OneHoleContext) : SiteData :=
  { site with context, address := contextAddress context }

private theorem arguments_same {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments others : List Pattern} {parameters : List TermParam}
    (same : List.Forall₂ Same arguments others)
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    ArgumentsHaveTypes language free bound others parameters := by
  induction same generalizing parameters with
  | nil => cases typed; exact .nil
  | cons equal rest ih =>
    cases typed with
    | cons representation parameterType head tail =>
      apply ArgumentsHaveTypes.cons _ parameterType
        (hasType_of_chain (eqvGen_reflTransGen ((same_iff _ _).mp equal)) head) (ih tail)
      apply (matchesParameterRepresentation?_eq_true_iff _ _).mp
      rw [← matchesParameterRepresentation?_same _ equal]
      exact (matchesParameterRepresentation?_eq_true_iff _ _).mpr representation

private theorem objects_same {arguments others : List Pattern}
    (same : List.Forall₂ Same arguments others)
    (objects : isObjectPatternList arguments = true) :
    isObjectPatternList others = true := by
  induction same with
  | nil => rfl
  | @cons first second _ _ equal rest ih =>
    simp only [isObjectPatternList, Bool.and_eq_true] at objects ⊢
    refine ⟨?_, ih objects.2⟩
    rw [← isObjectPattern_canon second, ← equal, isObjectPattern_canon first]
    exact objects.1

private theorem replace_same {elements : List Pattern} {index : Nat} {element replacement : Pattern}
    (selected : elements[index]? = some element) (same : Same element replacement) :
    List.Forall₂ Same elements
      (elements.take index ++ replacement :: elements.drop (index + 1)) := by
  conv_lhs => rw [← take_selected_drop selected]
  exact List.rel_append (forall₂_same_of_map rfl) (.cons same (forall₂_same_of_map rfl))

private theorem splice_position {α : Type} {items : List α} {index : Nat} {item : α}
    (within : index < items.length) :
    (items.take index ++ item :: items.drop (index + 1))[index]? = some item := by
  rw [List.getElem?_append_right]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt within)]
  · simp [List.length_take]

private theorem splice_take {α : Type} {items : List α} {index : Nat} {item : α}
    (within : index < items.length) :
    (items.take index ++ item :: items.drop (index + 1)).take index = items.take index := by
  rw [List.take_append_of_le_length]
  · simp
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt within)]

private theorem splice_drop {α : Type} {items : List α} {index : Nat} {item : α}
    (within : index < items.length) :
    (items.take index ++ item :: items.drop (index + 1)).drop (index + 1) = items.drop (index + 1) := by
  simp [List.drop_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt within)]

/-- Every generated residual variant is a licensed occurrence in its source
presentation, with the original dependent focus and declaration frames. -/
theorem contextVariants_licensed {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    {context : OneHoleContext} (member : context ∈ contextVariants site.focus site.context) :
    Licensed language free permissions bound expected (context.fill site.focus) (recontext site context) := by
  induction licensed generalizing context with
  | here enabled object typed =>
    have same : context = .hole := by simpa [SiteData.here, contextVariants] using member
    subst context
    exact .here enabled object typed
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    have innerNew := ih innerMember
    have equal : Same argument (variant.fill inner.focus) := by
      rw [← innerLicensed.source_eq]
      exact contextVariants_source _ _ innerMember
    have relation := replace_same selected equal
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have next := Licensed.application declared ordinary (arguments_same relation typed)
      (objects_same relation objects) (splice_position within)
      parameterSelected parameterTyped permitted innerNew
    simpa only [SiteData.wrapApplication, recontext, OneHoleContext.fill, contextAddress,
      splice_take within, splice_drop within, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt within)] using next
  | lambda permitted innerLicensed ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact .lambda permitted (ih innerMember)
  | multiLambda permitted innerLicensed ih =>
    obtain ⟨variant, innerMember, rfl⟩ := List.mem_map.mp member
    exact .multiLambda permitted (ih innerMember)
  | @directCollection bound kind elements index element elementType inner
      permitted typed objects selected innerLicensed ih =>
    obtain ⟨variant, innerMember, chosen⟩ := List.mem_flatMap.mp member
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have innerNew := ih innerMember
    by_cases vector : kind = .vec
    · simp only [vector, ↓reduceIte, List.mem_singleton] at chosen
      subst context
      have equal : Same element (variant.fill inner.focus) := by
        rw [← innerLicensed.source_eq]
        exact contextVariants_source _ _ innerMember
      have typed' := replace_element typed selected innerNew.source_typed
      have next := Licensed.directCollection permitted typed'
        (objects_same (replace_same selected equal) objects) (splice_position within) innerNew
      simpa only [SiteData.wrapCollection, recontext, OneHoleContext.fill, contextAddress, vector,
        splice_take within, splice_drop within, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt within)] using next
    · simp only [SiteData.wrapCollection, vector, ↓reduceIte] at chosen
      obtain ⟨residual, residualMember, rfl⟩ := List.mem_map.mp chosen
      have reconstructs : Presents kind elements (element :: residual) := by
        rw [innerLicensed.source_eq, take_selected_drop selected] at residualMember
        have reconstructs := kindResiduals_sound vector
          (by simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt within)] using within)
          residualMember
        simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt within),
          (List.getElem?_eq_some_iff.mp selected).2] using reconstructs
      have typed' := presents_typed reconstructs typed
      have objects' := presents_objects reconstructs objects
      have same : Same element (variant.fill inner.focus) := by
        rw [← innerLicensed.source_eq]
        exact contextVariants_source _ _ innerMember
      have relation := List.Forall₂.cons same (forall₂_same_of_map rfl (targets := residual))
      have next := Licensed.directCollection permitted
        (replace_element typed' (index := 0) rfl innerNew.source_typed)
        (objects_same relation objects') (index := 0) rfl innerNew
      simpa only [SiteData.wrapCollection, recontext, OneHoleContext.fill, contextAddress,
        List.take_zero, List.drop_succ_cons, List.drop_zero, List.length_nil, List.nil_append] using next
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected innerLicensed ih =>
    obtain ⟨variant, innerMember, chosen⟩ := List.mem_flatMap.mp member
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have innerNew := ih innerMember
    by_cases vector : kind = .vec
    · simp only [vector, ↓reduceIte, List.mem_singleton] at chosen
      subst context
      have equal : Same element (variant.fill inner.focus) := by
        rw [← innerLicensed.source_eq]
        exact contextVariants_source _ _ innerMember
      have typed' := replace_element typed selected innerNew.source_typed
      have next := Licensed.authoredCollection declared shape permitted typed'
        (objects_same (replace_same selected equal) objects) (splice_position within) innerNew
      simpa only [SiteData.wrapCollection, recontext, OneHoleContext.fill, contextAddress, vector,
        splice_take within, splice_drop within, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt within)] using next
    · simp only [SiteData.wrapCollection, vector, ↓reduceIte] at chosen
      obtain ⟨residual, residualMember, rfl⟩ := List.mem_map.mp chosen
      have reconstructs : Presents kind elements (element :: residual) := by
        rw [innerLicensed.source_eq, take_selected_drop selected] at residualMember
        have reconstructs := kindResiduals_sound vector
          (by simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt within)] using within)
          residualMember
        simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt within),
          (List.getElem?_eq_some_iff.mp selected).2] using reconstructs
      have typed' := presents_typed reconstructs typed
      have objects' := presents_objects reconstructs objects
      have same : Same element (variant.fill inner.focus) := by
        rw [← innerLicensed.source_eq]
        exact contextVariants_source _ _ innerMember
      have relation := List.Forall₂.cons same (forall₂_same_of_map rfl (targets := residual))
      have next := Licensed.authoredCollection declared shape permitted
        (replace_element typed' (index := 0) rfl innerNew.source_typed)
        (objects_same relation objects') (index := 0) rfl innerNew
      simpa only [SiteData.wrapCollection, recontext, OneHoleContext.fill, contextAddress,
        List.take_zero, List.drop_succ_cons, List.drop_zero, List.length_nil, List.nil_append] using next

/-- Keep the original occurrence even when two equal bag elements produce
identical reconstructed contexts. Their source positions remain distinct. -/
structure SiteVariant where
  original : SiteData
  site : SiteData
  deriving DecidableEq, Repr

def siteVariants (site : SiteData) : List SiteVariant :=
  (contextVariants site.focus site.context).map fun context =>
    ⟨site, recontext site context⟩

theorem siteVariants_original {site : SiteData} {variant : SiteVariant}
    (member : variant ∈ siteVariants site) : variant.original = site := by
  obtain ⟨context, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem siteVariants_source {site : SiteData} {variant : SiteVariant}
    (member : variant ∈ siteVariants site) :
    Same (site.context.fill site.focus) (variant.site.context.fill variant.site.focus) := by
  obtain ⟨context, generated, rfl⟩ := List.mem_map.mp member
  exact contextVariants_source site.focus site.context generated

theorem siteVariants_typed_source {language : LanguageDef}
    {free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {site : SiteData} {variant : SiteVariant}
    (member : variant ∈ siteVariants site)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted language free bound expected
      (site.context.fill site.focus)) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted language free bound expected
      (variant.site.context.fill variant.site.focus) :=
  openPatternWellSorted_of_eqvGen ((same_iff _ _).mp (siteVariants_source member)) typed

theorem siteVariants_licensed {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData} {variant : SiteVariant}
    (licensed : Licensed language free permissions bound expected source site)
    (member : variant ∈ siteVariants site) :
    Licensed language free permissions bound expected
      (variant.site.context.fill variant.site.focus) variant.site := by
  obtain ⟨context, generated, rfl⟩ := List.mem_map.mp member
  exact contextVariants_licensed licensed generated

/-- Residual choices extend the existing grammar-derived occurrence generator.
They do not replace its typing or permission checks. -/
def generatedVariants (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : List SiteVariant :=
  (generate language free permissions bound expected source).flatMap siteVariants

theorem generatedVariants_sound {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {variant : SiteVariant}
    (member : variant ∈ generatedVariants language free permissions bound expected source) :
    Licensed language free permissions bound expected source variant.original ∧
    Same source (variant.site.context.fill variant.site.focus) ∧
    Licensed language free permissions bound expected
      (variant.site.context.fill variant.site.focus) variant.site := by
  obtain ⟨site, generated, residual⟩ := List.mem_flatMap.mp member
  have licensed := generate_sound _ _ _ _ _ _ _ generated
  refine ⟨?_, ?_, siteVariants_licensed licensed residual⟩
  · rw [siteVariants_original residual]
    exact licensed
  · rw [← licensed.source_eq]
    exact siteVariants_source residual

theorem generatedVariants_focus {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {variant : SiteVariant}
    (member : variant ∈ generatedVariants language free permissions bound expected source) :
    variant.site.focus = variant.original.focus ∧
    variant.site.focusBound = variant.original.focusBound ∧
    variant.site.focusType = variant.original.focusType ∧
    variant.site.typingFrames = variant.original.typingFrames := by
  obtain ⟨site, _, residual⟩ := List.mem_flatMap.mp member
  obtain ⟨context, _, rfl⟩ := List.mem_map.mp residual
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Changing an equal focused payload preserves the class of its enclosing
source, including through binding and collection frames. -/
theorem context_fill_same (context : OneHoleContext) {first second : Pattern}
    (same : Same first second) : Same (context.fill first) (context.fill second) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
    exact same_apply_congr _ (List.rel_append (forall₂_same_of_map rfl)
      (.cons ih (forall₂_same_of_map rfl)))
  | lambda display inner ih => exact same_lambda_congr _ ih
  | multiLambda arity display inner ih => exact same_multiLambda_congr _ _ ih
  | substBody inner replacement ih => exact same_subst_congr ih rfl
  | substReplacement body inner ih => exact same_subst_congr rfl ih
  | collection kind before inner after rest ih =>
    exact same_collection_congr _ _ (List.rel_append (forall₂_same_of_map rfl)
      (.cons ih (forall₂_same_of_map rfl)))

/-- Keep the authored occurrence and every dependent frame while replacing
its focus by the presentation reconstructed from a matching receipt. -/
def refocus (site : SiteData) (focus : Pattern) : SiteData := { site with focus }

/-- Collection equality transports the licensed occurrence itself, not just
the type of its endpoint. No new permission or declaration choice is made. -/
theorem refocus_licensed {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    {focus : Pattern} (same : Same site.focus focus) :
    Licensed language free permissions bound expected (site.context.fill focus) (refocus site focus) := by
  induction licensed with
  | here enabled object typed =>
    refine .here enabled ?_ (hasType_of_chain (eqvGen_reflTransGen ((same_iff _ _).mp same)) typed)
    change isObjectPattern focus = true
    rw [← isObjectPattern_canon focus, ← same, isObjectPattern_canon]
    exact object
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
    have innerNew := ih same
    have equal : Same argument (inner.context.fill focus) := by
      rw [← innerLicensed.source_eq]
      exact context_fill_same _ same
    have relation := replace_same selected equal
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have next := Licensed.application declared ordinary (arguments_same relation typed)
      (objects_same relation objects) (splice_position within)
      parameterSelected parameterTyped permitted innerNew
    simpa only [SiteData.wrapApplication, refocus, OneHoleContext.fill,
      splice_take within, splice_drop within] using next
  | lambda permitted innerLicensed ih => exact .lambda permitted (ih same)
  | multiLambda permitted innerLicensed ih => exact .multiLambda permitted (ih same)
  | @directCollection bound kind elements index element elementType inner
      permitted typed objects selected innerLicensed ih =>
    have innerNew := ih same
    have equal : Same element (inner.context.fill focus) := by
      rw [← innerLicensed.source_eq]
      exact context_fill_same _ same
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have next := Licensed.directCollection permitted
      (replace_element typed selected innerNew.source_typed)
      (objects_same (replace_same selected equal) objects) (splice_position within) innerNew
    simpa only [SiteData.wrapCollection, refocus, OneHoleContext.fill,
      splice_take within, splice_drop within] using next
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected innerLicensed ih =>
    have innerNew := ih same
    have equal : Same element (inner.context.fill focus) := by
      rw [← innerLicensed.source_eq]
      exact context_fill_same _ same
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have next := Licensed.authoredCollection declared shape permitted
      (replace_element typed selected innerNew.source_typed)
      (objects_same (replace_same selected equal) objects) (splice_position within) innerNew
    simpa only [SiteData.wrapCollection, refocus, OneHoleContext.fill,
      splice_take within, splice_drop within] using next

end Mettapedia.OSLF.MeTTaIL.CollectionSelection
