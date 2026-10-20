import Mettapedia.OSLF.MeTTaIL.LawNormalFiring
import Mettapedia.OSLF.MeTTaIL.LicensedCompose

/-!
# Flattening along a site's path

The law-normal form splices a nested collection of a flattening kind into its parent. A licensed
site whose path enters such a nested collection has a counterpart one flattening move away: the
same focus with a shorter path, or, when the focus is the nested collection itself, the
flattened parent (`flatten_site`). The law-normal form does not change (`normalize_fill`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

variable {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}

/-! ## The law-normal form only sees normal forms of subterms -/

theorem normalElements_congr (kind : CollType) {before after : List Pattern} {x y : Pattern}
    (same : normalize laws x = normalize laws y) :
    normalElements laws kind (before ++ x :: after) = normalElements laws kind (before ++ y :: after) := by
  unfold normalElements
  cases lawFor laws kind <;> simp [List.map_append, same]

/-- **Filling a context with terms of equal law-normal forms gives equal law-normal forms.** -/
theorem normalize_fill (context : OneHoleContext) {x y : Pattern} (same : normalize laws x = normalize laws y) :
    normalize laws (context.fill x) = normalize laws (context.fill y) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
    simp only [OneHoleContext.fill]
    rw [normalize, normalize]
    simp only [List.map_append, List.map_cons, ih]
  | lambda binder inner ih => simp only [OneHoleContext.fill]; rw [normalize, normalize, ih]
  | multiLambda arity binders inner ih => simp only [OneHoleContext.fill]; rw [normalize, normalize, ih]
  | substBody inner replacement ih => simp only [OneHoleContext.fill]; rw [normalize, normalize, ih]
  | substReplacement body inner ih => simp only [OneHoleContext.fill]; rw [normalize, normalize, ih]
  | collection kind before inner after rest ih =>
    simp only [OneHoleContext.fill]
    rw [normalize_collection', normalize_collection', normalElements_congr kind ih]

/-- Flattening a nested collection of a flattening kind keeps the law-normal form. -/
theorem normalize_flatten {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (before inner after : List Pattern) (rest : Option String) :
    normalize laws (.collection kind (before ++ .collection kind inner none :: after) rest) =
      normalize laws (.collection kind (before ++ inner ++ after) rest) := by
  rw [normalize_collection', normalize_collection']
  congr 1
  unfold normalElements
  rw [found]
  dsimp only
  have sameKind : law.kind = kind := lawFor_kind found
  rw [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
    List.flatMap_append, List.flatMap_append, normalize_collection']
  simp only [splice, sameKind, if_true]
  unfold normalElements
  rw [found]
  simp only [List.append_assoc]

/-! ## Law-equality through contexts -/

/-- **Law-equality lifts through every context.** -/
theorem LawSame.fill (context : OneHoleContext) {x y : Pattern} (same : LawSame laws x y) :
    LawSame laws (context.fill x) (context.fill y) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
    exact LawSame.lift (f := fun z => .apply label (before ++ z :: after)) (fun step => .apply step) ih
  | lambda binder inner ih => exact lawSame_lambda_congr _ ih
  | multiLambda arity binders inner ih => exact lawSame_multiLambda_congr _ _ ih
  | substBody inner replacement ih => exact lawSame_subst_congr ih (.refl _)
  | substReplacement body inner ih => exact lawSame_subst_congr (.refl _) ih
  | collection kind before inner after rest ih =>
    exact LawSame.lift (f := fun z => .collection kind (before ++ z :: after) rest) (fun step => .element step) ih

/-- The replacement check of one context sees only the shape of law-equal fills. -/
theorem replacementRepresentations?_lawSame_target (target : LanguageDef) :
    ∀ (context : OneHoleContext) (frames : List TypingFrame) {hole hole' : Pattern}, LawSame laws hole hole' →
      replacementRepresentations? target context frames hole = replacementRepresentations? target context frames hole'
  | .hole, [], _, _, _ => rfl
  | .hole, _ :: _, _, _, _ => rfl
  | .apply _ _ inner _, [], _, _, _ => rfl
  | .apply label before inner after, frame :: frames, hole, hole', same => by
    cases frame with
    | application declaration index =>
      simp only [replacementRepresentations?]
      cases (target.terms[declaration]?.bind fun rule => rule.params[index]?) with
      | none => rfl
      | some parameter =>
        simp only
        rw [matchesParameterRepresentation?_lawSame parameter (LawSame.fill inner same),
          replacementRepresentations?_lawSame_target target inner frames same]
    | _ => rfl
  | .lambda _ inner, [], _, _, _ => rfl
  | .lambda binder inner, frame :: frames, hole, hole', same => by
    cases frame with
    | lambda => exact replacementRepresentations?_lawSame_target target inner frames same
    | _ => rfl
  | .multiLambda _ _ inner, [], _, _, _ => rfl
  | .multiLambda arity binders inner, frame :: frames, hole, hole', same => by
    cases frame with
    | multiLambda => exact replacementRepresentations?_lawSame_target target inner frames same
    | _ => rfl
  | .substBody _ _, _, _, _, _ => by cases ‹List TypingFrame› <;> rfl
  | .substReplacement _ _, _, _, _, _ => by cases ‹List TypingFrame› <;> rfl
  | .collection _ _ inner _ _, [], _, _, _ => rfl
  | .collection kind before inner after rest, frame :: frames, hole, hole', same => by
    cases frame with
    | directCollection => exact replacementRepresentations?_lawSame_target target inner frames same
    | authoredCollection => exact replacementRepresentations?_lawSame_target target inner frames same
    | _ => rfl

theorem matchesParameterRepresentation_lawSame {parameter : TermParam} {left right : Pattern}
    (same : LawSame laws left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  rw [← matchesParameterRepresentation?_eq_true_iff] at matched ⊢
  rw [← matchesParameterRepresentation?_lawSame parameter same]
  exact matched

/-! ## One flattening move along a path -/

variable (laws language free) in
/-- A site one flattening move away: the same focus on a shorter path, the focus absorbed into its
flattened parent, or a declared unit as focus. -/
inductive Flattened (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (site : SiteData) : Prop where
  | shorter (source' : Pattern) (site' : SiteData)
      (licensed : Licensed language free permissions bound expected source' site')
      (normal : normalize laws source' = normalize laws source) (same : LawSame laws source source')
      (focus : site'.focus = site.focus) (focusBound : site'.focusBound = site.focusBound)
      (focusType : site'.focusType = site.focusType)
      (fill : ∀ hole hole', LawSame laws hole hole' → LawSame laws (site.context.fill hole) (site'.context.fill hole'))
      (accepts : ∀ (target : LanguageDef) hole hole', LawSame laws hole hole' →
        replacementRepresentations? target site.context site.typingFrames hole =
          replacementRepresentations? target site'.context site'.typingFrames hole')
      (shorter : site'.typingFrames.length < site.typingFrames.length)
  | absorbed (source' : Pattern) (site' : SiteData) (law : Laws) (front back elements : List Pattern)
      (licensed : Licensed language free permissions bound expected source' site')
      (normal : normalize laws source' = normalize laws source) (same : LawSame laws source source')
      (found : lawFor laws law.kind = some law)
      (focus : site.focus = .collection law.kind elements none)
      (focus' : site'.focus = .collection law.kind (front ++ elements ++ back) none)
      (focusBound : site'.focusBound = site.focusBound)
      (fill : ∀ inner hole', LawSame laws (.collection law.kind (front ++ inner ++ back) none) hole' →
        LawSame laws (site.context.fill (.collection law.kind inner none)) (site'.context.fill hole'))
      (accepts : ∀ (target : LanguageDef) inner hole', LawSame laws (.collection law.kind (front ++ inner ++ back) none) hole' →
        replacementRepresentations? target site.context site.typingFrames (.collection law.kind inner none) =
          replacementRepresentations? target site'.context site'.typingFrames hole')
      (shorter : site'.typingFrames.length < site.typingFrames.length)
  | unit (law : Laws) (label : String) (kind : CollType) (found : lawFor laws kind = some law)
      (unit : law.unit = some label) (focus : site.focus = .apply label [])

/-! ## The replacement check along composed paths -/

theorem argumentsHaveTypes_representation {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam} {index : Nat} {argument : Pattern} {parameter : TermParam},
      ArgumentsHaveTypes language free bound arguments parameters → arguments[index]? = some argument →
      parameters[index]? = some parameter → MatchesParameterRepresentation parameter argument
  | _ :: _, _ :: _, 0, _, _, .cons representation _ _ _, selected, parameterSelected => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at selected parameterSelected
    subst selected; subst parameterSelected; exact representation
  | _ :: _, _ :: _, index + 1, _, _, .cons _ _ _ tail, selected, parameterSelected => by
    simp only [List.getElem?_cons_succ] at selected parameterSelected
    exact argumentsHaveTypes_representation tail selected parameterSelected
  | [], _, _, _, _, _, selected, _ => by simp at selected

/-- A licensed site accepts its own focus. -/
theorem Licensed.accepts_self {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData} (licensed : Licensed language free permissions bound expected source site) :
    site.acceptsReplacementRepresentation language site.focus = true := by
  induction licensed with
  | here => rfl
  | application declared _ typed _ selected parameterSelected _ _ innerLicensed ih =>
    have declarationAt := List.mk_mem_zipIdx_iff_getElem?.mp declared
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapApplication, replacementRepresentations?,
      declarationAt, Option.bind_some, parameterSelected, Bool.and_eq_true] at ih ⊢
    rw [innerLicensed.source_eq, matchesParameterRepresentation?_eq_true_iff]
    exact ⟨argumentsHaveTypes_representation typed selected parameterSelected, ih⟩
  | lambda _ _ ih => exact ih
  | multiLambda _ _ ih => exact ih
  | directCollection _ _ _ _ _ ih => exact ih
  | authoredCollection _ _ _ _ _ _ _ ih => exact ih

/-- **The replacement check splits along a licensed outer path.** -/
theorem Licensed.replacement_comp {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData} (licensed : Licensed language free permissions bound expected source site)
    (target : LanguageDef) (context : OneHoleContext) (frames : List TypingFrame) (hole : Pattern) :
    replacementRepresentations? target (site.context.comp context) (site.typingFrames ++ frames) hole =
      (replacementRepresentations? target site.context site.typingFrames (context.fill hole) &&
        replacementRepresentations? target context frames hole) := by
  induction licensed with
  | here => simp [SiteData.here, OneHoleContext.comp, replacementRepresentations?]
  | @application bound rule declaration index arguments argument parameter parameterType inner _ _ _ _ _ _ _ _ _ ih =>
    simp only [SiteData.wrapApplication, OneHoleContext.comp, List.cons_append, replacementRepresentations?]
    cases (target.terms[declaration]?.bind fun rule => rule.params[index]?) with
    | none => rfl
    | some parameter => simp only [OneHoleContext.fill_comp, ih, Bool.and_assoc]
  | lambda _ _ ih => simpa [SiteData.wrapLambda, OneHoleContext.comp, replacementRepresentations?] using ih
  | multiLambda _ _ ih => simpa [SiteData.wrapMultiLambda, OneHoleContext.comp, replacementRepresentations?] using ih
  | directCollection _ _ _ _ _ ih => simpa [SiteData.wrapCollection, OneHoleContext.comp, replacementRepresentations?] using ih
  | authoredCollection _ _ _ _ _ _ _ ih =>
    simpa [SiteData.wrapCollection, OneHoleContext.comp, replacementRepresentations?] using ih

/-- **A flattening move inside the focus of a licensed outer path lifts to the whole term.** -/
theorem Flattened.wrap {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {outer inner : SiteData} (outerLicensed : Licensed language free permissions bound expected source outer)
    (flattened : Flattened laws language free permissions outer.focusBound outer.focusType outer.focus inner) :
    Flattened laws language free permissions bound expected source (outer.compose inner) := by
  have sourceEq := outerLicensed.source_eq
  have acceptsOf : ∀ {replacement : Pattern}, LawSame laws outer.focus replacement →
      outer.acceptsReplacementRepresentation language replacement = true := by
    intro replacement same
    have self := CanonicalBags.Licensed.accepts_self outerLicensed
    simp only [SiteData.acceptsReplacementRepresentation] at self ⊢
    rw [← replacementRepresentations?_lawSame_target language outer.context outer.typingFrames same]
    exact self
  cases flattened with
  | shorter source' site' licensed normal same focus focusBound focusType fill accepts shorter =>
    refine .shorter (outer.context.fill source') (outer.compose site') (outerLicensed.compose (acceptsOf same) licensed)
      ?_ ?_ focus focusBound focusType ?_ ?_ ?_
    · rw [← sourceEq]; exact normalize_fill outer.context normal
    · rw [← sourceEq]; exact LawSame.fill outer.context same
    · intro hole hole' sameHole
      simp only [SiteData.compose, OneHoleContext.fill_comp]
      exact LawSame.fill outer.context (fill hole hole' sameHole)
    · intro target hole hole' sameHole
      simp only [SiteData.compose]
      rw [CanonicalBags.Licensed.replacement_comp outerLicensed, CanonicalBags.Licensed.replacement_comp outerLicensed,
        replacementRepresentations?_lawSame_target target outer.context outer.typingFrames (fill hole hole' sameHole),
        accepts target hole hole' sameHole]
    · simp only [SiteData.compose, List.length_append]; omega
  | absorbed source' site' law front back elements licensed normal same found focus focus' focusBound fill accepts shorter =>
    refine .absorbed (outer.context.fill source') (outer.compose site') law front back elements
      (outerLicensed.compose (acceptsOf same) licensed) ?_ ?_ found focus focus' focusBound ?_ ?_ ?_
    · rw [← sourceEq]; exact normalize_fill outer.context normal
    · rw [← sourceEq]; exact LawSame.fill outer.context same
    · intro innerElements hole' sameHole
      simp only [SiteData.compose, OneHoleContext.fill_comp]
      exact LawSame.fill outer.context (fill innerElements hole' sameHole)
    · intro target innerElements hole' sameHole
      simp only [SiteData.compose]
      rw [CanonicalBags.Licensed.replacement_comp outerLicensed, CanonicalBags.Licensed.replacement_comp outerLicensed,
        replacementRepresentations?_lawSame_target target outer.context outer.typingFrames
          (fill innerElements hole' sameHole),
        accepts target innerElements hole' sameHole]
    · simp only [SiteData.compose, List.length_append]; omega
  | unit law label kind found unit focus => exact .unit law label kind found unit focus

/-! ## The flattening move at one collection -/

/-- What splicing removes or opens: a nested collection of the kind, or the declared unit. -/
theorem spliced_shape {law : Laws} {pattern : Pattern} (spliced : splice law (normalize laws pattern) ≠ [normalize laws pattern]) :
    (∃ elements, pattern = .collection law.kind elements none) ∨ (∃ label, law.unit = some label ∧ pattern = .apply label []) := by
  cases pattern with
  | collection kind elements rest =>
    rw [normalize_collection'] at spliced
    cases rest with
    | none =>
      simp only [splice] at spliced
      split at spliced
      · rename_i same; exact .inl ⟨elements, by rw [same]⟩
      · exact absurd rfl spliced
    | some _ => simp [splice] at spliced
  | apply label arguments =>
    rw [normalize] at spliced
    cases arguments with
    | nil =>
      simp only [List.map_nil, splice] at spliced
      split at spliced
      · rename_i unit; exact .inr ⟨label, unit, rfl⟩
      · exact absurd rfl spliced
    | cons => simp [splice] at spliced
  | _ => rw [normalize] at spliced; simp [splice] at spliced

theorem elements_flatten_typed {bound : List TypeExpr} {element : TypeExpr} {elements inner : List Pattern} {index : Nat}
    (typed : ElementsHaveType language free bound elements element)
    (innerTyped : ElementsHaveType language free bound inner element) :
    ElementsHaveType language free bound (elements.take index ++ inner ++ elements.drop (index + 1)) element := by
  apply elementsHaveType_iff.mpr
  intro item member
  simp only [List.mem_append] at member
  rcases member with (inTake | inInner) | inDrop
  · exact elementsHaveType_iff.mp typed item (List.mem_of_mem_take inTake)
  · exact elementsHaveType_iff.mp innerTyped item inInner
  · exact elementsHaveType_iff.mp typed item (List.mem_of_mem_drop inDrop)

theorem objects_flatten {elements inner : List Pattern} {index : Nat} (objects : isObjectPatternList elements = true)
    (innerObjects : isObjectPatternList inner = true) :
    isObjectPatternList (elements.take index ++ inner ++ elements.drop (index + 1)) = true := by
  rw [isObjectPatternList_eq_all, List.all_eq_true] at objects innerObjects ⊢
  intro item member
  simp only [List.mem_append] at member
  rcases member with (inTake | inInner) | inDrop
  · exact objects item (List.mem_of_mem_take inTake)
  · exact innerObjects item inInner
  · exact objects item (List.mem_of_mem_drop inDrop)

theorem getElem?_flatten {elements inner : List Pattern} {index position : Nat} {item : Pattern}
    (within : index < elements.length) (selected : inner[position]? = some item) :
    (elements.take index ++ inner ++ elements.drop (index + 1))[index + position]? = some item := by
  have length : (elements.take index).length = index := by simp; omega
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.append_assoc, List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left,
    List.getElem?_append_left inside]
  exact selected

theorem take_flatten {elements inner : List Pattern} {index position : Nat} (within : index < elements.length)
    (inside : position < inner.length) :
    (elements.take index ++ inner ++ elements.drop (index + 1)).take (index + position) =
      elements.take index ++ inner.take position := by
  have length : (elements.take index).length = index := by simp; omega
  rw [List.append_assoc, List.take_append, length, List.take_take, Nat.min_eq_right (Nat.le_add_right index position),
    Nat.add_sub_cancel_left, List.take_append, show position - inner.length = 0 by omega, List.take_zero,
    List.append_nil]

theorem drop_flatten {elements inner : List Pattern} {index position : Nat} (within : index < elements.length)
    (inside : position < inner.length) :
    (elements.take index ++ inner ++ elements.drop (index + 1)).drop (index + position + 1) =
      inner.drop (position + 1) ++ elements.drop (index + 1) := by
  have length : (elements.take index).length = index := by simp; omega
  rw [List.append_assoc, List.drop_append, length, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show index + position + 1 - index = position + 1 by omega, List.drop_append,
    show position + 1 - inner.length = 0 by omega, List.drop_zero]

/-- **The flattening move at a collection whose selected element splices into it.** -/
theorem flatten_collection (strict : LawsTypedStrict laws language free) {permissions : OperationalPermissions}
    {bound : List TypeExpr} {expected elementType : TypeExpr} {kind : CollType} {law : Laws} {elements : List Pattern}
    {index : Nat} {element : Pattern} {inner : SiteData} (origin : TypingFrame)
    (collectionFrame : (∃ kind', origin = .directCollection kind') ∨ ∃ declaration, origin = .authoredCollection declaration)
    (rebuild : ∀ {elements' : List Pattern} {index' : Nat} {element' : Pattern} {inner' : SiteData},
      ElementsHaveType language free bound elements' elementType → isObjectPatternList elements' = true →
      elements'[index']? = some element' → Licensed language free permissions bound elementType element' inner' →
      Licensed language free permissions bound expected (.collection kind elements' none)
        (inner'.wrapCollection origin kind elements' index'))
    (enabled : permissions.enabled = true)
    (sourceTyped : HasType language free bound (.collection kind elements none) expected)
    (boundOk : ∀ entry ∈ bound, LawTypeOk laws language entry) (expectedOk : LawTypeOk laws language expected)
    (typed : ElementsHaveType language free bound elements elementType) (objects : isObjectPatternList elements = true)
    (selected : elements[index]? = some element)
    (elementLicensed : Licensed language free permissions bound elementType element inner)
    (found : lawFor laws kind = some law) (spliced : splice law (normalize laws element) ≠ [normalize laws element])
    (elementBase : ∃ category, elementType = .base category) :
    Flattened laws language free permissions bound expected (.collection kind elements none)
      (inner.wrapCollection origin kind elements index) := by
  have sameKind : law.kind = kind := lawFor_kind found
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have atIndex : elements[index] = element := (List.getElem?_eq_some_iff.mp selected).2
  have sourceSplit : elements.take index ++ element :: elements.drop (index + 1) = elements :=
    take_selected_drop selected
  have objectsAll := objects
  rw [isObjectPatternList_eq_all, List.all_eq_true] at objectsAll
  have elementObject : isObjectPattern element = true := objectsAll element (List.mem_of_getElem? selected)
  rcases spliced_shape spliced with ⟨nested, rfl⟩ | ⟨label, unit, rfl⟩
  · rw [sameKind] at elementObject
    have nestedObjects : isObjectPatternList nested = true := by
      simpa [isObjectPattern] using elementObject
    have flattenStep : LawSame laws (.collection kind elements none)
        (.collection kind (elements.take index ++ nested ++ elements.drop (index + 1)) none) := by
      conv_lhs => rw [← sourceSplit]
      rw [sameKind]
      exact .rel _ _ (.flatten found)
    have normalEq : normalize laws (.collection kind (elements.take index ++ nested ++ elements.drop (index + 1)) none) =
        normalize laws (.collection kind elements none) := by
      conv_rhs => rw [← sourceSplit]
      rw [sameKind, normalize_flatten found]
    have sourceObject : isObjectPattern (.collection kind elements none) = true := by
      simpa [isObjectPattern] using objects
    have source'Typed := LawSame.hasType strict flattenStep boundOk expectedOk sourceObject sourceTyped
    have source'Object : isObjectPattern (.collection kind (elements.take index ++ nested ++ elements.drop (index + 1))
        none) = true := by
      simpa [isObjectPattern] using objects_flatten (index := index) objects nestedObjects
    cases elementLicensed with
    | here =>
      refine .absorbed (.collection kind (elements.take index ++ nested ++ elements.drop (index + 1)) none)
        (SiteData.here bound expected _) law (elements.take index) (elements.drop (index + 1)) nested
        (.here enabled source'Object source'Typed) normalEq flattenStep (by rw [sameKind]; exact found)
        (by simp [SiteData.wrapCollection, SiteData.here]) (by simp [SiteData.here, sameKind, List.append_assoc]) rfl ?_ ?_
        (by simp [SiteData.here, SiteData.wrapCollection])
      · intro innerElements hole' sameHole
        simp only [SiteData.wrapCollection, SiteData.here, OneHoleContext.fill]
        refine .trans _ _ _ ?_ sameHole
        rw [sameKind]
        exact .rel _ _ (.flatten found)
      · intro target innerElements hole' _
        rcases collectionFrame with ⟨kind', rfl⟩ | ⟨declaration, rfl⟩ <;>
          simp [SiteData.wrapCollection, SiteData.here, replacementRepresentations?]
    | directCollection _ _ _ _ _ =>
      obtain ⟨category, same⟩ := elementBase
      cases same
    | @authoredCollection _ rule' declaration' parameterName' _ _ position item elementType' inner2 declared' shape'
        permitted' nestedTyped _ nestedSelected inner2Licensed =>
      have homogeneous := strict.homogeneous law law.kind (by rw [sameKind]; exact found) rule'
        (List.fst_mem_of_mem_zipIdx declared') _ _ shape'
      subst homogeneous
      have inside := (List.getElem?_eq_some_iff.mp nestedSelected).1
      refine .shorter (.collection kind (elements.take index ++ nested ++ elements.drop (index + 1)) none)
        (inner2.wrapCollection origin kind (elements.take index ++ nested ++ elements.drop (index + 1)) (index + position))
        (rebuild (elements_flatten_typed typed nestedTyped) (objects_flatten objects nestedObjects)
          (getElem?_flatten within nestedSelected) inner2Licensed)
        normalEq flattenStep (by simp [SiteData.wrapCollection]) (by simp [SiteData.wrapCollection])
        (by simp [SiteData.wrapCollection]) ?_ ?_ (by simp [SiteData.wrapCollection])
      · intro hole hole' sameHole
        simp only [SiteData.wrapCollection, OneHoleContext.fill]
        rw [take_flatten within inside, drop_flatten within inside, sameKind]
        refine .trans _ _ _ (.rel _ _ (.flatten found)) ?_
        have lifted := LawSame.fill (.collection kind (elements.take index ++ nested.take position) .hole
          (nested.drop (position + 1) ++ elements.drop (index + 1)) none) (LawSame.fill inner2.context sameHole)
        simpa [OneHoleContext.fill, List.append_assoc] using lifted
      · intro target hole hole' sameHole
        rcases collectionFrame with ⟨kind', rfl⟩ | ⟨declaration, rfl⟩ <;>
        · simp only [SiteData.wrapCollection, replacementRepresentations?]
          exact replacementRepresentations?_lawSame_target target inner2.context inner2.typingFrames sameHole
  · cases elementLicensed with
    | here => exact .unit law label kind found unit (by simp [SiteData.wrapCollection, SiteData.here])
    | application _ _ _ _ argumentSelected => simp at argumentSelected

/-- **A site whose path is not flat has a counterpart one flattening move away.** -/
theorem flatten_site (strict : LawsTypedStrict laws language free) {permissions : OperationalPermissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    (∀ entry ∈ bound, LawTypeOk laws language entry) → LawTypeOk laws language expected →
      ¬ PathFlat laws site.context site.focus → Flattened laws language free permissions bound expected source site := by
  induction licensed with
  | here => intro _ _ notFlat; exact absurd (.hole _) notFlat
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
    intro boundOk expectedOk notFlat
    have innerNotFlat : ¬ PathFlat laws inner.context inner.focus := fun flat => notFlat (by
      simpa [SiteData.wrapApplication] using PathFlat.apply (label := rule.label) (before := arguments.take index)
        (after := arguments.drop (index + 1)) flat)
    have parameterOk := strict.parameters rule (List.fst_mem_of_mem_zipIdx declared) parameter
      (List.mem_of_getElem? parameterSelected) parameterType parameterTyped
    have outerLicensed : Licensed language free permissions bound (.base rule.category) (.apply rule.label arguments)
        ((SiteData.here bound parameterType argument).wrapApplication declaration rule.label arguments index) :=
      .application declared ordinary typed objects selected parameterSelected parameterTyped permitted
        (.here innerLicensed.enabled innerLicensed.source_object innerLicensed.source_typed)
    have wrapped := Flattened.wrap outerLicensed (ih boundOk parameterOk innerNotFlat)
    have siteEq : ((SiteData.here bound parameterType argument).wrapApplication declaration rule.label arguments index).compose
        inner = inner.wrapApplication declaration rule.label arguments index := by
      cases inner; simp [SiteData.compose, SiteData.wrapApplication, SiteData.here, OneHoleContext.comp]
    rw [siteEq] at wrapped
    exact wrapped
  | @lambda bound binder body domain codomain inner enabled innerLicensed ih =>
    intro boundOk expectedOk notFlat
    have innerNotFlat : ¬ PathFlat laws inner.context inner.focus := fun flat => notFlat (by
      simpa [SiteData.wrapLambda] using PathFlat.lambda (binder := binder) flat)
    have outerLicensed : Licensed language free permissions bound (.arrow domain codomain) (.lambda binder body)
        ((SiteData.here (domain :: bound) codomain body).wrapLambda binder domain) :=
      .lambda enabled (.here innerLicensed.enabled innerLicensed.source_object innerLicensed.source_typed)
    have wrapped := Flattened.wrap outerLicensed (ih (fun entry member => by
      rcases List.mem_cons.mp member with rfl | other
      · exact expectedOk.1
      · exact boundOk entry other) expectedOk.2 innerNotFlat)
    have siteEq : ((SiteData.here (domain :: bound) codomain body).wrapLambda binder domain).compose inner =
        inner.wrapLambda binder domain := by
      cases inner; simp [SiteData.compose, SiteData.wrapLambda, SiteData.here, OneHoleContext.comp]
    rw [siteEq] at wrapped
    exact wrapped
  | @multiLambda bound arity binders body domain codomain inner enabled innerLicensed ih =>
    intro boundOk expectedOk notFlat
    have innerNotFlat : ¬ PathFlat laws inner.context inner.focus := fun flat => notFlat (by
      simpa [SiteData.wrapMultiLambda] using PathFlat.multiLambda (arity := arity) (binders := binders) flat)
    have outerLicensed : Licensed language free permissions bound (.arrow (.multiBinder domain) codomain)
        (.multiLambda arity binders body)
        ((SiteData.here (List.replicate arity domain ++ bound) codomain body).wrapMultiLambda arity binders domain) :=
      .multiLambda enabled (.here innerLicensed.enabled innerLicensed.source_object innerLicensed.source_typed)
    have wrapped := Flattened.wrap outerLicensed (ih (fun entry member => by
      rcases List.mem_append.mp member with inReplicate | other
      · rw [List.eq_of_mem_replicate inReplicate]; exact expectedOk.1
      · exact boundOk entry other) expectedOk.2 innerNotFlat)
    have siteEq : ((SiteData.here (List.replicate arity domain ++ bound) codomain body).wrapMultiLambda arity binders
        domain).compose inner = inner.wrapMultiLambda arity binders domain := by
      cases inner; simp [SiteData.compose, SiteData.wrapMultiLambda, SiteData.here, OneHoleContext.comp]
    rw [siteEq] at wrapped
    exact wrapped
  | @directCollection bound kind elements index element elementType inner permitted typed objects selected
      innerLicensed ih =>
    intro boundOk expectedOk notFlat
    by_cases innerFlat : PathFlat laws inner.context inner.focus
    · have levelSpliced : ∃ law, lawFor laws kind = some law ∧ splice law (normalize laws element) ≠ [normalize laws element] := by
        by_contra none
        push Not at none
        apply notFlat
        simp only [SiteData.wrapCollection]
        refine .collection innerFlat fun law found => ?_
        rw [innerLicensed.source_eq]
        exact none law found
      obtain ⟨law, found, spliced⟩ := levelSpliced
      obtain ⟨rule, _, name, _, rfl⟩ := expectedOk.lawful found
      exact flatten_collection strict (.directCollection kind) (.inl ⟨kind, rfl⟩)
        (fun typed' objects' selected' inner' => .directCollection permitted typed' objects' selected' inner')
        innerLicensed.enabled (.collection typed) boundOk expectedOk typed objects selected innerLicensed found spliced
        ⟨_, rfl⟩
    · have outerLicensed : Licensed language free permissions bound (.collection kind elementType)
          (.collection kind elements none)
          ((SiteData.here bound elementType element).wrapCollection (.directCollection kind) kind elements index) :=
        .directCollection permitted typed objects selected
          (.here innerLicensed.enabled innerLicensed.source_object innerLicensed.source_typed)
      have wrapped := Flattened.wrap outerLicensed (ih boundOk expectedOk.element innerFlat)
      have siteEq : ((SiteData.here bound elementType element).wrapCollection (.directCollection kind) kind elements
          index).compose inner = inner.wrapCollection (.directCollection kind) kind elements index := by
        cases inner; simp [SiteData.compose, SiteData.wrapCollection, SiteData.here, OneHoleContext.comp]
      rw [siteEq] at wrapped
      exact wrapped
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected innerLicensed ih =>
    intro boundOk expectedOk notFlat
    have parameterOk := strict.parameters rule (List.fst_mem_of_mem_zipIdx declared) _ (by rw [shape]; exact .head _) _ rfl
    by_cases innerFlat : PathFlat laws inner.context inner.focus
    · have levelSpliced : ∃ law, lawFor laws kind = some law ∧ splice law (normalize laws element) ≠ [normalize laws element] := by
        by_contra none
        push Not at none
        apply notFlat
        simp only [SiteData.wrapCollection]
        refine .collection innerFlat fun law found => ?_
        rw [innerLicensed.source_eq]
        exact none law found
      obtain ⟨law, found, spliced⟩ := levelSpliced
      have homogeneous := strict.homogeneous law kind found rule (List.fst_mem_of_mem_zipIdx declared) _ _ shape
      exact flatten_collection strict (.authoredCollection declaration) (.inr ⟨declaration, rfl⟩)
        (fun typed' objects' selected' inner' => .authoredCollection declared shape permitted typed' objects' selected' inner')
        innerLicensed.enabled (.collectionConstructor (List.fst_mem_of_mem_zipIdx declared) shape typed) boundOk
        expectedOk typed objects selected innerLicensed found spliced ⟨_, homogeneous⟩
    · have outerLicensed : Licensed language free permissions bound (.base rule.category)
          (.collection kind elements none)
          ((SiteData.here bound elementType element).wrapCollection (.authoredCollection declaration) kind elements index) :=
        .authoredCollection declared shape permitted typed objects selected
          (.here innerLicensed.enabled innerLicensed.source_object innerLicensed.source_typed)
      have wrapped := Flattened.wrap outerLicensed (ih boundOk parameterOk.element innerFlat)
      have siteEq : ((SiteData.here bound elementType element).wrapCollection (.authoredCollection declaration) kind
          elements index).compose inner = inner.wrapCollection (.authoredCollection declaration) kind elements index := by
        cases inner; simp [SiteData.compose, SiteData.wrapCollection, SiteData.here, OneHoleContext.comp]
      rw [siteEq] at wrapped
      exact wrapped

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
