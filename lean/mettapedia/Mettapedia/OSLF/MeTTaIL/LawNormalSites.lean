import Mettapedia.OSLF.MeTTaIL.LawNormalTyping
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Licensed sites at law-normal forms

When no reduction context lies inside a collection of a flattening kind (`NoLawDescent`), every
path to a licensed site crosses only constructors, binders and collections without laws, whose
positions normalization keeps. Every licensed site then has a licensed counterpart at the
law-normal form, with the normal form of the focus, the same typing frames, and a context that
keeps law-equality (`licensed_normalize`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

variable {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}

/-- No reduction context lies inside a collection of a flattening kind. -/
def NoLawDescent (laws : List Laws) (permissions : OperationalPermissions) : Prop :=
  ∀ kind law, lawFor laws kind = some law → kind ∉ permissions.collectionKinds

theorem noNested_of_lawTypeOk {type : TypeExpr} (ok : LawTypeOk laws language type) : NoNested laws type := by
  induction type with
  | base => trivial
  | arrow _ _ domain codomain => exact ⟨domain ok.1, codomain ok.2⟩
  | multiBinder _ domain => exact domain ok
  | collection _ _ element =>
    rcases ok with ⟨unlawful, inner⟩ | ⟨_, _, _, _, rfl⟩
    · exact ⟨element inner, fun law found => by rw [unlawful] at found; cases found⟩
    · exact ⟨trivial, fun _ _ _ same => by cases same⟩

/-- Strictly typed laws are typed. -/
theorem LawsTypedStrict.toLawsTyped (admission : LawsTypedStrict laws language free) : LawsTyped laws language free where
  homogeneous := admission.homogeneous
  parameters rule declared parameter member type typed :=
    noNested_of_lawTypeOk (admission.parameters rule declared parameter member type typed)
  freeNames name type found := noNested_of_lawTypeOk (admission.freeNames name type found)

theorem matchesParameterRepresentation?_lawSame (parameter : TermParam) {left right : Pattern}
    (same : LawSame laws left right) :
    matchesParameterRepresentation? parameter left = matchesParameterRepresentation? parameter right := by
  induction same with
  | rel _ _ step =>
    apply Bool.eq_iff_iff.mpr
    rw [matchesParameterRepresentation?_eq_true_iff, matchesParameterRepresentation?_eq_true_iff]
    exact step.matchesParameterRepresentation_iff
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

private theorem forall₂_normalize (items : List Pattern) : List.Forall₂ (LawSame laws) items (items.map (normalize laws)) :=
  List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun item _ => to_normalize laws item)

private theorem lawSame_middle {before before' after after' : List Pattern} {x y : Pattern}
    (front : List.Forall₂ (LawSame laws) before before') (middle : LawSame laws x y)
    (back : List.Forall₂ (LawSame laws) after after') :
    List.Forall₂ (LawSame laws) (before ++ x :: after) (before' ++ y :: after') :=
  List.rel_append front (.cons middle back)

private theorem elements_normalize (admission : LawsTyped laws language free) {bound : List TypeExpr}
    {element : TypeExpr} {elements : List Pattern} (boundOk : ∀ entry ∈ bound, NoNested laws entry)
    (elementOk : NoNested laws element) (objects : isObjectPatternList elements = true)
    (typed : ElementsHaveType language free bound elements element) :
    ElementsHaveType language free bound (elements.map (normalize laws)) element := by
  apply elementsHaveType_iff.mpr
  intro item member
  obtain ⟨original, inElements, rfl⟩ := List.mem_map.mp member
  have object : isObjectPattern original = true := by
    rw [isObjectPatternList_eq_all, List.all_eq_true] at objects; exact objects original inElements
  exact normalize_hasType admission original boundOk elementOk object (elementsHaveType_iff.mp typed original inElements)

private theorem normalElements_unlawful {kind : CollType} (unlawful : lawFor laws kind = none) (elements : List Pattern) :
    normalElements laws kind elements = elements.map (normalize laws) := by
  unfold normalElements; rw [unlawful]

/-! ## Normalizing the elements of a collection in place -/

/-- Normalized elements around a selected element that is its own splice. -/
theorem normalElements_split (kind : CollType) (elements : List Pattern) (index : Nat) (within : index < elements.length)
    (fixed : ∀ law, lawFor laws kind = some law →
      splice law (normalize laws elements[index]) = [normalize laws elements[index]]) :
    normalElements laws kind elements = normalElements laws kind (elements.take index) ++
      normalize laws elements[index] :: normalElements laws kind (elements.drop (index + 1)) := by
  have split : elements = elements.take index ++ elements[index] :: elements.drop (index + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  conv_lhs => rw [split]
  unfold normalElements
  cases found : lawFor laws kind with
  | some law =>
    dsimp only
    rw [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, fixed law found]
    rfl
  | none => dsimp only; rw [List.map_append, List.map_cons]

/-- **Normalizing a segment of a collection's elements in place is a sequence of law moves.** -/
theorem lawSame_normalElements (kind : CollType) (rest : Option String) (suffix : List Pattern) :
    ∀ (prefix' segment : List Pattern),
      LawSame laws (.collection kind (prefix' ++ segment ++ suffix) rest)
        (.collection kind (prefix' ++ normalElements laws kind segment ++ suffix) rest)
  | prefix', [] => by rw [normalElements_nil]; exact .refl _
  | prefix', item :: segment => by
    have normalized : LawSame laws (.collection kind (prefix' ++ item :: (segment ++ suffix)) rest)
        (.collection kind (prefix' ++ normalize laws item :: (segment ++ suffix)) rest) :=
      LawSame.lift (f := fun x => .collection kind (prefix' ++ x :: (segment ++ suffix)) rest)
        (fun step => .element step) (to_normalize laws item)
    unfold normalElements
    cases found : lawFor laws kind with
    | some law =>
      dsimp only
      rw [List.map_cons, List.flatMap_cons]
      have spliced : LawSame laws (.collection kind (prefix' ++ normalize laws item :: (segment ++ suffix)) rest)
          (.collection kind (prefix' ++ splice law (normalize laws item) ++ (segment ++ suffix)) rest) := by
        have sameKind : law.kind = kind := lawFor_kind found
        generalize normalize laws item = piece
        cases piece with
        | collection actual elements innerRest =>
          cases innerRest with
          | none =>
            simp only [splice]
            split
            · rename_i isKind
              rw [isKind, sameKind]
              exact .rel _ _ (.flatten found)
            · simp only [List.singleton_append, List.append_assoc]; exact .refl _
          | some _ => simp only [splice, List.singleton_append, List.append_assoc]; exact .refl _
        | apply label arguments =>
          cases arguments with
          | nil =>
            simp only [splice]
            split
            · rename_i unit
              simp only [List.append_nil]
              exact .rel _ _ (.unit found unit)
            · simp only [List.singleton_append, List.append_assoc]; exact .refl _
          | cons => simp only [splice, List.singleton_append, List.append_assoc]; exact .refl _
        | _ => simp only [splice, List.singleton_append, List.append_assoc]; exact .refl _
      have later := lawSame_normalElements kind rest suffix (prefix' ++ splice law (normalize laws item)) segment
      unfold normalElements at later
      rw [found] at later
      simp only [List.append_assoc] at later spliced normalized ⊢
      exact .trans _ _ _ normalized (.trans _ _ _ spliced later)
    | none =>
      dsimp only
      rw [List.map_cons]
      have later := lawSame_normalElements kind rest suffix (prefix' ++ [normalize laws item]) segment
      unfold normalElements at later
      rw [found] at later
      simp only [List.append_assoc, List.singleton_append] at later normalized ⊢
      exact .trans _ _ _ normalized later

/-- Normalized elements of a typed collection keep the element type. -/
theorem normalElements_typed (admission : LawsTyped laws language free) {bound : List TypeExpr} {kind : CollType}
    {element : TypeExpr} {elements : List Pattern} (boundOk : ∀ entry ∈ bound, NoNested laws entry)
    (elementOk : NoNested laws element)
    (notNested : ∀ law, lawFor laws kind = some law → ∀ inner, element ≠ .collection kind inner)
    (objects : isObjectPatternList elements = true) (typed : ElementsHaveType language free bound elements element) :
    ElementsHaveType language free bound (normalElements laws kind elements) element := by
  have each := elements_normalize admission boundOk elementOk objects typed
  apply elementsHaveType_iff.mpr
  unfold normalElements
  cases found : lawFor laws kind with
  | some law =>
    intro item member
    obtain ⟨piece, inPieces, inSplice⟩ := List.mem_flatMap.mp member
    exact splice_typed admission found (notNested law found) (elementsHaveType_iff.mp each piece inPieces) item inSplice
  | none => exact elementsHaveType_iff.mp each

/-- Every path element of a site is its own splice: normalization keeps the path. -/
inductive PathFlat (laws : List Laws) : OneHoleContext → Pattern → Prop where
  | hole (focus : Pattern) : PathFlat laws .hole focus
  | apply {label : String} {before after : List Pattern} {inner : OneHoleContext} {focus : Pattern} :
      PathFlat laws inner focus → PathFlat laws (.apply label before inner after) focus
  | lambda {binder : Option String} {inner : OneHoleContext} {focus : Pattern} :
      PathFlat laws inner focus → PathFlat laws (.lambda binder inner) focus
  | multiLambda {arity : Nat} {binders : List String} {inner : OneHoleContext} {focus : Pattern} :
      PathFlat laws inner focus → PathFlat laws (.multiLambda arity binders inner) focus
  | collection {kind : CollType} {before after : List Pattern} {inner : OneHoleContext} {rest : Option String}
      {focus : Pattern} : PathFlat laws inner focus →
      (∀ law, lawFor laws kind = some law →
        splice law (normalize laws (inner.fill focus)) = [normalize laws (inner.fill focus)]) →
      PathFlat laws (.collection kind before inner after rest) focus

/-- **Every licensed site whose path normalization keeps has a licensed counterpart at the
law-normal form**, with the normal form of the focus, the same typing frames, and a context that
keeps law-equality. -/
theorem licensed_normalize (admission : LawsTyped laws language free) {permissions : OperationalPermissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {site : SiteData} (licensed : Licensed language free permissions bound expected source site)
    (boundOk : ∀ entry ∈ bound, NoNested laws entry) (expectedOk : NoNested laws expected) :
    PathFlat laws site.context site.focus → ∃ site', Licensed language free permissions bound expected (normalize laws source) site' ∧
      site'.focus = normalize laws site.focus ∧ site'.focusBound = site.focusBound ∧
      site'.focusType = site.focusType ∧ site'.typingFrames = site.typingFrames ∧
      (∀ hole hole', LawSame laws hole hole' → LawSame laws (site.context.fill hole) (site'.context.fill hole')) ∧
      (∀ (target : LanguageDef) hole hole', LawSame laws hole hole' →
        replacementRepresentations? target site.context site.typingFrames hole =
          replacementRepresentations? target site'.context site'.typingFrames hole') := by
  induction licensed with
  | @here bound expected source enabled object typed =>
    intro _
    refine ⟨SiteData.here bound expected (normalize laws source),
      .here enabled (normalize_object source object) (normalize_hasType admission source boundOk expectedOk object typed),
      rfl, rfl, rfl, rfl, fun _ _ same => same, ?_⟩
    intro target hole hole' _
    rfl
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted _ ih =>
    have parameterOk : NoNested laws parameterType :=
      admission.parameters rule (List.fst_mem_of_mem_zipIdx declared) parameter
        (List.mem_of_getElem? parameterSelected) parameterType parameterTyped
    intro flat
    cases flat with
    | apply innerFlat =>
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, fill, accepts⟩ := ih boundOk parameterOk innerFlat
    have objectsAll : ∀ item ∈ arguments, isObjectPattern item = true := by
      rw [isObjectPatternList_eq_all, List.all_eq_true] at objects; exact objects
    refine ⟨inner'.wrapApplication declaration rule.label (arguments.map (normalize laws)) index, ?_, focus, focusBound,
      focusType, by simp [SiteData.wrapApplication, frames], ?_, ?_⟩
    · rw [normalize]
      exact .application declared ordinary
        (argumentsHaveTypes_normalize admission arguments boundOk objectsAll
          (fun parameter member => admission.parameters rule (List.fst_mem_of_mem_zipIdx declared) parameter member)
          typed)
        (isObjectPatternList_eq_all _ ▸ by
          rw [List.all_eq_true]; intro item member
          obtain ⟨original, inArguments, rfl⟩ := List.mem_map.mp member
          exact normalize_object original (objectsAll original inArguments))
        (by simp [List.getElem?_map, selected]) parameterSelected parameterTyped permitted licensed'
    · intro hole hole' same
      simp only [SiteData.wrapApplication, OneHoleContext.fill, ← List.map_take, ← List.map_drop]
      exact lawSame_apply_congr _ (lawSame_middle (forall₂_normalize _) (fill hole hole' same) (forall₂_normalize _))
    · intro target hole hole' same
      simp only [SiteData.wrapApplication, replacementRepresentations?]
      cases (target.terms[declaration]?.bind fun rule => rule.params[index]?) with
      | none => rfl
      | some parameter =>
        simp only
        rw [matchesParameterRepresentation?_lawSame parameter (fill hole hole' same), accepts target hole hole' same]
  | @lambda bound binder body domain codomain inner enabled _ ih =>
    intro flat
    cases flat with
    | lambda innerFlat =>
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, fill, accepts⟩ := ih
      (fun entry member => by
        rcases List.mem_cons.mp member with rfl | other
        · exact expectedOk.1
        · exact boundOk entry other) expectedOk.2 innerFlat
    refine ⟨inner'.wrapLambda binder domain, ?_, focus, focusBound, focusType,
      by simp [SiteData.wrapLambda, frames], ?_, ?_⟩
    · rw [normalize]; exact .lambda enabled licensed'
    · intro hole hole' same
      simp only [SiteData.wrapLambda, OneHoleContext.fill]
      exact lawSame_lambda_congr _ (fill hole hole' same)
    · intro target hole hole' same
      simp only [SiteData.wrapLambda, replacementRepresentations?]
      exact accepts target hole hole' same
  | @multiLambda bound arity binders body domain codomain inner enabled _ ih =>
    intro flat
    cases flat with
    | multiLambda innerFlat =>
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, fill, accepts⟩ := ih
      (fun entry member => by
        rcases List.mem_append.mp member with inReplicate | other
        · rw [List.eq_of_mem_replicate inReplicate]; exact expectedOk.1
        · exact boundOk entry other) expectedOk.2 innerFlat
    refine ⟨inner'.wrapMultiLambda arity binders domain, ?_, focus, focusBound, focusType,
      by simp [SiteData.wrapMultiLambda, frames], ?_, ?_⟩
    · rw [normalize]; exact .multiLambda enabled licensed'
    · intro hole hole' same
      simp only [SiteData.wrapMultiLambda, OneHoleContext.fill]
      exact lawSame_multiLambda_congr _ _ (fill hole hole' same)
    · intro target hole hole' same
      simp only [SiteData.wrapMultiLambda, replacementRepresentations?]
      exact accepts target hole hole' same
  | @directCollection bound kind elements index element elementType inner permitted typed objects selected
      innerLicensed ih =>
    intro flat
    cases flat with
    | collection innerFlat fixed =>
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have atIndex : elements[index] = element := (List.getElem?_eq_some_iff.mp selected).2
    simp only [SiteData.wrapCollection] at innerFlat fixed
    rw [innerLicensed.source_eq] at fixed
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, fill, accepts⟩ := ih boundOk expectedOk.1 innerFlat
    have split := normalElements_split (laws := laws) kind elements index within (by rw [atIndex]; exact fixed)
    rw [atIndex] at split
    have notNested : ∀ law, lawFor laws kind = some law → ∀ inner, elementType ≠ .collection kind inner :=
      fun law found inner same => by rw [same] at expectedOk; exact expectedOk.2 law found inner rfl
    refine ⟨inner'.wrapCollection (.directCollection kind) kind (normalElements laws kind elements)
      (normalElements laws kind (elements.take index)).length, ?_, focus, focusBound, focusType,
      by simp [SiteData.wrapCollection, frames], ?_, ?_⟩
    · rw [normalize_collection']
      refine .directCollection permitted (normalElements_typed admission boundOk expectedOk.1 notNested objects typed)
        (by
          rw [isObjectPatternList_eq_all, List.all_eq_true]
          intro item member
          exact normalize_object (laws := laws) (.collection kind elements none)
            (by simpa [isObjectPattern] using objects) |> fun object => by
              simp only [normalize_collection', isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all,
                List.all_eq_true] at object
              exact object.2 item member)
        (by rw [split]; simp) licensed'
    · intro hole hole' same
      have takeEq : (normalElements laws kind elements).take (normalElements laws kind (elements.take index)).length =
          normalElements laws kind (elements.take index) := by rw [split]; simp
      have dropEq : (normalElements laws kind elements).drop ((normalElements laws kind (elements.take index)).length + 1) =
          normalElements laws kind (elements.drop (index + 1)) := by rw [split]; simp
      simp only [SiteData.wrapCollection, OneHoleContext.fill]
      rw [takeEq, dropEq]
      have prefixStep := lawSame_normalElements (laws := laws) kind none (inner.context.fill hole :: elements.drop (index + 1))
        [] (elements.take index)
      have suffixStep := lawSame_normalElements (laws := laws) kind none []
        (normalElements laws kind (elements.take index) ++ [inner.context.fill hole]) (elements.drop (index + 1))
      have middleStep : LawSame laws
          (.collection kind (normalElements laws kind (elements.take index) ++ inner.context.fill hole ::
            normalElements laws kind (elements.drop (index + 1))) none)
          (.collection kind (normalElements laws kind (elements.take index) ++ inner'.context.fill hole' ::
            normalElements laws kind (elements.drop (index + 1))) none) :=
        LawSame.lift (f := fun x => .collection kind (normalElements laws kind (elements.take index) ++ x ::
          normalElements laws kind (elements.drop (index + 1))) none) (fun step => .element step) (fill hole hole' same)
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append] at prefixStep suffixStep
      exact .trans _ _ _ prefixStep (.trans _ _ _ suffixStep middleStep)
    · intro target hole hole' same
      simp only [SiteData.wrapCollection, replacementRepresentations?]
      exact accepts target hole hole' same
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected innerLicensed ih =>
    intro flat
    cases flat with
    | collection innerFlat fixed =>
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have atIndex : elements[index] = element := (List.getElem?_eq_some_iff.mp selected).2
    simp only [SiteData.wrapCollection] at innerFlat fixed
    rw [innerLicensed.source_eq] at fixed
    have parameterOk : NoNested laws (.collection kind elementType) :=
      admission.parameters rule (List.fst_mem_of_mem_zipIdx declared) _
        (by rw [((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2]; exact .head _) _ rfl
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, fill, accepts⟩ := ih boundOk parameterOk.1 innerFlat
    have split := normalElements_split (laws := laws) kind elements index within (by rw [atIndex]; exact fixed)
    rw [atIndex] at split
    have notNested : ∀ law, lawFor laws kind = some law → ∀ inner, elementType ≠ .collection kind inner :=
      fun law found inner same => parameterOk.2 law found inner same
    refine ⟨inner'.wrapCollection (.authoredCollection declaration) kind (normalElements laws kind elements)
      (normalElements laws kind (elements.take index)).length, ?_, focus, focusBound, focusType,
      by simp [SiteData.wrapCollection, frames], ?_, ?_⟩
    · rw [normalize_collection']
      refine .authoredCollection declared shape permitted
        (normalElements_typed admission boundOk parameterOk.1 notNested objects typed)
        (by
          rw [isObjectPatternList_eq_all, List.all_eq_true]
          intro item member
          exact normalize_object (laws := laws) (.collection kind elements none)
            (by simpa [isObjectPattern] using objects) |> fun object => by
              simp only [normalize_collection', isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all,
                List.all_eq_true] at object
              exact object.2 item member)
        (by rw [split]; simp) licensed'
    · intro hole hole' same
      have takeEq : (normalElements laws kind elements).take (normalElements laws kind (elements.take index)).length =
          normalElements laws kind (elements.take index) := by rw [split]; simp
      have dropEq : (normalElements laws kind elements).drop ((normalElements laws kind (elements.take index)).length + 1) =
          normalElements laws kind (elements.drop (index + 1)) := by rw [split]; simp
      simp only [SiteData.wrapCollection, OneHoleContext.fill]
      rw [takeEq, dropEq]
      have prefixStep := lawSame_normalElements (laws := laws) kind none (inner.context.fill hole :: elements.drop (index + 1))
        [] (elements.take index)
      have suffixStep := lawSame_normalElements (laws := laws) kind none []
        (normalElements laws kind (elements.take index) ++ [inner.context.fill hole]) (elements.drop (index + 1))
      have middleStep : LawSame laws
          (.collection kind (normalElements laws kind (elements.take index) ++ inner.context.fill hole ::
            normalElements laws kind (elements.drop (index + 1))) none)
          (.collection kind (normalElements laws kind (elements.take index) ++ inner'.context.fill hole' ::
            normalElements laws kind (elements.drop (index + 1))) none) :=
        LawSame.lift (f := fun x => .collection kind (normalElements laws kind (elements.take index) ++ x ::
          normalElements laws kind (elements.drop (index + 1))) none) (fun step => .element step) (fill hole hole' same)
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append] at prefixStep suffixStep
      exact .trans _ _ _ prefixStep (.trans _ _ _ suffixStep middleStep)
    · intro target hole hole' same
      simp only [SiteData.wrapCollection, replacementRepresentations?]
      exact accepts target hole hole' same

/-- Without reduction contexts inside collections of a flattening kind, every path is flat. -/
theorem pathFlat_of_noDescent {permissions : OperationalPermissions} (noDescent : NoLawDescent laws permissions)
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    PathFlat laws site.context site.focus := by
  induction licensed with
  | here => exact .hole _
  | application _ _ _ _ _ _ _ _ _ ih => exact .apply ih
  | lambda _ _ ih => exact .lambda ih
  | multiLambda _ _ ih => exact .multiLambda ih
  | @directCollection _ kind _ _ _ _ _ permitted _ _ _ _ ih =>
    exact .collection ih fun law found => absurd permitted (noDescent kind law found)
  | @authoredCollection _ _ _ _ kind _ _ _ _ _ _ _ permitted _ _ _ _ ih =>
    exact .collection ih fun law found => absurd permitted (noDescent kind law found)

/-- **Site types are typed for the laws**, when the ambient types are, the laws are strictly
typed, and no reduction context lies inside a collection of a flattening kind. -/
theorem Licensed.lawTypeOk (admission : LawsTypedStrict laws language free) {permissions : OperationalPermissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {site : SiteData} (licensed : Licensed language free permissions bound expected source site)
    (boundOk : ∀ entry ∈ bound, LawTypeOk laws language entry) (expectedOk : LawTypeOk laws language expected) :
    LawTypeOk laws language site.focusType ∧ ∀ entry ∈ site.focusBound, LawTypeOk laws language entry := by
  induction licensed with
  | here => exact ⟨expectedOk, boundOk⟩
  | application declared _ _ _ _ parameterSelected parameterTyped _ _ ih =>
    exact ih boundOk (admission.parameters _ (List.fst_mem_of_mem_zipIdx declared) _
      (List.mem_of_getElem? parameterSelected) _ parameterTyped)
  | lambda _ _ ih =>
    exact ih (fun entry member => by
      rcases List.mem_cons.mp member with rfl | other
      · exact expectedOk.1
      · exact boundOk entry other) expectedOk.2
  | multiLambda _ _ ih =>
    exact ih (fun entry member => by
      rcases List.mem_append.mp member with inReplicate | other
      · rw [List.eq_of_mem_replicate inReplicate]; exact expectedOk.1
      · exact boundOk entry other) expectedOk.2
  | directCollection _ _ _ _ _ ih => exact ih boundOk expectedOk.element
  | authoredCollection declared shape _ _ _ _ _ ih =>
    exact ih boundOk (admission.parameters _ (List.fst_mem_of_mem_zipIdx declared) _
      (by rw [((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2]; exact .head _) _ rfl).element

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
