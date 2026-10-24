import Mettapedia.OSLF.MeTTaIL.WrapperInstantiation

/-!
# Licensed sites at wrapper normal forms

Every licensed occurrence of a term has a licensed counterpart in the term's wrapper normal form
(`licensed_wrapper`), with the normal form of the focus and the same focus typing. The normal form keeps
every node on the path to the site except a singleton collection of a flattening kind, whose element the
path passes through: that frame disappears, and since the bare constructor is homogeneous its element
has the collection's own type. The context with its fixed parts in normal form and without those frames,
filled with a forward-related term, is reached by a forward chain, and the replacement check survives.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax DerivedContexts GeneralTypedSites ReflectiveSubstitution CanonicalBags CollectionLaws
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

variable {laws : List Laws} {declaration : ReflectivePresentationDecl} {language : LanguageDef}
  {free : FreeTypeContext}

/-! ## Parameter representations along forward chains -/

theorem matchesParameterRepresentation_qwStep {parameter : TermParam} {left right : Pattern}
    (step : QWStep laws declaration left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  rcases step with quoteDrop | wrapped
  · exact QuoteDrop.matchesParameterRepresentation_step quoteDrop matched
  · exact matchesParameterRepresentation_wrapper wrapped matched

theorem matchesParameterRepresentation_qwForward {parameter : TermParam} {left right : Pattern}
    (forward : QWForward laws declaration left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  induction forward with
  | refl => exact matched
  | tail _ step ih => exact matchesParameterRepresentation_qwStep step ih

theorem matchesParameterRepresentation?_qwForward {parameter : TermParam} {left right : Pattern}
    (forward : QWForward laws declaration left right) (matched : matchesParameterRepresentation? parameter left = true) :
    matchesParameterRepresentation? parameter right = true := by
  rw [matchesParameterRepresentation?_eq_true_iff] at matched ⊢
  exact matchesParameterRepresentation_qwForward forward matched

theorem matchesParameterRepresentation_wrapperForward {parameter : TermParam} {left right : Pattern}
    (forward : WrapperForward laws left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  induction forward with
  | refl => exact matched
  | tail _ step ih => exact matchesParameterRepresentation_wrapper step ih

/-! ## Lists in wrapper normal form -/

theorem isObjectPatternList_wrapper {items : List Pattern} (objects : isObjectPatternList items = true) :
    isObjectPatternList (items.map (wrapperNormal laws)) = true := by
  rw [isObjectPatternList_eq_all, List.all_eq_true] at objects ⊢
  intro item member
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
  exact WrapperForward.object (to_wrapperNormal original) (objects original originalIn)

theorem argumentsHaveTypes_wrapper (admission : WrappersTyped laws language) {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam},
      (∀ parameter ∈ parameters, ∀ type, parameterType? parameter = some type → NoLawCollections laws type) →
      isObjectPatternList arguments = true →
      ArgumentsHaveTypes language free bound arguments parameters →
      ArgumentsHaveTypes language free bound (arguments.map (wrapperNormal laws)) parameters
  | [], _, _, _, typed => by cases typed; exact .nil
  | argument :: _, _, noLaw, objects, typed => by
    cases typed with
    | cons representation parameterType head tail =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      exact .cons (matchesParameterRepresentation_wrapperForward (to_wrapperNormal argument) representation)
        parameterType
        (WrapperForward.hasType admission (to_wrapperNormal argument) objects.1
          (noLaw _ (.head _) _ parameterType) head)
        (argumentsHaveTypes_wrapper admission (fun parameter member => noLaw parameter (.tail _ member)) objects.2 tail)

theorem elementsHaveType_wrapper (admission : WrappersTyped laws language) {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr} (noLaw : NoLawCollections laws elementType)
    (objects : isObjectPatternList elements = true) (typed : ElementsHaveType language free bound elements elementType) :
    ElementsHaveType language free bound (elements.map (wrapperNormal laws)) elementType :=
  elementsHaveType_iff.mpr fun item member => by
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [isObjectPatternList_eq_all, List.all_eq_true] at objects
    exact WrapperForward.hasType admission (to_wrapperNormal original) (objects original inOriginal) noLaw
      (elementsHaveType_iff.mp typed original inOriginal)

theorem forall₂_wrapper (items : List Pattern) :
    List.Forall₂ (QWForward laws declaration) items (items.map (wrapperNormal laws)) :=
  List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun item _ => QWForward.ofWrapper (to_wrapperNormal item))

theorem forall₂_take_wrapper (items : List Pattern) (count : Nat) :
    List.Forall₂ (QWForward laws declaration) (items.take count) ((items.map (wrapperNormal laws)).take count) := by
  have shape := forall₂_wrapper (laws := laws) (declaration := declaration) (items.take count)
  simpa [List.map_take] using shape

theorem forall₂_drop_wrapper (items : List Pattern) (count : Nat) :
    List.Forall₂ (QWForward laws declaration) (items.drop count) ((items.map (wrapperNormal laws)).drop count) := by
  have shape := forall₂_wrapper (laws := laws) (declaration := declaration) (items.drop count)
  simpa [List.map_drop] using shape

/-! ## Licensed sites -/

/-- **Every licensed site has a licensed counterpart at the wrapper normal form**: the normal focus with
the same focus typing, a context that keeps forward chains, and the replacement check. -/
theorem licensed_wrapper (admission : WrappersTyped laws language) {permissions : OperationalPermissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) (noLaw : NoLawCollections laws expected) :
    ∃ site', Licensed language free permissions bound expected (wrapperNormal laws source) site' ∧
      site'.focus = wrapperNormal laws site.focus ∧ site'.focusBound = site.focusBound ∧
      site'.focusType = site.focusType ∧ NoLawCollections laws site.focusType ∧
      (∀ hole hole', QWForward laws declaration hole hole' →
        QWForward laws declaration (site.context.fill hole) (site'.context.fill hole')) ∧
      (∀ (target : LanguageDef) hole hole', QWForward laws declaration hole hole' →
        replacementRepresentations? target site.context site.typingFrames hole = true →
        replacementRepresentations? target site'.context site'.typingFrames hole' = true) := by
  induction licensed with
  | @here bound expected source enabled object typed =>
    refine ⟨SiteData.here bound expected (wrapperNormal laws source),
      .here enabled (WrapperForward.object (to_wrapperNormal source) object)
        (WrapperForward.hasType admission (to_wrapperNormal source) object noLaw typed),
      rfl, rfl, rfl, noLaw, fun _ _ forward => forward, ?_⟩
    intro target hole hole' _ _
    rfl
  | @application bound rule declarationIndex index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted _ ih =>
    have parametersOk := admission.parameters rule (List.fst_mem_of_mem_zipIdx declared) ordinary
    obtain ⟨inner', licensed', focus, focusBound, focusType, focusOk, fill, accepts⟩ :=
      ih (parametersOk parameter (List.mem_of_getElem? parameterSelected) parameterType parameterTyped)
    refine ⟨inner'.wrapApplication declarationIndex rule.label (arguments.map (wrapperNormal laws)) index, ?_, focus,
      focusBound, focusType, focusOk, ?_, ?_⟩
    · rw [wrapperNormal_apply]
      exact .application declared ordinary (argumentsHaveTypes_wrapper admission parametersOk objects typed)
        (isObjectPatternList_wrapper objects) (by simp [List.getElem?_map, selected]) parameterSelected parameterTyped
        permitted licensed'
    · intro hole hole' forward
      simp only [SiteData.wrapApplication, OneHoleContext.fill]
      exact qwForward_apply _ (List.rel_append (forall₂_take_wrapper _ _)
        (.cons (fill hole hole' forward) (forall₂_drop_wrapper _ _)))
    · intro target hole hole' forward accepted
      simp only [SiteData.wrapApplication, replacementRepresentations?] at accepted ⊢
      cases lookup : (target.terms[declarationIndex]?.bind fun rule => rule.params[index]?) with
      | none => rw [lookup] at accepted; cases accepted
      | some found =>
        rw [lookup] at accepted
        simp only [Bool.and_eq_true] at accepted ⊢
        exact ⟨matchesParameterRepresentation?_qwForward (fill hole hole' forward) accepted.1,
          accepts target hole hole' forward accepted.2⟩
  | @lambda bound binder body domain codomain inner enabled _ ih =>
    obtain ⟨inner', licensed', focus, focusBound, focusType, focusOk, fill, accepts⟩ := ih noLaw.2
    refine ⟨inner'.wrapLambda binder domain, ?_, focus, focusBound, focusType, focusOk, ?_, ?_⟩
    · rw [wrapperNormal_lambda]; exact .lambda enabled licensed'
    · intro hole hole' forward
      simp only [SiteData.wrapLambda, OneHoleContext.fill]
      exact qwForward_lambda _ (fill hole hole' forward)
    · intro target hole hole' forward accepted
      simp only [SiteData.wrapLambda, replacementRepresentations?] at accepted ⊢
      exact accepts target hole hole' forward accepted
  | @multiLambda bound arity binders body domain codomain inner enabled _ ih =>
    obtain ⟨inner', licensed', focus, focusBound, focusType, focusOk, fill, accepts⟩ := ih noLaw.2
    refine ⟨inner'.wrapMultiLambda arity binders domain, ?_, focus, focusBound, focusType, focusOk, ?_, ?_⟩
    · rw [wrapperNormal_multiLambda]; exact .multiLambda enabled licensed'
    · intro hole hole' forward
      simp only [SiteData.wrapMultiLambda, OneHoleContext.fill]
      exact qwForward_multiLambda _ _ (fill hole hole' forward)
    · intro target hole hole' forward accepted
      simp only [SiteData.wrapMultiLambda, replacementRepresentations?] at accepted ⊢
      exact accepts target hole hole' forward accepted
  | @directCollection bound kind elements index element elementType inner permitted typed objects selected _ ih =>
    obtain ⟨plain, elementOk⟩ := noLaw
    obtain ⟨inner', licensed', focus, focusBound, focusType, focusOk, fill, accepts⟩ := ih elementOk
    refine ⟨inner'.wrapCollection (.directCollection kind) kind (elements.map (wrapperNormal laws)) index, ?_, focus,
      focusBound, focusType, focusOk, ?_, ?_⟩
    · rw [wrapperNormal_plain plain]
      exact .directCollection permitted (elementsHaveType_wrapper admission elementOk objects typed)
        (isObjectPatternList_wrapper objects) (by simp [List.getElem?_map, selected]) licensed'
    · intro hole hole' forward
      simp only [SiteData.wrapCollection, OneHoleContext.fill]
      exact qwForward_collection _ _
        (List.rel_append (forall₂_take_wrapper _ _) (.cons (fill hole hole' forward) (forall₂_drop_wrapper _ _)))
    · intro target hole hole' forward accepted
      simp only [SiteData.wrapCollection, replacementRepresentations?] at accepted ⊢
      exact accepts target hole hole' forward accepted
  | @authoredCollection bound rule declarationIndex parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected _ ih =>
    have elementOk := admission.bareElements rule (List.fst_mem_of_mem_zipIdx declared) parameterName kind elementType
      ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2
    obtain ⟨inner', licensed', focus, focusBound, focusType, focusOk, fill, accepts⟩ := ih elementOk
    -- the frame kept: a kind without laws, or at least two elements
    have kept : (lawFor laws kind = none ∨ 2 ≤ elements.length) →
        ∃ site', Licensed language free permissions bound (.base rule.category) (wrapperNormal laws (.collection kind elements none))
          site' ∧ site'.focus = wrapperNormal laws inner.focus ∧ site'.focusBound = inner.focusBound ∧
          site'.focusType = inner.focusType ∧ NoLawCollections laws inner.focusType ∧
          (∀ hole hole', QWForward laws declaration hole hole' →
            QWForward laws declaration
              ((inner.wrapCollection (.authoredCollection declarationIndex) kind elements index).context.fill hole)
              (site'.context.fill hole')) ∧
          (∀ (target : LanguageDef) hole hole', QWForward laws declaration hole hole' →
            replacementRepresentations? target
              (inner.wrapCollection (.authoredCollection declarationIndex) kind elements index).context
              (inner.wrapCollection (.authoredCollection declarationIndex) kind elements index).typingFrames hole = true →
            replacementRepresentations? target site'.context site'.typingFrames hole' = true) := by
      intro long
      refine ⟨inner'.wrapCollection (.authoredCollection declarationIndex) kind (elements.map (wrapperNormal laws)) index,
        ?_, focus, focusBound, focusType, focusOk, ?_, ?_⟩
      · rw [wrapperNormal_collection_long (long.imp_right fun two => .inr two)]
        exact .authoredCollection declared shape permitted (elementsHaveType_wrapper admission elementOk objects typed)
          (isObjectPatternList_wrapper objects) (by simp [List.getElem?_map, selected]) licensed'
      · intro hole hole' forward
        simp only [SiteData.wrapCollection, OneHoleContext.fill]
        exact qwForward_collection _ _
          (List.rel_append (forall₂_take_wrapper _ _) (.cons (fill hole hole' forward) (forall₂_drop_wrapper _ _)))
      · intro target hole hole' forward accepted
        simp only [SiteData.wrapCollection, replacementRepresentations?] at accepted ⊢
        exact accepts target hole hole' forward accepted
    cases found : lawFor laws kind with
    | none => exact kept (.inl found)
    | some law =>
      match elements, index, selected with
      | [single], 0, selected =>
        -- a singleton: its frame disappears, and its element has the collection's type
        simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
        subst selected
        have same := admission.homogeneous law kind found rule (List.fst_mem_of_mem_zipIdx declared) parameterName
          elementType ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2
        subst same
        refine ⟨inner', ?_, focus, focusBound, focusType, focusOk, ?_, ?_⟩
        · rw [wrapperNormal_law found]
          simpa [wrapFinish] using licensed'
        · intro hole hole' forward
          simp only [SiteData.wrapCollection, OneHoleContext.fill, List.take_zero, List.drop_succ_cons, List.drop_zero,
            List.nil_append]
          exact (Relation.ReflTransGen.single (.inr (.singleton found))).trans (fill hole hole' forward)
        · intro target hole hole' forward accepted
          simp only [SiteData.wrapCollection, replacementRepresentations?] at accepted
          exact accepts target hole hole' forward accepted
      | _ :: _ :: _, _, _ => exact kept (.inr (by simp))
      | [], _, selected => simp at selected
      | [_], _ + 1, selected => simp at selected

end Mettapedia.OSLF.MeTTaIL.Wrappers
