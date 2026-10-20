import Mettapedia.OSLF.MeTTaIL.CanonicalTyping
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Licensed sites at canonical forms

Every licensed occurrence of a term whose path crosses no set has a licensed counterpart in the
term's canonical form: the same typing frames, the canonical form of the focus, and a context
equal up to permutation (`ContextSame`). In a bag the focus may move to another position; the
other elements are the same multiset. A set's canonical form drops repetitions, so the other
elements of a set need not survive as a multiset: `licensed_canon` assumes that the site's
context crosses no set (`OneHoleContext.setFree`), which holds whenever no reduction context lies
inside a set (`NoSetDescent`).

- `ContextSame.fill`: contexts equal up to permutation, filled with permutation-equal terms,
  give permutation-equal terms;
- `replacementRepresentations?_same`: the replacement check sees only permutation-invariant shape;
- `licensed_canon`: every licensed site whose context crosses no set has a licensed counterpart
  at the canonical form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext

/-- The path from the root to the hole crosses no set-kinded collection. -/
def setFree : OneHoleContext → Bool
  | .hole => true
  | .apply _ _ inner _ => inner.setFree
  | .lambda _ inner => inner.setFree
  | .multiLambda _ _ inner => inner.setFree
  | .substBody inner _ => inner.setFree
  | .substReplacement _ inner => inner.setFree
  | .collection kind _ inner _ _ => !decide (kind = .hashSet) && inner.setFree

end Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax DerivedContexts GeneralTypedSites PatternLexOrder
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-- Contexts with the same frames and permutation-equal fixed parts; an unordered collection
frame may move its hole among the same multiset of other elements. -/
inductive ContextSame : OneHoleContext → OneHoleContext → Prop where
  | hole : ContextSame .hole .hole
  | apply {label : String} {before before' after after' : List Pattern} {inner inner' : OneHoleContext} :
      List.Forall₂ Same before before' → ContextSame inner inner' → List.Forall₂ Same after after' →
      ContextSame (.apply label before inner after) (.apply label before' inner' after')
  | lambda {binder : Option String} {inner inner' : OneHoleContext} :
      ContextSame inner inner' → ContextSame (.lambda binder inner) (.lambda binder inner')
  | multiLambda {arity : Nat} {binders : List String} {inner inner' : OneHoleContext} :
      ContextSame inner inner' → ContextSame (.multiLambda arity binders inner) (.multiLambda arity binders inner')
  | ordered {kind : CollType} {before before' after after' : List Pattern} {inner inner' : OneHoleContext}
      {rest : Option String} : Unordered kind = false →
      List.Forall₂ Same before before' → ContextSame inner inner' → List.Forall₂ Same after after' →
      ContextSame (.collection kind before inner after rest) (.collection kind before' inner' after' rest)
  | unordered {kind : CollType} {before before' after after' : List Pattern} {inner inner' : OneHoleContext}
      {rest : Option String} : Unordered kind = true →
      List.Perm ((before ++ after).map canon) ((before' ++ after').map canon) → ContextSame inner inner' →
      ContextSame (.collection kind before inner after rest) (.collection kind before' inner' after' rest)

private theorem forall₂_middle {before before' after after' : List Pattern} {x y : Pattern}
    (front : List.Forall₂ Same before before') (middle : Same x y) (back : List.Forall₂ Same after after') :
    List.Forall₂ Same (before ++ x :: after) (before' ++ y :: after') :=
  List.rel_append front (.cons middle back)

/-- **Contexts equal up to permutation keep permutation-equality.** -/
theorem ContextSame.fill {context context' : OneHoleContext} (same : ContextSame context context')
    {hole hole' : Pattern} (sameHole : Same hole hole') : Same (context.fill hole) (context'.fill hole') := by
  induction same with
  | hole => exact sameHole
  | apply front _ back ih => exact same_apply_congr _ (forall₂_middle front ih back)
  | lambda _ ih => exact same_lambda_congr _ ih
  | multiLambda _ ih => exact same_multiLambda_congr _ _ ih
  | ordered _ front _ back ih => exact same_collection_congr _ _ (forall₂_middle front ih back)
  | @unordered kind before before' after after' inner inner' rest unordered permutation _ ih =>
    unfold Same
    simp only [OneHoleContext.fill, canon_collection]
    congr 1
    apply arrange_perm unordered
    simp only [List.map_append, List.map_cons]
    refine List.perm_middle.trans ?_
    refine List.Perm.trans ?_ List.perm_middle.symm
    rw [show canon (inner.fill hole) = canon (inner'.fill hole') from ih]
    exact .cons _ (by simpa only [List.map_append] using permutation)

theorem matchesParameterRepresentation?_canon (parameter : TermParam) (pattern : Pattern) :
    matchesParameterRepresentation? parameter (canon pattern) = matchesParameterRepresentation? parameter pattern := by
  cases pattern with
  | lambda binder body => rw [canon]; cases parameter <;> cases binder <;> rfl
  | multiLambda arity binders body => rw [canon]; cases parameter <;> cases binders <;> rfl
  | _ => rw [canon] <;> cases parameter <;> rfl

theorem matchesParameterRepresentation?_same (parameter : TermParam) {left right : Pattern} (same : Same left right) :
    matchesParameterRepresentation? parameter left = matchesParameterRepresentation? parameter right := by
  rw [← matchesParameterRepresentation?_canon, same, matchesParameterRepresentation?_canon]

/-- **The replacement check sees only permutation-invariant shape.** -/
theorem replacementRepresentations?_same {language : LanguageDef} {context context' : OneHoleContext}
    (same : ContextSame context context') :
    ∀ (frames : List TypingFrame) {target target' : Pattern}, Same target target' →
      replacementRepresentations? language context frames target =
        replacementRepresentations? language context' frames target' := by
  induction same with
  | hole =>
    intro frames target target' _
    cases frames <;> rfl
  | @apply label before before' after after' inner inner' _ _ _ ih =>
    intro frames target target' sameTarget
    cases frames with
    | nil => rfl
    | cons frame frames =>
      cases frame with
      | application declaration index =>
        simp only [replacementRepresentations?]
        cases (language.terms[declaration]?.bind fun rule => rule.params[index]?) with
        | none => rfl
        | some parameter =>
          simp only
          rw [matchesParameterRepresentation?_same parameter (ContextSame.fill ‹_› sameTarget),
            ih frames sameTarget]
      | _ => rfl
  | lambda _ ih =>
    intro frames target target' sameTarget
    cases frames with
    | nil => rfl
    | cons frame frames =>
      cases frame with
      | lambda => exact ih frames sameTarget
      | _ => rfl
  | multiLambda _ ih =>
    intro frames target target' sameTarget
    cases frames with
    | nil => rfl
    | cons frame frames =>
      cases frame with
      | multiLambda => exact ih frames sameTarget
      | _ => rfl
  | ordered _ _ _ _ ih =>
    intro frames target target' sameTarget
    cases frames with
    | nil => rfl
    | cons frame frames =>
      cases frame with
      | directCollection => exact ih frames sameTarget
      | authoredCollection => exact ih frames sameTarget
      | _ => rfl
  | unordered _ _ _ ih =>
    intro frames target target' sameTarget
    cases frames with
    | nil => rfl
    | cons frame frames =>
      cases frame with
      | directCollection => exact ih frames sameTarget
      | authoredCollection => exact ih frames sameTarget
      | _ => rfl

/-! ## Typing of canonical lists -/

theorem matchesParameterRepresentation_canon {parameter : TermParam} {pattern : Pattern}
    (matched : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (canon pattern) := by
  cases pattern with
  | lambda binder body =>
    rw [canon]; cases parameter <;> cases binder <;> simp_all [MatchesParameterRepresentation]
  | multiLambda arity binders body =>
    rw [canon]; cases parameter <;> cases binders <;> simp_all [MatchesParameterRepresentation]
  | _ => rw [canon]; cases parameter <;> simp_all [MatchesParameterRepresentation]

theorem argumentsHaveTypes_canon {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound arguments parameters →
      ArgumentsHaveTypes language free bound (arguments.map canon) parameters
  | [], _, .nil => .nil
  | _ :: _, _ :: _, .cons representation parameterType head tail =>
    .cons (matchesParameterRepresentation_canon representation) parameterType (hasType_canon head)
      (argumentsHaveTypes_canon tail)

theorem isObjectPatternList_eq_all (items : List Pattern) : isObjectPatternList items = items.all isObjectPattern := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [isObjectPatternList, ih]

theorem isObjectPatternList_canon {items : List Pattern} (objects : isObjectPatternList items = true) :
    isObjectPatternList (items.map canon) = true := by
  rw [isObjectPatternList_eq_all] at objects ⊢
  simpa [List.all_map, Function.comp_def, isObjectPattern_canon] using objects

theorem forall₂_same_canon : ∀ items : List Pattern, List.Forall₂ Same items (items.map canon)
  | [] => .nil
  | item :: rest => .cons (canon_idempotent item).symm (forall₂_same_canon rest)

theorem map_canon_canonical {items : List Pattern} (canonical : ∀ item ∈ items, canon item = item) :
    items.map canon = items := by
  conv_rhs => rw [← List.map_id items]
  exact List.map_congr_left canonical

theorem sortLex_canonical (items : List Pattern) : ∀ item ∈ sortLex (items.map canon), canon item = item := by
  intro item member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp ((sortLex_perm _).mem_iff.mp member)
  exact canon_idempotent original

/-- The arranged canonical elements of a bag or vector, with the focus at its new position and
the other elements forming the same multiset: in a vector the position is unchanged, in a bag the
residual of the sorted list is the sorted residual. A set is excluded: its arrangement drops
repetitions, so the other elements need not survive as a multiset. -/
theorem arrange_select {kind : CollType} (notSet : kind ≠ .hashSet) {elements : List Pattern} {index : Nat}
    {element : Pattern} (selected : elements[index]? = some element) :
    ∃ position, (arrange kind (elements.map canon))[position]? = some (canon element) ∧
      (if Unordered kind then
        List.Perm (((elements.take index) ++ (elements.drop (index + 1))).map canon)
          ((((arrange kind (elements.map canon)).take position) ++
            ((arrange kind (elements.map canon)).drop (position + 1))).map canon)
      else position = index) := by
  obtain ⟨within, found⟩ := List.getElem?_eq_some_iff.mp selected
  cases kind with
  | vec => exact ⟨index, by simp [arrange_vec, List.getElem?_map, selected], by simp [Unordered]⟩
  | hashSet => exact absurd rfl notSet
  | hashBag =>
    obtain ⟨position, inside, atPosition, residual⟩ := sortLex_eraseIdx elements index within
    refine ⟨position, ?_, ?_⟩
    · rw [arrange_bag, List.getElem?_eq_getElem inside, atPosition, found]
    · simp only [Unordered, if_true, arrange_bag]
      rw [← List.eraseIdx_eq_take_drop_succ, ← List.eraseIdx_eq_take_drop_succ, residual,
        map_canon_canonical (sortLex_canonical _)]
      exact (sortLex_perm _).symm

/-! ## Licensed sites -/

/-- The arranged canonical elements of a typed collection keep the element type. -/
theorem arrange_canon_typed {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {kind : CollType} {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType language free bound elements elementType) :
    ElementsHaveType language free bound (arrange kind (elements.map canon)) elementType := by
  apply elementsHaveType_iff.mpr
  intro item member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp ((arrange_mem item).mp member)
  exact hasType_canon (elementsHaveType_iff.mp typed original inOriginal)

/-- The arranged canonical elements of object elements are objects. -/
theorem arrange_canon_objects {kind : CollType} {elements : List Pattern}
    (objects : isObjectPatternList elements = true) :
    isObjectPatternList (arrange kind (elements.map canon)) = true := by
  have mapped := isObjectPatternList_canon objects
  rw [isObjectPatternList_eq_all, List.all_eq_true] at mapped ⊢
  exact fun item member => mapped item ((arrange_mem item).mp member)

/-- **Every licensed site whose context crosses no set has a licensed counterpart at the
canonical form**, with the same typing frames and focus typing, the canonical focus, and a
context equal up to permutation. -/
theorem licensed_canon {language : LanguageDef} {free : FreeTypeContext} {permissions : OperationalPermissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (noSet : site.context.setFree = true) :
    ∃ site', Licensed language free permissions bound expected (canon source) site' ∧
      site'.focus = canon site.focus ∧ site'.focusBound = site.focusBound ∧ site'.focusType = site.focusType ∧
      site'.typingFrames = site.typingFrames ∧ ContextSame site.context site'.context := by
  induction licensed with
  | @here bound expected source enabled object typed =>
    exact ⟨SiteData.here bound expected (canon source),
      .here enabled (by rw [isObjectPattern_canon]; exact object) (hasType_canon typed), rfl, rfl, rfl, rfl, .hole⟩
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted _ ih =>
    simp only [SiteData.wrapApplication, OneHoleContext.setFree] at noSet
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, context⟩ := ih noSet
    refine ⟨inner'.wrapApplication declaration rule.label (arguments.map canon) index, ?_, focus, focusBound,
      focusType, by simp [SiteData.wrapApplication, frames], ?_⟩
    · rw [canon_apply]
      exact .application declared ordinary (argumentsHaveTypes_canon typed) (isObjectPatternList_canon objects)
        (by simp [List.getElem?_map, selected]) parameterSelected parameterTyped permitted licensed'
    · simp only [SiteData.wrapApplication, ← List.map_take, ← List.map_drop]
      exact .apply (forall₂_same_canon _) context (forall₂_same_canon _)
  | @lambda bound binder body domain codomain inner enabled _ ih =>
    simp only [SiteData.wrapLambda, OneHoleContext.setFree] at noSet
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, context⟩ := ih noSet
    refine ⟨inner'.wrapLambda binder domain, ?_, focus, focusBound, focusType, by simp [SiteData.wrapLambda, frames],
      .lambda context⟩
    rw [canon]; exact .lambda enabled licensed'
  | @multiLambda bound arity binders body domain codomain inner enabled _ ih =>
    simp only [SiteData.wrapMultiLambda, OneHoleContext.setFree] at noSet
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, context⟩ := ih noSet
    refine ⟨inner'.wrapMultiLambda arity binders domain, ?_, focus, focusBound, focusType,
      by simp [SiteData.wrapMultiLambda, frames], .multiLambda context⟩
    rw [canon]; exact .multiLambda enabled licensed'
  | @directCollection bound kind elements index element elementType inner permitted typed objects selected _ ih =>
    simp only [SiteData.wrapCollection, OneHoleContext.setFree, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at noSet
    obtain ⟨notSet, innerNoSet⟩ := noSet
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, context⟩ := ih innerNoSet
    obtain ⟨position, atPosition, relation⟩ := arrange_select notSet selected
    refine ⟨inner'.wrapCollection (.directCollection kind) kind (arrange kind (elements.map canon)) position, ?_,
      focus, focusBound, focusType, by simp [SiteData.wrapCollection, frames], ?_⟩
    · rw [canon_collection]
      exact .directCollection permitted (arrange_canon_typed typed) (arrange_canon_objects objects) atPosition licensed'
    · simp only [SiteData.wrapCollection]
      cases kind with
      | vec =>
        simp only [Unordered, Bool.false_eq_true, if_false] at relation
        subst relation
        simp only [arrange_vec, ← List.map_take, ← List.map_drop]
        exact .ordered rfl (forall₂_same_canon _) context (forall₂_same_canon _)
      | hashBag =>
        simp only [Unordered, if_true] at relation
        exact .unordered rfl relation context
      | hashSet => exact absurd rfl notSet
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected _ ih =>
    simp only [SiteData.wrapCollection, OneHoleContext.setFree, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at noSet
    obtain ⟨notSet, innerNoSet⟩ := noSet
    obtain ⟨inner', licensed', focus, focusBound, focusType, frames, context⟩ := ih innerNoSet
    obtain ⟨position, atPosition, relation⟩ := arrange_select notSet selected
    refine ⟨inner'.wrapCollection (.authoredCollection declaration) kind (arrange kind (elements.map canon))
      position, ?_, focus, focusBound, focusType, by simp [SiteData.wrapCollection, frames], ?_⟩
    · rw [canon_collection]
      exact .authoredCollection declared shape permitted (arrange_canon_typed typed) (arrange_canon_objects objects)
        atPosition licensed'
    · simp only [SiteData.wrapCollection]
      cases kind with
      | vec =>
        simp only [Unordered, Bool.false_eq_true, if_false] at relation
        subst relation
        simp only [arrange_vec, ← List.map_take, ← List.map_drop]
        exact .ordered rfl (forall₂_same_canon _) context (forall₂_same_canon _)
      | hashBag =>
        simp only [Unordered, if_true] at relation
        exact .unordered rfl relation context
      | hashSet => exact absurd rfl notSet

/-- No reduction context lies inside a set. -/
def NoSetDescent (permissions : OperationalPermissions) : Prop := CollType.hashSet ∉ permissions.collectionKinds

/-- Without reduction contexts inside sets, every licensed site's context crosses no set. -/
theorem contextSetFree_of_noSetDescent {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} (noDescent : NoSetDescent permissions)
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) : site.context.setFree = true := by
  induction licensed with
  | here => rfl
  | application _ _ _ _ _ _ _ _ _ ih => simpa [SiteData.wrapApplication, OneHoleContext.setFree] using ih
  | lambda _ _ ih => simpa [SiteData.wrapLambda, OneHoleContext.setFree] using ih
  | multiLambda _ _ ih => simpa [SiteData.wrapMultiLambda, OneHoleContext.setFree] using ih
  | @directCollection _ kind _ _ _ _ _ permitted _ _ _ _ ih =>
    have notSet : kind ≠ .hashSet := fun same => noDescent (same ▸ permitted)
    simp [SiteData.wrapCollection, OneHoleContext.setFree, notSet, ih]
  | @authoredCollection _ _ _ _ kind _ _ _ _ _ _ _ permitted _ _ _ _ ih =>
    have notSet : kind ≠ .hashSet := fun same => noDescent (same ▸ permitted)
    simp [SiteData.wrapCollection, OneHoleContext.setFree, notSet, ih]

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
