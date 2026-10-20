import Mettapedia.OSLF.MeTTaIL.WrapperMatching
import Mettapedia.OSLF.MeTTaIL.QuoteDropTyping

/-!
# Wrapper normal forms through reflective substitution

Reflective substitution looks at names through their quote-drop normal forms, which do not see the
wrapper laws: `@{*z}` is opaque to it while `@(*z)` is the name `z`. A wrapper step therefore changes a
term's quote-drop normal form by forward quote-drop and wrapper steps (`normal_qwForward`), and
reflective binder elimination maps the wrapper normal form of its body and a forward chain of its
quoted replacement to a forward chain of quote-drop and wrapper steps, whenever the original result is
inScope (`instantiate_wrapper`). Scope rules out the one case where the two disagree beyond such a
chain: a variable that only the collapsed wrapper exposes would be the eliminated one or a free one,
and the original result would mention it unbound.

Wrapper steps keep scope, binder metadata, object terms, substitution and index lifting; with the
quote-drop steps they form the forward chains `QWForward`, which keep well-sortedness
(`QWForward.openPatternWellSorted`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags ReflectiveSubstitution QuoteDrop
open Mettapedia.GSLT.LanguageDef.WellSorted
open Relation (ReflTransGen)

variable {laws : List Laws} {declaration : ReflectivePresentationDecl}

/-! ## Wrapper steps keep scope, binder metadata and object terms -/

theorem listAll_middle' {f : Pattern → Bool} {before after : List Pattern} {x y : Pattern} (same : f x = f y) :
    (before ++ x :: after).all f = (before ++ y :: after).all f := by
  simp [List.all_append, same]

theorem wellScopedList_middle (depth : Nat) {before after : List Pattern} {x y : Pattern}
    (same : x.isWellScopedAt depth = y.isWellScopedAt depth) :
    Pattern.isWellScopedListAt depth (before ++ x :: after) = Pattern.isWellScopedListAt depth (before ++ y :: after) := by
  induction before with
  | nil => simp [Pattern.isWellScopedListAt, same]
  | cons first rest ih => simp [Pattern.isWellScopedListAt, ih]

theorem WrapperStep.wellScoped {left right : Pattern} (step : WrapperStep laws left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction step with
  | singleton _ => intro depth; simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | empty _ _ => intro depth; simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | apply _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact wellScopedList_middle depth (ih depth)
  | lambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | multiLambda _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact ih _
  | substBody _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | substReplacement _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | element _ ih => intro depth; simp only [Pattern.isWellScopedAt]; exact wellScopedList_middle depth (ih depth)

theorem WrapperStep.binderMetadata_eq {left right : Pattern} (step : WrapperStep laws left right) :
    left.hasCanonicalBinderMetadata = right.hasCanonicalBinderMetadata := by
  have listForm : ∀ items : List Pattern,
      Pattern.hasCanonicalBinderMetadataList items = items.all Pattern.hasCanonicalBinderMetadata := by
    intro items
    induction items with
    | nil => rfl
    | cons item rest ih => simp [Pattern.hasCanonicalBinderMetadataList, ih]
  induction step with
  | singleton _ => simp [Pattern.hasCanonicalBinderMetadata, listForm]
  | empty _ _ => simp [Pattern.hasCanonicalBinderMetadata, listForm]
  | apply _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle' ih
  | lambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | multiLambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substBody _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substReplacement _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | element _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle' ih

theorem WrapperStep.objectPattern_eq {left right : Pattern} (step : WrapperStep laws left right) :
    isObjectPattern left = isObjectPattern right := by
  induction step with
  | singleton _ => simp [isObjectPattern, isObjectPatternList_eq_all]
  | empty _ _ => simp [isObjectPattern, isObjectPatternList_eq_all]
  | apply _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all]; exact listAll_middle' ih
  | lambda _ ih => simp only [isObjectPattern, ih]
  | multiLambda _ ih => simp only [isObjectPattern, ih]
  | substBody _ _ => simp only [isObjectPattern]
  | substReplacement _ _ => simp only [isObjectPattern]
  | element _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all]; rw [listAll_middle' ih]

/-- **One wrapper step keeps well-sortedness** at a type without collections of a flattening kind. -/
theorem WrapperStep.openPatternWellSorted {language : LanguageDef} {free : FreeTypeContext}
    (admission : WrappersTyped laws language) {left right : Pattern} (step : WrapperStep laws left right)
    {bound : List TypeExpr} {type : TypeExpr} (noLaw : NoLawCollections laws type)
    (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  obtain ⟨typed, metadata, object, scope⟩ := sorted
  exact ⟨step.hasType admission object noLaw typed, step.binderMetadata_eq ▸ metadata, step.objectPattern_eq ▸ object,
    by unfold ScopeSafeAt at scope ⊢; rw [← step.wellScoped]; exact scope⟩

/-! ## Substitution and index lifting -/

theorem WrapperStep.substitute {left right : Pattern} (step : WrapperStep laws left right) :
    ∀ assignment : ContextSubstitution.Assignment,
      WrapperStep laws (ContextSubstitution.substitute assignment left) (ContextSubstitution.substitute assignment right) := by
  induction step with
  | singleton found =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_cons, List.map_nil]
    exact .singleton found
  | empty found unit =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_nil]
    exact .empty found unit
  | apply _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .apply (ih assignment)
  | lambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .lambda (ih _)
  | multiLambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .multiLambda (ih _)
  | substBody _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substBody (ih _)
  | substReplacement _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substReplacement (ih _)
  | element _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .element (ih assignment)

theorem WrapperStep.liftBVars {left right : Pattern} (step : WrapperStep laws left right) :
    ∀ cutoff shift, WrapperStep laws (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) := by
  induction step with
  | singleton found =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_cons, List.map_nil]
    exact .singleton found
  | empty found unit =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_nil]
    exact .empty found unit
  | apply _ ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .apply (ih cutoff shift)
  | lambda _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .lambda (ih _ _)
  | multiLambda _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .multiLambda (ih _ _)
  | substBody _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .substBody (ih _ _)
  | substReplacement _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .substReplacement (ih _ _)
  | element _ ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .element (ih cutoff shift)

/-! ## Forward chains of quote-drop and wrapper steps -/

variable (laws declaration) in
/-- One quote-drop or wrapper step, left to right. -/
def QWStep (left right : Pattern) : Prop := QuoteDropStep declaration left right ∨ WrapperStep laws left right

variable (laws declaration) in
/-- A forward chain of quote-drop and wrapper steps. -/
abbrev QWForward (left right : Pattern) : Prop := ReflTransGen (QWStep laws declaration) left right

theorem QWForward.lift {f : Pattern → Pattern}
    (quoteLift : ∀ {a b : Pattern}, QuoteDropStep declaration a b → QuoteDropStep declaration (f a) (f b))
    (wrapperLift : ∀ {a b : Pattern}, WrapperStep laws a b → WrapperStep laws (f a) (f b)) {a b : Pattern}
    (forward : QWForward laws declaration a b) : QWForward laws declaration (f a) (f b) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · exact .tail ih (.inl (quoteLift quoteDrop))
    · exact .tail ih (.inr (wrapperLift wrapped))

theorem QWForward.ofQuoteDrop {a b : Pattern} (forward : QuoteDropForward declaration a b) :
    QWForward laws declaration a b := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.inl step)

theorem QWForward.ofWrapper {a b : Pattern} (forward : WrapperForward laws a b) : QWForward laws declaration a b := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.inr step)

theorem qwForward_pointwise (wrap : List Pattern → Pattern)
    (quoteLift : ∀ (before after : List Pattern) {a b : Pattern}, QuoteDropStep declaration a b →
      QuoteDropStep declaration (wrap (before ++ a :: after)) (wrap (before ++ b :: after)))
    (wrapperLift : ∀ (before after : List Pattern) {a b : Pattern}, WrapperStep laws a b →
      WrapperStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before : List Pattern) {items items' : List Pattern}, List.Forall₂ (QWForward laws declaration) items items' →
      QWForward laws declaration (wrap (before ++ items)) (wrap (before ++ items'))
  | _, [], [], .nil => .refl
  | before, item :: rest, item' :: _, .cons head tail => by
    have first : QWForward laws declaration (wrap (before ++ item :: rest)) (wrap (before ++ item' :: rest)) :=
      QWForward.lift (f := fun x => wrap (before ++ x :: rest)) (fun step => quoteLift before rest step)
        (fun step => wrapperLift before rest step) head
    have later := qwForward_pointwise wrap quoteLift wrapperLift (before ++ [item']) tail
    simp only [List.append_assoc, List.singleton_append] at later
    exact first.trans later

theorem qwForward_apply (label : String) {items items' : List Pattern}
    (each : List.Forall₂ (QWForward laws declaration) items items') :
    QWForward laws declaration (.apply label items) (.apply label items') := by
  simpa using qwForward_pointwise (fun items => .apply label items) (fun _ _ _ _ step => .apply step)
    (fun _ _ _ _ step => .apply step) [] each

theorem qwForward_collection (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (each : List.Forall₂ (QWForward laws declaration) items items') :
    QWForward laws declaration (.collection kind items rest) (.collection kind items' rest) := by
  simpa using qwForward_pointwise (fun items => .collection kind items rest) (fun _ _ _ _ step => .element step)
    (fun _ _ _ _ step => .element step) [] each

theorem qwForward_lambda (binder : Option String) {body body' : Pattern} (forward : QWForward laws declaration body body') :
    QWForward laws declaration (.lambda binder body) (.lambda binder body') :=
  QWForward.lift (f := .lambda binder) (fun step => .lambda step) (fun step => .lambda step) forward

theorem qwForward_multiLambda (arity : Nat) (binders : List String) {body body' : Pattern}
    (forward : QWForward laws declaration body body') :
    QWForward laws declaration (.multiLambda arity binders body) (.multiLambda arity binders body') :=
  QWForward.lift (f := .multiLambda arity binders) (fun step => .multiLambda step) (fun step => .multiLambda step) forward

theorem qwForward_subst {body body' replacement replacement' : Pattern}
    (forwardBody : QWForward laws declaration body body')
    (forwardReplacement : QWForward laws declaration replacement replacement') :
    QWForward laws declaration (.subst body replacement) (.subst body' replacement') :=
  (QWForward.lift (f := fun x => .subst x replacement) (fun step => .substBody step) (fun step => .substBody step)
    forwardBody).trans
    (QWForward.lift (f := fun x => .subst body' x) (fun step => .substReplacement step)
      (fun step => .substReplacement step) forwardReplacement)

theorem QWForward.substitute {left right : Pattern} (forward : QWForward laws declaration left right)
    (assignment : ContextSubstitution.Assignment) :
    QWForward laws declaration (ContextSubstitution.substitute assignment left)
      (ContextSubstitution.substitute assignment right) :=
  QWForward.lift (f := ContextSubstitution.substitute assignment) (fun step => step.substitute assignment)
    (fun step => step.substitute assignment) forward

theorem QWForward.liftBVars {left right : Pattern} (forward : QWForward laws declaration left right)
    (cutoff shift : Nat) :
    QWForward laws declaration (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) :=
  QWForward.lift (f := Substitution.liftBVars cutoff shift) (fun step => step.liftBVars cutoff shift)
    (fun step => step.liftBVars cutoff shift) forward

/-- **Substituting forward-related values gives forward-related results.** -/
theorem qwForward_substitute_assignment : ∀ (pattern : Pattern) {first second : ContextSubstitution.Assignment},
    (∀ index, QWForward laws declaration (first index) (second index)) →
    QWForward laws declaration (ContextSubstitution.substitute first pattern) (ContextSubstitution.substitute second pattern)
  | .bvar index, _, _, pointwise => by simp only [ContextSubstitution.substitute]; exact pointwise index
  | .fvar _, _, _, _ => by simp only [ContextSubstitution.substitute]; exact .refl
  | .apply label arguments, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply qwForward_apply
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact qwForward_substitute_assignment item pointwise
  | .lambda binder body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply qwForward_lambda
    apply qwForward_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl
    · exact QWForward.liftBVars (pointwise _) 0 1
  | .multiLambda arity binders body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply qwForward_multiLambda
    apply qwForward_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl
    · exact QWForward.liftBVars (pointwise _) 0 arity
  | .subst body replacement, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply qwForward_subst
    · apply qwForward_substitute_assignment body
      intro index
      unfold ContextSubstitution.lift
      split
      · exact .refl
      · exact QWForward.liftBVars (pointwise _) 0 1
    · exact qwForward_substitute_assignment replacement pointwise
  | .collection kind elements rest, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply qwForward_collection
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact qwForward_substitute_assignment item pointwise
termination_by pattern => sizeOf pattern

/-- **Ordinary binder elimination maps forward chains to a forward chain.** -/
theorem instantiateBVar_qwForward {replacement replacement' body body' : Pattern}
    (forwardReplacement : QWForward laws declaration replacement replacement')
    (forwardBody : QWForward laws declaration body body') :
    QWForward laws declaration (Substitution.instantiateBVar replacement body)
      (Substitution.instantiateBVar replacement' body') := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar,
    ← ContextSubstitution.substitute_single_eq_instantiateBVar]
  refine (QWForward.substitute forwardBody _).trans (qwForward_substitute_assignment body' ?_)
  intro index
  cases index with
  | zero => exact forwardReplacement
  | succ => exact .refl

/-! ## Scope, indices and drops along forward chains -/

theorem QWStep.wellScoped {left right : Pattern} (step : QWStep laws declaration left right) (depth : Nat) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  rcases step with quoteDrop | wrapped
  · exact quoteDrop.wellScoped depth
  · exact wrapped.wellScoped depth

theorem QWForward.wellScoped {left right : Pattern} (forward : QWForward laws declaration left right) (depth : Nat) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction forward with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step.wellScoped depth)

theorem qwForward_bvar {index : Nat} {other : Pattern} (forward : QWForward laws declaration (.bvar index) other) :
    other = .bvar index := by
  induction forward with
  | refl => rfl
  | tail _ step ih =>
    subst ih
    rcases step with quoteDrop | wrapped
    · cases quoteDrop
    · cases wrapped

theorem qwStep_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {name other : Pattern}
    (step : QWStep laws declaration (.apply declaration.dropConstructor [name]) other) :
    ∃ name', other = .apply declaration.dropConstructor [name'] ∧ QWStep laws declaration name name' := by
  rcases step with quoteDrop | wrapped
  · generalize source : Pattern.apply declaration.dropConstructor [name] = term at quoteDrop
    cases quoteDrop with
    | collapse inner =>
      simp only [Pattern.apply.injEq] at source
      exact absurd source.1 distinct
    | @apply label before after argument changed inner =>
      simp only [Pattern.apply.injEq] at source
      obtain ⟨rfl, same⟩ := source
      match before, after, same with
      | [], [], same =>
        simp only [List.nil_append, List.cons.injEq, and_true] at same
        subst same
        exact ⟨changed, rfl, .inl inner⟩
      | _ :: _, _, same => simp at same
      | [], _ :: _, same => simp at same
    | _ => cases source
  · generalize source : Pattern.apply declaration.dropConstructor [name] = term at wrapped
    cases wrapped with
    | @apply label before after argument changed inner =>
      simp only [Pattern.apply.injEq] at source
      obtain ⟨rfl, same⟩ := source
      match before, after, same with
      | [], [], same =>
        simp only [List.nil_append, List.cons.injEq, and_true] at same
        subst same
        exact ⟨changed, rfl, .inr inner⟩
      | _ :: _, _, same => simp at same
      | [], _ :: _, same => simp at same
    | _ => cases source

theorem qwForward_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {name other : Pattern}
    (forward : QWForward laws declaration (.apply declaration.dropConstructor [name]) other) :
    ∃ name', other = .apply declaration.dropConstructor [name'] ∧ QWForward laws declaration name name' := by
  induction forward with
  | refl => exact ⟨name, rfl, .refl⟩
  | tail _ step ih =>
    obtain ⟨middle, rfl, before⟩ := ih
    obtain ⟨last, rfl, after⟩ := qwStep_drop distinct step
    exact ⟨last, rfl, before.tail after⟩

/-! ## Quote-drop normal forms along wrapper steps -/

/-- **The quote-drop test maps forward chains of the arguments to a forward chain.** -/
theorem finish_qwForward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (label : String)
    {arguments arguments' : List Pattern} (each : List.Forall₂ (QWForward laws declaration) arguments arguments') :
    QWForward laws declaration (finishNormalizeReflectiveApply declaration label arguments)
      (finishNormalizeReflectiveApply declaration label arguments') := by
  by_cases quoted : label = declaration.quoteConstructor
  · subst quoted
    match arguments, arguments', each with
    | [], [], .nil => exact .refl
    | first :: second :: rest, first' :: second' :: rest', each =>
      rw [finish_long, finish_long]
      exact qwForward_apply _ each
    | [argument], [argument'], .cons head .nil =>
      by_cases shaped : ∃ name, argument = .apply declaration.dropConstructor [name]
      · obtain ⟨name, rfl⟩ := shaped
        obtain ⟨name', rfl, forwardName⟩ := qwForward_drop distinct head
        rw [finish_drop, finish_drop]
        simpa using forwardName
      · have notDrop : ∀ name, argument ≠ .apply declaration.dropConstructor [name] :=
          fun name same => shaped ⟨name, same⟩
        rw [finish_quote_plain notDrop]
        have quoted : QWForward laws declaration (.apply declaration.quoteConstructor [argument])
            (.apply declaration.quoteConstructor [argument']) := qwForward_apply _ (.cons head .nil)
        by_cases shaped' : ∃ name', argument' = .apply declaration.dropConstructor [name']
        · obtain ⟨name', rfl⟩ := shaped'
          rw [finish_drop]
          simp only [beq_self_eq_true, Bool.and_self, if_true]
          exact quoted.tail (.inl (.collapse name'))
        · rw [finish_quote_plain fun name same => shaped' ⟨name, same⟩]
          exact quoted
  · have notQuote : label ≠ declaration.quoteConstructor := quoted
    rw [finish_not_quote notQuote, finish_not_quote notQuote]
    exact qwForward_apply label each

/-- **A wrapper step moves the quote-drop normal form by a forward chain.** -/
theorem normal_qwForward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {left right : Pattern}
    (step : WrapperStep laws left right) :
    QWForward laws declaration (normal declaration left) (normal declaration right) := by
  induction step with
  | singleton found =>
    rw [normal_collection]
    simp only [List.map_cons, List.map_nil]
    exact .single (.inr (.singleton found))
  | @empty kind law label found unit =>
    rw [normal_collection, normal_apply, List.map_nil, finish_nil]
    exact .single (.inr (.empty found unit))
  | @apply label before after argument changed _ ih =>
    rw [normal_apply, normal_apply]
    apply finish_qwForward distinct
    simp only [List.map_append, List.map_cons]
    exact List.rel_append (List.forall₂_same.mpr fun _ _ => .refl) (.cons ih (List.forall₂_same.mpr fun _ _ => .refl))
  | lambda _ ih => rw [normal_lambda, normal_lambda]; exact qwForward_lambda _ ih
  | multiLambda _ ih => rw [normal_multiLambda, normal_multiLambda]; exact qwForward_multiLambda _ _ ih
  | substBody _ ih => rw [normal_subst, normal_subst]; exact qwForward_subst ih .refl
  | substReplacement _ ih => rw [normal_subst, normal_subst]; exact qwForward_subst .refl ih
  | element _ ih =>
    rw [normal_collection, normal_collection]
    apply qwForward_collection
    simp only [List.map_append, List.map_cons]
    exact List.rel_append (List.forall₂_same.mpr fun _ _ => .refl) (.cons ih (List.forall₂_same.mpr fun _ _ => .refl))

theorem normal_qwForward_of_forward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (forward : WrapperForward laws left right) :
    QWForward laws declaration (normal declaration left) (normal declaration right) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (normal_qwForward distinct step)

/-- A forward chain of quote-drop and wrapper steps moves the quote-drop normal form by a forward chain:
a quote-drop step keeps it. -/
theorem normal_qwForward_of_qwForward (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (forward : QWForward laws declaration left right) :
    QWForward laws declaration (normal declaration left) (normal declaration right) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · rw [← quoteDrop.normalize_eq distinct]; exact ih
    · exact ih.trans (normal_qwForward distinct wrapped)

/-! ## Reflective binder elimination -/

open ReflectiveInstantiation in
/-- How a name is marked: through its normal form, an index or an opaque name. -/
theorem nameMark_cases (depth : Nat) (replacement name : Pattern) :
    (∃ index, normalizeReflective declaration name = .bvar index ∧
      nameMark declaration depth replacement name =
        (Substitution.instantiateBVarAt depth replacement (.bvar index), index == depth)) ∨
    ((∀ index, normalizeReflective declaration name ≠ .bvar index) ∧
      nameMark declaration depth replacement name = (normalizeReflective declaration name, false)) := by
  unfold nameMark
  cases normalIs : normalizeReflective declaration name with
  | bvar index => exact .inl ⟨index, rfl, rfl⟩
  | _ => exact .inr ⟨fun _ same => (nomatch same), rfl⟩

open ReflectiveInstantiation in
/-- **Reflective binder elimination maps the wrapper normal form of its body and a forward chain of its
quoted replacement to a forward chain**, when the original result is inScope. -/
theorem instantiate_wrapper (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {process process' : Pattern} (forwardProcess : QWForward laws declaration process process') (body : Pattern) :
    ∀ depth, (instantiate declaration depth (.apply declaration.quoteConstructor [process]) body).isWellScopedAt depth →
      QWForward laws declaration (instantiate declaration depth (.apply declaration.quoteConstructor [process]) body)
        (instantiate declaration depth (.apply declaration.quoteConstructor [process']) (wrapperNormal laws body)) := by
  have liftedReplacement : ∀ depth, QWForward laws declaration
      (Substitution.liftBVars 0 depth (.apply declaration.quoteConstructor [process]))
      (Substitution.liftBVars 0 depth (.apply declaration.quoteConstructor [process'])) := fun depth =>
    QWForward.liftBVars (qwForward_apply _ (.cons forwardProcess .nil)) 0 depth
  -- the bound-variable case, shared by plain indices and by names normalizing to an index
  have atIndex : ∀ depth index, QWForward laws declaration
      (Substitution.instantiateBVarAt depth (.apply declaration.quoteConstructor [process]) (.bvar index))
      (Substitution.instantiateBVarAt depth (.apply declaration.quoteConstructor [process']) (.bvar index)) := by
    intro depth index
    unfold Substitution.instantiateBVarAt
    split
    · exact .refl
    · split
      · exact liftedReplacement depth
      · exact .refl
  -- a name whose normal form moves forward to an index that the original result keeps unbound
  have toIndex : ∀ depth {name : Pattern} {index : Nat}, name.isWellScopedAt depth = true →
      QWForward laws declaration name (.bvar index) → index < depth := by
    intro depth name index inScope forward
    rw [forward.wellScoped depth] at inScope
    simpa [Pattern.isWellScopedAt] using inScope
  induction body using Pattern.inductionOn with
  | hbvar index =>
    intro depth _
    rw [wrapperNormal_bvar]
    simp only [instantiate]
    exact atIndex depth index
  | hfvar name => intro depth _; rw [wrapperNormal_fvar]; simp only [instantiate]; exact .refl
  | happly label arguments ih =>
    intro depth inScope
    rw [wrapperNormal_apply]
    by_cases single : arguments.length = 1
    · match arguments, single with
      | [payload], _ =>
        have payloadForward : WrapperForward laws payload (wrapperNormal laws payload) := to_wrapperNormal payload
        by_cases quoted : label = declaration.quoteConstructor
        · subst quoted
          simp only [List.map_cons, List.map_nil]
          rw [instantiate_quote declaration depth _ payload (by simp)] at inScope
          rw [instantiate_quote declaration depth _ payload (by simp),
            instantiate_quote declaration depth _ (wrapperNormal laws payload) (by simp)]
          have normalForward : QWForward laws declaration
              (normalizeReflective declaration (.apply declaration.quoteConstructor [payload]))
              (normalizeReflective declaration (.apply declaration.quoteConstructor [wrapperNormal laws payload])) :=
            normal_qwForward_of_forward distinct (wrapperForward_apply _ (.cons payloadForward .nil))
          rcases nameMark_cases (declaration := declaration) depth (.apply declaration.quoteConstructor [process])
              (.apply declaration.quoteConstructor [payload]) with ⟨index, normalIs, marked⟩ | ⟨notIndex, marked⟩
          · rw [normalIs] at normalForward
            have movedIs := qwForward_bvar normalForward
            rcases nameMark_cases (declaration := declaration) depth (.apply declaration.quoteConstructor [process'])
                (.apply declaration.quoteConstructor [wrapperNormal laws payload]) with
              ⟨index', normalIs', marked'⟩ | ⟨notIndex', _⟩
            · rw [movedIs] at normalIs'
              cases normalIs'
              rw [marked, marked']
              exact atIndex depth index
            · exact absurd movedIs (notIndex' index)
          · rw [marked] at inScope ⊢
            rcases nameMark_cases (declaration := declaration) depth (.apply declaration.quoteConstructor [process'])
                (.apply declaration.quoteConstructor [wrapperNormal laws payload]) with
              ⟨index', normalIs', marked'⟩ | ⟨_, marked'⟩
            · rw [normalIs'] at normalForward
              have below := toIndex depth inScope normalForward
              rw [marked']
              simp only
              unfold Substitution.instantiateBVarAt
              rw [if_pos below]
              exact normalForward
            · rw [marked']
              exact normalForward
        · by_cases dropped : label = declaration.dropConstructor
          · subst dropped
            simp only [List.map_cons, List.map_nil]
            rw [instantiate_drop declaration depth _ payload (beq_false_of_ne' distinct) (by simp)] at inScope
            rw [instantiate_drop declaration depth _ payload (beq_false_of_ne' distinct) (by simp),
              instantiate_drop declaration depth _ (wrapperNormal laws payload) (beq_false_of_ne' distinct) (by simp)]
            have normalForward : QWForward laws declaration (normalizeReflective declaration payload)
                (normalizeReflective declaration (wrapperNormal laws payload)) :=
              normal_qwForward_of_forward distinct payloadForward
            rcases nameMark_cases (declaration := declaration) depth (.apply declaration.quoteConstructor [process])
                payload with ⟨index, normalIs, marked⟩ | ⟨notIndex, marked⟩
            · rw [normalIs] at normalForward
              have movedIs := qwForward_bvar normalForward
              rcases nameMark_cases (declaration := declaration) depth (.apply declaration.quoteConstructor [process'])
                  (wrapperNormal laws payload) with ⟨index', normalIs', marked'⟩ | ⟨notIndex', _⟩
              · rw [movedIs] at normalIs'
                cases normalIs'
                rw [marked, marked']
                simp only
                by_cases same : index = depth
                · subst same
                  have lifted : ∀ inner : Pattern, Substitution.instantiateBVarAt index
                      (.apply declaration.quoteConstructor [inner]) (.bvar index) =
                      .apply declaration.quoteConstructor [Substitution.liftBVars 0 index inner] := by
                    intro inner
                    unfold Substitution.instantiateBVarAt
                    simp [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
                  rw [lifted, lifted]
                  simp only [beq_self_eq_true, dropResult_shaped, if_true]
                  exact QWForward.liftBVars forwardProcess 0 _
                · have plain : ∀ inner : Pattern, Substitution.instantiateBVarAt depth
                      (.apply declaration.quoteConstructor [inner]) (.bvar index) =
                      if index < depth then .bvar index else .bvar (index - 1) := by
                    intro inner
                    unfold Substitution.instantiateBVarAt
                    split <;> simp_all
                  rw [plain, plain]
              · exact absurd movedIs (notIndex' index)
            · rw [marked] at inScope ⊢
              simp only at inScope ⊢
              rw [dropResult_plain _ _ (.inr rfl)] at inScope ⊢
              have originalScoped : (normalizeReflective declaration payload).isWellScopedAt depth = true := by
                simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using inScope
              rcases nameMark_cases (declaration := declaration) depth (.apply declaration.quoteConstructor [process'])
                  (wrapperNormal laws payload) with ⟨index', normalIs', marked'⟩ | ⟨_, marked'⟩
              · rw [normalIs'] at normalForward
                have below := toIndex depth originalScoped normalForward
                rw [marked']
                simp only
                have lowered : Substitution.instantiateBVarAt depth (.apply declaration.quoteConstructor [process'])
                    (.bvar index') = .bvar index' := by
                  unfold Substitution.instantiateBVarAt
                  rw [if_pos below]
                rw [lowered, dropResult_plain _ _ (.inr (by simp; omega))]
                exact qwForward_apply _ (.cons normalForward .nil)
              · rw [marked']
                simp only
                rw [dropResult_plain _ _ (.inr rfl)]
                exact qwForward_apply _ (.cons normalForward .nil)
          · simp only [List.map_cons, List.map_nil]
            rw [instantiate_plainOne declaration depth _ payload (beq_false_of_ne' quoted) (beq_false_of_ne' dropped)]
              at inScope
            rw [instantiate_plainOne declaration depth _ payload (beq_false_of_ne' quoted) (beq_false_of_ne' dropped),
              instantiate_plainOne declaration depth _ (wrapperNormal laws payload) (beq_false_of_ne' quoted)
                (beq_false_of_ne' dropped)]
            have inner : (instantiate declaration depth (.apply declaration.quoteConstructor [process]) payload).isWellScopedAt
                depth = true := by
              simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using inScope
            exact qwForward_apply _ (.cons (ih payload (by simp) depth inner) .nil)
    · rw [instantiate_many declaration depth _ label single] at inScope
      rw [instantiate_many declaration depth _ label single,
        instantiate_many declaration depth _ label (by simpa using single)]
      apply qwForward_apply
      rw [List.map_map]
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      intro argument member
      have inner : (instantiate declaration depth (.apply declaration.quoteConstructor [process]) argument).isWellScopedAt
          depth = true := by
        simp only [Pattern.isWellScopedAt] at inScope
        exact (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope _ (List.mem_map.mpr ⟨argument, member, rfl⟩)
      exact ih argument member depth inner
  | hlambda binder body ih =>
    intro depth inScope
    rw [wrapperNormal_lambda]
    simp only [instantiate, Pattern.isWellScopedAt] at inScope ⊢
    exact qwForward_lambda _ (ih (depth + 1) inScope)
  | hmultiLambda arity binders body ih =>
    intro depth inScope
    rw [wrapperNormal_multiLambda]
    simp only [instantiate, Pattern.isWellScopedAt] at inScope ⊢
    exact qwForward_multiLambda _ _ (ih (depth + arity) inScope)
  | hsubst body value bodyIH valueIH =>
    intro depth inScope
    rw [wrapperNormal_subst]
    simp only [instantiate, Pattern.isWellScopedAt, Bool.and_eq_true] at inScope ⊢
    exact qwForward_subst (bodyIH (depth + 1) inScope.1) (valueIH depth inScope.2)
  | hcollection kind elements rest ih =>
    intro depth inScope
    simp only [instantiate, instantiateList_map'] at inScope ⊢
    have each : ∀ element ∈ elements, QWForward laws declaration
        (instantiate declaration depth (.apply declaration.quoteConstructor [process]) element)
        (instantiate declaration depth (.apply declaration.quoteConstructor [process']) (wrapperNormal laws element)) := by
      intro element member
      have inner : (instantiate declaration depth (.apply declaration.quoteConstructor [process]) element).isWellScopedAt
          depth = true := by
        simp only [Pattern.isWellScopedAt] at inScope
        exact (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope _ (List.mem_map.mpr ⟨element, member, rfl⟩)
      exact ih element member depth inner
    have mapped : QWForward laws declaration
        (.collection kind (elements.map (instantiate declaration depth (.apply declaration.quoteConstructor [process]))) rest)
        (.collection kind ((elements.map (wrapperNormal laws)).map
          (instantiate declaration depth (.apply declaration.quoteConstructor [process']))) rest) := by
      apply qwForward_collection
      rw [List.map_map]
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact List.forall₂_same.mpr each
    cases found : lawFor laws kind with
    | none =>
      rw [wrapperNormal_plain found]
      simp only [instantiate, instantiateList_map']
      exact mapped
    | some law =>
      rw [wrapperNormal_law found]
      unfold wrapFinish
      split
      · rename_i item same
        -- a singleton: the original keeps the wrapper, which then collapses
        obtain ⟨element, rfl, rfl⟩ : ∃ element, elements = [element] ∧ item = wrapperNormal laws element := by
          match elements, same with
          | [element], same => exact ⟨element, rfl, by simpa using same.symm⟩
        simp only [List.map_cons, List.map_nil] at mapped
        exact mapped.tail (.inr (.singleton found))
      · rename_i same
        have empty : elements = [] := by simpa using same
        subst empty
        split
        · rename_i label unit
          simp only [instantiate, instantiateList_map', List.map_nil]
          exact .single (.inr (.empty found unit))
        · simp only [instantiate, instantiateList_map', List.map_nil]
          exact .refl
      · simp only [instantiate, instantiateList_map']
        exact mapped

/-- **The reflective binder operation maps the wrapper normal form of its body and a forward chain of
its quoted replacement to a forward chain**, when the original result is closed. -/
theorem reflectiveOperation_wrapper (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {payload payload' : Pattern} (forwardPayload : QWForward laws declaration payload payload') (body : Pattern)
    (inScope : (ScopedRuleInstantiation.reflectiveOperation declaration (.apply declaration.quoteConstructor [payload])
      body).isWellScopedAt 0 = true) :
    QWForward laws declaration
      (ScopedRuleInstantiation.reflectiveOperation declaration (.apply declaration.quoteConstructor [payload]) body)
      (ScopedRuleInstantiation.reflectiveOperation declaration (.apply declaration.quoteConstructor [payload'])
        (wrapperNormal laws body)) := by
  unfold ScopedRuleInstantiation.reflectiveOperation at inScope ⊢
  simp only [normalizeReflectiveReplacement, beq_self_eq_true, if_true] at inScope ⊢
  exact instantiate_wrapper distinct (normal_qwForward_of_qwForward distinct forwardPayload) body 0 inScope

/-! ## Typing along forward chains -/

/-- **A forward chain of quote-drop and wrapper steps keeps well-sortedness** at a type without
collections of a flattening kind. -/
theorem QWForward.openPatternWellSorted {language : LanguageDef} {free : FreeTypeContext}
    (typedPresentation : QuoteDropTyped language declaration) (admission : WrappersTyped laws language)
    {left right : Pattern} (forward : QWForward laws declaration left right) {bound : List TypeExpr} {type : TypeExpr}
    (noLaw : NoLawCollections laws type) (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  induction forward with
  | refl => exact sorted
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · exact quoteDrop.openPatternWellSorted typedPresentation ih
    · exact wrapped.openPatternWellSorted admission noLaw ih

end Mettapedia.OSLF.MeTTaIL.Wrappers
