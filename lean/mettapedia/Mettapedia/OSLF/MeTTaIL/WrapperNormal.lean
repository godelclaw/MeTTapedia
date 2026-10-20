import Mettapedia.OSLF.MeTTaIL.WrapperTyping

/-!
# The wrapper normal form

`wrapperNormal` collapses, bottom up, every singleton collection of a flattening kind to its element
and every empty one to the declared unit; every other node keeps its shape. It is reached by a forward
chain of wrapper steps (`to_wrapperNormal`), it is idempotent, it commutes with renamings and index
lifting, and it keeps scope and free names. A forward chain keeps the type of an object term at a type
without collections of a flattening kind (`WrapperForward.hasType`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open Relation (ReflTransGen)

variable (laws : List Laws)

/-- **The wrapper normal form**: bottom up, a singleton collection of a flattening kind is its element
and an empty one is the declared unit. -/
def wrapperNormal : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map wrapperNormal)
  | .lambda binder body => .lambda binder (wrapperNormal body)
  | .multiLambda arity binders body => .multiLambda arity binders (wrapperNormal body)
  | .subst body replacement => .subst (wrapperNormal body) (wrapperNormal replacement)
  | .collection kind elements rest =>
      match lawFor laws kind with
      | some law => wrapFinish law kind (elements.map wrapperNormal) rest
      | none => .collection kind (elements.map wrapperNormal) rest
decreasing_by all_goals sizeOf_pattern_dec

/-- A forward chain of wrapper steps. -/
abbrev WrapperForward (left right : Pattern) : Prop := ReflTransGen (WrapperStep laws) left right

variable {laws}

/-! ## Equations -/

theorem wrapperNormal_bvar (index : Nat) : wrapperNormal laws (.bvar index) = .bvar index := by
  rw [wrapperNormal]

theorem wrapperNormal_fvar (name : String) : wrapperNormal laws (.fvar name) = .fvar name := by
  rw [wrapperNormal]

theorem wrapperNormal_apply (label : String) (arguments : List Pattern) :
    wrapperNormal laws (.apply label arguments) = .apply label (arguments.map (wrapperNormal laws)) := by
  rw [wrapperNormal]

theorem wrapperNormal_lambda (binder : Option String) (body : Pattern) :
    wrapperNormal laws (.lambda binder body) = .lambda binder (wrapperNormal laws body) := by
  rw [wrapperNormal]

theorem wrapperNormal_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    wrapperNormal laws (.multiLambda arity binders body) = .multiLambda arity binders (wrapperNormal laws body) := by
  rw [wrapperNormal]

theorem wrapperNormal_subst (body replacement : Pattern) :
    wrapperNormal laws (.subst body replacement) = .subst (wrapperNormal laws body) (wrapperNormal laws replacement) := by
  rw [wrapperNormal]

theorem wrapperNormal_law {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (elements : List Pattern) (rest : Option String) :
    wrapperNormal laws (.collection kind elements rest) =
      wrapFinish law kind (elements.map (wrapperNormal laws)) rest := by
  rw [wrapperNormal, found]

theorem wrapperNormal_plain {kind : CollType} (none : lawFor laws kind = none) (elements : List Pattern)
    (rest : Option String) :
    wrapperNormal laws (.collection kind elements rest) = .collection kind (elements.map (wrapperNormal laws)) rest := by
  rw [wrapperNormal, none]

/-- A collection that keeps its shape: of a kind without laws, with a rest, or with at least two
elements. -/
theorem wrapperNormal_collection_long {kind : CollType} {elements : List Pattern} {rest : Option String}
    (long : lawFor laws kind = none ∨ rest.isSome ∨ 2 ≤ elements.length) :
    wrapperNormal laws (.collection kind elements rest) = .collection kind (elements.map (wrapperNormal laws)) rest := by
  cases found : lawFor laws kind with
  | none => exact wrapperNormal_plain found elements rest
  | some law =>
    rw [wrapperNormal_law found]
    rw [found] at long
    simp only [reduceCtorEq, false_or] at long
    match rest, elements, long with
    | some _, _, _ => rfl
    | none, _ :: _ :: _, _ => rfl
    | none, [], .inr two => simp at two
    | none, [_], .inr two => simp at two
    | none, _, .inl isSome => simp at isSome

/-! ## Forward chains -/

theorem WrapperForward.lift {f : Pattern → Pattern}
    (lift : ∀ {a b : Pattern}, WrapperStep laws a b → WrapperStep laws (f a) (f b)) {a b : Pattern}
    (forward : WrapperForward laws a b) : WrapperForward laws (f a) (f b) := by
  induction forward with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (lift step)

theorem wrapperForward_pointwise (wrap : List Pattern → Pattern)
    (lift : ∀ (before after : List Pattern) {a b : Pattern}, WrapperStep laws a b →
      WrapperStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before : List Pattern) {items items' : List Pattern}, List.Forall₂ (WrapperForward laws) items items' →
      WrapperForward laws (wrap (before ++ items)) (wrap (before ++ items'))
  | _, [], [], .nil => .refl
  | before, item :: rest, item' :: _, .cons head tail => by
    have first : WrapperForward laws (wrap (before ++ item :: rest)) (wrap (before ++ item' :: rest)) :=
      WrapperForward.lift (f := fun x => wrap (before ++ x :: rest)) (fun step => lift before rest step) head
    have later := wrapperForward_pointwise wrap lift (before ++ [item']) tail
    simp only [List.append_assoc, List.singleton_append] at later
    exact first.trans later

theorem wrapperForward_apply (label : String) {items items' : List Pattern}
    (each : List.Forall₂ (WrapperForward laws) items items') :
    WrapperForward laws (.apply label items) (.apply label items') := by
  simpa using wrapperForward_pointwise (fun items => .apply label items) (fun _ _ _ _ step => .apply step) [] each

theorem wrapperForward_collection (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (each : List.Forall₂ (WrapperForward laws) items items') :
    WrapperForward laws (.collection kind items rest) (.collection kind items' rest) := by
  simpa using wrapperForward_pointwise (fun items => .collection kind items rest) (fun _ _ _ _ step => .element step)
    [] each

theorem wrapperForward_lambda (binder : Option String) {body body' : Pattern} (forward : WrapperForward laws body body') :
    WrapperForward laws (.lambda binder body) (.lambda binder body') :=
  WrapperForward.lift (f := .lambda binder) (fun step => .lambda step) forward

theorem wrapperForward_multiLambda (arity : Nat) (binders : List String) {body body' : Pattern}
    (forward : WrapperForward laws body body') :
    WrapperForward laws (.multiLambda arity binders body) (.multiLambda arity binders body') :=
  WrapperForward.lift (f := .multiLambda arity binders) (fun step => .multiLambda step) forward

theorem wrapperForward_subst {body body' replacement replacement' : Pattern} (forwardBody : WrapperForward laws body body')
    (forwardReplacement : WrapperForward laws replacement replacement') :
    WrapperForward laws (.subst body replacement) (.subst body' replacement') :=
  (WrapperForward.lift (f := fun x => .subst x replacement) (fun step => .substBody step) forwardBody).trans
    (WrapperForward.lift (f := fun x => .subst body' x) (fun step => .substReplacement step) forwardReplacement)

theorem forall₂_map_self {f : Pattern → Pattern} :
    ∀ {items : List Pattern}, (∀ item ∈ items, WrapperForward laws item (f item)) →
      List.Forall₂ (WrapperForward laws) items (items.map f)
  | [], _ => .nil
  | _ :: _, each => .cons (each _ (by simp)) (forall₂_map_self fun item member => each item (by simp [member]))

/-- The wrapper collapse of a collection is a forward chain. -/
theorem wrapFinish_forward {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (items : List Pattern) (rest : Option String) :
    WrapperForward laws (.collection kind items rest) (wrapFinish law kind items rest) := by
  unfold wrapFinish
  split
  · exact .single (.singleton found)
  · split
    · rename_i label unit
      exact .single (.empty found unit)
    · exact .refl
  · exact .refl

/-- **Every term reaches its wrapper normal form by a forward chain.** -/
theorem to_wrapperNormal : ∀ pattern : Pattern, WrapperForward laws pattern (wrapperNormal laws pattern)
  | .bvar index => by rw [wrapperNormal_bvar]
  | .fvar name => by rw [wrapperNormal_fvar]
  | .apply label arguments => by
    rw [wrapperNormal_apply]
    exact wrapperForward_apply label (forall₂_map_self fun item member =>
      have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      to_wrapperNormal item)
  | .lambda binder body => by rw [wrapperNormal_lambda]; exact wrapperForward_lambda binder (to_wrapperNormal body)
  | .multiLambda arity binders body => by
    rw [wrapperNormal_multiLambda]; exact wrapperForward_multiLambda arity binders (to_wrapperNormal body)
  | .subst body replacement => by
    rw [wrapperNormal_subst]; exact wrapperForward_subst (to_wrapperNormal body) (to_wrapperNormal replacement)
  | .collection kind elements rest => by
    have mapped : WrapperForward laws (.collection kind elements rest)
        (.collection kind (elements.map (wrapperNormal laws)) rest) :=
      wrapperForward_collection kind rest (forall₂_map_self fun item member =>
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        to_wrapperNormal item)
    cases found : lawFor laws kind with
    | none => rw [wrapperNormal_plain found]; exact mapped
    | some law => rw [wrapperNormal_law found]; exact mapped.trans (wrapFinish_forward found _ rest)
termination_by pattern => sizeOf pattern

/-! ## Idempotence -/

/-- Wrapper normal forms, hereditarily: every collection of a flattening kind keeps its shape. -/
inductive Collapsed (laws : List Laws) : Pattern → Prop where
  | bvar (index : Nat) : Collapsed laws (.bvar index)
  | fvar (name : String) : Collapsed laws (.fvar name)
  | apply {label : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments, Collapsed laws argument) → Collapsed laws (.apply label arguments)
  | lambda {binder : Option String} {body : Pattern} : Collapsed laws body → Collapsed laws (.lambda binder body)
  | multiLambda {arity : Nat} {binders : List String} {body : Pattern} :
      Collapsed laws body → Collapsed laws (.multiLambda arity binders body)
  | subst {body replacement : Pattern} :
      Collapsed laws body → Collapsed laws replacement → Collapsed laws (.subst body replacement)
  | collectionPlain {kind : CollType} {items : List Pattern} {rest : Option String} :
      (∀ item ∈ items, Collapsed laws item) → lawFor laws kind = none → Collapsed laws (.collection kind items rest)
  | collectionLaw {kind : CollType} {items : List Pattern} {rest : Option String} {law : Laws} :
      (∀ item ∈ items, Collapsed laws item) → lawFor laws kind = some law →
      wrapFinish law kind items rest = .collection kind items rest → Collapsed laws (.collection kind items rest)

theorem Collapsed.fixed {pattern : Pattern} (collapsed : Collapsed laws pattern) :
    wrapperNormal laws pattern = pattern := by
  induction collapsed with
  | bvar index => rw [wrapperNormal_bvar]
  | fvar name => rw [wrapperNormal_fvar]
  | apply _ ih => rw [wrapperNormal_apply, List.map_congr_left ih, List.map_id']
  | lambda _ ih => rw [wrapperNormal_lambda, ih]
  | multiLambda _ ih => rw [wrapperNormal_multiLambda, ih]
  | subst _ _ bodyIH replacementIH => rw [wrapperNormal_subst, bodyIH, replacementIH]
  | collectionPlain _ none ih => rw [wrapperNormal_plain none, List.map_congr_left ih, List.map_id']
  | collectionLaw _ found settled ih => rw [wrapperNormal_law found, List.map_congr_left ih, List.map_id', settled]

theorem collapsed_wrapFinish {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    {items : List Pattern} (each : ∀ item ∈ items, Collapsed laws item) (rest : Option String) :
    Collapsed laws (wrapFinish law kind items rest) := by
  match rest, items, each with
  | none, [item], each => exact each item (by simp)
  | none, [], _ =>
    cases unit : law.unit with
    | some label => simp only [wrapFinish, unit]; exact .apply (by simp)
    | none =>
      have settled : wrapFinish law kind [] none = .collection kind [] none := by simp only [wrapFinish, unit]
      rw [settled]
      exact .collectionLaw (by simp) found settled
  | none, _ :: _ :: _, each => exact .collectionLaw each found rfl
  | some _, _, each => exact .collectionLaw each found rfl

/-- **The wrapper normal form is collapsed.** -/
theorem collapsed_wrapperNormal : ∀ pattern : Pattern, Collapsed laws (wrapperNormal laws pattern)
  | .bvar index => by rw [wrapperNormal_bvar]; exact .bvar index
  | .fvar name => by rw [wrapperNormal_fvar]; exact .fvar name
  | .apply label arguments => by
    rw [wrapperNormal_apply]
    refine .apply fun argument member => ?_
    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
    have : sizeOf original < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem originalIn; simp only [Pattern.apply.sizeOf_spec]; omega
    exact collapsed_wrapperNormal original
  | .lambda binder body => by rw [wrapperNormal_lambda]; exact .lambda (collapsed_wrapperNormal body)
  | .multiLambda arity binders body => by
    rw [wrapperNormal_multiLambda]; exact .multiLambda (collapsed_wrapperNormal body)
  | .subst body replacement => by
    rw [wrapperNormal_subst]; exact .subst (collapsed_wrapperNormal body) (collapsed_wrapperNormal replacement)
  | .collection kind elements rest => by
    have each : ∀ item ∈ elements.map (wrapperNormal laws), Collapsed laws item := by
      intro item member
      obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
      have : sizeOf original < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem originalIn; simp only [Pattern.collection.sizeOf_spec]; omega
      exact collapsed_wrapperNormal original
    cases found : lawFor laws kind with
    | none => rw [wrapperNormal_plain found]; exact .collectionPlain each found
    | some law => rw [wrapperNormal_law found]; exact collapsed_wrapFinish found each rest
termination_by pattern => sizeOf pattern

theorem wrapperNormal_idempotent (pattern : Pattern) :
    wrapperNormal laws (wrapperNormal laws pattern) = wrapperNormal laws pattern :=
  (collapsed_wrapperNormal pattern).fixed

/-! ## Renamings and index lifting -/

theorem wrapFinish_map {f : Pattern → Pattern} {law : Laws} (kind : CollType) (items : List Pattern)
    (rest : Option String) (onUnit : ∀ label, f (.apply label []) = .apply label [])
    (onCollection : ∀ items rest, f (.collection kind items rest) = .collection kind (items.map f) rest) :
    wrapFinish law kind (items.map f) rest = f (wrapFinish law kind items rest) := by
  unfold wrapFinish
  match rest, items with
  | none, [item] => rfl
  | none, [] =>
    simp only [List.map_nil]
    split
    · rw [onUnit]
    · rw [onCollection]; rfl
  | none, _ :: _ :: _ => simp only [List.map_cons]; rw [onCollection]; rfl
  | some name, items => simp only; rw [onCollection]

/-- **The wrapper normal form commutes with every renaming.** -/
theorem wrapperNormal_substitute_renaming (pattern : Pattern) :
    ∀ {assignment : ContextSubstitution.Assignment}, QuoteDrop.Renaming assignment →
      wrapperNormal laws (ContextSubstitution.substitute assignment pattern) =
        ContextSubstitution.substitute assignment (wrapperNormal laws pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro assignment renames
    obtain ⟨other, found⟩ := renames index
    simp only [ContextSubstitution.substitute, found, wrapperNormal_bvar]
  | hfvar name => intro assignment _; simp only [ContextSubstitution.substitute, wrapperNormal_fvar]
  | happly label arguments ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, wrapperNormal_apply,
      List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member renames
  | hlambda binder body ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, wrapperNormal_lambda, ih (renames.lift 1)]
  | hmultiLambda arity binders body ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, wrapperNormal_multiLambda, ih (renames.lift arity)]
  | hsubst body replacement bodyIH replacementIH =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, wrapperNormal_subst, bodyIH (renames.lift 1), replacementIH renames]
  | hcollection kind elements rest ih =>
    intro assignment renames
    have inner : (elements.map (ContextSubstitution.substitute assignment)).map (wrapperNormal laws) =
        (elements.map (wrapperNormal laws)).map (ContextSubstitution.substitute assignment) := by
      simp only [List.map_map]
      exact List.map_congr_left fun element member => ih element member renames
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    cases found : lawFor laws kind with
    | none =>
      rw [wrapperNormal_plain found, wrapperNormal_plain found, inner]
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    | some law =>
      rw [wrapperNormal_law found, wrapperNormal_law found, inner]
      exact wrapFinish_map kind _ rest (fun label => by simp [ContextSubstitution.substitute])
        (fun items rest => by simp [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map])

/-- **The wrapper normal form commutes with index lifting.** -/
theorem wrapperNormal_liftBVars (pattern : Pattern) :
    ∀ cutoff shift, wrapperNormal laws (Substitution.liftBVars cutoff shift pattern) =
      Substitution.liftBVars cutoff shift (wrapperNormal laws pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro cutoff shift
    by_cases high : index ≥ cutoff <;> simp [Substitution.liftBVars, high, wrapperNormal_bvar]
  | hfvar name => intro cutoff shift; simp only [Substitution.liftBVars, wrapperNormal_fvar]
  | happly label arguments ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, wrapperNormal_apply, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member cutoff shift
  | hlambda binder body ih => intro cutoff shift; simp only [Substitution.liftBVars, wrapperNormal_lambda, ih]
  | hmultiLambda arity binders body ih =>
    intro cutoff shift; simp only [Substitution.liftBVars, wrapperNormal_multiLambda, ih]
  | hsubst body replacement bodyIH replacementIH =>
    intro cutoff shift; simp only [Substitution.liftBVars, wrapperNormal_subst, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    intro cutoff shift
    have inner : (elements.map (Substitution.liftBVars cutoff shift)).map (wrapperNormal laws) =
        (elements.map (wrapperNormal laws)).map (Substitution.liftBVars cutoff shift) := by
      simp only [List.map_map]
      exact List.map_congr_left fun element member => ih element member cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
    cases found : lawFor laws kind with
    | none =>
      rw [wrapperNormal_plain found, wrapperNormal_plain found, inner]
      simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
    | some law =>
      rw [wrapperNormal_law found, wrapperNormal_law found, inner]
      exact wrapFinish_map kind _ rest (fun label => by simp [Substitution.liftBVars])
        (fun items rest => by simp [Substitution.liftBVars, Substitution.liftBVarsList_eq_map])

/-! ## Scope and names -/

theorem wellScopedList_map (depth : Nat) (f : Pattern → Pattern) :
    ∀ items : List Pattern, (∀ item ∈ items, (f item).isWellScopedAt depth = item.isWellScopedAt depth) →
      Pattern.isWellScopedListAt depth (items.map f) = Pattern.isWellScopedListAt depth items
  | [], _ => rfl
  | item :: rest, each => by
    simp [Pattern.isWellScopedListAt, each item (by simp),
      wellScopedList_map depth f rest fun other member => each other (by simp [member])]

theorem wrapFinish_wellScoped {law : Laws} (kind : CollType) (items : List Pattern) (rest : Option String)
    (depth : Nat) :
    (wrapFinish law kind items rest).isWellScopedAt depth = (Pattern.collection kind items rest).isWellScopedAt depth := by
  unfold wrapFinish
  split
  · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  · split
    · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
    · rfl
  · rfl

/-- **The wrapper normal form keeps scope.** -/
theorem wrapperNormal_wellScoped (pattern : Pattern) :
    ∀ depth, (wrapperNormal laws pattern).isWellScopedAt depth = pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; rw [wrapperNormal_bvar]
  | hfvar name => intro depth; rw [wrapperNormal_fvar]
  | happly label arguments ih =>
    intro depth
    rw [wrapperNormal_apply]
    simp only [Pattern.isWellScopedAt]
    exact wellScopedList_map depth _ arguments fun argument member => ih argument member depth
  | hlambda binder body ih => intro depth; rw [wrapperNormal_lambda]; simp only [Pattern.isWellScopedAt, ih]
  | hmultiLambda arity binders body ih =>
    intro depth; rw [wrapperNormal_multiLambda]; simp only [Pattern.isWellScopedAt, ih]
  | hsubst body replacement bodyIH replacementIH =>
    intro depth; rw [wrapperNormal_subst]; simp only [Pattern.isWellScopedAt, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    intro depth
    have mapped : (Pattern.collection kind (elements.map (wrapperNormal laws)) rest).isWellScopedAt depth =
        (Pattern.collection kind elements rest).isWellScopedAt depth := by
      simp only [Pattern.isWellScopedAt]
      exact wellScopedList_map depth _ elements fun element member => ih element member depth
    cases found : lawFor laws kind with
    | none => rw [wrapperNormal_plain found]; exact mapped
    | some law => rw [wrapperNormal_law found, wrapFinish_wellScoped]; exact mapped

/-- **The wrapper normal form adds no free name.** -/
theorem wrapperNormal_freeFvarNames (pattern : Pattern) (name : String) :
    name ∈ (wrapperNormal laws pattern).freeFvarNames → name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => simp [wrapperNormal_bvar, Pattern.freeFvarNames]
  | hfvar other => simp [wrapperNormal_fvar]
  | happly label arguments ih =>
    intro member
    rw [wrapperNormal_apply] at member
    simp only [Pattern.freeFvarNames, List.mem_flatMap, List.mem_map] at member ⊢
    obtain ⟨_, ⟨argument, argumentIn, rfl⟩, named⟩ := member
    exact ⟨argument, argumentIn, ih argument argumentIn name named⟩
  | hlambda binder body ih =>
    intro member; rw [wrapperNormal_lambda] at member; simp only [Pattern.freeFvarNames] at member ⊢; exact ih name member
  | hmultiLambda arity binders body ih =>
    intro member; rw [wrapperNormal_multiLambda] at member; simp only [Pattern.freeFvarNames] at member ⊢
    exact ih name member
  | hsubst body replacement bodyIH replacementIH =>
    intro member
    rw [wrapperNormal_subst] at member
    simp only [Pattern.freeFvarNames, List.mem_append] at member ⊢
    exact member.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro member
    have mapped : name ∈ (Pattern.collection kind (elements.map (wrapperNormal laws)) rest).freeFvarNames := by
      cases found : lawFor laws kind with
      | none => rwa [wrapperNormal_plain found] at member
      | some law => rw [wrapperNormal_law found] at member; exact wrapFinish_freeFvarNames kind _ rest name member
    simp only [Pattern.freeFvarNames, List.mem_append, List.flatMap_map] at mapped ⊢
    refine mapped.imp (fun inside => ?_) id
    obtain ⟨element, elementIn, named⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨element, elementIn, ih element elementIn name named⟩

/-! ## Typing -/

/-- A wrapper step keeps object terms. -/
theorem WrapperStep.object {left right : Pattern} (step : WrapperStep laws left right)
    (object : isObjectPattern left = true) : isObjectPattern right = true := by
  induction step with
  | singleton _ =>
    simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_cons, List.all_nil, Bool.and_true,
      Option.isNone_none, Bool.true_and] at object
    exact object
  | empty _ _ => simp [isObjectPattern, isObjectPatternList]
  | apply _ ih =>
    simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons, Bool.and_eq_true]
      at object ⊢
    exact ⟨object.1, ih object.2.1, object.2.2⟩
  | lambda _ ih => simp only [isObjectPattern] at object ⊢; exact ih object
  | multiLambda _ ih => simp only [isObjectPattern] at object ⊢; exact ih object
  | substBody _ _ => simp [isObjectPattern] at object
  | substReplacement _ _ => simp [isObjectPattern] at object
  | element _ ih =>
    simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons, Bool.and_eq_true]
      at object ⊢
    exact ⟨object.1, object.2.1, ih object.2.2.1, object.2.2.2⟩

theorem WrapperForward.object {left right : Pattern} (forward : WrapperForward laws left right)
    (object : isObjectPattern left = true) : isObjectPattern right = true := by
  induction forward with
  | refl => exact object
  | tail _ step ih => exact step.object ih

/-- **A forward chain keeps the type of an object term** at a type without collections of a flattening
kind. -/
theorem WrapperForward.hasType {language : LanguageDef} {free : FreeTypeContext}
    (admission : WrappersTyped laws language) {left right : Pattern} (forward : WrapperForward laws left right)
    {bound : List TypeExpr} {type : TypeExpr} (object : isObjectPattern left = true) (noLaw : NoLawCollections laws type)
    (typed : HasType language free bound left type) : HasType language free bound right type := by
  induction forward with
  | refl => exact typed
  | tail chain step ih => exact step.hasType admission (WrapperForward.object chain object) noLaw ih

end Mettapedia.OSLF.MeTTaIL.Wrappers
