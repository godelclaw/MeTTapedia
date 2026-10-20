import Mettapedia.OSLF.MeTTaIL.LawNormalReflective

/-!
# The quote-drop equation as a normal form

A reflective presentation declares a quote constructor `@` and a drop constructor `*`, and the
equation `@(*n) = n`. `QuoteDropStep` is one use of that equation, left to right, in any context;
`QuoteDropSame` is the equality it generates. The static quote-drop normal form
(`ReflectiveSubstitution.normalizeReflective`) is a normal form for it:

- `quoteDrop_sound`: every term is quote-drop equal to its normal form;
- `QuoteDropStep.normalize_eq`: one step keeps the normal form, when quote and drop are distinct
  constructors;
- `quoteDropSame_iff`: two terms are quote-drop equal exactly when their normal forms agree.

Quote-drop steps are closed under context substitution and index lifting
(`QuoteDropStep.substitute`, `QuoteDropStep.liftBVars`), and the normal form commutes with every
renaming of indices (`normalize_substitute_renaming`, `normalize_liftBVars`), keeps free names
(`normalize_freeFvarNames`) and adds no name.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax ReflectiveSubstitution CanonicalBags

variable (declaration : ReflectivePresentationDecl)

/-- One use of the quote-drop equation `@(*n) = n`, left to right, in any context. -/
inductive QuoteDropStep : Pattern → Pattern → Prop where
  | collapse (name : Pattern) :
      QuoteDropStep (.apply declaration.quoteConstructor [.apply declaration.dropConstructor [name]]) name
  | apply {label : String} {before after : List Pattern} {argument changed : Pattern} :
      QuoteDropStep argument changed →
      QuoteDropStep (.apply label (before ++ argument :: after)) (.apply label (before ++ changed :: after))
  | lambda {binder : Option String} {body changed : Pattern} :
      QuoteDropStep body changed → QuoteDropStep (.lambda binder body) (.lambda binder changed)
  | multiLambda {arity : Nat} {binders : List String} {body changed : Pattern} :
      QuoteDropStep body changed → QuoteDropStep (.multiLambda arity binders body) (.multiLambda arity binders changed)
  | substBody {body changed replacement : Pattern} :
      QuoteDropStep body changed → QuoteDropStep (.subst body replacement) (.subst changed replacement)
  | substReplacement {body replacement changed : Pattern} :
      QuoteDropStep replacement changed → QuoteDropStep (.subst body replacement) (.subst body changed)
  | element {kind : CollType} {before after : List Pattern} {element changed : Pattern} {rest : Option String} :
      QuoteDropStep element changed →
      QuoteDropStep (.collection kind (before ++ element :: after) rest) (.collection kind (before ++ changed :: after) rest)

/-- Equality under the quote-drop equation. -/
abbrev QuoteDropSame (left right : Pattern) : Prop := Relation.EqvGen (QuoteDropStep declaration) left right

/-- The quote-drop normal form. -/
abbrev normal (pattern : Pattern) : Pattern := normalizeReflective declaration pattern

variable {declaration}

/-! ## Congruence -/

theorem QuoteDropSame.lift {f : Pattern → Pattern}
    (step : ∀ {a b : Pattern}, QuoteDropStep declaration a b → QuoteDropStep declaration (f a) (f b))
    {left right : Pattern} (same : QuoteDropSame declaration left right) : QuoteDropSame declaration (f left) (f right) := by
  induction same with
  | rel _ _ move => exact .rel _ _ (step move)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem quoteDropSame_pointwise (wrap : List Pattern → Pattern)
    (step : ∀ {before after : List Pattern} {a b : Pattern}, QuoteDropStep declaration a b →
      QuoteDropStep declaration (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before : List Pattern) {items items' : List Pattern}, List.Forall₂ (QuoteDropSame declaration) items items' →
      QuoteDropSame declaration (wrap (before ++ items)) (wrap (before ++ items'))
  | _, [], [], .nil => .refl _
  | before, item :: rest, item' :: rest', .cons head tail => by
    have here : QuoteDropSame declaration (wrap (before ++ item :: rest)) (wrap (before ++ item' :: rest)) :=
      QuoteDropSame.lift (f := fun x => wrap (before ++ x :: rest)) (fun move => step move) head
    have later := quoteDropSame_pointwise wrap step (before ++ [item']) tail
    simp only [List.append_assoc, List.cons_append, List.nil_append] at later
    exact .trans _ _ _ here later

theorem quoteDropSame_apply_congr (label : String) {items items' : List Pattern}
    (pointwise : List.Forall₂ (QuoteDropSame declaration) items items') :
    QuoteDropSame declaration (.apply label items) (.apply label items') :=
  quoteDropSame_pointwise (.apply label) (fun move => .apply move) [] pointwise

theorem quoteDropSame_collection_congr (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (pointwise : List.Forall₂ (QuoteDropSame declaration) items items') :
    QuoteDropSame declaration (.collection kind items rest) (.collection kind items' rest) :=
  quoteDropSame_pointwise (fun items => .collection kind items rest) (fun move => .element move) [] pointwise

theorem quoteDropSame_lambda_congr (binder : Option String) {body body' : Pattern}
    (same : QuoteDropSame declaration body body') : QuoteDropSame declaration (.lambda binder body) (.lambda binder body') :=
  QuoteDropSame.lift (f := fun x => .lambda binder x) (fun move => .lambda move) same

theorem quoteDropSame_multiLambda_congr (arity : Nat) (binders : List String) {body body' : Pattern}
    (same : QuoteDropSame declaration body body') :
    QuoteDropSame declaration (.multiLambda arity binders body) (.multiLambda arity binders body') :=
  QuoteDropSame.lift (f := fun x => .multiLambda arity binders x) (fun move => .multiLambda move) same

theorem quoteDropSame_subst_congr {body body' replacement replacement' : Pattern}
    (sameBody : QuoteDropSame declaration body body') (sameReplacement : QuoteDropSame declaration replacement replacement') :
    QuoteDropSame declaration (.subst body replacement) (.subst body' replacement') :=
  .trans _ _ _ (QuoteDropSame.lift (f := fun x => .subst x replacement) (fun move => .substBody move) sameBody)
    (QuoteDropSame.lift (f := fun x => .subst body' x) (fun move => .substReplacement move) sameReplacement)

/-! ## Forward chains -/

/-- Uses of the quote-drop equation left to right only. -/
abbrev QuoteDropForward (declaration : ReflectivePresentationDecl) (left right : Pattern) : Prop :=
  Relation.ReflTransGen (QuoteDropStep declaration) left right

theorem QuoteDropForward.same {left right : Pattern} (forward : QuoteDropForward declaration left right) :
    QuoteDropSame declaration left right := by
  induction forward with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

theorem QuoteDropForward.lift {f : Pattern → Pattern}
    (step : ∀ {a b : Pattern}, QuoteDropStep declaration a b → QuoteDropStep declaration (f a) (f b))
    {left right : Pattern} (forward : QuoteDropForward declaration left right) :
    QuoteDropForward declaration (f left) (f right) := by
  induction forward with
  | refl => exact .refl
  | tail _ move ih => exact .tail ih (step move)

theorem quoteDropForward_pointwise (wrap : List Pattern → Pattern)
    (step : ∀ {before after : List Pattern} {a b : Pattern}, QuoteDropStep declaration a b →
      QuoteDropStep declaration (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before : List Pattern) {items items' : List Pattern}, List.Forall₂ (QuoteDropForward declaration) items items' →
      QuoteDropForward declaration (wrap (before ++ items)) (wrap (before ++ items'))
  | _, [], [], .nil => .refl
  | before, item :: rest, item' :: rest', .cons head tail => by
    have here : QuoteDropForward declaration (wrap (before ++ item :: rest)) (wrap (before ++ item' :: rest)) :=
      QuoteDropForward.lift (f := fun x => wrap (before ++ x :: rest)) (fun move => step move) head
    have later := quoteDropForward_pointwise wrap step (before ++ [item']) tail
    simp only [List.append_assoc, List.cons_append, List.nil_append] at later
    exact here.trans later

theorem quoteDropForward_apply_congr (label : String) {items items' : List Pattern}
    (pointwise : List.Forall₂ (QuoteDropForward declaration) items items') :
    QuoteDropForward declaration (.apply label items) (.apply label items') :=
  quoteDropForward_pointwise (.apply label) (fun move => .apply move) [] pointwise

theorem quoteDropForward_collection_congr (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (pointwise : List.Forall₂ (QuoteDropForward declaration) items items') :
    QuoteDropForward declaration (.collection kind items rest) (.collection kind items' rest) :=
  quoteDropForward_pointwise (fun items => .collection kind items rest) (fun move => .element move) [] pointwise

theorem quoteDropForward_lambda_congr (binder : Option String) {body body' : Pattern}
    (forward : QuoteDropForward declaration body body') :
    QuoteDropForward declaration (.lambda binder body) (.lambda binder body') :=
  QuoteDropForward.lift (f := fun x => .lambda binder x) (fun move => .lambda move) forward

theorem quoteDropForward_multiLambda_congr (arity : Nat) (binders : List String) {body body' : Pattern}
    (forward : QuoteDropForward declaration body body') :
    QuoteDropForward declaration (.multiLambda arity binders body) (.multiLambda arity binders body') :=
  QuoteDropForward.lift (f := fun x => .multiLambda arity binders x) (fun move => .multiLambda move) forward

theorem quoteDropForward_subst_congr {body body' replacement replacement' : Pattern}
    (forwardBody : QuoteDropForward declaration body body')
    (forwardReplacement : QuoteDropForward declaration replacement replacement') :
    QuoteDropForward declaration (.subst body replacement) (.subst body' replacement') :=
  (QuoteDropForward.lift (f := fun x => .subst x replacement) (fun move => .substBody move) forwardBody).trans
    (QuoteDropForward.lift (f := fun x => .subst body' x) (fun move => .substReplacement move) forwardReplacement)

/-! ## The normal form -/

theorem normal_apply (label : String) (arguments : List Pattern) :
    normal declaration (.apply label arguments) =
      finishNormalizeReflectiveApply declaration label (arguments.map (normal declaration)) := by
  simp only [normal, normalizeReflective, normalizeReflectiveList_map]

theorem normal_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    normal declaration (.collection kind elements rest) = .collection kind (elements.map (normal declaration)) rest := by
  simp only [normal, normalizeReflective, normalizeReflectiveList_map]

theorem normal_lambda (binder : Option String) (body : Pattern) :
    normal declaration (.lambda binder body) = .lambda binder (normal declaration body) := by
  simp only [normal, normalizeReflective]

theorem normal_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    normal declaration (.multiLambda arity binders body) = .multiLambda arity binders (normal declaration body) := by
  simp only [normal, normalizeReflective]

theorem normal_subst (body replacement : Pattern) :
    normal declaration (.subst body replacement) = .subst (normal declaration body) (normal declaration replacement) := by
  simp only [normal, normalizeReflective]

theorem normal_bvar (index : Nat) : normal declaration (.bvar index) = .bvar index := by
  simp only [normal, normalizeReflective]

theorem normal_fvar (name : String) : normal declaration (.fvar name) = .fvar name := by
  simp only [normal, normalizeReflective]

/-- The quote-drop test at a constructor is at most one step. -/
theorem finish_same (label : String) (arguments : List Pattern) :
    QuoteDropSame declaration (.apply label arguments) (finishNormalizeReflectiveApply declaration label arguments) := by
  unfold finishNormalizeReflectiveApply
  split
  · rename_i quote
    split
    · rename_i drop name
      split
      · rename_i dropped
        have quoteEq : label = declaration.quoteConstructor := by simpa using quote
        have dropEq : drop = declaration.dropConstructor := by simpa using dropped
        subst quoteEq dropEq
        exact .rel _ _ (.collapse name)
      · exact .refl _
    · exact .refl _
  · exact .refl _

/-- **Every term is quote-drop equal to its normal form.** -/
theorem quoteDrop_sound (pattern : Pattern) : QuoteDropSame declaration pattern (normal declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [normal_bvar]; exact .refl _
  | hfvar name => rw [normal_fvar]; exact .refl _
  | happly label arguments ih =>
    rw [normal_apply]
    have pointwise : List.Forall₂ (QuoteDropSame declaration) arguments (arguments.map (normal declaration)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun argument member => ih argument member
    exact .trans _ _ _ (quoteDropSame_apply_congr label pointwise) (finish_same label _)
  | hlambda binder body ih => rw [normal_lambda]; exact quoteDropSame_lambda_congr binder ih
  | hmultiLambda arity binders body ih => rw [normal_multiLambda]; exact quoteDropSame_multiLambda_congr arity binders ih
  | hsubst body replacement bodyIH replacementIH => rw [normal_subst]; exact quoteDropSame_subst_congr bodyIH replacementIH
  | hcollection kind elements rest ih =>
    rw [normal_collection]
    have pointwise : List.Forall₂ (QuoteDropSame declaration) elements (elements.map (normal declaration)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun element member => ih element member
    exact quoteDropSame_collection_congr kind rest pointwise

/-- The quote-drop test at a constructor is at most one forward step. -/
theorem finish_forward (label : String) (arguments : List Pattern) :
    QuoteDropForward declaration (.apply label arguments) (finishNormalizeReflectiveApply declaration label arguments) := by
  unfold finishNormalizeReflectiveApply
  split
  · rename_i quote
    split
    · rename_i drop name
      split
      · rename_i dropped
        have quoteEq : label = declaration.quoteConstructor := by simpa using quote
        have dropEq : drop = declaration.dropConstructor := by simpa using dropped
        subst quoteEq dropEq
        exact .single (.collapse name)
      · exact .refl
    · exact .refl
  · exact .refl

/-- **Every term reaches its normal form by forward quote-drop steps.** -/
theorem quoteDrop_forward (pattern : Pattern) : QuoteDropForward declaration pattern (normal declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [normal_bvar]
  | hfvar name => rw [normal_fvar]
  | happly label arguments ih =>
    rw [normal_apply]
    have pointwise : List.Forall₂ (QuoteDropForward declaration) arguments (arguments.map (normal declaration)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun argument member => ih argument member
    exact (quoteDropForward_apply_congr label pointwise).trans (finish_forward label _)
  | hlambda binder body ih => rw [normal_lambda]; exact quoteDropForward_lambda_congr binder ih
  | hmultiLambda arity binders body ih => rw [normal_multiLambda]; exact quoteDropForward_multiLambda_congr arity binders ih
  | hsubst body replacement bodyIH replacementIH =>
    rw [normal_subst]; exact quoteDropForward_subst_congr bodyIH replacementIH
  | hcollection kind elements rest ih =>
    rw [normal_collection]
    have pointwise : List.Forall₂ (QuoteDropForward declaration) elements (elements.map (normal declaration)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun element member => ih element member
    exact quoteDropForward_collection_congr kind rest pointwise

/-- **One quote-drop step keeps the normal form**, when quote and drop are distinct constructors. -/
theorem QuoteDropStep.normalize_eq (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (step : QuoteDropStep declaration left right) :
    normal declaration left = normal declaration right := by
  induction step with
  | collapse name =>
    rw [normal_apply, List.map_cons, List.map_nil, normal_apply, List.map_cons, List.map_nil]
    have plainDrop : finishNormalizeReflectiveApply declaration declaration.dropConstructor [normal declaration name] =
        .apply declaration.dropConstructor [normal declaration name] := by
      unfold finishNormalizeReflectiveApply
      rw [if_neg (by simpa using distinct)]
    rw [plainDrop, finish_drop]
    simp
  | apply _ ih =>
    rw [normal_apply, normal_apply]
    simp only [List.map_append, List.map_cons, ih]
  | lambda _ ih => rw [normal_lambda, normal_lambda, ih]
  | multiLambda _ ih => rw [normal_multiLambda, normal_multiLambda, ih]
  | substBody _ ih => rw [normal_subst, normal_subst, ih]
  | substReplacement _ ih => rw [normal_subst, normal_subst, ih]
  | element _ ih =>
    rw [normal_collection, normal_collection]
    simp only [List.map_append, List.map_cons, ih]

theorem QuoteDropSame.normalize_eq (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (same : QuoteDropSame declaration left right) :
    normal declaration left = normal declaration right := by
  induction same with
  | rel _ _ step => exact step.normalize_eq distinct
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Quote-drop equality is equality of normal forms.** -/
theorem quoteDropSame_iff (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (left right : Pattern) :
    QuoteDropSame declaration left right ↔ normal declaration left = normal declaration right := by
  constructor
  · exact QuoteDropSame.normalize_eq distinct
  · intro same
    exact .trans _ _ _ (quoteDrop_sound left) (same ▸ .symm _ _ (quoteDrop_sound right))

theorem normal_idempotent (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern) :
    normal declaration (normal declaration pattern) = normal declaration pattern :=
  (QuoteDropSame.normalize_eq distinct (quoteDrop_sound pattern)).symm

/-! ## Substitution and lifting -/

/-- **Context substitution maps a quote-drop step to a quote-drop step.** -/
theorem QuoteDropStep.substitute {left right : Pattern} (step : QuoteDropStep declaration left right) :
    ∀ assignment : ContextSubstitution.Assignment,
      QuoteDropStep declaration (ContextSubstitution.substitute assignment left)
        (ContextSubstitution.substitute assignment right) := by
  induction step with
  | collapse name =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_cons, List.map_nil]
    exact .collapse _
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

/-- Lifting indices maps a quote-drop step to a quote-drop step. -/
theorem QuoteDropStep.liftBVars {left right : Pattern} (step : QuoteDropStep declaration left right) :
    ∀ cutoff shift, QuoteDropStep declaration (Substitution.liftBVars cutoff shift left)
      (Substitution.liftBVars cutoff shift right) := by
  induction step with
  | collapse name =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_cons, List.map_nil]
    exact .collapse _
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

theorem QuoteDropSame.substitute {left right : Pattern} (same : QuoteDropSame declaration left right)
    (assignment : ContextSubstitution.Assignment) :
    QuoteDropSame declaration (ContextSubstitution.substitute assignment left)
      (ContextSubstitution.substitute assignment right) :=
  QuoteDropSame.lift (f := ContextSubstitution.substitute assignment) (fun move => move.substitute assignment) same

theorem QuoteDropSame.liftBVars {left right : Pattern} (same : QuoteDropSame declaration left right) (cutoff shift : Nat) :
    QuoteDropSame declaration (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) :=
  QuoteDropSame.lift (f := Substitution.liftBVars cutoff shift) (fun move => move.liftBVars cutoff shift) same

/-- **Substituting quote-drop equal values gives quote-drop equal results.** -/
theorem quoteDropSame_substitute_assignment : ∀ (pattern : Pattern) {first second : ContextSubstitution.Assignment},
    (∀ index, QuoteDropSame declaration (first index) (second index)) →
    QuoteDropSame declaration (ContextSubstitution.substitute first pattern) (ContextSubstitution.substitute second pattern)
  | .bvar index, _, _, pointwise => by simp only [ContextSubstitution.substitute]; exact pointwise index
  | .fvar _, _, _, _ => by simp only [ContextSubstitution.substitute]; exact .refl _
  | .apply label arguments, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply quoteDropSame_apply_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact quoteDropSame_substitute_assignment item pointwise
  | .lambda binder body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply quoteDropSame_lambda_congr
    apply quoteDropSame_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl _
    · exact (pointwise _).liftBVars 0 1
  | .multiLambda arity binders body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply quoteDropSame_multiLambda_congr
    apply quoteDropSame_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl _
    · exact (pointwise _).liftBVars 0 arity
  | .subst body replacement, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply quoteDropSame_subst_congr
    · apply quoteDropSame_substitute_assignment body
      intro index
      unfold ContextSubstitution.lift
      split
      · exact .refl _
      · exact (pointwise _).liftBVars 0 1
    · exact quoteDropSame_substitute_assignment replacement pointwise
  | .collection kind elements rest, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply quoteDropSame_collection_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact quoteDropSame_substitute_assignment item pointwise
termination_by pattern => sizeOf pattern

theorem QuoteDropForward.substitute {left right : Pattern} (forward : QuoteDropForward declaration left right)
    (assignment : ContextSubstitution.Assignment) :
    QuoteDropForward declaration (ContextSubstitution.substitute assignment left)
      (ContextSubstitution.substitute assignment right) :=
  QuoteDropForward.lift (f := ContextSubstitution.substitute assignment) (fun move => move.substitute assignment) forward

theorem QuoteDropForward.liftBVars {left right : Pattern} (forward : QuoteDropForward declaration left right)
    (cutoff shift : Nat) :
    QuoteDropForward declaration (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) :=
  QuoteDropForward.lift (f := Substitution.liftBVars cutoff shift) (fun move => move.liftBVars cutoff shift) forward

/-- **Substituting forward-related values gives forward-related results.** -/
theorem quoteDropForward_substitute_assignment : ∀ (pattern : Pattern) {first second : ContextSubstitution.Assignment},
    (∀ index, QuoteDropForward declaration (first index) (second index)) →
    QuoteDropForward declaration (ContextSubstitution.substitute first pattern) (ContextSubstitution.substitute second pattern)
  | .bvar index, _, _, pointwise => by simp only [ContextSubstitution.substitute]; exact pointwise index
  | .fvar _, _, _, _ => by simp only [ContextSubstitution.substitute]; exact .refl
  | .apply label arguments, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply quoteDropForward_apply_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact quoteDropForward_substitute_assignment item pointwise
  | .lambda binder body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply quoteDropForward_lambda_congr
    apply quoteDropForward_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl
    · exact (pointwise _).liftBVars 0 1
  | .multiLambda arity binders body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply quoteDropForward_multiLambda_congr
    apply quoteDropForward_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl
    · exact (pointwise _).liftBVars 0 arity
  | .subst body replacement, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply quoteDropForward_subst_congr
    · apply quoteDropForward_substitute_assignment body
      intro index
      unfold ContextSubstitution.lift
      split
      · exact .refl
      · exact (pointwise _).liftBVars 0 1
    · exact quoteDropForward_substitute_assignment replacement pointwise
  | .collection kind elements rest, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply quoteDropForward_collection_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact quoteDropForward_substitute_assignment item pointwise
termination_by pattern => sizeOf pattern

/-! ## Renamings -/

/-- An assignment that maps every index to an index. -/
def Renaming (assignment : ContextSubstitution.Assignment) : Prop := ∀ index, ∃ other, assignment index = .bvar other

theorem Renaming.lift {assignment : ContextSubstitution.Assignment} (renames : Renaming assignment) (arity : Nat) :
    Renaming (ContextSubstitution.lift arity assignment) := by
  intro index
  unfold ContextSubstitution.lift
  split
  · exact ⟨index, rfl⟩
  · obtain ⟨other, found⟩ := renames (index - arity)
    rw [found]
    unfold Substitution.liftBVars
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- A shape-preserving map commutes with the quote-drop test at a constructor. -/
theorem finish_map {f : Pattern → Pattern}
    (onApply : ∀ label arguments, f (.apply label arguments) = .apply label (arguments.map f))
    (keepsShape : ∀ pattern, (∀ label arguments, pattern ≠ .apply label arguments) →
      ∀ label arguments, f pattern ≠ .apply label arguments)
    (label : String) (arguments : List Pattern) :
    finishNormalizeReflectiveApply declaration label (arguments.map f) =
      f (finishNormalizeReflectiveApply declaration label arguments) := by
  match arguments with
  | [] => simp only [List.map_nil, finish_nil, onApply]
  | first :: second :: rest =>
    rw [List.map_cons, List.map_cons, finish_long, finish_long, onApply]
    rfl
  | [first] =>
    by_cases shaped : ∃ drop name, first = .apply drop [name]
    · obtain ⟨drop, name, rfl⟩ := shaped
      rw [List.map_cons, List.map_nil, onApply, List.map_cons, List.map_nil, finish_drop, finish_drop]
      split
      · rfl
      · rw [onApply, List.map_cons, List.map_nil, onApply, List.map_cons, List.map_nil]
    · have notShaped : ¬ ∃ drop name, f first = .apply drop [name] := by
        rintro ⟨drop, name, same⟩
        by_cases isApply : ∃ label arguments, first = .apply label arguments
        · obtain ⟨label', arguments', rfl⟩ := isApply
          rw [onApply] at same
          simp only [Pattern.apply.injEq] at same
          obtain ⟨rfl, lengths⟩ := same
          match arguments', lengths with
          | [argument], _ => exact shaped ⟨_, argument, rfl⟩
        · push Not at isApply
          exact keepsShape first isApply drop [name] same
      rw [List.map_cons, List.map_nil, finish_plain declaration label notShaped, finish_plain declaration label shaped,
        onApply, List.map_cons, List.map_nil]

theorem substitute_keepsShape {assignment : ContextSubstitution.Assignment} (renames : Renaming assignment)
    (pattern : Pattern) (notApply : ∀ label arguments, pattern ≠ .apply label arguments) :
    ∀ label arguments, ContextSubstitution.substitute assignment pattern ≠ .apply label arguments := by
  intro label arguments same
  cases pattern with
  | bvar index =>
    obtain ⟨other, found⟩ := renames index
    simp only [ContextSubstitution.substitute, found] at same
    cases same
  | apply label' arguments' => exact notApply label' arguments' rfl
  | _ => simp [ContextSubstitution.substitute] at same

/-- **The normal form commutes with every renaming.** -/
theorem normalize_substitute_renaming (pattern : Pattern) :
    ∀ {assignment : ContextSubstitution.Assignment}, Renaming assignment →
      normal declaration (ContextSubstitution.substitute assignment pattern) =
        ContextSubstitution.substitute assignment (normal declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro assignment renames
    obtain ⟨other, found⟩ := renames index
    simp only [ContextSubstitution.substitute, found, normal_bvar]
  | hfvar name => intro assignment _; simp only [ContextSubstitution.substitute, normal_fvar]
  | happly label arguments ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, normal_apply, List.map_map]
    rw [List.map_congr_left (fun argument member => by
      show normal declaration (ContextSubstitution.substitute assignment argument) =
        ContextSubstitution.substitute assignment (normal declaration argument)
      exact ih argument member renames)]
    have mapped := finish_map (declaration := declaration) (f := ContextSubstitution.substitute assignment)
      (fun label arguments => by simp [ContextSubstitution.substitute])
      (substitute_keepsShape renames) label (arguments.map (normal declaration))
    rw [List.map_map] at mapped
    exact mapped
  | hlambda binder body ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, normal_lambda, ih (renames.lift 1)]
  | hmultiLambda arity binders body ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, normal_multiLambda, ih (renames.lift arity)]
  | hsubst body replacement bodyIH replacementIH =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, normal_subst, bodyIH (renames.lift 1), replacementIH renames]
  | hcollection kind elements rest ih =>
    intro assignment renames
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, normal_collection,
      List.map_map]
    congr 1
    exact List.map_congr_left fun element member => ih element member renames

theorem liftBVars_keepsShape (cutoff shift : Nat) (pattern : Pattern)
    (notApply : ∀ label arguments, pattern ≠ .apply label arguments) :
    ∀ label arguments, Substitution.liftBVars cutoff shift pattern ≠ .apply label arguments := by
  intro label arguments same
  cases pattern with
  | bvar index =>
    unfold Substitution.liftBVars at same
    split at same <;> cases same
  | apply label' arguments' => exact notApply label' arguments' rfl
  | _ => simp [Substitution.liftBVars] at same

/-- **The normal form commutes with index lifting.** -/
theorem normalize_liftBVars (pattern : Pattern) :
    ∀ cutoff shift, normal declaration (Substitution.liftBVars cutoff shift pattern) =
      Substitution.liftBVars cutoff shift (normal declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro cutoff shift
    by_cases high : index ≥ cutoff <;> simp [Substitution.liftBVars, high, normal_bvar]
  | hfvar name => intro cutoff shift; simp only [Substitution.liftBVars, normal_fvar]
  | happly label arguments ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, normal_apply, List.map_map]
    rw [List.map_congr_left (fun argument member => by
      show normal declaration (Substitution.liftBVars cutoff shift argument) =
        Substitution.liftBVars cutoff shift (normal declaration argument)
      exact ih argument member cutoff shift)]
    have mapped := finish_map (declaration := declaration) (f := Substitution.liftBVars cutoff shift)
      (fun label arguments => by simp [Substitution.liftBVars])
      (liftBVars_keepsShape cutoff shift) label (arguments.map (normal declaration))
    rw [List.map_map] at mapped
    exact mapped
  | hlambda binder body ih => intro cutoff shift; simp only [Substitution.liftBVars, normal_lambda, ih]
  | hmultiLambda arity binders body ih => intro cutoff shift; simp only [Substitution.liftBVars, normal_multiLambda, ih]
  | hsubst body replacement bodyIH replacementIH =>
    intro cutoff shift; simp only [Substitution.liftBVars, normal_subst, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, normal_collection, List.map_map]
    congr 1
    exact List.map_congr_left fun element member => ih element member cutoff shift

/-! ## Names -/

theorem finish_freeFvarNames (label : String) (arguments : List Pattern) (name : String) :
    name ∈ (finishNormalizeReflectiveApply declaration label arguments).freeFvarNames →
      name ∈ arguments.flatMap Pattern.freeFvarNames := by
  intro member
  unfold finishNormalizeReflectiveApply at member
  split at member
  · split at member
    · split at member
      · simpa [Pattern.freeFvarNames] using member
      · simpa [Pattern.freeFvarNames] using member
    · simpa [Pattern.freeFvarNames] using member
  · simpa [Pattern.freeFvarNames] using member

/-- **The normal form adds no free name.** -/
theorem normalize_freeFvarNames (pattern : Pattern) (name : String) :
    name ∈ (normal declaration pattern).freeFvarNames → name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => simp [normal_bvar, Pattern.freeFvarNames]
  | hfvar other => simp [normal_fvar]
  | happly label arguments ih =>
    intro member
    rw [normal_apply] at member
    have inside := finish_freeFvarNames label _ name member
    simp only [List.mem_flatMap, List.mem_map] at inside
    obtain ⟨_, ⟨argument, argumentIn, rfl⟩, named⟩ := inside
    simp only [Pattern.freeFvarNames, List.mem_flatMap]
    exact ⟨argument, argumentIn, ih argument argumentIn name named⟩
  | hlambda binder body ih =>
    intro member; rw [normal_lambda] at member; simp only [Pattern.freeFvarNames] at member ⊢; exact ih name member
  | hmultiLambda arity binders body ih =>
    intro member; rw [normal_multiLambda] at member; simp only [Pattern.freeFvarNames] at member ⊢; exact ih name member
  | hsubst body replacement bodyIH replacementIH =>
    intro member
    rw [normal_subst] at member
    simp only [Pattern.freeFvarNames, List.mem_append] at member ⊢
    exact member.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro member
    rw [normal_collection] at member
    simp only [Pattern.freeFvarNames, List.mem_append, List.flatMap_map] at member ⊢
    refine member.imp (fun inside => ?_) id
    obtain ⟨element, elementIn, named⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨element, elementIn, ih element elementIn name named⟩

/-- A quote-drop step keeps exactly the free names. -/
theorem QuoteDropStep.freeFvarNames {left right : Pattern} (step : QuoteDropStep declaration left right) (name : String) :
    name ∈ left.freeFvarNames ↔ name ∈ right.freeFvarNames := by
  induction step with
  | collapse inner => simp [Pattern.freeFvarNames]
  | apply _ ih => simp [Pattern.freeFvarNames, List.mem_append, ih]
  | lambda _ ih => simpa [Pattern.freeFvarNames] using ih
  | multiLambda _ ih => simpa [Pattern.freeFvarNames] using ih
  | substBody _ ih => simp [Pattern.freeFvarNames, ih]
  | substReplacement _ ih => simp [Pattern.freeFvarNames, ih]
  | element _ ih => simp [Pattern.freeFvarNames, List.mem_append, ih]

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
