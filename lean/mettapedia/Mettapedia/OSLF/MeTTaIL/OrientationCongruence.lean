import Mettapedia.OSLF.MeTTaIL.OrientationSubstitution

/-!
# The normal form is a congruence for the walks

The orientation normal form (`frameNormal`) writes every datum and decoration in the normal form of
`G ∗ F(V)` and decorates every occurrence. A walk *respects* it when normalizing before the walk
changes nothing after it, `N (W (N t)) = N (W t)`: then terms of one normal form are walked into terms
of one normal form. The action respects it (`frameAct_normal`), and so does instantiating a datum
(`instDatumWalk_normal`) at terms whose occurrences of the body sort are not the instantiated variable.
The normal form is idempotent (`frameNormal_idem`), and the action depends on the acting element
alone (`frameAct_congr`).

The tools are facts about walks in general:

- `mapFrame_fuse`: two walks are one walk, which walks the second over whatever the first puts at an
  occurrence;
- `frameAll_mapFrame`: what a walk puts at data and at occurrences decides what holds of its result;
- `frameAll_shift`, `frameAll_mono`, `frameAll_of`: the position predicates at a shifted depth,
  weakened, and everywhere.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

/-! ## Position predicates -/

section Positions

variable {language : LanguageDef} {decl : OrientationDecl}

mutual
  /-- **Predicates that hold everywhere hold at every position.** -/
  theorem frameAll_of {dataOk variableOk : Nat → Pattern → Prop} (dataAll : ∀ depth datum, dataOk depth datum)
      (variableAll : ∀ depth occurrence, (decorated? decl occurrence).isSome → variableOk depth occurrence) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk variableOk depth type pattern
    | depth, type, pattern => by
      rw [FrameAll.eq_def]
      split_ifs with data occurs
      · exact dataAll _ _
      · exact variableAll _ _ occurs.1
      · match pattern with
        | .apply label arguments =>
          dsimp only
          split
          · exact frameAllArgs_of dataAll variableAll depth _ arguments
          · trivial
        | .lambda binder body =>
          dsimp only
          split
          · exact frameAll_of dataAll variableAll (depth + 1) _ body
          · trivial
        | .multiLambda arity binders body =>
          dsimp only
          split
          · exact frameAll_of dataAll variableAll (depth + arity) _ body
          · trivial
        | .collection kind elements rest =>
          dsimp only
          split
          · exact frameAllList_of dataAll variableAll depth _ elements
          · trivial
        | .bvar _ => trivial
        | .fvar _ => trivial
        | .subst _ _ => trivial
  termination_by _ _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllArgs_of {dataOk variableOk : Nat → Pattern → Prop} (dataAll : ∀ depth datum, dataOk depth datum)
      (variableAll : ∀ depth occurrence, (decorated? decl occurrence).isSome → variableOk depth occurrence) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk depth types arguments
    | depth, type :: types, argument :: arguments => by
      rw [FrameAllArgs]
      exact ⟨frameAll_of dataAll variableAll depth type argument,
        frameAllArgs_of dataAll variableAll depth types arguments⟩
    | depth, [], arguments => by simp [FrameAllArgs]
    | depth, _ :: _, [] => by simp [FrameAllArgs]
  termination_by _ _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllList_of {dataOk variableOk : Nat → Pattern → Prop} (dataAll : ∀ depth datum, dataOk depth datum)
      (variableAll : ∀ depth occurrence, (decorated? decl occurrence).isSome → variableOk depth occurrence) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk depth element patterns
    | depth, element, [] => by rw [FrameAllList]; trivial
    | depth, element, pattern :: patterns => by
      rw [FrameAllList]
      exact ⟨frameAll_of dataAll variableAll depth element pattern,
        frameAllList_of dataAll variableAll depth element patterns⟩
  termination_by _ _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The data and variable branches of a weakening step. -/
syntax "mono_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mono_cases) => `(tactic| (
      rw [FrameAll.eq_def] at all ⊢
      split_ifs at all ⊢ with data occurs
      · exact dataImp _ _ all
      · exact variableImp _ _ all))

mutual
  /-- **Weaker predicates hold where stronger ones do.** -/
  theorem frameAll_mono {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (dataImp : ∀ depth datum, dataOk depth datum → dataOk' depth datum)
      (variableImp : ∀ depth occurrence, variableOk depth occurrence → variableOk' depth occurrence) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk variableOk depth type pattern →
          FrameAll language decl dataOk' variableOk' depth type pattern
    | depth, type, .apply label arguments, all => by
      mono_cases
      dsimp only at all ⊢
      cases found : paramTypes language label with
      | none => trivial
      | some types =>
        rw [found] at all
        dsimp only at all ⊢
        exact frameAllArgs_mono dataImp variableImp depth types arguments all
    | depth, type, .lambda binder body, all => by
      mono_cases
      dsimp only at all ⊢
      cases type with
      | arrow domain codomain => exact frameAll_mono dataImp variableImp (depth + 1) codomain body all
      | _ => trivial
    | depth, type, .multiLambda arity binders body, all => by
      mono_cases
      dsimp only at all ⊢
      cases type with
      | arrow domain codomain => exact frameAll_mono dataImp variableImp (depth + arity) codomain body all
      | _ => trivial
    | depth, type, .collection kind elements rest, all => by
      mono_cases
      dsimp only at all ⊢
      cases found : elementType language type kind with
      | none => trivial
      | some element =>
        rw [found] at all
        dsimp only at all ⊢
        exact frameAllList_mono dataImp variableImp depth element elements all
    | depth, type, .bvar index, all => by mono_cases; trivial
    | depth, type, .fvar name, all => by mono_cases; trivial
    | depth, type, .subst body replacement, all => by mono_cases; trivial
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllArgs_mono {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (dataImp : ∀ depth datum, dataOk depth datum → dataOk' depth datum)
      (variableImp : ∀ depth occurrence, variableOk depth occurrence → variableOk' depth occurrence) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk depth types arguments →
          FrameAllArgs language decl dataOk' variableOk' depth types arguments
    | depth, type :: types, argument :: arguments, all => by
      rw [FrameAllArgs] at all ⊢
      exact ⟨frameAll_mono dataImp variableImp depth type argument all.1,
        frameAllArgs_mono dataImp variableImp depth types arguments all.2⟩
    | depth, [], arguments, _ => by simp [FrameAllArgs]
    | depth, _ :: _, [], _ => by simp [FrameAllArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllList_mono {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (dataImp : ∀ depth datum, dataOk depth datum → dataOk' depth datum)
      (variableImp : ∀ depth occurrence, variableOk depth occurrence → variableOk' depth occurrence) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk depth element patterns →
          FrameAllList language decl dataOk' variableOk' depth element patterns
    | depth, element, [], _ => by rw [FrameAllList]; trivial
    | depth, element, pattern :: patterns, all => by
      rw [FrameAllList] at all ⊢
      exact ⟨frameAll_mono dataImp variableImp depth element pattern all.1,
        frameAllList_mono dataImp variableImp depth element patterns all.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The data and variable branches of a conjunction step. -/
syntax "and_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| and_cases) => `(tactic| (
      rw [FrameAll.eq_def] at first second ⊢
      split_ifs at first second ⊢ with data occurs
      · exact ⟨first, second⟩
      · exact ⟨first, second⟩))

mutual
  /-- **Predicates that hold at every position hold together.** -/
  theorem frameAll_and {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop} :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk variableOk depth type pattern →
          FrameAll language decl dataOk' variableOk' depth type pattern →
            FrameAll language decl (fun k datum => dataOk k datum ∧ dataOk' k datum)
              (fun k occurrence => variableOk k occurrence ∧ variableOk' k occurrence) depth type pattern
    | depth, type, .apply label arguments, first, second => by
      and_cases
      dsimp only at first second ⊢
      cases found : paramTypes language label with
      | none => trivial
      | some types =>
        rw [found] at first second
        dsimp only at first second ⊢
        exact frameAllArgs_and depth types arguments first second
    | depth, type, .lambda binder body, first, second => by
      and_cases
      dsimp only at first second ⊢
      cases type with
      | arrow domain codomain => exact frameAll_and (depth + 1) codomain body first second
      | _ => trivial
    | depth, type, .multiLambda arity binders body, first, second => by
      and_cases
      dsimp only at first second ⊢
      cases type with
      | arrow domain codomain => exact frameAll_and (depth + arity) codomain body first second
      | _ => trivial
    | depth, type, .collection kind elements rest, first, second => by
      and_cases
      dsimp only at first second ⊢
      cases found : elementType language type kind with
      | none => trivial
      | some element =>
        rw [found] at first second
        dsimp only at first second ⊢
        exact frameAllList_and depth element elements first second
    | depth, type, .bvar index, first, second => by and_cases; trivial
    | depth, type, .fvar name, first, second => by and_cases; trivial
    | depth, type, .subst body replacement, first, second => by and_cases; trivial
  termination_by _ _ pattern _ _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllArgs_and {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop} :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk depth types arguments →
          FrameAllArgs language decl dataOk' variableOk' depth types arguments →
            FrameAllArgs language decl (fun k datum => dataOk k datum ∧ dataOk' k datum)
              (fun k occurrence => variableOk k occurrence ∧ variableOk' k occurrence) depth types arguments
    | depth, type :: types, argument :: arguments, first, second => by
      rw [FrameAllArgs] at first second ⊢
      exact ⟨frameAll_and depth type argument first.1 second.1,
        frameAllArgs_and depth types arguments first.2 second.2⟩
    | depth, [], arguments, _, _ => by simp [FrameAllArgs]
    | depth, _ :: _, [], _, _ => by simp [FrameAllArgs]
  termination_by _ _ arguments _ _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllList_and {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop} :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk depth element patterns →
          FrameAllList language decl dataOk' variableOk' depth element patterns →
            FrameAllList language decl (fun k datum => dataOk k datum ∧ dataOk' k datum)
              (fun k occurrence => variableOk k occurrence ∧ variableOk' k occurrence) depth element patterns
    | depth, element, [], _, _ => by rw [FrameAllList]; trivial
    | depth, element, pattern :: patterns, first, second => by
      rw [FrameAllList] at first second ⊢
      exact ⟨frameAll_and depth element pattern first.1 second.1,
        frameAllList_and depth element patterns first.2 second.2⟩
  termination_by _ _ patterns _ _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- **The predicates at a deeper start are the predicates that see the extra depth.** -/
  theorem frameAll_shift {dataOk variableOk : Nat → Pattern → Prop} (shift : Nat) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk variableOk (depth + shift) type pattern ↔
          FrameAll language decl (fun k => dataOk (k + shift)) (fun k => variableOk (k + shift)) depth type pattern
    | depth, type, pattern => by
      rw [FrameAll.eq_def, FrameAll.eq_def]
      split_ifs with data occurs
      · exact Iff.rfl
      · exact Iff.rfl
      · match pattern with
        | .apply label arguments =>
          dsimp only
          cases paramTypes language label with
          | none => exact Iff.rfl
          | some types =>
            dsimp only
            exact frameAllArgs_shift shift depth types arguments
        | .lambda binder body =>
          dsimp only
          cases type with
          | arrow domain codomain =>
            dsimp only
            rw [show depth + shift + 1 = depth + 1 + shift by omega]
            exact frameAll_shift shift (depth + 1) codomain body
          | _ => exact Iff.rfl
        | .multiLambda arity binders body =>
          dsimp only
          cases type with
          | arrow domain codomain =>
            dsimp only
            rw [show depth + shift + arity = depth + arity + shift by omega]
            exact frameAll_shift shift (depth + arity) codomain body
          | _ => exact Iff.rfl
        | .collection kind elements rest =>
          dsimp only
          cases elementType language type kind with
          | none => exact Iff.rfl
          | some element =>
            dsimp only
            exact frameAllList_shift shift depth element elements
        | .bvar _ => exact Iff.rfl
        | .fvar _ => exact Iff.rfl
        | .subst _ _ => exact Iff.rfl
  termination_by _ _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllArgs_shift {dataOk variableOk : Nat → Pattern → Prop} (shift : Nat) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk (depth + shift) types arguments ↔
          FrameAllArgs language decl (fun k => dataOk (k + shift)) (fun k => variableOk (k + shift)) depth types
            arguments
    | depth, type :: types, argument :: arguments => by
      rw [FrameAllArgs, FrameAllArgs, frameAll_shift shift depth type argument,
        frameAllArgs_shift shift depth types arguments]
    | depth, [], arguments => by simp [FrameAllArgs]
    | depth, _ :: _, [] => by simp [FrameAllArgs]
  termination_by _ _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllList_shift {dataOk variableOk : Nat → Pattern → Prop} (shift : Nat) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk (depth + shift) element patterns ↔
          FrameAllList language decl (fun k => dataOk (k + shift)) (fun k => variableOk (k + shift)) depth element
            patterns
    | depth, element, [] => by simp [FrameAllList]
    | depth, element, pattern :: patterns => by
      rw [FrameAllList, FrameAllList, frameAll_shift shift depth element pattern,
        frameAllList_shift shift depth element patterns]
  termination_by _ _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Positions

/-! ## Fusing walks and transporting predicates -/

section Walks

variable {language : LanguageDef} {decl : OrientationDecl}

/-- The data and variable branches of a fusion step; leaves the structural branch with `data`,
`occurs`, and `structural` for the first walk's result. -/
syntax "fuse_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| fuse_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [mapFrame_data data, mapFrame_data data, mapFrame_data data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · have sameType : type = bodyType := Option.some.inj (occurs.2.symm.trans bodySort)
        rw [mapFrame_variable data occurs, mapFrame_variable data occurs, sameType]
      have structural := decorated?_mapFrame_structural (language := language) (f := f₁) (v := v₁)
        (depth := depth) keeps bodyNotData data occurs))

mutual
  /-- **Two walks are one walk**, which walks the second over whatever the first puts at an occurrence,
  when the first keeps a coefficient and the action does not act on data. -/
  theorem mapFrame_fuse {f₁ v₁ f₂ v₂ : Nat → Pattern → Pattern} (keeps : KeepsNotBare decl v₁)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        mapFrame language decl f₂ v₂ depth type (mapFrame language decl f₁ v₁ depth type pattern) =
          mapFrame language decl (fun d x => f₂ d (f₁ d x))
            (fun d x => mapFrame language decl f₂ v₂ d bodyType (v₁ d x)) depth type pattern
    | depth, type, .apply label arguments => by
      fuse_cases (.apply label arguments)
      cases found : paramTypes language label with
      | none => simp only [mapFrame_apply_unknown data occurs found]
      | some types =>
        rw [mapFrame_apply_structural (f := f₁) (v := v₁) data occurs found] at structural ⊢
        rw [mapFrame_apply_structural data structural found, mapFrame_apply_structural data occurs found,
          mapFrameArgs_fuse keeps bodyNotData bodySort depth types arguments]
    | depth, type, .lambda binder body => by
      fuse_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        rw [mapFrame_lambda data, mapFrame_lambda data, mapFrame_lambda data,
          mapFrame_fuse keeps bodyNotData bodySort (depth + 1) codomain body]
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        simp only [mapFrame_lambda_other data notArrow]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        simp only [mapFrame_lambda_other data notArrow]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        simp only [mapFrame_lambda_other data notArrow]
    | depth, type, .multiLambda arity binders body => by
      fuse_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        rw [mapFrame_multiLambda data, mapFrame_multiLambda data, mapFrame_multiLambda data,
          mapFrame_fuse keeps bodyNotData bodySort (depth + arity) codomain body]
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        simp only [mapFrame_multiLambda_other data notArrow]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        simp only [mapFrame_multiLambda_other data notArrow]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        simp only [mapFrame_multiLambda_other data notArrow]
    | depth, type, .collection kind elements rest => by
      fuse_cases (.collection kind elements rest)
      cases found : elementType language type kind with
      | none => simp only [mapFrame_collection_unknown data found]
      | some element =>
        simp only [mapFrame_collection data found]
        rw [mapFrameList_fuse keeps bodyNotData bodySort depth element elements]
    | depth, type, .bvar index => by
      fuse_cases (.bvar index)
      simp only [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩)]
    | depth, type, .fvar name => by
      fuse_cases (.fvar name)
      simp only [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩))]
    | depth, type, .subst body replacement => by
      fuse_cases (.subst body replacement)
      simp only [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩))]
  termination_by _ _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameArgs_fuse {f₁ v₁ f₂ v₂ : Nat → Pattern → Pattern} (keeps : KeepsNotBare decl v₁)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        mapFrameArgs language decl f₂ v₂ depth types (mapFrameArgs language decl f₁ v₁ depth types arguments) =
          mapFrameArgs language decl (fun d x => f₂ d (f₁ d x))
            (fun d x => mapFrame language decl f₂ v₂ d bodyType (v₁ d x)) depth types arguments
    | depth, type :: types, argument :: arguments => by
      rw [mapFrameArgs, mapFrameArgs, mapFrameArgs, mapFrame_fuse keeps bodyNotData bodySort depth type argument,
        mapFrameArgs_fuse keeps bodyNotData bodySort depth types arguments]
    | depth, [], arguments => by simp [mapFrameArgs]
    | depth, _ :: _, [] => by simp [mapFrameArgs]
  termination_by _ _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameList_fuse {f₁ v₁ f₂ v₂ : Nat → Pattern → Pattern} (keeps : KeepsNotBare decl v₁)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        mapFrameList language decl f₂ v₂ depth element (mapFrameList language decl f₁ v₁ depth element patterns) =
          mapFrameList language decl (fun d x => f₂ d (f₁ d x))
            (fun d x => mapFrame language decl f₂ v₂ d bodyType (v₁ d x)) depth element patterns
    | depth, element, [] => by simp [mapFrameList]
    | depth, element, pattern :: patterns => by
      rw [mapFrameList, mapFrameList, mapFrameList, mapFrame_fuse keeps bodyNotData bodySort depth element pattern,
        mapFrameList_fuse keeps bodyNotData bodySort depth element patterns]
  termination_by _ _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The data and variable branches of a transport step; leaves the structural branch with `data`,
`occurs`, `structural` for the walk's result, and `all` unfolded. -/
syntax "transport_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| transport_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [mapFrame_data data, FrameAll.eq_def, if_pos data]
        rw [FrameAll.eq_def, if_pos data] at all
        exact dataStep _ _ all
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · have sameType : type = bodyType := Option.some.inj (occurs.2.symm.trans bodySort)
        rw [FrameAll.eq_def, if_neg data, if_pos occurs] at all
        rw [mapFrame_variable data occurs, sameType]
        exact variableStep _ _ occurs.1 all
      have structural := decorated?_mapFrame_structural (language := language) (f := f) (v := v)
        (depth := depth) keeps bodyNotData data occurs
      rw [FrameAll.eq_def, if_neg data, if_neg occurs] at all))

mutual
  /-- **What a walk puts at data and at occurrences decides what holds of its result.** -/
  theorem frameAll_mapFrame {f v : Nat → Pattern → Pattern} {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (keeps : KeepsNotBare decl v) (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
      (dataStep : ∀ depth datum, dataOk depth datum → dataOk' depth (f depth datum))
      (variableStep : ∀ depth occurrence, (decorated? decl occurrence).isSome → variableOk depth occurrence →
        FrameAll language decl dataOk' variableOk' depth bodyType (v depth occurrence)) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk variableOk depth type pattern →
          FrameAll language decl dataOk' variableOk' depth type (mapFrame language decl f v depth type pattern)
    | depth, type, .apply label arguments, all => by
      transport_cases (.apply label arguments)
      dsimp only at all
      cases found : paramTypes language label with
      | none =>
        rw [mapFrame_apply_unknown data occurs found, FrameAll.eq_def, if_neg data, if_neg occurs]
        simp only [found]
      | some types =>
        rw [found] at all
        dsimp only at all
        rw [mapFrame_apply_structural data occurs found] at structural ⊢
        rw [FrameAll.eq_def, if_neg data, if_neg structural]
        simp only [found]
        exact frameAllArgs_mapFrame keeps bodyNotData bodySort dataStep variableStep depth types arguments all
    | depth, type, .lambda binder body, all => by
      transport_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only at all
        rw [mapFrame_lambda data, FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact frameAll_mapFrame keeps bodyNotData bodySort dataStep variableStep (depth + 1) codomain body all
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
    | depth, type, .multiLambda arity binders body, all => by
      transport_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only at all
        rw [mapFrame_multiLambda data, FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact frameAll_mapFrame keeps bodyNotData bodySort dataStep variableStep (depth + arity) codomain body all
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
    | depth, type, .collection kind elements rest, all => by
      transport_cases (.collection kind elements rest)
      dsimp only at all
      cases found : elementType language type kind with
      | none =>
        rw [mapFrame_collection_unknown data found, FrameAll.eq_def, if_neg data, if_neg occurs]
        simp only [found]
      | some element =>
        rw [found] at all
        dsimp only at all
        rw [mapFrame_collection data found, FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])]
        simp only [found]
        exact frameAllList_mapFrame keeps bodyNotData bodySort dataStep variableStep depth element elements all
    | depth, type, .bvar index, all => by
      transport_cases (.bvar index)
      rw [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩), FrameAll.eq_def, if_neg data, if_neg occurs]
      trivial
    | depth, type, .fvar name, all => by
      transport_cases (.fvar name)
      rw [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩)), FrameAll.eq_def, if_neg data, if_neg occurs]
      trivial
    | depth, type, .subst body replacement, all => by
      transport_cases (.subst body replacement)
      rw [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), FrameAll.eq_def, if_neg data,
        if_neg occurs]
      trivial
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllArgs_mapFrame {f v : Nat → Pattern → Pattern}
      {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (keeps : KeepsNotBare decl v) (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
      (dataStep : ∀ depth datum, dataOk depth datum → dataOk' depth (f depth datum))
      (variableStep : ∀ depth occurrence, (decorated? decl occurrence).isSome → variableOk depth occurrence →
        FrameAll language decl dataOk' variableOk' depth bodyType (v depth occurrence)) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk depth types arguments →
          FrameAllArgs language decl dataOk' variableOk' depth types (mapFrameArgs language decl f v depth types arguments)
    | depth, type :: types, argument :: arguments, all => by
      rw [FrameAllArgs] at all
      rw [mapFrameArgs, FrameAllArgs]
      exact ⟨frameAll_mapFrame keeps bodyNotData bodySort dataStep variableStep depth type argument all.1,
        frameAllArgs_mapFrame keeps bodyNotData bodySort dataStep variableStep depth types arguments all.2⟩
    | depth, [], arguments, _ => by simp [mapFrameArgs, FrameAllArgs]
    | depth, _ :: _, [], _ => by simp [mapFrameArgs, FrameAllArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllList_mapFrame {f v : Nat → Pattern → Pattern}
      {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (keeps : KeepsNotBare decl v) (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
      (dataStep : ∀ depth datum, dataOk depth datum → dataOk' depth (f depth datum))
      (variableStep : ∀ depth occurrence, (decorated? decl occurrence).isSome → variableOk depth occurrence →
        FrameAll language decl dataOk' variableOk' depth bodyType (v depth occurrence)) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk depth element patterns →
          FrameAllList language decl dataOk' variableOk' depth element
            (mapFrameList language decl f v depth element patterns)
    | depth, element, [], _ => by rw [mapFrameList, FrameAllList]; trivial
    | depth, element, pattern :: patterns, all => by
      rw [FrameAllList] at all
      rw [mapFrameList, FrameAllList]
      exact ⟨frameAll_mapFrame keeps bodyNotData bodySort dataStep variableStep depth element pattern all.1,
        frameAllList_mapFrame keeps bodyNotData bodySort dataStep variableStep depth element patterns all.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The data and variable branches of a reflection step; leaves the structural branch with `data`,
`occurs`, `structural` for the walk's result, and `all` unfolded at the result. -/
syntax "reflect_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| reflect_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [mapFrame_data data, FrameAll.eq_def, if_pos data] at all
        rw [FrameAll.eq_def, if_pos data]
        exact dataBack _ _ all
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [mapFrame_variable data occurs, FrameAll.eq_def, if_neg data,
          if_pos ⟨keeps.occurs _ _ occurs.1, occurs.2⟩] at all
        rw [FrameAll.eq_def, if_neg data, if_pos occurs]
        exact variableBack _ _ occurs.1 all
      have structural := decorated?_mapFrame_structural (language := language) (f := f) (v := v)
        (depth := depth) keeps.notBare bodyNotData data occurs
      rw [FrameAll.eq_def, if_neg data, if_neg occurs]))

mutual
  /-- **What holds of a walk's result holds of what it walked**, when the walk keeps occurrences and its
  functions reflect the predicates. -/
  theorem frameAll_reflect {f v : Nat → Pattern → Pattern} {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (keeps : KeepsOccurrences decl v) (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      (dataBack : ∀ depth datum, dataOk' depth (f depth datum) → dataOk depth datum)
      (variableBack : ∀ depth occurrence, (decorated? decl occurrence).isSome →
        variableOk' depth (v depth occurrence) → variableOk depth occurrence) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk' variableOk' depth type (mapFrame language decl f v depth type pattern) →
          FrameAll language decl dataOk variableOk depth type pattern
    | depth, type, .apply label arguments, all => by
      reflect_cases (.apply label arguments)
      dsimp only
      cases found : paramTypes language label with
      | none => trivial
      | some types =>
        dsimp only
        rw [mapFrame_apply_structural data occurs found] at structural all
        rw [FrameAll.eq_def, if_neg data, if_neg structural] at all
        simp only [found] at all
        exact frameAllArgs_reflect keeps bodyNotData dataBack variableBack depth types arguments all
    | depth, type, .lambda binder body, all => by
      reflect_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only
        rw [mapFrame_lambda data, FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])] at all
        exact frameAll_reflect keeps bodyNotData dataBack variableBack (depth + 1) codomain body all
      | _ => trivial
    | depth, type, .multiLambda arity binders body, all => by
      reflect_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only
        rw [mapFrame_multiLambda data, FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])] at all
        exact frameAll_reflect keeps bodyNotData dataBack variableBack (depth + arity) codomain body all
      | _ => trivial
    | depth, type, .collection kind elements rest, all => by
      reflect_cases (.collection kind elements rest)
      dsimp only
      cases found : elementType language type kind with
      | none => trivial
      | some element =>
        dsimp only
        rw [mapFrame_collection data found, FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])] at all
        simp only [found] at all
        exact frameAllList_reflect keeps bodyNotData dataBack variableBack depth element elements all
    | depth, type, .bvar index, all => by reflect_cases (.bvar index); trivial
    | depth, type, .fvar name, all => by reflect_cases (.fvar name); trivial
    | depth, type, .subst body replacement, all => by reflect_cases (.subst body replacement); trivial
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllArgs_reflect {f v : Nat → Pattern → Pattern}
      {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (keeps : KeepsOccurrences decl v) (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      (dataBack : ∀ depth datum, dataOk' depth (f depth datum) → dataOk depth datum)
      (variableBack : ∀ depth occurrence, (decorated? decl occurrence).isSome →
        variableOk' depth (v depth occurrence) → variableOk depth occurrence) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk' variableOk' depth types (mapFrameArgs language decl f v depth types arguments) →
          FrameAllArgs language decl dataOk variableOk depth types arguments
    | depth, type :: types, argument :: arguments, all => by
      rw [mapFrameArgs, FrameAllArgs] at all
      rw [FrameAllArgs]
      exact ⟨frameAll_reflect keeps bodyNotData dataBack variableBack depth type argument all.1,
        frameAllArgs_reflect keeps bodyNotData dataBack variableBack depth types arguments all.2⟩
    | depth, [], arguments, _ => by simp [FrameAllArgs]
    | depth, _ :: _, [], _ => by simp [FrameAllArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem frameAllList_reflect {f v : Nat → Pattern → Pattern}
      {dataOk variableOk dataOk' variableOk' : Nat → Pattern → Prop}
      (keeps : KeepsOccurrences decl v) (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      (dataBack : ∀ depth datum, dataOk' depth (f depth datum) → dataOk depth datum)
      (variableBack : ∀ depth occurrence, (decorated? decl occurrence).isSome →
        variableOk' depth (v depth occurrence) → variableOk depth occurrence) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk' variableOk' depth element
            (mapFrameList language decl f v depth element patterns) →
          FrameAllList language decl dataOk variableOk depth element patterns
    | depth, element, [], _ => by rw [FrameAllList]; trivial
    | depth, element, pattern :: patterns, all => by
      rw [mapFrameList, FrameAllList] at all
      rw [FrameAllList]
      exact ⟨frameAll_reflect keeps bodyNotData dataBack variableBack depth element pattern all.1,
        frameAllList_reflect keeps bodyNotData dataBack variableBack depth element patterns all.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Walks

/-! ## The normal form -/

section Normal

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- A function on patterns that, on data words, denotes the function `Φ` on `G ∗ F(V)`. -/
def WordMap (reading : DataReading decl G) (φ : Pattern → Pattern) (Φ : FreeData G → FreeData G) : Prop :=
  ∀ ⦃word : Pattern⦄ ⦃found : List (Letter G)⦄, letters decl reading.constant word = some found →
    ∃ again, letters decl reading.constant (φ word) = some again ∧ evalLetters again = Φ (evalLetters found)

/-- The normal form of a data word is a data word of the same value. -/
theorem letters_wordNormal {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) :
    ∃ again, letters decl reading.constant (wordNormal decl reading word) = some again ∧
      evalLetters again = evalLetters found := by
  obtain ⟨again, againParsed, value⟩ := letters_renderWord (reading := reading) (reduce found)
  refine ⟨again, ?_, by rw [value, eval_reduce]⟩
  unfold wordNormal
  rw [parsed]
  exact againParsed

/-- **A word map sees through the normal form**: normalizing its argument changes nothing after it. -/
theorem wordNormal_map_normal {φ : Pattern → Pattern} {Φ : FreeData G → FreeData G} (map : WordMap reading φ Φ)
    (word : Pattern) :
    wordNormal decl reading (φ (wordNormal decl reading word)) = wordNormal decl reading (φ word) := by
  cases parsed : letters decl reading.constant word with
  | none =>
    have same : wordNormal decl reading word = word := by
      unfold wordNormal
      rw [parsed]
    rw [same]
  | some found =>
    obtain ⟨normal, normalParsed, normalValue⟩ := letters_wordNormal parsed
    obtain ⟨first, firstParsed, firstValue⟩ := map normalParsed
    obtain ⟨second, secondParsed, secondValue⟩ := map parsed
    exact (wordNormal_eq_iff firstParsed secondParsed).mpr (by rw [firstValue, secondValue, normalValue])

omit [DecidableEq G] in
theorem wordMap_id : WordMap reading id id := fun _ found parsed => ⟨found, parsed, rfl⟩

/-- **The word normal form is idempotent**, on every pattern. -/
theorem wordNormal_normal (word : Pattern) :
    wordNormal decl reading (wordNormal decl reading word) = wordNormal decl reading word :=
  wordNormal_map_normal wordMap_id word

theorem wordNormal_write (x : G) : wordNormal decl reading (reading.write x) = reading.write x :=
  wordNormal_closed (reading.read_write x)

/-- The normal form keeps occurrences, and decorates every one. -/
theorem normalVariable_keeps : KeepsOccurrences decl (normalVariable decl reading) where
  occurs depth pattern found := by
    obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨bare, _, _⟩ := decorated?_shape found
    unfold normalVariable
    rw [found]
    cases coefficient <;> simp only [decorated?_action _ _ bare, Option.isSome_some]
  notBare depth pattern found _ := by
    obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp found
    unfold normalVariable
    rw [found]
    cases coefficient <;> rfl

/-- A decorated occurrence in normal form. -/
theorem normalVariable_decorated {coefficient occurrenceVar : Pattern} (bare : isBare occurrenceVar = true)
    (depth : Nat) :
    normalVariable decl reading depth (.apply decl.action [coefficient, occurrenceVar]) =
      .apply decl.action [wordNormal decl reading coefficient, occurrenceVar] := by
  unfold normalVariable
  rw [decorated?_action _ _ bare]

/-- A bare occurrence in normal form: decorated by the unit. -/
theorem normalVariable_bare {occurrenceVar : Pattern} (bare : isBare occurrenceVar = true) (depth : Nat) :
    normalVariable decl reading depth occurrenceVar = .apply decl.action [reading.write 1, occurrenceVar] := by
  unfold normalVariable
  match occurrenceVar, bare with
  | .bvar index, _ => rfl
  | .fvar name, _ => rfl

theorem normalVariable_idem (depth : Nat) {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome) :
    normalVariable decl reading depth (normalVariable decl reading depth occurrence) =
      normalVariable decl reading depth occurrence := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    rw [plain rfl, normalVariable_bare bare, normalVariable_decorated bare, wordNormal_write]
  | some c =>
    rw [applied c rfl, normalVariable_decorated bare, normalVariable_decorated bare, wordNormal_normal]

/-- **The normal-form walk does not see its depth.** -/
theorem normalWalk_depth (depth : Nat) (type : TypeExpr) (pattern : Pattern) :
    normalWalkAt (language := language) reading depth type pattern = frameNormal language decl reading type pattern := by
  unfold normalWalkAt frameNormal
  have shifted := mapFrame_shift (language := language) (decl := decl)
    (f := fun _ datum => wordNormal decl reading datum) (v := normalVariable decl reading) depth 0 type pattern
  rw [Nat.zero_add] at shifted
  exact shifted

/-- The positions of a walk, each an occurrence where an occurrence is asked for. -/
theorem frameAll_occurs (depth : Nat) (type : TypeExpr) (pattern : Pattern) :
    FrameAll language decl (fun _ _ => True) (fun _ occurrence => (decorated? decl occurrence).isSome) depth type
      pattern :=
  frameAll_of (fun _ _ => trivial) (fun _ _ occurs => occurs) depth type pattern

/-- **The normal form is idempotent.** -/
theorem normalWalk_idem (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) (depth : Nat)
    (type : TypeExpr) (pattern : Pattern) :
    normalWalkAt (language := language) reading depth type (normalWalkAt (language := language) reading depth type pattern) =
      normalWalkAt (language := language) reading depth type pattern := by
  unfold normalWalkAt
  rw [mapFrame_comp normalVariable_keeps bodyNotData]
  apply mapFrame_congr _ _ depth type pattern (frameAll_occurs depth type pattern)
  · intro _ datum _
    exact wordNormal_normal datum
  · intro k occurrence occurs
    exact normalVariable_idem k occurs

theorem frameNormal_idem (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) (type : TypeExpr)
    (pattern : Pattern) :
    frameNormal language decl reading type (frameNormal language decl reading type pattern) =
      frameNormal language decl reading type pattern :=
  normalWalk_idem bodyNotData 0 type pattern

end Normal

/-! ## The action respects the normal form -/

section Action

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- The conjugated coefficient of a decoration bound inside the acted term. -/
abbrev conjugateWord (g : Pattern) (depth : Nat) (word : Pattern) : Pattern :=
  mulWord decl (actData decl g depth word) (invWord decl (Substitution.liftBVars 0 depth g))

omit [DecidableEq G] in
theorem wordMap_actData {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x) (depth : Nat) :
    WordMap reading (actData decl g depth) (fun element => constEval x * frameHom x depth element) :=
  fun _ _ parsed => letters_actData gRead depth parsed

omit [DecidableEq G] in
theorem wordMap_conjugate {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x) (depth : Nat) :
    WordMap reading (conjugateWord (decl := decl) g depth)
      (fun element => constEval x * frameHom x depth element * (constEval x)⁻¹) :=
  fun _ _ parsed => letters_conjugate gRead depth parsed

omit [DecidableEq G] in
theorem letters_write_one :
    ∃ found, letters decl reading.constant (reading.write 1) = some found ∧ evalLetters found = 1 := by
  obtain ⟨found, parsed, value⟩ := letters_of_read reading.constant (reading.write 1) (reading.read_write 1)
  exact ⟨found, parsed, value.trans constEval_one⟩

/-- **At an occurrence, the action sees through the normal form.** -/
theorem actVariable_normal {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x) (depth : Nat)
    {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome) :
    normalVariable decl reading depth (actVariable decl g depth (normalVariable decl reading depth occurrence)) =
      normalVariable decl reading depth (actVariable decl g depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have gLift := liftBVars_closed gRead 0 depth
  obtain ⟨unitLetters, unitParsed, unitValue⟩ := letters_write_one (reading := reading)
  obtain ⟨gLetters, gParsed, gValue⟩ := letters_of_read reading.constant g gRead
  obtain ⟨acted, actedParsed, actedValue⟩ := letters_actData gRead depth unitParsed
  have actedUnit : wordNormal decl reading (actData decl g depth (reading.write 1)) = wordNormal decl reading g :=
    (wordNormal_eq_iff actedParsed gParsed).mpr (by rw [actedValue, unitValue, map_one, mul_one, gValue])
  cases coefficient with
  | none =>
    rw [plain rfl, normalVariable_bare bare]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside g _ inside, actVariable_bare_inside g inside, normalVariable_bare bare,
          normalVariable_decorated bare]
        obtain ⟨conjugated, conjugatedParsed, conjugatedValue⟩ := letters_conjugate gRead depth unitParsed
        have trivialConjugate : wordNormal decl reading (conjugateWord (decl := decl) g depth (reading.write 1)) =
            wordNormal decl reading (reading.write 1) :=
          (wordNormal_eq_iff conjugatedParsed unitParsed).mpr
            (by rw [conjugatedValue, unitValue, map_one, mul_one, mul_inv_cancel])
        rw [trivialConjugate, wordNormal_write]
      · rw [actVariable_decorated_outside g _ inside, actVariable_bare_outside g inside, gLift,
          normalVariable_decorated bare, normalVariable_decorated bare, actedUnit]
    | .fvar name, bare =>
      rw [actVariable_decorated_free, actVariable_bare_free, gLift, normalVariable_decorated bare,
        normalVariable_decorated bare, actedUnit]
  | some c =>
    rw [applied c rfl, normalVariable_decorated bare]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside g _ inside, actVariable_decorated_inside g _ inside,
          normalVariable_decorated bare, normalVariable_decorated bare,
          wordNormal_map_normal (wordMap_conjugate gRead depth) c]
      · rw [actVariable_decorated_outside g _ inside, actVariable_decorated_outside g _ inside,
          normalVariable_decorated bare, normalVariable_decorated bare,
          wordNormal_map_normal (wordMap_actData gRead depth) c]
    | .fvar name, bare =>
      rw [actVariable_decorated_free, actVariable_decorated_free, normalVariable_decorated bare,
        normalVariable_decorated bare, wordNormal_map_normal (wordMap_actData gRead depth) c]

/-- **The action respects the normal form**: normalizing before acting changes nothing after. -/
theorem actWalk_normal (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {g : Pattern} {x : G}
    (gRead : read decl reading.constant g = some x) (depth : Nat) (type : TypeExpr) (pattern : Pattern) :
    normalWalkAt (language := language) reading depth type
        (actWalkAt (language := language) (decl := decl) g depth type
          (normalWalkAt (language := language) reading depth type pattern)) =
      normalWalkAt (language := language) reading depth type
        (actWalkAt (language := language) (decl := decl) g depth type pattern) := by
  unfold normalWalkAt actWalkAt
  rw [mapFrame_comp normalVariable_keeps bodyNotData,
    mapFrame_comp (KeepsOccurrences.comp normalVariable_keeps (actVariable_keeps g)) bodyNotData,
    mapFrame_comp (actVariable_keeps g) bodyNotData]
  apply mapFrame_congr _ _ depth type pattern (frameAll_occurs depth type pattern)
  · intro k datum _
    exact wordNormal_map_normal (wordMap_actData gRead k) datum
  · intro k occurrence occurs
    exact actVariable_normal gRead k occurs

theorem frameAct_normal (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {g : Pattern} {x : G}
    (gRead : read decl reading.constant g = some x) (type : TypeExpr) (pattern : Pattern) :
    frameNormal language decl reading type
        (frameAct language decl g type (frameNormal language decl reading type pattern)) =
      frameNormal language decl reading type (frameAct language decl g type pattern) :=
  actWalk_normal bodyNotData gRead 0 type pattern

/-- **Terms of one normal form are acted on into terms of one normal form.** -/
theorem frameAct_respects (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {g : Pattern}
    {x : G} (gRead : read decl reading.constant g = some x) (type : TypeExpr) {first second : Pattern}
    (same : frameNormal language decl reading type first = frameNormal language decl reading type second) :
    frameNormal language decl reading type (frameAct language decl g type first) =
      frameNormal language decl reading type (frameAct language decl g type second) := by
  rw [← frameAct_normal bodyNotData gRead type first, same, frameAct_normal bodyNotData gRead type second]

/-- At an occurrence, words of one value act alike, in normal form. -/
theorem actVariable_congr {g h : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    (hRead : read decl reading.constant h = some x) (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (parses : CoefficientParses reading occurrence) :
    normalVariable decl reading depth (actVariable decl g depth occurrence) =
      normalVariable decl reading depth (actVariable decl h depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have gLift := liftBVars_closed gRead 0 depth
  have hLift := liftBVars_closed hRead 0 depth
  cases coefficient with
  | none =>
    rw [plain rfl]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside g inside, actVariable_bare_inside h inside]
      · rw [actVariable_bare_outside g inside, actVariable_bare_outside h inside, gLift, hLift,
          normalVariable_decorated bare, normalVariable_decorated bare, wordNormal_closed gRead,
          wordNormal_closed hRead]
    | .fvar name, bare =>
      rw [actVariable_bare_free, actVariable_bare_free, gLift, hLift, normalVariable_decorated bare,
        normalVariable_decorated bare, wordNormal_closed gRead, wordNormal_closed hRead]
  | some c =>
    rw [applied c rfl]
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (parses c occurrenceVar found)
    obtain ⟨gActed, gActedParsed, gActedValue⟩ := letters_actData gRead depth cParsed
    obtain ⟨hActed, hActedParsed, hActedValue⟩ := letters_actData hRead depth cParsed
    have actedSame : wordNormal decl reading (actData decl g depth c) = wordNormal decl reading (actData decl h depth c) :=
      (wordNormal_eq_iff gActedParsed hActedParsed).mpr (by rw [gActedValue, hActedValue])
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside g _ inside, actVariable_decorated_inside h _ inside]
        apply normalVariable_congr depth bare
        obtain ⟨gConjugated, gParsed, gValue⟩ := letters_conjugate gRead depth cParsed
        obtain ⟨hConjugated, hParsed, hValue⟩ := letters_conjugate hRead depth cParsed
        exact (wordNormal_eq_iff gParsed hParsed).mpr (by rw [gValue, hValue])
      · rw [actVariable_decorated_outside g _ inside, actVariable_decorated_outside h _ inside]
        exact normalVariable_congr depth bare actedSame
    | .fvar name, bare =>
      rw [actVariable_decorated_free, actVariable_decorated_free]
      exact normalVariable_congr depth bare actedSame

/-- What the value-dependence law asks of a term at a depth: its data and its decorations'
coefficients are data words. -/
abbrev WordsParseAt (reading : DataReading decl G) (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Prop :=
  FrameAll language decl (fun _ datum => (letters decl reading.constant datum).isSome)
    (fun _ occurrence => (decorated? decl occurrence).isSome ∧ CoefficientParses reading occurrence) depth type pattern

/-- **The action depends on the acting element alone**, in normal form. -/
theorem actWalk_congr (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {g h : Pattern} {x : G}
    (gRead : read decl reading.constant g = some x) (hRead : read decl reading.constant h = some x) (depth : Nat)
    (type : TypeExpr) (pattern : Pattern) (parse : WordsParseAt (language := language) reading depth type pattern) :
    normalWalkAt (language := language) reading depth type
        (actWalkAt (language := language) (decl := decl) g depth type pattern) =
      normalWalkAt (language := language) reading depth type
        (actWalkAt (language := language) (decl := decl) h depth type pattern) := by
  unfold normalWalkAt actWalkAt
  rw [mapFrame_comp (actVariable_keeps g) bodyNotData, mapFrame_comp (actVariable_keeps h) bodyNotData]
  apply mapFrame_congr _ _ depth type pattern parse
  · intro k datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    obtain ⟨gActed, gParsed, gValue⟩ := letters_actData gRead k parsed
    obtain ⟨hActed, hParsed, hValue⟩ := letters_actData hRead k parsed
    exact (wordNormal_eq_iff gParsed hParsed).mpr (by rw [gValue, hValue])
  · intro k occurrence ⟨occurs, parses⟩
    exact actVariable_congr gRead hRead k occurs parses

theorem frameAct_congr (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {g h : Pattern} {x : G}
    (gRead : read decl reading.constant g = some x) (hRead : read decl reading.constant h = some x)
    (type : TypeExpr) (pattern : Pattern) (parse : WordsParse language reading type pattern) :
    frameNormal language decl reading type (frameAct language decl g type pattern) =
      frameNormal language decl reading type (frameAct language decl h type pattern) :=
  actWalk_congr bodyNotData gRead hRead 0 type pattern parse

end Action

/-! ## Instantiating a datum respects the normal form -/

section Datum

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

omit [DecidableEq G] in
theorem wordMap_instantiate {datum : Pattern} {y : G} (datumRead : read decl reading.constant datum = some y)
    (depth : Nat) :
    WordMap reading (Substitution.instantiateBVarAt depth datum) (instHom y depth) :=
  fun word _ parsed => letters_instantiate datumRead depth word parsed

omit [Group G] [DecidableEq G] in
/-- A variable function that keeps occurrences, followed by one that keeps a coefficient, keeps a
coefficient. -/
theorem KeepsNotBare.after {first second : Nat → Pattern → Pattern} (keepsFirst : KeepsOccurrences decl first)
    (keepsSecond : KeepsNotBare decl second) :
    KeepsNotBare decl (fun depth pattern => second depth (first depth pattern)) :=
  fun depth pattern occurs notBare =>
    keepsSecond depth _ (keepsFirst.occurs depth pattern occurs) (keepsFirst.notBare depth pattern occurs notBare)

omit [Group G] [DecidableEq G] in
theorem decorated?_of_bare {occurrenceVar : Pattern} (bare : isBare occurrenceVar = true) :
    decorated? decl occurrenceVar = some (none, occurrenceVar) := by
  match occurrenceVar, bare with
  | .bvar index, _ => rfl
  | .fvar name, _ => rfl

omit [Group G] [DecidableEq G] in
/-- A bare variable other than the instantiated one loses the level and stays bare. -/
theorem instantiate_bare {occurrenceVar : Pattern} (bare : isBare occurrenceVar = true) {depth : Nat}
    (notLevel : occurrenceVar ≠ .bvar depth) (datum : Pattern) :
    isBare (Substitution.instantiateBVarAt depth datum occurrenceVar) = true := by
  match occurrenceVar, bare with
  | .bvar index, _ =>
    have indexNe : index ≠ depth := fun equal => notLevel (by rw [equal])
    by_cases below : index < depth
    · simp [Substitution.instantiateBVarAt, below, isBare]
    · simp [Substitution.instantiateBVarAt, below, indexNe, isBare]
  | .fvar name, _ => simp [Substitution.instantiateBVarAt, isBare]

/-- **At an occurrence other than the instantiated variable, instantiating a datum sees through the
normal form.** -/
theorem instDatumVariable_normal (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {datum : Pattern} {y : G}
    (datumRead : read decl reading.constant datum = some y) (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome)
    (notLevel : ∀ c v, decorated? decl occurrence = some (c, v) → v ≠ .bvar depth) :
    normalWalkAt (language := language) reading depth bodyType
        (Substitution.instantiateBVarAt depth datum (normalVariable decl reading depth occurrence)) =
      normalWalkAt (language := language) reading depth bodyType
        (Substitution.instantiateBVarAt depth datum occurrence) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have lowered := instantiate_bare bare (notLevel _ _ found) datum
  have actionInst : ∀ c, Substitution.instantiateBVarAt depth datum (.apply decl.action [c, occurrenceVar]) =
      .apply decl.action [Substitution.instantiateBVarAt depth datum c,
        Substitution.instantiateBVarAt depth datum occurrenceVar] := fun c => by
    simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil]
  have atAction : ∀ c, normalWalkAt (language := language) reading depth bodyType
      (.apply decl.action [c, Substitution.instantiateBVarAt depth datum occurrenceVar]) =
        .apply decl.action [wordNormal decl reading c, Substitution.instantiateBVarAt depth datum occurrenceVar] :=
    fun c => by
      unfold normalWalkAt
      rw [mapFrame_variable notData ⟨by rw [decorated?_action _ _ lowered]; rfl, bodySort⟩,
        normalVariable_decorated lowered]
  cases coefficient with
  | none =>
    rw [plain rfl, normalVariable_bare bare, actionInst, atAction,
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped (reading.read_write 1) depth),
      wordNormal_write]
    unfold normalWalkAt
    rw [mapFrame_variable notData ⟨by rw [decorated?_of_bare lowered]; rfl, bodySort⟩, normalVariable_bare lowered]
  | some c =>
    rw [applied c rfl, normalVariable_decorated bare, actionInst, actionInst, atAction, atAction,
      wordNormal_map_normal (wordMap_instantiate datumRead depth) c]

/-- No occurrence of the body sort is the variable of the walk's level. -/
abbrev AvoidsLevel (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Prop :=
  FrameAll language decl (fun _ _ => True)
    (fun k occurrence => (decorated? decl occurrence).isSome ∧
      ∀ c v, decorated? decl occurrence = some (c, v) → v ≠ .bvar k) depth type pattern

/-- **Instantiating a datum respects the normal form**, at terms whose occurrences of the body sort are
not the instantiated variable. -/
theorem instDatumWalk_normal (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {datum : Pattern} {y : G}
    (datumRead : read decl reading.constant datum = some y) (depth : Nat) (type : TypeExpr) (pattern : Pattern)
    (avoids : AvoidsLevel (language := language) (decl := decl) depth type pattern) :
    normalWalkAt (language := language) reading depth type
        (mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
          (fun k occurrence => Substitution.instantiateBVarAt k datum occurrence) depth type
          (normalWalkAt (language := language) reading depth type pattern)) =
      normalWalkAt (language := language) reading depth type
        (mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
          (fun k occurrence => Substitution.instantiateBVarAt k datum occurrence) depth type pattern) := by
  unfold normalWalkAt
  rw [mapFrame_comp normalVariable_keeps bodyNotData,
    mapFrame_fuse (KeepsNotBare.after normalVariable_keeps (instantiate_keepsNotBare datum)) bodyNotData bodySort,
    mapFrame_fuse (instantiate_keepsNotBare datum) bodyNotData bodySort]
  apply mapFrame_congr _ _ depth type pattern avoids
  · intro k word _
    exact wordNormal_map_normal (wordMap_instantiate datumRead k) word
  · intro k occurrence ⟨occurs, notLevel⟩
    exact instDatumVariable_normal bodyNotData bodySort datumRead k occurs notLevel

end Datum

end Mettapedia.OSLF.MeTTaIL.Orientation
