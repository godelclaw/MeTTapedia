import Mettapedia.OSLF.MeTTaIL.OrientationWords
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Data.Int.Cast.Lemmas

/-!
# The frame-normal action

In Meredith's oriented processes a variable occurs *decorated*, `^k X`, with the action pending on it
until substitution discharges it: `(^k X)σ = k · σ(X)`. The action of `g` multiplies every datum on
the left and composes with every decoration, `g · ^k X = ^(g k) X`. Binding occurrences are kept
undecorated by (FRAME), which renames the frame of a bound variable uniformly: a data variable `δ`
bound inside the acted term becomes `g⁻¹ · δ` throughout its scope, and a decoration `^w Z` of a
process variable bound inside becomes `^(w g⁻¹) Z`. The action in this frame-normal form is
`frameAct`:

- at a data position, the datum `w` becomes `g · w`, with each data variable bound inside renamed
  to `g⁻¹ · δ` (`frameWord`); a bare bound `δ` becomes `g · g⁻¹ · δ`, which is `δ` in normal form;
- at a position of the action's body sort, a variable bound inside keeps its frame (`^(g e g⁻¹) = ^e`),
  a decorated one is conjugated, `^w Z ↦ ^(g w g⁻¹) Z`, and a free variable is deferred, `X ↦ ^g X`,
  `^w X ↦ ^(g w) X`;
- everywhere else the action follows the declared parameter types, entering binders.

A decoration is written with the action constructor, `PAct w X`. `settle` evaluates action nodes
from the inside out and keeps the ones on variables, which are decorations.

The traversal is one generic walk, `mapFrame`, given what to do at a data position and at a
variable of the action's body sort, both knowing how many binders the walk has entered. Walks agree
where their functions agree (`mapFrame_congr`), and two walks are one (`mapFrame_comp`).

(FRAME) inside a datum is the endomorphism `frameHom x` of `G ∗ F(V)` that renames each bound
variable `δ ↦ x⁻¹ δ` (`letters_frameWord`); renaming twice is renaming by the product
(`frameHom_mul`). From these:

- `frameAct_mul`: acting by `h` and then by `g` is acting by `g · h`;
- `frameAct_one`: the unit acts trivially;

both in normal form (`frameNormal`: data and decorations in the normal form of `G ∗ F(V)`, every
occurrence decorated), for a language whose action does not act on data, on terms whose data and
decorations are data words (`WordsParse`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

variable (language : LanguageDef) (decl : OrientationDecl)

/-- The product word. -/
def mulWord (left right : Pattern) : Pattern := .apply decl.multiply [left, right]

/-- The inverse word. -/
def invWord (word : Pattern) : Pattern := .apply decl.inverse [word]

/-- The sort the action acts on: the type of its second parameter. -/
def actionType : Option TypeExpr :=
  match paramTypes language decl.action with
  | some [_, body] => some body
  | _ => none

/-- A variable occurrence, decorated or not, at the action's body sort. -/
def decorated? : Pattern → Option (Option Pattern × Pattern)
  | .bvar index => some (none, .bvar index)
  | .fvar name => some (none, .fvar name)
  | .apply label [coefficient, .bvar index] =>
      if label = decl.action then some (some coefficient, .bvar index) else none
  | .apply label [coefficient, .fvar name] =>
      if label = decl.action then some (some coefficient, .fvar name) else none
  | _ => none

mutual
  /-- **The generic frame walk**: `onData depth datum` at every data position, `onVariable depth
  occurrence` at every variable occurrence of the action's body sort, decorated or not, following the
  declared parameter types everywhere else. -/
  def mapFrame (onData onVariable : Nat → Pattern → Pattern) (depth : Nat) (type : TypeExpr)
      (pattern : Pattern) : Pattern :=
    if type = .base decl.dataSort then onData depth pattern
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then
      onVariable depth pattern
    else
      match pattern with
      | .apply label arguments =>
          match paramTypes language label with
          | some types => .apply label (mapFrameArgs onData onVariable depth types arguments)
          | none => .apply label arguments
      | .lambda binder body =>
          match type with
          | .arrow _ codomain => .lambda binder (mapFrame onData onVariable (depth + 1) codomain body)
          | _ => .lambda binder body
      | .multiLambda arity binders body =>
          match type with
          | .arrow _ codomain =>
              .multiLambda arity binders (mapFrame onData onVariable (depth + arity) codomain body)
          | _ => .multiLambda arity binders body
      | .collection kind elements rest =>
          match elementType language type kind with
          | some element => .collection kind (mapFrameList onData onVariable depth element elements) rest
          | none => .collection kind elements rest
      | other => other
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def mapFrameArgs (onData onVariable : Nat → Pattern → Pattern) (depth : Nat) :
      List TypeExpr → List Pattern → List Pattern
    | type :: types, argument :: arguments =>
        mapFrame onData onVariable depth type argument :: mapFrameArgs onData onVariable depth types arguments
    | _, arguments => arguments
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def mapFrameList (onData onVariable : Nat → Pattern → Pattern) (depth : Nat) (element : TypeExpr) :
      List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        mapFrame onData onVariable depth element pattern :: mapFrameList onData onVariable depth element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- The positions of the walk satisfy `dataOk` at data and `variableOk` at variables of the body
  sort. -/
  def FrameAll (dataOk variableOk : Nat → Pattern → Prop) (depth : Nat) (type : TypeExpr)
      (pattern : Pattern) : Prop :=
    if type = .base decl.dataSort then dataOk depth pattern
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then
      variableOk depth pattern
    else
      match pattern with
      | .apply label arguments =>
          match paramTypes language label with
          | some types => FrameAllArgs dataOk variableOk depth types arguments
          | none => True
      | .lambda _ body =>
          match type with
          | .arrow _ codomain => FrameAll dataOk variableOk (depth + 1) codomain body
          | _ => True
      | .multiLambda arity _ body =>
          match type with
          | .arrow _ codomain => FrameAll dataOk variableOk (depth + arity) codomain body
          | _ => True
      | .collection kind elements _ =>
          match elementType language type kind with
          | some element => FrameAllList dataOk variableOk depth element elements
          | none => True
      | _ => True
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def FrameAllArgs (dataOk variableOk : Nat → Pattern → Prop) (depth : Nat) :
      List TypeExpr → List Pattern → Prop
    | type :: types, argument :: arguments =>
        FrameAll dataOk variableOk depth type argument ∧ FrameAllArgs dataOk variableOk depth types arguments
    | _, _ => True
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def FrameAllList (dataOk variableOk : Nat → Pattern → Prop) (depth : Nat) (element : TypeExpr) :
      List Pattern → Prop
    | [] => True
    | pattern :: patterns =>
        FrameAll dataOk variableOk depth element pattern ∧ FrameAllList dataOk variableOk depth element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

section Walk

variable {language decl}

/-- The data and variable branches of a walk step; leaves the structural branch. -/
syntax "frame_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| frame_cases) => `(tactic| (
      rw [FrameAll.eq_def] at all
      rw [mapFrame.eq_def language decl f v, mapFrame.eq_def language decl f' v']
      split_ifs at all ⊢ with data occurs
      · exact agreeData _ _ all
      · exact agreeVariable _ _ all))

mutual
  /-- **Walks agree** where their functions agree on the positions they visit. -/
  theorem mapFrame_congr {f f' v v' : Nat → Pattern → Pattern} {dataOk variableOk : Nat → Pattern → Prop}
      (agreeData : ∀ depth datum, dataOk depth datum → f depth datum = f' depth datum)
      (agreeVariable : ∀ depth occurrence, variableOk depth occurrence → v depth occurrence = v' depth occurrence) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        FrameAll language decl dataOk variableOk depth type pattern →
          mapFrame language decl f v depth type pattern = mapFrame language decl f' v' depth type pattern
    | depth, type, .apply label arguments, all => by
      frame_cases
      dsimp only at all ⊢
      cases found : paramTypes language label with
      | none => rfl
      | some types =>
        rw [found] at all
        dsimp only at all ⊢
        rw [mapFrameArgs_congr agreeData agreeVariable depth types arguments all]
    | depth, type, .lambda binder body, all => by
      frame_cases
      dsimp only at all ⊢
      cases type with
      | arrow domain codomain =>
        dsimp only at all ⊢
        rw [mapFrame_congr agreeData agreeVariable (depth + 1) codomain body all]
      | _ => rfl
    | depth, type, .multiLambda arity binders body, all => by
      frame_cases
      dsimp only at all ⊢
      cases type with
      | arrow domain codomain =>
        dsimp only at all ⊢
        rw [mapFrame_congr agreeData agreeVariable (depth + arity) codomain body all]
      | _ => rfl
    | depth, type, .collection kind elements rest, all => by
      frame_cases
      dsimp only at all ⊢
      cases found : elementType language type kind with
      | none => rfl
      | some element =>
        rw [found] at all
        dsimp only at all ⊢
        rw [mapFrameList_congr agreeData agreeVariable depth element elements all]
    | depth, type, .bvar index, all => by frame_cases; rfl
    | depth, type, .fvar name, all => by frame_cases; rfl
    | depth, type, .subst body replacement, all => by frame_cases; rfl
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameArgs_congr {f f' v v' : Nat → Pattern → Pattern} {dataOk variableOk : Nat → Pattern → Prop}
      (agreeData : ∀ depth datum, dataOk depth datum → f depth datum = f' depth datum)
      (agreeVariable : ∀ depth occurrence, variableOk depth occurrence → v depth occurrence = v' depth occurrence) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk depth types arguments →
          mapFrameArgs language decl f v depth types arguments = mapFrameArgs language decl f' v' depth types arguments
    | depth, type :: types, argument :: arguments, all => by
      rw [FrameAllArgs] at all
      rw [mapFrameArgs, mapFrameArgs, mapFrame_congr agreeData agreeVariable depth type argument all.1,
        mapFrameArgs_congr agreeData agreeVariable depth types arguments all.2]
    | depth, [], arguments, _ => by simp [mapFrameArgs]
    | depth, _ :: _, [], _ => by simp [mapFrameArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameList_congr {f f' v v' : Nat → Pattern → Pattern} {dataOk variableOk : Nat → Pattern → Prop}
      (agreeData : ∀ depth datum, dataOk depth datum → f depth datum = f' depth datum)
      (agreeVariable : ∀ depth occurrence, variableOk depth occurrence → v depth occurrence = v' depth occurrence) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk depth element patterns →
          mapFrameList language decl f v depth element patterns = mapFrameList language decl f' v' depth element patterns
    | depth, element, [], _ => by rw [mapFrameList, mapFrameList]
    | depth, element, pattern :: patterns, all => by
      rw [FrameAllList] at all
      rw [mapFrameList, mapFrameList, mapFrame_congr agreeData agreeVariable depth element pattern all.1,
        mapFrameList_congr agreeData agreeVariable depth element patterns all.2]
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- A bare variable. -/
def isBare : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | _ => false

/-- A decorated occurrence has a coefficient exactly when it is not bare. -/
theorem decorated?_bare {pattern : Pattern} {coefficient : Option Pattern} {occurrence : Pattern}
    (found : decorated? decl pattern = some (coefficient, occurrence)) :
    coefficient = none ↔ isBare pattern = true := by
  match pattern with
  | .bvar _ => simp [decorated?] at found; simp [isBare, ← found.1]
  | .fvar _ => simp [decorated?] at found; simp [isBare, ← found.1]
  | .apply label [c, .bvar index] =>
    simp only [decorated?] at found
    split at found
    · cases found; simp [isBare]
    · cases found
  | .apply label [c, .fvar name] =>
    simp only [decorated?] at found
    split at found
    · cases found; simp [isBare]
    · cases found
  | .apply label [] => simp [decorated?] at found
  | .apply label [_] => simp [decorated?] at found
  | .apply label [_, .apply _ _] => simp [decorated?] at found
  | .apply label [_, .lambda _ _] => simp [decorated?] at found
  | .apply label [_, .multiLambda _ _ _] => simp [decorated?] at found
  | .apply label [_, .subst _ _] => simp [decorated?] at found
  | .apply label [_, .collection _ _ _] => simp [decorated?] at found
  | .apply label (_ :: _ :: _ :: _) => simp [decorated?] at found
  | .lambda _ _ => simp [decorated?] at found
  | .multiLambda _ _ _ => simp [decorated?] at found
  | .subst _ _ => simp [decorated?] at found
  | .collection _ _ _ => simp [decorated?] at found

/-- A walk step's variable function keeps occurrences: a decorated occurrence stays decorated, and a
coefficient stays a coefficient. -/
structure KeepsOccurrences (orientation : OrientationDecl) (v : Nat → Pattern → Pattern) : Prop where
  occurs : ∀ depth pattern, (decorated? orientation pattern).isSome →
    (decorated? orientation (v depth pattern)).isSome
  notBare : ∀ depth pattern, (decorated? orientation pattern).isSome → isBare pattern = false →
    isBare (v depth pattern) = false

/-- A walk step's variable function keeps a coefficient: a decorated occurrence that is not bare stays
not bare. -/
def KeepsNotBare (orientation : OrientationDecl) (v : Nat → Pattern → Pattern) : Prop :=
  ∀ depth pattern, (decorated? orientation pattern).isSome → isBare pattern = false → isBare (v depth pattern) = false

theorem mapFrame_notBare {f v : Nat → Pattern → Pattern} (keeps : KeepsNotBare decl v) {depth : Nat}
    {type : TypeExpr} (notData : type ≠ .base decl.dataSort) {pattern : Pattern} (notBare : isBare pattern = false) :
    isBare (mapFrame language decl f v depth type pattern) = false := by
  rw [mapFrame.eq_def, if_neg notData]
  split_ifs with occurs
  · exact keeps depth pattern occurs.1 notBare
  · match pattern with
    | .apply label arguments =>
      dsimp only
      split <;> rfl
    | .lambda binder body =>
      dsimp only
      split <;> rfl
    | .multiLambda arity binders body =>
      dsimp only
      split <;> rfl
    | .collection kind elements rest =>
      dsimp only
      split <;> rfl
    | .subst body replacement => rfl
    | .bvar _ => simp [isBare] at notBare
    | .fvar _ => simp [isBare] at notBare

/-- The structural branch of a walk never makes an occurrence of the body sort, when the action does
not act on data. -/
theorem decorated?_mapFrame_structural {f v : Nat → Pattern → Pattern} (keeps : KeepsNotBare decl v)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {depth : Nat} {type : TypeExpr}
    (notData : type ≠ .base decl.dataSort) {pattern : Pattern}
    (structural : ¬((decorated? decl pattern).isSome ∧ actionType language decl = some type)) :
    ¬((decorated? decl (mapFrame language decl f v depth type pattern)).isSome ∧
      actionType language decl = some type) := by
  rintro ⟨occurs, sort⟩
  have none : decorated? decl pattern = none := by
    cases found : decorated? decl pattern with
    | none => rfl
    | some _ => exact absurd ⟨by simp [found], sort⟩ structural
  rw [mapFrame.eq_def, if_neg notData, if_neg structural] at occurs
  match pattern, none, occurs with
  | .apply label arguments, none, occurs =>
    dsimp only at occurs
    cases typesFound : paramTypes language label with
    | none =>
      rw [typesFound] at occurs
      dsimp only at occurs
      rw [none] at occurs
      cases occurs
    | some types =>
      rw [typesFound] at occurs
      dsimp only at occurs
      by_cases isAction : label = decl.action
      · subst isAction
        have actionTypes : ∃ dataType, types = [dataType, type] := by
          unfold actionType at sort
          rw [typesFound] at sort
          split at sort
          · rename_i dataType body same
            cases sort
            exact ⟨dataType, by simpa using same⟩
          · cases sort
        obtain ⟨dataType, rfl⟩ := actionTypes
        match arguments, none, occurs with
        | [coefficient, body], none, occurs =>
          have bodyNotBare : isBare body = false := by
            cases body <;> simp_all [decorated?, isBare]
          have bodyTypeNotData : type ≠ .base decl.dataSort := fun same => bodyNotData (same ▸ sort)
          have result := mapFrame_notBare (language := language) (f := f) keeps (depth := depth) bodyTypeNotData bodyNotBare
          simp only [mapFrameArgs] at occurs
          generalize mapFrame language decl f v depth type body = changed at occurs result
          cases changed <;> simp_all [decorated?, isBare]
        | [], _, occurs => simp [mapFrameArgs, decorated?] at occurs
        | [_], _, occurs => simp [mapFrameArgs, decorated?] at occurs
        | _ :: _ :: _ :: _, _, occurs => simp [mapFrameArgs, decorated?] at occurs
      · generalize mapFrameArgs language decl f v depth types arguments = changed at occurs
        match changed with
        | [_, .bvar _] => simp [decorated?, isAction] at occurs
        | [_, .fvar _] => simp [decorated?, isAction] at occurs
        | [] => simp [decorated?] at occurs
        | [_] => simp [decorated?] at occurs
        | [_, .apply _ _] => simp [decorated?] at occurs
        | [_, .lambda _ _] => simp [decorated?] at occurs
        | [_, .multiLambda _ _ _] => simp [decorated?] at occurs
        | [_, .subst _ _] => simp [decorated?] at occurs
        | [_, .collection _ _ _] => simp [decorated?] at occurs
        | _ :: _ :: _ :: _ => simp [decorated?] at occurs
  | .lambda binder body, _, occurs =>
    dsimp only at occurs
    split at occurs <;> simp [decorated?] at occurs
  | .multiLambda arity binders body, _, occurs =>
    dsimp only at occurs
    split at occurs <;> simp [decorated?] at occurs
  | .collection kind elements rest, _, occurs =>
    dsimp only at occurs
    split at occurs <;> simp [decorated?] at occurs
  | .subst body replacement, _, occurs => simp [decorated?] at occurs
  | .bvar _, none, _ => simp [decorated?] at none
  | .fvar _, none, _ => simp [decorated?] at none

/-- The data and variable branches of a fused walk step, at a given pattern; leaves the structural
branch with `data`, `occurs` and the inner walk unfolded, and `structural` for the outer one. -/
syntax "comp_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| comp_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [mapFrame.eq_def language decl f₁ v₁ depth type, if_pos data,
          mapFrame.eq_def language decl f₂ v₂ depth type, if_pos data,
          mapFrame.eq_def language decl (fun d x => f₂ d (f₁ d x)) (fun d x => v₂ d (v₁ d x)) depth type,
          if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [mapFrame.eq_def language decl f₁ v₁ depth type, if_neg data, if_pos occurs,
          mapFrame.eq_def language decl f₂ v₂ depth type, if_neg data,
          if_pos ⟨keeps.occurs _ _ occurs.1, occurs.2⟩,
          mapFrame.eq_def language decl (fun d x => f₂ d (f₁ d x)) (fun d x => v₂ d (v₁ d x)) depth type,
          if_neg data, if_pos occurs]
      have structural := decorated?_mapFrame_structural (language := language) (f := f₁) (depth := depth)
        keeps.notBare bodyNotData data occurs
      rw [mapFrame.eq_def language decl f₁ v₁ depth type, if_neg data, if_neg occurs] at structural ⊢
      rw [mapFrame.eq_def language decl f₂ v₂ depth type, if_neg data, if_neg structural,
        mapFrame.eq_def language decl (fun d x => f₂ d (f₁ d x)) (fun d x => v₂ d (v₁ d x)) depth type,
        if_neg data, if_neg occurs]))

mutual
  /-- **Two walks are one walk**, when the first keeps occurrences and the action does not act on
  data. -/
  theorem mapFrame_comp {f₁ v₁ f₂ v₂ : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v₁)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        mapFrame language decl f₂ v₂ depth type (mapFrame language decl f₁ v₁ depth type pattern) =
          mapFrame language decl (fun d x => f₂ d (f₁ d x)) (fun d x => v₂ d (v₁ d x)) depth type pattern
    | depth, type, .apply label arguments => by
      comp_cases (.apply label arguments)
      cases found : paramTypes language label with
      | none => simp only [found]
      | some types =>
        simp only [found]
        rw [mapFrameArgs_comp keeps bodyNotData depth types arguments]
    | depth, type, .lambda binder body => by
      comp_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        simp only
        rw [mapFrame_comp keeps bodyNotData (depth + 1) codomain body]
      | _ => rfl
    | depth, type, .multiLambda arity binders body => by
      comp_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        simp only
        rw [mapFrame_comp keeps bodyNotData (depth + arity) codomain body]
      | _ => rfl
    | depth, type, .collection kind elements rest => by
      comp_cases (.collection kind elements rest)
      cases found : elementType language type kind with
      | none => simp only [found]
      | some element =>
        simp only [found]
        rw [mapFrameList_comp keeps bodyNotData depth element elements]
    | depth, type, .bvar index => by comp_cases (.bvar index)
    | depth, type, .fvar name => by comp_cases (.fvar name)
    | depth, type, .subst body replacement => by comp_cases (.subst body replacement)
  termination_by _ _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameArgs_comp {f₁ v₁ f₂ v₂ : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v₁)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        mapFrameArgs language decl f₂ v₂ depth types (mapFrameArgs language decl f₁ v₁ depth types arguments) =
          mapFrameArgs language decl (fun d x => f₂ d (f₁ d x)) (fun d x => v₂ d (v₁ d x)) depth types arguments
    | depth, type :: types, argument :: arguments => by
      rw [mapFrameArgs, mapFrameArgs, mapFrameArgs, mapFrame_comp keeps bodyNotData depth type argument,
        mapFrameArgs_comp keeps bodyNotData depth types arguments]
    | depth, [], arguments => by simp [mapFrameArgs]
    | depth, _ :: _, [] => by simp [mapFrameArgs]
  termination_by _ _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameList_comp {f₁ v₁ f₂ v₂ : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v₁)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        mapFrameList language decl f₂ v₂ depth element (mapFrameList language decl f₁ v₁ depth element patterns) =
          mapFrameList language decl (fun d x => f₂ d (f₁ d x)) (fun d x => v₂ d (v₁ d x)) depth element patterns
    | depth, element, [] => by simp [mapFrameList]
    | depth, element, pattern :: patterns => by
      rw [mapFrameList, mapFrameList, mapFrameList, mapFrame_comp keeps bodyNotData depth element pattern,
        mapFrameList_comp keeps bodyNotData depth element patterns]
  termination_by _ _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Walk

mutual
  /-- **(FRAME) inside a datum**: every data variable bound inside the acted term, `δ`, becomes
  `g⁻¹ · δ`. -/
  def frameWord (g : Pattern) (depth : Nat) : Pattern → Pattern
    | .bvar index => if index < depth then mulWord decl (invWord decl g) (.bvar index) else .bvar index
    | .apply label arguments => .apply label (frameWords g depth arguments)
    | other => other

  def frameWords (g : Pattern) (depth : Nat) : List Pattern → List Pattern
    | [] => []
    | argument :: arguments => frameWord g depth argument :: frameWords g depth arguments
end

/-- The action at a data position, `depth` binders inside the acted term. -/
def actData (g : Pattern) (depth : Nat) (datum : Pattern) : Pattern :=
  let shifted := Substitution.liftBVars 0 depth g
  mulWord decl shifted (frameWord decl shifted depth datum)

/-- The action at a variable occurrence of the body sort, `depth` binders inside the acted term: a
variable bound inside keeps its frame, a decorated one is conjugated, a free one is deferred. -/
def actVariable (g : Pattern) (depth : Nat) (occurrence : Pattern) : Pattern :=
  let shifted := Substitution.liftBVars 0 depth g
  match decorated? decl occurrence with
  | some (none, .bvar index) =>
      if index < depth then .bvar index else .apply decl.action [shifted, .bvar index]
  | some (none, occurrenceVar) => .apply decl.action [shifted, occurrenceVar]
  | some (some coefficient, .bvar index) =>
      if index < depth then
        .apply decl.action
          [mulWord decl (mulWord decl shifted (frameWord decl shifted depth coefficient)) (invWord decl shifted),
            .bvar index]
      else .apply decl.action [mulWord decl shifted (frameWord decl shifted depth coefficient), .bvar index]
  | some (some coefficient, occurrenceVar) =>
      .apply decl.action [mulWord decl shifted (frameWord decl shifted depth coefficient), occurrenceVar]
  | none => occurrence

/-- **The frame-normal action of `g`** on a term at a type. -/
def frameAct (g : Pattern) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapFrame language decl (actData decl g) (actVariable decl g) 0 type pattern

mutual
  /-- **Action nodes evaluated, decorations kept**: from the inside out, an action node on a
  variable of the body sort is a decoration, and two decorations compose; on any other term the node
  is the frame-normal action of its coefficient. -/
  def settle (type : TypeExpr) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments =>
        match paramTypes language label with
        | some types =>
            if label = decl.action then
              match settleArgs types arguments, types with
              | [coefficient, body], [_, bodyType] =>
                  match decorated? decl body with
                  | some (none, occurrenceVar) => .apply decl.action [coefficient, occurrenceVar]
                  | some (some inner, occurrenceVar) =>
                      .apply decl.action [mulWord decl coefficient inner, occurrenceVar]
                  | none => frameAct language decl coefficient bodyType body
              | inner, _ => .apply label inner
            else .apply label (settleArgs types arguments)
        | none => .apply label arguments
    | .lambda binder body =>
        match type with
        | .arrow _ codomain => .lambda binder (settle codomain body)
        | _ => .lambda binder body
    | .multiLambda arity binders body =>
        match type with
        | .arrow _ codomain => .multiLambda arity binders (settle codomain body)
        | _ => .multiLambda arity binders body
    | .subst body replacement => .subst body replacement
    | .collection kind elements rest =>
        match elementType language type kind with
        | some element => .collection kind (settleList element elements) rest
        | none => .collection kind elements rest
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def settleArgs : List TypeExpr → List Pattern → List Pattern
    | type :: types, argument :: arguments => settle type argument :: settleArgs types arguments
    | _, arguments => arguments
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def settleList (element : TypeExpr) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => settle element pattern :: settleList element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

variable {G : Type} [Group G] [DecidableEq G]

/-- Every occurrence decorated, its coefficient in normal form: a bare occurrence carries the unit's
word, so `X` and `^e X` have one normal form. -/
def normalVariable (reading : DataReading decl G) (_depth : Nat) (occurrence : Pattern) : Pattern :=
  match decorated? decl occurrence with
  | some (some coefficient, occurrenceVar) => .apply decl.action [wordNormal decl reading coefficient, occurrenceVar]
  | some (none, occurrenceVar) => .apply decl.action [reading.write 1, occurrenceVar]
  | none => occurrence

/-- **Every datum and every decoration in normal form.** -/
def frameNormal (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapFrame language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) 0 type pattern

/-- **The orientation normal form**: action nodes settled, then every datum and decoration in normal
form. -/
def orientNormal (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  frameNormal language decl reading type (settle language decl type pattern)

/-! ## (FRAME) as an endomorphism of `G ∗ F(V)` -/

section Algebra

/-- **(FRAME)'s renaming as an endomorphism of `G ∗ F(V)`**: a data variable bound inside the acted
term, `δ`, becomes `x⁻¹ δ`; constants and the other variables stay. -/
def frameHom (x : G) (depth : Nat) : FreeData G →* FreeData G :=
  Monoid.CoprodI.lift fun i =>
    match i with
    | none => Monoid.CoprodI.of
    | some (.bound index) =>
        (zpowersHom (FreeData G)
          (if index < depth then constEval x⁻¹ * powerEval (.bound index) 1 else powerEval (.bound index) 1) :
          Multiplicative ℤ →* FreeData G)
    | some (.free _) => Monoid.CoprodI.of

omit [DecidableEq G] in
theorem powerEval_zpow (v : DataVar) (n : ℤ) : powerEval (G := G) v 1 ^ n = powerEval v n := by
  have key : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
  exact (map_zpow (Monoid.CoprodI.of (M := Summand G) (i := some v)) (Multiplicative.ofAdd (1 : ℤ)) n).symm.trans
    (congrArg (Monoid.CoprodI.of (M := Summand G) (i := some v)) key)

omit [DecidableEq G] in
theorem frameHom_const (x : G) (depth : Nat) (c : G) : frameHom x depth (constEval c) = constEval c :=
  Monoid.CoprodI.lift_of _ _

omit [DecidableEq G] in
theorem frameHom_inside (x : G) {depth index : Nat} (inside : index < depth) :
    frameHom x depth (powerEval (.bound index) 1) = constEval x⁻¹ * powerEval (.bound index) 1 := by
  refine (Monoid.CoprodI.lift_of _ _).trans ?_
  dsimp only
  rw [if_pos inside]
  refine (zpowersHom_apply _ _ _).trans ?_
  show (constEval x⁻¹ * powerEval (DataVar.bound index) 1) ^ (1 : ℤ) = _
  exact zpow_one _

omit [DecidableEq G] in
theorem frameHom_outside (x : G) {depth index : Nat} (outside : ¬index < depth) (n : ℤ) :
    frameHom x depth (powerEval (.bound index) n) = powerEval (.bound index) n := by
  refine (Monoid.CoprodI.lift_of _ _).trans ?_
  dsimp only
  rw [if_neg outside]
  refine (zpowersHom_apply _ _ _).trans ?_
  show (powerEval (G := G) (DataVar.bound index) 1) ^ n = _
  exact powerEval_zpow _ n

omit [DecidableEq G] in
theorem frameHom_free (x : G) (depth : Nat) (name : String) (n : ℤ) :
    frameHom x depth (powerEval (.free name) n) = powerEval (.free name) n :=
  Monoid.CoprodI.lift_of _ _

omit [DecidableEq G] in
theorem constEval_one : constEval (1 : G) = 1 :=
  map_one (Monoid.CoprodI.of (M := Summand G) (i := none))

omit [DecidableEq G] in
theorem constEval_inv (x : G) : constEval x⁻¹ = (constEval x)⁻¹ :=
  map_inv (Monoid.CoprodI.of (M := Summand G) (i := none)) x

omit [DecidableEq G] in
/-- **Renaming twice is renaming by the product**: `δ ↦ y⁻¹ δ ↦ y⁻¹ x⁻¹ δ = (x y)⁻¹ δ`. -/
theorem frameHom_mul (x y : G) (depth : Nat) :
    (frameHom x depth).comp (frameHom y depth) = frameHom (x * y) depth := by
  apply Monoid.CoprodI.ext_hom
  intro i
  match i with
  | none =>
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply]
    exact (congrArg (frameHom x depth) (frameHom_const y depth (show G from c))).trans
      ((frameHom_const x depth (show G from c)).trans (frameHom_const (x * y) depth (show G from c)).symm)
  | some (.bound index) =>
    apply MonoidHom.ext_mint
    show frameHom x depth (frameHom y depth (powerEval (.bound index) 1)) =
      frameHom (x * y) depth (powerEval (.bound index) 1)
    by_cases inside : index < depth
    · rw [frameHom_inside y inside, map_mul, frameHom_const, frameHom_inside x inside, frameHom_inside (x * y) inside,
        ← mul_assoc, ← constEval_mul, mul_inv_rev]
    · rw [frameHom_outside y inside, frameHom_outside x inside, frameHom_outside (x * y) inside]
  | some (.free name) =>
    apply MonoidHom.ext_mint
    show frameHom x depth (frameHom y depth (powerEval (.free name) 1)) =
      frameHom (x * y) depth (powerEval (.free name) 1)
    rw [frameHom_free, frameHom_free, frameHom_free]

omit [DecidableEq G] in
/-- Renaming by the unit renames nothing. -/
theorem frameHom_one (depth : Nat) : frameHom (1 : G) depth = MonoidHom.id (FreeData G) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  match i with
  | none =>
    apply MonoidHom.ext
    intro c
    exact frameHom_const 1 depth (show G from c)
  | some (.bound index) =>
    apply MonoidHom.ext_mint
    show frameHom 1 depth (powerEval (.bound index) 1) = powerEval (.bound index) 1
    by_cases inside : index < depth
    · rw [frameHom_inside 1 inside, inv_one, constEval_one, one_mul]
    · rw [frameHom_outside 1 inside]
  | some (.free name) =>
    apply MonoidHom.ext_mint
    show frameHom 1 depth (powerEval (.free name) 1) = powerEval (.free name) 1
    rw [frameHom_free]

end Algebra

/-! ## Words under the action -/

variable {decl} {reading : DataReading decl G}

omit [DecidableEq G] in
/-- A closed word holds no bound variable, so lifting leaves it. -/
theorem liftBVars_closed {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (cutoff shift : Nat) :
    Substitution.liftBVars cutoff shift g = g := by
  match g, closed with
  | .apply label [], _ => simp [Substitution.liftBVars, Substitution.liftBVarsList]
  | .apply label [argument], closed =>
    rw [read] at closed
    split at closed
    · obtain ⟨y, inner, _⟩ := Option.map_eq_some_iff.mp closed
      have := liftBVars_closed inner cutoff shift
      simp [Substitution.liftBVars, Substitution.liftBVarsList, this]
    · cases closed
  | .apply label [left, right], closed =>
    rw [read] at closed
    split at closed
    · split at closed
      · rename_i y z leftRead rightRead
        have first := liftBVars_closed leftRead cutoff shift
        have second := liftBVars_closed rightRead cutoff shift
        simp [Substitution.liftBVars, Substitution.liftBVarsList, first, second]
      · cases closed
    · cases closed
  | .apply label (_ :: _ :: _ :: _), closed => simp [read] at closed
  | .bvar _, closed => simp [read] at closed
  | .fvar _, closed => simp [read] at closed
  | .lambda _ _, closed => simp [read] at closed
  | .multiLambda _ _ _, closed => simp [read] at closed
  | .subst _ _, closed => simp [read] at closed
  | .collection _ _ _, closed => simp [read] at closed
termination_by sizeOf g
decreasing_by all_goals sizeOf_pattern_dec

omit [DecidableEq G] in
/-- A closed word holds no bound variable, so (FRAME) leaves it. -/
theorem frameWord_closed {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (h : Pattern)
    (depth : Nat) : frameWord decl h depth g = g := by
  match g, closed with
  | .apply label [], _ => simp [frameWord, frameWords]
  | .apply label [argument], closed =>
    rw [read] at closed
    split at closed
    · obtain ⟨y, inner, _⟩ := Option.map_eq_some_iff.mp closed
      have := frameWord_closed inner h depth
      simp [frameWord, frameWords, this]
    · cases closed
  | .apply label [left, right], closed =>
    rw [read] at closed
    split at closed
    · split at closed
      · rename_i y z leftRead rightRead
        have first := frameWord_closed leftRead h depth
        have second := frameWord_closed rightRead h depth
        simp [frameWord, frameWords, first, second]
      · cases closed
    · cases closed
  | .apply label (_ :: _ :: _ :: _), closed => simp [read] at closed
  | .bvar _, closed => simp [read] at closed
  | .fvar _, closed => simp [read] at closed
  | .lambda _ _, closed => simp [read] at closed
  | .multiLambda _ _ _, closed => simp [read] at closed
  | .subst _ _, closed => simp [read] at closed
  | .collection _ _ _, closed => simp [read] at closed
termination_by sizeOf g
decreasing_by all_goals sizeOf_pattern_dec

omit [DecidableEq G] in
theorem letters_mulWord {left right : Pattern} {leftLetters rightLetters : List (Letter G)}
    (leftParsed : letters decl reading.constant left = some leftLetters)
    (rightParsed : letters decl reading.constant right = some rightLetters) :
    letters decl reading.constant (mulWord decl left right) = some (leftLetters ++ rightLetters) := by
  rw [mulWord, letters, if_pos rfl, leftParsed, rightParsed]

omit [DecidableEq G] in
theorem letters_invWord {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) :
    letters decl reading.constant (invWord decl word) = some (invertLetters found) := by
  rw [invWord, letters, if_pos rfl, parsed]
  rfl

omit [DecidableEq G] in
/-- **(FRAME) inside a datum is the renaming endomorphism.** -/
theorem letters_frameWord {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (depth : Nat) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      ∃ again, letters decl reading.constant (frameWord decl g depth word) = some again ∧
        evalLetters again = frameHom x depth (evalLetters found)
  | .bvar index, found, parsed => by
    rw [letters] at parsed
    cases parsed
    obtain ⟨gLetters, gParsed, gValue⟩ := letters_of_read reading.constant g closed
    by_cases inside : index < depth
    · refine ⟨invertLetters gLetters ++ [.power (.bound index) 1], ?_, ?_⟩
      · rw [frameWord, if_pos inside]
        exact letters_mulWord (letters_invWord gParsed) (by rw [letters])
      · rw [evalLetters_append, evalLetters_invert, gValue]
        simp only [evalLetters_cons, evalLetters_nil, mul_one]
        exact ((frameHom_inside x inside).trans (by rw [constEval_inv]; rfl)).symm
    · refine ⟨[.power (.bound index) 1], ?_, ?_⟩
      · rw [frameWord, if_neg inside, letters]
      · rw [evalLetters_cons, evalLetters_nil, mul_one]
        exact (frameHom_outside x inside 1).symm
  | .fvar name, found, parsed => by
    rw [letters] at parsed
    cases parsed
    refine ⟨[.power (.free name) 1], by show letters decl reading.constant (.fvar name) = _; rw [letters], ?_⟩
    rw [evalLetters_cons, evalLetters_nil, mul_one]
    exact (frameHom_free x depth name 1).symm
  | .apply label [], found, parsed => by
    refine ⟨found, by simpa [frameWord, frameWords] using parsed, ?_⟩
    rw [letters] at parsed
    split at parsed
    · cases parsed
      rw [evalLetters_nil, map_one]
    · obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp parsed
      rw [evalLetters_cons, evalLetters_nil, mul_one]
      exact (frameHom_const x depth c).symm
  | .apply label [argument], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i inverse
      obtain ⟨inner, innerParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      obtain ⟨again, againParsed, value⟩ := letters_frameWord closed depth argument innerParsed
      refine ⟨invertLetters again, ?_, ?_⟩
      · simp only [frameWord, frameWords]
        rw [letters, if_pos inverse, againParsed]
        rfl
      · rw [evalLetters_invert, evalLetters_invert, value, map_inv]
    · cases parsed
  | .apply label [left, right], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i multiply
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        cases parsed
        obtain ⟨leftAgain, leftAgainParsed, leftValue⟩ := letters_frameWord closed depth left leftParsed
        obtain ⟨rightAgain, rightAgainParsed, rightValue⟩ := letters_frameWord closed depth right rightParsed
        refine ⟨leftAgain ++ rightAgain, ?_, ?_⟩
        · simp only [frameWord, frameWords]
          rw [letters, if_pos multiply, leftAgainParsed, rightAgainParsed]
        · rw [evalLetters_append, evalLetters_append, leftValue, rightValue, map_mul]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed => by simp [letters] at parsed
  | .lambda _ _, found, parsed => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed => by simp [letters] at parsed
  | .subst _ _, found, parsed => by simp [letters] at parsed
  | .collection _ _ _, found, parsed => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec


/-! ## The action is a group action -/

omit [DecidableEq G] in
theorem read_mulWord {g h : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (hRead : read decl reading.constant h = some y) :
    read decl reading.constant (mulWord decl g h) = some (x * y) := by
  rw [mulWord, read_multiply, gRead, hRead]

/-- The unit's word. -/
def unitWord : Pattern := .apply decl.unit []

omit [DecidableEq G] in
theorem read_unitWord : read decl reading.constant (unitWord (decl := decl)) = some 1 := read_unit _

omit [DecidableEq G] in
/-- The action of a closed word at a datum denotes `x · φ_x(w)`. -/
theorem letters_actData {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (depth : Nat)
    {word : Pattern} {found : List (Letter G)} (parsed : letters decl reading.constant word = some found) :
    ∃ again, letters decl reading.constant (actData decl g depth word) = some again ∧
      evalLetters again = constEval x * frameHom x depth (evalLetters found) := by
  obtain ⟨gLetters, gParsed, gValue⟩ := letters_of_read reading.constant g closed
  obtain ⟨framed, framedParsed, framedValue⟩ := letters_frameWord closed depth word parsed
  refine ⟨gLetters ++ framed, ?_, ?_⟩
  · unfold actData
    rw [liftBVars_closed closed]
    exact letters_mulWord gParsed framedParsed
  · rw [evalLetters_append, gValue, framedValue]

/-- **At a datum, acting twice is acting by the product**, in normal form. -/
theorem actData_mul {g h : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (hRead : read decl reading.constant h = some y) (depth : Nat) {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) :
    wordNormal decl reading (actData decl g depth (actData decl h depth word)) =
      wordNormal decl reading (actData decl (mulWord decl g h) depth word) := by
  obtain ⟨inner, innerParsed, innerValue⟩ := letters_actData hRead depth parsed
  obtain ⟨outer, outerParsed, outerValue⟩ := letters_actData gRead depth innerParsed
  obtain ⟨product, productParsed, productValue⟩ := letters_actData (read_mulWord gRead hRead) depth parsed
  apply (wordNormal_eq_iff outerParsed productParsed).mpr
  rw [outerValue, productValue, innerValue, map_mul, frameHom_const, ← MonoidHom.comp_apply, frameHom_mul,
    constEval_mul, mul_assoc]

/-- **At a datum, the unit acts trivially**, in normal form. -/
theorem actData_one (depth : Nat) {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) :
    wordNormal decl reading (actData decl (unitWord (decl := decl)) depth word) = wordNormal decl reading word := by
  obtain ⟨acted, actedParsed, actedValue⟩ := letters_actData read_unitWord depth parsed
  apply (wordNormal_eq_iff actedParsed parsed).mpr
  rw [actedValue, frameHom_one, MonoidHom.id_apply, constEval_one, one_mul]

/-! ### At variables -/

omit [Group G] [DecidableEq G] in
theorem decorated?_action (coefficient occurrenceVar : Pattern) (bare : isBare occurrenceVar = true) :
    decorated? decl (.apply decl.action [coefficient, occurrenceVar]) = some (some coefficient, occurrenceVar) := by
  cases occurrenceVar <;> simp_all [decorated?, isBare]

omit [Group G] [DecidableEq G] in
/-- What a found occurrence is. -/
theorem decorated?_shape {pattern : Pattern} {coefficient : Option Pattern} {occurrenceVar : Pattern}
    (found : decorated? decl pattern = some (coefficient, occurrenceVar)) :
    isBare occurrenceVar = true ∧
      (coefficient = none → pattern = occurrenceVar) ∧
      (∀ c, coefficient = some c → pattern = .apply decl.action [c, occurrenceVar]) := by
  match pattern with
  | .bvar _ => simp [decorated?] at found; obtain ⟨rfl, rfl⟩ := found; simp [isBare]
  | .fvar _ => simp [decorated?] at found; obtain ⟨rfl, rfl⟩ := found; simp [isBare]
  | .apply label [c, .bvar index] =>
    simp only [decorated?] at found
    split at found
    · rename_i isAction
      cases found
      subst isAction
      simp [isBare]
    · cases found
  | .apply label [c, .fvar name] =>
    simp only [decorated?] at found
    split at found
    · rename_i isAction
      cases found
      subst isAction
      simp [isBare]
    · cases found
  | .apply _ [] => simp [decorated?] at found
  | .apply _ [_] => simp [decorated?] at found
  | .apply _ [_, .apply _ _] => simp [decorated?] at found
  | .apply _ [_, .lambda _ _] => simp [decorated?] at found
  | .apply _ [_, .multiLambda _ _ _] => simp [decorated?] at found
  | .apply _ [_, .subst _ _] => simp [decorated?] at found
  | .apply _ [_, .collection _ _ _] => simp [decorated?] at found
  | .apply _ (_ :: _ :: _ :: _) => simp [decorated?] at found
  | .lambda _ _ => simp [decorated?] at found
  | .multiLambda _ _ _ => simp [decorated?] at found
  | .subst _ _ => simp [decorated?] at found
  | .collection _ _ _ => simp [decorated?] at found

/-- A decoration's coefficient is a data word. -/
def CoefficientParses (reading : DataReading decl G) (occurrence : Pattern) : Prop :=
  ∀ coefficient occurrenceVar, decorated? decl occurrence = some (some coefficient, occurrenceVar) →
    (letters decl reading.constant coefficient).isSome

omit [Group G] [DecidableEq G] in
theorem actVariable_keeps (g : Pattern) : KeepsOccurrences decl (actVariable decl g) where
  occurs depth pattern found := by
    obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨bare, _, _⟩ := decorated?_shape found
    unfold actVariable
    rw [found]
    cases coefficient <;> cases occurrenceVar <;> simp_all [isBare] <;> (try split_ifs) <;>
      simp [decorated?]
  notBare depth pattern found notBare := by
    obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨bare, plain, _⟩ := decorated?_shape found
    cases coefficient with
    | none => rw [plain rfl] at notBare; rw [notBare] at bare; cases bare
    | some c =>
      unfold actVariable
      rw [found]
      cases occurrenceVar <;> simp_all [isBare]
      all_goals first | rfl | (split_ifs <;> rfl)

omit [Group G] [DecidableEq G] in
theorem KeepsOccurrences.comp {first second : Nat → Pattern → Pattern} (keepsFirst : KeepsOccurrences decl first)
    (keepsSecond : KeepsOccurrences decl second) :
    KeepsOccurrences decl (fun depth pattern => second depth (first depth pattern)) where
  occurs depth pattern found := keepsSecond.occurs depth _ (keepsFirst.occurs depth pattern found)
  notBare depth pattern found notBare :=
    keepsSecond.notBare depth _ (keepsFirst.occurs depth pattern found) (keepsFirst.notBare depth pattern found notBare)

omit [DecidableEq G] in
/-- The conjugated coefficient of a decoration bound inside denotes `x · φ_x(w) · x⁻¹`. -/
theorem letters_conjugate {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (depth : Nat)
    {word : Pattern} {found : List (Letter G)} (parsed : letters decl reading.constant word = some found) :
    ∃ again, letters decl reading.constant
        (mulWord decl (actData decl g depth word) (invWord decl (Substitution.liftBVars 0 depth g))) = some again ∧
      evalLetters again = constEval x * frameHom x depth (evalLetters found) * (constEval x)⁻¹ := by
  obtain ⟨acted, actedParsed, actedValue⟩ := letters_actData closed depth parsed
  obtain ⟨gLetters, gParsed, gValue⟩ := letters_of_read reading.constant g closed
  refine ⟨acted ++ invertLetters gLetters, ?_, ?_⟩
  · rw [liftBVars_closed closed]
    exact letters_mulWord actedParsed (letters_invWord gParsed)
  · rw [evalLetters_append, actedValue, evalLetters_invert, gValue]

/-- Decorations with coefficients of one normal form normalize alike. -/
theorem normalVariable_congr (depth : Nat) {first second occurrenceVar : Pattern} (bare : isBare occurrenceVar = true)
    (same : wordNormal decl reading first = wordNormal decl reading second) :
    normalVariable decl reading depth (.apply decl.action [first, occurrenceVar]) =
      normalVariable decl reading depth (.apply decl.action [second, occurrenceVar]) := by
  unfold normalVariable
  rw [decorated?_action first occurrenceVar bare, decorated?_action second occurrenceVar bare]
  exact congrArg (fun coefficient => Pattern.apply decl.action [coefficient, occurrenceVar]) same

omit [DecidableEq G] in
theorem frameHom_mul_apply (x y : G) (depth : Nat) (element : FreeData G) :
    frameHom x depth (frameHom y depth element) = frameHom (x * y) depth element := by
  rw [← frameHom_mul x y depth, MonoidHom.comp_apply]

omit [Group G] [DecidableEq G] in
theorem actVariable_bare_inside (g : Pattern) {depth index : Nat} (inside : index < depth) :
    actVariable decl g depth (.bvar index) = .bvar index := by
  simp [actVariable, decorated?, inside]

omit [Group G] [DecidableEq G] in
theorem actVariable_bare_outside (g : Pattern) {depth index : Nat} (outside : ¬index < depth) :
    actVariable decl g depth (.bvar index) = .apply decl.action [Substitution.liftBVars 0 depth g, .bvar index] := by
  simp [actVariable, decorated?, outside]

omit [Group G] [DecidableEq G] in
theorem actVariable_bare_free (g : Pattern) (depth : Nat) (name : String) :
    actVariable decl g depth (.fvar name) = .apply decl.action [Substitution.liftBVars 0 depth g, .fvar name] := by
  simp [actVariable, decorated?]

omit [Group G] [DecidableEq G] in
theorem actVariable_decorated_inside (g coefficient : Pattern) {depth index : Nat} (inside : index < depth) :
    actVariable decl g depth (.apply decl.action [coefficient, .bvar index]) =
      .apply decl.action
        [mulWord decl (actData decl g depth coefficient) (invWord decl (Substitution.liftBVars 0 depth g)),
          .bvar index] := by
  simp [actVariable, decorated?, inside, actData]

omit [Group G] [DecidableEq G] in
theorem actVariable_decorated_outside (g coefficient : Pattern) {depth index : Nat} (outside : ¬index < depth) :
    actVariable decl g depth (.apply decl.action [coefficient, .bvar index]) =
      .apply decl.action [actData decl g depth coefficient, .bvar index] := by
  simp [actVariable, decorated?, outside, actData]

omit [Group G] [DecidableEq G] in
theorem actVariable_decorated_free (g coefficient : Pattern) (depth : Nat) (name : String) :
    actVariable decl g depth (.apply decl.action [coefficient, .fvar name]) =
      .apply decl.action [actData decl g depth coefficient, .fvar name] := by
  simp [actVariable, decorated?, actData]

/-- **At a variable, acting twice is acting by the product**, in normal form. -/
theorem actVariable_mul {g h : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (hRead : read decl reading.constant h = some y) (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (parses : CoefficientParses reading occurrence) :
    normalVariable decl reading depth (actVariable decl g depth (actVariable decl h depth occurrence)) =
      normalVariable decl reading depth (actVariable decl (mulWord decl g h) depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have product := read_mulWord gRead hRead
  have gLift := liftBVars_closed gRead 0 depth
  have hLift := liftBVars_closed hRead 0 depth
  have productLift := liftBVars_closed product 0 depth
  have hData : actData decl g depth h = mulWord decl g h := by
    show mulWord decl (Substitution.liftBVars 0 depth g) (frameWord decl (Substitution.liftBVars 0 depth g) depth h) = _
    rw [gLift, frameWord_closed hRead]
  cases coefficient with
  | none =>
    have same := (plain rfl).symm
    subst same
    match occurrenceVar, bare with
    | .bvar index, _ =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside h inside, actVariable_bare_inside g inside,
          actVariable_bare_inside (mulWord decl g h) inside]
      · rw [actVariable_bare_outside h inside, hLift, actVariable_decorated_outside g h inside, hData,
          actVariable_bare_outside (mulWord decl g h) inside, productLift]
    | .fvar name, _ =>
      rw [actVariable_bare_free h depth name, hLift, actVariable_decorated_free g h depth name, hData,
        actVariable_bare_free (mulWord decl g h) depth name, productLift]
  | some c =>
    have same := (applied c rfl).symm
    subst same
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (parses c occurrenceVar found)
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside h c inside, actVariable_decorated_inside g _ inside,
          actVariable_decorated_inside (mulWord decl g h) c inside]
        apply normalVariable_congr depth bare
        obtain ⟨inner, innerParsed, innerValue⟩ := letters_conjugate hRead depth cParsed
        obtain ⟨outer, outerParsed, outerValue⟩ := letters_conjugate gRead depth innerParsed
        obtain ⟨both, bothParsed, bothValue⟩ := letters_conjugate product depth cParsed
        apply (wordNormal_eq_iff outerParsed bothParsed).mpr
        rw [outerValue, bothValue, innerValue, map_mul, map_mul, map_inv, frameHom_const,
          frameHom_mul_apply, constEval_mul, mul_inv_rev]
        simp only [mul_assoc]
      · rw [actVariable_decorated_outside h c inside, actVariable_decorated_outside g _ inside,
          actVariable_decorated_outside (mulWord decl g h) c inside]
        exact normalVariable_congr depth bare (actData_mul gRead hRead depth cParsed)
    | .fvar name, bare =>
      rw [actVariable_decorated_free h c depth name, actVariable_decorated_free g _ depth name,
        actVariable_decorated_free (mulWord decl g h) c depth name]
      exact normalVariable_congr depth bare (actData_mul gRead hRead depth cParsed)

/-- **At a variable, the unit acts trivially**, in normal form. -/
theorem actVariable_one (depth : Nat) {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome)
    (parses : CoefficientParses reading occurrence) :
    normalVariable decl reading depth (actVariable decl (unitWord (decl := decl)) depth occurrence) =
      normalVariable decl reading depth occurrence := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have unitLift := liftBVars_closed (read_unitWord (reading := reading)) 0 depth
  have unitNormal : wordNormal decl reading (unitWord (decl := decl)) = reading.write 1 :=
    wordNormal_closed read_unitWord
  cases coefficient with
  | none =>
    have same := (plain rfl).symm
    subst same
    have plainNormal : normalVariable decl reading depth occurrenceVar =
        .apply decl.action [reading.write 1, occurrenceVar] := by
      unfold normalVariable
      rw [found]
    rw [plainNormal]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside _ inside]
        exact plainNormal
      · rw [actVariable_bare_outside _ inside, unitLift]
        unfold normalVariable
        rw [decorated?_action _ _ bare]
        exact congrArg (fun coefficient => Pattern.apply decl.action [coefficient, _]) unitNormal
    | .fvar name, bare =>
      rw [actVariable_bare_free, unitLift]
      unfold normalVariable
      rw [decorated?_action _ _ bare]
      exact congrArg (fun coefficient => Pattern.apply decl.action [coefficient, _]) unitNormal
  | some c =>
    have same := (applied c rfl).symm
    subst same
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (parses c occurrenceVar found)
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside _ c inside]
        apply normalVariable_congr depth bare
        obtain ⟨conjugated, conjugatedParsed, conjugatedValue⟩ := letters_conjugate read_unitWord depth cParsed
        apply (wordNormal_eq_iff conjugatedParsed cParsed).mpr
        rw [conjugatedValue, frameHom_one, MonoidHom.id_apply, constEval_one, one_mul, inv_one, mul_one]
      · rw [actVariable_decorated_outside _ c inside]
        exact normalVariable_congr depth bare (actData_one depth cParsed)
    | .fvar name, bare =>
      rw [actVariable_decorated_free _ c depth name]
      exact normalVariable_congr depth bare (actData_one depth cParsed)

/-- What the group-action laws ask of a term: its data and its decorations' coefficients are data
words. -/
def WordsParse (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Prop :=
  FrameAll language decl (fun _ datum => (letters decl reading.constant datum).isSome)
    (fun _ occurrence => (decorated? decl occurrence).isSome ∧ CoefficientParses reading occurrence) 0 type pattern

variable {language}

/-- **Acting twice is acting by the product**, in normal form: the frame-normal action is an action of
the group on terms whose data are words. -/
theorem frameAct_mul (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {g h : Pattern}
    {x y : G} (gRead : read decl reading.constant g = some x) (hRead : read decl reading.constant h = some y)
    (type : TypeExpr) (pattern : Pattern) (parse : WordsParse language reading type pattern) :
    frameNormal language decl reading type (frameAct language decl g type (frameAct language decl h type pattern)) =
      frameNormal language decl reading type (frameAct language decl (mulWord decl g h) type pattern) := by
  unfold frameNormal frameAct
  rw [mapFrame_comp (actVariable_keeps h) bodyNotData,
    mapFrame_comp (KeepsOccurrences.comp (actVariable_keeps h) (actVariable_keeps g)) bodyNotData,
    mapFrame_comp (actVariable_keeps (mulWord decl g h)) bodyNotData]
  apply mapFrame_congr _ _ 0 type pattern parse
  · intro depth datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    exact actData_mul gRead hRead depth parsed
  · intro depth occurrence ⟨occurs, coefficients⟩
    exact actVariable_mul gRead hRead depth occurs coefficients

/-- **The unit acts trivially**, in normal form. -/
theorem frameAct_one (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) (type : TypeExpr)
    (pattern : Pattern) (parse : WordsParse language reading type pattern) :
    frameNormal language decl reading type (frameAct language decl (unitWord (decl := decl)) type pattern) =
      frameNormal language decl reading type pattern := by
  unfold frameNormal frameAct
  rw [mapFrame_comp (actVariable_keeps (unitWord (decl := decl))) bodyNotData]
  apply mapFrame_congr _ _ 0 type pattern parse
  · intro depth datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    exact actData_one depth parsed
  · intro depth occurrence ⟨occurs, coefficients⟩
    exact actVariable_one depth occurs coefficients

end Mettapedia.OSLF.MeTTaIL.Orientation
