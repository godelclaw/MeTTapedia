import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.PatternTreeSize

/-!
# The declared collection laws, as a normal form

A language declares, per bare collection constructor, that its collections flatten
(`{P, {Q, R}}` is `{P, Q, R}`) and optionally a unit constructor (`{P, 0}` is `{P}`). The laws
are declared data (`GrammarRule.algebra?`), never assumed.

`normalize` computes the normal form bottom up: inside a collection of a flattening kind,
an element that is itself a collection of that kind is spliced in, and a declared unit is
dropped. A kind flattens when exactly one bare constructor of the language has it and that
constructor declares flattening, so a nested collection of that kind is a term of the same
constructor.

Facts:

- `normalize_idempotent`: a normal form is normal;
- `normalize_freeFvarNames`: normalizing keeps every free name, so a footprint is kept;
- `normalize_rest`: a collection rest is left in place.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionLaws

open Syntax Substitution

/-- The collection kind of a bare collection constructor. -/
def bareKind (rule : GrammarRule) : Option CollType :=
  match rule.params with
  | [.simple _ (.collection kind _)] => some kind
  | _ => none

/-- The laws declared for one collection kind. -/
structure Laws where
  kind : CollType
  unit : Option String
  deriving DecidableEq, Repr

/-- The declared laws: kinds whose unique bare constructor flattens, with its unit. -/
def declared (language : LanguageDef) : List Laws :=
  [CollType.hashBag, .hashSet, .vec].filterMap fun kind =>
    match language.terms.filter (fun rule => bareKind rule == some kind) with
    | [rule] =>
        match rule.algebra? with
        | some algebra => if algebra.flatten then some ⟨kind, algebra.unit⟩ else none
        | none => none
    | _ => none

/-- One normalized element, spliced into its parent collection of kind `kind`. -/
def splice (laws : Laws) : Pattern → List Pattern
  | .collection actual elements none => if actual = laws.kind then elements else [.collection actual elements none]
  | .apply label [] => if laws.unit = some label then [] else [.apply label []]
  | other => [other]

/-- **The normal form under the declared laws.** -/
def normalize (laws : List Laws) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map (normalize laws))
  | .lambda binder body => .lambda binder (normalize laws body)
  | .multiLambda arity binders body => .multiLambda arity binders (normalize laws body)
  | .subst body replacement => .subst (normalize laws body) (normalize laws replacement)
  | .collection kind elements rest =>
      let inner := elements.map (normalize laws)
      match laws.find? (·.kind = kind) with
      | some law => .collection kind (inner.flatMap (splice law)) rest
      | none => .collection kind inner rest
decreasing_by all_goals sizeOf_pattern_dec

/-! ## Free names are kept -/

theorem splice_names (law : Laws) (pattern : Pattern) (name : String) :
    name ∈ (splice law pattern).flatMap Pattern.freeFvarNames ↔ name ∈ pattern.freeFvarNames := by
  cases pattern with
  | collection actual elements rest =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · simp [splice, same, Pattern.freeFvarNames]
      · simp [splice, same]
    | some other => simp [splice]
  | apply label arguments =>
    cases arguments with
    | nil => by_cases unit : law.unit = some label <;> simp [splice, unit, Pattern.freeFvarNames]
    | cons first rest => simp [splice]
  | _ => simp [splice]

/-- **Normalizing keeps every free name, and adds none.** -/
theorem normalize_freeFvarNames (laws : List Laws) (pattern : Pattern) (name : String) :
    name ∈ (normalize laws pattern).freeFvarNames ↔ name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => simp [normalize]
  | hfvar other => simp [normalize]
  | happly label arguments ih =>
    simp only [normalize, Pattern.freeFvarNames, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨argument, member, rfl⟩, inside⟩
      exact ⟨argument, member, (ih argument member name).mp inside⟩
    · rintro ⟨argument, member, inside⟩
      exact ⟨_, ⟨argument, member, rfl⟩, (ih argument member name).mpr inside⟩
  | hlambda binder body ih => simpa [normalize, Pattern.freeFvarNames] using ih name
  | hmultiLambda arity binders body ih => simpa [normalize, Pattern.freeFvarNames] using ih name
  | hsubst body replacement bodyIH replacementIH =>
    simp only [normalize, Pattern.freeFvarNames, List.mem_append]
    rw [bodyIH name, replacementIH name]
  | hcollection kind elements rest ih =>
    have inner : name ∈ (elements.map (normalize laws)).flatMap Pattern.freeFvarNames ↔
        name ∈ elements.flatMap Pattern.freeFvarNames := by
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨_, ⟨element, member, rfl⟩, inside⟩
        exact ⟨element, member, (ih element member name).mp inside⟩
      · rintro ⟨element, member, inside⟩
        exact ⟨_, ⟨element, member, rfl⟩, (ih element member name).mpr inside⟩
    simp only [normalize]
    split
    · rename_i law _
      simp only [Pattern.freeFvarNames, List.mem_append]
      rw [← inner]
      have spliced : name ∈ ((elements.map (normalize laws)).flatMap (splice law)).flatMap Pattern.freeFvarNames ↔
          name ∈ (elements.map (normalize laws)).flatMap Pattern.freeFvarNames := by
        simp only [List.flatMap_assoc, List.mem_flatMap]
        constructor
        · rintro ⟨item, member, inside⟩
          exact ⟨item, member, (splice_names law item name).mp (List.mem_flatMap.mpr inside)⟩
        · rintro ⟨item, member, inside⟩
          have back := (splice_names law item name).mpr inside
          simp only [List.mem_flatMap] at back
          exact ⟨item, member, back⟩
      rw [spliced]
    · simp only [Pattern.freeFvarNames, List.mem_append]
      rw [inner]

/-! ## A normal form is normal -/

/-- The law for a kind, when the kind flattens. -/
abbrev lawFor (laws : List Laws) (kind : CollType) : Option Laws := laws.find? (·.kind = kind)

theorem lawFor_kind {laws : List Laws} {kind : CollType} {law : Laws} (found : lawFor laws kind = some law) :
    law.kind = kind := by
  simpa using List.find?_some found

/-- What normalizing guarantees: the result is fixed, and inside a collection of a flattening
kind every element is fixed and stays in place. -/
def Settled (laws : List Laws) (pattern : Pattern) : Prop :=
  normalize laws pattern = pattern ∧
    ∀ kind items rest law, pattern = .collection kind items rest → lawFor laws kind = some law →
      ∀ item ∈ items, normalize laws item = item ∧ splice law item = [item]

theorem splice_fixed {laws : List Laws} {law : Laws} {kind : CollType} (same : law.kind = kind)
    (found : lawFor laws kind = some law) {item : Pattern} (settled : Settled laws item) :
    ∀ piece ∈ splice law item, normalize laws piece = piece ∧ splice law piece = [piece] := by
  intro piece member
  cases item with
  | collection actual elements rest =>
    cases rest with
    | none =>
      by_cases equal : actual = law.kind
      · simp only [splice, equal, if_true] at member
        subst equal
        exact settled.2 law.kind elements none law rfl (same ▸ found) piece member
      · simp only [splice, equal, if_false, List.mem_singleton] at member
        subst member
        exact ⟨settled.1, by simp [splice, equal]⟩
    | some other =>
      simp only [splice, List.mem_singleton] at member
      subst member
      exact ⟨settled.1, by simp [splice]⟩
  | apply label arguments =>
    cases arguments with
    | nil =>
      by_cases unit : law.unit = some label
      · simp [splice, unit] at member
      · simp only [splice, unit, if_false, List.mem_singleton] at member
        subst member
        exact ⟨settled.1, by simp [splice, unit]⟩
    | cons first rest =>
      simp only [splice, List.mem_singleton] at member
      subst member
      exact ⟨settled.1, by simp [splice]⟩
  | bvar index =>
    simp only [splice, List.mem_singleton] at member
    subst member
    exact ⟨settled.1, by simp [splice]⟩
  | fvar name =>
    simp only [splice, List.mem_singleton] at member
    subst member
    exact ⟨settled.1, by simp [splice]⟩
  | lambda binder body =>
    simp only [splice, List.mem_singleton] at member
    subst member
    exact ⟨settled.1, by simp [splice]⟩
  | multiLambda arity binders body =>
    simp only [splice, List.mem_singleton] at member
    subst member
    exact ⟨settled.1, by simp [splice]⟩
  | subst body replacement =>
    simp only [splice, List.mem_singleton] at member
    subst member
    exact ⟨settled.1, by simp [splice]⟩

theorem flatMap_splice_fixed (law : Laws) (items : List Pattern)
    (fixed : ∀ item ∈ items, splice law item = [item]) : items.flatMap (splice law) = items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    rw [List.flatMap_cons, fixed first (by simp), ih (fun item member => fixed item (by simp [member]))]
    rfl

/-- **Normalizing settles every pattern**; in particular a normal form is normal. -/
theorem normalize_settled (laws : List Laws) (pattern : Pattern) : Settled laws (normalize laws pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => exact ⟨by simp [normalize], by simp [normalize]⟩
  | hfvar name => exact ⟨by simp [normalize], by simp [normalize]⟩
  | happly label arguments ih =>
    refine ⟨?_, by simp [normalize]⟩
    simp only [normalize, List.map_map]
    congr 1
    apply List.map_congr_left
    intro argument member
    exact (ih argument member).1
  | hlambda binder body ih => exact ⟨by simp [normalize, ih.1], by simp [normalize]⟩
  | hmultiLambda arity binders body ih => exact ⟨by simp [normalize, ih.1], by simp [normalize]⟩
  | hsubst body replacement bodyIH replacementIH =>
    exact ⟨by simp [normalize, bodyIH.1, replacementIH.1], by simp [normalize]⟩
  | hcollection kind elements rest ih =>
    have pieces : ∀ law, lawFor laws kind = some law →
        ∀ piece ∈ (elements.map (normalize laws)).flatMap (splice law),
          normalize laws piece = piece ∧ splice law piece = [piece] := by
      intro law found piece member
      obtain ⟨item, itemMember, inside⟩ := List.mem_flatMap.mp member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp itemMember
      exact splice_fixed (lawFor_kind found) found (ih element elementMember) piece inside
    cases found : lawFor laws kind with
    | none =>
      have shape : normalize laws (.collection kind elements rest) =
          .collection kind (elements.map (normalize laws)) rest := by
        rw [normalize]; simp only [lawFor] at found; simp [found]
      rw [shape]
      refine ⟨?_, ?_⟩
      · rw [normalize]
        simp only [lawFor] at found
        simp only [found, List.map_map]
        congr 1
        apply List.map_congr_left
        intro element member
        exact (ih element member).1
      · intro actual items actualRest law same lawFound
        cases same
        rw [found] at lawFound
        cases lawFound
    | some law =>
      have shape : normalize laws (.collection kind elements rest) =
          .collection kind ((elements.map (normalize laws)).flatMap (splice law)) rest := by
        rw [normalize]; simp only [lawFor] at found; simp [found]
      rw [shape]
      refine ⟨?_, ?_⟩
      · rw [normalize]
        simp only [lawFor] at found
        simp only [found]
        have fixed := pieces law found
        rw [List.map_congr_left (fun piece member => (fixed piece member).1), List.map_id',
          flatMap_splice_fixed law _ (fun piece member => (fixed piece member).2)]
      · intro actual items actualRest other same otherFound
        cases same
        rw [found] at otherFound
        cases otherFound
        exact pieces law found

theorem normalize_idempotent (laws : List Laws) (pattern : Pattern) :
    normalize laws (normalize laws pattern) = normalize laws pattern :=
  (normalize_settled laws pattern).1

/-! ## Scope extrusion, run as a normalizer

A language that declares scope extrusion for a binder constructor `B` over a flattening
collection kind,

    {(B ^x.P), ...rest} = (B ^x.{P, ...rest})

(in core form: `P` depends on the binder, `rest` on nothing), runs that law left to right on
its states: inside a collection of that kind, each `B`-element is hoisted out, the other
elements move under its binder with their indices lifted, and a body of the same kind is
spliced in. Hoisting is a normal form of the declared law together with flattening. -/

/-- A declared scope-extrusion law: binder constructor `binder` over collections of `kind`. -/
structure Extrusion where
  kind : CollType
  binder : String
  deriving DecidableEq, Repr

/-- The scope-extrusion laws among a core language's equations. -/
def extrusions (language : LanguageDef) : List Extrusion :=
  language.equations.filterMap fun equation =>
    match equation.left, equation.right, equation.bindings with
    | .collection kind [.apply binder [.lambda _ (.fvar body)]] (some rest),
      .apply binder' [.lambda _ (.collection kind' [.fvar body'] (some rest'))], some spec =>
        if kind = kind' ∧ binder = binder' ∧ body = body' ∧ rest = rest' ∧
            (spec.dependencies.find? (·.1 = rest)).map (·.2) = some [] ∧
            ((spec.dependencies.find? (·.1 = body)).map (·.2.length)) = some 1 then
          some ⟨kind, binder⟩
        else none
    | _, _, _ => none

/-- A hoisted body's elements: its own elements when it is a closed collection of `kind`. -/
def bodyItems (kind : CollType) : Pattern → List Pattern
  | .collection actual elements none => if actual = kind then elements else [.collection actual elements none]
  | body => [body]

theorem bodyItems_names (kind : CollType) (body : Pattern) (name : String) :
    name ∈ (bodyItems kind body).flatMap Pattern.freeFvarNames ↔ name ∈ body.freeFvarNames := by
  unfold bodyItems
  split
  · split <;> simp [Pattern.freeFvarNames]
  · simp

/-- Hoist every `binder`-element of a collection of `kind`, left to right. -/
def hoist (extrusion : Extrusion) : Nat → List Pattern → List Pattern → Pattern
  | 0, done, todo => .collection extrusion.kind (done ++ todo) none
  | _ + 1, done, [] => .collection extrusion.kind done none
  | fuel + 1, done, item :: todo =>
      match item with
      | .apply label [.lambda display body] =>
          if label = extrusion.binder then
            .apply label [.lambda display (hoist extrusion fuel (done.map (liftBVars 0 1))
              (bodyItems extrusion.kind body ++ todo.map (liftBVars 0 1)))]
          else hoist extrusion fuel (done ++ [item]) todo
      | _ => hoist extrusion fuel (done ++ [item]) todo

/-- Scope extrusion run bottom up. -/
def extrude (extrusions : List Extrusion) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map (extrude extrusions))
  | .lambda binder body => .lambda binder (extrude extrusions body)
  | .multiLambda arity binders body => .multiLambda arity binders (extrude extrusions body)
  | .subst body replacement => .subst (extrude extrusions body) (extrude extrusions replacement)
  | .collection kind elements rest =>
      let inner := elements.map (extrude extrusions)
      match rest with
      | some name => .collection kind inner (some name)
      | none =>
          match extrusions.find? (·.kind = kind) with
          | some extrusion =>
              hoist extrusion (2 * (inner.map PatternTreeSize.nodes).sum + inner.length + 1) [] inner
          | none => .collection kind inner none
decreasing_by all_goals sizeOf_pattern_dec

/-- **The standard form**: the declared collection laws, then scope extrusion. -/
def standardForm (laws : List Laws) (extrusions : List Extrusion) (pattern : Pattern) : Pattern :=
  extrude extrusions (normalize laws pattern)

/-! ## The standard form keeps free names -/

theorem liftBVars_freeFvarNames (pattern : Pattern) :
    ∀ cutoff shift, (liftBVars cutoff shift pattern).freeFvarNames = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro cutoff shift
    unfold liftBVars
    split <;> simp [Pattern.freeFvarNames]
  | hfvar name => intro cutoff shift; simp [liftBVars, Pattern.freeFvarNames]
  | happly label arguments ih =>
    intro cutoff shift
    simp only [liftBVars, liftBVarsList_eq_map, Pattern.freeFvarNames, List.flatMap_map]
    exact List.flatMap_congr fun argument member => ih argument member cutoff shift
  | hlambda binder body ih => intro cutoff shift; simp [liftBVars, Pattern.freeFvarNames, ih]
  | hmultiLambda arity binders body ih => intro cutoff shift; simp [liftBVars, Pattern.freeFvarNames, ih]
  | hsubst body replacement bodyIH replacementIH =>
    intro cutoff shift; simp [liftBVars, Pattern.freeFvarNames, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    intro cutoff shift
    simp only [liftBVars, liftBVarsList_eq_map, Pattern.freeFvarNames, List.flatMap_map]
    rw [List.flatMap_congr fun element member => ih element member cutoff shift]

theorem lifted_names (items : List Pattern) (name : String) :
    name ∈ (items.map (liftBVars 0 1)).flatMap Pattern.freeFvarNames ↔ name ∈ items.flatMap Pattern.freeFvarNames := by
  simp only [List.flatMap_map, liftBVars_freeFvarNames]

theorem hoist_names (extrusion : Extrusion) (name : String) :
    ∀ fuel done todo, name ∈ (hoist extrusion fuel done todo).freeFvarNames ↔
      name ∈ (done ++ todo).flatMap Pattern.freeFvarNames
  | 0, done, todo => by simp [hoist, Pattern.freeFvarNames]
  | fuel + 1, done, [] => by simp [hoist, Pattern.freeFvarNames]
  | fuel + 1, done, item :: todo => by
    have later := hoist_names extrusion name fuel
    cases item with
    | apply label arguments =>
      cases arguments with
      | cons first others =>
        cases others with
        | nil =>
          cases first with
          | lambda display body =>
            have body_names := bodyItems_names extrusion.kind body name
            by_cases same : label = extrusion.binder
            · simp only [hoist, same, if_true, Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
                List.append_nil]
              rw [later]
              simp only [List.flatMap_append, List.mem_append, lifted_names, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, body_names, Pattern.freeFvarNames]
            · simp only [hoist, same, if_false]
              rw [later]
              simp [List.mem_append]
          | _ => simp only [hoist]; rw [later]; simp [List.mem_append]
        | cons second more => simp only [hoist]; rw [later]; simp [List.mem_append]
      | nil => simp only [hoist]; rw [later]; simp [List.mem_append]
    | _ => simp only [hoist]; rw [later]; simp [List.mem_append]

theorem extrude_freeFvarNames (extrusions : List Extrusion) (pattern : Pattern) (name : String) :
    name ∈ (extrude extrusions pattern).freeFvarNames ↔ name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => simp [extrude]
  | hfvar other => simp [extrude]
  | happly label arguments ih =>
    simp only [extrude, Pattern.freeFvarNames, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨argument, member, rfl⟩, inside⟩
      exact ⟨argument, member, (ih argument member name).mp inside⟩
    · rintro ⟨argument, member, inside⟩
      exact ⟨_, ⟨argument, member, rfl⟩, (ih argument member name).mpr inside⟩
  | hlambda binder body ih => simpa [extrude, Pattern.freeFvarNames] using ih name
  | hmultiLambda arity binders body ih => simpa [extrude, Pattern.freeFvarNames] using ih name
  | hsubst body replacement bodyIH replacementIH =>
    simp only [extrude, Pattern.freeFvarNames, List.mem_append]
    rw [bodyIH name, replacementIH name]
  | hcollection kind elements rest ih =>
    have inner : name ∈ (elements.map (extrude extrusions)).flatMap Pattern.freeFvarNames ↔
        name ∈ elements.flatMap Pattern.freeFvarNames := by
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨_, ⟨element, member, rfl⟩, inside⟩
        exact ⟨element, member, (ih element member name).mp inside⟩
      · rintro ⟨element, member, inside⟩
        exact ⟨_, ⟨element, member, rfl⟩, (ih element member name).mpr inside⟩
    cases rest with
    | some other =>
      rw [extrude]
      simp only [Pattern.freeFvarNames, List.mem_append]
      rw [inner]
    | none =>
      cases found : extrusions.find? (·.kind = kind) with
      | none =>
        rw [extrude]
        simp only [found, Pattern.freeFvarNames, List.mem_append]
        rw [inner]
      | some extrusion =>
        rw [extrude]
        simp only [found]
        rw [hoist_names]
        simpa [Pattern.freeFvarNames] using inner

/-- **The standard form keeps every free name, and adds none.** -/
theorem standardForm_freeFvarNames (laws : List Laws) (extrusions : List Extrusion) (pattern : Pattern)
    (name : String) :
    name ∈ (standardForm laws extrusions pattern).freeFvarNames ↔ name ∈ pattern.freeFvarNames := by
  rw [standardForm, extrude_freeFvarNames, normalize_freeFvarNames]

/-! ## No declared laws -/

theorem normalize_nil (pattern : Pattern) : normalize [] pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [normalize]
  | hfvar name => simp [normalize]
  | happly label arguments ih =>
    rw [normalize, (List.map_congr_left ih).trans (List.map_id _)]
  | hlambda binder body ih => rw [normalize, ih]
  | hmultiLambda arity binders body ih => rw [normalize, ih]
  | hsubst body replacement bodyIH replacementIH => rw [normalize, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    rw [normalize]
    simp only [List.find?_nil]
    rw [(List.map_congr_left ih).trans (List.map_id _)]

theorem extrude_nil (pattern : Pattern) : extrude [] pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [extrude]
  | hfvar name => simp [extrude]
  | happly label arguments ih =>
    rw [extrude, (List.map_congr_left ih).trans (List.map_id _)]
  | hlambda binder body ih => rw [extrude, ih]
  | hmultiLambda arity binders body ih => rw [extrude, ih]
  | hsubst body replacement bodyIH replacementIH => rw [extrude, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    cases rest with
    | none => rw [extrude]; simp only [List.find?_nil]; rw [(List.map_congr_left ih).trans (List.map_id _)]
    | some name => rw [extrude, (List.map_congr_left ih).trans (List.map_id _)]

/-- **With no declared laws, the standard form is the pattern itself.** -/
theorem standardForm_nil (pattern : Pattern) : standardForm [] [] pattern = pattern := by
  rw [standardForm, normalize_nil, extrude_nil]

end Mettapedia.OSLF.MeTTaIL.CollectionLaws
