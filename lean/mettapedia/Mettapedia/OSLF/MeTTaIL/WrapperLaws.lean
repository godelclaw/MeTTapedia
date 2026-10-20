import Mettapedia.OSLF.MeTTaIL.QuoteDropLaws

/-!
# The declared collection algebra, completed by its wrapper laws

A collection algebra declares four laws of a bare collection constructor
(`Syntax.CollectionAlgebra`; the language's equational semantics generates exactly these,
`EquationSemantics.DerivedInstance`): flattening of a nested occurrence and, with it, that a singleton
collection is its element; absorption of the declared unit and, with it, that the empty collection is
that unit. Flattening with the singleton law are the two laws of an algebra for the collection's monad,
and naming a unit names the image of the empty collection. The parallel laws (`LawStep`) cover
flattening, unit absorption and permutation; `WrapperStep` is one use of the other two, left to right,
in any context.

With the quote-drop equation of a reflective presentation these are the model's law moves
(`ModelMove`). They have one normal form, computed bottom up in a single pass (`modelNormal`): the
quote-drop test at each constructor, then splicing and unit removal at each collection of a flattening
kind, for a set the canonical forms of its elements without repetition (`setForm`), then the wrapper
collapse. One pass is needed because each kind of move can expose another: a collapsed wrapper can
expose a quote-drop pair, `@{*@P}` to `@(*@P)` to `@P`, a removed unit can leave a singleton, `{P, 0}` to
`{P}` to `P`, and a set's repetition can hide one, `{P, P}` to `{P}` to `P`.

- `to_modelNormal`: every term is related to its normal form by model moves.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags ReflectiveSubstitution QuoteDrop

variable (laws : List Laws)

/-- One use of a wrapper law, left to right, in any context: a singleton collection of a flattening
kind is its element, and an empty one is the declared unit. -/
inductive WrapperStep : Pattern → Pattern → Prop where
  | singleton {kind : CollType} {law : Laws} {element : Pattern} :
      lawFor laws kind = some law → WrapperStep (.collection kind [element] none) element
  | empty {kind : CollType} {law : Laws} {label : String} :
      lawFor laws kind = some law → law.unit = some label → WrapperStep (.collection kind [] none) (.apply label [])
  | apply {label : String} {before after : List Pattern} {argument changed : Pattern} :
      WrapperStep argument changed →
      WrapperStep (.apply label (before ++ argument :: after)) (.apply label (before ++ changed :: after))
  | lambda {binder : Option String} {body changed : Pattern} :
      WrapperStep body changed → WrapperStep (.lambda binder body) (.lambda binder changed)
  | multiLambda {arity : Nat} {binders : List String} {body changed : Pattern} :
      WrapperStep body changed → WrapperStep (.multiLambda arity binders body) (.multiLambda arity binders changed)
  | substBody {body changed replacement : Pattern} :
      WrapperStep body changed → WrapperStep (.subst body replacement) (.subst changed replacement)
  | substReplacement {body replacement changed : Pattern} :
      WrapperStep replacement changed → WrapperStep (.subst body replacement) (.subst body changed)
  | element {kind : CollType} {before after : List Pattern} {element changed : Pattern} {rest : Option String} :
      WrapperStep element changed →
      WrapperStep (.collection kind (before ++ element :: after) rest) (.collection kind (before ++ changed :: after) rest)

variable (declaration : ReflectivePresentationDecl)

/-- A law move of the model: a parallel law, a use of `@(*n) = n`, or a wrapper law. -/
def ModelMove (left right : Pattern) : Prop :=
  LawStep laws left right ∨ QuoteDropStep declaration left right ∨ WrapperStep laws left right

/-- Deep splicing into a collection of a flattening kind: a nested collection of the kind contributes
its elements, spliced again, and the declared unit contributes nothing. -/
def deepSplice (law : Laws) : Pattern → List Pattern
  | .collection kind elements none =>
      if kind = law.kind then elements.flatMap (deepSplice law) else [.collection kind elements none]
  | .apply label [] => if law.unit = some label then [] else [.apply label []]
  | other => [other]
decreasing_by all_goals sizeOf_pattern_dec

/-- The wrapper collapse of a collection after splicing: one element is that element, none is the unit. -/
def wrapFinish (law : Laws) (kind : CollType) (items : List Pattern) (rest : Option String) : Pattern :=
  match rest, items with
  | none, [item] => item
  | none, [] =>
      match law.unit with
      | some label => .apply label []
      | none => .collection kind [] none
  | _, _ => .collection kind items rest

/-- A set's elements in canonical form, without repetition; a bag's or a vector's as they are. The
wrapper collapse of a set is judged after this: `{P, P}` is the set `{P}`, which is `P`. -/
def setForm (kind : CollType) (items : List Pattern) : List Pattern :=
  match kind with
  | .hashSet => (items.map canon).dedup
  | .hashBag => items
  | .vec => items

theorem setForm_vec (items : List Pattern) : setForm .vec items = items := rfl
theorem setForm_bag (items : List Pattern) : setForm .hashBag items = items := rfl
theorem setForm_set (items : List Pattern) : setForm .hashSet items = (items.map canon).dedup := rfl
theorem setForm_nil (kind : CollType) : setForm kind [] = [] := by cases kind <;> rfl

/-- **The model normal form**: bottom up, the quote-drop test at each constructor, splicing and unit
removal at each collection of a flattening kind, a set's elements in canonical form without repetition,
then the wrapper collapse. -/
def modelNormal : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => finishNormalizeReflectiveApply declaration label (arguments.map modelNormal)
  | .lambda binder body => .lambda binder (modelNormal body)
  | .multiLambda arity binders body => .multiLambda arity binders (modelNormal body)
  | .subst body replacement => .subst (modelNormal body) (modelNormal replacement)
  | .collection kind elements rest =>
      match lawFor laws kind with
      | some law => wrapFinish law kind (setForm kind ((elements.map modelNormal).flatMap (deepSplice law))) rest
      | none => .collection kind (elements.map modelNormal) rest
decreasing_by all_goals sizeOf_pattern_dec

/-! ## Soundness -/

variable {laws declaration}

theorem liftMove {f : Pattern → Pattern}
    (lawLift : ∀ {a b : Pattern}, LawStep laws a b → LawStep laws (f a) (f b))
    (quoteLift : ∀ {a b : Pattern}, QuoteDropStep declaration a b → QuoteDropStep declaration (f a) (f b))
    (wrapperLift : ∀ {a b : Pattern}, WrapperStep laws a b → WrapperStep laws (f a) (f b))
    {a b : Pattern} (related : Relation.EqvGen (ModelMove laws declaration) a b) :
    Relation.EqvGen (ModelMove laws declaration) (f a) (f b) := by
  induction related with
  | rel _ _ move =>
    rcases move with lawMove | quoteDrop | wrapped
    · exact .rel _ _ (.inl (lawLift lawMove))
    · exact .rel _ _ (.inr (.inl (quoteLift quoteDrop)))
    · exact .rel _ _ (.inr (.inr (wrapperLift wrapped)))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem alongMove (g : Pattern → Pattern) (wrap : List Pattern → Pattern)
    (lawLift : ∀ (before after : List Pattern) {a b : Pattern}, LawStep laws a b →
      LawStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after)))
    (quoteLift : ∀ (before after : List Pattern) {a b : Pattern}, QuoteDropStep declaration a b →
      QuoteDropStep declaration (wrap (before ++ a :: after)) (wrap (before ++ b :: after)))
    (wrapperLift : ∀ (before after : List Pattern) {a b : Pattern}, WrapperStep laws a b →
      WrapperStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before items : List Pattern), (∀ item ∈ items, Relation.EqvGen (ModelMove laws declaration) item (g item)) →
      Relation.EqvGen (ModelMove laws declaration) (wrap (before ++ items)) (wrap (before ++ items.map g))
  | before, [], _ => by simpa using Relation.EqvGen.refl _
  | before, item :: rest, each => by
    have first : Relation.EqvGen (ModelMove laws declaration) (wrap (before ++ item :: rest))
        (wrap (before ++ g item :: rest)) :=
      liftMove (f := fun x => wrap (before ++ x :: rest)) (fun step => lawLift before rest step)
        (fun step => quoteLift before rest step) (fun step => wrapperLift before rest step) (each item (by simp))
    have later := alongMove g wrap lawLift quoteLift wrapperLift (before ++ [g item]) rest
      (fun other member => each other (by simp [member]))
    simp only [List.append_assoc, List.singleton_append] at later
    exact .trans _ _ _ first (by simpa using later)

theorem ofLaws {a b : Pattern} (related : Relation.EqvGen (LawStep laws) a b) :
    Relation.EqvGen (ModelMove laws declaration) a b :=
  Relation.EqvGen.mono (fun _ _ move => .inl move) _ _ related

theorem sizeOf_append_patterns : ∀ (first second : List Pattern),
    sizeOf (first ++ second) + 1 = sizeOf first + sizeOf second
  | [], second => by simp; omega
  | head :: tail, second => by
    simp only [List.cons_append, List.cons.sizeOf_spec]
    have := sizeOf_append_patterns tail second
    omega

/-- Deep splicing is a sequence of law moves. -/
theorem deepSpliceSteps {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (rest : Option String) : ∀ (before items : List Pattern),
      Relation.EqvGen (LawStep laws) (.collection kind (before ++ items) rest)
        (.collection kind (before ++ items.flatMap (deepSplice law)) rest)
  | before, [] => by simpa using Relation.EqvGen.refl _
  | before, item :: tail => by
    have kindIs : law.kind = kind := lawFor_kind found
    rw [List.flatMap_cons]
    have keep : deepSplice law item = [item] →
        Relation.EqvGen (LawStep laws) (.collection kind (before ++ item :: tail) rest)
          (.collection kind (before ++ (deepSplice law item ++ tail.flatMap (deepSplice law))) rest) := by
      intro kept
      have later := deepSpliceSteps found rest (before ++ [item]) tail
      simp only [kept, List.append_assoc, List.singleton_append] at later ⊢
      exact later
    cases item with
    | collection actual inner innerRest =>
      cases innerRest with
      | none =>
        by_cases same : actual = law.kind
        · rw [show actual = kind from same.trans kindIs]
          have move : LawStep laws (.collection kind (before ++ .collection kind inner none :: tail) rest)
              (.collection kind (before ++ inner ++ tail) rest) := .flatten found
          have inside := deepSpliceSteps found rest before (inner ++ tail)
          have spl : deepSplice law (.collection kind inner none) = inner.flatMap (deepSplice law) := by
            rw [deepSplice, if_pos kindIs.symm]
          rw [spl]
          simp only [List.flatMap_append, List.append_assoc] at inside move ⊢
          exact .trans _ _ _ (.rel _ _ move) inside
        · exact keep (by rw [deepSplice, if_neg same])
      | some name => exact keep (by simp [deepSplice])
    | apply label arguments =>
      cases arguments with
      | nil =>
        by_cases unit : law.unit = some label
        · have move : LawStep laws (.collection kind (before ++ .apply label [] :: tail) rest)
              (.collection kind (before ++ tail) rest) := .unit found unit
          have later := deepSpliceSteps found rest before tail
          rw [deepSplice, if_pos unit, List.nil_append]
          exact .trans _ _ _ (.rel _ _ move) later
        · exact keep (by rw [deepSplice, if_neg unit])
      | cons first others => exact keep (by simp [deepSplice])
    | bvar index => exact keep (by simp [deepSplice])
    | fvar name => exact keep (by simp [deepSplice])
    | lambda binder body => exact keep (by simp [deepSplice])
    | multiLambda arity binders body => exact keep (by simp [deepSplice])
    | subst body replacement => exact keep (by simp [deepSplice])
termination_by before items => (sizeOf items, before.length)
decreasing_by
  all_goals first
    | (left
       have := sizeOf_append_patterns inner tail
       simp only [List.cons.sizeOf_spec, Pattern.collection.sizeOf_spec]
       omega)
    | (left; simp only [List.cons.sizeOf_spec]; omega)

/-- The wrapper collapse is a wrapper move. -/
theorem wrapFinish_sound {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (items : List Pattern) (rest : Option String) :
    Relation.EqvGen (ModelMove laws declaration) (.collection kind items rest) (wrapFinish law kind items rest) := by
  unfold wrapFinish
  split
  · exact .rel _ _ (.inr (.inr (.singleton found)))
  · split
    · rename_i label unit
      exact .rel _ _ (.inr (.inr (.empty found unit)))
    · exact .refl _
  · exact .refl _

/-- A set's elements reach their canonical forms by law moves, and lose their repetitions by one. -/
theorem setForm_sound (kind : CollType) (items : List Pattern) (rest : Option String) :
    Relation.EqvGen (ModelMove laws declaration) (.collection kind items rest) (.collection kind (setForm kind items) rest) := by
  cases kind with
  | vec => exact .refl _
  | hashBag => exact .refl _
  | hashSet =>
    have each : ∀ item ∈ items, Relation.EqvGen (ModelMove laws declaration) item (canon item) := fun item _ =>
      ofLaws (Relation.EqvGen.mono (fun _ _ step => step.lawStep laws) _ _ (to_canon item))
    have mapped : Relation.EqvGen (ModelMove laws declaration) (.collection .hashSet items rest)
        (.collection .hashSet (items.map canon) rest) := by
      simpa using alongMove canon (fun elements => .collection .hashSet elements rest)
        (fun _ _ _ _ step => .element step) (fun _ _ _ _ step => .element step) (fun _ _ _ _ step => .element step)
        [] items each
    exact .trans _ _ _ mapped (.rel _ _ (.inl (.members fun a => List.mem_dedup.symm)))

/-- The quote-drop test at a constructor is a forward quote-drop chain. -/
theorem finish_sound (label : String) (arguments : List Pattern) :
    Relation.EqvGen (ModelMove laws declaration) (.apply label arguments)
      (finishNormalizeReflectiveApply declaration label arguments) :=
  Relation.EqvGen.mono (fun _ _ step => .inr (.inl step)) _ _ (finish_forward label arguments).same

/-- **The model normal form is sound**: every term is related to it by model moves. -/
theorem to_modelNormal : ∀ pattern : Pattern,
    Relation.EqvGen (ModelMove laws declaration) pattern (modelNormal laws declaration pattern)
  | .bvar index => by rw [modelNormal]; exact .refl _
  | .fvar name => by rw [modelNormal]; exact .refl _
  | .apply label arguments => by
    rw [modelNormal]
    have each : ∀ item ∈ arguments, Relation.EqvGen (ModelMove laws declaration) item
        (modelNormal laws declaration item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      to_modelNormal item
    have mapped : Relation.EqvGen (ModelMove laws declaration) (.apply label arguments)
        (.apply label (arguments.map (modelNormal laws declaration))) := by
      simpa using alongMove (modelNormal laws declaration) (fun items => .apply label items)
        (fun _ _ _ _ step => .apply step) (fun _ _ _ _ step => .apply step) (fun _ _ _ _ step => .apply step)
        [] arguments each
    exact .trans _ _ _ mapped (finish_sound label _)
  | .lambda binder body => by
    rw [modelNormal]
    exact liftMove (f := .lambda binder) (fun step => .lambda step) (fun step => .lambda step)
      (fun step => .lambda step) (to_modelNormal body)
  | .multiLambda arity binders body => by
    rw [modelNormal]
    exact liftMove (f := .multiLambda arity binders) (fun step => .multiLambda step) (fun step => .multiLambda step)
      (fun step => .multiLambda step) (to_modelNormal body)
  | .subst body replacement => by
    rw [modelNormal]
    exact .trans _ _ _
      (liftMove (f := fun x => .subst x replacement) (fun step => .substBody step) (fun step => .substBody step)
        (fun step => .substBody step) (to_modelNormal body))
      (liftMove (f := fun x => .subst (modelNormal laws declaration body) x) (fun step => .substReplacement step)
        (fun step => .substReplacement step) (fun step => .substReplacement step) (to_modelNormal replacement))
  | .collection kind elements rest => by
    rw [modelNormal]
    have each : ∀ item ∈ elements, Relation.EqvGen (ModelMove laws declaration) item
        (modelNormal laws declaration item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      to_modelNormal item
    have mapped : Relation.EqvGen (ModelMove laws declaration) (.collection kind elements rest)
        (.collection kind (elements.map (modelNormal laws declaration)) rest) := by
      simpa using alongMove (modelNormal laws declaration) (fun items => .collection kind items rest)
        (fun _ _ _ _ step => .element step) (fun _ _ _ _ step => .element step) (fun _ _ _ _ step => .element step)
        [] elements each
    split
    · rename_i law found
      exact .trans _ _ _ mapped (.trans _ _ _ (ofLaws (by simpa using deepSpliceSteps found rest [] _))
        (.trans _ _ _ (setForm_sound kind _ rest) (wrapFinish_sound found _ rest)))
    · exact mapped
termination_by pattern => sizeOf pattern

/-! ## Free names -/

/-- Deep splicing adds no free name. -/
theorem deepSplice_freeFvarNames (law : Laws) (pattern : Pattern) :
    ∀ item ∈ deepSplice law pattern, ∀ name ∈ item.freeFvarNames, name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
    intro item member name named
    cases rest with
    | none =>
      rw [deepSplice] at member
      split at member
      · obtain ⟨element, elementIn, inside⟩ := List.mem_flatMap.mp member
        simp only [Pattern.freeFvarNames, List.mem_append]
        exact .inl (List.mem_flatMap.mpr ⟨element, elementIn, ih element elementIn item inside name named⟩)
      · rw [List.mem_singleton] at member
        subst member
        exact named
    | some other =>
      have kept : deepSplice law (.collection kind elements (some other)) = [.collection kind elements (some other)] := by
        simp [deepSplice]
      rw [kept, List.mem_singleton] at member
      subst member
      exact named
  | happly label arguments _ =>
    intro item member name named
    cases arguments with
    | nil =>
      rw [deepSplice] at member
      split at member
      · simp at member
      · rw [List.mem_singleton] at member
        subst member
        exact named
    | cons first others =>
      have kept : deepSplice law (.apply label (first :: others)) = [.apply label (first :: others)] := by
        simp [deepSplice]
      rw [kept, List.mem_singleton] at member
      subst member
      exact named
  | hbvar index => intro item member name named; simp [deepSplice] at member; subst member; exact named
  | hfvar other => intro item member name named; simp [deepSplice] at member; subst member; exact named
  | hlambda binder body _ => intro item member name named; simp [deepSplice] at member; subst member; exact named
  | hmultiLambda arity binders body _ =>
    intro item member name named; simp [deepSplice] at member; subst member; exact named
  | hsubst body replacement _ _ =>
    intro item member name named; simp [deepSplice] at member; subst member; exact named

theorem wrapFinish_freeFvarNames {law : Laws} (kind : CollType) (items : List Pattern) (rest : Option String)
    (name : String) :
    name ∈ (wrapFinish law kind items rest).freeFvarNames → name ∈ (Pattern.collection kind items rest).freeFvarNames := by
  intro member
  unfold wrapFinish at member
  split at member
  · simpa [Pattern.freeFvarNames] using member
  · split at member
    · simp [Pattern.freeFvarNames] at member
    · exact member
  · exact member

theorem setForm_freeFvarNames (kind : CollType) (items : List Pattern) (rest : Option String) (name : String) :
    name ∈ (Pattern.collection kind (setForm kind items) rest).freeFvarNames →
      name ∈ (Pattern.collection kind items rest).freeFvarNames := by
  cases kind with
  | vec => exact id
  | hashBag => exact id
  | hashSet =>
    intro member
    simp only [setForm_set, Pattern.freeFvarNames, List.mem_append, List.mem_flatMap] at member ⊢
    refine member.imp (fun ⟨item, itemIn, named⟩ => ?_) id
    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp itemIn)
    exact ⟨original, originalIn, (canon_freeFvarNames original name).mp named⟩

/-- **The model normal form adds no free name.** -/
theorem modelNormal_freeFvarNames (pattern : Pattern) (name : String) :
    name ∈ (modelNormal laws declaration pattern).freeFvarNames → name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => intro member; rw [modelNormal] at member; exact member
  | hfvar other => intro member; rw [modelNormal] at member; exact member
  | happly label arguments ih =>
    intro member
    rw [modelNormal] at member
    have inside := QuoteDrop.finish_freeFvarNames label _ name member
    simp only [Pattern.freeFvarNames, List.mem_flatMap, List.mem_map] at inside ⊢
    obtain ⟨_, ⟨argument, argumentIn, rfl⟩, named⟩ := inside
    exact ⟨argument, argumentIn, ih argument argumentIn name named⟩
  | hlambda binder body ih =>
    intro member; rw [modelNormal] at member; simp only [Pattern.freeFvarNames] at member ⊢; exact ih name member
  | hmultiLambda arity binders body ih =>
    intro member; rw [modelNormal] at member; simp only [Pattern.freeFvarNames] at member ⊢; exact ih name member
  | hsubst body replacement bodyIH replacementIH =>
    intro member
    rw [modelNormal] at member
    simp only [Pattern.freeFvarNames, List.mem_append] at member ⊢
    exact member.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro member
    have mapped : name ∈ (Pattern.collection kind (elements.map (modelNormal laws declaration)) rest).freeFvarNames := by
      cases found : lawFor laws kind with
      | none => rw [modelNormal, found] at member; exact member
      | some law =>
        rw [modelNormal, found] at member
        have inside := setForm_freeFvarNames kind _ rest name (wrapFinish_freeFvarNames kind _ rest name member)
        simp only [Pattern.freeFvarNames, List.mem_append] at inside ⊢
        refine inside.imp (fun spliced => ?_) id
        obtain ⟨item, itemIn, named⟩ := List.mem_flatMap.mp spliced
        obtain ⟨original, originalIn, fromOriginal⟩ := List.mem_flatMap.mp itemIn
        exact List.mem_flatMap.mpr
          ⟨original, originalIn, deepSplice_freeFvarNames law original item fromOriginal name named⟩
    simp only [Pattern.freeFvarNames, List.mem_append, List.flatMap_map] at mapped ⊢
    refine mapped.imp (fun inside => ?_) id
    obtain ⟨element, elementIn, named⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨element, elementIn, ih element elementIn name named⟩

/-! ## Normal forms -/

variable (laws declaration)

/-- **Model normal forms**, hereditarily: no quote-drop pair at a constructor, and at a collection of a
flattening kind nothing left to splice, no wrapper to collapse, and for a set canonical elements
without repetition. -/
inductive Normal : Pattern → Prop where
  | bvar (index : Nat) : Normal (.bvar index)
  | fvar (name : String) : Normal (.fvar name)
  | apply {label : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments, Normal argument) →
      finishNormalizeReflectiveApply declaration label arguments = .apply label arguments →
      Normal (.apply label arguments)
  | lambda {binder : Option String} {body : Pattern} : Normal body → Normal (.lambda binder body)
  | multiLambda {arity : Nat} {binders : List String} {body : Pattern} :
      Normal body → Normal (.multiLambda arity binders body)
  | subst {body replacement : Pattern} : Normal body → Normal replacement → Normal (.subst body replacement)
  | collectionPlain {kind : CollType} {items : List Pattern} {rest : Option String} :
      (∀ item ∈ items, Normal item) → lawFor laws kind = none → Normal (.collection kind items rest)
  | collectionLaw {kind : CollType} {items : List Pattern} {rest : Option String} {law : Laws} :
      (∀ item ∈ items, Normal item) → lawFor laws kind = some law →
      (∀ item ∈ items, deepSplice law item = [item]) →
      wrapFinish law kind items rest = .collection kind items rest →
      (kind = .hashSet → items.Nodup ∧ ∀ item ∈ items, canon item = item) →
      Normal (.collection kind items rest)

variable {laws declaration}

theorem flatMap_stable {f : Pattern → List Pattern} :
    ∀ {items : List Pattern}, (∀ item ∈ items, f item = [item]) → items.flatMap f = items
  | [], _ => rfl
  | item :: rest, stable => by
    rw [List.flatMap_cons, stable item (.head _), flatMap_stable (fun other member => stable other (.tail _ member))]
    rfl

/-- Deep splicing leaves nothing to splice. -/
theorem deepSplice_stable (law : Laws) (pattern : Pattern) :
    ∀ item ∈ deepSplice law pattern, deepSplice law item = [item] := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
    intro item member
    cases rest with
    | none =>
      rw [deepSplice] at member
      split at member
      · obtain ⟨element, elementIn, inner⟩ := List.mem_flatMap.mp member
        exact ih element elementIn item inner
      · rename_i different
        rw [List.mem_singleton] at member
        subst member
        rw [deepSplice, if_neg different]
    | some name =>
      have kept : deepSplice law (.collection kind elements (some name)) = [.collection kind elements (some name)] := by
        simp [deepSplice]
      rw [kept, List.mem_singleton] at member
      subst member
      exact kept
  | happly label arguments _ =>
    intro item member
    cases arguments with
    | nil =>
      rw [deepSplice] at member
      split at member
      · simp at member
      · rename_i notUnit
        rw [List.mem_singleton] at member
        subst member
        rw [deepSplice, if_neg notUnit]
    | cons first others =>
      have kept : deepSplice law (.apply label (first :: others)) = [.apply label (first :: others)] := by
        simp [deepSplice]
      rw [kept, List.mem_singleton] at member
      subst member
      exact kept
  | hbvar index => intro item member; simp [deepSplice] at member; subst member; simp [deepSplice]
  | hfvar name => intro item member; simp [deepSplice] at member; subst member; simp [deepSplice]
  | hlambda binder body _ => intro item member; simp [deepSplice] at member; subst member; simp [deepSplice]
  | hmultiLambda arity binders body _ =>
    intro item member; simp [deepSplice] at member; subst member; simp [deepSplice]
  | hsubst body replacement _ _ => intro item member; simp [deepSplice] at member; subst member; simp [deepSplice]

/-- Deep splicing a collapsed wrapper gives back what was collapsed. -/
theorem deepSplice_wrapFinish {law : Laws} {kind : CollType} (kindIs : law.kind = kind) {items : List Pattern}
    (stable : ∀ item ∈ items, deepSplice law item = [item]) :
    deepSplice law (wrapFinish law kind items none) = items := by
  match items, stable with
  | [], _ =>
    unfold wrapFinish
    cases unit : law.unit with
    | none => simp only; rw [deepSplice, if_pos kindIs.symm]; rfl
    | some label => simp only; rw [deepSplice, if_pos unit]
  | [item], stable => exact stable item (.head _)
  | first :: second :: others, stable =>
    unfold wrapFinish
    simp only
    rw [deepSplice, if_pos kindIs.symm, flatMap_stable stable]

/-- The quote-drop test at a constructor either keeps the constructor or collapses a quote-drop pair. -/
theorem finish_cases (label : String) (arguments : List Pattern) :
    finishNormalizeReflectiveApply declaration label arguments = .apply label arguments ∨
      ∃ name, arguments = [.apply declaration.dropConstructor [name]] ∧
        finishNormalizeReflectiveApply declaration label arguments = name := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · split
      · rename_i drop name isDrop
        exact .inr ⟨name, by simp at isDrop; rw [isDrop], rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- A set of canonical elements without repetition is its own set form. -/
theorem setForm_fixed {kind : CollType} {items : List Pattern}
    (sets : kind = .hashSet → items.Nodup ∧ ∀ item ∈ items, canon item = item) : setForm kind items = items := by
  cases kind with
  | vec => rfl
  | hashBag => rfl
  | hashSet =>
    obtain ⟨nodup, fixed⟩ := sets rfl
    rw [setForm_set, List.map_congr_left fixed, List.map_id', nodup.dedup]

/-- **A normal form is its own model normal form.** -/
theorem Normal.fixed {pattern : Pattern} (normal : Normal laws declaration pattern) :
    modelNormal laws declaration pattern = pattern := by
  induction normal with
  | bvar index => rw [modelNormal]
  | fvar name => rw [modelNormal]
  | @apply label arguments _ kept ih =>
    rw [modelNormal, List.map_congr_left ih, List.map_id', kept]
  | lambda _ ih => rw [modelNormal, ih]
  | multiLambda _ ih => rw [modelNormal, ih]
  | subst _ _ bodyIH replacementIH => rw [modelNormal, bodyIH, replacementIH]
  | @collectionPlain kind items rest _ none ih =>
    rw [modelNormal, none]
    simp only
    rw [List.map_congr_left ih, List.map_id']
  | @collectionLaw kind items rest law _ found stable settled sets ih =>
    rw [modelNormal, found]
    simp only
    rw [List.map_congr_left ih, List.map_id', flatMap_stable stable, setForm_fixed sets, settled]

/-- Normal forms have normal deep splicings. -/
theorem deepSplice_normal {law : Laws} {kind : CollType} (found : lawFor laws kind = some law) {pattern : Pattern}
    (normal : Normal laws declaration pattern) : ∀ item ∈ deepSplice law pattern, Normal laws declaration item := by
  have kindIs : law.kind = kind := lawFor_kind found
  intro item member
  cases normal with
  | @collectionLaw actual items rest other members found' stable settled sets =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · subst same
        rw [kindIs] at found'
        rw [found] at found'
        cases found'
        rw [deepSplice, if_pos rfl, flatMap_stable stable] at member
        exact members item member
      · rw [deepSplice, if_neg same, List.mem_singleton] at member
        subst member
        exact .collectionLaw members found' stable settled sets
    | some name =>
      simp only [deepSplice, List.mem_singleton] at member
      subst member
      exact .collectionLaw members found' stable settled sets
  | @collectionPlain actual items rest members none =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · subst same; rw [kindIs, found] at none; cases none
      · rw [deepSplice, if_neg same, List.mem_singleton] at member
        subst member
        exact .collectionPlain members none
    | some name =>
      simp only [deepSplice, List.mem_singleton] at member
      subst member
      exact .collectionPlain members none
  | @apply label arguments members kept =>
    cases arguments with
    | nil =>
      rw [deepSplice] at member
      split at member
      · simp at member
      · rw [List.mem_singleton] at member; subst member; exact .apply members kept
    | cons first others =>
      simp only [deepSplice, List.mem_singleton] at member
      subst member
      exact .apply members kept
  | bvar index => simp only [deepSplice, List.mem_singleton] at member; subst member; exact .bvar index
  | fvar name => simp only [deepSplice, List.mem_singleton] at member; subst member; exact .fvar name
  | lambda body => simp only [deepSplice, List.mem_singleton] at member; subst member; exact .lambda body
  | multiLambda body => simp only [deepSplice, List.mem_singleton] at member; subst member; exact .multiLambda body
  | subst body replacement =>
    simp only [deepSplice, List.mem_singleton] at member; subst member; exact .subst body replacement

/-- The quote-drop test keeps normal forms normal. -/
theorem normal_finish (label : String) {arguments : List Pattern}
    (normal : ∀ argument ∈ arguments, Normal laws declaration argument) :
    Normal laws declaration (finishNormalizeReflectiveApply declaration label arguments) := by
  rcases finish_cases (declaration := declaration) label arguments with kept | ⟨name, rfl, collapsed⟩
  · rw [kept]; exact .apply normal kept
  · rw [collapsed]
    cases normal _ (.head _) with
    | apply members _ => exact members name (.head _)

/-- On a normal form, deep splicing is splicing. -/
theorem deepSplice_eq_splice {law : Laws} {kind : CollType} (found : lawFor laws kind = some law)
    {pattern : Pattern} (normal : Normal laws declaration pattern) : deepSplice law pattern = splice law pattern := by
  have kindIs : law.kind = kind := lawFor_kind found
  cases normal with
  | @collectionLaw actual items rest other members found' stable settled _ =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · subst same
        rw [kindIs, found] at found'
        cases found'
        rw [deepSplice, if_pos rfl, flatMap_stable stable, splice, if_pos rfl]
      · rw [deepSplice, if_neg same, splice, if_neg same]
    | some name => simp [deepSplice, splice]
  | @collectionPlain actual items rest members none =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · subst same; rw [kindIs, found] at none; cases none
      · rw [deepSplice, if_neg same, splice, if_neg same]
    | some name => simp [deepSplice, splice]
  | @apply label arguments members kept =>
    cases arguments with
    | nil => rw [deepSplice, splice]
    | cons first others => simp [deepSplice, splice]
  | bvar index => simp [deepSplice, splice]
  | fvar name => simp [deepSplice, splice]
  | lambda body => simp [deepSplice, splice]
  | multiLambda body => simp [deepSplice, splice]
  | subst body replacement => simp [deepSplice, splice]

/-- Canonical forms commute with the quote-drop test. -/
theorem canon_finish (label : String) (arguments : List Pattern) :
    canon (finishNormalizeReflectiveApply declaration label arguments) =
      finishNormalizeReflectiveApply declaration label (arguments.map canon) := by
  unfold finishNormalizeReflectiveApply
  split
  · match arguments with
    | [.apply drop [name]] =>
      simp only [List.map_cons, List.map_nil, canon_apply]
      split <;> simp [canon_apply]
    | [] => simp [canon_apply]
    | [.bvar index] => simp [canon_apply, canon]
    | [.fvar name] => simp [canon_apply, canon]
    | [.apply drop []] => simp [canon_apply]
    | [.apply drop (first :: second :: others)] => simp [canon_apply]
    | [.lambda binder body] => simp [canon_apply, canon]
    | [.multiLambda arity binders body] => simp [canon_apply, canon]
    | [.subst body replacement] => simp [canon_apply, canon]
    | [.collection kind elements rest] => simp [canon_apply, canon_collection]
    | first :: second :: others => simp [canon_apply]
  · rw [canon_apply]

/-! ## Canonical forms of normal forms -/

/-- Splicing is decided by the outermost shape, which the canonical form keeps. -/
theorem splice_canon_stable {law : Laws} {pattern : Pattern} (stable : splice law pattern = [pattern]) :
    splice law (canon pattern) = [canon pattern] := by
  cases pattern with
  | collection kind elements rest =>
    cases rest with
    | none =>
      rw [canon_collection]
      by_cases same : kind = law.kind
      · exfalso
        rw [splice, if_pos same] at stable
        have sizes := congrArg sizeOf stable
        simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Pattern.collection.sizeOf_spec] at sizes
        omega
      · rw [splice, if_neg same]
    | some name => rw [canon_collection]; simp [splice]
  | apply label arguments =>
    cases arguments with
    | nil =>
      rw [canon_apply, List.map_nil]
      exact stable
    | cons first others => rw [canon_apply, List.map_cons]; simp [splice]
  | bvar index => rw [canon]; simp [splice]
  | fvar name => rw [canon]; simp [splice]
  | lambda binder body => rw [canon]; simp [splice]
  | multiLambda arity binders body => rw [canon]; simp [splice]
  | subst body replacement => rw [canon]; simp [splice]

/-- The wrapper collapse is decided by the length of the elements, with the rest. -/
theorem wrapFinish_eq_of_length {law : Laws} {kind : CollType} {rest : Option String} {items items' : List Pattern}
    (lengths : items.length = items'.length) (settled : wrapFinish law kind items rest = .collection kind items rest) :
    wrapFinish law kind items' rest = .collection kind items' rest := by
  cases rest with
  | some name => rfl
  | none =>
    cases items with
    | nil =>
      cases items' with
      | nil => exact settled
      | cons _ _ => simp at lengths
    | cons first tail =>
      cases tail with
      | nil =>
        exfalso
        have sizes := congrArg sizeOf settled
        rw [show wrapFinish law kind [first] none = first from rfl] at sizes
        simp only [Pattern.collection.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec] at sizes
        omega
      | cons second others =>
        cases items' with
        | nil => simp at lengths
        | cons first' tail' =>
          cases tail' with
          | nil => simp at lengths
          | cons _ _ => rfl

/-- **The canonical form of a normal form is normal.** -/
theorem Normal.canonical {pattern : Pattern} (normal : Normal laws declaration pattern) :
    Normal laws declaration (canon pattern) := by
  induction normal with
  | bvar index => rw [CanonicalBags.canon]; exact .bvar index
  | fvar name => rw [CanonicalBags.canon]; exact .fvar name
  | @apply label arguments _ kept ih =>
    rw [canon_apply]
    refine .apply (fun argument member => ?_) ?_
    · obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
      exact ih original originalIn
    · rw [← canon_finish, kept, canon_apply]
  | lambda _ ih => rw [CanonicalBags.canon]; exact .lambda ih
  | multiLambda _ ih => rw [CanonicalBags.canon]; exact .multiLambda ih
  | subst _ _ bodyIH replacementIH => rw [CanonicalBags.canon]; exact .subst bodyIH replacementIH
  | @collectionPlain kind items rest _ none ih =>
    rw [canon_collection]
    refine .collectionPlain (fun item member => ?_) none
    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp ((arrange_mem item).mp member)
    exact ih original originalIn
  | @collectionLaw kind items rest law members found stable settled sets ih =>
    rw [canon_collection]
    have origins : ∀ item ∈ arrange kind (items.map canon), ∃ original ∈ items, item = canon original := by
      intro item member
      obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp ((arrange_mem item).mp member)
      exact ⟨original, originalIn, rfl⟩
    have lengths : items.length = (arrange kind (items.map canon)).length := by
      cases kind with
      | vec => simp [arrange_vec]
      | hashBag => simp [arrange_bag, (PatternLexOrder.sortLex_perm _).length_eq]
      | hashSet =>
        obtain ⟨nodup, fixed⟩ := sets rfl
        rw [arrange_set, List.map_congr_left fixed, List.map_id',
          ((PatternLexOrder.sortLex_perm items).nodup_iff.mpr nodup).dedup, (PatternLexOrder.sortLex_perm items).length_eq]
    refine .collectionLaw (fun item member => ?_) found (fun item member => ?_)
      (wrapFinish_eq_of_length lengths settled) ?_
    · obtain ⟨original, originalIn, rfl⟩ := origins item member
      exact ih original originalIn
    · obtain ⟨original, originalIn, rfl⟩ := origins item member
      rw [deepSplice_eq_splice found (ih original originalIn)]
      exact splice_canon_stable
        ((deepSplice_eq_splice found (members original originalIn)).symm.trans (stable original originalIn))
    · rintro rfl
      refine ⟨List.nodup_dedup _, fun item member => ?_⟩
      obtain ⟨original, _, rfl⟩ := origins item member
      exact canon_idempotent original

/-- **The model normal form is normal.** -/
theorem normal_modelNormal (pattern : Pattern) : Normal laws declaration (modelNormal laws declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [modelNormal]; exact .bvar index
  | hfvar name => rw [modelNormal]; exact .fvar name
  | happly label arguments ih =>
    rw [modelNormal]
    exact normal_finish label fun argument member => by
      obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
      exact ih original originalIn
  | hlambda binder body ih => rw [modelNormal]; exact .lambda ih
  | hmultiLambda arity binders body ih => rw [modelNormal]; exact .multiLambda ih
  | hsubst body replacement bodyIH replacementIH => rw [modelNormal]; exact .subst bodyIH replacementIH
  | hcollection kind elements rest ih =>
    rw [modelNormal]
    cases found : lawFor laws kind with
    | none =>
      simp only
      exact .collectionPlain (fun item member => by
        obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
        exact ih original originalIn) found
    | some law =>
      simp only
      have members : ∀ item ∈ (elements.map (modelNormal laws declaration)).flatMap (deepSplice law),
          Normal laws declaration item := by
        intro item member
        obtain ⟨normalized, normalizedIn, inside⟩ := List.mem_flatMap.mp member
        obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp normalizedIn
        exact deepSplice_normal found (ih original originalIn) item inside
      have stable : ∀ item ∈ (elements.map (modelNormal laws declaration)).flatMap (deepSplice law),
          deepSplice law item = [item] := by
        intro item member
        obtain ⟨normalized, _, inside⟩ := List.mem_flatMap.mp member
        exact deepSplice_stable law normalized item inside
      generalize ((elements.map (modelNormal laws declaration)).flatMap (deepSplice law)) = items at members stable
      have members' : ∀ item ∈ setForm kind items, Normal laws declaration item := fun item member => by
        cases kind with
        | vec => exact members item member
        | hashBag => exact members item member
        | hashSet =>
          obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp member)
          exact (members original originalIn).canonical
      have stable' : ∀ item ∈ setForm kind items, deepSplice law item = [item] := fun item member => by
        cases kind with
        | vec => exact stable item member
        | hashBag => exact stable item member
        | hashSet =>
          obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp member)
          rw [deepSplice_eq_splice found (members original originalIn).canonical]
          exact splice_canon_stable
            ((deepSplice_eq_splice found (members original originalIn)).symm.trans (stable original originalIn))
      have sets : kind = .hashSet → (setForm kind items).Nodup ∧ ∀ item ∈ setForm kind items, canon item = item := by
        rintro rfl
        refine ⟨List.nodup_dedup _, fun item member => ?_⟩
        obtain ⟨original, _, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp member)
        exact canon_idempotent original
      generalize setForm kind items = formed at members' stable' sets
      unfold wrapFinish
      split
      · exact members' _ (.head _)
      · split
        · rename_i label _
          exact .apply (fun _ member => by simp at member) (finish_nil declaration label)
        · exact .collectionLaw members' found stable' (by unfold wrapFinish; rename_i unit; simp [unit]) sets
      · exact .collectionLaw members' found stable' (by unfold wrapFinish; split <;> simp_all) sets

/-- **A normal form re-collapses to itself** after deep splicing into a collection of a flattening kind. -/
theorem Normal.rewrap {law : Laws} {kind : CollType} (found : lawFor laws kind = some law) {pattern : Pattern}
    (normal : Normal laws declaration pattern) :
    wrapFinish law kind (deepSplice law pattern) none = pattern := by
  have kindIs : law.kind = kind := lawFor_kind found
  cases normal with
  | @collectionLaw actual items rest other members found' stable settled _ =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · subst same
        rw [kindIs] at found' settled ⊢
        rw [found] at found'
        cases found'
        rw [deepSplice, if_pos kindIs.symm, flatMap_stable stable, settled]
      · rw [deepSplice, if_neg same]; rfl
    | some name => simp [deepSplice, wrapFinish]
  | @collectionPlain actual items rest members none =>
    cases rest with
    | none =>
      by_cases same : actual = law.kind
      · subst same; rw [kindIs, found] at none; cases none
      · rw [deepSplice, if_neg same]; rfl
    | some name => simp [deepSplice, wrapFinish]
  | @apply label arguments members kept =>
    cases arguments with
    | nil =>
      rw [deepSplice]
      split
      · rename_i unit
        unfold wrapFinish
        simp [unit]
      · rfl
    | cons first others => simp [deepSplice, wrapFinish]
  | bvar index => simp [deepSplice, wrapFinish]
  | fvar name => simp [deepSplice, wrapFinish]
  | lambda body => simp [deepSplice, wrapFinish]
  | multiLambda body => simp [deepSplice, wrapFinish]
  | subst body replacement => simp [deepSplice, wrapFinish]

theorem dedup_singleton (pattern : Pattern) : [pattern].dedup = [pattern] := (List.nodup_singleton pattern).dedup

/-- **A normal form re-collapses to itself, up to its canonical form**, after deep splicing into a
collection of a flattening kind and taking the set form. -/
theorem Normal.rewrap_same {law : Laws} {kind : CollType} (found : lawFor laws kind = some law) {pattern : Pattern}
    (normal : Normal laws declaration pattern) :
    Same (wrapFinish law kind (setForm kind (deepSplice law pattern)) none) pattern := by
  have kindIs : law.kind = kind := lawFor_kind found
  cases kind with
  | vec => rw [setForm_vec, normal.rewrap found]; exact same_refl _
  | hashBag => rw [setForm_bag, normal.rewrap found]; exact same_refl _
  | hashSet =>
    rw [setForm_set]
    cases normal with
    | @collectionLaw actual items rest other members found' stable settled sets =>
      cases rest with
      | none =>
        by_cases same : actual = law.kind
        · subst same
          rw [kindIs] at found' settled sets ⊢
          rw [found] at found'
          cases found'
          obtain ⟨nodup, fixed⟩ := sets rfl
          rw [deepSplice, if_pos kindIs.symm, flatMap_stable stable, List.map_congr_left fixed, List.map_id',
            nodup.dedup, settled]
          exact same_refl _
        · rw [deepSplice, if_neg same, List.map_cons, List.map_nil, dedup_singleton]
          exact canon_idempotent _
      | some name =>
        simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]
        exact canon_idempotent _
    | @collectionPlain actual items rest members none =>
      cases rest with
      | none =>
        by_cases same : actual = law.kind
        · subst same; rw [kindIs, found] at none; cases none
        · rw [deepSplice, if_neg same, List.map_cons, List.map_nil, dedup_singleton]
          exact canon_idempotent _
      | some name =>
        simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]
        exact canon_idempotent _
    | @apply label arguments members kept =>
      cases arguments with
      | nil =>
        rw [deepSplice]
        split
        · rename_i unit
          simp only [List.map_nil, List.dedup_nil, wrapFinish]
          rw [unit]
          exact rfl
        · rw [List.map_cons, List.map_nil, dedup_singleton]
          exact canon_idempotent _
      | cons first others =>
        simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]
        exact canon_idempotent _
    | bvar index => simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]; exact canon_idempotent _
    | fvar name => simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]; exact canon_idempotent _
    | lambda body => simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]; exact canon_idempotent _
    | multiLambda body =>
      simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]; exact canon_idempotent _
    | subst body replacement =>
      simp only [deepSplice, List.map_cons, List.map_nil, dedup_singleton]; exact canon_idempotent _

/-! ## Canonical forms commute with the steps of the normal form -/

/-- The model normal form of a collection of a flattening kind, with shallow splicing. -/
theorem modelNormal_collection_splice {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (elements : List Pattern) (rest : Option String) :
    modelNormal laws declaration (.collection kind elements rest) =
      wrapFinish law kind (setForm kind ((elements.map (modelNormal laws declaration)).flatMap (splice law))) rest := by
  rw [modelNormal, found]
  simp only
  congr 2
  apply List.flatMap_congr
  intro item member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact deepSplice_eq_splice found (normal_modelNormal original)

/-- **A model normal form is a normal form of the declared laws.** -/
theorem Normal.lawNormal {pattern : Pattern} (normal : Normal laws declaration pattern) :
    CollectionLaws.normalize laws pattern = pattern := by
  induction normal with
  | bvar index => rw [CollectionLaws.normalize]
  | fvar name => rw [CollectionLaws.normalize]
  | @apply label arguments _ _ ih => rw [CollectionLaws.normalize, List.map_congr_left ih, List.map_id']
  | lambda _ ih => rw [CollectionLaws.normalize, ih]
  | multiLambda _ ih => rw [CollectionLaws.normalize, ih]
  | subst _ _ bodyIH replacementIH => rw [CollectionLaws.normalize, bodyIH, replacementIH]
  | @collectionPlain kind items rest _ none ih =>
    rw [CollectionLaws.normalize]
    simp only [lawFor] at none
    simp only [none, List.map_congr_left ih, List.map_id']
  | @collectionLaw kind items rest law members found stable _ _ ih =>
    rw [CollectionLaws.normalize]
    have found' := found
    simp only [lawFor] at found'
    simp only [found', List.map_congr_left ih, List.map_id']
    rw [flatMap_splice_fixed law items fun item member =>
      (deepSplice_eq_splice found (members item member)).symm.trans (stable item member)]

/-- The declared laws leave the model normal form as it is. -/
theorem normalize_modelNormal (pattern : Pattern) :
    CollectionLaws.normalize laws (modelNormal laws declaration pattern) = modelNormal laws declaration pattern :=
  (normal_modelNormal pattern).lawNormal

theorem finish_same (label : String) {arguments arguments' : List Pattern}
    (pointwise : List.Forall₂ Same arguments arguments') :
    Same (finishNormalizeReflectiveApply declaration label arguments)
      (finishNormalizeReflectiveApply declaration label arguments') := by
  unfold Same
  rw [canon_finish, canon_finish, forall₂_same_map pointwise]

theorem presents_singleton {kind : CollType} {a b : Pattern} (presents : Presents kind [a] [b]) : a = b := by
  cases kind with
  | vec => exact List.singleton_inj.mp (show [a] = [b] from presents)
  | hashBag => exact List.singleton_perm_singleton.mp presents
  | hashSet => simpa using (presents a).mp (List.mem_singleton_self a)

theorem presents_length {kind : CollType} {left right : List Pattern} (presents : Presents kind left right)
    (nodupLeft : kind = .hashSet → left.Nodup) (nodupRight : kind = .hashSet → right.Nodup) :
    left.length = right.length := by
  cases kind with
  | vec => rw [show left = right from presents]
  | hashBag => exact List.Perm.length_eq presents
  | hashSet =>
    exact ((List.perm_ext_iff_of_nodup (nodupLeft rfl) (nodupRight rfl)).mpr presents).length_eq

/-- The set form presents the elements' canonical forms alike. -/
theorem setForm_presents (kind : CollType) (items : List Pattern) :
    Presents kind ((setForm kind items).map canon) (items.map canon) := by
  cases kind with
  | vec => exact rfl
  | hashBag => exact List.Perm.refl _
  | hashSet =>
    intro a
    simp only [setForm_set, List.mem_map, List.mem_dedup]
    constructor
    · rintro ⟨_, ⟨original, originalIn, rfl⟩, rfl⟩
      exact ⟨original, originalIn, (canon_idempotent original).symm⟩
    · rintro ⟨original, originalIn, rfl⟩
      exact ⟨canon original, ⟨original, originalIn, rfl⟩, canon_idempotent original⟩

theorem Presents.symm {kind : CollType} {left right : List Pattern} (presents : Presents kind left right) :
    Presents kind right left := by
  cases kind with
  | vec => exact presents.symm
  | hashBag => exact presents.symm
  | hashSet => exact fun a => (presents a).symm

theorem Presents.trans {kind : CollType} {first second third : List Pattern} (one : Presents kind first second)
    (two : Presents kind second third) : Presents kind first third := by
  cases kind with
  | vec => exact one.trans two
  | hashBag => exact one.trans two
  | hashSet => exact fun a => (one a).trans (two a)

theorem setForm_nodup (kind : CollType) (items : List Pattern) : kind = .hashSet → (setForm kind items).Nodup := by
  rintro rfl; exact List.nodup_dedup _

/-- The wrapper collapse of lists of equal length presented alike. -/
theorem wrapFinish_same_of_presents (law : Laws) (kind : CollType) (rest : Option String) {left right : List Pattern}
    (lengths : left.length = right.length) (presents : Presents kind (left.map canon) (right.map canon)) :
    Same (wrapFinish law kind left rest) (wrapFinish law kind right rest) := by
  cases rest with
  | some name => unfold wrapFinish; exact canon_collection_of_presents kind _ presents
  | none =>
    match left, right, lengths, presents with
    | [], [], _, _ => rfl
    | [item], [item'], _, presents =>
      unfold wrapFinish
      simp only
      exact presents_singleton presents
    | first :: second :: others, first' :: second' :: others', _, presents =>
      unfold wrapFinish
      exact canon_collection_of_presents kind _ presents

/-- The wrapper collapse respects the kind's presentation of the spliced elements: a permutation of a
bag's, the same elements of a set's. -/
theorem wrapFinish_same (law : Laws) (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (presents : Presents kind (items.map canon) (items'.map canon)) :
    Same (wrapFinish law kind (setForm kind items) rest) (wrapFinish law kind (setForm kind items') rest) := by
  have formed : Presents kind ((setForm kind items).map canon) ((setForm kind items').map canon) :=
    Presents.trans (Presents.trans (setForm_presents kind items) presents) (Presents.symm (setForm_presents kind items'))
  refine wrapFinish_same_of_presents law kind rest ?_ formed
  cases kind with
  | vec => simpa using congrArg List.length (show (setForm .vec items).map canon = (setForm .vec items').map canon from formed)
  | hashBag => simpa using List.Perm.length_eq formed
  | hashSet =>
    have fixed : ∀ list : List Pattern, (setForm .hashSet list).map canon = setForm .hashSet list := fun list => by
      rw [setForm_set]
      refine (List.map_congr_left fun item member => ?_).trans (List.map_id' _)
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp member)
      exact canon_idempotent original
    have perm : ((setForm .hashSet items).map canon).Perm ((setForm .hashSet items').map canon) := by
      rw [List.perm_ext_iff_of_nodup (by rw [fixed]; exact List.nodup_dedup _) (by rw [fixed]; exact List.nodup_dedup _)]
      exact formed
    simpa using perm.length_eq

/-! ## Every model move keeps the normal form -/

theorem pointwise_middle {before after : List Pattern} {a b : Pattern} (same : Same a b) :
    List.Forall₂ Same (before ++ a :: after) (before ++ b :: after) :=
  List.rel_append (List.forall₂_same.mpr fun _ _ => same_refl _) (.cons same (List.forall₂_same.mpr fun _ _ => same_refl _))

theorem context_apply (label : String) {before after : List Pattern} {a b : Pattern}
    (same : Same (modelNormal laws declaration a) (modelNormal laws declaration b)) :
    Same (modelNormal laws declaration (.apply label (before ++ a :: after)))
      (modelNormal laws declaration (.apply label (before ++ b :: after))) := by
  rw [modelNormal, modelNormal]
  apply finish_same
  simpa only [List.map_append, List.map_cons] using pointwise_middle same

theorem context_element (kind : CollType) (rest : Option String) {before after : List Pattern} {a b : Pattern}
    (same : Same (modelNormal laws declaration a) (modelNormal laws declaration b)) :
    Same (modelNormal laws declaration (.collection kind (before ++ a :: after) rest))
      (modelNormal laws declaration (.collection kind (before ++ b :: after) rest)) := by
  cases found : lawFor laws kind with
  | none =>
    rw [modelNormal, found, modelNormal, found]
    exact same_collection_congr kind rest (by simpa only [List.map_append, List.map_cons] using pointwise_middle same)
  | some law =>
    have kindIs : law.kind = kind := lawFor_kind found
    rw [modelNormal_collection_splice found, modelNormal_collection_splice found]
    apply wrapFinish_same
    simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, List.map_append]
    have presents := splice_same_presents law same
    rw [kindIs] at presents
    exact Presents.surround _ _ presents

theorem context_lambda (binder : Option String) {a b : Pattern}
    (same : Same (modelNormal laws declaration a) (modelNormal laws declaration b)) :
    Same (modelNormal laws declaration (.lambda binder a)) (modelNormal laws declaration (.lambda binder b)) := by
  rw [modelNormal, modelNormal]; exact same_lambda_congr binder same

theorem context_multiLambda (arity : Nat) (binders : List String) {a b : Pattern}
    (same : Same (modelNormal laws declaration a) (modelNormal laws declaration b)) :
    Same (modelNormal laws declaration (.multiLambda arity binders a))
      (modelNormal laws declaration (.multiLambda arity binders b)) := by
  rw [modelNormal, modelNormal]; exact same_multiLambda_congr arity binders same

theorem context_substBody {a b : Pattern} (replacement : Pattern)
    (same : Same (modelNormal laws declaration a) (modelNormal laws declaration b)) :
    Same (modelNormal laws declaration (.subst a replacement)) (modelNormal laws declaration (.subst b replacement)) := by
  rw [modelNormal, modelNormal]; exact same_subst_congr same (same_refl _)

theorem context_substReplacement (body : Pattern) {a b : Pattern}
    (same : Same (modelNormal laws declaration a) (modelNormal laws declaration b)) :
    Same (modelNormal laws declaration (.subst body a)) (modelNormal laws declaration (.subst body b)) := by
  rw [modelNormal, modelNormal]; exact same_subst_congr (same_refl _) same

/-- **Every parallel-law move keeps the model normal form**, up to permutation. -/
theorem LawStep.modelNormal_same {left right : Pattern} (step : LawStep laws left right) :
    Same (modelNormal laws declaration left) (modelNormal laws declaration right) := by
  induction step with
  | @permute kind elements permuted rest unordered permutation =>
    cases found : lawFor laws kind with
    | none =>
      rw [modelNormal, found, modelNormal, found]
      exact canon_collection_of kind rest (fun _ => (permutation.map _).map canon)
        (fun ordered => by rw [unordered] at ordered; cases ordered)
    | some law =>
      rw [modelNormal_collection_splice found, modelNormal_collection_splice found]
      exact wrapFinish_same law kind rest
        (presents_of_perm unordered (((permutation.map _).flatMap_right _).map canon))
  | @members elements others rest same =>
    cases found : lawFor laws .hashSet with
    | none =>
      rw [modelNormal, found, modelNormal, found]
      exact canon_collection_of_presents .hashSet rest (members_map (members_map same _) canon)
    | some law =>
      rw [modelNormal_collection_splice found, modelNormal_collection_splice found]
      exact wrapFinish_same law .hashSet rest (members_map (members_flatMap (members_map same _) _) canon)
  | @flatten kind law before inner after rest found =>
    have kindIs : law.kind = kind := lawFor_kind found
    have stable : ∀ item ∈ (inner.map (modelNormal laws declaration)).flatMap (deepSplice law),
        deepSplice law item = [item] := by
      intro item member
      obtain ⟨normalized, _, inside⟩ := List.mem_flatMap.mp member
      exact deepSplice_stable law normalized item inside
    have normalInner : ∀ item ∈ (inner.map (modelNormal laws declaration)).flatMap (deepSplice law),
        Normal laws declaration item := by
      intro item member
      obtain ⟨normalized, normalizedIn, inside⟩ := List.mem_flatMap.mp member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp normalizedIn
      exact deepSplice_normal found (normal_modelNormal original) item inside
    have stableForm : ∀ item ∈ setForm kind ((inner.map (modelNormal laws declaration)).flatMap (deepSplice law)),
        deepSplice law item = [item] := by
      intro item member
      cases kind with
      | vec => exact stable item member
      | hashBag => exact stable item member
      | hashSet =>
        obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp member)
        rw [deepSplice_eq_splice found (normalInner original originalIn).canonical]
        exact splice_canon_stable
          ((deepSplice_eq_splice found (normalInner original originalIn)).symm.trans (stable original originalIn))
    have innerSpliced : deepSplice law (modelNormal laws declaration (.collection kind inner none)) =
        setForm kind ((inner.map (modelNormal laws declaration)).flatMap (deepSplice law)) := by
      rw [modelNormal, found]
      exact deepSplice_wrapFinish kindIs stableForm
    rw [modelNormal, found, modelNormal, found]
    simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, innerSpliced,
      List.append_assoc]
    apply wrapFinish_same
    simp only [List.map_append]
    exact Presents.surround _ _ (setForm_presents kind _)
  | @unit kind law label before after rest found isUnit =>
    unfold Same
    congr 1
    rw [modelNormal, found, modelNormal, found]
    simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons]
    rw [modelNormal, List.map_nil, finish_nil, deepSplice, if_pos isUnit, List.nil_append]
  | apply _ ih => exact context_apply _ ih
  | lambda _ ih => exact context_lambda _ ih
  | multiLambda _ ih => exact context_multiLambda _ _ ih
  | substBody _ ih => exact context_substBody _ ih
  | substReplacement _ ih => exact context_substReplacement _ ih
  | element _ ih => exact context_element _ _ ih

/-- **Every use of `@(*n) = n` keeps the model normal form.** -/
theorem QuoteDropStep.modelNormal_same (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (step : QuoteDropStep declaration left right) :
    Same (modelNormal laws declaration left) (modelNormal laws declaration right) := by
  induction step with
  | collapse name =>
    unfold Same
    congr 1
    have plainDrop : finishNormalizeReflectiveApply declaration declaration.dropConstructor
        [modelNormal laws declaration name] = .apply declaration.dropConstructor [modelNormal laws declaration name] := by
      unfold finishNormalizeReflectiveApply
      rw [if_neg (by simpa using distinct)]
    rw [modelNormal, List.map_cons, List.map_nil, modelNormal, List.map_cons, List.map_nil, plainDrop, finish_drop]
    simp
  | apply _ ih => exact context_apply _ ih
  | lambda _ ih => exact context_lambda _ ih
  | multiLambda _ ih => exact context_multiLambda _ _ ih
  | substBody _ ih => exact context_substBody _ ih
  | substReplacement _ ih => exact context_substReplacement _ ih
  | element _ ih => exact context_element _ _ ih

/-- **Every use of a wrapper law keeps the model normal form.** -/
theorem WrapperStep.modelNormal_same {left right : Pattern} (step : WrapperStep laws left right) :
    Same (modelNormal laws declaration left) (modelNormal laws declaration right) := by
  induction step with
  | @singleton kind law element found =>
    rw [modelNormal, found]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (normal_modelNormal element).rewrap_same found
  | @empty kind law label found isUnit =>
    unfold Same
    congr 1
    have collapsed : modelNormal laws declaration (.collection kind [] none) = wrapFinish law kind [] none := by
      rw [modelNormal, found]; simp only [List.map_nil, List.flatMap_nil, setForm_nil]
    rw [collapsed, modelNormal, List.map_nil, finish_nil]
    simp [wrapFinish, isUnit]
  | apply _ ih => exact context_apply _ ih
  | lambda _ ih => exact context_lambda _ ih
  | multiLambda _ ih => exact context_multiLambda _ _ ih
  | substBody _ ih => exact context_substBody _ ih
  | substReplacement _ ih => exact context_substReplacement _ ih
  | element _ ih => exact context_element _ _ ih

/-- **The model's canonical form**: the model normal form, then sorted unordered collections. -/
def modelCanon (laws : List Laws) (declaration : ReflectivePresentationDecl) (pattern : Pattern) : Pattern :=
  canon (modelNormal laws declaration pattern)

/-- **Every model move keeps the model's canonical form.** -/
theorem ModelMove.modelCanon_eq (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (move : ModelMove laws declaration left right) :
    modelCanon laws declaration left = modelCanon laws declaration right := by
  rcases move with lawMove | quoteDrop | wrapped
  · exact LawStep.modelNormal_same lawMove
  · exact QuoteDropStep.modelNormal_same distinct quoteDrop
  · exact WrapperStep.modelNormal_same wrapped

/-- **The model's canonical form is sound**: every term is related to it by model moves. -/
theorem to_modelCanon (pattern : Pattern) :
    Relation.EqvGen (ModelMove laws declaration) pattern (modelCanon laws declaration pattern) := by
  refine .trans _ _ _ (to_modelNormal pattern) ?_
  exact ofLaws (Relation.EqvGen.mono (fun _ _ step => step.lawStep laws) _ _ (to_canon _))

/-- **The model's canonical form decides the model's law moves.** -/
theorem modelCanon_iff (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (left right : Pattern) :
    modelCanon laws declaration left = modelCanon laws declaration right ↔
      Relation.EqvGen (ModelMove laws declaration) left right := by
  constructor
  · intro same
    have toRight := to_modelCanon (laws := laws) (declaration := declaration) right
    rw [← same] at toRight
    exact .trans _ _ _ (to_modelCanon left) (.symm _ _ toRight)
  · intro related
    induction related with
    | rel _ _ move => exact move.modelCanon_eq distinct
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second

end Mettapedia.OSLF.MeTTaIL.Wrappers
