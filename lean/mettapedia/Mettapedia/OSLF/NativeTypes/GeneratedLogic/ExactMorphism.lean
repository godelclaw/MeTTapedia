import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism

/-!
# Exact morphisms

A bounded morphism carries the forward formulas: what an element reaches forward and how it is built. An **exact
morphism** is a bounded morphism that is also onto, whose image's predecessors come from predecessors, and that
commutes with application under a body (`ExactMorphism`). Along it **every** formula holds at an element exactly when
it holds at its image (`ExactMorphism.sat_iff`): the past modalities and the counting of predecessors go through the
predecessors, the quantifiers over a type through the elements onto which it maps, and the hom formers through the
values onto which it maps.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula NativeStructure

universe u v

/-- **An exact morphism**: a bounded morphism onto the target, whose image's predecessors come from predecessors, and
which commutes with application under a body. -/
structure ExactMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) extends BoundedMorphism S T where
  surjective : Function.Surjective map
  previousBack : ∀ {source' label target}, T.step source' label (map target) →
    ∃ source, S.step source label target ∧ map source = source'
  applyMap : ∀ {element inner}, S.body element inner → ∀ value,
    map (S.apply inner value) = T.apply (map inner) (map value)

namespace ExactMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  (morphism : ExactMorphism S T)

/-- Predecessors of an image come from predecessors of the element, a list at a time. -/
theorem previousesBack {element : Source} {label : StepLabel} : ∀ {sources' : List Target},
    (∀ source' ∈ sources', T.step source' label (morphism.map element)) →
      ∃ sources : List Source, sources.map morphism.map = sources' ∧ ∀ source ∈ sources, S.step source label element
  | [], _ => ⟨[], rfl, fun _ member => nomatch member⟩
  | source' :: sources', steps => by
    obtain ⟨source, step, rfl⟩ := morphism.previousBack (steps source' List.mem_cons_self)
    obtain ⟨sources, same, rest⟩ := previousesBack fun other member => steps other (List.mem_cons_of_mem _ member)
    refine ⟨source :: sources, by rw [List.map_cons, same], fun other member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact step
    · exact rest other member

/-- **Counting predecessors is preserved and reflected.** -/
theorem atLeast_previous_iff {count : ℕ} {element : Source} {label : StepLabel} {holds : Source → Prop}
    {holds' : Target → Prop} (same : ∀ other, holds other ↔ holds' (morphism.map other)) :
    (S.AtLeast count fun other => S.stepIn .backward element label other ∧ holds other) ↔
      T.AtLeast count fun other => T.stepIn .backward (morphism.map element) label other ∧ holds' other := by
  constructor
  · rintro ⟨witnesses, length, distinct, all⟩
    refine ⟨witnesses.map morphism.map, by rw [List.length_map, length],
      List.pairwise_map.mpr (distinct.imp fun differs identified => differs ((morphism.sameIff _ _).mpr identified)), ?_⟩
    intro other member
    obtain ⟨origin, originMember, rfl⟩ := List.mem_map.mp member
    exact ⟨morphism.step (all origin originMember).1, (same origin).mp (all origin originMember).2⟩
  · rintro ⟨witnesses, length, distinct, all⟩
    obtain ⟨sources, mapped, steps⟩ := morphism.previousesBack fun other member => (all other member).1
    subst mapped
    refine ⟨sources, by rw [← length, List.length_map],
      (List.pairwise_map.mp distinct).imp fun differs identified => differs ((morphism.sameIff _ _).mp identified),
      fun other member => ⟨steps other member, (same other).mpr (all _ (List.mem_map_of_mem member)).2⟩⟩

mutual
/-- **Along an exact morphism, every formula holds at an element exactly when it holds at its image.** -/
theorem sat_iff : ∀ {n : ℕ} (formula : Formula n),
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.toBoundedMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element)
  | _, .top, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _ => Iff.rfl
  | _, .and left right, _, _, related, element => by
    exact and_congr (sat_iff left related element) (sat_iff right related element)
  | _, .or left right, _, _, related, element => by
    exact or_congr (sat_iff left related element) (sat_iff right related element)
  | _, .var index, _, _, related, element => related index element
  | _, .mu inner, sourceEnv, targetEnv, related, element => by
    constructor
    · intro holds closed closedHolds
      exact holds (morphism.map ⁻¹' closed) fun other otherHolds =>
        closedHolds _ ((sat_iff inner (related.extend morphism.toBoundedMorphism closed) other).mp otherHolds)
    · intro holds closed closedHolds
      let pushed : Set Target := {image | ∀ origin, morphism.map origin = image → origin ∈ closed}
      have inside : ∀ origin, morphism.map origin ∈ pushed → origin ∈ closed :=
        fun origin member => member origin rfl
      have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
        subst originMaps
        exact closedHolds origin (S.sat_mono inner (sourceEnv.extend_sub fun other member => inside other member) origin
          ((sat_iff inner (related.extend morphism.toBoundedMorphism pushed) origin).mpr imageHolds))
      exact inside element pushedHolds
  | _, .nu inner, sourceEnv, targetEnv, related, element => by
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨morphism.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
      rintro _ ⟨other, otherMember, rfl⟩
      exact (sat_iff inner (related.extend morphism.toBoundedMorphism (morphism.map '' invariant)) other).mp
        (S.sat_mono inner (sourceEnv.extend_sub fun origin inside => Set.mem_image_of_mem morphism.map inside) other
          (preserved other otherMember))
    · rintro ⟨invariant, member, preserved⟩
      exact ⟨morphism.map ⁻¹' invariant, member, fun other otherMember =>
        (sat_iff inner (related.extend morphism.toBoundedMorphism invariant) other).mpr (preserved _ otherMember)⟩
  | _, .possibly _ formula, _, _, related, element => by
    constructor
    · rintro ⟨next, step, holds⟩
      exact ⟨morphism.map next, morphism.step step, (sat_iff formula related next).mp holds⟩
    · rintro ⟨next', step', holds'⟩
      obtain ⟨next, step, rfl⟩ := morphism.stepBack step'
      exact ⟨next, step, (sat_iff formula related next).mpr holds'⟩
  | _, .necessarily _ formula, _, _, related, element => by
    constructor
    · intro every next' step'
      obtain ⟨next, step, rfl⟩ := morphism.stepBack step'
      exact (sat_iff formula related next).mp (every next step)
    · intro every next step
      exact (sat_iff formula related next).mpr (every _ (morphism.step step))
  | _, .atLeast _ .forward _ formula, _, _, related, _ =>
    morphism.toBoundedMorphism.atLeast_steps_iff fun other => sat_iff formula related other
  | _, .allButFewer _ .forward _ formula, _, _, related, _ =>
    not_congr (morphism.toBoundedMorphism.atLeast_steps_iff fun other => not_congr (sat_iff formula related other))
  | _, .built _ arguments, _, _, related, element => by
    constructor
    · rintro ⟨parts, isBuilt, all⟩
      exact ⟨parts.map morphism.map, morphism.built isBuilt, (satAll_iff arguments related parts).mp all⟩
    · rintro ⟨parts', isBuilt', all'⟩
      obtain ⟨parts, isBuilt, rfl⟩ := morphism.builtBack isBuilt'
      exact ⟨parts, isBuilt, (satAll_iff arguments related parts).mpr all'⟩
  | _, .everyBuilt _ arguments, _, _, related, element => by
    constructor
    · intro every parts' isBuilt'
      obtain ⟨parts, isBuilt, rfl⟩ := morphism.builtBack isBuilt'
      exact (satSome_iff arguments related parts).mp (every parts isBuilt)
    · intro every parts isBuilt
      exact (satSome_iff arguments related parts).mpr (every _ (morphism.built isBuilt))
  | _, .split _ left right, _, _, related, element => by
    constructor
    · rintro ⟨first, second, isSplit, firstHolds, secondHolds⟩
      exact ⟨morphism.map first, morphism.map second, morphism.split isSplit,
        (sat_iff left related first).mp firstHolds, (sat_iff right related second).mp secondHolds⟩
    · rintro ⟨first', second', isSplit', firstHolds, secondHolds⟩
      obtain ⟨first, second, isSplit, rfl, rfl⟩ := morphism.splitBack isSplit'
      exact ⟨first, second, isSplit, (sat_iff left related first).mpr firstHolds,
        (sat_iff right related second).mpr secondHolds⟩
  | _, .everySplit _ left right, _, _, related, element => by
    constructor
    · intro every first' second' isSplit'
      obtain ⟨first, second, isSplit, rfl, rfl⟩ := morphism.splitBack isSplit'
      exact (every first second isSplit).imp (sat_iff left related first).mp
        (sat_iff right related second).mp
    · intro every first second isSplit
      exact (every _ _ (morphism.split isSplit)).imp (sat_iff left related first).mpr
        (sat_iff right related second).mpr
  | _, .empty _, _, _, _, element => ⟨fun isEmpty => morphism.empty isEmpty, fun isEmpty => morphism.emptyBack isEmpty⟩
  | _, .nonEmpty _, _, _, _, element =>
    ⟨fun notEmpty isEmpty => notEmpty (morphism.emptyBack isEmpty), fun notEmpty isEmpty => notEmpty (morphism.empty isEmpty)⟩
  | _, .single _ formula, _, _, related, element => by
    constructor
    · rintro ⟨member, isSingle, holds⟩
      exact ⟨morphism.map member, morphism.single isSingle, (sat_iff formula related member).mp holds⟩
    · rintro ⟨member', isSingle', holds'⟩
      obtain ⟨member, isSingle, rfl⟩ := morphism.singleBack isSingle'
      exact ⟨member, isSingle, (sat_iff formula related member).mpr holds'⟩
  | _, .everySingle _ formula, _, _, related, element => by
    constructor
    · intro every member' isSingle'
      obtain ⟨member, isSingle, rfl⟩ := morphism.singleBack isSingle'
      exact (sat_iff formula related member).mp (every member isSingle)
    · intro every member isSingle
      exact (sat_iff formula related member).mpr (every _ (morphism.single isSingle))
  | _, .body formula, _, _, related, element => by
    constructor
    · rintro ⟨inner, isBody, holds⟩
      exact ⟨morphism.map inner, morphism.body isBody, (sat_iff formula related inner).mp holds⟩
    · rintro ⟨inner', isBody', holds'⟩
      obtain ⟨inner, isBody, rfl⟩ := morphism.bodyBack isBody'
      exact ⟨inner, isBody, (sat_iff formula related inner).mpr holds'⟩
  | _, .everyBody formula, _, _, related, element => by
    constructor
    · intro every inner' isBody'
      obtain ⟨inner, isBody, rfl⟩ := morphism.bodyBack isBody'
      exact (sat_iff formula related inner).mp (every inner isBody)
    · intro every inner isBody
      exact (sat_iff formula related inner).mpr (every _ (morphism.body isBody))
  | _, .multiBody _ formula, _, _, related, element => by
    constructor
    · rintro ⟨inner, isBody, holds⟩
      exact ⟨morphism.map inner, morphism.multiBody isBody, (sat_iff formula related inner).mp holds⟩
    · rintro ⟨inner', isBody', holds'⟩
      obtain ⟨inner, isBody, rfl⟩ := morphism.multiBodyBack isBody'
      exact ⟨inner, isBody, (sat_iff formula related inner).mpr holds'⟩
  | _, .everyMultiBody _ formula, _, _, related, element => by
    constructor
    · intro every inner' isBody'
      obtain ⟨inner, isBody, rfl⟩ := morphism.multiBodyBack isBody'
      exact (sat_iff formula related inner).mp (every inner isBody)
    · intro every inner isBody
      exact (sat_iff formula related inner).mpr (every _ (morphism.multiBody isBody))
  | _, .bound _, _, _, _, element => ⟨fun isBound => morphism.bound isBound, fun isBound => morphism.boundBack isBound⟩
  | _, .notBound _, _, _, _, element =>
    ⟨fun notBound isBound => notBound (morphism.boundBack isBound), fun notBound isBound => notBound (morphism.bound isBound)⟩
  | _, .typed _, _, _, _, element => ⟨fun isTyped => morphism.typed isTyped, fun isTyped => morphism.typedBack isTyped⟩
  | _, .untyped _, _, _, _, element =>
    ⟨fun untyped isTyped => untyped (morphism.typedBack isTyped), fun untyped isTyped => untyped (morphism.typed isTyped)⟩
  | _, .is _, _, _, _, element => ⟨fun isNamed => morphism.named isNamed, fun isNamed => morphism.namedBack isNamed⟩
  | _, .isNot _, _, _, _, element =>
    ⟨fun notNamed isNamed => notNamed (morphism.namedBack isNamed), fun notNamed isNamed => notNamed (morphism.named isNamed)⟩
  | _, .sometimeBefore _ formula, _, _, related, element => by
    constructor
    · rintro ⟨previous, step, holds⟩
      exact ⟨morphism.map previous, morphism.step step, (sat_iff formula related previous).mp holds⟩
    · rintro ⟨previous', step', holds'⟩
      obtain ⟨previous, step, rfl⟩ := morphism.previousBack step'
      exact ⟨previous, step, (sat_iff formula related previous).mpr holds'⟩
  | _, .alwaysBefore _ formula, _, _, related, element => by
    constructor
    · intro every previous' step'
      obtain ⟨previous, step, rfl⟩ := morphism.previousBack step'
      exact (sat_iff formula related previous).mp (every previous step)
    · intro every previous step
      exact (sat_iff formula related previous).mpr (every _ (morphism.step step))
  | _, .atLeast _ .backward _ formula, _, _, related, _ =>
    morphism.atLeast_previous_iff fun other => sat_iff formula related other
  | _, .allButFewer _ .backward _ formula, _, _, related, _ =>
    not_congr (morphism.atLeast_previous_iff fun other => not_congr (sat_iff formula related other))
  | _, .someOf _ formula, _, _, related, _ => by
    constructor
    · rintro ⟨witness, isTyped, holds⟩
      exact ⟨morphism.map witness, morphism.typed isTyped, (sat_iff formula related witness).mp holds⟩
    · rintro ⟨witness', isTyped', holds'⟩
      obtain ⟨witness, rfl⟩ := morphism.surjective witness'
      exact ⟨witness, morphism.typedBack isTyped', (sat_iff formula related witness).mpr holds'⟩
  | _, .everyOf _ formula, _, _, related, _ => by
    constructor
    · intro every witness' isTyped'
      obtain ⟨witness, rfl⟩ := morphism.surjective witness'
      exact (sat_iff formula related witness).mp (every witness (morphism.typedBack isTyped'))
    · intro every witness isTyped
      exact (sat_iff formula related witness).mpr (every _ (morphism.typed isTyped))
  | _, .mapsAll argument result, _, _, related, element => by
    constructor
    · rintro ⟨inner, isBody, every⟩
      refine ⟨morphism.map inner, morphism.body isBody, fun value' => ?_⟩
      obtain ⟨value, rfl⟩ := morphism.surjective value'
      rw [← morphism.applyMap isBody value]
      exact (every value).imp (sat_iff argument related value).mp (sat_iff result related _).mp
    · rintro ⟨inner', isBody', every'⟩
      obtain ⟨inner, isBody, rfl⟩ := morphism.bodyBack isBody'
      refine ⟨inner, isBody, fun value => ?_⟩
      have mapped := every' (morphism.map value)
      rw [← morphism.applyMap isBody value] at mapped
      exact mapped.imp (sat_iff argument related value).mpr (sat_iff result related _).mpr
  | _, .mapsSome argument result, _, _, related, element => by
    constructor
    · intro every inner' isBody'
      obtain ⟨inner, isBody, rfl⟩ := morphism.bodyBack isBody'
      obtain ⟨value, argumentHolds, resultHolds⟩ := every inner isBody
      refine ⟨morphism.map value, (sat_iff argument related value).mp argumentHolds, ?_⟩
      rw [← morphism.applyMap isBody value]
      exact (sat_iff result related _).mp resultHolds
    · intro every inner isBody
      obtain ⟨value', argumentHolds, resultHolds⟩ := every _ (morphism.body isBody)
      obtain ⟨value, rfl⟩ := morphism.surjective value'
      rw [← morphism.applyMap isBody value] at resultHolds
      exact ⟨value, (sat_iff argument related value).mpr argumentHolds, (sat_iff result related _).mpr resultHolds⟩

theorem satAll_iff : ∀ {n : ℕ} (formulas : Formulas n),
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.toBoundedMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ parts, S.satAll sourceEnv formulas parts ↔ T.satAll targetEnv formulas (parts.map morphism.map)
  | _, .nil, _, _, _, [] => Iff.rfl
  | _, .nil, _, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, _, _, related, part :: parts => by
    exact and_congr (sat_iff formula related part) (satAll_iff formulas related parts)

theorem satSome_iff : ∀ {n : ℕ} (formulas : Formulas n),
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.toBoundedMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ parts, S.satSome sourceEnv formulas parts ↔ T.satSome targetEnv formulas (parts.map morphism.map)
  | _, .nil, _, _, _, [] => Iff.rfl
  | _, .nil, _, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, _, _, related, part :: parts => by
    exact or_congr (sat_iff formula related part) (satSome_iff formulas related parts)
end

end ExactMorphism

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
