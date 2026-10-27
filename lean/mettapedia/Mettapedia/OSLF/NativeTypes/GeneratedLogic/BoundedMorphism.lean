import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Transfer
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance

/-!
# Bounded morphisms

A homomorphism carries existential formulas forward and universal ones back. A **bounded morphism**
does both for every forward formula: the image's steps and shapes all come from the source.
- Each step, decomposition, split, member and body of an image is the image of one.
- The atoms (emptiness, bound variables, types and names) are reflected.

The forward formulas (`Formula.forward`) leave out the past modalities, the quantifiers over a type and
the hom formers. Each of those reaches beyond what an element reaches forward and how it is built. Along
a bounded morphism a forward formula holds at an element exactly when it holds at its image
(`BoundedMorphism.sat_iff`), fixed points and alternations of ∀ and ∃ included. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula NativeStructure

universe u v

namespace Formula

mutual
/-- **The forward formulas**: no past modalities, no counting of predecessors, no quantifiers over a type,
no hom formers and no context labels. -/
def forward : {n : ℕ} → Formula n → Bool
  | _, .sometimeBefore _ _ | _, .alwaysBefore _ _ | _, .someOf _ _ | _, .everyOf _ _ | _, .mapsAll _ _
  | _, .mapsSome _ _ | _, .atLeast _ .backward _ _ | _, .allButFewer _ .backward _ _ => false
  | _, .atLeast _ .forward label formula | _, .allButFewer _ .forward label formula =>
    !label.isContext && forward formula
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ | _, .inRelation _ | _, .notInRelation _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    forward left && forward right
  | _, .mu inner | _, .nu inner => forward inner
  | _, .possibly label formula | _, .necessarily label formula => !label.isContext && forward formula
  | _, .single _ formula | _, .everySingle _ formula
  | _, .body formula | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula =>
    forward formula
  | _, .built _ arguments | _, .everyBuilt _ arguments => forwardList arguments

/-- Every formula of the list is forward. -/
def forwardList : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => forward formula && forwardList formulas
end

mutual
/-- **The dual of a forward formula is forward.** -/
theorem forward_dual : ∀ {n : ℕ} (formula : Formula n), (dual formula).forward = formula.forward
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ | _, .inRelation _ | _, .notInRelation _
  | _, .sometimeBefore _ _ | _, .alwaysBefore _ _
  | _, .someOf _ _ | _, .everyOf _ _ | _, .mapsAll _ _ | _, .mapsSome _ _ | _, .atLeast _ .backward _ _
  | _, .allButFewer _ .backward _ _ => by simp [dual, forward]
  | _, .atLeast _ .forward _ formula | _, .allButFewer _ .forward _ formula => by
    simp only [dual, forward, forward_dual formula]
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right => by
    simp only [dual, forward, forward_dual left, forward_dual right]
  | _, .mu inner | _, .nu inner => by simp only [dual, forward, forward_dual inner]
  | _, .possibly _ formula | _, .necessarily _ formula => by simp only [dual, forward, forward_dual formula]
  | _, .single _ formula | _, .everySingle _ formula
  | _, .body formula | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula => by
    simp only [dual, forward, forward_dual formula]
  | _, .built _ arguments | _, .everyBuilt _ arguments => by
    simp only [dual, forward, forwardList_dualList arguments]

theorem forwardList_dualList : ∀ {n : ℕ} (formulas : Formulas n), forwardList (dualList formulas) = forwardList formulas
  | _, .nil => rfl
  | _, .cons formula formulas => by
    simp only [dualList, forwardList, forward_dual formula, forwardList_dualList formulas]
end

mutual
/-- **A forward formula has no context labels.** -/
theorem contextFree_of_forward : ∀ {n : ℕ} (formula : Formula n), formula.forward = true → formula.contextFree = true
  | _, .sometimeBefore _ _, forward | _, .alwaysBefore _ _, forward | _, .someOf _ _, forward
  | _, .everyOf _ _, forward | _, .mapsAll _ _, forward | _, .mapsSome _ _, forward
  | _, .atLeast _ .backward _ _, forward | _, .allButFewer _ .backward _ _, forward => by
    simp [Formula.forward] at forward
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .empty _, _ | _, .nonEmpty _, _ | _, .bound _, _
  | _, .notBound _, _ | _, .typed _, _ | _, .untyped _, _ | _, .is _, _ | _, .isNot _, _ | _, .inRelation _, _
  | _, .notInRelation _, _ => rfl
  | _, .atLeast _ .forward _ formula, forward | _, .allButFewer _ .forward _ formula, forward
  | _, .possibly _ formula, forward | _, .necessarily _ formula, forward => by
    simp only [Formula.forward, contextFree, Bool.and_eq_true] at forward ⊢
    exact ⟨forward.1, contextFree_of_forward formula forward.2⟩
  | _, .and left right, forward | _, .or left right, forward | _, .split _ left right, forward
  | _, .everySplit _ left right, forward => by
    simp only [Formula.forward, contextFree, Bool.and_eq_true] at forward ⊢
    exact ⟨contextFree_of_forward left forward.1, contextFree_of_forward right forward.2⟩
  | _, .mu inner, forward | _, .nu inner, forward => by
    simp only [Formula.forward, contextFree] at forward ⊢
    exact contextFree_of_forward inner forward
  | _, .single _ formula, forward | _, .everySingle _ formula, forward | _, .body formula, forward
  | _, .everyBody formula, forward | _, .multiBody _ formula, forward | _, .everyMultiBody _ formula, forward => by
    simp only [Formula.forward, contextFree] at forward ⊢
    exact contextFree_of_forward formula forward
  | _, .built _ arguments, forward | _, .everyBuilt _ arguments, forward => by
    simp only [Formula.forward, contextFree] at forward ⊢
    exact contextFreeList_of_forwardList arguments forward

theorem contextFreeList_of_forwardList : ∀ {n : ℕ} (formulas : Formulas n), forwardList formulas = true →
    contextFreeList formulas = true
  | _, .nil, _ => rfl
  | _, .cons formula formulas, forward => by
    simp only [forwardList, contextFreeList, Bool.and_eq_true] at forward ⊢
    exact ⟨contextFree_of_forward formula forward.1, contextFreeList_of_forwardList formulas forward.2⟩
end

end Formula

/-- **A bounded morphism**: a homomorphism under which the image's steps and shapes all come from the
source, and the atoms are reflected. -/
structure BoundedMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) extends Hom S T where
  stepBack : ∀ {source label target'}, label.isContext = false → T.step (map source) label target' →
    ∃ target, S.step source label target ∧ map target = target'
  builtBack : ∀ {element constructor parts'}, T.built (map element) constructor parts' →
    ∃ parts, S.built element constructor parts ∧ parts.map map = parts'
  splitBack : ∀ {element kind first' second'}, T.split (map element) kind first' second' →
    ∃ first second, S.split element kind first second ∧ map first = first' ∧ map second = second'
  emptyBack : ∀ {element kind}, T.empty (map element) kind → S.empty element kind
  singleBack : ∀ {element kind member'}, T.single (map element) kind member' →
    ∃ member, S.single element kind member ∧ map member = member'
  bodyBack : ∀ {element inner'}, T.body (map element) inner' → ∃ inner, S.body element inner ∧ map inner = inner'
  multiBodyBack : ∀ {element arity inner'}, T.multiBody (map element) arity inner' →
    ∃ inner, S.multiBody element arity inner ∧ map inner = inner'
  boundBack : ∀ {element index}, T.bound (map element) index → S.bound element index
  typedBack : ∀ {element type}, T.typed (map element) type → S.typed element type
  namedBack : ∀ {element term}, T.named (map element) term → S.named element term
  inRelationBack : ∀ {element relation}, T.inRelation (map element) relation → S.inRelation element relation
  /-- The map preserves and reflects identity, so it keeps counts. -/
  sameIff : ∀ first second, S.same first second ↔ T.same (map first) (map second)

namespace BoundedMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  (morphism : BoundedMorphism S T)

/-- Environments related by preimage: the source's sets are the preimages of the target's. -/
def EnvPreimage {n : ℕ} (sourceEnv : Env Source n) (targetEnv : Env Target n) : Prop :=
  ∀ index element, element ∈ sourceEnv index ↔ morphism.map element ∈ targetEnv index

theorem EnvPreimage.extend {n : ℕ} {sourceEnv : Env Source n} {targetEnv : Env Target n}
    (related : morphism.EnvPreimage sourceEnv targetEnv) (set : Set Target) :
    morphism.EnvPreimage (sourceEnv.extend (morphism.map ⁻¹' set)) (targetEnv.extend set) := by
  intro index element
  refine Fin.cases ?_ (fun index' => ?_) index
  · exact Iff.rfl
  · exact related index' element

theorem envPreimage_closed : morphism.EnvPreimage Env.closed Env.closed := fun index => index.elim0

/-- Steps from an image come from steps from the element, a list at a time. -/
theorem stepsBack {element : Source} {label : StepLabel} (own : label.isContext = false) : ∀ {targets : List Target},
    (∀ target ∈ targets, T.step (morphism.map element) label target) →
      ∃ sources : List Source, sources.map morphism.map = targets ∧ ∀ source ∈ sources, S.step element label source
  | [], _ => ⟨[], rfl, fun _ member => nomatch member⟩
  | target :: targets, steps => by
    obtain ⟨source, step, rfl⟩ := morphism.stepBack own (steps target List.mem_cons_self)
    obtain ⟨sources, same, rest⟩ := stepsBack own fun other member => steps other (List.mem_cons_of_mem _ member)
    refine ⟨source :: sources, by rw [List.map_cons, same], fun other member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact step
    · exact rest other member

/-- **Counting steps is preserved and reflected.** -/
theorem atLeast_steps_iff {count : ℕ} {element : Source} {label : StepLabel} (own : label.isContext = false)
    {holds : Source → Prop}
    {holds' : Target → Prop} (same : ∀ other, holds other ↔ holds' (morphism.map other)) :
    (S.AtLeast count fun other => S.step element label other ∧ holds other) ↔
      T.AtLeast count fun other => T.step (morphism.map element) label other ∧ holds' other := by
  constructor
  · rintro ⟨witnesses, length, distinct, all⟩
    refine ⟨witnesses.map morphism.map, by rw [List.length_map, length],
      List.pairwise_map.mpr (distinct.imp fun differs identified => differs ((morphism.sameIff _ _).mpr identified)), ?_⟩
    intro other member
    obtain ⟨origin, originMember, rfl⟩ := List.mem_map.mp member
    exact ⟨morphism.step own (all origin originMember).1, (same origin).mp (all origin originMember).2⟩
  · rintro ⟨witnesses, length, distinct, all⟩
    obtain ⟨sources, mapped, steps⟩ := morphism.stepsBack own fun other member => (all other member).1
    subst mapped
    refine ⟨sources, by rw [← length, List.length_map],
      (List.pairwise_map.mp distinct).imp fun differs identified => differs ((morphism.sameIff _ _).mp identified),
      fun other member => ⟨steps other member, (same other).mpr (all _ (List.mem_map_of_mem member)).2⟩⟩

mutual
/-- **Along a bounded morphism, a forward formula holds at an element exactly when it holds at its
image.** -/
theorem sat_iff : ∀ {n : ℕ} (formula : Formula n), formula.forward = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.EnvPreimage sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element)
  | _, .top, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _ => Iff.rfl
  | _, .and left right, forward, _, _, related, element => by
    simp only [Formula.forward, Bool.and_eq_true] at forward
    exact and_congr (sat_iff left forward.1 related element) (sat_iff right forward.2 related element)
  | _, .or left right, forward, _, _, related, element => by
    simp only [Formula.forward, Bool.and_eq_true] at forward
    exact or_congr (sat_iff left forward.1 related element) (sat_iff right forward.2 related element)
  | _, .var index, _, _, _, related, element => related index element
  | _, .mu inner, forward, sourceEnv, targetEnv, related, element => by
    constructor
    · intro holds closed closedHolds
      exact holds (morphism.map ⁻¹' closed) fun other otherHolds =>
        closedHolds _ ((sat_iff inner forward (related.extend morphism closed) other).mp otherHolds)
    · intro holds closed closedHolds
      let pushed : Set Target := {image | ∀ origin, morphism.map origin = image → origin ∈ closed}
      have inside : ∀ origin, morphism.map origin ∈ pushed → origin ∈ closed :=
        fun origin member => member origin rfl
      have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
        subst originMaps
        exact closedHolds origin (S.sat_mono inner (sourceEnv.extend_sub fun other member => inside other member) origin
          ((sat_iff inner forward (related.extend morphism pushed) origin).mpr imageHolds))
      exact inside element pushedHolds
  | _, .nu inner, forward, sourceEnv, targetEnv, related, element => by
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨morphism.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
      rintro _ ⟨other, otherMember, rfl⟩
      exact (sat_iff inner forward (related.extend morphism (morphism.map '' invariant)) other).mp
        (S.sat_mono inner (sourceEnv.extend_sub fun origin inside => Set.mem_image_of_mem morphism.map inside) other
          (preserved other otherMember))
    · rintro ⟨invariant, member, preserved⟩
      exact ⟨morphism.map ⁻¹' invariant, member, fun other otherMember =>
        (sat_iff inner forward (related.extend morphism invariant) other).mpr (preserved _ otherMember)⟩
  | _, .possibly _ formula, forward, _, _, related, element => by
    simp only [Formula.forward, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at forward
    obtain ⟨own, forward⟩ := forward
    constructor
    · rintro ⟨next, step, holds⟩
      exact ⟨morphism.map next, morphism.step own step, (sat_iff formula forward related next).mp holds⟩
    · rintro ⟨next', step', holds'⟩
      obtain ⟨next, step, rfl⟩ := morphism.stepBack own step'
      exact ⟨next, step, (sat_iff formula forward related next).mpr holds'⟩
  | _, .necessarily _ formula, forward, _, _, related, element => by
    simp only [Formula.forward, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at forward
    obtain ⟨own, forward⟩ := forward
    constructor
    · intro every next' step'
      obtain ⟨next, step, rfl⟩ := morphism.stepBack own step'
      exact (sat_iff formula forward related next).mp (every next step)
    · intro every next step
      exact (sat_iff formula forward related next).mpr (every _ (morphism.step own step))
  | _, .atLeast _ .forward _ formula, forward, _, _, related, _ => by
    simp only [Formula.forward, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at forward
    exact morphism.atLeast_steps_iff forward.1 fun other => sat_iff formula forward.2 related other
  | _, .allButFewer _ .forward _ formula, forward, _, _, related, _ => by
    simp only [Formula.forward, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at forward
    exact not_congr (morphism.atLeast_steps_iff forward.1 fun other =>
      not_congr (sat_iff formula forward.2 related other))
  | _, .built _ arguments, forward, _, _, related, element => by
    constructor
    · rintro ⟨parts, isBuilt, all⟩
      exact ⟨parts.map morphism.map, morphism.built isBuilt, (satAll_iff arguments forward related parts).mp all⟩
    · rintro ⟨parts', isBuilt', all'⟩
      obtain ⟨parts, isBuilt, rfl⟩ := morphism.builtBack isBuilt'
      exact ⟨parts, isBuilt, (satAll_iff arguments forward related parts).mpr all'⟩
  | _, .everyBuilt _ arguments, forward, _, _, related, element => by
    constructor
    · intro every parts' isBuilt'
      obtain ⟨parts, isBuilt, rfl⟩ := morphism.builtBack isBuilt'
      exact (satSome_iff arguments forward related parts).mp (every parts isBuilt)
    · intro every parts isBuilt
      exact (satSome_iff arguments forward related parts).mpr (every _ (morphism.built isBuilt))
  | _, .split _ left right, forward, _, _, related, element => by
    simp only [Formula.forward, Bool.and_eq_true] at forward
    constructor
    · rintro ⟨first, second, isSplit, firstHolds, secondHolds⟩
      exact ⟨morphism.map first, morphism.map second, morphism.split isSplit,
        (sat_iff left forward.1 related first).mp firstHolds, (sat_iff right forward.2 related second).mp secondHolds⟩
    · rintro ⟨first', second', isSplit', firstHolds, secondHolds⟩
      obtain ⟨first, second, isSplit, rfl, rfl⟩ := morphism.splitBack isSplit'
      exact ⟨first, second, isSplit, (sat_iff left forward.1 related first).mpr firstHolds,
        (sat_iff right forward.2 related second).mpr secondHolds⟩
  | _, .everySplit _ left right, forward, _, _, related, element => by
    simp only [Formula.forward, Bool.and_eq_true] at forward
    constructor
    · intro every first' second' isSplit'
      obtain ⟨first, second, isSplit, rfl, rfl⟩ := morphism.splitBack isSplit'
      exact (every first second isSplit).imp (sat_iff left forward.1 related first).mp
        (sat_iff right forward.2 related second).mp
    · intro every first second isSplit
      exact (every _ _ (morphism.split isSplit)).imp (sat_iff left forward.1 related first).mpr
        (sat_iff right forward.2 related second).mpr
  | _, .empty _, _, _, _, _, element => ⟨fun isEmpty => morphism.empty isEmpty, fun isEmpty => morphism.emptyBack isEmpty⟩
  | _, .nonEmpty _, _, _, _, _, element =>
    ⟨fun notEmpty isEmpty => notEmpty (morphism.emptyBack isEmpty), fun notEmpty isEmpty => notEmpty (morphism.empty isEmpty)⟩
  | _, .single _ formula, forward, _, _, related, element => by
    constructor
    · rintro ⟨member, isSingle, holds⟩
      exact ⟨morphism.map member, morphism.single isSingle, (sat_iff formula forward related member).mp holds⟩
    · rintro ⟨member', isSingle', holds'⟩
      obtain ⟨member, isSingle, rfl⟩ := morphism.singleBack isSingle'
      exact ⟨member, isSingle, (sat_iff formula forward related member).mpr holds'⟩
  | _, .everySingle _ formula, forward, _, _, related, element => by
    constructor
    · intro every member' isSingle'
      obtain ⟨member, isSingle, rfl⟩ := morphism.singleBack isSingle'
      exact (sat_iff formula forward related member).mp (every member isSingle)
    · intro every member isSingle
      exact (sat_iff formula forward related member).mpr (every _ (morphism.single isSingle))
  | _, .body formula, forward, _, _, related, element => by
    constructor
    · rintro ⟨inner, isBody, holds⟩
      exact ⟨morphism.map inner, morphism.body isBody, (sat_iff formula forward related inner).mp holds⟩
    · rintro ⟨inner', isBody', holds'⟩
      obtain ⟨inner, isBody, rfl⟩ := morphism.bodyBack isBody'
      exact ⟨inner, isBody, (sat_iff formula forward related inner).mpr holds'⟩
  | _, .everyBody formula, forward, _, _, related, element => by
    constructor
    · intro every inner' isBody'
      obtain ⟨inner, isBody, rfl⟩ := morphism.bodyBack isBody'
      exact (sat_iff formula forward related inner).mp (every inner isBody)
    · intro every inner isBody
      exact (sat_iff formula forward related inner).mpr (every _ (morphism.body isBody))
  | _, .multiBody _ formula, forward, _, _, related, element => by
    constructor
    · rintro ⟨inner, isBody, holds⟩
      exact ⟨morphism.map inner, morphism.multiBody isBody, (sat_iff formula forward related inner).mp holds⟩
    · rintro ⟨inner', isBody', holds'⟩
      obtain ⟨inner, isBody, rfl⟩ := morphism.multiBodyBack isBody'
      exact ⟨inner, isBody, (sat_iff formula forward related inner).mpr holds'⟩
  | _, .everyMultiBody _ formula, forward, _, _, related, element => by
    constructor
    · intro every inner' isBody'
      obtain ⟨inner, isBody, rfl⟩ := morphism.multiBodyBack isBody'
      exact (sat_iff formula forward related inner).mp (every inner isBody)
    · intro every inner isBody
      exact (sat_iff formula forward related inner).mpr (every _ (morphism.multiBody isBody))
  | _, .bound _, _, _, _, _, element => ⟨fun isBound => morphism.bound isBound, fun isBound => morphism.boundBack isBound⟩
  | _, .notBound _, _, _, _, _, element =>
    ⟨fun notBound isBound => notBound (morphism.boundBack isBound), fun notBound isBound => notBound (morphism.bound isBound)⟩
  | _, .typed _, _, _, _, _, element => ⟨fun isTyped => morphism.typed isTyped, fun isTyped => morphism.typedBack isTyped⟩
  | _, .untyped _, _, _, _, _, element =>
    ⟨fun untyped isTyped => untyped (morphism.typedBack isTyped), fun untyped isTyped => untyped (morphism.typed isTyped)⟩
  | _, .is _, _, _, _, _, element => ⟨fun isNamed => morphism.named isNamed, fun isNamed => morphism.namedBack isNamed⟩
  | _, .isNot _, _, _, _, _, element =>
    ⟨fun notNamed isNamed => notNamed (morphism.namedBack isNamed), fun notNamed isNamed => notNamed (morphism.named isNamed)⟩
  | _, .inRelation _, _, _, _, _, element =>
    ⟨fun isIn => morphism.inRelation isIn, fun isIn => morphism.inRelationBack isIn⟩
  | _, .notInRelation _, _, _, _, _, element =>
    ⟨fun notIn isIn => notIn (morphism.inRelationBack isIn), fun notIn isIn => notIn (morphism.inRelation isIn)⟩
  | _, .sometimeBefore _ _, forward, _, _, _, _ | _, .alwaysBefore _ _, forward, _, _, _, _
  | _, .someOf _ _, forward, _, _, _, _ | _, .everyOf _ _, forward, _, _, _, _
  | _, .mapsAll _ _, forward, _, _, _, _ | _, .mapsSome _ _, forward, _, _, _, _
  | _, .atLeast _ .backward _ _, forward, _, _, _, _ | _, .allButFewer _ .backward _ _, forward, _, _, _, _ => by
    simp [Formula.forward] at forward

theorem satAll_iff : ∀ {n : ℕ} (formulas : Formulas n), Formula.forwardList formulas = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.EnvPreimage sourceEnv targetEnv →
      ∀ parts, S.satAll sourceEnv formulas parts ↔ T.satAll targetEnv formulas (parts.map morphism.map)
  | _, .nil, _, _, _, _, [] => Iff.rfl
  | _, .nil, _, _, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, forward, _, _, related, part :: parts => by
    simp only [Formula.forwardList, Bool.and_eq_true] at forward
    exact and_congr (sat_iff formula forward.1 related part) (satAll_iff formulas forward.2 related parts)

theorem satSome_iff : ∀ {n : ℕ} (formulas : Formulas n), Formula.forwardList formulas = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.EnvPreimage sourceEnv targetEnv →
      ∀ parts, S.satSome sourceEnv formulas parts ↔ T.satSome targetEnv formulas (parts.map morphism.map)
  | _, .nil, _, _, _, _, [] => Iff.rfl
  | _, .nil, _, _, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, forward, _, _, related, part :: parts => by
    simp only [Formula.forwardList, Bool.and_eq_true] at forward
    exact or_congr (sat_iff formula forward.1 related part) (satSome_iff formulas forward.2 related parts)
end

/-- **The identity is a bounded morphism.** -/
def identity (S : NativeStructure Source) : BoundedMorphism S S where
  map := id
  step := fun _ stepped => stepped
  built := fun {_ _ parts} held => by rw [List.map_id]; exact held
  split := id
  empty := id
  single := id
  body := id
  multiBody := id
  bound := id
  typed := id
  named := id
  inRelation := id
  stepBack := fun {_ _ target} _ stepped => ⟨target, stepped, rfl⟩
  builtBack := fun {_ _ parts} held => ⟨parts, held, List.map_id _⟩
  splitBack := fun {_ _ first second} held => ⟨first, second, held, rfl, rfl⟩
  emptyBack := id
  singleBack := fun {_ _ member} held => ⟨member, held, rfl⟩
  bodyBack := fun {_ inner} held => ⟨inner, held, rfl⟩
  multiBodyBack := fun {_ _ inner} held => ⟨inner, held, rfl⟩
  boundBack := id
  typedBack := id
  namedBack := id
  inRelationBack := id
  sameIff := fun _ _ => Iff.rfl

end BoundedMorphism

/-! ## Generated substructures -/

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier) (P : Carrier → Prop)

/-- **A generated set of elements**: closed under its elements' own steps, and under taking the parts, the members and the bodies
of its elements and applying its bodies. -/
structure Generated : Prop where
  step : ∀ {source label target}, label.isContext = false → P source → S.step source label target → P target
  built : ∀ {element constructor parts}, P element → S.built element constructor parts → ∀ part ∈ parts, P part
  split : ∀ {element kind first second}, P element → S.split element kind first second → P first ∧ P second
  single : ∀ {element kind member}, P element → S.single element kind member → P member
  body : ∀ {element inner}, P element → S.body element inner → P inner
  multiBody : ∀ {element arity inner}, P element → S.multiBody element arity inner → P inner
  apply : ∀ {inner argument}, P inner → P argument → P (S.apply inner argument)

variable {S P}

/-- **The substructure on a generated set**: the relations among its elements. -/
def restrict (generated : S.Generated P) : NativeStructure {element // P element} where
  step source label target := S.step source.1 label target.1
  built element constructor parts := S.built element.1 constructor (parts.map Subtype.val)
  split element kind first second := S.split element.1 kind first.1 second.1
  empty element kind := S.empty element.1 kind
  single element kind member := S.single element.1 kind member.1
  body element inner := S.body element.1 inner.1
  multiBody element arity inner := S.multiBody element.1 arity inner.1
  bound element index := S.bound element.1 index
  typed element type := S.typed element.1 type
  named element term := S.named element.1 term
  same first second := S.same first.1 second.1
  apply inner argument := ⟨S.apply inner.1 argument.1, generated.apply inner.2 argument.2⟩
  inRelation element relation := S.inRelation element.1 relation

/-- **The inclusion of a generated substructure is a bounded morphism**: everything an element reaches forward
stays in the set, so a forward formula holds in the substructure exactly where it holds in the whole. -/
def Generated.inclusion (generated : S.Generated P) : BoundedMorphism (restrict generated) S where
  map := Subtype.val
  step _ holds := holds
  built holds := holds
  split holds := holds
  empty holds := holds
  single holds := holds
  body holds := holds
  multiBody holds := holds
  bound holds := holds
  typed holds := holds
  named holds := holds
  inRelation holds := holds
  stepBack {source _ target} own step := ⟨⟨target, generated.step own source.2 step⟩, step, rfl⟩
  builtBack {element _ parts} built := by
    have same : (parts.attach.map fun part => (⟨part.1, generated.built element.2 built part.1 part.2⟩ :
        {element // P element})).map Subtype.val = parts := by
      simp [List.map_map, Function.comp_def]
    refine ⟨parts.attach.map fun part => ⟨part.1, generated.built element.2 built part.1 part.2⟩, ?_, same⟩
    show S.built element.1 _ _
    rw [same]
    exact built
  splitBack {element _ first second} split :=
    ⟨⟨first, (generated.split element.2 split).1⟩, ⟨second, (generated.split element.2 split).2⟩, split, rfl, rfl⟩
  emptyBack holds := holds
  singleBack {element _ member} single := ⟨⟨member, generated.single element.2 single⟩, single, rfl⟩
  bodyBack {element inner} body := ⟨⟨inner, generated.body element.2 body⟩, body, rfl⟩
  multiBodyBack {element _ inner} body := ⟨⟨inner, generated.multiBody element.2 body⟩, body, rfl⟩
  boundBack holds := holds
  typedBack holds := holds
  namedBack holds := holds
  inRelationBack holds := holds
  sameIff _ _ := Iff.rfl

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
