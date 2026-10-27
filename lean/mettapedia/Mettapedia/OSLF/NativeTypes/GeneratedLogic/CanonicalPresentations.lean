import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Constructor presentations at the front door, for languages with canonical forms

A closed canonical region decides behavioural formulas, and a parts region adds splits. A constructor former looks at
the ways a term is built: modulo equations, a term may be built by a constructor from many argument lists, or from none
although its canonical form is built otherwise. A region that is to decide constructor formers must hold the canonical
forms of the arguments of every presentation of its terms, and must know their types. This works through one more
contract on canonical forms.

- **The fragment** (`Formula.presentedIn`): the behavioural formulas over admitted labels, with splits, emptiness,
  constructor formers and every-built formers, and types among admitted ones.
- **Presentation morphisms** (`PresentationMorphism`): label morphisms whose splits and constructor presentations go
  forward and come back, and that preserve and reflect emptiness and the admitted types. Along one, every formula of
  the fragment is preserved and reflected (`PresentationMorphism.sat_iff`).
- **The contract** (`PresentationListing`): a listing of parts, and at each admitted canonical term the argument lists
  of its presentations by each constructor up to canonical form, complete and sound, with admitted arguments; and a
  test of the admitted types.
- **The canonical structure with presentations** (`canonicalPresentedStructure`). Taking canonical forms is a
  presentation morphism onto it from what a term reaches by steps, parts and arguments (`canonPresentedMorphism`).
- **A closed presentation region** (`presentedRegion`): a closed parts region that also holds the listed arguments of
  its terms. Its inclusion is a presentation morphism (`presentedRegionMorphism`), so the finite evaluator's verdict on
  it is exact (`presented_check_iff`); `decidePresented` grows such a region from a term (`decidePresented_sound`) and
  `presentedDecider` is a certified decider for the front door.
- **Equation-free languages** list the arguments of a term's head (`identityPresentations`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)

universe u v

/-! ## The fragment -/

namespace Formula

mutual
/-- **Presented formulas** over admitted labels and types: the forward behavioural formulas over the labels, with
splits, every-splits, emptiness, constructor formers, every-built formers, and the admitted types. -/
def presentedIn (labels : StepLabel → Bool) (types : TypeExpr → Bool) : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ | _, .empty _ | _, .nonEmpty _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    presentedIn labels types left && presentedIn labels types right
  | _, .mu inner | _, .nu inner => presentedIn labels types inner
  | _, .possibly label formula | _, .necessarily label formula => label.admittedBy labels && presentedIn labels types formula
  | _, .atLeast _ .forward label formula | _, .allButFewer _ .forward label formula =>
    label.admittedBy labels && presentedIn labels types formula
  | _, .built _ arguments | _, .everyBuilt _ arguments => presentedAllIn labels types arguments
  | _, .typed type | _, .untyped type => types type
  | _, _ => false

/-- Every formula of a list is presented. -/
def presentedAllIn (labels : StepLabel → Bool) (types : TypeExpr → Bool) : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => presentedIn labels types formula && presentedAllIn labels types formulas
end

end Formula

/-! ## Presentation morphisms -/

/-- **A presentation morphism** on admitted labels and types: a label morphism whose splits and constructor
presentations go forward and come back, and that preserves and reflects emptiness and the admitted types. -/
structure PresentationMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) (labels : StepLabel → Bool) (types : TypeExpr → Bool)
    extends LabelMorphism S T labels where
  split : ∀ {element kind first second}, S.split element kind first second →
    T.split (map element) kind (map first) (map second)
  splitBack : ∀ {element kind first' second'}, T.split (map element) kind first' second' →
    ∃ first second, S.split element kind first second ∧ map first = first' ∧ map second = second'
  emptyIff : ∀ element kind, S.empty element kind ↔ T.empty (map element) kind
  built : ∀ {element constructor parts}, S.built element constructor parts →
    T.built (map element) constructor (parts.map map)
  builtBack : ∀ {element constructor parts'}, T.built (map element) constructor parts' →
    ∃ parts, S.built element constructor parts ∧ parts.map map = parts'
  typedIff : ∀ element {type}, types type = true → (S.typed element type ↔ T.typed (map element) type)

namespace PresentationMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  {labels : StepLabel → Bool} {types : TypeExpr → Bool} (morphism : PresentationMorphism S T labels types)

mutual
/-- **Along a presentation morphism, a presented formula holds at an element exactly when it holds at its
image.** -/
theorem sat_iff : ∀ {n : ℕ} (formula : Formula n), formula.presentedIn labels types = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n},
      morphism.toLabelMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element)
  | _, .top, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _ => Iff.rfl
  | _, .and left right, fragment, _, _, related, element => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    exact and_congr (sat_iff left fragment.1 related element) (sat_iff right fragment.2 related element)
  | _, .or left right, fragment, _, _, related, element => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    exact or_congr (sat_iff left fragment.1 related element) (sat_iff right fragment.2 related element)
  | _, .var index, _, _, _, related, element => related index element
  | _, .mu inner, fragment, sourceEnv, targetEnv, related, element => by
    simp only [Formula.presentedIn] at fragment
    constructor
    · intro holds closed closedHolds
      exact holds (morphism.map ⁻¹' closed) fun other otherHolds =>
        closedHolds _ ((sat_iff inner fragment (related.extend morphism.toLabelMorphism closed) other).mp otherHolds)
    · intro holds closed closedHolds
      let pushed : Set Target := {image | ∀ origin, morphism.map origin = image → origin ∈ closed}
      have inside : ∀ origin, morphism.map origin ∈ pushed → origin ∈ closed :=
        fun origin member => member origin rfl
      have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
        subst originMaps
        exact closedHolds origin (S.sat_mono inner (sourceEnv.extend_sub fun other member => inside other member) origin
          ((sat_iff inner fragment (related.extend morphism.toLabelMorphism pushed) origin).mpr imageHolds))
      exact inside element pushedHolds
  | _, .nu inner, fragment, sourceEnv, targetEnv, related, element => by
    simp only [Formula.presentedIn] at fragment
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨morphism.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
      rintro _ ⟨other, otherMember, rfl⟩
      exact (sat_iff inner fragment (related.extend morphism.toLabelMorphism (morphism.map '' invariant)) other).mp
        (S.sat_mono inner (sourceEnv.extend_sub fun origin inside => Set.mem_image_of_mem morphism.map inside) other
          (preserved other otherMember))
    · rintro ⟨invariant, member, preserved⟩
      exact ⟨morphism.map ⁻¹' invariant, member, fun other otherMember =>
        (sat_iff inner fragment (related.extend morphism.toLabelMorphism invariant) other).mpr
          (preserved _ otherMember)⟩
  | _, .possibly _ formula, fragment, _, _, related, element => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    constructor
    · rintro ⟨next, step, holds⟩
      exact ⟨morphism.map next, morphism.step fragment.1 step, (sat_iff formula fragment.2 related next).mp holds⟩
    · rintro ⟨next', step', holds'⟩
      obtain ⟨next, step, rfl⟩ := morphism.stepBack fragment.1 step'
      exact ⟨next, step, (sat_iff formula fragment.2 related next).mpr holds'⟩
  | _, .necessarily _ formula, fragment, _, _, related, element => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    constructor
    · intro every next' step'
      obtain ⟨next, step, rfl⟩ := morphism.stepBack fragment.1 step'
      exact (sat_iff formula fragment.2 related next).mp (every next step)
    · intro every next step
      exact (sat_iff formula fragment.2 related next).mpr (every _ (morphism.step fragment.1 step))
  | _, .atLeast _ .forward _ formula, fragment, _, _, related, _ => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    exact morphism.toLabelMorphism.atLeast_steps_iff fragment.1 fun other => sat_iff formula fragment.2 related other
  | _, .allButFewer _ .forward _ formula, fragment, _, _, related, _ => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    exact not_congr (morphism.toLabelMorphism.atLeast_steps_iff fragment.1 fun other =>
      not_congr (sat_iff formula fragment.2 related other))
  | _, .split _ left right, fragment, _, _, related, element => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    constructor
    · rintro ⟨first, second, split, leftHolds, rightHolds⟩
      exact ⟨morphism.map first, morphism.map second, morphism.split split,
        (sat_iff left fragment.1 related first).mp leftHolds, (sat_iff right fragment.2 related second).mp rightHolds⟩
    · rintro ⟨first', second', split', leftHolds, rightHolds⟩
      obtain ⟨first, second, split, rfl, rfl⟩ := morphism.splitBack split'
      exact ⟨first, second, split, (sat_iff left fragment.1 related first).mpr leftHolds,
        (sat_iff right fragment.2 related second).mpr rightHolds⟩
  | _, .everySplit _ left right, fragment, _, _, related, element => by
    simp only [Formula.presentedIn, Bool.and_eq_true] at fragment
    constructor
    · intro every first' second' split'
      obtain ⟨first, second, split, rfl, rfl⟩ := morphism.splitBack split'
      exact (every first second split).imp (sat_iff left fragment.1 related first).mp
        (sat_iff right fragment.2 related second).mp
    · intro every first second split
      exact (every _ _ (morphism.split split)).imp (sat_iff left fragment.1 related first).mpr
        (sat_iff right fragment.2 related second).mpr
  | _, .empty kind, _, _, _, _, element => morphism.emptyIff element kind
  | _, .nonEmpty kind, _, _, _, _, element => not_congr (morphism.emptyIff element kind)
  | _, .built _ arguments, fragment, _, _, related, element => by
    simp only [Formula.presentedIn] at fragment
    constructor
    · rintro ⟨parts, built, holds⟩
      exact ⟨parts.map morphism.map, morphism.built built, (satAll_iff arguments fragment related parts).mp holds⟩
    · rintro ⟨parts', built', holds'⟩
      obtain ⟨parts, built, rfl⟩ := morphism.builtBack built'
      exact ⟨parts, built, (satAll_iff arguments fragment related parts).mpr holds'⟩
  | _, .everyBuilt _ arguments, fragment, _, _, related, element => by
    simp only [Formula.presentedIn] at fragment
    constructor
    · intro every parts' built'
      obtain ⟨parts, built, rfl⟩ := morphism.builtBack built'
      exact (satSome_iff arguments fragment related parts).mp (every parts built)
    · intro every parts built
      exact (satSome_iff arguments fragment related parts).mpr (every _ (morphism.built built))
  | _, .typed _, fragment, _, _, _, element => by
    simp only [Formula.presentedIn] at fragment
    exact morphism.typedIff element fragment
  | _, .untyped _, fragment, _, _, _, element => by
    simp only [Formula.presentedIn] at fragment
    exact not_congr (morphism.typedIff element fragment)
  | _, .is term, _, _, _, _, element => morphism.namedIff element term
  | _, .isNot term, _, _, _, _, element => not_congr (morphism.namedIff element term)
  | _, .sometimeBefore _ _, fragment, _, _, _, _ | _, .alwaysBefore _ _, fragment, _, _, _, _
  | _, .atLeast _ .backward _ _, fragment, _, _, _, _ | _, .allButFewer _ .backward _ _, fragment, _, _, _, _
  | _, .single _ _, fragment, _, _, _, _ | _, .everySingle _ _, fragment, _, _, _, _
  | _, .body _, fragment, _, _, _, _ | _, .everyBody _, fragment, _, _, _, _
  | _, .multiBody _ _, fragment, _, _, _, _ | _, .everyMultiBody _ _, fragment, _, _, _, _
  | _, .bound _, fragment, _, _, _, _ | _, .notBound _, fragment, _, _, _, _
  | _, .mapsAll _ _, fragment, _, _, _, _ | _, .mapsSome _ _, fragment, _, _, _, _
  | _, .someOf _ _, fragment, _, _, _, _ | _, .everyOf _ _, fragment, _, _, _, _
  | _, .inRelation _, fragment, _, _, _, _ | _, .notInRelation _, fragment, _, _, _, _ => by
    simp [Formula.presentedIn] at fragment

/-- Along a presentation morphism, a list of presented formulas holds at a list of elements exactly when it holds at
their images. -/
theorem satAll_iff : ∀ {n : ℕ} (formulas : Formulas n), Formula.presentedAllIn labels types formulas = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n},
      morphism.toLabelMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ parts, S.satAll sourceEnv formulas parts ↔ T.satAll targetEnv formulas (parts.map morphism.map)
  | _, .nil, _, _, _, _, [] => Iff.rfl
  | _, .nil, _, _, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, fragment, _, _, related, part :: parts => by
    simp only [Formula.presentedAllIn, Bool.and_eq_true] at fragment
    exact and_congr (sat_iff formula fragment.1 related part) (satAll_iff formulas fragment.2 related parts)

/-- Along a presentation morphism, some formula of a presented list holds at the corresponding element exactly when
it holds at the corresponding image. -/
theorem satSome_iff : ∀ {n : ℕ} (formulas : Formulas n), Formula.presentedAllIn labels types formulas = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n},
      morphism.toLabelMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ parts, S.satSome sourceEnv formulas parts ↔ T.satSome targetEnv formulas (parts.map morphism.map)
  | _, .nil, _, _, _, _, [] => Iff.rfl
  | _, .nil, _, _, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, fragment, _, _, related, part :: parts => by
    simp only [Formula.presentedAllIn, Bool.and_eq_true] at fragment
    exact or_congr (sat_iff formula fragment.1 related part) (satSome_iff formulas fragment.2 related parts)
end

end PresentationMorphism

/-! ## The contract -/

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (canon : Pattern → Pattern)
  (domain : Pattern → Bool) (presentations : Pattern → List Pattern)

/-- **The presentations of canonical terms, listed**: a listing of parts and, at each admitted canonical term, the
argument lists of its presentations by each constructor up to canonical form, complete and sound for the language's
constructor presentations, with admitted arguments, among the constructors listed there; and a test of the types it
admits. -/
structure PresentationListing (reading : LanguageReading := .syntax) extends
    PartsListing relEnv language canon domain reading where
  constructors : Pattern → List String
  builds : Pattern → String → List (List Pattern)
  types : TypeExpr → Bool
  typed : Pattern → TypeExpr → Bool
  listed_constructor : ∀ {state constructor arguments}, arguments ∈ builds state constructor →
    constructor ∈ constructors state
  builds_complete : ∀ {state constructor parts}, domain state = true → canon state = state →
    (referenceStructure relEnv language reading).built state constructor parts →
      (∀ part ∈ parts, domain part = true) ∧ parts.map canon ∈ builds state constructor
  builds_sound : ∀ {state constructor arguments}, domain state = true → canon state = state →
    arguments ∈ builds state constructor → ∃ parts, (referenceStructure relEnv language reading).built state constructor parts ∧
      (∀ part ∈ parts, domain part = true) ∧ parts.map canon = arguments
  typed_iff : ∀ {state type}, domain state = true → canon state = state → types type = true →
    (typed state type = true ↔ (referenceStructure relEnv language reading).typed state type)

/-- **The canonical structure with presentations**: canonical terms, their steps, the canonical forms of the parts of
their splits and of the arguments of their constructor presentations, and their types. -/
def canonicalPresentedStructure (reading : LanguageReading := .syntax) : NativeStructure Pattern :=
  { canonicalPartsStructure relEnv language canon domain reading with
    built := fun element constructor parts => ∃ parts₀,
      (referenceStructure relEnv language reading).built element constructor parts₀ ∧
        (∀ part ∈ parts₀, domain part = true) ∧ parts₀.map canon = parts
    typed := fun element type => (referenceStructure relEnv language reading).typed element type }

/-! ## What a term reaches by steps, parts and arguments -/

/-- A step, a passage from a collection to a part of one of its splits, or a passage from a term to an argument of
one of its constructor presentations. -/
def PresentedStep (reading : LanguageReading) (source target : Pattern) : Prop :=
  (∃ label, label.isContext = false ∧ (referenceStructure relEnv language reading).step source label target) ∨
    (∃ kind other, (referenceStructure relEnv language reading).split source kind target other ∨
      (referenceStructure relEnv language reading).split source kind other target) ∨
    ∃ constructor parts, (referenceStructure relEnv language reading).built source constructor parts ∧ target ∈ parts

/-- The terms a term reaches by steps, parts and arguments. -/
def PresentedReached (reading : LanguageReading) (start : Pattern) : Pattern → Prop :=
  Relation.ReflTransGen (PresentedStep relEnv language reading) start

/-- **The part of the language's structure a term reaches by steps, parts and arguments.** -/
def presentedReachableStructure (reading : LanguageReading) (start : Pattern) :
    NativeStructure {term // PresentedReached relEnv language reading start term} where
  step source label target := (referenceStructure relEnv language reading).step source.val label target.val
  built element constructor parts :=
    (referenceStructure relEnv language reading).built element.val constructor (parts.map Subtype.val)
  split element kind first second := (referenceStructure relEnv language reading).split element.val kind first.val second.val
  empty element kind := (referenceStructure relEnv language reading).empty element.val kind
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed element type := (referenceStructure relEnv language reading).typed element.val type
  named element term := (referenceStructure relEnv language reading).named element.val term
  same first second := (referenceStructure relEnv language reading).same first.val second.val
  apply inner _ := inner
  inRelation element relation := (referenceStructure relEnv language reading).inRelation element.val relation

variable {relEnv language fuel canon domain presentations} {reading : LanguageReading}

/-- Lift a list of arguments of a reached term's presentation to reached terms. -/
def liftArguments {start : Pattern} (source : {term // PresentedReached relEnv language reading start term})
    {constructor : String} {parts : List Pattern}
    (built : (referenceStructure relEnv language reading).built source.val constructor parts) :
    List {term // PresentedReached relEnv language reading start term} :=
  parts.attach.map fun part => ⟨part.val, source.2.tail (Or.inr (Or.inr ⟨constructor, parts, built, part.2⟩))⟩

theorem liftArguments_val {start : Pattern} (source : {term // PresentedReached relEnv language reading start term})
    {constructor : String} {parts : List Pattern}
    (built : (referenceStructure relEnv language reading).built source.val constructor parts) :
    (liftArguments source built).map Subtype.val = parts := by
  simp [liftArguments]

/-- **The part a term reaches by steps, parts and arguments sits inside the language's structure.** -/
def presentedReachableMorphism (labels : StepLabel → Bool) (types : TypeExpr → Bool) (start : Pattern) :
    PresentationMorphism (presentedReachableStructure relEnv language reading start)
      (referenceStructure relEnv language reading) labels types where
  map := Subtype.val
  step _ step := step
  stepBack := by
    intro source label target own step
    exact ⟨⟨target, source.2.tail (Or.inl ⟨label, StepLabel.isContext_of_admittedBy own, step⟩)⟩, step, rfl⟩
  sameIff _ _ := Iff.rfl
  namedIff _ _ := Iff.rfl
  split split := split
  splitBack := by
    intro element kind first second split
    exact ⟨⟨first, element.2.tail (Or.inr (Or.inl ⟨kind, second, Or.inl split⟩))⟩,
      ⟨second, element.2.tail (Or.inr (Or.inl ⟨kind, first, Or.inr split⟩))⟩, split, rfl, rfl⟩
  emptyIff _ _ := Iff.rfl
  built built := built
  builtBack := by
    intro element constructor parts' built
    refine ⟨liftArguments element built, ?_, liftArguments_val element built⟩
    show (referenceStructure relEnv language reading).built element.val constructor
      ((liftArguments element built).map Subtype.val)
    rw [liftArguments_val]
    exact built
  typedIff _ _ _ := Iff.rfl

/-- **Taking canonical forms is a presentation morphism** from the part a term reaches by steps, parts and arguments
onto the canonical structure with presentations, when everything reached is admitted. -/
def canonPresentedMorphism (labels : StepLabel → Bool) (types : TypeExpr → Bool)
    (canonical : Canonical relEnv language canon domain reading) {start : Pattern}
    (admitted : ∀ term, PresentedReached relEnv language reading start term → domain term = true) :
    PresentationMorphism (presentedReachableStructure relEnv language reading start)
      (canonicalPresentedStructure relEnv language canon domain reading) labels types where
  map term := canon term.val
  step := by
    intro source label target _ step
    have saturated := referenceStructure_saturated relEnv language reading
    exact ⟨saturated.stepTarget (canonical.indistinct (admitted _ target.2))
        (saturated.stepSource (canonical.indistinct (admitted _ source.2)) step),
      canonical.admitted_canon (admitted _ target.2), canonical.idempotent (admitted _ target.2)⟩
  stepBack := by
    intro source label target' own step
    have saturated := referenceStructure_saturated relEnv language reading
    have original : (referenceStructure relEnv language reading).step source.val label target' :=
      saturated.stepSource (saturated.equivalence.symm (canonical.indistinct (admitted _ source.2))) step.1
    exact ⟨⟨target', source.2.tail (Or.inl ⟨label, StepLabel.isContext_of_admittedBy own, original⟩)⟩, original,
      step.2.2⟩
  sameIff first second := canonical.equivalent_iff (admitted _ first.2) (admitted _ second.2)
  namedIff element term := by
    constructor
    · rintro ⟨-, equivalent⟩
      exact ⟨equivalent.object_right (canonical.object (admitted _ element.2)),
        canonical.invariant (admitted _ element.2) equivalent,
        (canonical.same (admitted _ element.2) equivalent).symm⟩
    · rintro ⟨-, termAdmitted, same⟩
      exact ⟨canonical.object (admitted _ element.2),
        (canonical.equivalent_iff (admitted _ element.2) termAdmitted).mpr same.symm⟩
  split := by
    intro element kind first second split
    have saturated := referenceStructure_saturated relEnv language reading
    exact ⟨first.val, second.val, saturated.split (canonical.indistinct (admitted _ element.2)) split,
      admitted _ first.2, admitted _ second.2, rfl, rfl⟩
  splitBack := by
    intro element kind first' second' split
    obtain ⟨first, second, split, -, -, rfl, rfl⟩ := split
    have saturated := referenceStructure_saturated relEnv language reading
    have original : (referenceStructure relEnv language reading).split element.val kind first second :=
      saturated.split (saturated.equivalence.symm (canonical.indistinct (admitted _ element.2))) split
    exact ⟨⟨first, element.2.tail (Or.inr (Or.inl ⟨kind, second, Or.inl original⟩))⟩,
      ⟨second, element.2.tail (Or.inr (Or.inl ⟨kind, first, Or.inr original⟩))⟩, original, rfl, rfl⟩
  emptyIff element kind := by
    have saturated := referenceStructure_saturated relEnv language reading
    exact ⟨saturated.empty (canonical.indistinct (admitted _ element.2)),
      saturated.empty (saturated.equivalence.symm (canonical.indistinct (admitted _ element.2)))⟩
  built := by
    intro element constructor parts built
    have saturated := referenceStructure_saturated relEnv language reading
    refine ⟨parts.map Subtype.val, saturated.built (canonical.indistinct (admitted _ element.2)) built, ?_, ?_⟩
    · intro part member
      obtain ⟨reached, -, rfl⟩ := List.mem_map.mp member
      exact admitted _ reached.2
    · rw [List.map_map]
      rfl
  builtBack := by
    intro element constructor parts' built
    obtain ⟨parts, built, -, rfl⟩ := built
    have saturated := referenceStructure_saturated relEnv language reading
    have original : (referenceStructure relEnv language reading).built element.val constructor parts :=
      saturated.built (saturated.equivalence.symm (canonical.indistinct (admitted _ element.2))) built
    refine ⟨liftArguments element original, ?_, ?_⟩
    · show (referenceStructure relEnv language reading).built element.val constructor
        ((liftArguments element original).map Subtype.val)
      rw [liftArguments_val]
      exact original
    · calc (liftArguments element original).map (fun term => canon term.val)
          = ((liftArguments element original).map Subtype.val).map canon := by rw [List.map_map]; rfl
        _ = parts.map canon := by rw [liftArguments_val]
  typedIff element type _ := by
    have saturated := referenceStructure_saturated relEnv language reading
    exact ⟨saturated.typed (canonical.indistinct (admitted _ element.2)),
      saturated.typed (saturated.equivalence.symm (canonical.indistinct (admitted _ element.2)))⟩

/-! ## Closed presentation regions -/

variable (relEnv language fuel canon domain presentations)
  (listing : PresentationListing relEnv language canon domain reading) (region : List Pattern)

/-- **A closed presentation region**: a closed parts region that holds the listed arguments of each of its terms. -/
def presentedRegion : Bool :=
  partsRegion relEnv language fuel canon domain presentations listing.toPartsListing region &&
    region.all fun term => (listing.constructors term).all fun constructor =>
      (listing.builds term constructor).all fun arguments => arguments.all fun argument => decide (argument ∈ region)

/-- **The presentation region as a finite structure**: the parts region's steps, names, splits and emptiness, the
listed presentations, and the listed types among the admitted ones. -/
def presentedExploration : FiniteStructure (Fin region.length) :=
  { partsExploration relEnv language fuel canon domain presentations listing.toPartsListing region with
    built := fun element constructor parts =>
      (listing.builds region[element] constructor).any fun arguments => arguments == parts.map (region[·])
    typed := fun element type => listing.types type && listing.typed region[element] type }

variable {relEnv language fuel canon domain presentations listing region}

theorem presentedRegion_parts
    (closed : presentedRegion relEnv language fuel canon domain presentations listing region = true) :
    partsRegion relEnv language fuel canon domain presentations listing.toPartsListing region = true ∧
      ∀ term ∈ region, ∀ constructor, ∀ arguments ∈ listing.builds term constructor, ∀ argument ∈ arguments,
        argument ∈ region := by
  simp only [presentedRegion, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at closed
  exact ⟨closed.1, fun term member constructor arguments listed =>
    closed.2 term member constructor (listing.listed_constructor listed) arguments listed⟩

/-- **A closed presentation region's inclusion is a presentation morphism** on admitted labels and the listing's
types, given canonical forms, coherence on those labels and the listing. -/
def presentedRegionMorphism {labels : StepLabel → Bool} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentOn relEnv language fuel canon domain presentations labels reading)
    (closed : presentedRegion relEnv language fuel canon domain presentations listing region = true) :
    PresentationMorphism (presentedExploration relEnv language fuel canon domain presentations listing region).native
      (canonicalPresentedStructure relEnv language canon domain reading) labels listing.types where
  toLabelMorphism :=
    let regionSide := regionMorphismOn canonical coherent (partsRegion_parts (presentedRegion_parts closed).1).1
    LabelMorphism.mk regionSide.map regionSide.step regionSide.stepBack regionSide.sameIff regionSide.namedIff
  split := by
    intro element kind first second listed
    change ((listing.splits region[element] kind).any fun pair => pair.1 == region[first] && pair.2 == region[second])
      = true at listed
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at listed
    obtain ⟨pair, member, sameFirst, sameSecond⟩ := listed
    obtain ⟨admitted, canonState, -⟩ := (canonicalRegion_parts
      (partsRegion_parts (presentedRegion_parts closed).1).1).2 _ (List.getElem_mem element.2)
    obtain ⟨first₀, second₀, split, firstAdmitted, secondAdmitted, canonFirst, canonSecond⟩ :=
      listing.sound admitted canonState member
    exact ⟨first₀, second₀, split, firstAdmitted, secondAdmitted, canonFirst.trans sameFirst,
      canonSecond.trans sameSecond⟩
  splitBack := by
    intro element kind first' second' split
    obtain ⟨first₀, second₀, split, -, -, rfl, rfl⟩ := split
    have partsClosed := (presentedRegion_parts closed).1
    obtain ⟨admitted, canonState, -⟩ :=
      (canonicalRegion_parts (partsRegion_parts partsClosed).1).2 _ (List.getElem_mem element.2)
    obtain ⟨-, -, member⟩ := listing.complete admitted canonState split
    obtain ⟨firstListed, secondListed⟩ := (partsRegion_parts partsClosed).2 _ (List.getElem_mem element.2) kind _ member
    obtain ⟨first, isFirst⟩ := exists_index firstListed
    obtain ⟨second, isSecond⟩ := exists_index secondListed
    refine ⟨first, second, ?_, isFirst, isSecond⟩
    change ((listing.splits region[element] kind).any fun pair => pair.1 == region[first] && pair.2 == region[second])
      = true
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨_, member, isFirst.symm, isSecond.symm⟩
  emptyIff element kind := by
    obtain ⟨admitted, canonState, -⟩ := (canonicalRegion_parts
      (partsRegion_parts (presentedRegion_parts closed).1).1).2 _ (List.getElem_mem element.2)
    exact listing.empty_iff admitted canonState
  built := by
    intro element constructor parts listed
    change ((listing.builds region[element] constructor).any fun arguments => arguments == parts.map (region[·]))
      = true at listed
    simp only [List.any_eq_true, beq_iff_eq] at listed
    obtain ⟨arguments, member, same⟩ := listed
    obtain ⟨admitted, canonState, -⟩ := (canonicalRegion_parts
      (partsRegion_parts (presentedRegion_parts closed).1).1).2 _ (List.getElem_mem element.2)
    obtain ⟨parts₀, built, partsAdmitted, canonParts⟩ := listing.builds_sound admitted canonState member
    exact ⟨parts₀, built, partsAdmitted, canonParts.trans same⟩
  builtBack := by
    intro element constructor parts' built
    obtain ⟨parts₀, built, -, rfl⟩ := built
    obtain ⟨admitted, canonState, -⟩ := (canonicalRegion_parts
      (partsRegion_parts (presentedRegion_parts closed).1).1).2 _ (List.getElem_mem element.2)
    obtain ⟨-, member⟩ := listing.builds_complete admitted canonState built
    obtain ⟨indices, same⟩ := exists_indices (region := region) (terms := parts₀.map canon)
      ((presentedRegion_parts closed).2 _ (List.getElem_mem element.2) constructor _ member)
    refine ⟨indices, ?_, same⟩
    change ((listing.builds region[element] constructor).any fun arguments => arguments == indices.map (region[·]))
      = true
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, member, same.symm⟩
  typedIff element type admittedType := by
    obtain ⟨admitted, canonState, -⟩ := (canonicalRegion_parts
      (partsRegion_parts (presentedRegion_parts closed).1).1).2 _ (List.getElem_mem element.2)
    change (listing.types type && listing.typed region[element] type) = true ↔ _
    rw [admittedType, Bool.true_and]
    exact listing.typed_iff admitted canonState admittedType

/-- **Everything an admitted term reaches by steps, parts and arguments is admitted**, with its canonical form in a
closed presentation region that lists the term's. -/
theorem presentedReached_admitted (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentPlain relEnv language fuel canon domain presentations reading)
    (closed : presentedRegion relEnv language fuel canon domain presentations listing region = true) {start : Pattern}
    (admitted : domain start = true) (listed : canon start ∈ region) :
    ∀ {term}, PresentedReached relEnv language reading start term → domain term = true ∧ canon term ∈ region := by
  intro term reached
  have saturated := referenceStructure_saturated relEnv language reading
  have partsClosed := (presentedRegion_parts closed).1
  obtain ⟨canonicalClosed, partsListed⟩ := partsRegion_parts partsClosed
  induction reached with
  | refl => exact ⟨admitted, listed⟩
  | tail _ presentedStep previous =>
    obtain ⟨sourceAdmitted, sourceListed⟩ := previous
    rcases presentedStep with ⟨label, own, sourceState, targetState, redex, contractum, witness, before, redexState,
      valid, contractumState, after, admits⟩ | ⟨kind, other, split⟩ | ⟨constructor, parts, built, member⟩
    · rw [placed_iff own] at before
      obtain ⟨-, members⟩ := canonicalRegion_parts canonicalClosed
      obtain ⟨-, canonSource, listing'⟩ := members _ sourceListed
      have canonState := canonical.state sourceAdmitted sourceState
      obtain ⟨-, complete, successors⟩ := listing' (isStateBool_of_isState canonState)
      obtain ⟨entry, entryMember, sameCanon⟩ :=
        coherent canonState (canonical.admitted_canon sourceAdmitted) canonSource complete
          (ObjectEquivalent.equivalence.trans (ObjectEquivalent.equivalence.symm (canonical.equivalent sourceAdmitted))
            before) redexState valid
      have entryListed := successors entry entryMember
      have contractumAdmitted : domain contractum = true :=
        canonical.stepsAdmitted (canonical.invariant sourceAdmitted before) redexState valid
          (sameCanon ▸ (members _ entryListed).1)
      refine ⟨canonical.invariant contractumAdmitted after, ?_⟩
      rw [← canonical.same contractumAdmitted after, ← sameCanon]
      exact entryListed
    · have canonAdmitted := canonical.admitted_canon sourceAdmitted
      have canonIdempotent := canonical.idempotent sourceAdmitted
      rcases split with split | split
      · obtain ⟨targetAdmitted, -, pairMember⟩ := listing.complete canonAdmitted canonIdempotent
          (saturated.split (canonical.indistinct sourceAdmitted) split)
        exact ⟨targetAdmitted, (partsListed _ sourceListed kind _ pairMember).1⟩
      · obtain ⟨-, targetAdmitted, pairMember⟩ := listing.complete canonAdmitted canonIdempotent
          (saturated.split (canonical.indistinct sourceAdmitted) split)
        exact ⟨targetAdmitted, (partsListed _ sourceListed kind _ pairMember).2⟩
    · obtain ⟨partsAdmitted, argumentsMember⟩ := listing.builds_complete (canonical.admitted_canon sourceAdmitted)
        (canonical.idempotent sourceAdmitted) (saturated.built (canonical.indistinct sourceAdmitted) built)
      exact ⟨partsAdmitted _ member, (presentedRegion_parts closed).2 _ sourceListed constructor _ argumentsMember _
        (List.mem_map_of_mem member)⟩

/-- **A closed presentation region decides every presented formula** over admitted labels and the listing's types,
at the admitted terms whose canonical forms it lists, both ways. -/
theorem presented_check_iff {labels : StepLabel → Bool} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentOn relEnv language fuel canon domain presentations labels reading)
    (closed : presentedRegion relEnv language fuel canon domain presentations listing region = true)
    {formula : Formula 0} (fragment : formula.presentedIn labels listing.types = true) {index : Fin region.length}
    {term : Pattern} (admitted : domain term = true) (listed : canon term = region[index]) :
    (presentedExploration relEnv language fuel canon domain presentations listing region).check formula index = true ↔
      (referenceStructure relEnv language reading).sat Env.closed formula term := by
  have allAdmitted : ∀ other, PresentedReached relEnv language reading term other → domain other = true :=
    fun _ reached =>
      (presentedReached_admitted canonical coherent.plain closed admitted (listed ▸ List.getElem_mem index.2)
        reached).1
  have regionSide := (presentedRegionMorphism canonical coherent closed).sat_iff formula fragment
    (LabelMorphism.envPreimage_closed _) index
  have canonSide := (canonPresentedMorphism labels listing.types canonical allAdmitted).sat_iff formula fragment
    (LabelMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  have reachSide := (presentedReachableMorphism (relEnv := relEnv) (language := language) (reading := reading)
    labels listing.types term).sat_iff formula fragment
    (LabelMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  rw [FiniteStructure.check_iff]
  refine regionSide.trans (Iff.trans ?_ (canonSide.symm.trans reachSide))
  show (canonicalPresentedStructure relEnv language canon domain reading).sat Env.closed formula region[index] ↔
    (canonicalPresentedStructure relEnv language canon domain reading).sat Env.closed formula (canon term)
  rw [listed]

/-! ## Growing a presentation region -/

variable (relEnv language fuel canon presentations listing)

/-- What a term adds to a presentation region: the canonical forms of its listed successors when it is a state, the
listed parts of its splits, and the listed arguments of its presentations. -/
abbrev nextPresented (term : Pattern) : List Pattern :=
  nextCanonical relEnv language fuel canon presentations term reading.rules ++
    (collKinds.flatMap fun kind => (listing.splits term kind).flatMap fun pair => [pair.1, pair.2]) ++
    (listing.constructors term).flatMap fun constructor => (listing.builds term constructor).flatten

/-- Grow a presentation region from a term, the term's canonical form first. -/
def growPresented (term : Pattern) : ℕ → List Pattern
  | 0 => [canon term]
  | rounds + 1 =>
    let earlier := growPresented term rounds
    addNew earlier (earlier.flatMap (nextPresented relEnv language fuel canon presentations listing))

theorem growPresented_first (term : Pattern) :
    ∀ rounds, ∃ rest, growPresented relEnv language fuel canon presentations listing term rounds = canon term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := growPresented_first term rounds
    obtain ⟨extra, extended⟩ := addNew_extends
      (growPresented relEnv language fuel canon presentations listing term rounds)
      ((growPresented relEnv language fuel canon presentations listing term rounds).flatMap
        (nextPresented relEnv language fuel canon presentations listing))
    refine ⟨rest ++ extra, ?_⟩
    simp only [growPresented]
    rw [extended, same, List.cons_append]

theorem growPresented_length_pos (term : Pattern) (rounds : ℕ) :
    0 < (growPresented relEnv language fuel canon presentations listing term rounds).length := by
  obtain ⟨rest, same⟩ := growPresented_first relEnv language fuel canon presentations listing term rounds
  rw [same]
  exact Nat.succ_pos _

variable (domain)

/-- **Decide a presented formula at a term modulo the equations**: the exact verdict when the grown presentation
region closes, nothing otherwise. -/
def decidePresented (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  if domain term && presentedRegion relEnv language fuel canon domain presentations listing
    (growPresented relEnv language fuel canon presentations listing term rounds) then
    some ((presentedExploration relEnv language fuel canon domain presentations listing
      (growPresented relEnv language fuel canon presentations listing term rounds)).check
      formula ⟨0, growPresented_length_pos relEnv language fuel canon presentations listing term rounds⟩)
  else none

variable {relEnv language fuel canon domain presentations listing}

theorem growPresented_zero (term : Pattern) (rounds : ℕ) :
    (growPresented relEnv language fuel canon presentations listing term rounds)[(⟨0,
      growPresented_length_pos relEnv language fuel canon presentations listing term rounds⟩ :
        Fin (growPresented relEnv language fuel canon presentations listing term rounds).length)] = canon term := by
  obtain ⟨rest, same⟩ := growPresented_first relEnv language fuel canon presentations listing term rounds
  simp only [Fin.getElem_fin]
  simp [same]

/-- **A verdict from a closed presentation region is exact.** -/
theorem decidePresented_sound {labels : StepLabel → Bool} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentOn relEnv language fuel canon domain presentations labels reading)
    {formula : Formula 0} (fragment : formula.presentedIn labels listing.types = true) {term : Pattern} {rounds : ℕ}
    {verdict : Bool}
    (decided : decidePresented relEnv language fuel canon domain presentations listing formula term rounds =
      some verdict) :
    (verdict = true ↔ (referenceStructure relEnv language reading).sat Env.closed formula term) := by
  unfold decidePresented at decided
  split at decided
  · rename_i checked
    obtain ⟨admitted, closed⟩ := Bool.and_eq_true_iff.mp checked
    cases decided
    have listed := growPresented_zero (relEnv := relEnv) (language := language) (fuel := fuel) (canon := canon)
      (presentations := presentations) (listing := listing) term rounds
    exact presented_check_iff canonical coherent closed fragment admitted listed.symm
  · cases decided

/-! ## At the front door -/

/-- **The presentation decider of canonical forms**: for a formula presented over the forms' labels and the listing's
types, the verdict of the presentation region grown from the term, when it closes. -/
def presentedDecider (forms : CanonicalForms relEnv language fuel)
    (listing : PresentationListing relEnv language forms.canon forms.domain forms.reading) (rounds : ℕ) :
    Decider relEnv language forms.reading where
  decide formula term :=
    if formula.presentedIn forms.labels listing.types then
      decidePresented relEnv language fuel forms.canon forms.domain forms.presentations listing formula term rounds
    else none
  exact := by
    intro formula term answer decided
    by_cases fragment : formula.presentedIn forms.labels listing.types = true
    · rw [if_pos fragment] at decided
      exact (decidePresented_sound forms.canonical forms.coherent fragment decided).symm
    · rw [if_neg fragment] at decided
      cases decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
