import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions

/-!
# Splits at the front door, for languages with canonical forms

A closed canonical region decides the behavioural formulas: steps forward, counting forward, singletons, fixed points
and the connectives. A split looks inside a collection instead of along a step, so a region that is to decide splits
must also hold the parts of its collections. This works through one more contract on canonical forms.

- **The fragment** (`Formula.behaviouralParts`): the behavioural formulas, with splits, every-splits and emptiness.
- **Parts morphisms** (`PartsMorphism`): step morphisms whose splits go forward and come back, and that preserve and
  reflect emptiness. Along one, every formula of the fragment is preserved and reflected (`PartsMorphism.sat_iff`).
- **The contract** (`PartsListing`): at each admitted canonical collection, a list of splits up to canonical form,
  complete and sound for the language's splits, whose parts are admitted; and a test of emptiness.
- **The canonical structure with parts** (`canonicalPartsStructure`): canonical terms with the canonical forms of the
  parts of their splits. Taking canonical forms is a parts morphism onto it from what a term reaches by steps and
  parts (`canonPartsMorphism`).
- **A closed parts region** (`partsRegion`): a closed canonical region that also holds the listed parts of its terms.
  Its inclusion is a parts morphism (`partsRegionMorphism`), so the finite evaluator's verdict on it is exact
  (`parts_check_iff`); `decideParts` grows such a region from a term (`decideParts_sound`) and `partsDecider` is a
  certified decider for the front door.
- **Equation-free languages** list the cuts of a collection (`identityParts`): with no equations, the splits of
  `{a₁, …, aₙ}` are its ways of being written `left ++ right`.
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

/-- **Behavioural formulas with parts**: the forward behavioural formulas, with splits, every-splits and
emptiness. -/
def behaviouralParts : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ | _, .empty _ | _, .nonEmpty _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    behaviouralParts left && behaviouralParts right
  | _, .mu inner | _, .nu inner => behaviouralParts inner
  | _, .possibly label formula | _, .necessarily label formula => !label.isContext && behaviouralParts formula
  | _, .atLeast _ .forward label formula | _, .allButFewer _ .forward label formula =>
    !label.isContext && behaviouralParts formula
  | _, _ => false

/-- Every behavioural formula is one with parts. -/
theorem behaviouralParts_of_behaviouralForward : ∀ {n : ℕ} (formula : Formula n),
    formula.behaviouralForward = true → formula.behaviouralParts = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ => rfl
  | _, .and left right, behavioural | _, .or left right, behavioural => by
    simp only [behaviouralForward, Bool.and_eq_true] at behavioural
    simp only [behaviouralParts, behaviouralParts_of_behaviouralForward left behavioural.1,
      behaviouralParts_of_behaviouralForward right behavioural.2, Bool.and_self]
  | _, .mu inner, behavioural | _, .nu inner, behavioural =>
    behaviouralParts_of_behaviouralForward inner behavioural
  | _, .possibly _ formula, behavioural | _, .necessarily _ formula, behavioural
  | _, .atLeast _ .forward _ formula, behavioural | _, .allButFewer _ .forward _ formula, behavioural => by
    simp only [behaviouralForward, Bool.and_eq_true] at behavioural
    simp only [behaviouralParts, behavioural.1, behaviouralParts_of_behaviouralForward formula behavioural.2,
      Bool.and_self]
  | _, .sometimeBefore _ _, behavioural | _, .alwaysBefore _ _, behavioural
  | _, .atLeast _ .backward _ _, behavioural | _, .allButFewer _ .backward _ _, behavioural
  | _, .built _ _, behavioural | _, .everyBuilt _ _, behavioural | _, .split _ _ _, behavioural
  | _, .everySplit _ _ _, behavioural | _, .empty _, behavioural | _, .nonEmpty _, behavioural
  | _, .single _ _, behavioural | _, .everySingle _ _, behavioural | _, .body _, behavioural
  | _, .everyBody _, behavioural | _, .multiBody _ _, behavioural | _, .everyMultiBody _ _, behavioural
  | _, .bound _, behavioural | _, .notBound _, behavioural | _, .typed _, behavioural | _, .untyped _, behavioural
  | _, .mapsAll _ _, behavioural | _, .mapsSome _ _, behavioural | _, .someOf _ _, behavioural
  | _, .everyOf _ _, behavioural => by simp [behaviouralForward] at behavioural

end Formula

/-! ## Parts morphisms -/

/-- **A parts morphism**: a step morphism whose splits go forward and come back, and that preserves and reflects
emptiness. -/
structure PartsMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) extends StepMorphism S T where
  split : ∀ {element kind first second}, S.split element kind first second →
    T.split (map element) kind (map first) (map second)
  splitBack : ∀ {element kind first' second'}, T.split (map element) kind first' second' →
    ∃ first second, S.split element kind first second ∧ map first = first' ∧ map second = second'
  emptyIff : ∀ element kind, S.empty element kind ↔ T.empty (map element) kind

namespace PartsMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  (morphism : PartsMorphism S T)

/-- **Along a parts morphism, a behavioural formula with parts holds at an element exactly when it holds at its
image.** -/
theorem sat_iff : ∀ {n : ℕ} (formula : Formula n), formula.behaviouralParts = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.toStepMorphism.EnvPreimage sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element)
  | _, .top, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _ => Iff.rfl
  | _, .and left right, fragment, _, _, related, element => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true] at fragment
    exact and_congr (sat_iff left fragment.1 related element) (sat_iff right fragment.2 related element)
  | _, .or left right, fragment, _, _, related, element => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true] at fragment
    exact or_congr (sat_iff left fragment.1 related element) (sat_iff right fragment.2 related element)
  | _, .var index, _, _, _, related, element => related index element
  | _, .mu inner, fragment, sourceEnv, targetEnv, related, element => by
    constructor
    · intro holds closed closedHolds
      exact holds (morphism.map ⁻¹' closed) fun other otherHolds =>
        closedHolds _ ((sat_iff inner fragment (related.extend morphism.toStepMorphism closed) other).mp otherHolds)
    · intro holds closed closedHolds
      let pushed : Set Target := {image | ∀ origin, morphism.map origin = image → origin ∈ closed}
      have inside : ∀ origin, morphism.map origin ∈ pushed → origin ∈ closed :=
        fun origin member => member origin rfl
      have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
        subst originMaps
        exact closedHolds origin (S.sat_mono inner (sourceEnv.extend_sub fun other member => inside other member) origin
          ((sat_iff inner fragment (related.extend morphism.toStepMorphism pushed) origin).mpr imageHolds))
      exact inside element pushedHolds
  | _, .nu inner, fragment, sourceEnv, targetEnv, related, element => by
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨morphism.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
      rintro _ ⟨other, otherMember, rfl⟩
      exact (sat_iff inner fragment (related.extend morphism.toStepMorphism (morphism.map '' invariant)) other).mp
        (S.sat_mono inner (sourceEnv.extend_sub fun origin inside => Set.mem_image_of_mem morphism.map inside) other
          (preserved other otherMember))
    · rintro ⟨invariant, member, preserved⟩
      exact ⟨morphism.map ⁻¹' invariant, member, fun other otherMember =>
        (sat_iff inner fragment (related.extend morphism.toStepMorphism invariant) other).mpr (preserved _ otherMember)⟩
  | _, .possibly _ formula, fragment, _, _, related, element => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at fragment
    constructor
    · rintro ⟨next, step, holds⟩
      exact ⟨morphism.map next, morphism.step fragment.1 step, (sat_iff formula fragment.2 related next).mp holds⟩
    · rintro ⟨next', step', holds'⟩
      obtain ⟨next, step, rfl⟩ := morphism.stepBack fragment.1 step'
      exact ⟨next, step, (sat_iff formula fragment.2 related next).mpr holds'⟩
  | _, .necessarily _ formula, fragment, _, _, related, element => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at fragment
    constructor
    · intro every next' step'
      obtain ⟨next, step, rfl⟩ := morphism.stepBack fragment.1 step'
      exact (sat_iff formula fragment.2 related next).mp (every next step)
    · intro every next step
      exact (sat_iff formula fragment.2 related next).mpr (every _ (morphism.step fragment.1 step))
  | _, .atLeast _ .forward _ formula, fragment, _, _, related, _ => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at fragment
    exact morphism.toStepMorphism.atLeast_steps_iff fragment.1 fun other => sat_iff formula fragment.2 related other
  | _, .allButFewer _ .forward _ formula, fragment, _, _, related, _ => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at fragment
    exact not_congr (morphism.toStepMorphism.atLeast_steps_iff fragment.1 fun other =>
      not_congr (sat_iff formula fragment.2 related other))
  | _, .split _ left right, fragment, _, _, related, element => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true] at fragment
    constructor
    · rintro ⟨first, second, split, leftHolds, rightHolds⟩
      exact ⟨morphism.map first, morphism.map second, morphism.split split,
        (sat_iff left fragment.1 related first).mp leftHolds, (sat_iff right fragment.2 related second).mp rightHolds⟩
    · rintro ⟨first', second', split', leftHolds, rightHolds⟩
      obtain ⟨first, second, split, rfl, rfl⟩ := morphism.splitBack split'
      exact ⟨first, second, split, (sat_iff left fragment.1 related first).mpr leftHolds,
        (sat_iff right fragment.2 related second).mpr rightHolds⟩
  | _, .everySplit _ left right, fragment, _, _, related, element => by
    simp only [Formula.behaviouralParts, Bool.and_eq_true] at fragment
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
  | _, .is term, _, _, _, _, element => morphism.namedIff element term
  | _, .isNot term, _, _, _, _, element => not_congr (morphism.namedIff element term)
  | _, .sometimeBefore _ _, fragment, _, _, _, _ | _, .alwaysBefore _ _, fragment, _, _, _, _
  | _, .atLeast _ .backward _ _, fragment, _, _, _, _ | _, .allButFewer _ .backward _ _, fragment, _, _, _, _
  | _, .built _ _, fragment, _, _, _, _ | _, .everyBuilt _ _, fragment, _, _, _, _
  | _, .single _ _, fragment, _, _, _, _ | _, .everySingle _ _, fragment, _, _, _, _
  | _, .body _, fragment, _, _, _, _ | _, .everyBody _, fragment, _, _, _, _
  | _, .multiBody _ _, fragment, _, _, _, _ | _, .everyMultiBody _ _, fragment, _, _, _, _
  | _, .bound _, fragment, _, _, _, _ | _, .notBound _, fragment, _, _, _, _
  | _, .typed _, fragment, _, _, _, _ | _, .untyped _, fragment, _, _, _, _
  | _, .mapsAll _ _, fragment, _, _, _, _ | _, .mapsSome _ _, fragment, _, _, _, _
  | _, .someOf _ _, fragment, _, _, _, _ | _, .everyOf _ _, fragment, _, _, _, _ => by
    simp [Formula.behaviouralParts] at fragment

end PartsMorphism

/-! ## The contract -/

/-- The kinds of collections. -/
def collKinds : List CollType := [.vec, .hashBag, .hashSet]

theorem mem_collKinds (kind : CollType) : kind ∈ collKinds := by
  cases kind <;> simp [collKinds]

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (canon : Pattern → Pattern)
  (domain : Pattern → Bool) (presentations : Pattern → List Pattern)

/-- **The parts of canonical collections, listed**: at each admitted canonical term, its splits of each kind up to
canonical form, complete and sound for the language's splits, with admitted parts; and a test of emptiness. -/
structure PartsListing (reading : LanguageReading := .syntax) where
  splits : Pattern → CollType → List (Pattern × Pattern)
  empty : Pattern → CollType → Bool
  complete : ∀ {state kind first second}, domain state = true → canon state = state →
    (referenceStructure relEnv language reading).split state kind first second →
      domain first = true ∧ domain second = true ∧ (canon first, canon second) ∈ splits state kind
  sound : ∀ {state kind pair}, domain state = true → canon state = state → pair ∈ splits state kind →
    ∃ first second, (referenceStructure relEnv language reading).split state kind first second ∧ domain first = true ∧
      domain second = true ∧ canon first = pair.1 ∧ canon second = pair.2
  empty_iff : ∀ {state kind}, domain state = true → canon state = state →
    (empty state kind = true ↔ (referenceStructure relEnv language reading).empty state kind)

/-- **The canonical structure with parts**: canonical terms, their steps, and the canonical forms of the parts of
their splits. -/
def canonicalPartsStructure (reading : LanguageReading := .syntax) : NativeStructure Pattern :=
  { canonicalStructure relEnv language canon domain reading with
    split := fun element kind first second => ∃ first₀ second₀,
      (referenceStructure relEnv language reading).split element kind first₀ second₀ ∧ domain first₀ = true ∧
        domain second₀ = true ∧ canon first₀ = first ∧ canon second₀ = second
    empty := fun element kind => (referenceStructure relEnv language reading).empty element kind }

/-! ## What a term reaches by steps and parts -/

/-- A step of the term's own, or a passage from a collection to a part of one of its splits. -/
def PartStep (reading : LanguageReading) (source target : Pattern) : Prop :=
  (∃ label, label.isContext = false ∧ (referenceStructure relEnv language reading).step source label target) ∨
    ∃ kind other, (referenceStructure relEnv language reading).split source kind target other ∨
      (referenceStructure relEnv language reading).split source kind other target

/-- The terms a term reaches by steps and parts. -/
def PartsReached (reading : LanguageReading) (start : Pattern) : Pattern → Prop :=
  Relation.ReflTransGen (PartStep relEnv language reading) start

/-- **The part of the language's structure a term reaches by steps and parts.** -/
def partsReachableStructure (reading : LanguageReading) (start : Pattern) :
    NativeStructure {term // PartsReached relEnv language reading start term} where
  step source label target := (referenceStructure relEnv language reading).step source.val label target.val
  built _ _ _ := False
  split element kind first second := (referenceStructure relEnv language reading).split element.val kind first.val second.val
  empty element kind := (referenceStructure relEnv language reading).empty element.val kind
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ _ := False
  named element term := (referenceStructure relEnv language reading).named element.val term
  same first second := (referenceStructure relEnv language reading).same first.val second.val
  apply inner _ := inner
  inRelation element relation := (referenceStructure relEnv language reading).inRelation element.val relation

variable {relEnv language fuel canon domain presentations} {reading : LanguageReading}

/-- **The part a term reaches by steps and parts sits inside the language's structure.** -/
def partsReachableMorphism (start : Pattern) :
    PartsMorphism (partsReachableStructure relEnv language reading start) (referenceStructure relEnv language reading) where
  map := Subtype.val
  step _ step := step
  stepBack := by
    intro source label target own step
    exact ⟨⟨target, source.2.tail (Or.inl ⟨label, own, step⟩)⟩, step, rfl⟩
  sameIff _ _ := Iff.rfl
  namedIff _ _ := Iff.rfl
  split split := split
  splitBack := by
    intro element kind first second split
    exact ⟨⟨first, element.2.tail (Or.inr ⟨kind, second, Or.inl split⟩)⟩,
      ⟨second, element.2.tail (Or.inr ⟨kind, first, Or.inr split⟩)⟩, split, rfl, rfl⟩
  emptyIff _ _ := Iff.rfl

/-- **Taking canonical forms is a parts morphism** from the part a term reaches by steps and parts onto the
canonical structure with parts, when everything reached is admitted. -/
def canonPartsMorphism (canonical : Canonical relEnv language canon domain reading) {start : Pattern}
    (admitted : ∀ term, PartsReached relEnv language reading start term → domain term = true) :
    PartsMorphism (partsReachableStructure relEnv language reading start)
      (canonicalPartsStructure relEnv language canon domain reading) where
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
    exact ⟨⟨target', source.2.tail (Or.inl ⟨label, own, original⟩)⟩, original, step.2.2⟩
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
    exact ⟨⟨first, element.2.tail (Or.inr ⟨kind, second, Or.inl original⟩)⟩,
      ⟨second, element.2.tail (Or.inr ⟨kind, first, Or.inr original⟩)⟩, original, rfl, rfl⟩
  emptyIff element kind := by
    have saturated := referenceStructure_saturated relEnv language reading
    exact ⟨saturated.empty (canonical.indistinct (admitted _ element.2)),
      saturated.empty (saturated.equivalence.symm (canonical.indistinct (admitted _ element.2)))⟩

/-! ## Closed parts regions -/

variable (relEnv language fuel canon domain presentations) (listing : PartsListing relEnv language canon domain reading)
  (region : List Pattern)

/-- **A closed parts region**: a closed canonical region that holds the listed parts of each of its terms. -/
def partsRegion : Bool :=
  canonicalRegion relEnv language fuel canon domain presentations region reading.rules &&
    region.all fun term => collKinds.all fun kind =>
      (listing.splits term kind).all fun pair => decide (pair.1 ∈ region) && decide (pair.2 ∈ region)

/-- **The parts region as a finite structure**: the canonical region's steps and names, the listed splits and the
emptiness test. -/
def partsExploration : FiniteStructure (Fin region.length) :=
  { canonicalExploration relEnv language fuel canon domain presentations region reading.rules with
    split := fun element kind first second =>
      (listing.splits region[element] kind).any fun pair => pair.1 == region[first] && pair.2 == region[second]
    empty := fun element kind => listing.empty region[element] kind }

variable {relEnv language fuel canon domain presentations listing region}

theorem partsRegion_parts (closed : partsRegion relEnv language fuel canon domain presentations listing region = true) :
    canonicalRegion relEnv language fuel canon domain presentations region reading.rules = true ∧
      ∀ term ∈ region, ∀ kind, ∀ pair ∈ listing.splits term kind, pair.1 ∈ region ∧ pair.2 ∈ region := by
  simp only [partsRegion, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at closed
  exact ⟨closed.1, fun term member kind pair listed => closed.2 term member kind (mem_collKinds kind) pair listed⟩

/-- **A closed parts region's inclusion is a parts morphism**, given canonical forms, coherence and a listing of
parts. -/
def partsRegionMorphism (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    (closed : partsRegion relEnv language fuel canon domain presentations listing region = true) :
    PartsMorphism (partsExploration relEnv language fuel canon domain presentations listing region).native
      (canonicalPartsStructure relEnv language canon domain reading) where
  toStepMorphism :=
    let regionSide := regionMorphism canonical coherent (partsRegion_parts closed).1
    ⟨regionSide.map, regionSide.step, regionSide.stepBack, regionSide.sameIff, regionSide.namedIff⟩
  split := by
    intro element kind first second listed
    change ((listing.splits region[element] kind).any fun pair => pair.1 == region[first] && pair.2 == region[second])
      = true at listed
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at listed
    obtain ⟨pair, member, sameFirst, sameSecond⟩ := listed
    obtain ⟨admitted, canonState, -⟩ :=
      (canonicalRegion_parts (partsRegion_parts closed).1).2 _ (List.getElem_mem element.2)
    obtain ⟨first₀, second₀, split, firstAdmitted, secondAdmitted, canonFirst, canonSecond⟩ :=
      listing.sound admitted canonState member
    exact ⟨first₀, second₀, split, firstAdmitted, secondAdmitted, canonFirst.trans sameFirst,
      canonSecond.trans sameSecond⟩
  splitBack := by
    intro element kind first' second' split
    obtain ⟨first₀, second₀, split, -, -, rfl, rfl⟩ := split
    obtain ⟨admitted, canonState, -⟩ :=
      (canonicalRegion_parts (partsRegion_parts closed).1).2 _ (List.getElem_mem element.2)
    obtain ⟨-, -, member⟩ := listing.complete admitted canonState split
    obtain ⟨firstListed, secondListed⟩ := (partsRegion_parts closed).2 _ (List.getElem_mem element.2) kind _ member
    obtain ⟨first, isFirst⟩ := exists_index firstListed
    obtain ⟨second, isSecond⟩ := exists_index secondListed
    refine ⟨first, second, ?_, isFirst, isSecond⟩
    change ((listing.splits region[element] kind).any fun pair => pair.1 == region[first] && pair.2 == region[second])
      = true
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨_, member, isFirst.symm, isSecond.symm⟩
  emptyIff element kind := by
    obtain ⟨admitted, canonState, -⟩ :=
      (canonicalRegion_parts (partsRegion_parts closed).1).2 _ (List.getElem_mem element.2)
    exact listing.empty_iff admitted canonState

/-- **Everything an admitted term reaches by steps and parts is admitted**, with its canonical form in a closed parts
region that lists the term's. -/
theorem partsReached_admitted (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentPlain relEnv language fuel canon domain presentations reading)
    (closed : partsRegion relEnv language fuel canon domain presentations listing region = true) {start : Pattern}
    (admitted : domain start = true) (listed : canon start ∈ region) :
    ∀ {term}, PartsReached relEnv language reading start term → domain term = true ∧ canon term ∈ region := by
  intro term reached
  have saturated := referenceStructure_saturated relEnv language reading
  obtain ⟨canonicalClosed, partsListed⟩ := partsRegion_parts closed
  induction reached with
  | refl => exact ⟨admitted, listed⟩
  | tail _ partStep previous =>
    obtain ⟨sourceAdmitted, sourceListed⟩ := previous
    rcases partStep with ⟨label, own, sourceState, targetState, redex, contractum, witness, before, redexState, valid,
      contractumState, after, admits⟩ | ⟨kind, other, split⟩
    · rw [placed_iff own] at before
      obtain ⟨-, members⟩ := canonicalRegion_parts canonicalClosed
      obtain ⟨-, canonSource, listing'⟩ := members _ sourceListed
      have canonState := canonical.state sourceAdmitted sourceState
      obtain ⟨-, complete, successors⟩ := listing' (isStateBool_of_isState canonState)
      obtain ⟨entry, member, sameCanon⟩ :=
        coherent canonState (canonical.admitted_canon sourceAdmitted) canonSource complete
          (ObjectEquivalent.equivalence.trans (ObjectEquivalent.equivalence.symm (canonical.equivalent sourceAdmitted))
            before) redexState valid
      have entryListed := successors entry member
      have contractumAdmitted : domain contractum = true :=
        canonical.stepsAdmitted (canonical.invariant sourceAdmitted before) redexState valid
          (sameCanon ▸ (members _ entryListed).1)
      refine ⟨canonical.invariant contractumAdmitted after, ?_⟩
      rw [← canonical.same contractumAdmitted after, ← sameCanon]
      exact entryListed
    · have canonAdmitted := canonical.admitted_canon sourceAdmitted
      have canonIdempotent := canonical.idempotent sourceAdmitted
      rcases split with split | split
      · obtain ⟨targetAdmitted, -, member⟩ := listing.complete canonAdmitted canonIdempotent
          (saturated.split (canonical.indistinct sourceAdmitted) split)
        exact ⟨targetAdmitted, (partsListed _ sourceListed kind _ member).1⟩
      · obtain ⟨-, targetAdmitted, member⟩ := listing.complete canonAdmitted canonIdempotent
          (saturated.split (canonical.indistinct sourceAdmitted) split)
        exact ⟨targetAdmitted, (partsListed _ sourceListed kind _ member).2⟩

/-- **A closed parts region decides every behavioural formula with parts** at the admitted terms whose canonical
forms it lists, both ways. -/
theorem parts_check_iff (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    (closed : partsRegion relEnv language fuel canon domain presentations listing region = true) {formula : Formula 0}
    (fragment : formula.behaviouralParts = true) {index : Fin region.length} {term : Pattern}
    (admitted : domain term = true) (listed : canon term = region[index]) :
    (partsExploration relEnv language fuel canon domain presentations listing region).check formula index = true ↔
      (referenceStructure relEnv language reading).sat Env.closed formula term := by
  have allAdmitted : ∀ other, PartsReached relEnv language reading term other → domain other = true := fun _ reached =>
    (partsReached_admitted canonical coherent.plain closed admitted (listed ▸ List.getElem_mem index.2) reached).1
  have regionSide := (partsRegionMorphism canonical coherent closed).sat_iff formula fragment
    (StepMorphism.envPreimage_closed _) index
  have canonSide := (canonPartsMorphism canonical allAdmitted).sat_iff formula fragment
    (StepMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  have reachSide := (partsReachableMorphism (relEnv := relEnv) (language := language) (reading := reading)
    term).sat_iff formula fragment
    (StepMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  rw [FiniteStructure.check_iff]
  refine regionSide.trans (Iff.trans ?_ (canonSide.symm.trans reachSide))
  show (canonicalPartsStructure relEnv language canon domain reading).sat Env.closed formula region[index] ↔
    (canonicalPartsStructure relEnv language canon domain reading).sat Env.closed formula (canon term)
  rw [listed]

/-! ## Growing a parts region -/

variable (relEnv language fuel canon presentations listing)

/-- What a term adds to a parts region: the canonical forms of its listed successors when it is a state, and the
listed parts of its splits. -/
abbrev nextParts (term : Pattern) : List Pattern :=
  nextCanonical relEnv language fuel canon presentations term reading.rules ++
    collKinds.flatMap fun kind => (listing.splits term kind).flatMap fun pair => [pair.1, pair.2]

/-- Grow a parts region from a term, the term's canonical form first. -/
def growParts (term : Pattern) : ℕ → List Pattern
  | 0 => [canon term]
  | rounds + 1 =>
    let earlier := growParts term rounds
    addNew earlier (earlier.flatMap (nextParts relEnv language fuel canon presentations listing))

theorem growParts_first (term : Pattern) :
    ∀ rounds, ∃ rest, growParts relEnv language fuel canon presentations listing term rounds = canon term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := growParts_first term rounds
    obtain ⟨extra, extended⟩ := addNew_extends (growParts relEnv language fuel canon presentations listing term rounds)
      ((growParts relEnv language fuel canon presentations listing term rounds).flatMap
        (nextParts relEnv language fuel canon presentations listing))
    refine ⟨rest ++ extra, ?_⟩
    simp only [growParts]
    rw [extended, same, List.cons_append]

theorem growParts_length_pos (term : Pattern) (rounds : ℕ) :
    0 < (growParts relEnv language fuel canon presentations listing term rounds).length := by
  obtain ⟨rest, same⟩ := growParts_first relEnv language fuel canon presentations listing term rounds
  rw [same]
  exact Nat.succ_pos _

variable (domain)

/-- **Decide a behavioural formula with parts at a term modulo the equations**: the exact verdict when the grown
parts region closes, nothing otherwise. -/
def decideParts (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  if domain term && partsRegion relEnv language fuel canon domain presentations listing
    (growParts relEnv language fuel canon presentations listing term rounds) then
    some ((partsExploration relEnv language fuel canon domain presentations listing
      (growParts relEnv language fuel canon presentations listing term rounds)).check
      formula ⟨0, growParts_length_pos relEnv language fuel canon presentations listing term rounds⟩)
  else none

variable {relEnv language fuel canon domain presentations listing}

theorem growParts_zero (term : Pattern) (rounds : ℕ) :
    (growParts relEnv language fuel canon presentations listing term rounds)[(⟨0,
      growParts_length_pos relEnv language fuel canon presentations listing term rounds⟩ :
        Fin (growParts relEnv language fuel canon presentations listing term rounds).length)] = canon term := by
  obtain ⟨rest, same⟩ := growParts_first relEnv language fuel canon presentations listing term rounds
  simp only [Fin.getElem_fin]
  simp [same]

/-- **A verdict from a closed parts region is exact.** -/
theorem decideParts_sound (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    {formula : Formula 0} (fragment : formula.behaviouralParts = true) {term : Pattern} {rounds : ℕ}
    {verdict : Bool}
    (decided : decideParts relEnv language fuel canon domain presentations listing formula term rounds = some verdict) :
    (verdict = true ↔ (referenceStructure relEnv language reading).sat Env.closed formula term) := by
  unfold decideParts at decided
  split at decided
  · rename_i checked
    obtain ⟨admitted, closed⟩ := Bool.and_eq_true_iff.mp checked
    cases decided
    have listed := growParts_zero (relEnv := relEnv) (language := language) (fuel := fuel) (canon := canon)
      (presentations := presentations) (listing := listing) term rounds
    exact parts_check_iff canonical coherent closed fragment admitted listed.symm
  · cases decided


/-! ## Equation-free languages: the cuts of a collection -/

/-- **The cuts of a list**: its ways of being written `left ++ right`. -/
def cuts {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | head :: tail => ([], head :: tail) :: (cuts tail).map fun pair => (head :: pair.1, pair.2)

theorem mem_cuts {α : Type} : ∀ (list left right : List α), (left, right) ∈ cuts list ↔ left ++ right = list
  | [], left, right => by
    simp only [cuts, List.mem_singleton, Prod.mk.injEq, List.append_eq_nil_iff]
  | head :: tail, left, right => by
    simp only [cuts, List.mem_cons, Prod.mk.injEq, List.mem_map, Prod.exists]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨first, second, member, rfl, rfl⟩)
      · rfl
      · rw [List.cons_append, (mem_cuts tail first second).mp member]
    · intro same
      cases left with
      | nil => exact Or.inl ⟨rfl, same⟩
      | cons first rest =>
        rw [List.cons_append, List.cons.injEq] at same
        obtain ⟨rfl, rest'⟩ := same
        exact Or.inr ⟨rest, right, (mem_cuts tail rest right).mpr rest', rfl, rfl⟩

theorem isObjectPatternList_append : ∀ (first second : List Pattern),
    isObjectPatternList (first ++ second) = (isObjectPatternList first && isObjectPatternList second)
  | [], _ => by simp [isObjectPatternList]
  | head :: tail, second => by
    simp only [List.cons_append, isObjectPatternList, isObjectPatternList_append tail second, Bool.and_assoc]

/-- **The splits of an equation-free collection**: the two parts of each cut. -/
def cutSplits : Pattern → CollType → List (Pattern × Pattern)
  | .collection kind' elements none, kind =>
    if kind' = kind then (cuts elements).map fun pair => (.collection kind pair.1 none, .collection kind pair.2 none)
    else []
  | _, _ => []

/-- Whether a term is the empty collection of a kind. -/
def isEmptyCollection : Pattern → CollType → Bool
  | .collection kind' [] none, kind => kind' == kind
  | _, _ => false

theorem isEmptyCollection_iff (term : Pattern) (kind : CollType) :
    isEmptyCollection term kind = true ↔ term = .collection kind [] none := by
  cases term with
  | collection kind' elements rest =>
    rcases elements with _ | ⟨_, _⟩ <;> rcases rest with _ | _ <;> simp [isEmptyCollection]
  | bvar _ | fvar _ | apply _ _ | lambda _ _ | multiLambda _ _ _ | subst _ _ => simp [isEmptyCollection]

theorem mem_cutSplits {term : Pattern} {kind : CollType} {pair : Pattern × Pattern} :
    pair ∈ cutSplits term kind ↔ ∃ left right, term = .collection kind (left ++ right) none ∧
      pair = (.collection kind left none, .collection kind right none) := by
  cases term with
  | collection kind' elements rest =>
    rcases rest with _ | _
    · simp only [cutSplits]
      split
      · rename_i same
        subst same
        simp only [List.mem_map, Prod.exists, Pattern.collection.injEq, true_and, and_true]
        constructor
        · rintro ⟨left, right, member, rfl⟩
          exact ⟨left, right, ((mem_cuts elements left right).mp member).symm, rfl⟩
        · rintro ⟨left, right, rfl, rfl⟩
          exact ⟨left, right, (mem_cuts _ left right).mpr rfl, rfl⟩
      · rename_i differ
        simp only [List.not_mem_nil, false_iff, not_exists, not_and]
        intro _ _ same
        exact absurd (Pattern.collection.inj same).1 differ
    · simp [cutSplits]
  | bvar _ | fvar _ | apply _ _ | lambda _ _ | multiLambda _ _ _ | subst _ _ => simp [cutSplits]

/-- **An equation-free language lists the cuts of its collections**: with no equations, a collection splits exactly
at its cuts. -/
def identityParts (free : language.isEquationFree = true) :
    PartsListing relEnv language id fun term => isObjectPattern term where
  splits := cutSplits
  empty := isEmptyCollection
  complete := by
    intro state kind first second admitted _ split
    obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
    have same := (objectEquivalent_iff_eq_of_isEquationFree free).mp equivalent
    subst same
    simp only [isObjectPattern, Option.isNone_none, isObjectPatternList_append, Bool.true_and, Bool.and_eq_true]
      at admitted
    exact ⟨by simpa [isObjectPattern] using admitted.1, by simpa [isObjectPattern] using admitted.2,
      mem_cutSplits.mpr ⟨left, right, rfl, rfl⟩⟩
  sound := by
    intro state kind pair admitted _ member
    obtain ⟨left, right, rfl, rfl⟩ := mem_cutSplits.mp member
    have objects := admitted
    simp only [isObjectPattern, Option.isNone_none, isObjectPatternList_append, Bool.true_and, Bool.and_eq_true]
      at objects
    exact ⟨_, _, ⟨admitted, left, right, Relation.EqvGen.refl _, rfl, rfl⟩,
      by simpa [isObjectPattern] using objects.1, by simpa [isObjectPattern] using objects.2, rfl, rfl⟩
  empty_iff := by
    intro state kind admitted _
    rw [isEmptyCollection_iff]
    constructor
    · rintro rfl
      exact ⟨admitted, Relation.EqvGen.refl _⟩
    · rintro ⟨-, equivalent⟩
      exact (objectEquivalent_iff_eq_of_isEquationFree free).mp equivalent

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
