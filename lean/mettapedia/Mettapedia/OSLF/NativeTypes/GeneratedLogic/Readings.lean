import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions

/-!
# Readings: a language's rules fired at a chosen presentation

A language's rules can be read through a choice of presentation. Each state is written in a chosen
presentation of the same value, the rules fire there, and their results are taken to canonical form. A set,
for instance, can be written with each member once, so that a member a rule matches is consumed, or with every
member copied, so that a matched member stays.

- **The structure of a reading** (`readingStructure`): states, with the steps the rules take at the presentation
  of each, to canonical targets; an object term names its canonical form.
- **A closed region of a reading** (`readingRegion`): canonical states without repetition, each completely listed
  at its presentation, with the canonical forms of its listed successors in the region. Its inclusion is a step
  morphism into the reading's structure (`readingMorphism`), so the finite evaluator's verdict on it is exact for
  every behavioural formula, rule and site labels included (`reading_check_iff`).
- **Deciding** (`decideReading`): grow such a region from a term's canonical form and evaluate. A verdict is exact
  at the canonical form (`decideReading_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (present canon : Pattern → Pattern)

/-! ## The structure of a reading -/

/-- **The structure of a reading**: states, with the steps the rules take at the presentation of each, to
canonical targets; an object term names its canonical form. -/
def readingStructure : NativeStructure Pattern where
  step source label target := IsState source ∧ IsState target ∧ ∃ witness contractum,
    StepValid relEnv language (present source) witness contractum ∧ label.admits witness = true ∧
      canon contractum = target
  built _ _ _ := False
  split _ _ _ _ := False
  empty _ _ := False
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ _ := False
  named element term := IsObject term ∧ canon term = element
  same first second := first = second
  apply inner _ := inner

/-! ## Closed regions -/

/-- What a state adds to a region: the canonical forms of the steps listed at its presentation. -/
abbrev nextReading (state : Pattern) : List Pattern :=
  if isStateBool state then (stepsAt relEnv language fuel (present state)).map (canon ·.2) else []

/-- Grow a region from a term: its canonical form first, then the canonical forms of the listed successors of
states, without repetition. -/
def growReading (term : Pattern) : ℕ → List Pattern
  | 0 => [canon term]
  | rounds + 1 =>
    let earlier := growReading term rounds
    addNew earlier (earlier.flatMap (nextReading relEnv language fuel present canon))

variable (region : List Pattern)

/-- **A closed region of a reading**: canonical states without repetition, each completely listed at its
presentation, with the canonical forms of its listed successors in the region. -/
def readingRegion : Bool :=
  decide region.Nodup && region.all fun term => canon term == term &&
    (!isStateBool term ||
      (enough relEnv language fuel (present term) &&
        (stepsAt relEnv language fuel (present term)).all fun entry => canon entry.2 ∈ region))

/-- **The region as a finite structure**: its steps lead to the canonical forms of the steps listed at each
state's presentation. -/
def readingExploration : FiniteStructure (Fin region.length) where
  elements := List.finRange region.length
  complete := List.mem_finRange
  step source label target := isStateBool region[source] && isStateBool region[target] &&
    (stepsAt relEnv language fuel (present region[source])).any fun entry =>
      canon entry.2 == region[target] && label.admits entry.1
  built _ _ _ := false
  split _ _ _ _ := false
  empty _ _ := false
  single _ _ _ := false
  body _ _ := false
  multiBody _ _ _ := false
  bound _ _ := false
  typed _ _ := false
  named element term := isObjectPattern term && canon term == region[element]
  same first second := decide (first = second)
  apply inner _ := inner

variable {relEnv language fuel present canon region}

theorem readingRegion_parts (closed : readingRegion relEnv language fuel present canon region = true) :
    region.Nodup ∧ ∀ term ∈ region, canon term = term ∧
      (isStateBool term = true → enough relEnv language fuel (present term) = true ∧
        ∀ entry ∈ stepsAt relEnv language fuel (present term), canon entry.2 ∈ region) := by
  simp only [readingRegion, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at closed
  refine ⟨closed.1, fun term member => ⟨(closed.2 term member).1, fun state => ?_⟩⟩
  rcases (closed.2 term member).2 with notState | listed
  · rw [notState] at state
    cases state
  · exact ⟨listed.1, listed.2⟩

/-- **A closed region's inclusion is a step morphism into the reading's structure.** -/
def readingMorphism (closed : readingRegion relEnv language fuel present canon region = true) :
    StepMorphism (readingExploration relEnv language fuel present canon region).native
      (readingStructure relEnv language present canon) where
  map index := region[index]
  step := by
    intro source label target checked
    change (_ && _ && _) = true at checked
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨sourceState, targetState⟩, entry, member, same, admits⟩ := checked
    exact ⟨by simpa [isStateBool] using sourceState, by simpa [isStateBool] using targetState, entry.1, entry.2,
      stepValid_of_mem_stepsAt relEnv language member, admits, same⟩
  stepBack := by
    intro source label target' step
    obtain ⟨sourceState, targetState, witness, contractum, valid, admits, reached⟩ := step
    obtain ⟨-, members⟩ := readingRegion_parts closed
    obtain ⟨-, listing⟩ := members _ (List.getElem_mem source.2)
    obtain ⟨enoughAt, successors⟩ := listing (isStateBool_of_isState sourceState)
    have member := mem_stepsAt_of_enough enoughAt valid
    obtain ⟨target, isTarget⟩ := exists_index (successors _ member)
    refine ⟨target, ?_, isTarget.trans reached⟩
    show (_ && _ && _) = true
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
    exact ⟨⟨isStateBool_of_isState sourceState, isStateBool_of_isState (by rw [isTarget, reached]; exact targetState)⟩,
      (witness, contractum), member, isTarget.symm, admits⟩
  sameIff first second := by
    change decide (first = second) = true ↔ region[first] = region[second]
    rw [decide_eq_true_iff]
    constructor
    · rintro rfl
      rfl
    · intro same
      exact Fin.ext ((List.Nodup.getElem_inj_iff (readingRegion_parts closed).1).mp same)
  namedIff element term := by
    change (isObjectPattern term && canon term == region[element]) = true ↔ _
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact Iff.rfl

/-- **A closed region of a reading decides every behavioural formula** at its states, labels included. -/
theorem reading_check_iff (closed : readingRegion relEnv language fuel present canon region = true)
    {formula : Formula 0} (behavioural : formula.behaviouralForward = true) (index : Fin region.length) :
    (readingExploration relEnv language fuel present canon region).check formula index = true ↔
      (readingStructure relEnv language present canon).sat Env.closed formula region[index] := by
  rw [FiniteStructure.check_iff]
  exact (readingMorphism closed).sat_iff formula behavioural (StepMorphism.envPreimage_closed _) index

/-! ## Deciding -/

theorem growReading_first (term : Pattern) :
    ∀ rounds, ∃ rest, growReading relEnv language fuel present canon term rounds = canon term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := growReading_first term rounds
    obtain ⟨extra, extended⟩ := addNew_extends (growReading relEnv language fuel present canon term rounds)
      ((growReading relEnv language fuel present canon term rounds).flatMap
        (nextReading relEnv language fuel present canon))
    refine ⟨rest ++ extra, ?_⟩
    simp only [growReading]
    rw [extended, same, List.cons_append]

theorem growReading_length_pos (term : Pattern) (rounds : ℕ) :
    0 < (growReading relEnv language fuel present canon term rounds).length := by
  obtain ⟨rest, same⟩ := growReading_first (relEnv := relEnv) (language := language) (fuel := fuel)
    (present := present) (canon := canon) term rounds
  rw [same]
  exact Nat.succ_pos _

variable (relEnv language fuel present canon)

/-- **Decide a behavioural formula in a reading** at a term's canonical form: the exact verdict when the grown
region closes, nothing otherwise. -/
def decideReading (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  if readingRegion relEnv language fuel present canon (growReading relEnv language fuel present canon term rounds)
  then
    some ((readingExploration relEnv language fuel present canon
      (growReading relEnv language fuel present canon term rounds)).check
      formula ⟨0, growReading_length_pos term rounds⟩)
  else none

variable {relEnv language fuel present canon}

/-- **A verdict of a reading is exact** at the term's canonical form. -/
theorem decideReading_sound {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    {term : Pattern} {rounds : ℕ} {verdict : Bool}
    (decided : decideReading relEnv language fuel present canon formula term rounds = some verdict) :
    (verdict = true ↔ (readingStructure relEnv language present canon).sat Env.closed formula (canon term)) := by
  unfold decideReading at decided
  split at decided
  · rename_i closed
    cases decided
    obtain ⟨rest, same⟩ := growReading_first (relEnv := relEnv) (language := language) (fuel := fuel)
      (present := present) (canon := canon) term rounds
    have first : (growReading relEnv language fuel present canon term rounds)[(⟨0,
        growReading_length_pos term rounds⟩ : Fin (growReading relEnv language fuel present canon term rounds).length)] =
        canon term := by
      simp only [Fin.getElem_fin]
      simp [same]
    rw [← first]
    exact reading_check_iff closed behavioural _
  · cases decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
