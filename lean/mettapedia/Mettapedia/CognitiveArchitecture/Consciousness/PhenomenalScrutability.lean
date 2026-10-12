import Mettapedia.Logic.Propositions.ComponentBases
import Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalContent

/-!
# Component scrutability of explicitly indexed phenomenal descriptions

This interpretation separates a physical property, the existing independent
phenomenal-content facets, and a subject/time center.  Additional-object
counts provide genuinely distinguishable extensions of a scenario that still
verify its current component truths.  A bounding totality clause closes those
extensions only relative to this particular sentence language.

The motivating distinction is Chalmers's PQI base without T for positive
truths (*Constructing the World*, 2012, ch. 3 §1;
https://consc.net/constructing-the-world/).  The interpretation below is a
limited semantic reconstruction, not his general scrutability thesis.

The phenomenal sentences interpret the existing structural propositions of
`PhenomenalContent`, not felt intensities or an assignment of consciousness.
The physical component is the authored vocabulary of this model, not a claim
to an exhaustive physical description of reality.  Scenario extensions are
epistemic alternatives; they are not physical creation operations.

Categorical reports use the existing partial-section category.  Exact
sentence descriptions agree precisely when the chosen language cannot
distinguish the scenarios.  Pain-only reports can agree while the distinct
global-suffering facet remains different.  Subject and time indexicals remain
explicit rather than being inferred from a report's values.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalScrutability

open Mettapedia.Logic.Propositions
open Mettapedia.CategoryTheory


/-- A scenario contains real interpretive distinctions in every component. -/
structure Scenario where
  physical : Bool
  content : PhenomenalContent.Content
  subject : Bool
  now : Nat
  extraCount : Nat

/-- Persons, moments and physical locations remain different kinds of thing. -/
inductive Thing where
  | person (subject : Bool)
  | moment (time : Nat)
  | site (location : Bool)
  deriving DecidableEq

inductive Name where
  | self
  | now
  | person (subject : Bool)
  | moment (time : Nat)
  | site (location : Bool)
  deriving DecidableEq

inductive Predicate where
  | physical (value : Bool)
  | phenomenal (facet : PhenomenalContent.Facet) (present : Bool)
  | extra (index : Nat)
  | extraBound (upper : Nat)
  deriving DecidableEq

/-- A named polarity of a proposition is a truth report, not a signed
affective magnitude or a claim of exhaustiveness about phenomenal content. -/
def Reported (present : Bool) (proposition : Prop) : Prop :=
  match present with
  | true => proposition
  | false => ¬ proposition

def referent : Name -> Scenario -> Thing
  | .self, scenario => .person scenario.subject
  | .now, scenario => .moment scenario.now
  | .person subject, _ => .person subject
  | .moment time, _ => .moment time
  | .site location, _ => .site location

/-- The interpretation varies over both scenarios and worlds.  Indexical
names select the actual center, while physical and phenomenal predicates are
evaluated at the world under consideration. -/
def interpretation : Interpretation Scenario Scenario Thing Name Predicate where
  world := id
  referent := referent
  property
    | .physical value, _, world =>
        {thing | thing = .site false /\ world.physical = value}
    | .phenomenal facet present, actual, world =>
        {thing | thing = .person actual.subject /\
          Reported present (PhenomenalContent.statement world.content facet)}
    | .extra index, _, world =>
        {thing | thing = .site true /\ index < world.extraCount}
    | .extraBound upper, _, world =>
        {thing | thing = .site true /\ world.extraCount ≤ upper}

abbrev Statement := Sentence Name Predicate

def physicalSentence (value : Bool) : Statement := .pred (.physical value) (.site false)
def phenomenalSentence (facet : PhenomenalContent.Facet) (present : Bool) : Statement :=
  .pred (.phenomenal facet present) .self
def subjectSentence (subject : Bool) : Statement := .ident .self (.person subject)
def timeSentence (time : Nat) : Statement := .ident .now (.moment time)
def extraSentence (index : Nat) : Statement := .pred (.extra index) (.site true)
def boundSentence (upper : Nat) : Statement := .pred (.extraBound upper) (.site true)

@[simp]
theorem physical_primary (scenario : Scenario) (value : Bool) :
    scenario ∈ interpretation.primary (physicalSentence value) ↔ scenario.physical = value := by
  simp [Interpretation.primary, Interpretation.TrueAt, Form.Holds,
    physicalSentence, interpretation, referent]

@[simp]
theorem phenomenal_primary (scenario : Scenario) (facet : PhenomenalContent.Facet) (present : Bool) :
    scenario ∈ interpretation.primary (phenomenalSentence facet present) ↔
      Reported present (PhenomenalContent.statement scenario.content facet) := by
  simp [Interpretation.primary, Interpretation.TrueAt, Form.Holds,
    phenomenalSentence, interpretation, referent]

@[simp]
theorem subject_primary (scenario : Scenario) (subject : Bool) :
    scenario ∈ interpretation.primary (subjectSentence subject) ↔ scenario.subject = subject := by
  simp [Interpretation.primary, Interpretation.TrueAt, Form.Holds,
    subjectSentence, interpretation, referent]

@[simp]
theorem time_primary (scenario : Scenario) (time : Nat) :
    scenario ∈ interpretation.primary (timeSentence time) ↔ scenario.now = time := by
  simp [Interpretation.primary, Interpretation.TrueAt, Form.Holds,
    timeSentence, interpretation, referent]

@[simp]
theorem extra_primary (scenario : Scenario) (index : Nat) :
    scenario ∈ interpretation.primary (extraSentence index) ↔ index < scenario.extraCount := by
  simp [Interpretation.primary, Interpretation.TrueAt, Form.Holds,
    extraSentence, interpretation, referent]

@[simp]
theorem bound_primary (scenario : Scenario) (upper : Nat) :
    scenario ∈ interpretation.primary (boundSentence upper) ↔ scenario.extraCount ≤ upper := by
  simp [Interpretation.primary, Interpretation.TrueAt, Form.Holds,
    boundSentence, interpretation, referent]

/-- The physical vocabulary includes positive presence claims for every
additional index; it does not include its own upper bound. -/
def candidates : ComponentBases Statement where
  physical := {statement | (exists value, statement = physicalSentence value) ∨
    exists index, statement = extraSentence index}
  phenomenal := {statement | exists facet present, statement = phenomenalSentence facet present}
  indexical := {statement | (exists subject, statement = subjectSentence subject) ∨
    exists time, statement = timeSentence time}

def observationVocabulary : Set Statement := candidates.joined

/-- Selecting actual truths retains all three component identities. -/
def componentTruths (actual : Scenario) : ComponentBases Statement :=
  candidates.filter (interpretation.TrueIn actual)

def pqibase (actual : Scenario) : Set Statement := (componentTruths actual).joined

theorem pqibase_eq_truthsIn (actual : Scenario) :
    pqibase actual = interpretation.truthsIn actual observationVocabulary :=
  (interpretation.truthsIn_component_join actual candidates).symm

@[simp]
theorem mem_pqibase (actual : Scenario) (statement : Statement) :
    statement ∈ pqibase actual ↔
      statement ∈ observationVocabulary /\ actual ∈ interpretation.primary statement := by
  rw [pqibase_eq_truthsIn]
  rfl

theorem physical_in_vocabulary (value : Bool) : physicalSentence value ∈ observationVocabulary :=
  Or.inl (Or.inl (Or.inl ⟨value, rfl⟩))

theorem phenomenal_in_vocabulary (facet : PhenomenalContent.Facet) (present : Bool) :
    phenomenalSentence facet present ∈ observationVocabulary :=
  Or.inl (Or.inr ⟨facet, present, rfl⟩)

theorem subject_in_vocabulary (subject : Bool) : subjectSentence subject ∈ observationVocabulary :=
  Or.inr (Or.inl ⟨subject, rfl⟩)

theorem time_in_vocabulary (time : Nat) : timeSentence time ∈ observationVocabulary :=
  Or.inr (Or.inr ⟨time, rfl⟩)

theorem extra_in_vocabulary (index : Nat) : extraSentence index ∈ observationVocabulary :=
  Or.inl (Or.inl (Or.inr ⟨index, rfl⟩))

/-- Every scenario supplies inhabited true P, Q and I components.  The Q
component uses a real facet and a justified truth polarity. -/
theorem all_component_truths_inhabited (actual : Scenario) :
    (componentTruths actual).physical.Nonempty /\
    (componentTruths actual).phenomenal.Nonempty /\
    (componentTruths actual).indexical.Nonempty := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨physicalSentence actual.physical, Or.inl ⟨actual.physical, rfl⟩,
      (physical_primary actual actual.physical).2 rfl⟩
  · by_cases pain : PhenomenalContent.statement actual.content .pain
    · exact ⟨phenomenalSentence .pain true, ⟨.pain, true, rfl⟩,
        (phenomenal_primary actual .pain true).2 pain⟩
    · exact ⟨phenomenalSentence .pain false, ⟨.pain, false, rfl⟩,
        (phenomenal_primary actual .pain false).2 pain⟩
  · exact ⟨subjectSentence actual.subject, Or.inl ⟨actual.subject, rfl⟩,
      (subject_primary actual actual.subject).2 rfl⟩

/-- The actual scenario verifies its selected component base, so its
information state is nonempty. -/
theorem actual_in_information_state (actual : Scenario) :
    actual ∈ interpretation.stateOf (pqibase actual) :=
  fun statement member => ((mem_pqibase actual statement).1 member).2

def extend (scenario : Scenario) : Scenario :=
  {scenario with extraCount := scenario.extraCount + 1}

/-- Added presence preserves every previously accepted component truth;
the derivation inspects the actual interpretation of all component forms. -/
theorem extend_preserves_observations (actual : Scenario) :
    interpretation.Extends observationVocabulary (extend actual) actual := by
  intro statement inVocabulary holds
  rcases inVocabulary with ((physical | phenomenal) | indexical)
  · rcases physical with ⟨value, rfl⟩ | ⟨index, rfl⟩
    · simpa [extend] using holds
    · exact (extra_primary (extend actual) index).2
        (Nat.lt_succ_of_lt ((extra_primary actual index).1 holds))
  · rcases phenomenal with ⟨facet, present, rfl⟩
    simpa [extend] using holds
  · rcases indexical with ⟨subject, rfl⟩ | ⟨time, rfl⟩ <;>
      simpa [extend] using holds

/-- The extension changes a sentence despite retaining the component truths. -/
theorem extend_is_distinguishable (actual : Scenario) :
    ¬ interpretation.Indiscernible actual (extend actual) := by
  intro same
  have extensionTruth : extend actual ∈ interpretation.primary (extraSentence actual.extraCount) :=
    (extra_primary (extend actual) actual.extraCount).2 (Nat.lt_succ_self _)
  have oldTruth := (same (extraSentence actual.extraCount)).2 extensionTruth
  exact Nat.lt_irrefl _ ((extra_primary actual actual.extraCount).1 oldTruth)

theorem open_observation_space : interpretation.OpenEnded observationVocabulary :=
  fun actual => ⟨extend actual, extend_preserves_observations actual,
    extend_is_distinguishable actual⟩

/-- PQI component truths alone do not settle all truths of this language. -/
theorem pqibase_not_scrutability_base (actual : Scenario) :
    ¬ interpretation.ScrutabilityBase actual (pqibase actual) := by
  rw [pqibase_eq_truthsIn]
  exact interpretation.not_scrutabilityBase_of_open observationVocabulary
    open_observation_space actual

theorem missing_totality (actual : Scenario) :
    ¬ interpretation.ThatsAll observationVocabulary actual :=
  fun closes => extend_is_distinguishable actual
    (closes (extend actual) (extend_preserves_observations actual))

/-- A local positive query remains persistent relative to the declared
observation vocabulary; this does not certify a felt experience. -/
theorem local_pain_persistent :
    interpretation.Persistent observationVocabulary (phenomenalSentence .pain true) :=
  interpretation.persistent_of_mem observationVocabulary
    (phenomenal_in_vocabulary .pain true)

theorem local_pain_settled_iff (actual : Scenario) :
    interpretation.ScrutableFrom (pqibase actual) (phenomenalSentence .pain true) ↔
      PhenomenalContent.statement actual.content .pain := by
  rw [pqibase_eq_truthsIn]
  exact (interpretation.scrutableFrom_positiveTruths_iff_trueIn observationVocabulary
    local_pain_persistent actual).trans (phenomenal_primary actual .pain true)

theorem local_pain_information_query (actual : Scenario) :
    (interpretation.informationWorldModel.extract (interpretation.stateOf (pqibase actual))
      (phenomenalSentence .pain true)).settledTrue ↔ PhenomenalContent.statement actual.content .pain :=
  (interpretation.settledTrue_stateOf_iff (pqibase actual)
    (phenomenalSentence .pain true)).trans (local_pain_settled_iff actual)

/-! ## What the component base fixes, and a genuine totality clause -/

/-- Compatibility with the PQI truths has an exact componentwise reading.
Each facet is retained independently.  The additional-object component
provides only a lower bound until a totality clause is supplied. -/
theorem pqi_verification_iff (actual alternative : Scenario) :
    alternative ∈ interpretation.stateOf (pqibase actual) ↔
      actual.physical = alternative.physical /\
      (forall facet, PhenomenalContent.statement actual.content facet ↔
        PhenomenalContent.statement alternative.content facet) /\
      actual.subject = alternative.subject /\ actual.now = alternative.now /\
      actual.extraCount ≤ alternative.extraCount := by
  constructor
  · intro verifies
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ((physical_primary alternative actual.physical).1
        (verifies (physicalSentence actual.physical) ((mem_pqibase actual _).2
          ⟨physical_in_vocabulary actual.physical,
            (physical_primary actual actual.physical).2 rfl⟩))).symm
    · intro facet
      classical
      by_cases actualFacet : PhenomenalContent.statement actual.content facet
      · have alternativeFacet := (phenomenal_primary alternative facet true).1
          (verifies (phenomenalSentence facet true) ((mem_pqibase actual _).2
            ⟨phenomenal_in_vocabulary facet true,
              (phenomenal_primary actual facet true).2 actualFacet⟩))
        exact ⟨fun _ => alternativeFacet, fun _ => actualFacet⟩
      · have notAlternative := (phenomenal_primary alternative facet false).1
          (verifies (phenomenalSentence facet false) ((mem_pqibase actual _).2
            ⟨phenomenal_in_vocabulary facet false,
              (phenomenal_primary actual facet false).2 actualFacet⟩))
        exact ⟨fun holds => (actualFacet holds).elim,
          fun holds => (notAlternative holds).elim⟩
    · exact ((subject_primary alternative actual.subject).1
        (verifies (subjectSentence actual.subject) ((mem_pqibase actual _).2
          ⟨subject_in_vocabulary actual.subject,
            (subject_primary actual actual.subject).2 rfl⟩))).symm
    · exact ((time_primary alternative actual.now).1
        (verifies (timeSentence actual.now) ((mem_pqibase actual _).2
          ⟨time_in_vocabulary actual.now, (time_primary actual actual.now).2 rfl⟩))).symm
    · by_contra notBound
      have actualPresence : alternative.extraCount < actual.extraCount :=
        Nat.lt_of_not_ge notBound
      have impossiblePresence := (extra_primary alternative alternative.extraCount).1
        (verifies (extraSentence alternative.extraCount) ((mem_pqibase actual _).2
          ⟨extra_in_vocabulary alternative.extraCount,
            (extra_primary actual alternative.extraCount).2 actualPresence⟩))
      exact Nat.lt_irrefl _ impossiblePresence
  · rintro ⟨physical, facets, subject, time, count⟩ statement member
    rcases (mem_pqibase actual statement).1 member with ⟨inVocabulary, holds⟩
    rcases inVocabulary with ((physicalForm | phenomenalForm) | indexicalForm)
    · rcases physicalForm with ⟨value, rfl⟩ | ⟨index, rfl⟩
      · exact (physical_primary alternative value).2
          (physical.symm.trans ((physical_primary actual value).1 holds))
      · exact (extra_primary alternative index).2
          (Nat.lt_of_lt_of_le ((extra_primary actual index).1 holds) count)
    · rcases phenomenalForm with ⟨facet, present, rfl⟩
      apply (phenomenal_primary alternative facet present).2
      have reported := (phenomenal_primary actual facet present).1 holds
      cases present with
      | false => exact fun alternativeFacet => reported ((facets facet).2 alternativeFacet)
      | true => exact (facets facet).1 reported
    · rcases indexicalForm with ⟨person, rfl⟩ | ⟨moment, rfl⟩
      · exact (subject_primary alternative person).2
          (subject.symm.trans ((subject_primary actual person).1 holds))
      · exact (time_primary alternative moment).2
          (time.symm.trans ((time_primary actual moment).1 holds))

/-- Name interpretation respects the declared subject and time center. -/
theorem referents_agree (first second : Scenario)
    (subject : first.subject = second.subject) (time : first.now = second.now)
    (name : Name) : referent name first = referent name second := by
  cases name <;> simp [referent, subject, time]

/-- Agreement on the actual atomic observations suffices for all logical
forms, using the library's existing compositional interpretation law.  It
does not identify the underlying event systems or subject occurrences. -/
theorem indiscernible_of_observable_agreement (first second : Scenario)
    (physical : first.physical = second.physical)
    (facets : forall facet, PhenomenalContent.statement first.content facet ↔
      PhenomenalContent.statement second.content facet)
    (subject : first.subject = second.subject) (time : first.now = second.now)
    (count : first.extraCount = second.extraCount) :
    interpretation.Indiscernible first second := by
  intro statement
  apply Form.holds_congr
  · intro predicate name
    have sameName := referents_agree first second subject time name
    cases predicate with
    | physical value =>
        change (referent name first = .site false /\ first.physical = value) ↔
          (referent name second = .site false /\ second.physical = value)
        rw [sameName, physical]
    | phenomenal facet present =>
        change (referent name first = .person first.subject /\
            Reported present (PhenomenalContent.statement first.content facet)) ↔
          (referent name second = .person second.subject /\
            Reported present (PhenomenalContent.statement second.content facet))
        rw [sameName, subject]
        apply and_congr_right
        intro _
        cases present with
        | false => exact not_congr (facets facet)
        | true => exact facets facet
    | extra index =>
        change (referent name first = .site true /\ index < first.extraCount) ↔
          (referent name second = .site true /\ index < second.extraCount)
        rw [sameName, count]
    | extraBound upper =>
        change (referent name first = .site true /\ first.extraCount ≤ upper) ↔
          (referent name second = .site true /\ second.extraCount ≤ upper)
        rw [sameName, count]
  · intro left right
    change referent left first = referent right first ↔
      referent left second = referent right second
    rw [referents_agree first second subject time left,
      referents_agree first second subject time right]

/-- The totality sentence is a numerical upper bound, independently of the
scrutability conclusion.  It rules out additional admitted object indices. -/
def totalitySentence (actual : Scenario) : Statement := boundSentence actual.extraCount

def pqitBase (actual : Scenario) : Set Statement :=
  pqibase actual ∪ {totalitySentence actual}

/-- An admitted extension satisfying the explicit bound agrees on every
sentence of this interpretation.  This is a proved closure property rather
than a definition of totality as indiscernibility. -/
theorem totality_closes_extensions (actual alternative : Scenario)
    (extension : interpretation.Extends observationVocabulary alternative actual)
    (bound : alternative ∈ interpretation.primary (totalitySentence actual)) :
    interpretation.Indiscernible actual alternative := by
  have verifies : alternative ∈ interpretation.stateOf (pqibase actual) := by
    intro statement member
    rcases (mem_pqibase actual statement).1 member with ⟨candidate, holds⟩
    exact extension statement candidate holds
  rcases (pqi_verification_iff actual alternative).1 verifies with
    ⟨physical, facets, subject, time, lower⟩
  exact indiscernible_of_observable_agreement actual alternative physical facets subject time
    (Nat.le_antisymm lower ((bound_primary alternative actual.extraCount).1 bound))

/-- PQI together with the bounding clause forms a scrutability base for this
particular language.  The theorem gives no global PQI thesis, physical
completeness claim, or experiential adequacy guarantee. -/
theorem pqit_scrutability_base (actual : Scenario) :
    interpretation.ScrutabilityBase actual (pqitBase actual) := by
  apply (interpretation.scrutabilityBase_iff actual (pqitBase actual)).2
  constructor
  · intro statement member
    rcases member with pqi | bound
    · exact ((mem_pqibase actual statement).1 pqi).2
    · rcases bound with rfl
      exact (bound_primary actual actual.extraCount).2 (Nat.le_refl _)
  · intro alternative verifies
    apply totality_closes_extensions actual alternative
    · intro statement candidate holds
      exact verifies statement (Or.inl ((mem_pqibase actual statement).2 ⟨candidate, holds⟩))
    · exact verifies (totalitySentence actual) (Or.inr rfl)

theorem pqit_settles_true_sentences (actual : Scenario) (statement : Statement)
    (holds : actual ∈ interpretation.primary statement) :
    interpretation.ScrutableFrom (pqitBase actual) statement :=
  (pqit_scrutability_base actual).2 statement holds

/-! ## Exact descriptions and deliberately restricted reports -/

def sentenceDescription (scenario : Scenario) : PartialSections.View Statement Prop :=
  PartialSections.total (fun statement => scenario ∈ interpretation.primary statement)

def sentenceReport (observed : Set Statement) (scenario : Scenario) : PartialSections.View Statement Prop :=
  PartialSections.restrict observed (sentenceDescription scenario)

theorem sentence_description_eq_iff (first second : Scenario) :
    sentenceDescription first = sentenceDescription second ↔
      interpretation.Indiscernible first second := by
  constructor
  · intro same statement
    have assignments := PartialSections.total_injective same
    exact Iff.of_eq (congrFun assignments statement)
  · intro same
    apply PartialSections.View.ext
    · rfl
    · intro statement _ _
      exact propext (same statement)

def phenomenalDescription (scenario : Scenario) : PartialSections.View PhenomenalContent.Facet Prop :=
  PartialSections.total (fun facet => scenario ∈ interpretation.primary (phenomenalSentence facet true))

/-- Evaluated Q sentences agree with the existing structured content
description.  The vocabulary remains the declared four separate facets. -/
theorem phenomenal_description_agrees (scenario : Scenario) :
    phenomenalDescription scenario = PhenomenalContent.description scenario.content := by
  apply PartialSections.View.ext
  · rfl
  · intro facet _ _
    exact propext (phenomenal_primary scenario facet true)

def phenomenalReport (observed : Set PhenomenalContent.Facet) (scenario : Scenario) : PartialSections.View PhenomenalContent.Facet Prop :=
  PartialSections.restrict observed (phenomenalDescription scenario)

theorem phenomenal_report_agrees (observed : Set PhenomenalContent.Facet) (scenario : Scenario) :
    phenomenalReport observed scenario = PhenomenalContent.report observed scenario.content :=
  congrArg (PartialSections.restrict observed) (phenomenal_description_agrees scenario)

namespace Controls

def terminal : Scenario := ⟨true, PhenomenalContent.Controls.terminalPain, false, 0, 0⟩
def loop : Scenario := ⟨true, PhenomenalContent.Controls.separatingPainLoop, false, 0, 0⟩
def changedPhysical : Scenario := {terminal with physical := false}
def changedCenter : Scenario := {terminal with subject := true, now := 1}

/-- The same local report leaves the separate suffering dimension hidden. -/
theorem pain_report_same_suffering_different :
    phenomenalReport PhenomenalContent.Controls.painOnly terminal =
      phenomenalReport PhenomenalContent.Controls.painOnly loop /\
    terminal ∉ interpretation.primary (phenomenalSentence .globalSuffering true) /\
    loop ∈ interpretation.primary (phenomenalSentence .globalSuffering true) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phenomenal_report_agrees, phenomenal_report_agrees]
    exact PhenomenalContent.Controls.pain_only_reports_agree
  · exact fun suffering => PhenomenalContent.Controls.local_pain_without_global_suffering.2
      ((phenomenal_primary terminal .globalSuffering true).1 suffering)
  · exact (phenomenal_primary loop .globalSuffering true).2
      PhenomenalContent.Controls.separatingPainLoop_suffering

theorem full_sentence_descriptions_separate_suffering :
    sentenceDescription terminal ≠ sentenceDescription loop := by
  intro same
  have agrees := (sentence_description_eq_iff terminal loop).1 same
  exact pain_report_same_suffering_different.2.1
    ((agrees (phenomenalSentence .globalSuffering true)).2
      pain_report_same_suffering_different.2.2)

theorem local_pain_is_settled :
    interpretation.ScrutableFrom (pqibase terminal) (phenomenalSentence .pain true) :=
  (local_pain_settled_iff terminal).2 PhenomenalContent.Controls.local_pain_without_global_suffering.1

/-- Holding all physical and indexical observations fixed does not settle
the independently interpreted global-suffering facet.  This is a control on
this vocabulary, not an argument against richer physical descriptions. -/
theorem physical_indexical_do_not_settle_suffering :
    ¬ interpretation.ScrutableFrom
      ((componentTruths terminal).physical ∪ (componentTruths terminal).indexical)
      (.neg (phenomenalSentence .globalSuffering true)) := by
  intro scrutable
  have compatible : loop ∈ interpretation.stateOf
      ((componentTruths terminal).physical ∪ (componentTruths terminal).indexical) := by
    intro statement member
    rcases member with ⟨physicalForm, holds⟩ | ⟨indexicalForm, holds⟩
    · rcases physicalForm with ⟨value, rfl⟩ | ⟨index, rfl⟩
      · simpa [Interpretation.TrueIn, terminal, loop] using holds
      · simp [Interpretation.TrueIn, terminal] at holds
    · rcases indexicalForm with ⟨subject, rfl⟩ | ⟨time, rfl⟩ <;>
        simpa [Interpretation.TrueIn, terminal, loop] using holds
  have noSuffering := interpretation.scrutableFrom_iff.1 scrutable loop compatible
  exact noSuffering pain_report_same_suffering_different.2.2

/-- Phenomenal and centered observations do not determine the independent
physical property. -/
theorem phenomenal_indexical_do_not_settle_physical :
    ¬ interpretation.ScrutableFrom
      ((componentTruths terminal).phenomenal ∪ (componentTruths terminal).indexical)
      (physicalSentence true) := by
  intro scrutable
  have compatible : changedPhysical ∈ interpretation.stateOf
      ((componentTruths terminal).phenomenal ∪ (componentTruths terminal).indexical) := by
    intro statement member
    rcases member with ⟨phenomenalForm, holds⟩ | ⟨indexicalForm, holds⟩
    · rcases phenomenalForm with ⟨facet, present, rfl⟩
      simpa [Interpretation.TrueIn, terminal, changedPhysical] using holds
    · rcases indexicalForm with ⟨subject, rfl⟩ | ⟨time, rfl⟩ <;>
        simpa [Interpretation.TrueIn, terminal, changedPhysical] using holds
  have incompatible := interpretation.scrutableFrom_iff.1 scrutable changedPhysical compatible
  simp [changedPhysical] at incompatible

/-- Physical and phenomenal observations leave the subject/time center
undetermined.  The very same content has distinct centered alternatives. -/
theorem physical_phenomenal_do_not_settle_center :
    ¬ interpretation.ScrutableFrom
      ((componentTruths terminal).physical ∪ (componentTruths terminal).phenomenal)
      (subjectSentence false) /\
    ¬ interpretation.ScrutableFrom
      ((componentTruths terminal).physical ∪ (componentTruths terminal).phenomenal)
      (timeSentence 0) := by
  have compatible : changedCenter ∈ interpretation.stateOf
      ((componentTruths terminal).physical ∪ (componentTruths terminal).phenomenal) := by
    intro statement member
    rcases member with ⟨physicalForm, holds⟩ | ⟨phenomenalForm, holds⟩
    · rcases physicalForm with ⟨value, rfl⟩ | ⟨index, rfl⟩
      · simpa [Interpretation.TrueIn, terminal, changedCenter] using holds
      · simp [Interpretation.TrueIn, terminal] at holds
    · rcases phenomenalForm with ⟨facet, present, rfl⟩
      simpa [Interpretation.TrueIn, terminal, changedCenter] using holds
  constructor
  · intro scrutable
    have incompatible := interpretation.scrutableFrom_iff.1 scrutable changedCenter compatible
    simp [changedCenter] at incompatible
  · intro scrutable
    have incompatible := interpretation.scrutableFrom_iff.1 scrutable changedCenter compatible
    simp [changedCenter] at incompatible

/-- The two-dimensional interpretation actually varies across worlds.
The physical truth is epistemically true at the actual scenario, but fails
in the alternate world when that scenario remains fixed. -/
theorem primary_truth_need_not_be_necessary :
    terminal ∈ interpretation.primary (physicalSentence true) /\
    changedPhysical ∉ interpretation.secondary terminal (physicalSentence true) := by
  constructor
  · exact (physical_primary terminal true).2 rfl
  · simp [Interpretation.secondary, Interpretation.TrueAt, Form.Holds,
      interpretation, physicalSentence, referent, changedPhysical]

/-- The explicit totality clause is exactly what the open extension fails. -/
theorem extension_rejected_by_totality :
    extend terminal ∈ interpretation.stateOf (pqibase terminal) /\
    extend terminal ∉ interpretation.stateOf (pqitBase terminal) := by
  constructor
  · intro statement member
    rcases (mem_pqibase terminal statement).1 member with ⟨candidate, holds⟩
    exact extend_preserves_observations terminal statement candidate holds
  · intro verifies
    have impossible := (bound_primary (extend terminal) terminal.extraCount).1
      (verifies (totalitySentence terminal) (Or.inr rfl))
    exact Nat.not_succ_le_self _ impossible

end Controls

end Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalScrutability
