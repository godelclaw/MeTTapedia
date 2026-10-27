import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.MeTTaIL.ReferenceStepTabled

/-!
# Readings: a language's rules fired at a chosen presentation

A language's rules can be read through a choice of presentation. Each state is written in a chosen
presentation of the same value, the rules fire there, and their results are taken to canonical form. A set,
for instance, can be written with each member once, so that a member a rule matches is consumed, or with every
member copied, so that a matched member stays.

The reading holds at every boundary inside a step as well: a premise steps its child as the reading presents a
state (the canonical form of the child, then its presentation), a premise target and a relation's answers are
matched as presented, and a relation is asked about presented arguments (the presented internal boundary policy,
`InternalBoundaryPolicy.presented`, with `presentedOf present canon`).

- **The structure of a reading** (`readingStructure`): states, with the steps the rules take at the presentation
  of each, to canonical targets; an object term names its canonical form.
- **Listings** (`ReadingListing`): the steps listed at a presentation, each a step of the reading, and where the
  listing is complete, with every step listed alike on the labels it admits. The fuel lists the steps whose
  derivations fit within it, alike on every label (`fuelListing`); a certified table lists one step per rule and
  target, alike on the rule labels (`tableListing`).
- **A closed region of a reading** (`readingRegion`): canonical states without repetition, each completely listed
  at its presentation, with the canonical forms of its listed successors in the region. Its inclusion is a step
  morphism on the listing's labels into the reading's structure (`readingMorphism`), so the finite evaluator's
  verdict on it is exact for every behavioural formula over those labels (`reading_check_iff`).
- **Deciding** (`decideReading`, `decideTabled`): grow such a region from a term's canonical form and evaluate, with
  the fuel's listing, or with the table of the region reached from the term, tabulated within the fuel. A verdict is
  exact at the canonical form (`decideReading_sound`, `decideTabled_sound`). A premise whose child the reading
  presents as the term itself (`{x, x}` of `{x}`, read at canonical forms) lets derivations nest without bound: no
  fuel lists them all, and the table does.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (present canon : Pattern → Pattern)

/-! ## The structure of a reading -/

/-- **How a reading presents a term at an internal boundary**: its canonical form, then the reading's
presentation. -/
def presentedOf (term : Pattern) : List Pattern := [present (canon term)]

/-- **The structure of a reading**: states, with the steps the rules take at the presentation of each, to
canonical targets; an object term names its canonical form. -/
def readingStructure : NativeStructure Pattern where
  step source label target := IsState source ∧ IsState target ∧ ∃ witness contractum,
    StepValid relEnv language (present source) witness contractum (.presented (presentedOf present canon)) ∧
      label.admits witness = true ∧ canon contractum = target
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
  inRelation element relation := (referenceStructure relEnv language).inRelation element relation

/-! ## Labels -/

/-- **The labels kept**: every label when `deep`; otherwise those that do not look under a rule's premises. -/
def keptLabel (deep : Bool) : StepLabel → Bool
  | .under _ _ => deep
  | _ => true

theorem ruleOf_eq_ruleIndex (witness : Witness) : ruleOf witness = witness.ruleIndex := by
  cases witness <;> rfl

/-- **The rule labels agree for witnesses of one rule.** -/
theorem admits_of_ruleIndex {first second : Witness} (same : first.ruleIndex = second.ruleIndex) :
    ∀ label : StepLabel, keptLabel false label = true → label.admits first = label.admits second
  | .any, _ => rfl
  | .rule _, _ => by simp only [StepLabel.admits, ruleOf_eq_ruleIndex, same]
  | .under _ _, kept => by simp [keptLabel] at kept
  | .context _ _ _, _ => rfl

/-! ## Listings -/

/-- **A listing of a reading's steps**: the steps listed at a presentation, each a step of the reading, and where the
listing is complete, with every step listed alike on the admitted labels. -/
structure ReadingListing where
  steps : Pattern → List (Witness × Pattern)
  enough : Pattern → Bool
  admitted : StepLabel → Bool
  sound : ∀ {shown witness target}, (witness, target) ∈ steps shown →
    StepValid relEnv language shown witness target (.presented (presentedOf present canon))
  complete : ∀ {shown witness target}, enough shown = true →
    StepValid relEnv language shown witness target (.presented (presentedOf present canon)) →
      ∃ witness', (witness', target) ∈ steps shown ∧
        ∀ label, admitted label = true → label.admits witness' = label.admits witness

/-- **The fuel's listing**: the steps whose derivations fit within the fuel, complete where no derivation is cut
off, alike on every label. -/
def fuelListing : ReadingListing relEnv language present canon where
  steps := presentedStepsAt relEnv language (presentedOf present canon) fuel
  enough := presentedEnough relEnv language (presentedOf present canon) fuel
  admitted _ := true
  sound := stepValid_of_mem_presentedStepsAt
  complete enoughAt valid := ⟨_, mem_presentedStepsAt_of_enough enoughAt valid, fun _ _ => rfl⟩

/-- **A table's listing**: the table's steps once it is certified, complete at the presentations it visits, alike on
the rule labels. -/
def tableListing (todo : List Pattern) (table : List Entry) (certified : Bool)
    (checked : certified = true → TableCertified relEnv language (presentedOf present canon) todo table = true) :
    ReadingListing relEnv language present canon where
  steps shown := if certified then tableStepper table shown else []
  enough shown := certified && decide (shown ∈ todo)
  admitted := keptLabel false
  sound := by
    intro shown witness target member
    split at member
    · rename_i isCertified
      exact tableStepper_sound (TableCertified.valid (checked isCertified)) member
    · cases member
  complete := by
    intro shown witness target enoughAt valid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at enoughAt
    obtain ⟨isCertified, visited⟩ := enoughAt
    obtain ⟨entry, inside, sameRedex, sameRule, sameTarget⟩ := TableCertified.complete (checked isCertified) visited valid
    refine ⟨entry.2.1, ?_, admits_of_ruleIndex sameRule⟩
    rw [if_pos isCertified]
    simp only [tableStepper, List.mem_map, List.mem_filter, beq_iff_eq]
    exact ⟨entry, ⟨inside, sameRedex⟩, by rw [← sameTarget]⟩

/-- **The listing of a tabulated region**, certified once. -/
def tabledListing (region : List Pattern × List Entry) : ReadingListing relEnv language present canon :=
  tableListing relEnv language present canon region.1 region.2
    (TableCertified relEnv language (presentedOf present canon) region.1 region.2) id

/-! ## Closed regions -/

variable {relEnv language present canon} (listing : ReadingListing relEnv language present canon)

/-- What a state adds to a region: the canonical forms of the steps listed at its presentation. -/
abbrev nextReading (state : Pattern) : List Pattern :=
  if isStateBool state then (listing.steps (present state)).map (canon ·.2) else []

/-- Grow a region from a term: its canonical form first, then the canonical forms of the listed successors of
states, without repetition. -/
def growReading (term : Pattern) : ℕ → List Pattern
  | 0 => [canon term]
  | rounds + 1 =>
    let earlier := growReading term rounds
    addNew earlier (earlier.flatMap (nextReading listing))

variable (region : List Pattern)

/-- **A closed region of a reading**: canonical states without repetition, each completely listed at its
presentation, with the canonical forms of its listed successors in the region. -/
def readingRegion : Bool :=
  decide region.Nodup && region.all fun term => canon term == term &&
    (!isStateBool term ||
      (listing.enough (present term) && (listing.steps (present term)).all fun entry => canon entry.2 ∈ region))

/-- **The region as a finite structure**: its steps lead to the canonical forms of the steps listed at each
state's presentation. -/
def readingExploration : FiniteStructure (Fin region.length) where
  elements := List.finRange region.length
  complete := List.mem_finRange
  step source label target := isStateBool region[source] && isStateBool region[target] &&
    (listing.steps (present region[source])).any fun entry => canon entry.2 == region[target] && label.admits entry.1
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
  inRelation element relation := isObjectPattern region[element] && relationHolds relEnv language relation region[element]

variable {listing region}

theorem readingRegion_parts (closed : readingRegion listing region = true) :
    region.Nodup ∧ ∀ term ∈ region, canon term = term ∧
      (isStateBool term = true → listing.enough (present term) = true ∧
        ∀ entry ∈ listing.steps (present term), canon entry.2 ∈ region) := by
  simp only [readingRegion, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at closed
  refine ⟨closed.1, fun term member => ⟨(closed.2 term member).1, fun state => ?_⟩⟩
  rcases (closed.2 term member).2 with notState | listed
  · rw [notState] at state
    cases state
  · exact ⟨listed.1, listed.2⟩

/-- **A closed region's inclusion is a step morphism on the listing's labels into the reading's structure.** -/
def readingMorphism (closed : readingRegion listing region = true) :
    LabelMorphism (readingExploration listing region).native (readingStructure relEnv language present canon)
      listing.admitted where
  map index := region[index]
  step := by
    intro source label target _ checked
    change (_ && _ && _) = true at checked
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨sourceState, targetState⟩, entry, member, same, admits⟩ := checked
    exact ⟨by simpa [isStateBool] using sourceState, by simpa [isStateBool] using targetState, entry.1, entry.2,
      listing.sound member, admits, same⟩
  stepBack := by
    intro source label target' admitted step
    obtain ⟨sourceState, targetState, witness, contractum, valid, admits, reached⟩ := step
    obtain ⟨-, members⟩ := readingRegion_parts closed
    obtain ⟨-, listed⟩ := members _ (List.getElem_mem source.2)
    obtain ⟨enoughAt, successors⟩ := listed (isStateBool_of_isState sourceState)
    obtain ⟨witness', member, alike⟩ := listing.complete enoughAt valid
    have labelAdmitted : listing.admitted label = true := by
      simp only [StepLabel.admittedBy, Bool.and_eq_true] at admitted
      exact admitted.1
    obtain ⟨target, isTarget⟩ := exists_index (successors _ member)
    refine ⟨target, ?_, isTarget.trans reached⟩
    show (_ && _ && _) = true
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
    exact ⟨⟨isStateBool_of_isState sourceState, isStateBool_of_isState (by rw [isTarget, reached]; exact targetState)⟩,
      (witness', contractum), member, isTarget.symm, (alike label labelAdmitted).trans admits⟩
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

/-- **A closed region of a reading decides every behavioural formula over the listing's labels** at its states. -/
theorem reading_check_iff (closed : readingRegion listing region = true) {formula : Formula 0}
    (behavioural : formula.behaviouralIn listing.admitted = true) (index : Fin region.length) :
    (readingExploration listing region).check formula index = true ↔
      (readingStructure relEnv language present canon).sat Env.closed formula region[index] := by
  rw [FiniteStructure.check_iff]
  exact (readingMorphism closed).sat_iff formula behavioural (LabelMorphism.envPreimage_closed _) index

/-! ## Deciding -/

theorem growReading_first (term : Pattern) :
    ∀ rounds, ∃ rest, growReading listing term rounds = canon term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := growReading_first term rounds
    obtain ⟨extra, extended⟩ := addNew_extends (growReading listing term rounds)
      ((growReading listing term rounds).flatMap (nextReading listing))
    refine ⟨rest ++ extra, ?_⟩
    simp only [growReading]
    rw [extended, same, List.cons_append]

theorem growReading_length_pos (term : Pattern) (rounds : ℕ) : 0 < (growReading listing term rounds).length := by
  obtain ⟨rest, same⟩ := growReading_first (listing := listing) term rounds
  rw [same]
  exact Nat.succ_pos _

variable (listing) in
/-- **Decide a behavioural formula in a reading through a listing** at a term's canonical form: the exact verdict
when the grown region closes, nothing otherwise. -/
def decideListed (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  if readingRegion listing (growReading listing term rounds) then
    some ((readingExploration listing (growReading listing term rounds)).check formula
      ⟨0, growReading_length_pos term rounds⟩)
  else none

/-- **A verdict through a listing is exact** at the term's canonical form, for a formula over the listing's labels. -/
theorem decideListed_sound {formula : Formula 0} (behavioural : formula.behaviouralIn listing.admitted = true)
    {term : Pattern} {rounds : ℕ} {verdict : Bool} (decided : decideListed listing formula term rounds = some verdict) :
    (verdict = true ↔ (readingStructure relEnv language present canon).sat Env.closed formula (canon term)) := by
  unfold decideListed at decided
  split at decided
  · rename_i closed
    cases decided
    obtain ⟨rest, same⟩ := growReading_first (listing := listing) term rounds
    have first : (growReading listing term rounds)[(⟨0, growReading_length_pos term rounds⟩ :
        Fin (growReading listing term rounds).length)] = canon term := by
      simp only [Fin.getElem_fin]
      simp [same]
    rw [← first]
    exact reading_check_iff closed behavioural _
  · cases decided

variable (relEnv language present canon)

/-- **Decide a behavioural formula in a reading** at a term's canonical form, with the fuel's listing. -/
def decideReading (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  decideListed (fuelListing relEnv language fuel present canon) formula term rounds

/-- **Decide a behavioural formula over the rule labels in a reading by a table**: the region reached from the
presentation of the term's canonical form, tabulated within the fuel and certified once. -/
def decideTabled (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  if formula.behaviouralIn (keptLabel false) then
    decideListed (tabledListing relEnv language present canon
      (regionTabulate relEnv language (presentedOf present canon) fuel [present (canon term)] [])) formula term rounds
  else none

variable {relEnv language fuel present canon}

/-- **A verdict of a reading is exact** at the term's canonical form. -/
theorem decideReading_sound {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    {term : Pattern} {rounds : ℕ} {verdict : Bool}
    (decided : decideReading relEnv language fuel present canon formula term rounds = some verdict) :
    (verdict = true ↔ (readingStructure relEnv language present canon).sat Env.closed formula (canon term)) :=
  decideListed_sound (by rw [show (fuelListing relEnv language fuel present canon).admitted = fun _ => true from rfl,
    Formula.behaviouralIn_all]; exact behavioural) decided

/-- **A verdict of a reading by a table is exact** at the term's canonical form. -/
theorem decideTabled_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ} {verdict : Bool}
    (decided : decideTabled relEnv language fuel present canon formula term rounds = some verdict) :
    (verdict = true ↔ (readingStructure relEnv language present canon).sat Env.closed formula (canon term)) := by
  unfold decideTabled at decided
  split at decided
  · rename_i labels
    exact decideListed_sound labels decided
  · cases decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
