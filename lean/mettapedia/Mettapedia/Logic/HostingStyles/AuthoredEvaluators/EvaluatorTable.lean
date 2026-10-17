import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.ProgramSentence

/-!
# The evaluators met so far: one table

Five properties of an evaluator of the premises of the probe with a run
constructor.

* **Authored** (`IsAuthored`): it is the evaluator of an equation program, run
  by the shared engine.
* **Respects the static equivalence** (`RespectsStatics`).
* **Reads through the matches at the root** (`ReadsRootMatches`): its answers
  to the run premise depend on the subject only through the matches, at its
  root, of the left sides that the space stores.  This is the notion of a weak
  evaluator as first worded; it bounds nothing (`rootMatches_bound_fails`).
* **Weak** (`WeakEvaluator`): its answers to the run premise are the instances,
  at the root of the subject, of rules that the stored atoms are read as.
* **What it hosts through one run rewrite**, on terms.

| evaluator | authored | respects the static equivalence | reads through the matches at the root | weak | hosts through one run rewrite |
|---|---|---|---|---|---|
| silent (`silentEvaluator`) | yes, the empty program: `silentEvaluator_isAuthored` | yes: `silentEvaluator_respectsStatics` | yes: `silentEvaluator_readsRootMatches` | yes: `silentEvaluator_weak` | nothing, a run has no step: `silent_run_normal` |
| matching (`matchingEvaluator`) | yes, eighty-eight equations: `matchingEvaluator_isAuthored` | yes: `matchingEvaluator_respectsStatics` | yes: `matchingEvaluator_readsRootMatches` | yes: `matchingEvaluator_weak` | the instances at the root of the first-order tables whose rules determine their right sides, and of no other first-order table: `instances_hostedBy_matching_iff`; no theory that branches without bound along one reduction: `WeakEvaluator.not_hostedBy_of_unboundedBranching` |
| chosen from a listing (`stepEvaluator`) | depends on the listing: the one of the empty set of gates is the silent evaluator, `gateEvaluator_empty_isAuthored`; some set of gates has one that no program computes, `exists_gates_not_authored` | yes: `stepEvaluator_respectsStatics` | no, when the listed theory has a step: `stepEvaluator_not_readsRootMatches` | no, when the listed theory has a step: `stepEvaluator_not_weak` | the listed theory, whatever it is: `runMap_hosting` |
| chosen from the sources (`determinedEvaluator`) | not decided by its definition, which numbers its terms by choice: `determinedRunProbe_programmed_iff` | yes: `determinedEvaluator_respectsStatics` | no: `determinedEvaluator_not_readsRootMatches` | no: `determinedEvaluator_not_weak` | the theories of the tables whose rules determine their right sides, with beta and steps at every position: `determinedRunProbe_hosts` |
| one step of the rule-table evaluator (`tableRunEvaluator`) | not decided by its definition, which numbers its terms by choice; the step at the empty table is authored, by the beta program below; no authored evaluator that respects the static equivalence hosts its whole class: `authored_not_hostOf_tabular` | no: `tableRunEvaluator_not_respectsStatics` | no: `tableRunEvaluator_not_readsRootMatches` | no: `tableRunEvaluator_not_weak` | every theory given by a table: `runPresentation_hostOf_tabular_terms` |
| the beta program (`betaAuthored`) | yes, seventy-six equations | yes: `betaAuthored_respectsStatics` | no: `betaAuthored_not_readsRootMatches` | no: `betaAuthored_not_weak` | the pure λΠ-calculus, the theory of the empty table, with beta at every position: `betaAuthored_hosts` |
| the climbing program (`climbAuthored`) | yes, twenty-three equations | yes: `climbAuthored_respectsStatics` | no: `climbAuthored_not_readsRootMatches` | no: `climbAuthored_not_weak` | a theory that branches without bound along one reduction: `climbAuthored_hosts` |
| the label program (`labelAuthored`) | yes, one equation | no: `labelAuthored_not_respectsStatics` | no: `labelAuthored_not_readsRootMatches` | no: `labelAuthored_not_weak` | it is the program of no candidate: `labelAuthored_no_candidate` |

Reading the table by columns:

* *Authored* and *respects the static equivalence* are independent: the label
  program is authored and does not respect it; some evaluator chosen from a
  listing respects it and is not authored.
* *Weak* constrains the answers to the run premise only.  The evaluator that
  gives those answers to the run premise and none to any other premise
  respects the static equivalence (`AnswersByStoredRules.respectsStatics`),
  and a weak evaluator answers nothing at a space that stores no atom
  (`WeakEvaluator.rulesFromSpace`).
* *Authored* does not imply *weak* (the beta program, the climbing program),
  and *weak* is a property of what is computed, not of how it is given.
* Only the weak rows have a bound on what one run rewrite hosts.
* Beta at every position is hosted by an authored evaluator that respects the
  static equivalence (`beta_everywhere_authored`).  With a table of declared
  rules a step also rewrites by an instance of a rule; the program for that
  is not written.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory Tabled tableEvaluator rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## The two notions, for evaluators -/

/-- **A weak evaluator**: it answers the run premise by a function whose
answers are answers by stored rules. -/
def WeakEvaluator (base : BasePremiseEvaluator) : Prop :=
  ∃ answers : Pattern → Pattern → List Pattern,
    AnswersRunBy base answers ∧ AnswersByStoredRules answers

/-- **An evaluator reads its subject through the matches at the root**: it
answers the run premise by a function that does. -/
def ReadsRootMatches (base : BasePremiseEvaluator) : Prop :=
  ∃ answers : Pattern → Pattern → List Pattern,
    AnswersRunBy base answers ∧ ReadsThroughRootMatches answers

/-- **A weak evaluator takes its rules from the space**: where the space
stores no atom it answers nothing. -/
theorem WeakEvaluator.rulesFromSpace {base : BasePremiseEvaluator} (weak : WeakEvaluator base) :
    RulesFromSpace base := by
  obtain ⟨answers, byRun, stored⟩ := weak
  intro lang bindings empty
  rw [byRun]
  have short := stored.length_le (applyBindings bindings (.fvar "space"))
    (applyBindings bindings (.fvar "subject"))
  rw [empty] at short
  rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)]
  rfl

/-- **Through one run rewrite a weak evaluator hosts no theory that branches
without bound along one reduction.** -/
theorem WeakEvaluator.not_hostedBy_of_unboundedBranching {base : BasePremiseEvaluator}
    (weak : WeakEvaluator base) {source : GSLT.{0}} (branching : UnboundedBranching source) :
    ¬ HostedBy source.termsAlone (contextTheory base spacePresentation) := by
  obtain ⟨answers, byRun, stored⟩ := weak
  exact storedRules_not_hostedBy_of_unboundedBranching byRun stored branching

/-- At the empty space, an evaluator that reads its subject through the
matches at the root gives every subject as many answers. -/
theorem ReadsRootMatches.emptySpace_length {base : BasePremiseEvaluator}
    (reads : ReadsRootMatches base) (lang : LanguageDef) (subject other : Pattern) :
    (base lang [("subject", subject), ("space", emptySpace)] runPremise).length =
      (base lang [("subject", other), ("space", emptySpace)] runPremise).length := by
  obtain ⟨answers, byRun, through⟩ := reads
  have spaceValue : ∀ value : Pattern,
      applyBindings [("subject", value), ("space", emptySpace)] (.fvar "space") = emptySpace := by
    intro value
    simp [applyBindings]
  have subjectValue : ∀ value : Pattern,
      applyBindings [("subject", value), ("space", emptySpace)] (.fvar "subject") = value := by
    intro value
    simp [applyBindings]
  rw [byRun, byRun, List.length_map, List.length_map, spaceValue, spaceValue, subjectValue,
    subjectValue, through emptySpace subject other (by
      rw [show contract emptySpace = emptySpace by decide, rootMatches_emptySpace,
        rootMatches_emptySpace])]

/-! ## The silent evaluator -/

theorem silentEvaluator_answersRunBy : AnswersRunBy silentEvaluator fun _ _ => [] :=
  fun _ _ => rfl

theorem silentEvaluator_weak : WeakEvaluator silentEvaluator := by
  refine ⟨fun _ _ => [], silentEvaluator_answersRunBy, fun _ => none, ?_, ?_⟩
  · intro atom rule found
    cases found
  · intro space subject
    have none : ∀ atoms : List Pattern,
        atoms.filterMap (fun _ : Pattern => (none : Option (Pattern × Pattern))) = [] := by
      intro atoms
      induction atoms with
      | nil => rfl
      | cons atom rest step => rw [List.filterMap_cons_none rfl, step]
    rw [none]
    rfl

theorem silentEvaluator_readsRootMatches : ReadsRootMatches silentEvaluator :=
  ⟨fun _ _ => [], silentEvaluator_answersRunBy, fun _ _ _ _ => rfl⟩

/-- Under the silent evaluator a run has no step. -/
theorem silent_run_normal (space subject target : Pattern) :
    ¬ Step silentEvaluator probeWithSpace (runPattern space subject) target := by
  intro moved
  obtain ⟨_, _, result, -, found, -⟩ := answered_step_inv probeWithSpace_rewrites
    silentEvaluator_answersRunBy (by rw [contract_runPattern']; rfl) moved
  cases found

/-! ## The matching evaluator -/

theorem matchingEvaluator_weak : WeakEvaluator matchingEvaluator :=
  ⟨_, matchingEvaluator_answersRunBy, matching_answersByStoredRules⟩

theorem matchingEvaluator_readsRootMatches : ReadsRootMatches matchingEvaluator :=
  ⟨_, matchingEvaluator_answersRunBy, matching_readsThroughRootMatches⟩

/-! ## Evaluators chosen from a listing -/

/-- The evaluator of a listing answers nothing at a subject that is no
numeral. -/
theorem stepEvaluator_bvar {Source : Type} (code : Source → Nat) (next : Source → List Source)
    (lang : LanguageDef) (space : Pattern) :
    stepEvaluator code next lang [("subject", .bvar 0), ("space", space)] runPremise = [] := by
  show stepAnswers code next _ (.fvar "subject") "answer" = []
  unfold stepAnswers
  rw [dif_neg]
  rintro ⟨term, same⟩
  have value : applyBindings [("subject", Pattern.bvar 0), ("space", space)] (.fvar "subject") =
      .bvar 0 := by simp [applyBindings]
  rw [value] at same
  cases numeralCase : code term with
  | zero => rw [numeralCase] at same; simp [contract, numeral, unitAtom] at same
  | succ count => rw [numeralCase] at same; simp [contract, numeral] at same

/-- At the numeral of a term with a step it answers. -/
theorem stepEvaluator_numeral_ne_nil {source : GSLT.{0}} (listing : StepListing source)
    {term reduct : source.Term} (moved : source.rewrites term reduct) (lang : LanguageDef)
    (space : Pattern) :
    stepEvaluator listing.code listing.next lang
      [("subject", numeral (listing.code term)), ("space", space)] runPremise ≠ [] := by
  have answered : (("answer", numeral (listing.code reduct)) ::
      [("subject", numeral (listing.code term)), ("space", space)]) ∈
      stepEvaluator listing.code listing.next lang
        [("subject", numeral (listing.code term)), ("space", space)] runPremise := by
    show _ ∈ stepAnswers listing.code listing.next _ (.fvar "subject") "answer"
    rw [stepAnswers_eq listing.injective listing.next "answer" (term := term)
      (by
        rw [show applyBindings [("subject", numeral (listing.code term)), ("space", space)]
          (.fvar "subject") = numeral (listing.code term) by simp [applyBindings],
          contract_numeral])]
    exact List.mem_map.mpr ⟨reduct, (listing.branches term reduct).mp moved, rfl⟩
  exact List.ne_nil_of_mem answered

/-- **The evaluator of a listed theory with a step is not weak.** -/
theorem stepEvaluator_not_weak {source : GSLT.{0}} (listing : StepListing source)
    {term reduct : source.Term} (moved : source.rewrites term reduct) :
    ¬ WeakEvaluator (stepEvaluator listing.code listing.next) := fun weak =>
  stepEvaluator_not_rulesFromSpace listing moved weak.rulesFromSpace

/-- **Nor does it read its subject through the matches at the root.** -/
theorem stepEvaluator_not_readsRootMatches {source : GSLT.{0}} (listing : StepListing source)
    {term reduct : source.Term} (moved : source.rewrites term reduct) :
    ¬ ReadsRootMatches (stepEvaluator listing.code listing.next) := by
  intro reads
  have lengths := reads.emptySpace_length probeWithSpace (numeral (listing.code term)) (.bvar 0)
  rw [stepEvaluator_bvar, List.length_nil] at lengths
  exact stepEvaluator_numeral_ne_nil listing moved probeWithSpace emptySpace
    (List.eq_nil_of_length_eq_zero lengths)

/-- **Positive**: the evaluator of the empty set of gates is the silent
evaluator, so it is authored. -/
theorem gateEvaluator_empty_isAuthored : IsAuthored (gateEvaluator ∅) := by
  have silent : gateEvaluator ∅ = silentEvaluator := by
    funext lang bindings premise
    unfold gateEvaluator stepEvaluator
    split
    · rename_i subject answer
      show stepAnswers (gateListing ∅).code (gateListing ∅).next bindings subject answer = []
      unfold stepAnswers
      split_ifs with known
      · have none : (gateListing ∅).next (Classical.choose known) = [] := by
          show gateNext ∅ _ = []
          unfold gateNext
          exact if_neg fun wrong => wrong
        rw [none]
        rfl
      · rfl
    · rfl
  rw [silent]
  exact silentEvaluator_isAuthored

/-! ## The evaluator chosen from the sources -/

theorem determinedEvaluator_not_weak : ¬ WeakEvaluator determinedEvaluator := fun weak =>
  determinedEvaluator_not_rulesFromSpace weak.rulesFromSpace

theorem determinedEvaluator_not_readsRootMatches : ¬ ReadsRootMatches determinedEvaluator :=
  stepEvaluator_not_readsRootMatches (unionListing determinedListing)
    (term := ⟨0, selfIdentity⟩) (reduct := ⟨0, identityTerm⟩)
    (UnionStep.member (selfIdentity_step _))

/-! ## One step of the rule-table evaluator -/

/-- The evaluator of an enumerated theory answers, at the spelling of a place
of the sequence of a term, with the reduct at that place. -/
theorem spellingEvaluator_spelled {source : GSLT.{0}} (enumeration : StepEnumeration source)
    {term next : source.Term} {depth : Nat} (found : enumeration.reduct term depth = some next)
    (lang : LanguageDef) (space : Pattern) :
    spellingEvaluator enumeration.code enumeration.reduct lang
      [("subject", spelledAtom depth (enumeration.code term)), ("space", space)] runPremise ≠ [] := by
  have answered : (("answer", spelledAtom 0 (enumeration.code next)) ::
      [("subject", spelledAtom depth (enumeration.code term)), ("space", space)]) ∈
      spellingEvaluator enumeration.code enumeration.reduct lang
        [("subject", spelledAtom depth (enumeration.code term)), ("space", space)] runPremise := by
    show _ ∈ spellingAnswers enumeration.code enumeration.reduct _ (.fvar "subject") "answer"
    rw [spellingAnswers_eq enumeration.injective enumeration.reduct "answer" (term := term)
      (by simp [applyBindings, contract_spelledAtom])]
    have place : drops (applyBindings
        [("subject", spelledAtom depth (enumeration.code term)), ("space", space)]
        (.fvar "subject")) - 1 = depth := by
      simp [applyBindings, drops_spelledAtom]
    rw [place, found]
    exact List.mem_map.mpr ⟨next, by simp, rfl⟩
  exact List.ne_nil_of_mem answered

/-- It answers nothing at a subject that is no spelled atom. -/
theorem spellingEvaluator_bvar {Source : Type} (code : Source → Nat)
    (reduct : Source → Nat → Option Source) (lang : LanguageDef) (space : Pattern) :
    spellingEvaluator code reduct lang [("subject", .bvar 0), ("space", space)] runPremise = [] := by
  show spellingAnswers code reduct _ (.fvar "subject") "answer" = []
  unfold spellingAnswers
  rw [dif_neg]
  rintro ⟨term, same⟩
  have value : applyBindings [("subject", Pattern.bvar 0), ("space", space)] (.fvar "subject") =
      .bvar 0 := by simp [applyBindings]
  rw [value] at same
  simp [contract, spelledAtom, dropped] at same

/-- A term of the rule-table evaluator with a step: `(λx. x) (λx. x)` under
the empty table. -/
theorem tableEvaluator_step :
    (tableEvaluator.gslt ()).rewrites (⟨∅, selfIdentity⟩ : Tabled) ⟨∅, identityTerm⟩ :=
  ⟨rfl, selfIdentity_step _⟩

theorem tableRunEvaluator_not_rulesFromSpace : ¬ RulesFromSpace tableRunEvaluator := by
  intro fromSpace
  obtain ⟨depth, found⟩ :=
    (evaluatorEnumeration.branches _ _).mp tableEvaluator_step
  refine spellingEvaluator_spelled evaluatorEnumeration found probeWithSpace emptySpace
    (fromSpace probeWithSpace _ ?_)
  rw [show applyBindings
    [("subject", spelledAtom depth (evaluatorEnumeration.code (⟨∅, selfIdentity⟩ : Tabled))),
      ("space", emptySpace)] (.fvar "space") = emptySpace by simp [applyBindings]]
  decide

theorem tableRunEvaluator_not_weak : ¬ WeakEvaluator tableRunEvaluator := fun weak =>
  tableRunEvaluator_not_rulesFromSpace weak.rulesFromSpace

theorem tableRunEvaluator_not_readsRootMatches : ¬ ReadsRootMatches tableRunEvaluator := by
  intro reads
  obtain ⟨depth, found⟩ :=
    (evaluatorEnumeration.branches _ _).mp tableEvaluator_step
  have lengths := reads.emptySpace_length probeWithSpace
    (spelledAtom depth (evaluatorEnumeration.code (⟨∅, selfIdentity⟩ : Tabled))) (.bvar 0)
  rw [show tableRunEvaluator probeWithSpace [("subject", Pattern.bvar 0), ("space", emptySpace)]
    runPremise = [] from spellingEvaluator_bvar _ _ _ _, List.length_nil] at lengths
  exact spellingEvaluator_spelled evaluatorEnumeration found probeWithSpace emptySpace
    (List.eq_nil_of_length_eq_zero lengths)

/-! ## The beta program -/

theorem betaAuthored_not_weak : ¬ WeakEvaluator betaAuthored.evaluator := fun weak =>
  weak.not_hostedBy_of_unboundedBranching (rewritingTheory_unboundedBranching (Theory.ofTable ∅))
    betaAuthored_hosts

theorem betaAuthored_not_readsRootMatches : ¬ ReadsRootMatches betaAuthored.evaluator := by
  intro reads
  have lengths := reads.emptySpace_length probeWithSpace
    (termAtom (.app (.lam (.con "A") (.var 0)) (.con "c"))) unitAtom
  have redexValue : applyBindings
      [("subject", termAtom (.app (.lam (.con "A") (.var 0)) (.con "c"))), ("space", emptySpace)]
      (.fvar "subject") = termAtom (.app (.lam (.con "A") (.var 0)) (.con "c")) := by
    simp [applyBindings]
  have unitValue : applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "subject") =
      unitAtom := by simp [applyBindings]
  rw [betaAuthored.evaluator_runPremise, betaAuthored.evaluator_runPremise, List.length_map,
    List.length_map, betaAuthored_run, betaAuthored_run, redexValue, unitValue, contract_termAtom,
    show contract unitAtom = unitAtom by decide, betaAnswers_identity, betaAnswers_unitAtom]
    at lengths
  simp at lengths

/-! ## The two programs of `ClimbProgram` -/

theorem climbAuthored_not_weak : ¬ WeakEvaluator climbAuthored.evaluator := fun weak =>
  climbAuthored_not_rulesFromSpace weak.rulesFromSpace

theorem climbAuthored_not_readsRootMatches : ¬ ReadsRootMatches climbAuthored.evaluator := by
  intro reads
  have lengths := reads.emptySpace_length probeWithSpace unitAtom (numeral 1)
  have unitValue : applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "subject") =
      unitAtom := by simp [applyBindings]
  have oneValue : applyBindings [("subject", numeral 1), ("space", emptySpace)] (.fvar "subject") =
      numeral 1 := by simp [applyBindings]
  rw [climbAuthored.evaluator_runPremise, climbAuthored.evaluator_runPremise, List.length_map,
    List.length_map, climbAuthored_run, climbAuthored_run, unitValue, oneValue] at lengths
  revert lengths
  decide

/-- The label program fails at a subject that is no application. -/
theorem labelAuthored_bvar (relation : String) (space : Pattern) (index : Nat) :
    labelAuthored.answers relation [space, .bvar index] = [] := by
  refine labelAuthored.answers_of_failure (fuel := 0) ?_
  have unmatched : labelProgram.select "premise"
      (premiseArguments relation [space, .bvar index]) = none := rfl
  have defined : labelProgram.definesAt "premise"
      (premiseArguments relation [space, .bvar index]).length = true := rfl
  show DeterministicEquations.apply labelProgram sharedHost 0 "premise"
    (premiseArguments relation [space, .bvar index]) = .failure
  simp [DeterministicEquations.apply, DeterministicEquations.applyWith, defined, unmatched]

theorem labelAuthored_not_weak : ¬ WeakEvaluator labelAuthored.evaluator := by
  intro weak
  have silent := weak.rulesFromSpace probeWithSpace [("subject", unitAtom), ("space", emptySpace)]
    (by
      rw [show applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "space") =
        emptySpace by simp [applyBindings]]
      decide)
  rw [labelAuthored.evaluator_runPremise] at silent
  have spaceValue : applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "space") =
      emptySpace := by simp [applyBindings]
  have subjectValue : applyBindings [("subject", unitAtom), ("space", emptySpace)]
      (.fvar "subject") = .apply "prime-unit" [] := by simp [applyBindings, unitAtom]
  rw [spaceValue, subjectValue, labelAuthored_answers] at silent
  cases silent

theorem labelAuthored_not_readsRootMatches : ¬ ReadsRootMatches labelAuthored.evaluator := by
  intro reads
  have lengths := reads.emptySpace_length probeWithSpace unitAtom (.bvar 0)
  have spaceValue : ∀ value : Pattern,
      applyBindings [("subject", value), ("space", emptySpace)] (.fvar "space") = emptySpace := by
    intro value
    simp [applyBindings]
  have unitValue : applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "subject") =
      .apply "prime-unit" [] := by simp [applyBindings, unitAtom]
  have otherValue : applyBindings [("subject", Pattern.bvar 0), ("space", emptySpace)]
      (.fvar "subject") = .bvar 0 := by simp [applyBindings]
  rw [labelAuthored.evaluator_runPremise, labelAuthored.evaluator_runPremise, List.length_map,
    List.length_map, spaceValue, spaceValue, unitValue, otherValue, labelAuthored_answers,
    labelAuthored_bvar] at lengths
  cases lengths

#print axioms WeakEvaluator.rulesFromSpace
#print axioms WeakEvaluator.not_hostedBy_of_unboundedBranching
#print axioms ReadsRootMatches.emptySpace_length
#print axioms silentEvaluator_weak
#print axioms silent_run_normal
#print axioms matchingEvaluator_weak
#print axioms matchingEvaluator_readsRootMatches
#print axioms stepEvaluator_not_weak
#print axioms stepEvaluator_not_readsRootMatches
#print axioms gateEvaluator_empty_isAuthored
#print axioms determinedEvaluator_not_weak
#print axioms determinedEvaluator_not_readsRootMatches
#print axioms tableRunEvaluator_not_weak
#print axioms tableRunEvaluator_not_readsRootMatches
#print axioms betaAuthored_not_weak
#print axioms betaAuthored_not_readsRootMatches
#print axioms climbAuthored_not_weak
#print axioms climbAuthored_not_readsRootMatches
#print axioms labelAuthored_not_weak
#print axioms labelAuthored_not_readsRootMatches

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
