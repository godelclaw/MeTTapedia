import Mettapedia.Logic.HostingStyles.AmbientRegions.AtomSubjects
import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.WeakEvaluators
import Mettapedia.Logic.HostingStyles.AmbientSpace.RulesFromSpace

/-!
# The evaluator of a region is weak, and takes its rules from two spaces

* **Without a guard the evaluator is weak in the sense of
  `AnswersByStoredRules`, for both premises** (`regionEvaluator_weak`): one
  function of a space and a subject, whose answers are the instances at the
  root of the subject of the rules that the stored atoms of the space are
  read as, answers the premise of the ambient root step at the ambient space
  (`AnswersAmbientBy`) and the premise of the root step of a run at the space
  of the run (`AnswersRunBy`).  So a subject has at most as many answers as
  the space that is asked stores atoms (`admittedAnswers_any_length_le`).
* **The family takes its rules from the spaces** (`FamilyRulesFromSpaces`,
  `regionEvaluator_rulesFromSpaces`), under every guard: at an ambient space
  that stores no atom it answers no ambient root step, and for a run in a
  space that stores no atom it answers no root step of the run.  Negative:
  the family that answers the root step of a run from the ambient space
  (`ambientAnswersRuns_not_rulesFromSpaces`), and the family of a listing
  (`listedFamily_not_rulesFromSpaces`).
* **A guard costs the weakness** (`guarded_not_answersByStoredRules`): the
  answers under a guard that admits the unit atom and a bound variable and
  refuses some subject are answers by stored rules for no reading of the
  stored atoms.  A stored equation between one variable and itself answers
  every admitted subject with itself, so it would be read as a rule whose left
  side is a variable, and a variable matches the refused subject too.  In
  particular `notRun`, `atomHead` and `atomNotRun`
  (`notRun_not_answersByStoredRules`, `atomHead_not_answersByStoredRules`,
  `atomNotRun_not_answersByStoredRules`).

So containment and a weak evaluator pull apart in the two presentations as
written: without a guard the evaluator is weak and the contained presentation
is contained only at ambient spaces that answer nothing for a run; under a
guard it is contained everywhere and its evaluator is not weak in the stated
sense.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AuthoredEvaluators
  (AnswersByStoredRules AnswersRunBy rootInstances matching_answersByStoredRules catchAll
    guardSpace guardSpace_contracted matchResults_eq_filterMap atomResult_identity)

/-! ## Answering the two premises by one function -/

/-- **An evaluator answers the premise of the ambient root step by a function
of a fixed space and the subject**: it binds the answer variable, in front of
the bindings, to each pattern of a list computed from the two, and changes
nothing else. -/
def AnswersAmbientBy (base : BasePremiseEvaluator) (ambientSpace : Pattern)
    (answers : Pattern → Pattern → List Pattern) : Prop :=
  ∀ (lang : LanguageDef) (bindings : Bindings),
    base lang bindings rootPremise =
      (answers ambientSpace (applyBindings bindings (.fvar "subject"))).map
        fun result => ("answer", result) :: bindings

/-- **Positive**: the evaluator of a region, by the answers that its guard
admits. -/
theorem regionEvaluator_answersAmbientBy (admits : Pattern → Bool) (ambientSpace : Pattern) :
    AnswersAmbientBy (regionEvaluator admits ambientSpace) ambientSpace (admittedAnswers admits) :=
  fun _ _ => rfl

/-- **Positive**: it answers the root step of a run by the same function, at
the space of the run. -/
theorem regionEvaluator_answersRunBy (admits : Pattern → Bool) (ambientSpace : Pattern) :
    AnswersRunBy (regionEvaluator admits ambientSpace) (admittedAnswers admits) :=
  fun _ _ => rfl

/-- **Negative**: the matching evaluator answers no ambient root step, so it
does not answer that premise by the answers of a space that stores a rule. -/
theorem matchingEvaluator_not_answersAmbientBy :
    ¬ AnswersAmbientBy matchingEvaluator (ruleSpace [identityRule])
      (admittedAnswers anySubject) := by
  intro answers
  have silent := answers ambient [("subject", unitAtom)]
  have found : unitAtom ∈ admittedAnswers anySubject (ruleSpace [identityRule])
      (applyBindings [("subject", unitAtom)] (.fvar "subject")) := by
    refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
    rw [contract_ruleSpace,
      show applyBindings [("subject", unitAtom)] (.fvar "subject") = unitAtom by
        simp [applyBindings],
      show contract unitAtom = unitAtom by decide]
    exact identity_answers _
  have nonempty : (("answer", unitAtom) :: [("subject", unitAtom)]) ∈
      (admittedAnswers anySubject (ruleSpace [identityRule])
        (applyBindings [("subject", unitAtom)] (.fvar "subject"))).map
          fun result => ("answer", result) :: [("subject", unitAtom)] :=
    List.mem_map.mpr ⟨unitAtom, found, rfl⟩
  rw [← silent] at nonempty
  simp [matchingEvaluator, rootPremise] at nonempty

/-! ## Without a guard the evaluator is weak -/

/-- **The answers without a guard are answers by stored rules.** -/
theorem admittedAnswers_any_answersByStoredRules :
    AnswersByStoredRules (admittedAnswers anySubject) := by
  have same : admittedAnswers anySubject =
      fun space subject => matchResults (contract space) (contract subject) := by
    funext space subject
    rfl
  rw [same]
  exact matching_answersByStoredRules

/-- **The evaluator of a region is weak, for the ambient step and for the
step of a run**: without a guard, one function whose answers are the instances
at the root of the subject of the rules that the stored atoms are read as
answers both premises, the first at the ambient space and the second at the
space of the run. -/
theorem regionEvaluator_weak (ambientSpace : Pattern) :
    ∃ answers : Pattern → Pattern → List Pattern, AnswersByStoredRules answers ∧
      AnswersAmbientBy (regionEvaluator anySubject ambientSpace) ambientSpace answers ∧
        AnswersRunBy (regionEvaluator anySubject ambientSpace) answers :=
  ⟨admittedAnswers anySubject, admittedAnswers_any_answersByStoredRules,
    regionEvaluator_answersAmbientBy anySubject ambientSpace,
    regionEvaluator_answersRunBy anySubject ambientSpace⟩

/-- **A subject has at most as many answers as the space that is asked stores
atoms**: the ambient space for the ambient root step, the space of the run
for the root step of a run. -/
theorem admittedAnswers_any_length_le (space subject : Pattern) :
    (admittedAnswers anySubject space subject).length ≤ (storedAtoms (contract space)).length :=
  admittedAnswers_any_answersByStoredRules.length_le space subject

/-! ## The family takes its rules from the spaces -/

/-- A space that stores no atom answers nothing, under every guard. -/
theorem admittedAnswers_of_stores_nothing (admits : Pattern → Bool) {space : Pattern}
    (empty : storedAtoms (contract space) = []) (subject : Pattern) :
    admittedAnswers admits space subject = [] := by
  unfold admittedAnswers
  split_ifs
  · rw [matchResults, empty]
    rfl
  · rfl

/-- **A family of evaluators indexed by an ambient space takes its rules from
the spaces**: from the ambient space for the ambient root step, and from the
space of the run for the root step of a run.  The member at a space that
stores no atom answers no ambient root step, and every member answers no root
step of a run whose space stores no atom. -/
def FamilyRulesFromSpaces (family : Pattern → BasePremiseEvaluator) : Prop :=
  FamilyRulesFromSpace family ∧ ∀ space : Pattern, RulesFromSpace (family space)

/-- **Positive**: the family of the evaluators of a region, under every
guard. -/
theorem regionEvaluator_rulesFromSpaces (admits : Pattern → Bool) :
    FamilyRulesFromSpaces (regionEvaluator admits) := by
  constructor
  · intro space empty lang bindings
    rw [regionEvaluator_rootPremise, admittedAnswers_of_stores_nothing admits empty]
    rfl
  · intro space lang bindings empty
    rw [regionEvaluator_runPremise, admittedAnswers_of_stores_nothing admits empty]
    rfl

/-- **The family that answers the root step of a run from the ambient
space**: the space of the run is not read. -/
def ambientAnswersRuns (ambientSpace : Pattern) : BasePremiseEvaluator :=
  fun _ bindings premise =>
    match premise with
    | .relationQuery "AmbientStep" [subject, .fvar answer] =>
        (matchResults (contract ambientSpace) (contract (applyBindings bindings subject))).map
          fun result => (answer, result) :: bindings
    | .relationQuery "PrimeStep" [_, subject, .fvar answer] =>
        (matchResults (contract ambientSpace) (contract (applyBindings bindings subject))).map
          fun result => (answer, result) :: bindings
    | _ => []

/-- It takes the rules of the ambient root step from the ambient space. -/
theorem ambientAnswersRuns_rulesFromSpace : FamilyRulesFromSpace ambientAnswersRuns := by
  intro space empty lang bindings
  show (matchResults (contract space)
    (contract (applyBindings bindings (.fvar "subject")))).map _ = []
  rw [matchResults, empty]
  rfl

/-- **Negative**: it does not take the rules of a run from the space of the
run.  At the ambient space of the rule `x ⟶ x` it answers the root step of a
run in the empty space. -/
theorem ambientAnswersRuns_not_rulesFromSpaces : ¬ FamilyRulesFromSpaces ambientAnswersRuns := by
  rintro ⟨-, fromRun⟩
  have silent := fromRun (ruleSpace [identityRule]) ambient
    [("subject", unitAtom), ("space", emptySpace)]
    (by
      rw [show applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "space") =
        emptySpace by simp [applyBindings]]
      decide)
  have found : unitAtom ∈ matchResults (contract (ruleSpace [identityRule]))
      (contract (applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "subject"))) := by
    rw [contract_ruleSpace,
      show applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "subject") =
        unitAtom by simp [applyBindings],
      show contract unitAtom = unitAtom by decide]
    exact identity_answers _
  have answered : (("answer", unitAtom) :: [("subject", unitAtom), ("space", emptySpace)]) ∈
      ambientAnswersRuns (ruleSpace [identityRule]) ambient
        [("subject", unitAtom), ("space", emptySpace)] runPremise :=
    List.mem_map.mpr ⟨unitAtom, found, rfl⟩
  rw [silent] at answered
  cases answered

/-- **Negative**: the family of a listing does not take its rules from the
spaces, where the listed theory has a step. -/
theorem listedFamily_not_rulesFromSpaces {source : GSLT.{0}} (listing : StepListing source)
    {term reduct : source.Term} (step : source.rewrites term reduct) :
    ¬ FamilyRulesFromSpaces (listedFamily listing.code listing.next) :=
  fun fromSpaces => listedFamily_not_rulesFromSpace listing step fromSpaces.1

/-! ## A guard costs the weakness -/

/-- The space that stores an equation between one variable and itself answers
every subject that the guard admits with that subject. -/
theorem admittedAnswers_guardSpace {admits : Pattern → Bool} {subject : Pattern}
    (fixed : contract subject = subject) (admitted : admits subject = true) :
    admittedAnswers admits guardSpace subject = [subject] := by
  unfold admittedAnswers
  rw [fixed, if_pos admitted, guardSpace_contracted, matchResults_eq_filterMap, guardSpace,
    storedAtoms_spaceOfAtoms]
  simp [catchAll, atomResult_identity]

/-- **The answers under a guard that admits the unit atom and a bound
variable, and refuses some subject, are answers by stored rules for no
reading of the stored atoms.** -/
theorem guarded_not_answersByStoredRules {admits : Pattern → Bool}
    (unit : admits unitAtom = true) (bound : admits (.bvar 0) = true) {refused : Pattern}
    (fixed : contract refused = refused) (no : admits refused = false) :
    ¬ AnswersByStoredRules (admittedAnswers admits) := by
  rintro ⟨read, exact, shape⟩
  have stored : storedAtoms (contract guardSpace) = [catchAll] := by
    rw [guardSpace_contracted, guardSpace, storedAtoms_spaceOfAtoms]
  have atUnit := shape guardSpace unitAtom
  have atVariable := shape guardSpace (.bvar 0)
  have atRefused := shape guardSpace refused
  rw [stored, admittedAnswers_guardSpace (by decide) unit,
    show contract unitAtom = unitAtom by decide] at atUnit
  rw [stored, admittedAnswers_guardSpace (by rw [contract]) bound,
    show contract (Pattern.bvar 0) = .bvar 0 by rw [contract]] at atVariable
  rw [stored, admittedAnswers_of_not_admitted (by rw [fixed]; exact no), fixed] at atRefused
  cases readAs : read catchAll with
  | none =>
      simp [readAs, rootInstances] at atUnit
  | some rule =>
      obtain ⟨left, right⟩ := rule
      have leftExact := exact catchAll (left, right) readAs
      simp only [List.filterMap_cons, readAs, List.filterMap_nil, rootInstances, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at atUnit atVariable atRefused
      cases left with
      | fvar name => simp [matchPattern] at atRefused
      | bvar index => simp [matchPattern, unitAtom] at atUnit
      | apply label parameters =>
          have none : matchPattern (.apply label parameters) (.bvar 0) = [] :=
            List.eq_nil_iff_forall_not_mem.mpr fun _ => bvar_not_matched
          simp [none] at atVariable
      | lambda binder body => simp [isMatchCorrectAux] at leftExact
      | multiLambda arity binders body => simp [isMatchCorrectAux] at leftExact
      | subst body replacement => simp [isMatchCorrectAux] at leftExact
      | collection kind elements rest => simp [isMatchCorrectAux] at leftExact

/-- **The answers under the guard that admits what is no run are not answers
by stored rules.** -/
theorem notRun_not_answersByStoredRules : ¬ AnswersByStoredRules (admittedAnswers notRun) :=
  guarded_not_answersByStoredRules (by decide) (by decide)
    (refused := runPattern emptySpace unitAtom) (by decide) (by decide)

/-- **The answers under the guard that admits what has the head of an atom
are not answers by stored rules.** -/
theorem atomHead_not_answersByStoredRules : ¬ AnswersByStoredRules (admittedAnswers atomHead) :=
  guarded_not_answersByStoredRules (by decide) (by decide) (refused := emptySpace) (by decide)
    (by decide)

/-- **Nor are the answers under the guard that admits an atom that is no
run.** -/
theorem atomNotRun_not_answersByStoredRules :
    ¬ AnswersByStoredRules (admittedAnswers atomNotRun) :=
  guarded_not_answersByStoredRules (by decide) (by decide) (refused := emptySpace) (by decide)
    (by decide)

#print axioms regionEvaluator_answersAmbientBy
#print axioms regionEvaluator_answersRunBy
#print axioms matchingEvaluator_not_answersAmbientBy
#print axioms admittedAnswers_any_answersByStoredRules
#print axioms regionEvaluator_weak
#print axioms admittedAnswers_any_length_le
#print axioms regionEvaluator_rulesFromSpaces
#print axioms ambientAnswersRuns_not_rulesFromSpaces
#print axioms listedFamily_not_rulesFromSpaces
#print axioms guarded_not_answersByStoredRules
#print axioms notRun_not_answersByStoredRules
#print axioms atomHead_not_answersByStoredRules
#print axioms atomNotRun_not_answersByStoredRules
#print axioms admittedAnswers_of_stores_nothing
#print axioms ambientAnswersRuns_rulesFromSpace
#print axioms admittedAnswers_guardSpace

end Mettapedia.Logic.HostingStyles.AmbientRegions
