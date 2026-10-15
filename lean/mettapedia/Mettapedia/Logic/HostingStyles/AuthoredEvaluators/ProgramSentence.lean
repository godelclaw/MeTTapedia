import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.BetaProgram
import Mettapedia.Logic.HostingStyles.Guests.PatternNumbering

/-!
# The hosting sentence, with the program named

A presented candidate is a presentation with an evaluator of its premises that
respects its static equivalence (`PresentedCandidate`).  The evaluator is a
function that the candidate does not show.  A *programmed* candidate is a
presentation with a program: its evaluator is the evaluator of an equation
program, run by the shared engine (`ProgrammedCandidate`).  Everything about
it is data: the declarations of the presentation and the equations of the
program.

* `ProgrammedCandidate.Hosts` is the hosting sentence of the presented
  candidate that it gives (`ProgrammedCandidate.presented`).
* **The candidate of the route by a fixed evaluator is programmed**:
  `matchingProgrammed` is the probe with a space together with the matching
  program, and the presented candidate that it gives is `matchingProbe`
  itself (`matchingProgrammed_presented`).  So it hosts what `matchingProbe`
  hosts, and no more (`matchingProgrammed_hosts_firstOrderInstances`,
  `matchingProgrammed_hosts_instances_iff`,
  `matchingProgrammed_not_hosts_tabular`).
* The candidates of the route by own rewrites are programmed with the empty
  program (`silentTuringProgrammed_hosts_machines`).
* A program does not make a candidate weak: `climbProgrammed` hosts a theory
  that branches without bound along one reduction
  (`climbProgrammed_hosts`), and `betaProgrammed` hosts the pure λΠ-calculus
  with beta at every position (`betaProgrammed_hosts`).  And a program is not
  enough for a candidate:
  the label program respects no static equivalence of the probe, so it is the
  program of no candidate over it (`labelAuthored_no_candidate`).

## The negative example: an evaluator chosen from the sources

The authored evaluators are countably many (`isAuthored_countable`), for a
program is a finite list of equations.  The evaluators chosen from the step
relations of sources are not: for each set of numbers, the evaluator of the
theory in which exactly the numbers of the set step to their successors
respects the static equivalence, is a presented candidate over the probe with
the run constructor, and hosts its theory through the run rewrite
(`gateProbe`, `gateProbe_hosts`); different sets give different evaluators
(`gateEvaluator_injective`).  So **some presented candidate has no program**
(`exists_presented_without_program`).

What fails for such an evaluator is exactly this: it is a function that no
equation program computes.  For the evaluator of the tables whose rules
determine their right sides the question is not decided by its definition,
which takes the numbers of its terms by choice
(`determinedRunProbe_programmed_iff` states what a program for it would be).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.Authored (termPattern termPattern_injective)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti (Theory RuleTable FirstOrderTable rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.Guests (patternCode patternCode_injective)

/-! ## Programmed candidates -/

/-- **A programmed candidate**: a presentation together with a program for the
premises of its rewrites, whose evaluator respects its static equivalence. -/
structure ProgrammedCandidate where
  /-- The presentation. -/
  presentation : ValidatedLanguageDef
  /-- The program, with the proof that it halts on every query. -/
  authored : AuthoredEvaluator
  respects : RespectsStatics authored.evaluator presentation.language

namespace ProgrammedCandidate

/-- The equations of the program. -/
def program (candidate : ProgrammedCandidate) : Program := candidate.authored.program

/-- **The presented candidate that a programmed candidate gives**: its
evaluator is the evaluator of the program. -/
def presented (candidate : ProgrammedCandidate) : PresentedCandidate where
  presentation := candidate.presentation
  evaluator := candidate.authored.evaluator
  respects := candidate.respects

/-- The theory of a programmed candidate, with all its contexts. -/
def theory (candidate : ProgrammedCandidate) : ContextTheory.{0} := candidate.presented.theory

/-- **The hosting sentence, with the program named.** -/
def Hosts (candidate : ProgrammedCandidate) (sources : ContextTheory.{0} → Prop)
    (level : PrimeCandidate.Level) (demand : PrimeCandidate.Demand) : Prop :=
  candidate.presented.Hosts sources level demand

end ProgrammedCandidate

/-- Two presented candidates with one presentation and one evaluator are
one. -/
theorem presentedCandidate_eq {first second : PresentedCandidate}
    (presentations : first.presentation = second.presentation)
    (evaluators : first.evaluator = second.evaluator) : first = second := by
  cases first
  cases second
  cases presentations
  cases evaluators
  rfl

/-- **A presented candidate has a program** when its evaluator is authored. -/
theorem exists_programmed_iff (candidate : PresentedCandidate) :
    (∃ programmed : ProgrammedCandidate, programmed.presented = candidate) ↔
      IsAuthored candidate.evaluator := by
  constructor
  · rintro ⟨programmed, rfl⟩
    exact ⟨programmed.authored, rfl⟩
  · rintro ⟨authored, same⟩
    exact ⟨⟨candidate.presentation, authored, same ▸ candidate.respects⟩,
      presentedCandidate_eq rfl same⟩

/-! ## The route by a fixed evaluator, with its program -/

/-- **The candidate of the route by a fixed evaluator, with its program**: the
probe with a run constructor, a space that is a term and a variable atom,
together with the matching program. -/
def matchingProgrammed : ProgrammedCandidate where
  presentation := spacePresentation
  authored := matchingAuthored
  respects := by
    rw [matchingAuthored_evaluator]
    exact matchingProbe.respects

/-- **It is `matchingProbe`**: the evaluator of the matching program is the
matching evaluator. -/
theorem matchingProgrammed_presented : matchingProgrammed.presented = matchingProbe :=
  presentedCandidate_eq rfl matchingAuthored_evaluator

/-- Its program is the matching program: eighty-eight equations. -/
theorem matchingProgrammed_program :
    matchingProgrammed.program = matchingProgram ∧ matchingProgrammed.program.length = 88 :=
  ⟨rfl, rfl⟩

theorem matchingProgrammed_theory : matchingProgrammed.theory = matchingCandidate := by
  show matchingProgrammed.presented.theory = matchingProbe.theory
  rw [matchingProgrammed_presented]

/-- **Positive**: it is a host of the theories of first-order rule instances,
on terms. -/
theorem matchingProgrammed_hosts_firstOrderInstances :
    matchingProgrammed.Hosts FirstOrderInstances .terms .hosting := by
  show matchingProgrammed.presented.Hosts _ _ _
  rw [matchingProgrammed_presented]
  exact matchingProbe_hosts_firstOrderInstances

/-- Among the first-order tables it hosts the instances of exactly those whose
rules determine their right sides. -/
theorem matchingProgrammed_hosts_instances_iff {table : RuleTable}
    (firstOrder : FirstOrderTable table) :
    HostedBy (instanceTheory table).termsAlone matchingProgrammed.theory ↔
      DeterminedTable table := by
  rw [matchingProgrammed_theory]
  exact instances_hostedBy_matching_iff firstOrder

/-- **Negative**: it is no host of the theories given by a table, on terms. -/
theorem matchingProgrammed_not_hosts_tabular :
    ¬ matchingProgrammed.Hosts TabularTheory .terms .hosting := by
  show ¬ matchingProgrammed.presented.Hosts _ _ _
  rw [matchingProgrammed_presented]
  exact matchingProbe_not_hosts_tabular

/-- Its answers to the run premise are answers by stored rules, so through
the run rewrite it hosts no theory that branches without bound along one
reduction. -/
theorem matchingProgrammed_not_hostedBy_of_unboundedBranching {source : GSLT.{0}}
    (branching : UnboundedBranching source) :
    ¬ HostedBy source.termsAlone matchingProgrammed.theory :=
  storedRules_not_hostedBy_of_unboundedBranching matchingAuthored.answersRunBy
    matchingAuthored_answersByStoredRules branching

/-! ## Other programmed candidates -/

/-- The probe together with the universal Turing theory, with the empty
program. -/
def silentTuringProgrammed : ProgrammedCandidate where
  presentation := turingPresentation
  authored := silentAuthored
  respects := silentAuthored_respectsStatics _

/-- **Positive**: a candidate that hosts by rewrites of its own needs no
program.  With the empty program it is a host of the Turing machines. -/
theorem silentTuringProgrammed_hosts_machines :
    silentTuringProgrammed.Hosts MachineTheory .terms .hosting :=
  turingProbe_hosts_machines silentTuringProgrammed.presented rfl

/-- The probe with a space, with the climbing program. -/
def climbProgrammed : ProgrammedCandidate where
  presentation := spacePresentation
  authored := climbAuthored
  respects := climbAuthored_respectsStatics

/-- **A program does not make a candidate weak**: this one hosts a theory that
branches without bound along one reduction, which the candidate with the
matching program does not host. -/
theorem climbProgrammed_hosts :
    HostedBy climbTheory.termsAlone climbProgrammed.theory ∧
      ¬ HostedBy climbTheory.termsAlone matchingProgrammed.theory :=
  ⟨climbAuthored_hosts,
    matchingProgrammed_not_hostedBy_of_unboundedBranching climbTheory_unboundedBranching⟩

/-- The probe with a space, with the beta program. -/
def betaProgrammed : ProgrammedCandidate where
  presentation := spacePresentation
  authored := betaAuthored
  respects := betaAuthored_respectsStatics

/-- **A candidate whose program runs the pure λΠ-calculus**: through one run
rewrite it hosts beta at every position, which the candidate with the
matching program does not host. -/
theorem betaProgrammed_hosts :
    HostedBy ((rewritingTheory (Theory.ofTable ∅)).gslt ()).termsAlone betaProgrammed.theory ∧
      ¬ HostedBy ((rewritingTheory (Theory.ofTable ∅)).gslt ()).termsAlone
        matchingProgrammed.theory :=
  ⟨betaAuthored_hosts,
    matchingProgrammed_not_hostedBy_of_unboundedBranching (rewritingTheory_unboundedBranching _)⟩

/-- **Negative**: the label program is the program of no candidate over the
probe with a space. -/
theorem labelAuthored_no_candidate :
    ¬ ∃ candidate : ProgrammedCandidate,
      candidate.presentation = spacePresentation ∧ candidate.authored = labelAuthored := by
  rintro ⟨⟨presentation, authored, respects⟩, rfl, rfl⟩
  exact labelAuthored_not_respectsStatics respects

/-! ## The authored evaluators are countably many -/

instance termCountable : Countable Term :=
  Function.Injective.countable (f := fun term : Term => patternCode (termPattern term))
    fun _ _ same => termPattern_injective (patternCode_injective same)

instance equationCountable : Countable DeterministicEquations.Equation :=
  Function.Injective.countable
    (f := fun equation : DeterministicEquations.Equation =>
      (equation.name, equation.head, equation.params, equation.body))
    (by
      rintro ⟨firstName, firstHead, firstParams, firstBody⟩
        ⟨secondName, secondHead, secondParams, secondBody⟩ same
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl, rfl, rfl⟩ := same
      rfl)

instance authoredCountable : Countable AuthoredEvaluator :=
  Function.Injective.countable (f := AuthoredEvaluator.program) (by
    rintro ⟨firstProgram, _⟩ ⟨secondProgram, _⟩ same
    cases (same : firstProgram = secondProgram)
    rfl)

/-- **The authored evaluators are countably many.** -/
theorem isAuthored_countable : {base : BasePremiseEvaluator | IsAuthored base}.Countable := by
  have range : {base : BasePremiseEvaluator | IsAuthored base} =
      Set.range AuthoredEvaluator.evaluator := by
    ext base
    exact Iff.rfl
  rw [range]
  exact Set.countable_range _

/-! ## Evaluators chosen from sources -/

/-- **The theory of a set of numbers**: exactly the numbers of the set step,
each to its successor. -/
def gateTheory (gates : Set Nat) : GSLT.{0} where
  Term := Nat
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun term next => term ∈ gates ∧ next = term + 1
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- The reducts of a number in the theory of a set. -/
noncomputable def gateNext (gates : Set Nat) (term : Nat) : List Nat :=
  open Classical in if term ∈ gates then [term + 1] else []

/-- The theory of a set is listed. -/
noncomputable def gateListing (gates : Set Nat) : StepListing (gateTheory gates) where
  code := fun (term : Nat) => term
  injective := fun _ _ same => same
  next := gateNext gates
  branches := fun (term next : Nat) => by
    show term ∈ gates ∧ next = term + 1 ↔ next ∈ gateNext gates term
    unfold gateNext
    by_cases open_ : term ∈ gates
    · simp [open_]
    · simp [open_]
  discrete := fun _ _ same => same

/-- **The evaluator chosen from the theory of a set.** -/
noncomputable def gateEvaluator (gates : Set Nat) : BasePremiseEvaluator :=
  stepEvaluator (gateListing gates).code (gateListing gates).next

theorem gateEvaluator_run (gates : Set Nat) (term : Nat) :
    gateEvaluator gates probeWithRun [("subject", numeral term)] runPremise =
      (gateNext gates term).map fun reduct =>
        ("answer", numeral reduct) :: [("subject", numeral term)] := by
  show stepAnswers (gateListing gates).code (gateListing gates).next _ (.fvar "subject") "answer" = _
  rw [stepAnswers_eq (gateListing gates).injective (gateListing gates).next "answer"
    (term := (term : Nat)) (by simp [applyBindings, contract_numeral]; rfl)]
  rfl

/-- **Different sets give different evaluators.** -/
theorem gateEvaluator_injective : Function.Injective gateEvaluator := by
  intro first second same
  ext term
  have answers := congrFun (congrFun (congrFun same probeWithRun) [("subject", numeral term)])
    runPremise
  rw [gateEvaluator_run, gateEvaluator_run] at answers
  have lengths := congrArg List.length answers
  rw [List.length_map, List.length_map] at lengths
  unfold gateNext at lengths
  by_cases inFirst : term ∈ first <;> by_cases inSecond : term ∈ second <;>
    simp [inFirst, inSecond] at lengths ⊢

/-- **The presented candidate of a set**: the probe with the run constructor
under the evaluator chosen from the theory of the set. -/
noncomputable def gateProbe (gates : Set Nat) : PresentedCandidate where
  presentation := runPresentation
  evaluator := gateEvaluator gates
  respects := stepEvaluator_respectsStatics _ _

/-- It hosts the theory of its set, on terms, through the run rewrite. -/
theorem gateProbe_hosts (gates : Set Nat) :
    HostedBy (gateTheory gates).termsAlone (gateProbe gates).theory :=
  ⟨runMap (gateListing gates), runMap_hosting (gateListing gates)⟩

/-- **Positive**: the evaluator of the empty set answers nothing to the run
premise at a numeral. -/
theorem gateEvaluator_empty (term : Nat) :
    gateEvaluator ∅ probeWithRun [("subject", numeral term)] runPremise = [] := by
  rw [gateEvaluator_run]
  simp [gateNext]

/-- **Some set of numbers has an evaluator that no program computes.** -/
theorem exists_gates_not_authored : ∃ gates : Set Nat, ¬ IsAuthored (gateEvaluator gates) := by
  by_contra none
  have all : ∀ gates : Set Nat, IsAuthored (gateEvaluator gates) := fun gates => by
    by_contra unauthored
    exact none ⟨gates, unauthored⟩
  have countable : (Set.range gateEvaluator).Countable :=
    isAuthored_countable.mono (by
      rintro _ ⟨gates, rfl⟩
      exact all gates)
  obtain ⟨number, numbered⟩ := Set.countable_iff_exists_injective.mp countable
  exact Function.cantor_injective
    (fun gates : Set Nat => number ⟨gateEvaluator gates, Set.mem_range_self gates⟩)
    (fun first second same => gateEvaluator_injective (congrArg Subtype.val (numbered same)))

/-- **The negative example.**  Some presented candidate over the probe with
the run constructor, whose evaluator is chosen from the step relation of a
source that it hosts through the run rewrite, has no program: its evaluator
respects the static equivalence and is the evaluator of no equation
program. -/
theorem exists_presented_without_program :
    ∃ (candidate : PresentedCandidate) (source : GSLT.{0}),
      candidate.presentation = runPresentation ∧ HostedBy source.termsAlone candidate.theory ∧
        ¬ ∃ programmed : ProgrammedCandidate, programmed.presented = candidate := by
  obtain ⟨gates, unauthored⟩ := exists_gates_not_authored
  exact ⟨gateProbe gates, gateTheory gates, rfl, gateProbe_hosts gates,
    fun programmed => unauthored ((exists_programmed_iff (gateProbe gates)).mp programmed)⟩

/-- **What a program for the evaluator of the tables whose rules determine
their right sides would be.**  That evaluator takes the numbers of its terms
by choice; whether it is authored is not decided by its definition. -/
theorem determinedRunProbe_programmed_iff :
    (∃ programmed : ProgrammedCandidate, programmed.presented = determinedRunProbe) ↔
      IsAuthored determinedEvaluator :=
  exists_programmed_iff determinedRunProbe

#print axioms matchingProgrammed
#print axioms matchingProgrammed_presented
#print axioms matchingProgrammed_hosts_firstOrderInstances
#print axioms matchingProgrammed_hosts_instances_iff
#print axioms matchingProgrammed_not_hosts_tabular
#print axioms matchingProgrammed_not_hostedBy_of_unboundedBranching
#print axioms silentTuringProgrammed_hosts_machines
#print axioms climbProgrammed_hosts
#print axioms betaProgrammed_hosts
#print axioms labelAuthored_no_candidate
#print axioms isAuthored_countable
#print axioms gateEvaluator_injective
#print axioms gateProbe_hosts
#print axioms exists_gates_not_authored
#print axioms exists_presented_without_program
#print axioms determinedRunProbe_programmed_iff

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
