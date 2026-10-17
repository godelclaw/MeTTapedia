import Mettapedia.Logic.HostingStyles.AmbientRegions.InRuns
import Mettapedia.Logic.HostingStyles.AmbientRegions.AllHeadedHosting
import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedScoped
import Mettapedia.Logic.HostingStyles.LocatedAtoms.Summary

/-!
# The ambient space with a run as a region, beside the ambient member and located atoms

The sources are the theories given by a table of rules without binder whose
right sides mention only variables of their left sides, on terms and, on the
terms with free variables below a width, with all contexts.  "Silent" means
an ambient space that answers nothing for a run (`RunSilent`).

| | ambient member | contained (`containedRun`) | scoped (`scopedRun`) | located atoms |
|---|---|---|---|---|
| class hosted, on terms and with contexts | the theories of its table (`member_hostOf_tabularAt`, `member_hostOf_scopedTabularAt`) | the same, at the space of the table (`contained_hostOf_tabularAt`, `contained_hostOf_scopedTabularAt`); a term without a run steps as in the ambient member (`contained_termStep_iff_member`); on terms a silent member hosts every table, in runs (`contained_hostOf_firstOrderTabular_inRuns`), and not with contexts (`contained_singleRun_not_hosting_scoped`) | the same (`scoped_hostOf_tabularAt`, `scoped_hostOf_scopedTabularAt`, `scoped_termStep_iff_member`) | every table, one candidate (`located_hostOf_firstOrderTabular`, `located_hostOf_scopedFirstOrderTabular`) |
| static equivalence | quotation and dropping (`ambient_quoteDropOnly`) | quotation and dropping (`contained_quoteDropOnly`); a term equal to a run is a run (`eq_runTermIn_of_related`) | quotation and dropping (`scoped_quoteDropOnly`) | five laws (`located_not_quoteDropOnly`) |
| evaluator | the matching evaluator with its space fixed (`matchingEvaluator_run_eq_ambient`) | the same for the ambient root step, the matching evaluator for the root step of a run (`regionEvaluator_rootPremise_any`, `regionEvaluator_runPremise_any`); weak for both (`regionEvaluator_weak`); rules from the two spaces (`regionEvaluator_rulesFromSpaces`) | the same evaluator | reads a normal form (`locatedEvaluator_respectsStatics`); the matching evaluator is unsound there (`matching_foreign_step`) |
| a part in another space | no: no run (`ambient_not_declaresRun`) | yes; each part by its own space only (`contained_pairAtoms_termStep_iff`, `matching_mixedCoins`); any tree of runs (`contained_tree_step_iff`) | yes; each part by its own space and the ambient one (`scoped_mixedCoins_argument_steps`) | yes (`pair_termStep_inv`) |
| what a region sees of the outside | no region | at silent ambient spaces nothing: `contained_run_step_ambient_irrelevant`, `contained_run_step_iff`; a run in a run sees its own space only (`contained_nested_step_iff`); at other ambient spaces the ambient rules reach it (`anySubject_run_depends_on_ambient`, `anySubject_ambient_reaches_inside`) | the ambient space (`scoped_run_step_iff`, `scoped_run_depends_on_ambient`), and not the space of a run around it (`scoped_nested_step_iff`, `scoped_nested_outer_unseen`) | a run of a run is the inner run (`runTerm_run`) |
| whether a space can step | yes (`ambient_space_steps`) | yes (`anySubject_space_steps`); under the guard `atomHead` no, at stages of atoms (`contained_space_static`) | yes; under the guard no (`scoped_space_static`) | no (`located_space_static`) |

Two guards and three changes of the presentation remove what the untyped root
step lets through:

* `notRun` (the evaluator answers for no run): every ambient space is silent,
  so containment holds at every ambient space
  (`contained_run_step_iff_of_refuses`).
* `atomHead` (the evaluator answers for a subject with the head of an atom):
  no space and no name steps at a stage of atoms; a bound variable of sort
  `Space` still does (`boundSpace_steps`).
* A guard costs the weakness of the evaluator
  (`guarded_not_answersByStoredRules`).
* `headedContained` (eight root steps headed by the constructors of atoms, in
  place of the one with a variable): with the evaluator unchanged, contained
  at every ambient space, no space and no name step at every stage, and the
  evaluator weak (`headed_weak_contained_static`); it loses the rules whose
  left side is a variable (`headed_variableRule_not_preserved`).  The root
  step of a run keeps a variable as its subject (`headed_runRoot_unheaded`).
* `allHeaded` (the root step of a run headed too, by eight root steps of a
  run): with the evaluator unchanged, at every ambient space and for every
  subject the steps of a run are the runs of the steps of its subject in the
  member at its space (`allHeaded_run_step_iff`); a run in a run sees its own
  space alone, whatever the outer and the ambient space store
  (`allHeaded_nested_step_iff`); no space and no name steps, and the
  evaluator is weak (`allHeaded_weak_contained_static`).  It loses the rules
  whose left side is a variable inside a run too
  (`allHeaded_variableRule_not_preserved`).
* `headedScoped` (the scoped presentation with the eight root steps in place
  of the ambient root step): with the evaluator unchanged, at every ambient
  space the steps of a run are those by the rules of either space
  (`headedScoped_run_step_iff`); every step of `headedContained` is a step of
  it (`step_headedContained_headedScoped`) and one step is its own
  (`headedScoped_alone_steps`); no space and no name steps, and the evaluator
  is weak (`headedScoped_weak_scoped_static`).

The contained reading, in its four forms:

| | every ambient space | every subject | a run in a run | evaluator weak | no space steps | tables hosted at their space |
|---|---|---|---|---|---|---|
| `containedRun`, no guard | the silent ones (`contained_run_step_iff`, `anySubject_run_depends_on_ambient`) | a subject without a run, or a silent space of the run (`contained_run_step_iff`) | a silent outer space (`contained_nested_step_iff`) | yes (`regionEvaluator_weak`) | no (`anySubject_space_steps`) | all (`contained_hostOf_tabularAt`) |
| `containedRun`, guard `atomNotRun` | yes (`atomNotRun_containment`) | yes (`atomNotRun_containment`) | yes (`contained_nested_step_iff`, `runSilent_atomNotRun`) | no (`atomNotRun_not_answersByStoredRules`) | at stages of atoms (`contained_space_static`) | all (`contained_hostOf_tabularAt`, `atomNotRun_admitsAtoms`) |
| `headedContained`, no guard | yes (`headed_run_step_ambient_irrelevant`) | the atoms of terms (`headed_runAtom_step_iff`), not a bound variable (`headed_runRoot_unheaded`) | the outer space is asked for the inner run as a whole (`headed_nested_step_iff`, `headed_nested_outer_rewrites`) | yes (`headed_weak_contained_static`) | yes (`headed_space_static`) | those without a variable as a left side (`headed_hostOf_tabularAt`); in runs, on terms, all (`headed_hostOf_firstOrderTabular_inRuns`) |
| `allHeaded`, no guard | yes (`allHeaded_run_step_ambient_irrelevant`) | yes (`allHeaded_run_step_iff`) | yes (`allHeaded_nested_step_iff`) | yes (`allHeaded_weak_contained_static`) | yes (`allHeaded_space_static`) | those without a variable as a left side (`allHeaded_hostOf_tabularAt`); in runs, on terms, the same at every ambient space (`allHeaded_hostOf_tabular_inRuns`) |

The scoped reading, in its two forms:

| | every ambient space | a run in a run | evaluator weak | no space steps | tables hosted at their space |
|---|---|---|---|---|---|
| `scopedRun`, no guard | the silent ones (`scoped_run_step_iff`), and not beyond them (`scoped_run_needs_silent`) | a silent ambient and a silent outer space (`scoped_nested_step_iff`) | yes (`regionEvaluator_weak`) | no (`anySubject_space_steps`) | all (`scoped_hostOf_tabularAt`) |
| `headedScoped`, no guard | yes (`headedScoped_run_step_iff`) | a silent outer space (`headedScoped_nested_step_iff`) | yes (`headedScoped_weak_scoped_static`) | yes (`headedScoped_space_static`) | those without a variable as a left side (`headedScoped_hostOf_tabularAt`) |

Not in either presentation: a rewrite that hands the space of a run to a run
inside its subject,
`run(outer, X) ~> run(outer, Y) ⊢ run(outer, run(inner, X)) ~> run(outer, run(inner, Y))`.
With it the scoped run would be a lexical scope.

The rows are also theorems: `hosting_row`, `statics_row`, `evaluator_row`,
`otherSpace_row`, `outside_row`, `spaceStep_row`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory withChoice chooseLeft chooseRight)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Logic.HostingStyles.AuthoredEvaluators (AnswersByStoredRules AnswersRunBy)
open Mettapedia.Logic.HostingStyles.LocatedAtoms
  (located locatedTheory locatedEvaluator located_hostOf_firstOrderTabular
    located_hostOf_scopedFirstOrderTabular located_not_quoteDropOnly
    locatedEvaluator_respectsStatics matchingEvaluator_not_respectsStatics matching_foreign_step
    runAtom takeAll)

/-! ## Located atoms: a space has no transition -/

/-- Every rewrite of the candidate with located atoms is headed by a
constructor of atoms: it has the rewrites of the candidate in which atoms
reduce. -/
theorem located_headedIn_atom : rewritesHeadedIn located ["Atom"] = true := by decide

/-- **With located atoms no space has a transition**, at every stage and
under every evaluator. -/
theorem located_space_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term located ⟨.base "Space", stage⟩) :
    ¬ TermStep base located term next := by
  intro step
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts located_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact absurd (TypeExpr.base.inj type) (by decide)

/-- **With located atoms no name has a transition**, at every stage and under
every evaluator. -/
theorem located_name_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term located ⟨.base "CandidateName", stage⟩) :
    ¬ TermStep base located term next := by
  intro step
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts located_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact absurd (TypeExpr.base.inj type) (by decide)

/-! ## The rows -/

variable {declared : Contexts.Interface → Prop}

/-- **The class hosted, on terms and with contexts.**  At the space of a
table of first-order rules with bound right sides, the ambient member, the
contained presentation and the scoped presentation are hosts of the theories
given by that table, on terms and with all contexts; the candidate with
located atoms is a host of the theories of every such table; and on terms the
member of the contained presentation at the empty space is a host of the
theories of every such table, each term read in a run. -/
theorem hosting_row {table : RuleTable} (admitted : BoundFirstOrder table)
    (free : AtomsFree declared) :
    (HostOf (ambientTheory (tableSpace table))
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting ∧
      HostOf ((ambientTheory (tableSpace table)).regionReading declared)
        (fun source => ∃ (theory : Theory) (width : Nat),
          theory.Tabular table ∧ source = scopedRewriting width theory)
        .contexts .hosting) ∧
    (HostOf (containedTheory anySubject (tableSpace table).1)
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting ∧
      HostOf ((containedTheory anySubject (tableSpace table).1).regionReading declared)
        (fun source => ∃ (theory : Theory) (width : Nat),
          theory.Tabular table ∧ source = scopedRewriting width theory)
        .contexts .hosting) ∧
    (HostOf (scopedTheory anySubject (tableSpace table).1)
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting ∧
      HostOf ((scopedTheory anySubject (tableSpace table).1).regionReading declared)
        (fun source => ∃ (theory : Theory) (width : Nat),
          theory.Tabular table ∧ source = scopedRewriting width theory)
        .contexts .hosting) ∧
    (HostOf (locatedTheory.regionReading declared) FirstOrderTabular .terms .hosting ∧
      HostOf (locatedTheory.regionReading declared) ScopedFirstOrderTabular .contexts .hosting) ∧
    HostOf (containedTheory anySubject emptySpace) FirstOrderTabular .terms .hosting :=
  ⟨⟨member_hostOf_tabularAt admitted, member_hostOf_scopedTabularAt admitted free⟩,
    ⟨contained_hostOf_tabularAt anySubject_admitsAtoms admitted,
      contained_hostOf_scopedTabularAt anySubject_admitsAtoms admitted free⟩,
    ⟨scoped_hostOf_tabularAt anySubject_admitsAtoms admitted,
      scoped_hostOf_scopedTabularAt anySubject_admitsAtoms admitted free⟩,
    ⟨located_hostOf_firstOrderTabular declared, located_hostOf_scopedFirstOrderTabular free⟩,
    emptyMember_hostOf_firstOrderTabular_inRuns⟩

/-- **The static equivalences**: quotation and dropping alone in the ambient
presentation and in the five presentations with a run as a region; not in
the candidate with located atoms. -/
theorem statics_row :
    QuoteDropOnly ambient ∧ QuoteDropOnly containedRun ∧ QuoteDropOnly scopedRun ∧
      QuoteDropOnly headedContained ∧ QuoteDropOnly allHeaded ∧ QuoteDropOnly headedScoped ∧
        ¬ QuoteDropOnly located :=
  ⟨ambient_quoteDropOnly, contained_quoteDropOnly, scoped_quoteDropOnly,
    headedContained_quoteDropOnly, allHeaded_quoteDropOnly, headedScoped_quoteDropOnly,
    located_not_quoteDropOnly⟩

/-- **The evaluators.**  Every member of the ambient family respects the
statics and takes its rules from its space.  The evaluator of a region
respects the statics of the five presentations under every guard, takes its
rules from the two spaces under every guard, and without a guard answers both
premises by one function that answers by stored rules; under the guards
`notRun` and `atomHead` its answers are not answers by stored rules.  The
evaluator of located atoms respects its statics, and the matching evaluator
does not. -/
theorem evaluator_row :
    ((∀ space : Pattern, RespectsStatics (ambientEvaluator space) ambient) ∧
      FamilyRulesFromSpace ambientEvaluator) ∧
    ((∀ (admits : Pattern → Bool) (space : Pattern),
        RespectsStatics (regionEvaluator admits space) containedRun ∧
          RespectsStatics (regionEvaluator admits space) scopedRun ∧
            RespectsStatics (regionEvaluator admits space) headedContained ∧
              RespectsStatics (regionEvaluator admits space) allHeaded ∧
                RespectsStatics (regionEvaluator admits space) headedScoped) ∧
      (∀ admits : Pattern → Bool, FamilyRulesFromSpaces (regionEvaluator admits)) ∧
      (∀ space : Pattern, ∃ answers : Pattern → Pattern → List Pattern,
        AnswersByStoredRules answers ∧
          AnswersAmbientBy (regionEvaluator anySubject space) space answers ∧
            AnswersRunBy (regionEvaluator anySubject space) answers) ∧
      ¬ AnswersByStoredRules (admittedAnswers notRun) ∧
        ¬ AnswersByStoredRules (admittedAnswers atomHead)) ∧
    (RespectsStatics locatedEvaluator located ∧ ¬ RespectsStatics matchingEvaluator located) :=
  ⟨⟨ambient_respectsStatics, ambientEvaluator_rulesFromSpace⟩,
    ⟨fun admits space => ⟨contained_respectsStatics admits space,
        scoped_respectsStatics admits space, headedContained_respectsStatics admits space,
        allHeaded_respectsStatics admits space, headedScoped_respectsStatics admits space⟩,
      regionEvaluator_rulesFromSpaces, regionEvaluator_weak, notRun_not_answersByStoredRules,
      atomHead_not_answersByStoredRules⟩,
    ⟨locatedEvaluator_respectsStatics, matchingEvaluator_not_respectsStatics⟩⟩

/-- **A part in another space.**  The ambient presentation has no run.  In
the contained presentation, under the matching evaluator, the application of
`choose heads tails` in the space of the rules of choice to `choose heads
tails` in the empty space steps in its function, every transition of it is a
step of its function, and its argument does not step.  In the scoped
presentation the argument steps by the ambient rules.  With located atoms,
under the matching evaluator, the atom in the empty space has a transition by
a rule of another space. -/
theorem otherSpace_row :
    ¬ DeclaresRun ambient ∧
    (TermStep (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) containedRun
        mixedCoins (mixedPair (.con "heads") coin) ∧
      (∀ target : Contexts.Term containedRun AtomsReduce.closedAtom,
        TermStep (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) containedRun
            mixedCoins target →
          ∃ next, Dedukti.Step (withChoice Theory.empty) coin next ∧
            target = mixedPair next coin) ∧
        ¬ TermStep (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) containedRun
          mixedCoins (mixedPair coin (.con "heads"))) ∧
    Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) scopedRun
      (.apply "App" [runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin),
        runPattern (ruleSpace []) (atomAt 0 coin)])
      (.apply "App" [runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin),
        runPattern (ruleSpace []) (atomAt 0 (.con "heads"))]) ∧
    TermStep matchingEvaluator located (runAtom [] 0 coin) (runAtom [takeAll] 0 (.con "u")) :=
  ⟨ambient_not_declaresRun, matching_mixedCoins,
    scoped_mixedCoins_argument_steps anySubject_admitsAtoms, matching_foreign_step⟩

/-- **What a region sees of the outside.**  Contained, under the guard that
admits no run: for every two ambient spaces a run has the same steps, the
runs of the steps of its subject in the member at its space.  Contained,
without a guard: the same at ambient spaces that answer nothing for a run,
and a run whose steps depend on the ambient space otherwise.  Scoped: a run
whose steps depend on the ambient space, between two ambient spaces that
answer nothing for a run; and a run in a run that does not see the space
around it.  With headed root steps and without a guard: for every two ambient
spaces a run has the same steps.  With every root step headed and without a
guard: at every ambient space the steps of a run are the runs of the steps of
its subject in the member at its space.  Scoped with headed root steps and
without a guard: at every ambient space the steps of a run are those by the
rules of either space. -/
theorem outside_row :
    (∀ first second space subject target : Pattern,
        (Step (regionEvaluator notRun first) containedRun (runPattern space subject) target ↔
          Step (regionEvaluator notRun second) containedRun (runPattern space subject) target) ∧
        (Step (regionEvaluator notRun first) containedRun (runPattern space subject) target ↔
          ∃ next, target = runPattern space next ∧
            Step (regionEvaluator notRun space) containedRun subject next)) ∧
    ((∀ first second space subject target : Pattern, RunSilent anySubject first →
        RunSilent anySubject second →
          (Step (regionEvaluator anySubject first) containedRun (runPattern space subject) target ↔
            Step (regionEvaluator anySubject second) containedRun (runPattern space subject)
              target)) ∧
      Step (regionEvaluator anySubject (ruleSpace [identityRule])) containedRun
        (runPattern emptySpace (atomAt 0 (.srt .type)))
        (runPattern emptySpace (atomAt 0 (.srt .type))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject emptySpace) containedRun
          (runPattern emptySpace (atomAt 0 (.srt .type))) target) ∧
    ((Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) scopedRun
        (runPattern (ruleSpace []) (atomAt 0 coin))
        (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject (ruleSpace [])) scopedRun
          (runPattern (ruleSpace []) (atomAt 0 coin)) target) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject (ruleSpace [])) scopedRun
          (runPattern (ruleSpace [chooseLeft, chooseRight])
            (runPattern (ruleSpace []) (atomAt 0 coin))) target) ∧
    (∀ first second space subject target : Pattern,
      Step (regionEvaluator anySubject first) headedContained (runPattern space subject) target ↔
        Step (regionEvaluator anySubject second) headedContained (runPattern space subject)
          target) ∧
    (∀ ambientSpace space subject target : Pattern,
      Step (regionEvaluator anySubject ambientSpace) allHeaded (runPattern space subject) target ↔
        ∃ next, target = runPattern space next ∧
          Step (regionEvaluator anySubject space) allHeaded subject next) ∧
    ∀ ambientSpace space subject target : Pattern,
      Step (regionEvaluator anySubject ambientSpace) headedScoped (runPattern space subject)
          target ↔
        ∃ next, target = runPattern space next ∧
          (Step (regionEvaluator anySubject ambientSpace) headedScoped subject next ∨
            Step (regionEvaluator anySubject space) ambient subject next) :=
  ⟨fun first second _ _ _ =>
      ⟨contained_run_step_ambient_irrelevant (runSilent_notRun first) (runSilent_notRun second),
        contained_run_step_iff_of_refuses notRun_run⟩,
    ⟨fun _ _ _ _ _ silentFirst silentSecond =>
        contained_run_step_ambient_irrelevant silentFirst silentSecond,
      anySubject_run_depends_on_ambient.1, anySubject_run_depends_on_ambient.2⟩,
    ⟨⟨scoped_runCoin_steps anySubject_admitsAtoms,
        scoped_runCoin_normal_at_empty anySubject_admitsAtoms⟩,
      scoped_nested_outer_unseen anySubject_admitsAtoms⟩,
    fun first second _ _ _ => headed_run_step_ambient_irrelevant first second,
    fun _ _ _ _ => allHeaded_run_step_iff, fun _ _ _ _ => headedScoped_run_step_iff⟩

/-- **Whether a space can step.**  In the ambient member a space has a
transition; so it has in the contained and in the scoped presentation without
a guard.  Under the guard `atomHead` no space has a transition at a stage of
atoms, in the three, and a bound variable of sort `Space` has one.  With
headed root steps, contained or scoped, with every root step headed and with
located atoms no space has a transition, at every stage and under every
evaluator. -/
theorem spaceStep_row :
    (ambientTheory (listSpace [identityRule])).rewrites (interface := closedSpace) emptySpaceTerm
      emptySpaceTerm ∧
    ((containedTheory anySubject (ruleSpace [identityRule])).rewrites (interface := closedSpace)
        (emptySpaceIn containedRun (by decide)) (emptySpaceIn containedRun (by decide)) ∧
      (scopedTheory anySubject (ruleSpace [identityRule])).rewrites (interface := closedSpace)
        (emptySpaceIn scopedRun (by decide)) (emptySpaceIn scopedRun (by decide))) ∧
    ((∀ (space : SpaceTerm) (stage : List TypeExpr), (∀ type ∈ stage, type = .base "Atom") →
        ∀ term next : Contexts.Term ambient ⟨.base "Space", stage⟩,
          ¬ (guardedMember atomHead space).theory.rewrites term next) ∧
      (∀ (ambientSpace : Pattern) (stage : List TypeExpr),
        (∀ type ∈ stage, type = .base "Atom") →
          ∀ term next : Contexts.Term containedRun ⟨.base "Space", stage⟩,
            ¬ (containedTheory atomHead ambientSpace).rewrites term next) ∧
      (∀ (ambientSpace : Pattern) (stage : List TypeExpr),
        (∀ type ∈ stage, type = .base "Atom") →
          ∀ term next : Contexts.Term scopedRun ⟨.base "Space", stage⟩,
            ¬ (scopedTheory atomHead ambientSpace).rewrites term next) ∧
      (guardedMember atomHead (listSpace [identityRule])).theory.rewrites boundSpace boundSpace) ∧
    (∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
        (term next : Contexts.Term headedContained ⟨.base "Space", stage⟩),
      ¬ TermStep base headedContained term next) ∧
    (∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
        (term next : Contexts.Term allHeaded ⟨.base "Space", stage⟩),
      ¬ TermStep base allHeaded term next) ∧
    (∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
        (term next : Contexts.Term headedScoped ⟨.base "Space", stage⟩),
      ¬ TermStep base headedScoped term next) ∧
    ∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
      (term next : Contexts.Term located ⟨.base "Space", stage⟩),
      ¬ TermStep base located term next :=
  ⟨ambient_space_steps, anySubject_space_steps,
    ⟨fun space _ atomStage term next => ambient_space_static space atomStage term next,
      fun ambientSpace _ atomStage term next =>
        contained_space_static atomHead_refusesData ambientSpace atomStage term next,
      fun ambientSpace _ atomStage term next =>
        scoped_space_static atomHead_refusesData ambientSpace atomStage term next,
      boundSpace_steps⟩,
    fun _ _ term next => headed_space_static term next,
    fun _ _ term next => allHeaded_space_static term next,
    fun _ _ term next => headedScoped_space_static term next,
    fun _ _ term next => located_space_static term next⟩

#print axioms located_space_static
#print axioms located_name_static
#print axioms hosting_row
#print axioms statics_row
#print axioms evaluator_row
#print axioms otherSpace_row
#print axioms outside_row
#print axioms spaceStep_row
#print axioms located_headedIn_atom

end Mettapedia.Logic.HostingStyles.AmbientRegions
