import Mettapedia.Logic.HostingStyles.AmbientRegions.Nested

/-!
# The root rewrite matched by atoms only

The ambient root step `AmbientStep(subject, answer) ⊢ subject ~> answer`
declares its subject an atom and has a variable as left side: firing does not
read the declared sort, so a term of sort `Space` has a transition
(`ambient_space_steps`).  This module builds the members whose evaluator
answers the root step only for a subject that is an atom, as far as the head
of the subject says (`atomHead`): `guardedMember atomHead`, and
`containedMember atomHead`, `scopedMember atomHead`.

* **No space and no name has a transition** (`guarded_data_static`,
  `ambient_space_static`, `ambient_name_static`, `contained_space_static`,
  `contained_name_static`, `scoped_space_static`, `scoped_name_static`), at
  every stage of atoms.  Every binder of the three presentations binds an
  atom, so these are the stages that their terms reach.
* **Without the guard a space has a transition**, in the three presentations
  (`anySubject_space_steps`).
* **The head of the subject is not its sort** (`boundSpace_steps`): at a
  stage with a variable of sort `Space` that variable has a transition under
  the guard.  A bound variable has no head, and the guard has to accept bound
  variables: the atoms of terms beneath binders are subjects
  (`atomHead_admitsAtoms`).
* **Hosting, containment, scoping and two spaces under the guard** (`atomHead_nothing_lost`,
  `atomHead_containment`, `atomHead_scoping`, `atomHead_twoSpaces`): every
  statement of the earlier modules is for an arbitrary guard that admits the
  atoms of terms, and `atomHead` is one.

## What the framework would have to read

A rewrite fires through `StepAt.rule`, from a match of its left side and a
derivation of its premises; `rule.typeContext` is not an argument of either.
For the effect above with the unchanged evaluator, the rule clause would need
the premise

```
∀ entry ∈ rule.typeContext, ∀ value,
  initial.find? (·.1 == entry.1) = some (entry.1, value) →
    HasType lang FreeTypeContext.empty stage value entry.2
```

with `stage` the stage of the redex: the sorts of the binders above it, which
a congruence premise beneath a binder extends by the sort of that binder.
`StepAt` carries no stage.  For the root rewrite the premise is
`HasType lang ∅ stage subject (.base "Atom")`, and it decides the sort of the
subject at every stage, bound variables included
(`declaredSort_excludes_data`, `declaredSort_of_atom`), where the head does
not (`boundSpace_steps`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory patternVars usesOnly withChoice chooseLeft chooseRight)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## Languages in which only an atom is a redex, the ambient root step aside -/

/-- The heads of the left sides that have one. -/
def redexHeads : List String := ["App", "Pi", "Lam", "prime-drop", "prime-run"]

/-- The labels of the constructors of spaces and of names. -/
def dataHeads : List String := ["prime-space-empty", "prime-space-add", "prime-quote"]

/-- **In a language only an atom is a redex, the ambient root step aside**:
every rewrite other than the ambient root step is headed by a constructor of
atoms, and the constructors of spaces and of names are the two of a space and
quotation. -/
structure AtomsAreRedexes (lang : LanguageDef) : Prop where
  headed : ∀ rule ∈ lang.rewrites, rule = rootRule ∨
    ∃ label parameters, rule.left = .apply label parameters ∧ label ∈ redexHeads
  atoms : ∀ rule ∈ lang.terms, rule.label ∈ redexHeads → rule.category = "Atom"
  data : ∀ rule ∈ lang.terms, rule.category = "Space" ∨ rule.category = "CandidateName" →
    rule.label ∈ dataHeads
  plain : ∀ rule ∈ lang.terms, usesBareCollection? rule = false

/-- **Positive**: the ambient presentation. -/
theorem ambient_atomsAreRedexes : AtomsAreRedexes ambient where
  headed := by
    intro rule member
    rw [ambient_rewrites] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl rfl
      | exact .inr ⟨_, _, rfl, by decide⟩
  atoms := by decide
  data := by decide
  plain := by decide

/-- **Positive**: the contained presentation. -/
theorem contained_atomsAreRedexes : AtomsAreRedexes containedRun where
  headed := by
    intro rule member
    rw [contained_rewrites] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl rfl
      | exact .inr ⟨_, _, rfl, by decide⟩
  atoms := by decide
  data := by decide
  plain := by decide

/-- **Positive**: the scoped presentation. -/
theorem scoped_atomsAreRedexes : AtomsAreRedexes scopedRun where
  headed := by
    intro rule member
    rw [scoped_rewrites] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl rfl
      | exact .inr ⟨_, _, rfl, by decide⟩
  atoms := by decide
  data := by decide
  plain := by decide

/-- **Negative**: the probe with a run constructor reduces in its sort of
processes; its first rewrite is headed by a query. -/
theorem probeWithRun_not_atomsAreRedexes : ¬ AtomsAreRedexes probeWithRun := by
  intro reduces
  rcases reduces.headed MeTTaZero.queryRewrite (by rw [probeWithRun_rewrites]; simp) with
    same | ⟨label, parameters, left, listed⟩
  · exact absurd (congrArg RewriteRule.name same) (by decide)
  · have head : head? MeTTaZero.queryRewrite.left = some label := by rw [left]; rfl
    have query : head? MeTTaZero.queryRewrite.left = some "zero-query" := rfl
    obtain rfl : "zero-query" = label := Option.some.inj (query.symm.trans head)
    exact absurd listed (by decide)

/-- **A term of sort `Space` or of the sort of names, at a stage of atoms, is
headed by a constructor of spaces or by quotation.** -/
theorem dataHead_of_sorted {lang : LanguageDef} (reduces : AtomsAreRedexes lang)
    {stage : List TypeExpr} (atomStage : ∀ type ∈ stage, type = .base "Atom") {sort : String}
    (isData : sort = "Space" ∨ sort = "CandidateName") {pattern : Pattern}
    (sorted : OpenPatternWellSorted lang FreeTypeContext.empty stage (.base sort) pattern) :
    ∃ label arguments, pattern = .apply label arguments ∧ label ∈ dataHeads := by
  obtain ⟨typed, -, object, -⟩ := sorted
  cases typed with
  | bvar found =>
      obtain rfl : sort = "Atom" := TypeExpr.base.inj (atomStage _ (List.mem_of_getElem? found))
      rcases isData with wrong | wrong <;> exact absurd wrong (by decide)
  | fvar found => simp [FreeTypeContext.empty] at found
  | @constructor _ rule arguments member notBare argumentsTyped =>
      exact ⟨rule.label, arguments, rfl, reduces.data rule member isData⟩
  | subst _ _ => simp [isObjectPattern] at object
  | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
      elementsTyped =>
      have bare : usesBareCollection? rule = true :=
        (usesBareCollection?_eq_true_iff rule).mpr ⟨_, _, _, shape⟩
      rw [reduces.plain rule member] at bare
      cases bare

/-! ## No space and no name has a transition -/

/-- A guard admits no constructor of spaces and no quotation. -/
def RefusesData (admits : Pattern → Bool) : Prop :=
  ∀ (label : String) (arguments : List Pattern), label ∈ dataHeads →
    admits (.apply label arguments) = false

/-- **Positive**: the guard that admits what has the head of an atom. -/
theorem atomHead_refusesData : RefusesData atomHead := by
  intro label arguments listed
  simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> simp [atomHead]

/-- **Positive**: the guard that admits an atom that is no run. -/
theorem atomNotRun_refusesData : RefusesData atomNotRun := fun label arguments listed => by
  simp [atomNotRun, atomHead_refusesData label arguments listed]

/-- **Negative**: no guard. -/
theorem anySubject_not_refusesData : ¬ RefusesData anySubject :=
  fun refuses => absurd (refuses "prime-space-empty" [] (by decide)) (by decide)

variable {admits : Pattern → Bool}

/-- **Under a guard that admits no constructor of spaces and no quotation, no
space and no name has a transition**, at every stage of atoms: in every
language in which only an atom is a redex, the ambient root step aside, and
whose static equivalence is that of quotation and dropping. -/
theorem guarded_data_static {lang : LanguageDef} (reduces : AtomsAreRedexes lang)
    (quoteSorted : QuoteDropSorted lang) (refuses : RefusesData admits) (ambientSpace : Pattern)
    {stage : List TypeExpr} (atomStage : ∀ type ∈ stage, type = .base "Atom") {sort : String}
    (isData : sort = "Space" ∨ sort = "CandidateName")
    (term next : Contexts.Term lang ⟨.base sort, stage⟩) :
    ¬ TermStep (regionEvaluator admits ambientSpace) lang term next := by
  rintro ⟨redex, contractum, -, ⟨fuel, fired⟩, -⟩
  cases fuel with
  | zero => cases fired
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, -⟩ := exists_rule_of_stepAt fired
      rcases reduces.headed rule member with rfl | ⟨label, parameters, left, listed⟩
      · obtain ⟨answer, found, -⟩ := ambientRoot_inv matched premises
        obtain ⟨dataLabel, arguments, shape, isDataLabel⟩ :=
          dataHead_of_sorted reduces atomStage isData (contract_wellSorted quoteSorted redex.2)
        have admitted := (mem_admittedAnswers.mp found).1
        rw [shape, refuses dataLabel arguments isDataLabel] at admitted
        cases admitted
      · rw [left] at matched
        obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
        have typed : HasType lang FreeTypeContext.empty stage redex.1 (.base sort) := redex.2.1
        rw [shape] at typed
        obtain ⟨constructor, declared, sameLabel, type⟩ :=
          declared_constructor_of_hasType_apply typed
        have category := reduces.atoms constructor declared (sameLabel ▸ listed)
        rw [category] at type
        obtain rfl : sort = "Atom" := TypeExpr.base.inj type
        rcases isData with wrong | wrong <;> exact absurd wrong (by decide)

/-- **The member of the ambient presentation at a space, under a guard**, as
a presented candidate.  Under `atomHead` its evaluator answers the root step
only for a subject that has the head of an atom. -/
def guardedMember (admits : Pattern → Bool) (space : SpaceTerm) : PresentedCandidate where
  presentation := ambientPresentation
  evaluator := regionEvaluator admits space.1
  respects := ambient_respectsStatics_region admits space.1

/-- **Positive**: without a guard it has the transitions of the member of the
ambient family. -/
theorem guardedMember_any_rewrites_iff (space : SpaceTerm) {interface : Contexts.Interface}
    {term next : Contexts.Term ambient interface} :
    (guardedMember anySubject space).theory.rewrites term next ↔
      (ambientTheory space).rewrites term next := by
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    exact ⟨redex, contractum, termSetoid_base_irrelevant before,
      step_any_iff_ambientEvaluator.mp fired, termSetoid_base_irrelevant after⟩
  · rintro ⟨redex, contractum, before, fired, after⟩
    exact ⟨redex, contractum, termSetoid_base_irrelevant before,
      step_any_iff_ambientEvaluator.mpr fired, termSetoid_base_irrelevant after⟩

/-- **In the ambient presentation, under the guard, no space has a
transition.** -/
theorem ambient_space_static (space : SpaceTerm) {stage : List TypeExpr}
    (atomStage : ∀ type ∈ stage, type = .base "Atom")
    (term next : Contexts.Term ambient ⟨.base "Space", stage⟩) :
    ¬ (guardedMember atomHead space).theory.rewrites term next :=
  guarded_data_static ambient_atomsAreRedexes ambient_quoteDropSorted atomHead_refusesData space.1
    atomStage (.inl rfl) term next

/-- **In the ambient presentation, under the guard, no name has a
transition.** -/
theorem ambient_name_static (space : SpaceTerm) {stage : List TypeExpr}
    (atomStage : ∀ type ∈ stage, type = .base "Atom")
    (term next : Contexts.Term ambient ⟨.base "CandidateName", stage⟩) :
    ¬ (guardedMember atomHead space).theory.rewrites term next :=
  guarded_data_static ambient_atomsAreRedexes ambient_quoteDropSorted atomHead_refusesData space.1
    atomStage (.inr rfl) term next

/-- **In the contained presentation, under the guard, no space has a
transition.** -/
theorem contained_space_static (refuses : RefusesData admits) (ambientSpace : Pattern)
    {stage : List TypeExpr} (atomStage : ∀ type ∈ stage, type = .base "Atom")
    (term next : Contexts.Term containedRun ⟨.base "Space", stage⟩) :
    ¬ (containedTheory admits ambientSpace).rewrites term next :=
  guarded_data_static contained_atomsAreRedexes contained_quoteDropSorted refuses ambientSpace
    atomStage (.inl rfl) term next

/-- **In the contained presentation, under the guard, no name has a
transition.** -/
theorem contained_name_static (refuses : RefusesData admits) (ambientSpace : Pattern)
    {stage : List TypeExpr} (atomStage : ∀ type ∈ stage, type = .base "Atom")
    (term next : Contexts.Term containedRun ⟨.base "CandidateName", stage⟩) :
    ¬ (containedTheory admits ambientSpace).rewrites term next :=
  guarded_data_static contained_atomsAreRedexes contained_quoteDropSorted refuses ambientSpace
    atomStage (.inr rfl) term next

/-- **In the scoped presentation, under the guard, no space has a
transition.** -/
theorem scoped_space_static (refuses : RefusesData admits) (ambientSpace : Pattern)
    {stage : List TypeExpr} (atomStage : ∀ type ∈ stage, type = .base "Atom")
    (term next : Contexts.Term scopedRun ⟨.base "Space", stage⟩) :
    ¬ (scopedTheory admits ambientSpace).rewrites term next :=
  guarded_data_static scoped_atomsAreRedexes scoped_quoteDropSorted refuses ambientSpace
    atomStage (.inl rfl) term next

/-- **In the scoped presentation, under the guard, no name has a
transition.** -/
theorem scoped_name_static (refuses : RefusesData admits) (ambientSpace : Pattern)
    {stage : List TypeExpr} (atomStage : ∀ type ∈ stage, type = .base "Atom")
    (term next : Contexts.Term scopedRun ⟨.base "CandidateName", stage⟩) :
    ¬ (scopedTheory admits ambientSpace).rewrites term next :=
  guarded_data_static scoped_atomsAreRedexes scoped_quoteDropSorted refuses ambientSpace
    atomStage (.inr rfl) term next

/-! ## Without the guard, and what the head does not say -/

/-- The empty space, as a closed space of each presentation. -/
def emptySpaceIn (lang : LanguageDef) (declared : emptySpaceConstructor ∈ lang.terms) :
    Contexts.Term lang closedSpace :=
  ⟨emptySpace, wellSorted_apply_zero (lang := lang) (label := "prime-space-empty") declared⟩

/-- **Without the guard a space has a transition**, in the contained and in
the scoped presentation as in the ambient one: at the space of the rule
`x ⟶ x` the empty space steps to itself. -/
theorem anySubject_space_steps :
    (containedTheory anySubject (ruleSpace [identityRule])).rewrites (interface := closedSpace)
        (emptySpaceIn containedRun (by decide)) (emptySpaceIn containedRun (by decide)) ∧
      (scopedTheory anySubject (ruleSpace [identityRule])).rewrites (interface := closedSpace)
        (emptySpaceIn scopedRun (by decide)) (emptySpaceIn scopedRun (by decide)) := by
  have found : emptySpace ∈ admittedAnswers anySubject (ruleSpace [identityRule]) emptySpace := by
    refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
    rw [contract_ruleSpace, show contract emptySpace = emptySpace by decide]
    exact identity_answers emptySpace
  exact ⟨⟨_, _, .refl _, ⟨1, step_ambientRoot
      (show rootRule ∈ containedRun.rewrites by simp [contained_rewrites]) found⟩, .refl _⟩,
    ⟨_, _, .refl _, ⟨1, step_ambientRoot
      (show rootRule ∈ scopedRun.rewrites by simp [scoped_rewrites]) found⟩, .refl _⟩⟩

/-- A bound variable of sort `Space`, at the stage of one binder of a
space. -/
def boundSpace : Contexts.Term ambient ⟨.base "Space", [.base "Space"]⟩ :=
  ⟨.bvar 0, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The head of the subject is not its sort.**  At a stage with a variable
of sort `Space`, that variable has a transition under the guard, at the space
of the rule `x ⟶ x`: a bound variable has no head, and the evaluator is not
given the stage. -/
theorem boundSpace_steps :
    (guardedMember atomHead (listSpace [identityRule])).theory.rewrites boundSpace boundSpace := by
  refine ⟨boundSpace, boundSpace, .refl _,
    ⟨1, step_ambientRoot (show rootRule ∈ ambient.rewrites by simp [ambient_rewrites]) ?_⟩,
    .refl _⟩
  refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
  show Pattern.bvar 0 ∈ matchResults (contract (ruleSpace [identityRule])) (contract (.bvar 0))
  rw [contract_ruleSpace]
  exact identity_answers _

/-- **Negative**: the stage of that variable is no stage of atoms. -/
theorem boundSpace_stage_not_atoms :
    ¬ ∀ type ∈ [TypeExpr.base "Space"], type = TypeExpr.base "Atom" := by
  intro atoms
  exact absurd (TypeExpr.base.inj (atoms _ (List.mem_singleton.mpr rfl))) (by decide)

/-! ## The declared sort of the subject, as a judgment at the stage -/

/-- In the ambient presentation two constructors of one label have one
sort. -/
theorem ambient_label_category :
    ∀ first ∈ ambient.terms, ∀ second ∈ ambient.terms, first.label = second.label →
      first.category = second.category := by
  decide

/-- **A term of another sort does not have the sort that the root rewrite
declares for its subject**, at any stage: the judgment
`HasType lang ∅ stage subject (.base "Atom")` fails for it, bound variables
included. -/
theorem declaredSort_excludes_data {stage : List TypeExpr} {sort : String} (other : sort ≠ "Atom")
    (term : Contexts.Term ambient ⟨.base sort, stage⟩) :
    ¬ HasType ambient FreeTypeContext.empty stage term.1 (.base "Atom") := by
  intro asAtom
  have typed : HasType ambient FreeTypeContext.empty stage term.1 (.base sort) := term.2.1
  have object : isObjectPattern term.1 = true := term.2.2.2.1
  generalize term.1 = pattern at asAtom typed object
  cases typed with
  | bvar found =>
      cases asAtom with
      | bvar foundAtom =>
          rw [found] at foundAtom
          exact other (TypeExpr.base.inj (Option.some.inj foundAtom))
  | fvar found => simp [FreeTypeContext.empty] at found
  | @constructor _ rule arguments member notBare argumentsTyped =>
      obtain ⟨atomRule, atomMember, sameLabel, type⟩ := declared_constructor_of_hasType_apply asAtom
      have category := ambient_label_category atomRule atomMember rule member sameLabel
      rw [category] at type
      exact other (TypeExpr.base.inj type).symm
  | subst _ _ => simp [isObjectPattern] at object
  | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
      elementsTyped =>
      have bare : usesBareCollection? rule = true :=
        (usesBareCollection?_eq_true_iff rule).mpr ⟨_, _, _, shape⟩
      rw [ambient_atomsAreRedexes.plain rule member] at bare
      cases bare

/-- **Positive**: an atom has it, by its typing. -/
theorem declaredSort_of_atom {stage : List TypeExpr}
    (term : Contexts.Term ambient ⟨.base "Atom", stage⟩) :
    HasType ambient FreeTypeContext.empty stage term.1 (.base "Atom") :=
  term.2.1

/-- **The judgment separates where the head does not**: the bound variable of
sort `Space` has the head of an atom and does not have the sort of an atom at
its stage. -/
theorem boundSpace_head_and_sort :
    atomHead boundSpace.1 = true ∧
      ¬ HasType ambient FreeTypeContext.empty [.base "Space"] boundSpace.1 (.base "Atom") :=
  ⟨rfl, declaredSort_excludes_data (by decide) boundSpace⟩

/-! ## Hosting, containment, scoping and two spaces, under the guard -/

variable {declared : Contexts.Interface → Prop}

/-- **Nothing is lost under the guard**: at the space of a table both
presentations are hosts of the theories given by the table, on terms and
with all contexts. -/
theorem atomHead_nothing_lost {table : RuleTable} (admitted : BoundFirstOrder table)
    (free : AtomsFree declared) :
    (HostOf (containedTheory atomHead (tableSpace table).1)
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting ∧
      HostOf ((containedTheory atomHead (tableSpace table).1).regionReading declared)
        (fun source => ∃ (theory : Theory) (width : Nat),
          theory.Tabular table ∧ source = scopedRewriting width theory)
        .contexts .hosting) ∧
      HostOf (scopedTheory atomHead (tableSpace table).1)
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting ∧
      HostOf ((scopedTheory atomHead (tableSpace table).1).regionReading declared)
        (fun source => ∃ (theory : Theory) (width : Nat),
          theory.Tabular table ∧ source = scopedRewriting width theory)
        .contexts .hosting :=
  ⟨⟨contained_hostOf_tabularAt atomHead_admitsAtoms admitted,
      contained_hostOf_scopedTabularAt atomHead_admitsAtoms admitted free⟩,
    scoped_hostOf_tabularAt atomHead_admitsAtoms admitted,
    scoped_hostOf_scopedTabularAt atomHead_admitsAtoms admitted free⟩

/-- **Containment under the guard**: at two ambient spaces that answer
nothing for a run, a run has the same steps, and they are the runs of the
steps of its subject in the member at its space. -/
theorem atomHead_containment {first second space subject target : Pattern}
    (silentFirst : RunSilent atomHead first) (silentSecond : RunSilent atomHead second)
    (side : tokens runLabel subject = 0 ∨ RunSilent atomHead space) :
    (Step (regionEvaluator atomHead first) containedRun (runPattern space subject) target ↔
        Step (regionEvaluator atomHead second) containedRun (runPattern space subject) target) ∧
      (Step (regionEvaluator atomHead first) containedRun (runPattern space subject) target ↔
        ∃ next, target = runPattern space next ∧
          Step (regionEvaluator atomHead space) containedRun subject next) :=
  ⟨contained_run_step_ambient_irrelevant silentFirst silentSecond,
    contained_run_step_iff silentFirst side⟩

/-- **Under the guard that also admits no run, at every ambient space.** -/
theorem atomNotRun_containment {first second space subject target : Pattern} :
    (Step (regionEvaluator atomNotRun first) containedRun (runPattern space subject) target ↔
        Step (regionEvaluator atomNotRun second) containedRun (runPattern space subject) target) ∧
      (Step (regionEvaluator atomNotRun first) containedRun (runPattern space subject) target ↔
        ∃ next, target = runPattern space next ∧
          Step (regionEvaluator atomNotRun space) containedRun subject next) :=
  ⟨contained_run_step_ambient_irrelevant (runSilent_atomNotRun first)
      (runSilent_atomNotRun second),
    contained_run_step_iff_of_refuses atomNotRun_run⟩

/-- **Scoping under the guard**: every step of the contained presentation is
a step of the scoped one, the steps of a run are those by the rules of either
space, and the scoped presentation has a step that the contained one has
not. -/
theorem atomHead_scoping {ambientSpace space subject target : Pattern}
    (silent : RunSilent atomHead ambientSpace) :
    (∀ {source reached : Pattern},
        Step (regionEvaluator atomHead ambientSpace) containedRun source reached →
          Step (regionEvaluator atomHead ambientSpace) scopedRun source reached) ∧
      (Step (regionEvaluator atomHead ambientSpace) scopedRun (runPattern space subject) target ↔
        ∃ next, target = runPattern space next ∧
          (Step (regionEvaluator atomHead ambientSpace) scopedRun subject next ∨
            Step (regionEvaluator atomHead space) ambient subject next)) ∧
      (Step (regionEvaluator atomHead (ruleSpace [chooseLeft, chooseRight])) scopedRun
          (runPattern (ruleSpace []) (atomAt 0 coin))
          (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
        ∀ reached : Pattern,
          ¬ Step (regionEvaluator atomHead (ruleSpace [chooseLeft, chooseRight])) containedRun
            (runPattern (ruleSpace []) (atomAt 0 coin)) reached) :=
  ⟨fun step => step_contained_scoped step, scoped_run_step_iff silent,
    scoped_alone_steps atomHead_admitsAtoms⟩

/-- **Two spaces in one term under the guard**: the function of the mixed
application steps, and its argument does not move. -/
theorem atomHead_twoSpaces :
    TermStep (regionEvaluator atomHead (ruleSpace [chooseLeft, chooseRight])) containedRun
        mixedCoins (mixedPair (.con "heads") coin) ∧
      (∀ target : Contexts.Term containedRun AtomsReduce.closedAtom,
        TermStep (regionEvaluator atomHead (ruleSpace [chooseLeft, chooseRight])) containedRun
            mixedCoins target →
          ∃ next, Dedukti.Step (withChoice Theory.empty) coin next ∧
            target = mixedPair next coin) ∧
        ¬ TermStep (regionEvaluator atomHead (ruleSpace [chooseLeft, chooseRight])) containedRun
          mixedCoins (mixedPair coin (.con "heads")) :=
  ⟨mixedCoins_function_steps atomHead_admitsAtoms,
    fun _ step => mixedCoins_argument_still atomHead_admitsAtoms step,
    mixedCoins_argument_not_by_function_rules atomHead_admitsAtoms⟩

#print axioms ambient_atomsAreRedexes
#print axioms contained_atomsAreRedexes
#print axioms scoped_atomsAreRedexes
#print axioms probeWithRun_not_atomsAreRedexes
#print axioms dataHead_of_sorted
#print axioms guarded_data_static
#print axioms guardedMember
#print axioms guardedMember_any_rewrites_iff
#print axioms ambient_space_static
#print axioms ambient_name_static
#print axioms contained_space_static
#print axioms contained_name_static
#print axioms scoped_space_static
#print axioms scoped_name_static
#print axioms anySubject_space_steps
#print axioms boundSpace_steps
#print axioms declaredSort_excludes_data
#print axioms boundSpace_head_and_sort
#print axioms atomHead_nothing_lost
#print axioms atomHead_containment
#print axioms atomNotRun_containment
#print axioms atomHead_scoping
#print axioms atomHead_twoSpaces
#print axioms atomHead_refusesData
#print axioms atomNotRun_refusesData
#print axioms anySubject_not_refusesData
#print axioms boundSpace_stage_not_atoms
#print axioms ambient_label_category
#print axioms declaredSort_of_atom

end Mettapedia.Logic.HostingStyles.AmbientRegions
