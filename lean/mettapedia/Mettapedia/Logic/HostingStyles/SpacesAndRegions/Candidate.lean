import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Assembled
import Mettapedia.Logic.HostingStyles.AmbientRegions.AllHeadedHosting
import Mettapedia.Logic.HostingStyles.AmbientRegions.InRuns

/-!
# The candidate of spaces and regions, stated once

`spacesAndRegions` is the presentation `allHeaded` with its root steps
generated (`spacesAndRegions_eq_allHeaded`).  This module states, under that
name, what the candidate is and what it does.  Each statement is the
statement of the same number for `allHeaded`, carried along that equality.

1. **A presentation** that passes the declaration gate
   (`spacesAndRegions_validate`, `spacesAndRegionsPresentation`).
2. **Its statics**: the equivalence of quotation and dropping
   (`spacesAndRegions_quoteDropOnly`, `spacesAndRegions_quoteDropSorted`,
   `spacesAndRegions_namesOnlyDropped`); it carries the atoms of terms and
   declares the run (`spacesAndRegions_carriesAtoms`,
   `spacesAndRegions_declaresRun`).
3. **Its evaluator** is the evaluator of a region; every member respects the
   statics (`spacesAndRegions_respectsStatics`), so the candidate is **a
   family of presented candidates indexed by the ambient space**
   (`spacesAndRegionsMember`).  Without a guard the evaluator is weak: the
   premises it is handed are queries for first-order subjects, and it answers
   them by one function that answers by stored rules
   (`spacesAndRegions_weak`).
4. **No space and no name steps**, at every stage and under every evaluator
   (`spacesAndRegions_space_static`, `spacesAndRegions_name_static`); and a
   bound variable has no step (`spacesAndRegions_boundVariable_normal`).
5. **Containment of a run**: at every ambient space the steps of a run are
   the runs of the steps of its subject in the member at the space of the run
   (`spacesAndRegions_run_step_iff`, on terms
   `spacesAndRegions_run_termStep_iff`), so the ambient space is irrelevant to
   a run (`spacesAndRegions_run_step_ambient_irrelevant`); a run in a run
   steps by its own space alone (`spacesAndRegions_nested_step_iff`).
6. **Two spaces in one term** (`spacesAndRegions_pair_step_iff`).
7. **The class it hosts**: at the space of a table of first-order rules with
   bound right sides none of whose left sides is a variable, the theories of
   that table, on terms and with all contexts
   (`spacesAndRegions_hostOf_tabularAt`,
   `spacesAndRegions_hostOf_scopedTabularAt`); and on terms, read in runs, at
   every ambient space (`spacesAndRegions_hostOf_tabular_inRuns`).  The steps
   behind it: `spacesAndRegions_atom_step_iff`,
   `spacesAndRegions_runAtom_step_iff`.
8. **What it does not do**: a rule whose left side is a variable does not
   fire on a bound variable in a run
   (`spacesAndRegions_runVariable_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory patternVars usesOnly)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## A presentation -/

/-- **The candidate passes the declaration gate.** -/
theorem spacesAndRegions_validate : spacesAndRegions.validate = [] := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_validate

/-- The candidate, as a presentation. -/
def spacesAndRegionsPresentation : ValidatedLanguageDef :=
  ⟨spacesAndRegions, spacesAndRegions_validate⟩

/-- It is the presentation of `allHeaded`. -/
theorem spacesAndRegionsPresentation_eq : spacesAndRegionsPresentation = allHeadedPresentation := by
  unfold spacesAndRegionsPresentation allHeadedPresentation
  congr 1

/-! ## Its statics -/

/-- **The static equivalence is that of quotation and dropping.** -/
theorem spacesAndRegions_quoteDropOnly : QuoteDropOnly spacesAndRegions := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_quoteDropOnly

/-- Quotation takes an atom to a name and dropping takes a name. -/
theorem spacesAndRegions_quoteDropSorted : QuoteDropSorted spacesAndRegions := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_quoteDropSorted

/-- A name is taken by dropping alone. -/
theorem spacesAndRegions_namesOnlyDropped : NamesOnlyDropped spacesAndRegions unquotedSorts := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_namesOnlyDropped

/-- It carries the atoms of λΠ terms and the spaces of rules. -/
theorem spacesAndRegions_carriesAtoms : CarriesAtoms spacesAndRegions := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_carriesAtoms

/-- It declares the run of an atom in a space, as an atom. -/
theorem spacesAndRegions_declaresRun : DeclaresRun spacesAndRegions := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_declaresRun

/-! ## Its evaluator, and the family of presented candidates -/

variable {admits : Pattern → Bool}

/-- **Every member respects the static equivalence**, under every guard. -/
theorem spacesAndRegions_respectsStatics (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) spacesAndRegions := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_respectsStatics admits ambientSpace

/-- A space of the candidate: a closed term of its sort `Space`. -/
abbrev SpacesAndRegionsSpace : Type := Contexts.Term spacesAndRegions closedSpace

/-- **The member of the family at an ambient space**, under a guard, as a
presented candidate: the candidate under the evaluator of a region. -/
def spacesAndRegionsMember (admits : Pattern → Bool) (space : SpacesAndRegionsSpace) :
    PresentedCandidate where
  presentation := spacesAndRegionsPresentation
  evaluator := regionEvaluator admits space.1
  respects := spacesAndRegions_respectsStatics admits space.1

/-- The theory of the candidate at an ambient space, with all its contexts. -/
abbrev spacesAndRegionsTheory (admits : Pattern → Bool) (space : Pattern) : ContextTheory.{0} :=
  contextTheory (regionEvaluator admits space) spacesAndRegionsPresentation

theorem spacesAndRegionsMember_theory (admits : Pattern → Bool) (space : SpacesAndRegionsSpace) :
    (spacesAndRegionsMember admits space).theory = spacesAndRegionsTheory admits space.1 :=
  rfl

/-- All members have one presentation; they differ by their evaluator. -/
theorem spacesAndRegionsMember_presentation (admits : Pattern → Bool)
    (first second : SpacesAndRegionsSpace) :
    (spacesAndRegionsMember admits first).presentation =
      (spacesAndRegionsMember admits second).presentation :=
  rfl

/-- The theory at an ambient space is that of `allHeaded` there. -/
theorem spacesAndRegionsTheory_eq (admits : Pattern → Bool) (space : Pattern) :
    spacesAndRegionsTheory admits space = allHeadedTheory admits space := by
  unfold spacesAndRegionsTheory allHeadedTheory
  rw [spacesAndRegionsPresentation_eq]

/-- **The evaluator is weak.**  Every premise that the candidate hands to its
evaluator is a query of the ambient root step or of the root step of a run
for a first-order subject, or a congruence; without a guard the evaluator
answers the queries of both kinds by one function, the first at the ambient
space and the second at the space of the run; and that function answers by
stored rules. -/
theorem spacesAndRegions_weak :
    (∀ premise ∈ presentedPremises spacesAndRegions,
      (∃ subject, isMatchCorrectAux subject = true ∧
        premise = .relationQuery "AmbientStep" [subject, .fvar "answer"]) ∨
      (∃ subject, isMatchCorrectAux subject = true ∧
        premise = .relationQuery "PrimeStep" [.fvar "space", subject, .fvar "answer"]) ∨
      ∃ source target, premise = .congruence source target) ∧
    (∀ (ambientSpace : Pattern) (lang : LanguageDef) (bindings : Bindings) (subject : Pattern),
        regionEvaluator anySubject ambientSpace lang bindings
            (.relationQuery "AmbientStep" [subject, .fvar "answer"]) =
          (admittedAnswers anySubject ambientSpace (applyBindings bindings subject)).map
            fun result => ("answer", result) :: bindings) ∧
    (∀ (ambientSpace : Pattern) (lang : LanguageDef) (bindings : Bindings) (subject : Pattern),
        regionEvaluator anySubject ambientSpace lang bindings
            (.relationQuery "PrimeStep" [.fvar "space", subject, .fvar "answer"]) =
          (admittedAnswers anySubject (applyBindings bindings (.fvar "space"))
            (applyBindings bindings subject)).map fun result => ("answer", result) :: bindings) ∧
    AuthoredEvaluators.AnswersByStoredRules (admittedAnswers anySubject) := by
  refine ⟨?_, regionEvaluator_ambientQuery anySubject, regionEvaluator_runQuery anySubject,
    admittedAnswers_any_answersByStoredRules⟩
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_premises

/-! ## No space and no name steps -/

/-- **No space has a transition**, at every stage and under every
evaluator. -/
theorem spacesAndRegions_space_static {base : BasePremiseEvaluator} {stage : List TypeExpr} :
    ∀ term next : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩,
      ¬ TermStep base spacesAndRegions term next := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_space_static

/-- **No name has a transition**, at every stage and under every
evaluator. -/
theorem spacesAndRegions_name_static {base : BasePremiseEvaluator} {stage : List TypeExpr} :
    ∀ term next : Contexts.Term spacesAndRegions ⟨.base "CandidateName", stage⟩,
      ¬ TermStep base spacesAndRegions term next := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_name_static

/-- **A bound variable has no step**, under every evaluator. -/
theorem spacesAndRegions_boundVariable_normal {base : BasePremiseEvaluator} (index : Nat)
    (target : Pattern) : ¬ Step base spacesAndRegions (.bvar index) target := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_boundVariable_normal index target

/-! ## Containment of a run -/

/-- **The steps of a run are the runs of the steps of its subject in the
member at the space of the run**: under every guard, at every ambient space,
for every space and every subject. -/
theorem spacesAndRegions_run_step_iff {ambientSpace space subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) spacesAndRegions (runPattern space subject)
        target ↔
      ∃ next, target = runPattern space next ∧
        Step (regionEvaluator admits space) spacesAndRegions subject next := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_run_step_iff

/-- **For every two ambient spaces a run has the same steps.** -/
theorem spacesAndRegions_run_step_ambient_irrelevant (first second : Pattern)
    {space subject target : Pattern} :
    Step (regionEvaluator admits first) spacesAndRegions (runPattern space subject) target ↔
      Step (regionEvaluator admits second) spacesAndRegions (runPattern space subject) target :=
  spacesAndRegions_run_step_iff.trans spacesAndRegions_run_step_iff.symm

/-- **A run in a run**: its steps are the runs of the runs of the steps of
the inner subject in the member at the inner space. -/
theorem spacesAndRegions_nested_step_iff {ambientSpace outer inner subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) spacesAndRegions
        (runPattern outer (runPattern inner subject)) target ↔
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        Step (regionEvaluator admits inner) spacesAndRegions subject next := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_nested_step_iff

/-- **The run of a bound variable has no step**, under every guard and at
every ambient space: a rule whose left side is a variable does not fire on
it. -/
theorem spacesAndRegions_runVariable_normal (ambientSpace space : Pattern) (index : Nat)
    (target : Pattern) :
    ¬ Step (regionEvaluator admits ambientSpace) spacesAndRegions
      (runPattern space (.bvar index)) target := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_runVariable_normal ambientSpace space index target

/-- **On terms: the transitions of `run(space, atom)` are the runs of the
transitions of `atom` in the member at `space`**, under every guard and at
every ambient space. -/
theorem spacesAndRegions_run_termStep_iff {ambientSpace : Pattern} {stage : List TypeExpr} :
    ∀ (space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
      (atom target : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩),
      TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
          (runTermIn spacesAndRegions_declaresRun space atom) target ↔
        ∃ next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩,
          TermStep (regionEvaluator admits space.1) spacesAndRegions atom next ∧
            (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
              ⟨.base "Atom", stage⟩).r target
                (runTermIn spacesAndRegions_declaresRun space next) := by
  have general : ∀ (lang : LanguageDef) (same : lang = allHeaded) (declares : DeclaresRun lang)
      (space : Contexts.Term lang ⟨.base "Space", stage⟩)
      (atom target : Contexts.Term lang ⟨.base "Atom", stage⟩),
      TermStep (regionEvaluator admits ambientSpace) lang (runTermIn declares space atom) target ↔
        ∃ next : Contexts.Term lang ⟨.base "Atom", stage⟩,
          TermStep (regionEvaluator admits space.1) lang atom next ∧
            (termSetoid (regionEvaluator admits ambientSpace) lang ⟨.base "Atom", stage⟩).r
              target (runTermIn declares space next) := by
    rintro _ rfl declares space atom target
    exact allHeaded_run_termStep_iff space atom target
  exact general spacesAndRegions spacesAndRegions_eq_allHeaded spacesAndRegions_declaresRun

/-! ## Two spaces in one term -/

/-- **The steps of an application of two runs**, at every ambient space: a
step of the function in the member at its space, a step of the argument in
the member at its space, or an answer of the ambient space for the
application. -/
theorem spacesAndRegions_pair_step_iff
    {ambientSpace first second function argument target : Pattern} :
    Step (regionEvaluator admits ambientSpace) spacesAndRegions
        (.apply "App" [runPattern first function, runPattern second argument]) target ↔
      (∃ next, target = .apply "App" [runPattern first next, runPattern second argument] ∧
        Step (regionEvaluator admits first) spacesAndRegions function next) ∨
      (∃ next, target = .apply "App" [runPattern first function, runPattern second next] ∧
        Step (regionEvaluator admits second) spacesAndRegions argument next) ∨
      target ∈ admittedAnswers admits ambientSpace
        (.apply "App" [runPattern first function, runPattern second argument]) := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_pair_step_iff

/-! ## The class it hosts -/

/-- **Outside a run the candidate computes, on the atom of a term, by beta and
by the rules that the ambient space stores**, for a list of rules none of
whose left sides is a variable. -/
theorem spacesAndRegions_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) spacesAndRegions (atomAt depth source)
        target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_atom_step_iff admitsAtoms firstOrder bound headed rulesIff undefined

/-- **The run of the atom of a term computes by the rules of its space, at
every ambient space**, for a list of rules none of whose left sides is a
variable. -/
theorem spacesAndRegions_runAtom_step_iff (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits ambientSpace) spacesAndRegions
        (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
      ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
        Dedukti.Step theory source next := by
  rw [spacesAndRegions_eq_allHeaded]
  exact allHeaded_runAtom_step_iff admitsAtoms ambientSpace firstOrder bound headed rulesIff
    undefined

variable {declared : Contexts.Interface → Prop}

/-- **On terms: at the space of a table of first-order rules with bound right
sides none of whose left sides is a variable, the candidate is a host of the
theories given by that table.** -/
theorem spacesAndRegions_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (spacesAndRegionsTheory admits (tableSpace table).1)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rw [spacesAndRegionsTheory_eq]
  exact allHeaded_hostOf_tabularAt admitsAtoms admitted headed

/-- **With contexts: a reading of the candidate, at the space of such a table,
in which the holes of atoms are free is a host, with all contexts, of the
theories given by the table** on the terms with free variables below a width,
for every width. -/
theorem spacesAndRegions_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits)
    {table : RuleTable} (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) (free : AtomsFree declared) :
    HostOf ((spacesAndRegionsTheory admits (tableSpace table).1).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  have general : ∀ presentation : ValidatedLanguageDef, presentation = allHeadedPresentation →
      HostOf ((contextTheory (regionEvaluator admits (tableSpace table).1)
          presentation).regionReading declared)
        (fun source => ∃ (theory : Theory) (width : Nat),
          theory.Tabular table ∧ source = scopedRewriting width theory)
        .contexts .hosting := by
    rintro _ rfl
    exact allHeaded_hostOf_scopedTabularAt admitsAtoms admitted headed free
  exact general _ spacesAndRegionsPresentation_eq

/-- **In runs, at every ambient space**: each member is a host, on terms, of
the theories of such a table, each term read as the run of its atom in the
space of the table. -/
theorem spacesAndRegions_hostOf_tabular_inRuns (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) {table : RuleTable} (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (spacesAndRegionsTheory admits ambientSpace)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rw [spacesAndRegionsTheory_eq]
  exact allHeaded_hostOf_tabular_inRuns admitsAtoms ambientSpace admitted headed

#print axioms spacesAndRegions_validate
#print axioms spacesAndRegionsPresentation_eq
#print axioms spacesAndRegions_quoteDropOnly
#print axioms spacesAndRegions_quoteDropSorted
#print axioms spacesAndRegions_namesOnlyDropped
#print axioms spacesAndRegions_carriesAtoms
#print axioms spacesAndRegions_declaresRun
#print axioms spacesAndRegions_respectsStatics
#print axioms spacesAndRegionsMember
#print axioms spacesAndRegionsMember_theory
#print axioms spacesAndRegionsMember_presentation
#print axioms spacesAndRegionsTheory_eq
#print axioms spacesAndRegions_weak
#print axioms spacesAndRegions_space_static
#print axioms spacesAndRegions_name_static
#print axioms spacesAndRegions_boundVariable_normal
#print axioms spacesAndRegions_run_step_iff
#print axioms spacesAndRegions_run_step_ambient_irrelevant
#print axioms spacesAndRegions_nested_step_iff
#print axioms spacesAndRegions_runVariable_normal
#print axioms spacesAndRegions_run_termStep_iff
#print axioms spacesAndRegions_pair_step_iff
#print axioms spacesAndRegions_atom_step_iff
#print axioms spacesAndRegions_runAtom_step_iff
#print axioms spacesAndRegions_hostOf_tabularAt
#print axioms spacesAndRegions_hostOf_scopedTabularAt
#print axioms spacesAndRegions_hostOf_tabular_inRuns

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
