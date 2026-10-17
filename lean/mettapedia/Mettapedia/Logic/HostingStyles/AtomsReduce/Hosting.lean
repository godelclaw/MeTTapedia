import Mettapedia.Logic.HostingStyles.AtomsReduce.Steps
import Mettapedia.Logic.HostingStyles.AtomsReduce.Statics

/-!
# The candidate in which atoms reduce hosts the theories given by a table of first-order rules

The rule-table evaluator has its rules as data: a term of it is a table and a
λΠ term, and it steps by beta or by a rule of the table, at every position.
Its restriction to the tables of rules without binder whose right sides
mention only variables of their left sides is `firstOrderEvaluator`.

* **The candidate hosts the restricted evaluator, on terms**
  (`tableMap_hosting`).  A term is read as the run of its atom in the space of
  its table (`runTermIn`).  The map identifies no two terms, a step of the
  evaluator is a step of the candidate, and a step of the candidate from an
  image is the image of a step.
* Hence **it is a host of the theories given by such a table, on terms**
  (`atomsReduceProbe_hosts_firstOrderTabular`): the pure calculus, the
  calculus with choice, and every theory whose declared rules form such a
  table and which has no definition, each on all its terms, with beta and
  with steps at every position.  The evaluator is the matching evaluator; no
  rule is in the presentation.
* One step of the source is one step of the candidate (`tableMap_steps`).
* The candidate has no rank (`atomsReduce_not_rank`), and closed terms that
  reduce exist (`omegaRun_cycle`).

What the map does not reach is stated with witnesses:

* a rule whose right side binds: the space of `k x ⟶ λ y : Type. x` answers
  nothing, so the image of `k c` has no transition, while the evaluator
  contracts it (`bindingRule_not_preserved`);
* the class `BoundFirstOrder` leaves out the tables with a right-side
  variable that the left side does not bind (`freeTable_not_boundFirstOrder`)
  and the tables with a binder (`bindingTable_not_boundFirstOrder`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable Tabled TableStep tableEvaluator rewritingTheory FirstOrderTable inst
    patternVars usesOnly constantFunctionRule choiceTable withChoice withChoice_empty_tabular
    empty_tabular omega omega_step normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## The run of a term in the space of a list of rules -/

theorem runIn_wellSorted (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty [] (.base "Atom")
      (runPattern (ruleSpace rules) (atomAt 0 term)) :=
  wellSorted_apply_two (lang := atomsReduce) (label := "prime-run") (firstName := "space")
    (secondName := "subject") (by decide) (ruleSpace_wellSorted rules) (atomAt_wellSorted term 0)

/-- **A term, in the space of a list of rules**: the run of its atom, a closed
atom of the candidate. -/
def runTermIn (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    Contexts.Term atomsReduce closedAtom :=
  ⟨runPattern (ruleSpace rules) (atomAt 0 term), runIn_wellSorted rules term⟩

theorem contract_runIn (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    contract (runPattern (ruleSpace rules) (atomAt 0 term)) =
      runPattern (ruleSpace rules) (atomAt 0 term) := by
  rw [contract_runPattern', contract_ruleSpace, contract_atomAt]

/-- The run of a term has no dropping. -/
theorem tokens_drop_runIn (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    tokens dropLabel (runPattern (ruleSpace rules) (atomAt 0 term)) = 0 := by
  have space : tokens dropLabel (ruleSpace rules) = 0 :=
    tokens_ruleSpace (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) rules
  have subject : tokens dropLabel (atomAt 0 term) = 0 :=
    tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) term 0
  simp [runPattern, tokens, tokensList, space, subject, dropLabel]

/-- **The run of a term in the space of a list of rules is the only term of
its class**: what the static equivalence identifies with it is it. -/
theorem eq_runTermIn_of_related {base : BasePremiseEvaluator} {rules : List Dedukti.RewriteRule}
    {term : LF.Term} {other : Contexts.Term atomsReduce closedAtom}
    (related : (termSetoid base atomsReduce closedAtom).r (runTermIn rules term) other) :
    other = runTermIn rules term :=
  eq_of_related_of_dropFree (by decide) (contract_runIn rules term) (tokens_drop_runIn rules term)
    related

/-- The run of a term determines the list of rules and the term. -/
theorem runTermIn_injective {rules others : List Dedukti.RewriteRule} {term other : LF.Term}
    (same : runTermIn rules term = runTermIn others other) : rules = others ∧ term = other := by
  obtain ⟨spaces, atoms⟩ := runPattern_injective (congrArg Subtype.val same)
  exact ⟨ruleSpace_injective spaces, atomAt_injective 0 atoms⟩

/-- **The transitions of the run of a term**, in the space of a list of
rules without binder whose right sides are bound: the runs of its steps in a
theory whose rules are those of the list and which has no definition. -/
theorem termStep_runTermIn_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source : LF.Term}
    {target : Contexts.Term atomsReduce closedAtom} :
    TermStep matchingEvaluator atomsReduce (runTermIn rules source) target ↔
      ∃ next, Dedukti.Step theory source next ∧
        (termSetoid matchingEvaluator atomsReduce closedAtom).r target (runTermIn rules next) := by
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    obtain rfl := eq_runTermIn_of_related before
    obtain ⟨next, shape, step⟩ := (run_step_iff firstOrder bound rulesIff undefined).mp fired
    have same : contractum = runTermIn rules next := Subtype.ext shape
    exact ⟨next, step, (termSetoid matchingEvaluator atomsReduce closedAtom).iseqv.symm
      (same ▸ after)⟩
  · rintro ⟨next, step, related⟩
    exact ⟨runTermIn rules source, runTermIn rules next, Relation.EqvGen.refl _,
      (run_step_iff firstOrder bound rulesIff undefined).mpr ⟨next, rfl, step⟩,
      (termSetoid matchingEvaluator atomsReduce closedAtom).iseqv.symm related⟩

/-! ## The rule-table evaluator, restricted -/

/-- **A table of rules without binder whose right sides mention only
variables of their left sides.** -/
def BoundFirstOrder (table : RuleTable) : Prop := FirstOrderTable table ∧ BoundTable table

/-- **Positive**: the empty table. -/
theorem empty_boundFirstOrder : BoundFirstOrder ∅ :=
  ⟨fun _ member => absurd member (Finset.notMem_empty _),
    fun _ member => absurd member (Finset.notMem_empty _)⟩

/-- **Positive**: the two rules of choice. -/
theorem choiceTable_boundFirstOrder : BoundFirstOrder choiceTable :=
  ⟨choiceTable_firstOrder, choiceTable_bound⟩

/-- **Negative**: the table of `c ⟶ x`, whose right side mentions a variable
that its left side does not bind. -/
theorem freeTable_not_boundFirstOrder : ¬ BoundFirstOrder {freeRule} :=
  fun admitted => freeTable_not_bound admitted.2

/-- **Negative**: the table of `k x ⟶ λ y : Type. x`, whose right side
binds. -/
theorem bindingTable_not_boundFirstOrder : ¬ BoundFirstOrder {constantFunctionRule} := by
  intro admitted
  have free := (admitted.1 constantFunctionRule (Finset.mem_singleton_self _)).2
  revert free
  decide

theorem BoundFirstOrder.listed {table : RuleTable} (admitted : BoundFirstOrder table) :
    (∀ rule ∈ table.toList,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
      ∀ rule ∈ table.toList, usesOnly (patternVars rule.lhs) 0 rule.rhs = true :=
  ⟨fun rule member => admitted.1 rule (Finset.mem_toList.mp member),
    fun rule member => admitted.2 rule (Finset.mem_toList.mp member)⟩

/-- **The rule-table evaluator, on the tables of first-order rules with bound
right sides**: its terms with such a table, its steps between them. -/
def firstOrderEvaluator : GSLT.{0} :=
  (tableEvaluator.gslt ()).region fun tabled => BoundFirstOrder tabled.table

/-- The run of a term of the evaluator: the run of its term in the space of
its table. -/
noncomputable def runOfTabled (tabled : Tabled) : Contexts.Term atomsReduce closedAtom :=
  runTermIn tabled.table.toList tabled.term

theorem runOfTabled_injective : Function.Injective runOfTabled := by
  intro first second same
  obtain ⟨lists, terms⟩ := runTermIn_injective same
  have tables : first.table = second.table := by
    rw [← Finset.toList_toFinset first.table, ← Finset.toList_toFinset second.table, lists]
  cases first
  cases second
  simp only [Tabled.mk.injEq]
  exact ⟨tables, terms⟩

/-- **The restricted evaluator, in the candidate**: a term is read as the run
of its atom in the space of its table. -/
noncomputable def tableMap : ContextMap firstOrderEvaluator.termsAlone atomsReduceTheory :=
  ContextMap.ofTerms (source := firstOrderEvaluator) (target := atomsReduceTheory) closedAtom
    (fun tabled => runOfTabled tabled.1)
    (fun {first second} related => by
      have same : first.1 = second.1 := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- **Under the matching evaluator the candidate in which atoms reduce hosts
the rule-table evaluator on the tables of first-order rules with bound right
sides**: no two terms get one image, a step of the evaluator (beta, or a
rule of the table, at any position) is a step of the image, and a step of the
image is the image of a step. -/
theorem tableMap_hosting : tableMap.Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := firstOrderEvaluator)
    (target := atomsReduceTheory) closedAtom (fun tabled => runOfTabled tabled.1)
    (fun {first second} related => by
      have same : first.1 = second.1 := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same : runOfTabled second.1 = runOfTabled first.1 := eq_runTermIn_of_related related
    exact (runOfTabled_injective same).symm
  · intro first next step
    obtain ⟨sameTable, stepTerm⟩ := step
    obtain ⟨firstOrder, bound⟩ := first.2.listed
    have moved : TermStep matchingEvaluator atomsReduce (runOfTabled first.1)
        (runTermIn first.1.table.toList next.1.term) :=
      (termStep_runTermIn_iff firstOrder bound (theory := Theory.ofTable first.1.table)
        (fun _ => Finset.mem_toList.symm) (fun _ => rfl)).mpr
        ⟨next.1.term, stepTerm, Relation.EqvGen.refl _⟩
    have image : runOfTabled next.1 = runTermIn first.1.table.toList next.1.term := by
      show runTermIn next.1.table.toList next.1.term = _
      rw [sameTable]
    rw [← image] at moved
    exact moved
  · intro first next step
    obtain ⟨firstOrder, bound⟩ := first.2.listed
    obtain ⟨nextTerm, stepTerm, related⟩ :=
      (termStep_runTermIn_iff firstOrder bound (theory := Theory.ofTable first.1.table)
        (fun _ => Finset.mem_toList.symm) (fun _ => rfl)).mp step
    exact ⟨⟨⟨first.1.table, nextTerm⟩, first.2⟩, ⟨rfl, stepTerm⟩, related⟩

/-- **One step of the evaluator is one step of the candidate**: a reduction
of `count` steps is a reduction of `count` steps. -/
theorem tableMap_steps {count : Nat} {first final : firstOrderEvaluator.Term}
    (steps : firstOrderEvaluator.termsAlone.Steps (interface := PUnit.unit) count first final) :
    atomsReduceTheory.Steps count (runOfTabled first.1) (runOfTabled final.1) :=
  tableMap.steps_of_preserves tableMap_hosting.preserves steps

/-! ## The class, by transitivity -/

/-- **The theories given by a table of first-order rules with bound right
sides**, as they run: beta and the rules of the table, at every position, on
all terms. -/
def FirstOrderTabular (source : ContextTheory.{0}) : Prop :=
  ∃ (theory : Theory) (table : RuleTable), theory.Tabular table ∧ BoundFirstOrder table ∧
    source = rewritingTheory theory

/-- **Positive**: the pure calculus. -/
theorem pure_firstOrderTabular : FirstOrderTabular (rewritingTheory Theory.empty) :=
  ⟨Theory.empty, ∅, empty_tabular, empty_boundFirstOrder, rfl⟩

/-- **Positive**: the calculus with a choice between two results. -/
theorem choice_firstOrderTabular : FirstOrderTabular (rewritingTheory (withChoice Theory.empty)) :=
  ⟨withChoice Theory.empty, choiceTable, withChoice_empty_tabular, choiceTable_boundFirstOrder,
    rfl⟩

/-- A table of first-order rules with bound right sides determines its right
sides. -/
theorem BoundFirstOrder.determined {table : RuleTable} (admitted : BoundFirstOrder table) :
    DeterminedTable table :=
  fun rule member => (usesOnly_patternVars_iff_rightDetermined (admitted.1 rule member).1).mp
    (admitted.2 rule member)

/-- Such a theory is given by a table whose rules determine their right
sides. -/
theorem FirstOrderTabular.determined {source : ContextTheory.{0}}
    (member : FirstOrderTabular source) : DeterminedTabularTheory source := by
  obtain ⟨theory, table, tabular, admitted, rfl⟩ := member
  exact ⟨theory, table, tabular, admitted.determined, rfl⟩

/-- **Negative**: the theory of the table of the rule `c ⟶ x`, whose constant
reduces to every variable. -/
theorem freeTable_not_firstOrderTabular :
    ¬ FirstOrderTabular (rewritingTheory (Theory.ofTable {freeRule})) :=
  fun member => freeTable_not_determinedTabular member.determined

/-- Load a table next to every term, into the restricted evaluator. -/
def loadFirstOrder (theory : Theory) {table : RuleTable} (admitted : BoundFirstOrder table)
    (interface : (rewritingTheory theory).Interface) :
    ContextMap ((rewritingTheory theory).gslt interface).termsAlone
      firstOrderEvaluator.termsAlone :=
  ContextMap.ofTerms (source := (rewritingTheory theory).gslt interface)
    (target := firstOrderEvaluator.termsAlone) PUnit.unit
    (fun term => (⟨⟨table, term⟩, admitted⟩ : firstOrderEvaluator.Term))
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact firstOrderEvaluator.equations.iseqv.refl _)

/-- **Loading the table of a theory is hosting.** -/
theorem loadFirstOrder_hosting {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) (admitted : BoundFirstOrder table)
    (interface : (rewritingTheory theory).Interface) :
    (loadFirstOrder theory admitted interface).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt interface)
    (target := firstOrderEvaluator.termsAlone) PUnit.unit
    (fun term => (⟨⟨table, term⟩, admitted⟩ : firstOrderEvaluator.Term))
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact firstOrderEvaluator.equations.iseqv.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same : (⟨table, first⟩ : Tabled) = ⟨table, second⟩ := related
    exact congrArg Tabled.term same
  · intro first next step
    exact ⟨rfl, tabular.step_iff.mp step⟩
  · rintro first ⟨⟨nextTable, nextTerm⟩, nextAdmitted⟩ step
    obtain ⟨sameTable, stepTerm⟩ := step
    have tables : nextTable = table := sameTable
    subst tables
    exact ⟨nextTerm, tabular.step_iff.mpr stepTerm, firstOrderEvaluator.equations.iseqv.refl _⟩

/-- **The candidate in which atoms reduce is a host of the theories given by
a table of first-order rules with bound right sides, on terms.** -/
theorem atomsReduce_hostOf_firstOrderTabular :
    HostOf atomsReduceTheory FirstOrderTabular .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, admitted, rfl⟩, interface, rfl⟩
  exact ⟨tableMap.comp (loadFirstOrder theory admitted interface),
    tableMap_hosting.comp (loadFirstOrder_hosting tabular admitted interface)⟩

/-- **The sentence for the candidate, with its evaluator named.** -/
theorem atomsReduceProbe_hosts_firstOrderTabular :
    atomsReduceProbe.Hosts FirstOrderTabular .terms .hosting :=
  atomsReduce_hostOf_firstOrderTabular

/-! ## No rank, and closed terms that reduce -/

/-- `(λ x. x x) (λ x. x x)`, with the empty table: a term of the restricted
evaluator. -/
def omegaTabled : firstOrderEvaluator.Term := ⟨⟨∅, omega⟩, empty_boundFirstOrder⟩

/-- Its run at the empty space: a closed atom of the candidate. -/
noncomputable def omegaRun : Contexts.Term atomsReduce closedAtom := runOfTabled omegaTabled.1

/-- **A closed term of the candidate that reduces, to itself**: beta alone,
through the congruence of the subject of a run. -/
theorem omegaRun_cycle : atomsReduceTheory.rewrites omegaRun omegaRun :=
  tableMap.preservesRewrites_of_transitions tableMap_hosting.preserves
    (interface := PUnit.unit) (term := omegaTabled) (next := omegaTabled) ⟨rfl, omega_step _⟩

/-- **The candidate has no rank.** -/
theorem atomsReduce_not_rank : IsEmpty atomsReduceTheory.Rank :=
  ⟨fun ranked => ranked.not_cycle (.single omegaRun_cycle)⟩

/-! ## What the map does not reach: a right side that binds -/

/-- `k c ⟶ λ y : Type. c`, a step of the theory of the rule `k x ⟶ λ y : Type. x`. -/
theorem bindingRule_step :
    Dedukti.Step (Theory.ofTable {constantFunctionRule}) (.app (.con "k") (.con "c"))
      (.lam (.srt .type) (.con "c")) := by
  have root : Dedukti.RootStep (Theory.ofTable {constantFunctionRule})
      (inst (fun _ => .con "c") constantFunctionRule.lhs)
      (inst (fun _ => .con "c") constantFunctionRule.rhs) :=
    .rule _ (Finset.mem_singleton_self _)
  exact Dedukti.Step.root root

/-- The cover of the pure calculus: no definition and no rule. -/
def emptyCover : Theory.empty.Cover where
  rigid := fun _ => true
  rules := []
  rigid_sound := fun _ _ => rfl
  rules_sound := fun _ member => member.elim

/-- **The run of `k c` in the space of that rule has no transition**: the
evaluator answers nothing for an equation whose right side binds, and `k c`
has no beta step. -/
theorem bindingRule_run_normal (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites
      (runTermIn [constantFunctionRule] (.app (.con "k") (.con "c"))) target := by
  rintro ⟨redex, contractum, before, ⟨fuel, fired⟩, -⟩
  obtain rfl := eq_runTermIn_of_related before
  obtain ⟨next, -, step⟩ := run_stepAt_sound_of (theory := Theory.empty)
    (space := ruleSpace [constantFunctionRule])
    (fun found => by
      rw [contract_ruleSpace, matchResults_constantFunctionRule] at found
      cases found) fuel fired
  exact normal_of_normalTest emptyCover _ (by decide) _ step

/-- **A rule whose right side binds is not hosted by this reading**: the
evaluator contracts `k c`, and the image of `k c` has no transition. -/
theorem bindingRule_not_preserved :
    tableEvaluator.rewrites (interface := ())
        (⟨{constantFunctionRule}, .app (.con "k") (.con "c")⟩ : Tabled)
        ⟨{constantFunctionRule}, .lam (.srt .type) (.con "c")⟩ ∧
      ∀ target : Contexts.Term atomsReduce closedAtom,
        ¬ atomsReduceTheory.rewrites
          (runTermIn [constantFunctionRule] (.app (.con "k") (.con "c"))) target :=
  ⟨⟨rfl, bindingRule_step⟩, bindingRule_run_normal⟩

#print axioms termStep_runTermIn_iff
#print axioms runOfTabled_injective
#print axioms tableMap_hosting
#print axioms tableMap_steps
#print axioms pure_firstOrderTabular
#print axioms choice_firstOrderTabular
#print axioms freeTable_not_firstOrderTabular
#print axioms loadFirstOrder_hosting
#print axioms atomsReduce_hostOf_firstOrderTabular
#print axioms atomsReduceProbe_hosts_firstOrderTabular
#print axioms omegaRun_cycle
#print axioms atomsReduce_not_rank
#print axioms bindingRule_run_normal
#print axioms bindingRule_not_preserved
#print axioms freeTable_not_boundFirstOrder
#print axioms bindingTable_not_boundFirstOrder

end Mettapedia.Logic.HostingStyles.AtomsReduce
