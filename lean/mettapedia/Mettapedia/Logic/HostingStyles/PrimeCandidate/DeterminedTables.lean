import Mettapedia.Logic.HostingStyles.PrimeCandidate.SpellingEvaluator

/-!
# Tables whose rules determine their right sides

The evaluator of a finite listing (`stepEvaluator`) reads its subject up to
the static equivalence, and hosts on terms the theories whose terms have
finitely many reducts.  This module says which theories given by a table
those are, and hosts them all under one such evaluator.

* A rule **determines its right side** (`RightDetermined`) when two of its
  instances with one left side have one right side.  A rule whose right side
  is closed does (`rightDetermined_of_closed`), the two rules of choice do
  (`chooseLeft_rightDetermined`, `chooseRight_rightDetermined`), and the rule
  `c ⟶ x` does not (`freeRule_not_rightDetermined`).
* A theory whose terms have finitely many contractions at the root has
  finitely many reducts (`step_finite_of_rootStep_finite`), and the theory of
  a table of rules that determine their right sides is one
  (`rootStep_finite_of_rightDetermined`).  So it is listed (`tableListing`).
* **Under one evaluator that reads its subject up to the static equivalence,
  the probe with the run constructor hosts on terms every theory given by a
  table whose rules determine their right sides**
  (`runPresentation_hostOf_determinedTabular_terms`).  The theory with choice
  is one of them (`choice_determinedTabular`).

The theory of the table of the one rule `c ⟶ x` is not one of them
(`freeTable_not_determinedTabular`): there the constant has infinitely many
reducts, and the extended presentation hosts it through an evaluator that
reads the spelling of its subject (`runPresentation_hostOf_tabular_terms`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable RootStep rewritingTheory inst chooseLeft chooseRight choiceTable withChoice
    withChoice_empty_tabular)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)

/-! ## Rules that determine their right sides -/

/-- **The right side of a rule is determined by its left side**: two
instances of the rule with one left side have one right side. -/
def RightDetermined (rule : Dedukti.RewriteRule) : Prop :=
  ∀ first second : Nat → LF.Term, inst first rule.lhs = inst second rule.lhs →
    inst first rule.rhs = inst second rule.rhs

/-- **Positive**: a rule whose right side is closed. -/
theorem rightDetermined_of_closed {rule : Dedukti.RewriteRule} (closed : Dedukti.Closed rule.rhs) :
    RightDetermined rule := fun first second _ => by
  rw [Dedukti.Closed.inst closed first, Dedukti.Closed.inst closed second]

/-- **Positive**: `choose x y ⟶ x`, whose right side is a variable of its
left side. -/
theorem chooseLeft_rightDetermined : RightDetermined chooseLeft := by
  intro first second same
  simp only [chooseLeft, Dedukti.choose, Dedukti.inst_app, Dedukti.inst_con, Dedukti.inst_var,
    LF.Term.app.injEq, true_and] at same ⊢
  exact same.1

/-- **Positive**: `choose x y ⟶ y`. -/
theorem chooseRight_rightDetermined : RightDetermined chooseRight := by
  intro first second same
  simp only [chooseRight, Dedukti.choose, Dedukti.inst_app, Dedukti.inst_con, Dedukti.inst_var,
    LF.Term.app.injEq, true_and] at same ⊢
  exact same.2

/-- **Negative**: `c ⟶ x`, whose right side is a variable that its left side
does not bind. -/
theorem freeRule_not_rightDetermined : ¬ RightDetermined freeRule := by
  intro determined
  have same := determined (fun _ => .var 0) (fun _ => .var 1) rfl
  simp [freeRule] at same

/-- A table all of whose rules determine their right sides. -/
def DeterminedTable (table : RuleTable) : Prop := ∀ rule ∈ table, RightDetermined rule

theorem choiceTable_determined : DeterminedTable choiceTable := by
  intro rule member
  simp only [choiceTable, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact chooseLeft_rightDetermined
  · exact chooseRight_rightDetermined

/-! ## Finitely many reducts -/

/-- **A theory whose terms have finitely many contractions at the root has
finitely many reducts of each term.** -/
theorem step_finite_of_rootStep_finite {theory : Theory}
    (rootFinite : ∀ term : LF.Term, {next | RootStep theory term next}.Finite) :
    ∀ term : LF.Term, {next | Dedukti.Step theory term next}.Finite := by
  intro term
  induction term with
  | srt sort => exact (rootFinite _).subset fun next step => Dedukti.Step.srt_inv step
  | con name => exact (rootFinite _).subset fun next step => Dedukti.Step.con_inv step
  | var index => exact (rootFinite _).subset fun next step => Dedukti.Step.var_inv step
  | pi domain body ihDomain ihBody =>
      refine ((rootFinite (.pi domain body)).union
        ((ihDomain.image fun domain' => LF.Term.pi domain' body).union
          (ihBody.image fun body' => LF.Term.pi domain body'))).subset ?_
      intro next step
      rcases Dedukti.Step.pi_inv step with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact Or.inl root
      · exact Or.inr (Or.inl ⟨domain', inner, rfl⟩)
      · exact Or.inr (Or.inr ⟨body', inner, rfl⟩)
  | lam domain body ihDomain ihBody =>
      refine ((rootFinite (.lam domain body)).union
        ((ihDomain.image fun domain' => LF.Term.lam domain' body).union
          (ihBody.image fun body' => LF.Term.lam domain body'))).subset ?_
      intro next step
      rcases Dedukti.Step.lam_inv step with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact Or.inl root
      · exact Or.inr (Or.inl ⟨domain', inner, rfl⟩)
      · exact Or.inr (Or.inr ⟨body', inner, rfl⟩)
  | app function argument ihFunction ihArgument =>
      refine ((rootFinite (.app function argument)).union
        ((ihFunction.image fun function' => LF.Term.app function' argument).union
          (ihArgument.image fun argument' => LF.Term.app function argument'))).subset ?_
      intro next step
      rcases Dedukti.Step.app_inv step with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · exact Or.inl root
      · exact Or.inr (Or.inl ⟨function', inner, rfl⟩)
      · exact Or.inr (Or.inr ⟨argument', inner, rfl⟩)

/-- **Under a table of rules that determine their right sides a term has
finitely many contractions at the root**: one by beta at most, and one for
each rule at most. -/
theorem rootStep_finite_of_rightDetermined {table : RuleTable} (determined : DeterminedTable table)
    (term : LF.Term) : {next | RootStep (Theory.ofTable table) term next}.Finite := by
  have beta : {next : LF.Term | ∃ domain body argument : LF.Term,
      term = .app (.lam domain body) argument ∧
        next = LFTyping.subst0 argument body}.Subsingleton := by
    rintro _ ⟨domain, body, argument, shape, rfl⟩ _ ⟨domain', body', argument', shape', rfl⟩
    rw [shape] at shape'
    simp only [LF.Term.app.injEq, LF.Term.lam.injEq] at shape'
    obtain ⟨⟨_, rfl⟩, rfl⟩ := shape'
    rfl
  have rules : ∀ rule ∈ (table : Set Dedukti.RewriteRule),
      {next : LF.Term | ∃ assignment : Nat → LF.Term,
        inst assignment rule.lhs = term ∧ next = inst assignment rule.rhs}.Finite := by
    intro rule member
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨first, left, rfl⟩ _ ⟨second, left', rfl⟩
    exact determined rule (Finset.mem_coe.mp member) first second (left.trans left'.symm)
  refine (beta.finite.union (Set.Finite.biUnion table.finite_toSet rules)).subset ?_
  intro next step
  cases step with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => cases defined
  | rule assignment member =>
      exact Or.inr (Set.mem_biUnion (Finset.mem_coe.mpr member) ⟨assignment, rfl, rfl⟩)

/-! ## Listings from finiteness -/

/-- **A theory with countably many terms, compared by identity, each with
finitely many reducts, has a listing.** -/
noncomputable def StepListing.ofFinite (source : GSLT.{0}) (countable : Countable source.Term)
    (finite : ∀ term : source.Term, {next | source.rewrites term next}.Finite)
    (discrete : ∀ first second : source.Term, source.equations.r first second → first = second) :
    StepListing source where
  code := Classical.choose (exists_injective_nat source.Term)
  injective := Classical.choose_spec (exists_injective_nat source.Term)
  next := fun term => (finite term).toFinset.toList
  branches := fun term reduct => by
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
    rfl
  discrete := discrete

/-- **The theory of a table of rules that determine their right sides is
listed.** -/
noncomputable def tableListing (table : RuleTable) (determined : DeterminedTable table) :
    StepListing ((rewritingTheory (Theory.ofTable table)).gslt ()) :=
  StepListing.ofFinite _ (inferInstanceAs (Countable LF.Term))
    (step_finite_of_rootStep_finite (rootStep_finite_of_rightDetermined determined))
    fun _ _ same => same

/-! ## One evaluator for all of them -/

/-- A number for each table. -/
noncomputable def tableCode : RuleTable → Nat :=
  Classical.choose (exists_injective_nat RuleTable)

theorem tableCode_injective : Function.Injective tableCode :=
  Classical.choose_spec (exists_injective_nat RuleTable)

/-- The table of a number: the table of rules that determine their right
sides with that number, and the empty table if there is none. -/
noncomputable def tableAt (index : Nat) : RuleTable :=
  open Classical in
  if known : ∃ table, tableCode table = index ∧ DeterminedTable table then Classical.choose known
  else ∅

theorem tableAt_determined (index : Nat) : DeterminedTable (tableAt index) := by
  unfold tableAt
  split_ifs with known
  · exact (Classical.choose_spec known).2
  · intro rule member
    exact absurd member (Finset.notMem_empty rule)

theorem tableAt_tableCode {table : RuleTable} (determined : DeterminedTable table) :
    tableAt (tableCode table) = table := by
  have known : ∃ other, tableCode other = tableCode table ∧ DeterminedTable other :=
    ⟨table, rfl, determined⟩
  unfold tableAt
  rw [dif_pos known]
  exact tableCode_injective (Classical.choose_spec known).1

/-- The numbered family of the theories of those tables. -/
noncomputable def determinedFamily (index : Nat) : GSLT.{0} :=
  (rewritingTheory (Theory.ofTable (tableAt index))).gslt ()

/-- Each member of the family is listed. -/
noncomputable def determinedListing (index : Nat) : StepListing (determinedFamily index) :=
  tableListing (tableAt index) (tableAt_determined index)

/-- **The evaluator of the premises that runs every table of rules that
determine their right sides.**  It reads its subject up to the static
equivalence. -/
noncomputable def determinedEvaluator : BasePremiseEvaluator :=
  stepEvaluator (unionListing determinedListing).code (unionListing determinedListing).next

/-- **The theories given by a table whose rules determine their right
sides.** -/
def DeterminedTabularTheory (source : ContextTheory.{0}) : Prop :=
  ∃ (theory : Theory) (table : RuleTable),
    theory.Tabular table ∧ DeterminedTable table ∧ source = rewritingTheory theory

/-- They are theories given by a table. -/
theorem DeterminedTabularTheory.tabular {source : ContextTheory.{0}}
    (determined : DeterminedTabularTheory source) : TabularTheory source := by
  obtain ⟨theory, table, tabular, _, rfl⟩ := determined
  exact ⟨theory, table, tabular, rfl⟩

/-- The steps of a theory given by such a table are the steps of the member
of the family with the number of the table. -/
theorem determinedFamily_step {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) (determined : DeterminedTable table) {first next : LF.Term} :
    (determinedFamily (tableCode table)).rewrites first next ↔ Dedukti.Step theory first next := by
  show Dedukti.Step (Theory.ofTable (tableAt (tableCode table))) first next ↔ _
  rw [tableAt_tableCode determined]
  exact tabular.step_iff.symm

/-- **The probe with the run constructor is a host of the theories given by a
table whose rules determine their right sides, on terms**, under one
evaluator of its premises that reads its subject up to the static
equivalence. -/
theorem runPresentation_hostOf_determinedTabular_terms :
    HostOf (contextTheory determinedEvaluator runPresentation) DeterminedTabularTheory .terms
      .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, determined, rfl⟩, interface, rfl⟩
  obtain ⟨map, hosting⟩ := runPresentation_hosts_family determinedListing (tableCode table)
  let member : ContextMap ((rewritingTheory theory).gslt interface).termsAlone
      (determinedFamily (tableCode table)).termsAlone :=
    ContextMap.ofTerms (source := (rewritingTheory theory).gslt interface)
      (target := (determinedFamily (tableCode table)).termsAlone) PUnit.unit
      (fun term => (term : LF.Term)) (fun related => related)
  have memberHosting : member.Hosting :=
    (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt interface)
      (target := (determinedFamily (tableCode table)).termsAlone) PUnit.unit
      (fun term => (term : LF.Term)) (fun related => related)).mpr
      ⟨fun _ _ same => same,
        fun _ _ step => (determinedFamily_step tabular determined).mpr step,
        fun _ next step => ⟨next, (determinedFamily_step tabular determined).mp step, rfl⟩⟩
  exact ⟨map.comp member, hosting.comp memberHosting⟩

/-! ## Examples -/

/-- **Positive**: the pure calculus, whose table is empty. -/
theorem pure_determinedTabular : DeterminedTabularTheory (rewritingTheory Theory.empty) :=
  ⟨Theory.empty, ∅, Dedukti.empty_tabular, fun _ member => absurd member (Finset.notMem_empty _),
    rfl⟩

/-- **Positive**: the pure calculus with the two rules of choice. -/
theorem choice_determinedTabular :
    DeterminedTabularTheory (rewritingTheory (withChoice Theory.empty)) :=
  ⟨_, choiceTable, withChoice_empty_tabular, choiceTable_determined, rfl⟩

/-- Every term of such a theory has finitely many reducts. -/
theorem DeterminedTabularTheory.finite_reducts {source : ContextTheory.{0}}
    (determined : DeterminedTabularTheory source) (interface : source.Interface)
    (term : source.Term interface) : {next | source.rewrites term next}.Finite := by
  obtain ⟨theory, table, tabular, determinedTable, rfl⟩ := determined
  refine (step_finite_of_rootStep_finite (rootStep_finite_of_rightDetermined determinedTable)
    term).subset ?_
  intro next step
  exact tabular.step_iff.mp step

/-- **Negative**: the theory of the table of the rule `c ⟶ x` is not one of
them: its constant reduces to every variable. -/
theorem freeTable_not_determinedTabular :
    ¬ DeterminedTabularTheory (rewritingTheory (Theory.ofTable {freeRule})) := by
  intro determined
  have finite := determined.finite_reducts () (LF.Term.con "c")
  have every : ∀ index : Nat, (LF.Term.var index) ∈
      {next | (rewritingTheory (Theory.ofTable {freeRule})).rewrites (interface := ())
        (LF.Term.con "c") next} := fun index =>
    (evaluator_reduces_to_every (.var index)).2
  exact Set.infinite_range_of_injective (fun first second same => LF.Term.var.inj same)
    (finite.subset (by
      rintro _ ⟨index, rfl⟩
      exact every index))

#print axioms chooseLeft_rightDetermined
#print axioms freeRule_not_rightDetermined
#print axioms step_finite_of_rootStep_finite
#print axioms rootStep_finite_of_rightDetermined
#print axioms tableListing
#print axioms runPresentation_hostOf_determinedTabular_terms
#print axioms pure_determinedTabular
#print axioms choice_determinedTabular
#print axioms freeTable_not_determinedTabular

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
