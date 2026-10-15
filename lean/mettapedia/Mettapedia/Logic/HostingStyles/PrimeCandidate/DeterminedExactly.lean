import Mettapedia.Logic.HostingStyles.PrimeCandidate.AdmissibleEvaluators

/-!
# Exactly the tables whose rules determine their right sides

`AdmissibleEvaluators` shows that, under an evaluator that respects the
static equivalence, the probe with the run constructor hosts on terms exactly
the theories whose terms have finitely many reducts.  This module says which
theories given by a table those are, by the syntax of the table.

* A rule determines its right side **exactly when every free variable of its
  right side occurs in its left side** (`rightDetermined_iff_mentions`).  The
  instances of a term determine the assignment at the variables that occur in
  it (`eq_of_instantiate_eq`), and only there (`instantiate_congr_of_mentions`).
  For a rule without binder on its left side this is the check
  `usesOnly (patternVars lhs) 0 rhs` (`usesOnly_patternVars_iff_rightDetermined`).
* A theory with a rule that does not determine its right side has a term with
  infinitely many reducts (`infinite_reducts_of_not_rightDetermined`): the
  variable that the left side does not bind takes every value.
* So for a theory given by a table, **each term has finitely many reducts
  exactly when the rules of the table determine their right sides**
  (`finite_reducts_iff_determinedTable`), and that is exactly when some
  evaluator that respects the static equivalence makes the probe with the run
  constructor host it on terms (`hostedBy_respecting_iff_determinedTable`).
* **One evaluator serves the whole class**
  (`exists_respecting_hostOf_iff_determinedTabular`): a class of theories
  given by tables is hosted on terms under one evaluator that respects the
  static equivalence exactly when it lies among the theories of the tables
  whose rules determine their right sides.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable RootStep rewritingTheory inst instantiate usesOnly patternVars binderFree)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)

/-! ## The free variables of a term -/

/-- **A free variable occurs in a term** that stands beneath a number of
binders. -/
def Mentions (index : Nat) : Nat → LF.Term → Prop
  | depth, .var found => found = depth + index
  | _, .srt _ => False
  | _, .con _ => False
  | depth, .pi domain body => Mentions index depth domain ∨ Mentions index (depth + 1) body
  | depth, .lam domain body => Mentions index depth domain ∨ Mentions index (depth + 1) body
  | depth, .app function argument =>
      Mentions index depth function ∨ Mentions index depth argument

/-- **Positive**: the variable of the body of `λx. y`, which the binder does
not bind. -/
theorem mentions_free_under_binder : Mentions 0 0 (.lam (.srt .type) (.var 1)) :=
  Or.inr rfl

/-- **Negative**: the variable that the binder binds. -/
theorem not_mentions_bound : ∀ index, ¬ Mentions index 0 (.lam (.srt .type) (.var 0)) := by
  rintro index (inDomain | inBody)
  · exact inDomain
  · have shape : (0 : Nat) = 0 + 1 + index := inBody
    omega

/-- Lifting is injective. -/
theorem lift_injective (amount : Nat) :
    ∀ {first second : LF.Term} {cutoff : Nat},
      lift amount cutoff first = lift amount cutoff second → first = second := by
  intro first
  induction first with
  | var index =>
      intro second cutoff same
      cases second with
      | var other =>
          simp only [lift, LF.Term.var.injEq] at same
          congr 1
          split_ifs at same <;> omega
      | _ => simp [lift] at same
  | srt sort =>
      intro second cutoff same
      cases second <;> simp_all [lift]
  | con name =>
      intro second cutoff same
      cases second <;> simp_all [lift]
  | pi domain body ihDomain ihBody =>
      intro second cutoff same
      cases second with
      | pi otherDomain otherBody =>
          simp only [lift, LF.Term.pi.injEq] at same
          rw [ihDomain same.1, ihBody same.2]
      | _ => simp [lift] at same
  | lam domain body ihDomain ihBody =>
      intro second cutoff same
      cases second with
      | lam otherDomain otherBody =>
          simp only [lift, LF.Term.lam.injEq] at same
          rw [ihDomain same.1, ihBody same.2]
      | _ => simp [lift] at same
  | app function argument ihFunction ihArgument =>
      intro second cutoff same
      cases second with
      | app otherFunction otherArgument =>
          simp only [lift, LF.Term.app.injEq] at same
          rw [ihFunction same.1, ihArgument same.2]
      | _ => simp [lift] at same

/-- **The instances of a term determine the assignment at the variables that
occur in it.** -/
theorem eq_of_instantiate_eq {first second : Nat → LF.Term} {index : Nat} :
    ∀ {term : LF.Term} {depth : Nat}, Mentions index depth term →
      instantiate first depth term = instantiate second depth term →
        first index = second index := by
  intro term
  induction term with
  | var found =>
      intro depth mentioned same
      have shape : found = depth + index := mentioned
      subst shape
      simp only [instantiate, Nat.not_lt.mpr (Nat.le_add_right depth index), if_false,
        Nat.add_sub_cancel_left] at same
      exact lift_injective depth same
  | srt sort => intro depth mentioned _; exact mentioned.elim
  | con name => intro depth mentioned _; exact mentioned.elim
  | pi domain body ihDomain ihBody =>
      intro depth mentioned same
      simp only [instantiate, LF.Term.pi.injEq] at same
      rcases mentioned with inDomain | inBody
      · exact ihDomain inDomain same.1
      · exact ihBody inBody same.2
  | lam domain body ihDomain ihBody =>
      intro depth mentioned same
      simp only [instantiate, LF.Term.lam.injEq] at same
      rcases mentioned with inDomain | inBody
      · exact ihDomain inDomain same.1
      · exact ihBody inBody same.2
  | app function argument ihFunction ihArgument =>
      intro depth mentioned same
      simp only [instantiate, LF.Term.app.injEq] at same
      rcases mentioned with inFunction | inArgument
      · exact ihFunction inFunction same.1
      · exact ihArgument inArgument same.2

/-- **Two assignments that agree at the variables that occur in a term give
one instance of it.** -/
theorem instantiate_congr_of_mentions {first second : Nat → LF.Term} :
    ∀ {term : LF.Term} {depth : Nat},
      (∀ index, Mentions index depth term → first index = second index) →
        instantiate first depth term = instantiate second depth term := by
  intro term
  induction term with
  | var found =>
      intro depth agree
      by_cases bound : found < depth
      · simp [instantiate, bound]
      · have value := agree (found - depth) (show found = depth + (found - depth) by omega)
        simp [instantiate, bound, value]
  | srt sort => intro depth _; rfl
  | con name => intro depth _; rfl
  | pi domain body ihDomain ihBody =>
      intro depth agree
      simp only [instantiate]
      rw [ihDomain fun index mentioned => agree index (Or.inl mentioned),
        ihBody fun index mentioned => agree index (Or.inr mentioned)]
  | lam domain body ihDomain ihBody =>
      intro depth agree
      simp only [instantiate]
      rw [ihDomain fun index mentioned => agree index (Or.inl mentioned),
        ihBody fun index mentioned => agree index (Or.inr mentioned)]
  | app function argument ihFunction ihArgument =>
      intro depth agree
      simp only [instantiate]
      rw [ihFunction fun index mentioned => agree index (Or.inl mentioned),
        ihArgument fun index mentioned => agree index (Or.inr mentioned)]

/-! ## Rules that determine their right sides, by their variables -/

/-- An assignment with one value changed to a variable. -/
def assignedAt (index value : Nat) : Nat → LF.Term :=
  Function.update (fun _ => LF.Term.srt .type) index (.var value)

/-- The instances of a term in which the changed variable does not occur do
not depend on the value. -/
theorem inst_assignedAt_of_not_mentions {index : Nat} {term : LF.Term}
    (absent : ¬ Mentions index 0 term) (first second : Nat) :
    inst (assignedAt index first) term = inst (assignedAt index second) term :=
  instantiate_congr_of_mentions fun other mentioned => by
    have differs : other ≠ index := fun same => absent (same ▸ mentioned)
    rw [assignedAt, assignedAt, Function.update_of_ne differs, Function.update_of_ne differs]

/-- The instances of a term in which it occurs do. -/
theorem inst_assignedAt_injective {index : Nat} {term : LF.Term}
    (present : Mentions index 0 term) :
    Function.Injective fun value => inst (assignedAt index value) term := by
  intro first second same
  have values := eq_of_instantiate_eq present same
  rw [assignedAt, assignedAt, Function.update_self, Function.update_self] at values
  exact LF.Term.var.inj values

/-- **A rule determines its right side exactly when every free variable of
its right side occurs in its left side.** -/
theorem rightDetermined_iff_mentions {rule : Dedukti.RewriteRule} :
    RightDetermined rule ↔ ∀ index, Mentions index 0 rule.rhs → Mentions index 0 rule.lhs := by
  constructor
  · intro determined index inRight
    by_contra notLeft
    have same := determined (assignedAt index 0) (assignedAt index 1)
      (inst_assignedAt_of_not_mentions notLeft 0 1)
    exact absurd (inst_assignedAt_injective inRight same) (by decide)
  · intro bound first second same
    exact instantiate_congr_of_mentions fun index inRight =>
      eq_of_instantiate_eq (bound index inRight) same

/-- A rule that does not determine its right side has a variable on its
right side that its left side does not bind. -/
theorem exists_unbound_of_not_rightDetermined {rule : Dedukti.RewriteRule}
    (free : ¬ RightDetermined rule) :
    ∃ index, Mentions index 0 rule.rhs ∧ ¬ Mentions index 0 rule.lhs := by
  by_contra none
  exact free (rightDetermined_iff_mentions.mpr fun index inRight =>
    by_contra fun notLeft => none ⟨index, inRight, notLeft⟩)

/-- The check that a term uses only some variables, by the variables that
occur in it. -/
theorem usesOnly_iff_mentions {allowed : List Nat} :
    ∀ {term : LF.Term} {depth : Nat},
      usesOnly allowed depth term = true ↔
        ∀ index, Mentions index depth term → index ∈ allowed := by
  intro term
  induction term with
  | var found =>
      intro depth
      simp only [usesOnly, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (bound | listed) index mentioned
        · have shape : found = depth + index := mentioned
          omega
        · have shape : found = depth + index := mentioned
          have same : found - depth = index := by omega
          exact same ▸ listed
      · intro each
        by_cases bound : found < depth
        · exact Or.inl bound
        · exact Or.inr (each (found - depth) (show found = depth + (found - depth) by omega))
  | srt sort => intro depth; exact ⟨fun _ _ mentioned => mentioned.elim, fun _ => rfl⟩
  | con name => intro depth; exact ⟨fun _ _ mentioned => mentioned.elim, fun _ => rfl⟩
  | pi domain body ihDomain ihBody =>
      intro depth
      simp only [usesOnly, Bool.and_eq_true, ihDomain, ihBody]
      exact ⟨fun both index mentioned => mentioned.elim (both.1 index) (both.2 index),
        fun each => ⟨fun index mentioned => each index (Or.inl mentioned),
          fun index mentioned => each index (Or.inr mentioned)⟩⟩
  | lam domain body ihDomain ihBody =>
      intro depth
      simp only [usesOnly, Bool.and_eq_true, ihDomain, ihBody]
      exact ⟨fun both index mentioned => mentioned.elim (both.1 index) (both.2 index),
        fun each => ⟨fun index mentioned => each index (Or.inl mentioned),
          fun index mentioned => each index (Or.inr mentioned)⟩⟩
  | app function argument ihFunction ihArgument =>
      intro depth
      simp only [usesOnly, Bool.and_eq_true, ihFunction, ihArgument]
      exact ⟨fun both index mentioned => mentioned.elim (both.1 index) (both.2 index),
        fun each => ⟨fun index mentioned => each index (Or.inl mentioned),
          fun index mentioned => each index (Or.inr mentioned)⟩⟩

/-- The pattern variables of a term without binder are the variables that
occur in it. -/
theorem mem_patternVars_iff_mentions {index : Nat} :
    ∀ {term : LF.Term}, binderFree term = true →
      (index ∈ patternVars term ↔ Mentions index 0 term) := by
  intro term
  induction term with
  | var found =>
      intro _
      simp only [patternVars, List.mem_singleton, Mentions, Nat.zero_add]
      exact eq_comm
  | srt sort => intro _; simp [patternVars, Mentions]
  | con name => intro _; simp [patternVars, Mentions]
  | pi domain body _ _ => intro free; simp [binderFree] at free
  | lam domain body _ _ => intro free; simp [binderFree] at free
  | app function argument ihFunction ihArgument =>
      intro free
      simp only [binderFree, Bool.and_eq_true] at free
      simp only [patternVars, List.mem_append, Mentions, ihFunction free.1, ihArgument free.2]

/-- **For a rule without binder on its left side, the check that its right
side uses only the variables of its left side says that it determines its
right side.** -/
theorem usesOnly_patternVars_iff_rightDetermined {rule : Dedukti.RewriteRule}
    (leftFree : binderFree rule.lhs = true) :
    usesOnly (patternVars rule.lhs) 0 rule.rhs = true ↔ RightDetermined rule := by
  rw [usesOnly_iff_mentions, rightDetermined_iff_mentions]
  exact forall_congr' fun index => imp_congr_right fun _ => mem_patternVars_iff_mentions leftFree

/-- **A theory with a rule that does not determine its right side has a term
with infinitely many reducts.** -/
theorem infinite_reducts_of_not_rightDetermined {theory : Theory} {rule : Dedukti.RewriteRule}
    (member : theory.rule rule) (free : ¬ RightDetermined rule) :
    ∃ term : LF.Term, {next | Dedukti.Step theory term next}.Infinite := by
  obtain ⟨index, inRight, notLeft⟩ := exists_unbound_of_not_rightDetermined free
  refine ⟨inst (assignedAt index 0) rule.lhs,
    Set.infinite_of_injective_forall_mem (inst_assignedAt_injective inRight) fun value => ?_⟩
  have root := RootStep.rule (theory := theory) (assignedAt index value) member
  rw [inst_assignedAt_of_not_mentions notLeft value 0] at root
  exact Dedukti.Step.root root

/-! ## Which theories given by a table are finitely branching -/

/-- **In a theory given by a table each term has finitely many reducts
exactly when the rules of the table determine their right sides.** -/
theorem finite_reducts_iff_determinedTable {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) :
    (∀ term : LF.Term, {next | Dedukti.Step theory term next}.Finite) ↔
      DeterminedTable table := by
  constructor
  · intro finite rule member
    by_contra free
    obtain ⟨term, infinite⟩ :=
      infinite_reducts_of_not_rightDetermined ((tabular.rules rule).mpr member) free
    exact infinite (finite term)
  · intro determined term
    exact (step_finite_of_rootStep_finite (rootStep_finite_of_rightDetermined determined)
      term).subset fun _ step => tabular.step_iff.mp step

/-- **Exactly the tables whose rules determine their right sides.**  A theory
given by a table is hosted on terms by the probe with the run constructor,
under some evaluator that respects the static equivalence, exactly when the
rules of the table determine their right sides. -/
theorem hostedBy_respecting_iff_determinedTable {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) :
    (∃ base : BasePremiseEvaluator, RespectsStatics base probeWithRun ∧
        HostedBy ((rewritingTheory theory).gslt ()).termsAlone
          (contextTheory base runPresentation)) ↔
      DeterminedTable table :=
  (hostedBy_respecting_iff_finite theory).trans (finite_reducts_iff_determinedTable tabular)

/-- **One evaluator for the whole class.**  A class of theories given by
tables has an evaluator that respects the static equivalence and under which
the probe with the run constructor is a host of the class, on terms, exactly
when the rules of each of the tables determine their right sides. -/
theorem exists_respecting_hostOf_iff_determinedTabular {sources : ContextTheory.{0} → Prop}
    (tabular : ∀ source, sources source → TabularTheory source) :
    (∃ base : BasePremiseEvaluator, RespectsStatics base probeWithRun ∧
        HostOf (contextTheory base runPresentation) sources .terms .hosting) ↔
      ∀ source, sources source → DeterminedTabularTheory source := by
  constructor
  · rintro ⟨base, respects, hosts⟩ source member
    obtain ⟨theory, table, isTabular, rfl⟩ := tabular source member
    exact ⟨theory, table, isTabular,
      (hostedBy_respecting_iff_determinedTable isTabular).mp
        ⟨base, respects, hosts _ ⟨_, member, (), rfl⟩⟩, rfl⟩
  · intro determined
    exact ⟨determinedEvaluator, determinedEvaluator_respectsStatics,
      runPresentation_hostOf_determinedTabular_terms.mono determined⟩

/-- **Negative**: the rule `c ⟶ x` does not determine its right side, by its
variables. -/
theorem freeRule_unbound : Mentions 0 0 freeRule.rhs ∧ ¬ Mentions 0 0 freeRule.lhs := by
  constructor
  · show Mentions 0 0 (.var 0)
    rfl
  · show ¬ Mentions 0 0 (.con "c")
    exact id

#print axioms lift_injective
#print axioms eq_of_instantiate_eq
#print axioms instantiate_congr_of_mentions
#print axioms rightDetermined_iff_mentions
#print axioms usesOnly_iff_mentions
#print axioms mem_patternVars_iff_mentions
#print axioms usesOnly_patternVars_iff_rightDetermined
#print axioms infinite_reducts_of_not_rightDetermined
#print axioms finite_reducts_iff_determinedTable
#print axioms hostedBy_respecting_iff_determinedTable
#print axioms exists_respecting_hostOf_iff_determinedTabular
#print axioms freeRule_unbound

end Mettapedia.Logic.HostingStyles.PrimeCandidate
