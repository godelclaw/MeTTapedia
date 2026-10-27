import Mettapedia.Languages.Megalodon.FuelledConversionWitness
import Mettapedia.TypeTheory.GradedCheck

/-!
# The definition-unfolding search as a graded check, and what its answers do not mean

`FuelledConversionWitness.seek` follows named-definition unfoldings forward from a source
towards a target within a budget and answers `found`, `exhausted` or `refused`. It decides
exactly one judgment: the target lies on the forward unfolding chain of the source
(`Reaches`). For that judgment it is a graded check in the sense of `TypeTheory.GradedCheck`
(`searchCheck`): `found` is established evidence, `exhausted` an incomplete run, `refused` a
checked refutation (`not_reaches_of_refused`).

Its evidence transfers to conversion (`conversion_of_reaches`); its refutations do not.

* **Refusal is not inequality** (`Controls.refused_not_inequality`): at every budget the
  search refutes that `a` lies on the chain of the parameter `c`, and `c` converts to `a`.
* **Exhaustion is not inequality** (`Controls.exhausted_not_inequality`): the search from
  `a` to `c` is exhausted at budget zero, and `a` converts to `c`.
* **The bounded recognizer's `false` is not a refutation** (`Controls.recognizer_not_refutation`):
  it answers `false` for `a` and `c` at budget one and `true` at budget two, so it reads
  refutation of no graded check of conversion.
* **Read at the level of conversion, a refusal is a boundary found by running**
  (`Controls.boundary_found_by_running`): the search from `a` to an unrelated name is
  exhausted at budget zero and refused at budget two. A conversion-level reading that sends
  `refused` to the boundary outcome therefore moves from `incomplete` to `outsideFragment`,
  which `AuthorityTheory.Outcome.BudgetRefines` does not allow.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.DirectedSearchGradedCheck

open MathdataKernel ConversionElaboration FuelledConversionWitness
open Mettapedia.TypeTheory.AuthorityTheory Mettapedia.TypeTheory.GradedChecking

/-- The target lies on the forward unfolding chain of the source. -/
inductive Reaches (environment : Environment) : Tm → Tm → Prop where
  | here (term : Tm) : Reaches environment term term
  | next {source target : Tm} {step : Step} :
      nextDelta environment source = some step → Reaches environment step.target target →
        Reaches environment source target

/-- **Reaching is conversion**: every unfolding on the chain is a checked reduction. -/
theorem conversion_of_reaches {environment : Environment} {source target : Tm}
    (reaches : Reaches environment source target) : Conversion environment.terms source target := by
  induction reaches with
  | here _ => exact Relation.EqvGen.refl _
  | @next source target step next _ rest =>
      obtain ⟨sourceEq, valid⟩ := nextDelta_valid environment source step next
      have edge : checkEdge environment.terms ⟨step, false⟩ = true := valid
      have first : Conversion environment.terms source step.target := by
        have := edge_sound environment.terms ⟨step, false⟩ edge
        simpa only [Edge.source, Edge.target, Bool.false_eq_true, if_false, sourceEq] using this
      exact Relation.EqvGen.trans _ _ _ first rest

/-- A found path witnesses reaching. -/
theorem reaches_of_found {environment : Environment} :
    ∀ (budget : ℕ) {source target : Tm} {edges : List Edge},
      seek environment budget source target = .found edges → Reaches environment source target
  | 0, source, target, edges, found => by
      simp only [seek] at found
      split at found
      · rename_i same
        subst same
        exact .here _
      · split at found <;> cases found
  | budget + 1, source, target, edges, found => by
      simp only [seek] at found
      split at found
      · rename_i same
        subst same
        exact .here _
      · split at found
        · cases found
        · rename_i step next
          split at found
          · rename_i rest childFound
            exact .next next (reaches_of_found budget childFound)
          · cases found
          · cases found

/-- **A refusal is a checked refutation of reaching.** -/
theorem not_reaches_of_refused {environment : Environment} :
    ∀ (budget : ℕ) {source target : Tm},
      seek environment budget source target = .refused → ¬ Reaches environment source target
  | 0, source, target, refused, reaches => by
      simp only [seek] at refused
      split at refused
      · cases refused
      · rename_i different
        split at refused
        · rename_i none
          cases reaches with
          | here => exact different rfl
          | next next _ => rw [none] at next; cases next
        · cases refused
  | budget + 1, source, target, refused, reaches => by
      simp only [seek] at refused
      split at refused
      · cases refused
      · rename_i different
        split at refused
        · rename_i none
          cases reaches with
          | here => exact different rfl
          | next next _ => rw [none] at next; cases next
        · rename_i step next
          split at refused
          · cases refused
          · cases refused
          · rename_i childRefused
            cases reaches with
            | here => exact different rfl
            | next next' rest =>
                rw [next] at next'
                cases next'
                exact not_reaches_of_refused budget childRefused rest

/-- Reaching, with reaching proofs as evidence and their negations as refutations. -/
def reachingAuthority (environment : Environment) : Authority (Tm × Tm) where
  Holds pair := Reaches environment pair.1 pair.2
  Evidence pair := PLift (Reaches environment pair.1 pair.2)
  Obstruction pair := PLift (¬ Reaches environment pair.1 pair.2)
  evidenceSound _ evidence := evidence.down
  obstructionSound _ obstruction := obstruction.down

/-- The outcome of one directed search. -/
def classify (environment : Environment) (budget : ℕ) (pair : Tm × Tm) :
    AuthorizedOutcome (reachingAuthority environment) Unit Unit pair :=
  match searched : seek environment budget pair.1 pair.2 with
  | .found _ => .established ⟨reaches_of_found budget searched⟩
  | .exhausted => .incomplete ()
  | .refused => .refuted ⟨not_reaches_of_refused budget searched⟩

theorem classify_of_refused {environment : Environment} {budget : ℕ} {pair : Tm × Tm}
    (refused : seek environment budget pair.1 pair.2 = .refused) :
    ∃ obstruction, classify environment budget pair = .refuted obstruction := by
  unfold classify
  split
  · simp_all
  · simp_all
  · exact ⟨_, rfl⟩

theorem classify_of_exhausted {environment : Environment} {budget : ℕ} {pair : Tm × Tm}
    (exhausted : seek environment budget pair.1 pair.2 = .exhausted) :
    classify environment budget pair = .incomplete () := by
  unfold classify
  split <;> simp_all

theorem classify_of_found {environment : Environment} {budget : ℕ} {pair : Tm × Tm}
    {edges : List Edge} (found : seek environment budget pair.1 pair.2 = .found edges) :
    ∃ evidence, classify environment budget pair = .established evidence := by
  unfold classify
  split
  · exact ⟨_, rfl⟩
  · simp_all
  · simp_all

/-- **Monotone in the budget**: only an exhausted search changes its outcome. -/
theorem classify_mono (environment : Environment) (pair : Tm × Tm) {small large : ℕ}
    (le : small ≤ large) :
    Outcome.BudgetRefines (classify environment small pair) (classify environment large pair) := by
  cases searched : seek environment small pair.1 pair.2 with
  | exhausted =>
      rw [classify_of_exhausted searched]
      cases later : seek environment large pair.1 pair.2 with
      | exhausted => rw [classify_of_exhausted later]; exact .incomplete () ()
      | refused =>
          obtain ⟨obstruction, refuted⟩ := classify_of_refused later
          rw [refuted]
          exact .incompleteRefuted () obstruction
      | found edges =>
          obtain ⟨evidence, established⟩ := classify_of_found later
          rw [established]
          exact .incompleteEstablished () evidence
  | refused =>
      have same := seek_completed_mono environment pair.1 pair.2 le (by rw [searched]; simp)
      obtain ⟨before, refutedBefore⟩ := classify_of_refused searched
      obtain ⟨after, refutedAfter⟩ := classify_of_refused (same.trans searched)
      rw [refutedBefore, refutedAfter]
      exact .refuted before after
  | found edges =>
      have same := seek_completed_mono environment pair.1 pair.2 le (by rw [searched]; simp)
      obtain ⟨before, establishedBefore⟩ := classify_of_found searched
      obtain ⟨after, establishedAfter⟩ := classify_of_found (same.trans searched)
      rw [establishedBefore, establishedAfter]
      exact .established before after

/-- **The directed search is a graded check of reaching.** -/
def searchCheck (environment : Environment) :
    GradedCheck (reachingAuthority environment) Unit Unit where
  run := classify environment
  mono pair _ _ le := classify_mono environment pair le

/-- Conversion by checked reduction articles, with checked paths as evidence and no
refutations: the authority the search's evidence transfers to. -/
def conversionAuthority (environment : Environment) : Authority (Tm × Tm) where
  Holds pair := Conversion environment.terms pair.1 pair.2
  Evidence pair := {edges : List Edge // checkPath environment.terms pair.1 pair.2 edges = true}
  Obstruction _ := PEmpty.{1}
  evidenceSound pair evidence := checkPath_sound environment.terms pair.1 pair.2 evidence.1 evidence.2
  obstructionSound _ obstruction := obstruction.elim

/-! ## Separations, in the control environment `a := b`, `b := c`, `c` a parameter -/

namespace Controls

open FuelledConversionWitness.Controls

theorem a_converts_c : Conversion environment.terms (.named "a") (.named "c") :=
  recognizes_sound environment 2 _ _ composite_at_two

/-- **Exhaustion is not inequality.** -/
theorem exhausted_not_inequality :
    (searchCheck environment).run 0 (.named "a", .named "c") = .incomplete () ∧
      Conversion environment.terms (.named "a") (.named "c") :=
  ⟨classify_of_exhausted (environment := environment) (budget := 0)
    (pair := (.named "a", .named "c")) exhausted_with_next_definition, a_converts_c⟩

/-- At every budget the search from the parameter `c` to `a` is refused. -/
theorem seek_c_a_refused (budget : ℕ) : seek environment budget (.named "c") (.named "a") = .refused := by
  cases budget <;> simp [seek, nextDelta, environment, Environment.lookupTerm?, lookupTermList?]

/-- **Refusal is not inequality**: at every budget the search refutes reaching `a` from `c`,
and `c` converts to `a`. -/
theorem refused_not_inequality (budget : ℕ) :
    (∃ obstruction, (searchCheck environment).run budget (.named "c", .named "a") = .refuted obstruction) ∧
      Conversion environment.terms (.named "c") (.named "a") :=
  ⟨classify_of_refused (environment := environment) (budget := budget)
    (pair := (.named "c", .named "a")) (seek_c_a_refused budget),
    Relation.EqvGen.symm _ _ a_converts_c⟩

/-- The search finds the two-step path at budget two. -/
theorem established_at_two :
    ∃ evidence, (searchCheck environment).run 2 (.named "a", .named "c") = .established evidence :=
  classify_of_found (environment := environment) (budget := 2)
    (pair := (.named "a", .named "c")) (edges := [firstEdge, secondEdge])
    (by simp [seek, nextDelta, environment, Environment.lookupTerm?, lookupTermList?, deltaStep,
      firstEdge, secondEdge])

/-- **The bounded recognizer's `false` reads refutation of no graded check of conversion.** -/
theorem recognizer_not_refutation :
    ¬ ∃ check : GradedCheck (conversionAuthority environment) Unit Unit, ∀ budget pair,
      recognizes environment budget pair.1 pair.2 = false ↔
        ∃ obstruction, check.run budget pair = .refuted obstruction :=
  no_refutation_reading_of_flip (fun budget pair => recognizes environment budget pair.1 pair.2)
    (judgment := (.named "a", .named "c")) (small := 1) (large := 2) (by decide)
    composite_not_at_one composite_at_two

/-- **A boundary found by running.** The search from `a` to the unrelated name `z` is
exhausted at budget zero and refused at budget two; a conversion-level reading that sends a
refusal to the boundary outcome moves from `incomplete` to `outsideFragment`, which budget
refinement does not allow. -/
theorem boundary_found_by_running :
    seek environment 0 (.named "a") (.named "z") = .exhausted ∧
      seek environment 2 (.named "a") (.named "z") = .refused ∧
      ¬ Outcome.BudgetRefines
        (.incomplete () : Outcome PUnit.{1} PEmpty.{1} Unit Unit) (.outsideFragment ()) := by
  refine ⟨by simp [seek, nextDelta, environment, Environment.lookupTerm?, lookupTermList?],
    by simp [seek, nextDelta, environment, Environment.lookupTerm?, lookupTermList?, deltaStep], ?_⟩
  intro refines
  cases refines

end Controls

/-! ## Axiom audit -/

#print axioms conversion_of_reaches
#print axioms reaches_of_found
#print axioms not_reaches_of_refused
#print axioms classify_mono
#print axioms searchCheck
#print axioms Controls.exhausted_not_inequality
#print axioms Controls.refused_not_inequality
#print axioms Controls.established_at_two
#print axioms Controls.recognizer_not_refutation
#print axioms Controls.boundary_found_by_running

end Mettapedia.Languages.Megalodon.DirectedSearchGradedCheck
