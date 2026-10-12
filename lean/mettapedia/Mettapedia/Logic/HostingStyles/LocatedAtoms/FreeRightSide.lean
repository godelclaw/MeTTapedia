import Mettapedia.Logic.HostingStyles.LocatedAtoms.Limits

/-!
# Located atoms: a right side with a variable that the left side does not bind

The rule `c ⟶ x` sends the constant `c` to every term.  A space stores it as
one equation, and the answers of a space for a subject are at most one for
each stored atom.  So the run of the atom of `c` in the space of that rule
has at most one result, as in the two other candidates.

* **A step from a spelling of a leaf is a root step** (`leaf_spelled_stepAt`):
  a leaf has no beta step and no part, so a step from one of its spellings is
  the root step of one of the runs around it, and its result has the normal
  form of an answer of the space pushed in the space.
* **The run of `c` in the space of the rule `c ⟶ x` has at most one result**
  (`located_freeRule_unique`).
* **The rule is not hosted by this reading** (`located_freeRule_not_preserved`):
  `c` steps to the sort of types and to the sort of kinds, and its image does
  not step to the images of both.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-- A leaf has no run. -/
theorem IsLeaf.clean {atom : Pattern} (leaf : IsLeaf atom) : tokens runLabel atom = 0 := by
  rcases leaf with ⟨index, rfl⟩ | ⟨code, rfl⟩ | ⟨index, rfl⟩
  · rfl
  · simpa [symbolAtom, tokens, tokensList, runLabel] using
      tokens_numeral (counted := runLabel) (by decide) (by decide) code
  · simpa [variableAtom, tokens, tokensList, runLabel] using
      tokens_numeral (counted := runLabel) (by decide) (by decide) index

/-- **A step from a spelling of a leaf is a root step of a run around it**:
its result has the normal form of an answer of the space for the leaf, pushed
in the space. -/
theorem leaf_spelled_stepAt {space : Pattern} (plain : PlainSpace space) :
    ∀ (fuel : Nat) {whole : Bool} {pattern target atom : Pattern},
      Spells space whole pattern atom → IsLeaf atom →
      StepAt locatedEvaluator located fuel pattern target →
        ∃ answer ∈ matchResults space atom, settle target = push space (settle answer) := by
  intro fuel
  induction fuel with
  | zero => intro whole pattern target atom _ _ step; cases step
  | succ fuel ih =>
      intro whole pattern target atom spelled isLeaf step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [located_rewrites, atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, -⟩ := beta_inv matched premises
        obtain ⟨first, second, rfl, -, -⟩ := spelled.app_inv
        exact absurd isLeaf (not_isLeaf_app _ _)
      · obtain ⟨function, argument, next, rfl, -, -⟩ := appFunction_inv matched premises
        obtain ⟨first, second, rfl, -, -⟩ := spelled.app_inv
        exact absurd isLeaf (not_isLeaf_app _ _)
      · obtain ⟨function, argument, next, rfl, -, -⟩ := appArgument_inv matched premises
        obtain ⟨first, second, rfl, -, -⟩ := spelled.app_inv
        exact absurd isLeaf (not_isLeaf_app _ _)
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := piDomain_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.binder_inv (.inr rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := piBody_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.binder_inv (.inr rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := lamDomain_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.binder_inv (.inl rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨domain, binder, body, next, rfl, -, -⟩ := lamBody_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.binder_inv (.inl rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨dropped, rfl, -⟩ := release_inv matched premises
        exact absurd spelled Spells.not_dropped
      · obtain ⟨outer, subject, next, rfl, inner, applied⟩ := runSubject_inv matched premises
        rcases spelled.run_inv with ⟨rfl, other, live⟩ | dead
        · obtain ⟨answer, found, moved⟩ := ih live isLeaf inner
          exact ⟨answer, found, by rw [applied, settle_runPattern, moved, push_push]⟩
        · obtain ⟨answer, found, moved⟩ := ih dead isLeaf inner
          exact ⟨answer, found, by rw [applied, settle_runPattern, moved, push_push]⟩
      · obtain ⟨outer, subject, answer, rfl, found, applied⟩ := locatedRoot_inv matched premises
        rw [locatedAnswers_of_settle (spelled.run_whole.settle_whole plain) isLeaf.clean] at found
        obtain ⟨plainAnswer, inResults, rfl⟩ := List.mem_map.mp found
        exact ⟨plainAnswer, inResults, by
          rw [applied, settle_runPattern, settle_runPattern, plain.normal, push_push]⟩
      · obtain ⟨outer, function, argument, next, rfl, -, -⟩ := runAppFunction_inv matched premises
        obtain ⟨first, second, rfl, -, -⟩ := spelled.run_app_inv
        exact absurd isLeaf (not_isLeaf_app _ _)
      · obtain ⟨outer, function, argument, next, rfl, -, -⟩ := runAppArgument_inv matched premises
        obtain ⟨first, second, rfl, -, -⟩ := spelled.run_app_inv
        exact absurd isLeaf (not_isLeaf_app _ _)
      · obtain ⟨outer, domain, binder, body, next, rfl, -, -⟩ := runPiDomain_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.run_binder_inv (.inr rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨outer, domain, binder, body, next, rfl, -, -⟩ := runPiBody_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.run_binder_inv (.inr rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨outer, domain, binder, body, next, rfl, -, -⟩ := runLamDomain_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.run_binder_inv (.inl rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)
      · obtain ⟨outer, domain, binder, body, next, rfl, -, -⟩ := runLamBody_inv matched premises
        obtain ⟨_, first, second, -, rfl, -, -⟩ := spelled.run_binder_inv (.inl rfl)
        rcases isLeaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)

/-- **The run of `c` in the space of the rule `c ⟶ x` has at most one
result**, up to the static equivalence: two transitions to runs of atoms of
terms are transitions to one run. -/
theorem located_freeRule_unique {first second : LF.Term}
    (firstStep : TermStep locatedEvaluator located (runAtom [freeRule] 0 (.con "c"))
      (runAtom [freeRule] 0 first))
    (secondStep : TermStep locatedEvaluator located (runAtom [freeRule] 0 (.con "c"))
      (runAtom [freeRule] 0 second)) : first = second := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := firstStep
  obtain ⟨otherRedex, otherContractum, otherBefore, ⟨otherFuel, otherFired⟩, otherAfter⟩ :=
    secondStep
  have spelled := spells_of_settle (ruleSpace_plain [freeRule]) redex.2
    (show settle redex.1 = push (ruleSpace [freeRule]) (atomAt 0 (.con "c")) by
      rw [← settle_eq_of_related before]
      exact settle_run_atomAt _ _ 0)
  have otherSpelled := spells_of_settle (ruleSpace_plain [freeRule]) otherRedex.2
    (show settle otherRedex.1 = push (ruleSpace [freeRule]) (atomAt 0 (.con "c")) by
      rw [← settle_eq_of_related otherBefore]
      exact settle_run_atomAt _ _ 0)
  obtain ⟨answer, found, moved⟩ := leaf_spelled_stepAt (ruleSpace_plain [freeRule]) fuel spelled
    (isLeaf_atomAt_con 0 "c") fired
  obtain ⟨otherAnswer, otherFound, otherMoved⟩ :=
    leaf_spelled_stepAt (ruleSpace_plain [freeRule]) otherFuel otherSpelled
      (isLeaf_atomAt_con 0 "c") otherFired
  have short : (matchResults (ruleSpace [freeRule]) (atomAt 0 (.con "c"))).length ≤ 1 := by
    refine (matchResults_length_le _ _).trans ?_
    rw [ruleSpace, storedAtoms_spaceOfAtoms]
    simp
  have same : answer = otherAnswer := eq_of_mem_of_length_le_one short found otherFound
  have firstNormal : push (ruleSpace [freeRule]) (settle answer) =
      push (ruleSpace [freeRule]) (atomAt 0 first) := by
    rw [← moved, settle_eq_of_related after]
    exact settle_run_atomAt _ _ 0
  have secondNormal : push (ruleSpace [freeRule]) (settle otherAnswer) =
      push (ruleSpace [freeRule]) (atomAt 0 second) := by
    rw [← otherMoved, settle_eq_of_related otherAfter]
    exact settle_run_atomAt _ _ 0
  rw [same] at firstNormal
  have plain := congrArg unlocate (firstNormal.symm.trans secondNormal)
  rw [unlocate_push _ _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) first 0),
    unlocate_push _ _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) second 0)] at plain
  exact atomAt_injective 0 plain

/-- **A rule whose right side has a variable that its left side does not
bind is not hosted by this reading**: `c` steps to the sort of types and to
the sort of kinds, and its image does not step to the images of both. -/
theorem located_freeRule_not_preserved :
    Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") (.srt .type) ∧
      Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") (.srt .kind) ∧
        ¬ (TermStep locatedEvaluator located (runAtom [freeRule] 0 (.con "c"))
              (runAtom [freeRule] 0 (.srt .type)) ∧
            TermStep locatedEvaluator located (runAtom [freeRule] 0 (.con "c"))
              (runAtom [freeRule] 0 (.srt .kind))) :=
  ⟨freeRule_step _, freeRule_step _, fun both =>
    absurd (located_freeRule_unique both.1 both.2) (by decide)⟩

#print axioms leaf_spelled_stepAt
#print axioms located_freeRule_unique
#print axioms located_freeRule_not_preserved

end Mettapedia.Logic.HostingStyles.LocatedAtoms
