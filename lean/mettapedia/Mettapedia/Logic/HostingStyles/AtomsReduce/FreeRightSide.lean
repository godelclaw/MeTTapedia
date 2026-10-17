import Mettapedia.Logic.HostingStyles.AtomsReduce.Hosting

/-!
# A right side with a variable that the left side does not bind

The class that the candidate hosts on terms leaves out the tables with a rule
whose right side mentions a variable that its left side does not bind.  This
module gives the witness for the reading of terms as runs.

The rule `c ⟶ x` sends the constant `c` to every term.  A space answers a
subject with at most as many atoms as it stores, so the run of `c` in the
space of that rule has at most one transition by the rule, and it has none by
beta (`constant_run_stepAt_inv`).  Two steps of `c` with results that are
apart are therefore not both steps of the image (`freeRule_not_preserved`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory inst normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-- Two members of a list with at most one member are one. -/
theorem eq_of_mem_of_length_le_one {α : Type} {list : List α} (short : list.length ≤ 1)
    {first second : α} (firstIn : first ∈ list) (secondIn : second ∈ list) : first = second := by
  rcases list with _ | ⟨head, _ | ⟨next, rest⟩⟩
  · cases firstIn
  · rw [List.mem_singleton] at firstIn secondIn
    rw [firstIn, secondIn]
  · simp at short

/-- **The run of the constant `c` steps by an answer of its space alone**:
the constant has no beta step, and it is no application, abstraction or
product, so no congruence beneath the run applies. -/
theorem constant_run_stepAt_inv {space : Pattern} {fuel : Nat} {target : Pattern}
    (step : StepAt matchingEvaluator atomsReduce fuel
      (runPattern space (atomAt 0 (.con "c"))) target) :
    ∃ answer ∈ matchResults (contract space) (atomAt 0 (.con "c")),
      target = runPattern space answer := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨otherSpace, subject, next, shape, inner, -⟩ := runSubject_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨nextTerm, -, innerStep⟩ := plain_stepAt_sound Theory.empty fuel inner
        exact absurd innerStep (normal_of_normalTest emptyCover _ (by decide) _)
      · obtain ⟨otherSpace, subject, answer, shape, found, applied⟩ :=
          runRoot_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [contract_atomAt] at found
        exact ⟨answer, found, applied⟩
      · obtain ⟨otherSpace, function, argument, next, shape, -, -⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨first, second, termEq, -, -⟩ := atomAt_eq_app (runPattern_injective shape).2
        cases termEq
      · obtain ⟨otherSpace, function, argument, next, shape, -, -⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨first, second, termEq, -, -⟩ := atomAt_eq_app (runPattern_injective shape).2
        cases termEq
      · obtain ⟨otherSpace, domain, binder, body, next, shape, -, -⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨first, second, termEq, -, -⟩ := atomAt_eq_pi (runPattern_injective shape).2
        cases termEq
      · obtain ⟨otherSpace, domain, binder, body, next, shape, -, -⟩ :=
          runPiBody_inv matched premises
        obtain ⟨first, second, termEq, -, -⟩ := atomAt_eq_pi (runPattern_injective shape).2
        cases termEq
      · obtain ⟨otherSpace, domain, binder, body, next, shape, -, -⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨first, second, termEq, -, -⟩ := atomAt_eq_lam (runPattern_injective shape).2
        cases termEq
      · obtain ⟨otherSpace, domain, binder, body, next, shape, -, -⟩ :=
          runLamBody_inv matched premises
        obtain ⟨first, second, termEq, -, -⟩ := atomAt_eq_lam (runPattern_injective shape).2
        cases termEq

/-- `c ⟶ x` sends the constant to every term. -/
theorem freeRule_step (term : LF.Term) :
    Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") term := by
  have root : Dedukti.RootStep (Theory.ofTable {freeRule}) (inst (fun _ => term) freeRule.lhs)
      (inst (fun _ => term) freeRule.rhs) := .rule _ (Finset.mem_singleton_self _)
  simpa [freeRule] using Dedukti.Step.root root

/-- **The run of `c` in the space of the rule `c ⟶ x` has at most one
result**, up to the static equivalence: two transitions to runs of terms are
transitions to one run. -/
theorem freeRule_run_unique {first second : LF.Term}
    (firstStep : atomsReduceTheory.rewrites (runTermIn [freeRule] (.con "c"))
      (runTermIn [freeRule] first))
    (secondStep : atomsReduceTheory.rewrites (runTermIn [freeRule] (.con "c"))
      (runTermIn [freeRule] second)) : first = second := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := firstStep
  obtain ⟨otherRedex, otherContractum, otherBefore, ⟨otherFuel, otherFired⟩, otherAfter⟩ :=
    secondStep
  obtain rfl := eq_runTermIn_of_related before
  obtain rfl := eq_runTermIn_of_related otherBefore
  obtain rfl := eq_runTermIn_of_related
    ((termSetoid matchingEvaluator atomsReduce closedAtom).iseqv.symm after)
  obtain rfl := eq_runTermIn_of_related
    ((termSetoid matchingEvaluator atomsReduce closedAtom).iseqv.symm otherAfter)
  obtain ⟨answer, found, shape⟩ := constant_run_stepAt_inv fired
  obtain ⟨otherAnswer, otherFound, otherShape⟩ := constant_run_stepAt_inv otherFired
  have firstAnswer : atomAt 0 first = answer := (runPattern_injective shape).2
  have secondAnswer : atomAt 0 second = otherAnswer := (runPattern_injective otherShape).2
  have short : (matchResults (contract (ruleSpace [freeRule])) (atomAt 0 (.con "c"))).length ≤ 1 := by
    refine (matchResults_length_le _ _).trans ?_
    rw [contract_ruleSpace, ruleSpace, storedAtoms_spaceOfAtoms]
    simp
  have same : answer = otherAnswer := eq_of_mem_of_length_le_one short found otherFound
  exact atomAt_injective 0 (firstAnswer.trans (same.trans secondAnswer.symm))

/-- **A rule whose right side has a variable that its left side does not
bind is not hosted by this reading**: `c` steps to the sort of types and to
the sort of kinds, and its image does not step to the images of both. -/
theorem freeRule_not_preserved :
    Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") (.srt .type) ∧
      Dedukti.Step (Theory.ofTable {freeRule}) (.con "c") (.srt .kind) ∧
        ¬ (atomsReduceTheory.rewrites (runTermIn [freeRule] (.con "c"))
              (runTermIn [freeRule] (.srt .type)) ∧
            atomsReduceTheory.rewrites (runTermIn [freeRule] (.con "c"))
              (runTermIn [freeRule] (.srt .kind))) :=
  ⟨freeRule_step _, freeRule_step _, fun both =>
    absurd (freeRule_run_unique both.1 both.2) (by decide)⟩

#print axioms constant_run_stepAt_inv
#print axioms freeRule_step
#print axioms freeRule_run_unique
#print axioms freeRule_not_preserved

end Mettapedia.Logic.HostingStyles.AtomsReduce
