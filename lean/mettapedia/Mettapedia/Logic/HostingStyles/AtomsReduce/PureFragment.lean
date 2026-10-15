import Mettapedia.Logic.HostingStyles.AtomsReduce.Hosting

/-!
# What the candidate computes without a space: the pure calculus, under every evaluator

Beta and the congruences of application, abstraction and product are
rewrites of the candidate, and they carry no premise that an evaluator
answers.  So **under every evaluator of its premises the candidate hosts the
pure λΠ-calculus on all its terms** (`atomMap_hosting`,
`pure_hostedBy_everyEvaluator`): a term is read as its atom, with no run and
no space.  One step of the calculus is one step of the candidate.

This is the part of the candidate that does not ask the evaluator.  The
rules that a table adds are found by the evaluator in a space, through a run
(`tableMap_hosting`); under the evaluator that answers nothing the run of a
term in the space of a rule has the beta steps only
(`silent_run_misses_rule`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-- The atom of a term has no dropping. -/
theorem tokens_drop_atomAt (term : LF.Term) (depth : Nat) :
    tokens dropLabel (atomAt depth term) = 0 :=
  tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) term depth

/-- **The atom of a term is the only term of its class**: what the static
equivalence identifies with it is it. -/
theorem eq_atomTermAt_of_related {base : BasePremiseEvaluator} {depth : Nat} {term : LF.Term}
    {other : Contexts.Term atomsReduce (atomInterface depth)}
    (related : (termSetoid base atomsReduce (atomInterface depth)).r (atomTermAt depth term) other) :
    other = atomTermAt depth term :=
  eq_of_related_of_dropFree (show resultIn unquotedSorts (.base "Atom") = true by decide)
    (contract_atomAt term depth) (tokens_drop_atomAt term depth) related

/-- **The transitions of the atom of a term are the atoms of its beta
steps**, at every depth and under every evaluator. -/
theorem termStep_atomTermAt_iff {base : BasePremiseEvaluator} {depth : Nat} {source : LF.Term}
    {target : Contexts.Term atomsReduce (atomInterface depth)} :
    TermStep base atomsReduce (atomTermAt depth source) target ↔
      ∃ next, Dedukti.Step Theory.empty source next ∧ target = atomTermAt depth next := by
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    obtain rfl := eq_atomTermAt_of_related before
    obtain ⟨next, shape, step⟩ := plain_step_iff.mp fired
    have same : contractum = atomTermAt depth next := Subtype.ext shape
    rw [same] at after
    exact ⟨next, step, eq_atomTermAt_of_related after⟩
  · rintro ⟨next, step, rfl⟩
    exact ⟨atomTermAt depth source, atomTermAt depth next, Relation.EqvGen.refl _,
      plain_step_iff.mpr ⟨next, rfl, step⟩, Relation.EqvGen.refl _⟩

/-- **The pure calculus, in the candidate**: a term is read as its atom. -/
def atomMap (base : BasePremiseEvaluator) :
    ContextMap ((rewritingTheory Theory.empty).gslt ()).termsAlone
      (contextTheory base atomsReducePresentation) :=
  ContextMap.ofTerms (source := (rewritingTheory Theory.empty).gslt ())
    (target := contextTheory base atomsReducePresentation) closedAtom
    (fun term => atomTermAt 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- **Under every evaluator of its premises the candidate hosts the pure
λΠ-calculus on all its terms**, by beta and congruences of its own. -/
theorem atomMap_hosting (base : BasePremiseEvaluator) : (atomMap base).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory Theory.empty).gslt ())
    (target := contextTheory base atomsReducePresentation) closedAtom
    (fun term => atomTermAt 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same : atomTermAt 0 second = atomTermAt 0 first :=
      eq_atomTermAt_of_related (base := base) (depth := 0) related
    exact (atomAt_injective 0 (congrArg Subtype.val same)).symm
  · intro first next step
    exact (termStep_atomTermAt_iff (base := base) (depth := 0)).mpr ⟨next, step, rfl⟩
  · intro first next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTermAt_iff (base := base) (depth := 0)).mp step
    exact ⟨nextTerm, sourceStep, Relation.EqvGen.refl _⟩

/-- So under every evaluator, the one that answers nothing included, the
presentation hosts the pure calculus on terms. -/
theorem pure_hostedBy_everyEvaluator (base : BasePremiseEvaluator) :
    HostedBy ((rewritingTheory Theory.empty).gslt ()).termsAlone
      (contextTheory base atomsReducePresentation) :=
  ⟨atomMap base, atomMap_hosting base⟩

/-- **Negative**: under the evaluator that answers nothing, a rule stored in
a space is not applied: the run of `choose heads tails` in the space of the
two rules of choice has no transition, while under the matching evaluator it
has two. -/
theorem silent_run_misses_rule
    (target : Contexts.Term atomsReduce closedAtom) :
    ¬ TermStep silentEvaluator atomsReduce
      (runTermIn [Dedukti.chooseLeft, Dedukti.chooseRight]
        (Dedukti.choose (.con "heads") (.con "tails"))) target := by
  rintro ⟨redex, contractum, before, ⟨fuel, fired⟩, -⟩
  obtain rfl := eq_runTermIn_of_related before
  have plainOnly : ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {reduct : Pattern},
      StepAt silentEvaluator atomsReduce fuel
          (runPattern (ruleSpace [Dedukti.chooseLeft, Dedukti.chooseRight]) (atomAt depth source))
          reduct →
        ∃ next, Dedukti.Step Theory.empty source next := by
    intro fuel
    induction fuel with
    | zero => intro depth source reduct step; cases step
    | succ fuel ih =>
        intro depth source reduct step
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
        · obtain ⟨space, subject, next, shape, inner, -⟩ := runSubject_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨nextTerm, -, innerStep⟩ := plain_stepAt_sound Theory.empty fuel inner
          exact ⟨nextTerm, innerStep⟩
        · have silent : PremisesAt silentEvaluator atomsReduce fuel initial [runPremise] final :=
            premises
          cases silent with
          | cons first rest =>
              cases first with
              | relationQuery answered => cases answered
        · obtain ⟨space, function, argument, next, shape, inner, -⟩ :=
            runAppFunction_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app subjectEq
          obtain ⟨nextTerm, innerStep⟩ := ih inner
          exact ⟨_, innerStep.plug (.appFunction .hole second)⟩
        · obtain ⟨space, function, argument, next, shape, inner, -⟩ :=
            runAppArgument_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app subjectEq
          obtain ⟨nextTerm, innerStep⟩ := ih inner
          exact ⟨_, innerStep.plug (.appArgument first .hole)⟩
        · obtain ⟨space, domain, binder, body, next, shape, inner, -⟩ :=
            runPiDomain_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi subjectEq
          obtain ⟨nextTerm, innerStep⟩ := ih inner
          exact ⟨_, innerStep.plug (.piDomain .hole second)⟩
        · obtain ⟨space, domain, binder, body, next, shape, inner, -⟩ :=
            runPiBody_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi subjectEq
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, innerStep⟩ := ih inner
          exact ⟨_, innerStep.plug (.piBody first .hole)⟩
        · obtain ⟨space, domain, binder, body, next, shape, inner, -⟩ :=
            runLamDomain_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam subjectEq
          obtain ⟨nextTerm, innerStep⟩ := ih inner
          exact ⟨_, innerStep.plug (.lamDomain .hole second)⟩
        · obtain ⟨space, domain, binder, body, next, shape, inner, -⟩ :=
            runLamBody_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam subjectEq
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, innerStep⟩ := ih inner
          exact ⟨_, innerStep.plug (.lamBody first .hole)⟩
  obtain ⟨next, step⟩ := plainOnly fuel fired
  exact Dedukti.normal_of_normalTest emptyCover _ (by decide) _ step

#print axioms termStep_atomTermAt_iff
#print axioms atomMap_hosting
#print axioms pure_hostedBy_everyEvaluator
#print axioms silent_run_misses_rule

end Mettapedia.Logic.HostingStyles.AtomsReduce
