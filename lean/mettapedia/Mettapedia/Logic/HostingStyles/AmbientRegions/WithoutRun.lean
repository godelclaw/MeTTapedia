import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedContainment

/-!
# A term without a run steps as in the ambient member

On patterns a pattern without a run steps in the contained and in the scoped
presentation as in the member of the ambient family
(`runFree_step_iff_member`).  This module states it for terms.

A term of the ambient presentation is a term of both presentations
(`ambientInContained`, `ambientInScoped`), and those are their terms without
a run.  **Its transitions in the member of each presentation at a space of
the ambient presentation, without a guard, are exactly its transitions in the
member of the ambient family at that space**
(`contained_termStep_iff_member`, `scoped_termStep_iff_member`): every reduct
is again a term of the ambient presentation, because a space without a run
answers no run.

**Negative** (`runEquationSpace_builds_run`): at an ambient space that stores
a run, a term without a run can reach a term with one; the space of the
statement has to be a space of the ambient presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-- **A term without a run, in a language with the constructors of the
ambient presentation and the run, has in the member without a guard the
transitions of the member of the ambient family**, at every space of the
ambient presentation, when the two step on patterns without a run alike. -/
theorem termStep_iff_member_of_runFree {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang) (sub : ∀ rule ∈ ambient.terms, rule ∈ lang.terms)
    (kept : ∀ rule ∈ lang.terms, runLabel rule.label = false → rule ∈ ambient.terms)
    (plain : ∀ rule ∈ lang.terms, usesBareCollection? rule = false) (space : SpaceTerm)
    (steps : ∀ {source target : Pattern}, tokens runLabel source = 0 →
      (Step (regionEvaluator anySubject space.1) lang source target ↔
        Step (ambientEvaluator space.1) ambient source target))
    {interface : Contexts.Interface} (term : Contexts.Term ambient interface)
    (target : Contexts.Term lang interface) :
    TermStep (regionEvaluator anySubject space.1) lang
        ⟨term.1, wellSorted_of_terms_subset sub term.2⟩ target ↔
      ∃ next : Contexts.Term ambient interface, (ambientTheory space).rewrites term next ∧
        target = ⟨next.1, wellSorted_of_terms_subset sub next.2⟩ := by
  have cleanSpace : tokens runLabel (contract space.1) = 0 := by
    rw [tokens_contract (by decide) (by decide)]
    exact tokens_run_ambient space
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    have sameRedex : contract term.1 = contract redex.1 := only.contract_eq before
    have cleanRedex : tokens runLabel redex.1 = 0 := by
      rw [← tokens_contract (counted := runLabel) (by decide) (by decide) redex.1, ← sameRedex,
        tokens_contract (by decide) (by decide)]
      exact tokens_run_ambient term
    obtain ⟨fuel, bounded⟩ := (steps cleanRedex).mp fired
    have cleanContractum : tokens runLabel contractum.1 = 0 :=
      ambient_stepAt_tokens (by decide) (by decide) cleanSpace fuel bounded cleanRedex
    have sameTarget : contract contractum.1 = contract target.1 := only.contract_eq after
    have cleanTarget : tokens runLabel target.1 = 0 := by
      rw [← tokens_contract (counted := runLabel) (by decide) (by decide) target.1, ← sameTarget,
        tokens_contract (by decide) (by decide)]
      exact cleanContractum
    refine ⟨⟨target.1, wellSorted_of_tokens_eq_zero kept plain target.2 cleanTarget⟩,
      ⟨⟨redex.1, wellSorted_of_tokens_eq_zero kept plain redex.2 cleanRedex⟩,
        ⟨contractum.1, wellSorted_of_tokens_eq_zero kept plain contractum.2 cleanContractum⟩,
        ?_, ⟨fuel, bounded⟩, ?_⟩, rfl⟩
    · exact (ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted).mpr sameRedex
    · exact (ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted).mpr sameTarget
  · rintro ⟨next, ⟨redex, contractum, before, fired, after⟩, rfl⟩
    refine ⟨⟨redex.1, wellSorted_of_terms_subset sub redex.2⟩,
      ⟨contractum.1, wellSorted_of_terms_subset sub contractum.2⟩, ?_,
      (steps (tokens_run_ambient redex)).mpr fired, ?_⟩
    · exact (only.termSetoid_iff sorted).mpr (ambient_quoteDropOnly.contract_eq before)
    · exact (only.termSetoid_iff sorted).mpr (ambient_quoteDropOnly.contract_eq after)

/-- A term of the ambient presentation, as a term of the contained one. -/
def ambientInContained {interface : Contexts.Interface} (term : Contexts.Term ambient interface) :
    Contexts.Term containedRun interface :=
  ⟨term.1, wellSorted_of_terms_subset (small := ambient) (large := containedRun)
    ambient_terms_subset term.2⟩

/-- A term of the ambient presentation, as a term of the scoped one. -/
def ambientInScoped {interface : Contexts.Interface} (term : Contexts.Term ambient interface) :
    Contexts.Term scopedRun interface :=
  ⟨term.1, wellSorted_of_terms_subset (small := ambient) (large := scopedRun)
    ambient_terms_subset term.2⟩

/-- **Positive**: such a term has no run. -/
theorem tokens_run_ambientInContained {interface : Contexts.Interface}
    (term : Contexts.Term ambient interface) : tokens runLabel (ambientInContained term).1 = 0 :=
  tokens_run_ambient term

/-- **Negative**: the run of the unit atom in the empty space is a term of
the contained presentation that is no term of the ambient one. -/
theorem run_not_ambientInContained (term : Contexts.Term ambient AtomsReduce.closedAtom) :
    (ambientInContained term).1 ≠ runPattern emptySpace unitAtom := by
  intro same
  have clean := tokens_run_ambient term
  have patterns : term.1 = runPattern emptySpace unitAtom := same
  rw [patterns] at clean
  exact absurd clean (by decide)

/-- **In the contained presentation, a term without a run has the
transitions of the member of the ambient family**, at every space of the
ambient presentation and without a guard. -/
theorem contained_termStep_iff_member (space : SpaceTerm) {interface : Contexts.Interface}
    (term : Contexts.Term ambient interface) (target : Contexts.Term containedRun interface) :
    TermStep (regionEvaluator anySubject space.1) containedRun (ambientInContained term) target ↔
      ∃ next : Contexts.Term ambient interface, (ambientTheory space).rewrites term next ∧
        target = ambientInContained next :=
  termStep_iff_member_of_runFree contained_quoteDropOnly contained_quoteDropSorted
    ambient_terms_subset atomsReduce_terms_kept atomsReduce_plain space
    (fun clean => (runFree_step_iff_member clean).1) term target

/-- **In the scoped presentation, a term without a run has the transitions of
the member of the ambient family**, at every space of the ambient
presentation and without a guard. -/
theorem scoped_termStep_iff_member (space : SpaceTerm) {interface : Contexts.Interface}
    (term : Contexts.Term ambient interface) (target : Contexts.Term scopedRun interface) :
    TermStep (regionEvaluator anySubject space.1) scopedRun (ambientInScoped term) target ↔
      ∃ next : Contexts.Term ambient interface, (ambientTheory space).rewrites term next ∧
        target = ambientInScoped next :=
  termStep_iff_member_of_runFree scoped_quoteDropOnly scoped_quoteDropSorted
    ambient_terms_subset atomsReduce_terms_kept atomsReduce_plain space
    (fun clean => (runFree_step_iff_member clean).2) term target

/-- An equation whose right side is a run: the unit atom steps to the run of
the unit atom in the empty space. -/
def unitToRun : Pattern := .apply "=" [unitAtom, runPattern emptySpace unitAtom]

/-- **Negative**: at an ambient space that stores a run, a term without a run
reaches a term with one.  The space of the two statements above has to be a
space of the ambient presentation. -/
theorem runEquationSpace_builds_run :
    Step (regionEvaluator anySubject (spaceOfAtoms [unitToRun])) containedRun unitAtom
        (runPattern emptySpace unitAtom) ∧
      tokens runLabel unitAtom = 0 ∧ tokens runLabel (runPattern emptySpace unitAtom) ≠ 0 := by
  refine ⟨⟨1, step_ambientRoot (by simp [contained_rewrites]) ?_⟩, by decide, by decide⟩
  refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
  have spaceFixed : contract (spaceOfAtoms [unitToRun]) = spaceOfAtoms [unitToRun] := by decide
  have subjectFixed : contract unitAtom = unitAtom := by decide
  rw [spaceFixed, subjectFixed, mem_matchResults_spaceOfAtoms]
  refine ⟨unitToRun, List.mem_singleton.mpr rfl, ?_⟩
  have leftRead : asRule unitAtom = unitAtom := by decide
  have rightRead : asRule (runPattern emptySpace unitAtom) = runPattern emptySpace unitAtom := by
    decide
  rw [unitToRun, atomResults_equation _ (by rw [leftRead]; decide) (by rw [rightRead]; decide),
    leftRead, rightRead]
  simp [runPattern, emptySpace, unitAtom, matchPattern, matchArgs, applyBindings]

#print axioms termStep_iff_member_of_runFree
#print axioms contained_termStep_iff_member
#print axioms scoped_termStep_iff_member
#print axioms runEquationSpace_builds_run
#print axioms tokens_run_ambientInContained
#print axioms run_not_ambientInContained

end Mettapedia.Logic.HostingStyles.AmbientRegions
