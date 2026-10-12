import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Readings
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedStored
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedAsWritten
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedReducts
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedContexts
import Mettapedia.Logic.HostingStyles.AtomsReduce.Summary
import Mettapedia.Logic.HostingStyles.AmbientRegions.Summary

/-!
# The candidate of spaces and regions: the table

Four candidates, side by side.

* **A run at the root**: `atomsReduce` under the matching evaluator.  An atom
  reduces by the rules of a space only inside a run; a program is the run of
  its call in the space of its table.
* **`allHeaded`**: an ambient space, a run as a contained region, every root
  step headed by a constructor of atoms, the root steps written by hand.
* **Assembled, on all terms**: `spacesAndRegions`, the presentation
  `allHeaded` with its root steps generated from its constructors
  (`spacesAndRegions_eq_allHeaded`).
* **Assembled, on sealed terms**: `sealedPart`, the part of `spacesAndRegions`
  on the terms whose contraction is sealed with plain runs, at an ambient
  space whose contraction quotes only what was quoted: each variable that a
  right side has beneath a quotation, its left side has beneath a quotation
  (`QuotesOnlyQuoted`).  The plain spaces, the space of a table among them,
  are such spaces (`quotesOnlyQuoted_of_plainSpace`).

"Tables" are the tables of first-order rules whose right sides mention only
variables of their left sides.

| | a run at the root | `allHeaded` | assembled, all terms | assembled, sealed terms |
|---|---|---|---|---|
| **class hosted, on terms** | every table, a term read as the run of its atom in the space of the table (`atomsReduceProbe_hosts_firstOrderTabular`) | the tables without a variable as a left side: at the space of the table (`allHeaded_hostOf_tabularAt`), and in runs at every ambient space (`allHeaded_hostOf_tabular_inRuns`); a variable as a left side is lost (`allHeaded_variableRule_not_preserved`) | the same (`spacesAndRegions_hostOf_tabularAt`, `spacesAndRegions_hostOf_tabular_inRuns`, `spacesAndRegions_runVariable_normal`) | the same: at the space of the table (`sealedPart_hostOf_tabularAt`), and in runs at every ambient space whose contraction quotes only what was quoted (`sealedPart_hostOf_tabular_inRuns`) |
| **class hosted, with contexts** | the pure calculus on the terms with free variables below a width (`atomRegions_hostOf_scoped`); for a table no reading with one run in the image of each term is hosting (`not_hosting_of_singleRun`), and whether another reading is, is open | those tables, on the terms with free variables below a width, at the space of the table (`allHeaded_hostOf_scopedTabularAt`) | the same (`spacesAndRegions_hostOf_scopedTabularAt`) | the same, in the reading of the sealed part (`sealedPart_hostOf_scopedTabularAt`): each context out of which the image of a context of terms is made keeps sealing (`placedHole_keeps`, `applicationContext_keeps`, `binderContext_keeps`) |
| **statics** | quotation and dropping (`atomsReduce_quoteDropOnly`) | quotation and dropping (`allHeaded_quoteDropOnly`) | quotation and dropping (`spacesAndRegions_quoteDropOnly`, `spacesAndRegions_quoteDropSorted`) | the same equivalence between sealed terms; equal terms are sealed together (`sealedTerm_of_related`); at the stages without a name and the types whose binders bind no name a term is sealed exactly when it is sealed as it is written (`sealedTerm_iff_sealedAsWritten`), and those are the terms of the reflective carrier of the pattern syntax whose runs have plain spaces (`sealedTerm_iff_reflective`); where a name is a variable a sealed term need not be sealed as it is written (`sealedTerm_not_literal`) |
| **evaluator** | the matching evaluator, fixed (`evaluator_fixed`) | the evaluator of a region, unchanged and weak (`allHeaded_weak_contained_static`); a family indexed by the ambient space (`allHeadedMember`) | the same (`spacesAndRegions_weak`, `spacesAndRegionsMember`) | the same evaluator, at the ambient spaces whose contraction quotes only what was quoted (`sealedTerm_of_termStep`, `spacesAndRegions_step_sealedUpToStatics`); at the space of the rule `$0 ⟶ *@$0`, whose right side has its variable beneath a quotation and whose left side has it outside every quotation, the sealed terms are not closed under transitions (`not_quotesOnlyQuoted_quotingSpace`, `sealedTerm_not_kept_at_quotingSpace`) |
| **a part in another space** | a run computes by the rules of its space (`run_step_iff`); two runs in one application step each by itself (`atomsReduce_pair_step_iff`) | at every ambient space the steps of a run are the runs of the steps of its subject in the member at its space (`allHeaded_run_step_iff`); two runs (`allHeaded_pair_step_iff`); a run in a run (`allHeaded_nested_step_iff`) | the same (`spacesAndRegions_run_step_iff`, `spacesAndRegions_pair_step_iff`, `spacesAndRegions_nested_step_iff`); a tree of any finite number of runs (`spacesAndRegions_tree_step_iff`); on terms (`spacesAndRegions_run_termStep_iff`, `spacesAndRegions_nested_termStep_iff`, `spacesAndRegions_tree_termStep_iff`) | a run is in the part exactly when the contraction of its space is plain and its atom is in the part (`sealedTerm_run_iff`); containment inside the part (`sealedPart_run_termStep_iff`) |
| **a space steps** | no (`space_static`) | no, and no name (`allHeaded_space_static`, `allHeaded_name_static`) | no, and no name (`spacesAndRegions_space_static`, `spacesAndRegions_name_static`) | no (`sealedPart_space_static`) |
| **root steps** | none of an atom outside a run; the root step of a run is written, with a variable as its subject (`atomsReduce_rewrites`) | written by hand, eight and eight (`allHeaded_rewrites`); a constructor of atoms added later has no step (`writtenWithPair_pair_normal`, `writtenWithPair_runPair_normal`) | generated from the constructors (`spacesAndRegions_rewrites`, `generatedRoots_written`); they cover every constructor of atoms of every list (`assembledOver_root_step`, `assembledOver_runRoot_step`, `generatedWithPair_pair_steps`) | those of the candidate; an answer of a space that quotes only what was quoted, for a sealed subject, is sealed (`QuotesOnlyQuoted.sealed_of_mem_matchResults`): a match rebuilds its subject, so what a left side finds beneath a quotation is closed (`uses_sealed_of_instance`) |
| **stored programs and MM0** | the run of a call reaches the run of the engine's value (`Stores.run_reaches`, `Stores.run_reaches_iff`); MM0 (`check_run_iff_derives`, `admission_run_iff`, `verification_run_iff`); one development replayed (`admission_instance_replays`) | those of the next column, which are statements of `allHeaded` by `spacesAndRegions_eq_allHeaded` | the plain atom of a call at the space of the table (`callAtom_reaches_iff`) and its run at every ambient space (`callRegion_reaches_iff`); MM0 in both forms (`check_atom_iff_derives`, `check_region_iff_derives`, `admission_atom_iff`, `admission_region_iff`, `verification_atom_iff`, `verification_region_iff`); one development replayed (`admission_instance_atom`, `admission_instance_region`) | the same statements inside the part (`sealedPart_callAtom_reaches_iff`, `sealedPart_callRegion_reaches_iff`, `sealedPart_check_iff_derives`, `sealedPart_admission_iff`, `sealedPart_verification_iff`), by `sealedPart_reaches_iff` |
| **substitution into a quotation** | beta substitutes beneath a quotation (`substitution_enters_quotation`) | as the next column | beta substitutes beneath a quotation: the plain reading of `((lam x *@(f x)) payload)` reaches `(f payload)` (`quotedUseProgram_plain_reaches`, `quotation_changed_when_not_sealed`) | none: a beta step changes no quotation (`beta_keeps_quotations`, `instantiateBVarAt_quoted_of_sealed`); the sealing reading of that program reaches `(f x)` (`quotedUseProgram_sealing_reaches`) and, at the empty ambient space, only terms of four classes and not `(f payload)`, whatever spelling a transition takes (`quotedUseProgram_sealing_reducts_on_terms`, `quotedUseProgram_sealing_not_plainResult_on_terms`) |

Beside the table:

* the part is a part of the theory with the contexts that keep sealing, and
  its inclusion is a hosting map (`sealedInclusion_hosting`);
* the step of a dropped quotation to itself is a transition of the part, and
  the part has no rank (`sealedPart_droppedQuotation_self`,
  `sealedPart_not_rank`);
* one induction over the thirty-three rewrites serves every property that the
  operations of a step keep (`OperationInvariant.stepAt`): sealing
  (`spacesAndRegions_step_sealed`), sealing up to the static equivalence
  (`spacesAndRegions_step_sealedUpToStatics`), and a count of constructors
  that is zero (`spacesAndRegions_stepAt_tokens`);
* the runs of a sealed term have plain spaces, and a condition on them is
  needed: at the empty ambient space a sealed abstraction with a run in the
  space of the rule `$0 ⟶ *@$0` steps to one that is not sealed
  (`quotingRun_unseals`).

The one open cell, as a goal.  For a table `table` of first-order rules with
bound right sides and a class `declared` of interfaces in which the holes of
atoms are free, it is not known whether

    HostOf (atomsReduceTheory.regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting

holds or fails.  What is known is that a map which reads every term with one
run is not hosting (`not_hosting_of_singleRun`).

This module adds the two cells that had no theorem:
`atomsReduce_pair_step_iff` and `sealedPart_space_static`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (termSetoid TermStep)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.PrimeCandidate (contract runPattern runRewrite)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (atomsReduce atomsReduce_rewrites beta_inv appFunction_inv appArgument_inv step_appFunction
    step_appArgument exists_rule_of_stepAt releaseRule runSubjectRule runAppFunctionRule
    runAppArgumentRule runPiDomainRule runPiBodyRule runLamDomainRule runLamBodyRule)
open Mettapedia.Logic.HostingStyles.AmbientRegions (apply_not_matched)

/-! ## Two runs in one application, in the candidate with a run at the root -/

/-- **Two runs in one application, in the candidate with a run at the root**:
under every evaluator, a step of the application of two runs is a step of one
of the two runs.  That candidate has no root step of an application, so
nothing is asked about the application as a whole. -/
theorem atomsReduce_pair_step_iff {base : BasePremiseEvaluator}
    {first second function argument target : Pattern} :
    Step base atomsReduce (.apply "App" [runPattern first function, runPattern second argument])
        target ↔
      (∃ next, Step base atomsReduce (runPattern first function) next ∧
        target = .apply "App" [next, runPattern second argument]) ∨
      ∃ next, Step base atomsReduce (runPattern second argument) next ∧
        target = .apply "App" [runPattern first function, next] := by
  constructor
  · rintro ⟨fuel, step⟩
    cases fuel with
    | zero => cases step
    | succ fuel =>
        obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
        rw [atomsReduce_rewrites] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, value, shape, -⟩ := beta_inv matched premises
          simp [runPattern] at shape
        · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
            appFunction_inv matched premises
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
          obtain ⟨rfl, rfl⟩ := shape
          exact .inl ⟨moved, ⟨fuel, inner⟩, applied⟩
        · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
            appArgument_inv matched premises
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
          obtain ⟨rfl, rfl⟩ := shape
          exact .inr ⟨moved, ⟨fuel, inner⟩, applied⟩
        · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
        · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-drop") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · exact absurd matched
            (apply_not_matched (label := "prime-run") (other := "App") (by decide))
  · rintro (⟨next, ⟨fuel, step⟩, rfl⟩ | ⟨next, ⟨fuel, step⟩, rfl⟩)
    · exact ⟨fuel + 1, step_appFunction (by simp [atomsReduce_rewrites]) _ step⟩
    · exact ⟨fuel + 1, step_appArgument (by simp [atomsReduce_rewrites]) _ step⟩

/-! ## No space steps in the sealed part -/

/-- **No space has a transition in the sealed part**, at every stage: a
transition of the part is a transition of the candidate. -/
theorem sealedPart_space_static (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) {stage : List TypeExpr}
    (term next : (sealedPart admits ambientSpace safe).Term ⟨.base "Space", stage⟩) :
    ¬ (sealedPart admits ambientSpace safe).rewrites term next :=
  fun step => spacesAndRegions_space_static term.1 next.1 step

#print axioms atomsReduce_pair_step_iff
#print axioms sealedPart_space_static

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
