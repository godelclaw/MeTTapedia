import Mettapedia.Logic.HostingStyles.AtomsReduce.Defects
import Mettapedia.Logic.HostingStyles.AtomsReduce.ScopedContexts
import Mettapedia.Logic.HostingStyles.AtomsReduce.FreeRightSide

/-!
# The candidate in which atoms reduce, beside the four presented candidates

`atomsReduceProbe` is the presentation `atomsReduce` under the matching
evaluator.  The four earlier candidates are `matchingProbe`, `turingProbe`,
`lambdaPiProbe` and `combinedProbe`.

| | `matchingProbe` | `turingProbe` | `lambdaPiProbe` | `combinedProbe` | `atomsReduceProbe` |
|---|---|---|---|---|---|
| what reduces | a process, which no constructor takes | a process, and the bag of a machine in sorts of its own | a process, and a term of the calculus in sorts of its own | as the first and the third | an atom, which the constructors of expressions take (`separateSort_absent`) |
| class hosted on terms | instances **at the root** of first-order rule tables stored in the space, no beta (`matchingProbe_hosts_firstOrderInstances`) | Turing machines, the table in the term (`turingProbe_hosts_machines`) | one theory, its rules in the presentation, with beta and steps at every position (`lambdaPiProbe_hosts_scopes`) | both classes (`combinedProbe_hosts_both`) | the theories given by a table of rules without binder whose right sides mention only variables of their left sides, the table stored in the space, **with beta and with steps at every position**, on all terms (`atomsReduceProbe_hosts_firstOrderTabular`); the pure calculus under every evaluator (`pure_hostedBy_everyEvaluator`) |
| with contexts, linear | no theory given by a table (`spacePresentation_not_hostOf_tabular_contexts`) | not examined: it has bags | no theory given by a table (`QuoteDropOnly.not_hostOf_tabular_contexts`) | no theory given by a table (`combinedProbe_not_hosts_tabular_contexts`) | no map at all from a theory of the λΠ-calculus modulo (`atomsReduce_isEmpty_contextMap`) |
| with contexts, names and spaces free, what reduces used once | no hosting map (`spaceReading_not_hosting`) | not examined | not examined | not examined | no map preserves transitions (`dataRegions_not_preserves`) |
| with contexts, what reduces free (atoms free, or cartesian) | no hosting map from a theory of the λΠ-calculus modulo, under any reading and any evaluator (`spaceReading_not_hosting`) | not examined | not examined | not examined | **hosted**, under every evaluator: the pure calculus on the terms with free variables below a width, for every width, with all the contexts of those terms (`atomRegions_hostOf_scoped`, `cartesian_hostOf_scoped`).  A theory given by a table: no reading with one run in the image of each term is hosting (`not_hosting_of_singleRun`); whether another reading is, is not settled |
| assumed of the evaluator | it is the matching evaluator | nothing | nothing | the matching evaluator, for the first class | it is the matching evaluator, for the rules of a table (`evaluator_fixed`); nothing, for beta (`pure_hostedBy_everyEvaluator`) |
| steps per source step | one | one | one | one | one (`tableMap_steps`) |
| not hosted | every theory of the λΠ-calculus modulo on terms (`matchingProbe_not_hosts_tabular`) | not settled | on terms, a theory other than its own: not settled | not settled beyond its two classes | by the reading of terms as runs: a rule whose right side binds (`bindingRule_not_preserved`), a rule whose right side has a variable that its left side does not bind (`freeRule_not_preserved`); by the reading of terms as atoms: all terms at once with their contexts (`atomReading_not_contextMap`) |

On terms the candidate hosts a class that the matching probe does not
(`atomsReduce_separates_from_matching`).  With contexts the two are apart on
one source: the closed terms of the pure calculus, with all their contexts,
are hosted by the cartesian reading of the candidate and by no reading of the
presentation of the matching probe (`closedPure_separates_with_contexts`,
`spaceReading_not_hosting_closed`).  The candidate has no rank
(`atomsReduce_not_rank`), also by the release of a dropped quotation alone
and under every evaluator (`release_not_rank`).

The rows of the candidate are also two theorems: `atomsReduce_terms_row` and
`atomsReduce_contexts_row`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## Beside the matching probe, on terms -/

/-- **The matching probe hosts none of the theories that the candidate hosts
on terms**: each of them is a theory of the λΠ-calculus modulo, with beta and
with steps beneath the root. -/
theorem matchingProbe_hosts_no_firstOrderTabular {source : ContextTheory.{0}}
    (member : FirstOrderTabular source) (interface : source.Interface) :
    ¬ HostedBy (source.gslt interface).termsAlone matchingProbe.theory := by
  obtain ⟨theory, table, tabular, -, rfl⟩ := member
  exact matchingCandidate_hosts_no_tabular_terms ⟨theory, table, tabular, rfl⟩ interface

/-- **The candidate in which atoms reduce is a host, on terms, of a class of
which the matching probe is none.** -/
theorem atomsReduce_separates_from_matching :
    atomsReduceProbe.Hosts FirstOrderTabular .terms .hosting ∧
      ¬ matchingProbe.Hosts FirstOrderTabular .terms .hosting :=
  ⟨atomsReduceProbe_hosts_firstOrderTabular, fun hosts =>
    matchingProbe_hosts_no_firstOrderTabular pure_firstOrderTabular ()
      (hosts _ ⟨_, pure_firstOrderTabular, (), rfl⟩)⟩

/-! ## The matching probe, under every reading -/

/-- **No reading of the presentation of the matching probe hosts a theory of
the λΠ-calculus modulo with its contexts**, under any evaluator: it reduces
in a sort that no constructor takes, and the image of the context that
applies its first hole to its second can use one of them at most. -/
theorem spaceReading_not_hosting (base : BasePremiseEvaluator)
    (declared : Contexts.Interface → Prop) {theory : Theory}
    (map : ContextMap (rewritingTheory theory)
      ((contextTheory base spacePresentation).regionReading declared)) : ¬ map.Hosting :=
  not_hosting_of_separateSort (presentation := spacePresentation) (active := "Process")
    (show rewritesHeadedIn probeWithSpace ["Process"] = true by decide)
    (show takesNoneOf probeWithSpace "Process" = true by decide)
    (fun related => probeWithSpace_quoteDropOnly.tokens_eq
      (show sortLabels probeWithSpace "Process" "prime-quote" = false by decide)
      (show sortLabels probeWithSpace "Process" "prime-drop" = false by decide) related)
    map (termApplication theory)
    (moving := Dedukti.omega) (next := Dedukti.omega) (still := (.srt .type : LF.Term))
    (other := (.srt .kind : LF.Term)) (Dedukti.omega_step theory)
    (fun same => absurd (show LF.Term.app Dedukti.omega (.srt .type) =
      .app Dedukti.omega (.srt .kind) from same) (by decide))
    (fun same => absurd (show LF.Term.app (.srt .type) Dedukti.omega =
      .app (.srt .kind) Dedukti.omega from same) (by decide))

/-- **Nor the closed terms of the pure calculus with their contexts**: the
same obstruction, at the source that the candidate hosts. -/
theorem spaceReading_not_hosting_closed (base : BasePremiseEvaluator)
    (declared : Contexts.Interface → Prop)
    (map : ContextMap (scopedRewriting 0 Theory.empty)
      ((contextTheory base spacePresentation).regionReading declared)) : ¬ map.Hosting :=
  not_hosting_of_separateSort (presentation := spacePresentation) (active := "Process")
    (show rewritesHeadedIn probeWithSpace ["Process"] = true by decide)
    (show takesNoneOf probeWithSpace "Process" = true by decide)
    (fun related => probeWithSpace_quoteDropOnly.tokens_eq
      (show sortLabels probeWithSpace "Process" "prime-quote" = false by decide)
      (show sortLabels probeWithSpace "Process" "prime-drop" = false by decide) related)
    map closedApplication
    (moving := ⟨Dedukti.omega, omega_closed⟩) (next := ⟨Dedukti.omega, omega_closed⟩)
    (still := ⟨.srt .type, .srt⟩) (other := ⟨.srt .kind, .srt⟩)
    (Dedukti.omega_step Theory.empty)
    (fun same => absurd (show LF.Term.app Dedukti.omega (.srt .type) =
      .app Dedukti.omega (.srt .kind) from congrArg Subtype.val same) (by decide))
    (fun same => absurd (show LF.Term.app (.srt .type) Dedukti.omega =
      .app (.srt .kind) Dedukti.omega from congrArg Subtype.val same) (by decide))

/-- **With contexts, on one source**: the closed terms of the pure calculus
with all their contexts are hosted by the cartesian reading of the candidate,
and not by the cartesian reading of the matching probe. -/
theorem closedPure_separates_with_contexts :
    HostedBy (scopedRewriting 0 Theory.empty) atomsReduceTheory.cartesianReading ∧
      ¬ HostedBy (scopedRewriting 0 Theory.empty) matchingProbe.theory.cartesianReading :=
  ⟨⟨scopedMap matchingEvaluator atomsFree_all 0,
      scopedMap_hosting matchingEvaluator atomsFree_all 0⟩,
    fun ⟨map, hosting⟩ =>
      spaceReading_not_hosting_closed matchingEvaluator (fun _ => True) map hosting⟩

/-! ## The rows of the candidate -/

/-- **On terms**: under the matching evaluator the candidate is a host of
the theories given by a table of first-order rules with bound right sides;
under every evaluator it hosts the pure calculus; and it has no rank. -/
theorem atomsReduce_terms_row :
    atomsReduceProbe.Hosts FirstOrderTabular .terms .hosting ∧
      (∀ base : BasePremiseEvaluator,
        HostedBy ((rewritingTheory Theory.empty).gslt ()).termsAlone (candidateUnder base)) ∧
        IsEmpty atomsReduceTheory.Rank :=
  ⟨atomsReduceProbe_hosts_firstOrderTabular, pure_hostedBy_everyEvaluator, atomsReduce_not_rank⟩

/-- **With contexts**: as it is, the candidate receives no map from a theory
of the λΠ-calculus modulo; with names and spaces free and atoms used once no
map preserves transitions; with atoms free, and with every hole free, it
hosts the pure calculus on the terms with free variables below a width, for
every width, with all the contexts of those terms. -/
theorem atomsReduce_contexts_row :
    (∀ theory : Theory, IsEmpty (ContextMap (rewritingTheory theory) atomsReduceTheory)) ∧
      (∀ (theory : Theory) (map : ContextMap (rewritingTheory theory) dataRegions),
        ¬ map.PreservesTransitions) ∧
        HostOf atomRegions
          (fun source => ∃ width : Nat, source = scopedRewriting width Theory.empty)
          .contexts .hosting ∧
          HostOf atomsReduceTheory.cartesianReading
            (fun source => ∃ width : Nat, source = scopedRewriting width Theory.empty)
            .contexts .hosting :=
  ⟨atomsReduce_isEmpty_contextMap matchingEvaluator, dataRegions_not_preserves,
    atomRegions_hostOf_scoped, cartesian_hostOf_scoped⟩

#print axioms matchingProbe_hosts_no_firstOrderTabular
#print axioms atomsReduce_separates_from_matching
#print axioms spaceReading_not_hosting
#print axioms spaceReading_not_hosting_closed
#print axioms closedPure_separates_with_contexts
#print axioms atomsReduce_terms_row
#print axioms atomsReduce_contexts_row

end Mettapedia.Logic.HostingStyles.AtomsReduce
