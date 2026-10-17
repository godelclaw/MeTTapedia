import Mettapedia.Logic.HostingStyles.LocatedAtoms.FreeRightSide
import Mettapedia.Logic.HostingStyles.AmbientSpace.RulesFromSpace
import Mettapedia.Logic.HostingStyles.AmbientSpace.ChangedSpace
import Mettapedia.Logic.HostingStyles.AmbientSpace.RootSubject

/-!
# Three candidates: the space in a run at the root, outside the term, and at the leaves

One sentence measures the three: `HostOf candidate sources level demand`,
with the sources the theories given by a table of rules without binder whose
right sides mention only variables of their left sides (`FirstOrderTabular`
on terms, `ScopedFirstOrderTabular` with contexts).

| | run at the root (`atomsReduceProbe`) | ambient family (`ambientMember`, `ambientSum`) | located atoms (`locatedProbe`) |
|---|---|---|---|
| where the space is | in one run at the root of a term | the index of a family of evaluators, in no term (`space_taken_by_no_atom`) | in runs that the equations move between the root and the leaves (`Law`) |
| class hosted on terms | `FirstOrderTabular`, by the one candidate (`atomsReduce_hostOf_firstOrderTabular`) | each member, the theories of its table (`member_hostOf_tabularAt`); the sum, `FirstOrderTabular` (`ambientSum_hostOf_firstOrderTabular`) | `FirstOrderTabular`, by the one candidate (`located_hostOf_firstOrderTabular`) |
| with contexts, each hole used once | no map (`atomsReduce_isEmpty_contextMap`) | no map (`ambientMember_isEmpty_contextMap_scoped`, `linearSum_isEmpty_contextMap_scoped`) | no map (`located_isEmpty_contextMap_scoped`) |
| with contexts, the holes of atoms free | the pure calculus (`atomsFree_hostOf_scoped`); for a table, no reading with one run in each image is hosting (`not_hosting_of_singleRun`, `singleRun_not_hosting_scoped`) | hosted: each member, the theories of its table at every width (`member_hostOf_scopedTabularAt`); the sum, `ScopedFirstOrderTabular` (`ambientSum_hostOf_scopedFirstOrderTabular`) | hosted: `ScopedFirstOrderTabular`, by the one candidate (`located_hostOf_scopedFirstOrderTabular`); the image of a context is its pattern with its leaves located, and its plain pattern is refuted (`plainPattern_not_equivariant`) |
| assumed of the evaluator | it is the matching evaluator, which respects the statics and takes its rules from the space of the run (`evaluator_fixed`) | the member at a space is the matching evaluator with the space fixed (`matchingEvaluator_run_eq_ambient`); each member respects the statics (`ambient_respectsStatics`); the family takes its rules from the space (`ambientEvaluator_rulesFromSpace`, negative `listedFamily_not_rulesFromSpace`) | it is the evaluator that reads the normal form, which respects the statics (`locatedEvaluator_respectsStatics`); the matching evaluator does not (`matchingEvaluator_not_respectsStatics`) and lets a rule of another space fire (`matching_foreign_step`); the rules come from the space in which the subject is located (`locatedAnswers_of_stores_nothing`), not from the space of the run premise (`locatedEvaluator_not_rulesFromSpace`) |
| the static equivalence | quotation and dropping (`atomsReduce_quoteDropOnly`); the run of a term is alone in its class (`eq_of_related_of_dropFree`) | quotation and dropping (`ambient_quoteDropOnly`); the atom of a term is alone in its class (`eq_atomTerm_of_related`) | five laws (`located_generator`, `Law.equiv`), not quotation and dropping alone (`located_not_quoteDropOnly`); a normal form constant on classes (`settle_eq_of_related`) that decides the class of the run of an atom (`related_runAtom_iff`); the run of a term is not alone (`run_not_alone`), its class is its spellings (`spells_of_settle`, `spelled_related`); the normal form of a term need not be a term (`settle_not_term`); the equations with a binder capture (`binder_captures`); no linear size (`located_no_linearSize`) |
| steps per source step | one (`tableMap_steps`) | one (`memberMap_steps`) | one transition (`locatedTermsMap_steps`) |
| a part in another space | no: the run is one node at the root | no: a term of the sum sits in one space (`ambientSum_isEmpty_context_of_ne`) | yes, and each part steps by the rules of its own space only (`pair_termStep_inv`); such a term is the image of no atom of a member (`mixedCoins_in_no_member`) |
| not hosted | a right side that binds (`bindingRule_not_preserved`); a right side with a variable that the left side does not bind (`freeRule_not_preserved`); all terms at once with their contexts (`atomReading_not_contextMap`) | the same three (`ambient_bindingRule_not_preserved`, `ambient_freeRule_not_preserved`, `ambient_atomReading_not_contextMap`); and a space has a transition (`ambient_space_steps`) | a right side that binds (`located_bindingRule_not_preserved`); a right side with a variable that the left side does not bind (`located_freeRule_not_preserved`); all terms at once with their contexts: open |
| between the forms | | a member into the run at the root: hosting on terms (`placeInRun_hosting`), not with contexts (`placeInRun_not_hosting_with_contexts`); one more atom in the space keeps every step and adds some (`addedSpace_steps`, `enlargeMap_not_hosting`) | the members into located atoms (`compareMap`): no two atoms identified (`compareMap_reflectsEquations`), transitions preserved and reflected on the image of a table (`compare_step_iff`), not hosting under the matching evaluator (`compareMap_matching_not_hosting`) |

The cells that are open, with their goals:

* located atoms, all terms at once: for every width and every
  `map : ContextMap (rewritingTheory theory) (locatedTheory.regionReading declared)`,
  `(∀ term, (map.term term).1 = runPattern (ruleSpace rules) (atomAt width term)) → False`;
* located atoms, the normal form on all terms: for two terms `first` and
  `second` of one interface, `settle first.1 = settle second.1 →
  (termSetoid base located interface).r first second`;
* the comparison on all atoms of all members: for every space and atoms
  `atom`, `next` of the member, `(ambientTheory space).rewrites atom next →
  TermStep locatedEvaluator located (locatedOf space atom) (locatedOf space next)`,
  and for every `target`, `TermStep locatedEvaluator located (locatedOf space atom) target →
  ∃ next, (ambientTheory space).rewrites atom next ∧
    (termSetoid locatedEvaluator located closedAtom).r target (locatedOf space next)`.

The rows are also theorems: `terms_row`, `linear_row`, `contexts_row`,
`evaluator_row`, `statics_row`, `otherSpace_row`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory withChoice chooseLeft chooseRight)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (ambient SpaceTerm ambientTheory ambientEvaluator ambientSum ScopedFirstOrderTabular coin
    FamilyRulesFromSpace)

/-- **On terms**: each of the three is a host of the theories given by a
table of first-order rules with bound right sides; the ambient form as the
sum of its members, under every reading, and the located form under every
reading. -/
theorem terms_row :
    HostOf atomsReduceTheory FirstOrderTabular .terms .hosting ∧
      (∀ regions : Contexts.Interface → Prop,
        HostOf (ambientSum regions) FirstOrderTabular .terms .hosting) ∧
        ∀ regions : Contexts.Interface → Prop,
          HostOf (locatedTheory.regionReading regions) FirstOrderTabular .terms .hosting :=
  ⟨atomsReduce_hostOf_firstOrderTabular, AmbientSpace.ambientSum_hostOf_firstOrderTabular,
    located_hostOf_firstOrderTabular⟩

/-- **With contexts, each hole used once**: none of the three receives a map
from a theory of the λΠ-calculus modulo with its contexts. -/
theorem linear_row (width : Nat) (theory : Theory) :
    IsEmpty (ContextMap (rewritingTheory theory) atomsReduceTheory) ∧
      IsEmpty (ContextMap (scopedRewriting width theory)
        (ContextTheory.sum fun space : SpaceTerm => ambientTheory space)) ∧
        IsEmpty (ContextMap (scopedRewriting width theory) locatedTheory) :=
  ⟨atomsReduce_isEmpty_contextMap matchingEvaluator theory,
    AmbientSpace.linearSum_isEmpty_contextMap_scoped width theory,
    located_isEmpty_contextMap_scoped locatedEvaluator width theory⟩

/-- **With contexts, the holes of atoms free**: for a table, no reading of
the run at the root with one run in each image is hosting; the ambient sum
and the located form are hosts of the theories given by a table on the terms
with free variables below a width, for every table and every width. -/
theorem contexts_row {declared : Contexts.Interface → Prop} (free : AtomsFree declared) :
    (∀ {theory : Theory}
        (map : ContextMap (rewritingTheory theory) (atomsReduceTheory.regionReading declared)),
        (∀ term : (rewritingTheory theory).Term (), tokens runLabel (map.term term).1 = 1) →
          ¬ map.Hosting) ∧
      HostOf (ambientSum declared) ScopedFirstOrderTabular .contexts .hosting ∧
        HostOf (locatedTheory.regionReading declared) ScopedFirstOrderTabular .contexts
          .hosting :=
  ⟨fun map single => not_hosting_of_singleRun map single,
    AmbientSpace.ambientSum_hostOf_scopedFirstOrderTabular free,
    located_hostOf_scopedFirstOrderTabular free⟩

/-- **The evaluators**: the matching evaluator respects the statics of the
run at the root and takes its rules from the space of the run; every member
of the ambient family respects the statics, and the family takes its rules
from the space; the evaluator of located atoms respects the statics, does not
take its rules from the space of the run premise, and the matching evaluator
does not respect the statics of located atoms. -/
theorem evaluator_row :
    (RespectsStatics matchingEvaluator atomsReduce ∧ RulesFromSpace matchingEvaluator) ∧
      ((∀ space : Pattern, RespectsStatics (ambientEvaluator space) ambient) ∧
        FamilyRulesFromSpace ambientEvaluator) ∧
        (RespectsStatics locatedEvaluator located ∧ ¬ RulesFromSpace locatedEvaluator ∧
          ¬ RespectsStatics matchingEvaluator located) :=
  ⟨⟨atomsReduce_respectsStatics, matchingEvaluator_rulesFromSpace⟩,
    ⟨AmbientSpace.ambient_respectsStatics, AmbientSpace.ambientEvaluator_rulesFromSpace⟩,
    ⟨locatedEvaluator_respectsStatics, locatedEvaluator_not_rulesFromSpace,
      matchingEvaluator_not_respectsStatics⟩⟩

/-- **The static equivalences**: quotation and dropping alone in the first
two; not in the third, which has no linear size and in which the run of an
application and the application of the runs are two terms of one class. -/
theorem statics_row :
    QuoteDropOnly atomsReduce ∧ QuoteDropOnly ambient ∧
      (¬ QuoteDropOnly located ∧ IsEmpty locatedTheory.LinearSize ∧
        (termSetoid locatedEvaluator located AtomsReduce.closedAtom).r runOfApplication
          applicationOfRuns ∧ runOfApplication ≠ applicationOfRuns) :=
  ⟨atomsReduce_quoteDropOnly, AmbientSpace.ambient_quoteDropOnly, located_not_quoteDropOnly,
    located_no_linearSize locatedEvaluator, (run_not_alone locatedEvaluator).1,
    (run_not_alone locatedEvaluator).2⟩

/-- **A part in another space**: a term of the ambient sum sits in one space;
in the located form the application of a run in the space of the rules of
choice to a run in the empty space is a term, its function steps, every
transition of it is a step of its function, and it is the image of no atom of
a member. -/
theorem otherSpace_row :
    (∀ {declared : Contexts.Interface → Prop} {first second : SpaceTerm}, first ≠ second →
        ∀ source target : Contexts.Interface,
          IsEmpty ((ambientSum declared).Context
            (fun _ : Unit => (⟨first, source⟩ : (ambientSum declared).Interface))
            ⟨second, target⟩)) ∧
      TermStep locatedEvaluator located mixedCoins
        (appTerm (runAtom [chooseLeft, chooseRight] 0 (.con "heads")) (runAtom [] 0 coin)) ∧
        (∀ target : Contexts.Term located AtomsReduce.closedAtom,
          TermStep locatedEvaluator located mixedCoins target →
            ∃ next, Dedukti.Step (withChoice Theory.empty) coin next ∧
              (termSetoid locatedEvaluator located AtomsReduce.closedAtom).r target
                (appTerm (runAtom [chooseLeft, chooseRight] 0 next) (runAtom [] 0 coin))) ∧
          ∀ (space : SpaceTerm) (atom : Contexts.Term ambient AtomsReduce.closedAtom),
            ¬ (termSetoid locatedEvaluator located AtomsReduce.closedAtom).r
              (locatedOf space atom) mixedCoins :=
  ⟨fun apart source target => AmbientSpace.ambientSum_isEmpty_context_of_ne apart source target,
    mixedCoins_function_steps, fun _ step => mixedCoins_argument_still step,
    mixedCoins_in_no_member locatedEvaluator⟩

#print axioms terms_row
#print axioms linear_row
#print axioms contexts_row
#print axioms evaluator_row
#print axioms statics_row
#print axioms otherSpace_row

end Mettapedia.Logic.HostingStyles.LocatedAtoms
