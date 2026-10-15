import Mettapedia.Logic.HostingStyles.PrimeCandidate.CombinedCandidate
import Mettapedia.Logic.HostingStyles.PrimeCandidate.TuringUnion

/-!
# The hosting sentence, with the evaluator named

`HostOf candidate sources level demand` takes a theory as its candidate.  For
a presented candidate the theory is generated from a presentation and an
evaluator of its premises, and what it hosts on terms can be all in the
evaluator.  A `PresentedCandidate` names both, and asks that the evaluator
respect the static equivalence of the presentation; its sentence is
`PresentedCandidate.Hosts`.

## Four candidates

One candidate hosts through its evaluator, which is fixed; two host through
rewrites of their own, and for them the evaluator does not matter; the fourth
has both.

| | a fixed evaluator: `matchingProbe` | own rewrites, the rules in the term: `turingProbe` | own rewrites, the rules in the presentation: `lambdaPiProbe` | both: `combinedProbe` |
|---|---|---|---|---|
| candidate | the probe with a run constructor, a space that is a term and a variable atom, under the matching evaluator | the probe together with the universal Turing theory, under any evaluator that respects the static equivalence | the probe together with the language of one theory of the λΠ-calculus modulo (beta, the congruences, its declared rules), under any evaluator that respects the static equivalence | the first presentation together with the language of one theory of the λΠ-calculus modulo, under the matching evaluator |
| class hosted | the theories of first-order rule instances, the table in the term (`matchingProbe_hosts_firstOrderInstances`); among first-order tables, exactly those whose rules determine their right sides (`instances_hostedBy_matching_iff`) | the Turing machines on their configurations, the table in the term (`turingProbe_hosts_machines`) | the scopes of that one theory: its terms beneath each number of binders, with beta and the steps beneath the root (`lambdaPiProbe_hosts_scopes`) | the theories of first-order rule instances and the scopes of its theory (`combinedProbe_hosts_both`) |
| level | terms | terms | terms | terms |
| assumed of the evaluator | it is the matching evaluator: computable, respects the static equivalence, takes its rules from the space (`matchingEvaluator_rulesFromSpace`) | nothing: the same holds under every evaluator (`turingPresentation_hostOf_machineTheory`) | nothing: the same holds under every evaluator (`CarriesLambdaPi.hostOf_scopes`) | it is the matching evaluator, for the first class; nothing, for the second |
| steps per source step | one (`matchingProbe_steps`) | one (`turing_steps`) | one (`lambdaPi_steps`) | one |
| not hosted | every theory of the λΠ-calculus modulo, on all its terms and on the closed terms of any presentation of it (`matchingProbe_not_hosts_tabular`, `matchingProbe_not_hosts_scopes`): beta and steps beneath the root; one closed first-order rule applied at every position, without beta (`doublingContextual_not_hostedBy_matching`); every theory with a term of infinitely many reducts (`freeInstances_not_hostedBy_matching`); with all contexts, the theories given by a table (`spacePresentation_not_hostOf_tabular_contexts`) | not settled here | with all contexts, the theories given by a table (`QuoteDropOnly.not_hostOf_tabular_contexts`); on terms, a theory other than its own: not settled here | with all contexts, the theories given by a table (`combinedProbe_not_hosts_tabular_contexts`); on terms, a theory other than its own beyond its instances at the root: not settled here |

None of the four has a rank: the first under its evaluator
(`matchingCandidate_not_rank`), the others under every evaluator
(`turingPresentation_not_rank`, `CarriesLambdaPi.not_rank`).

## The negative example

The probe with the run constructor, under the evaluator chosen from the
enumeration of the steps of the rule-table evaluator, is no presented
candidate (`tableRunEvaluator_no_candidate`), and no presented candidate over
that presentation is a host of the theories given by a table
(`runProbe_not_hosts_tabular`).  Respecting the static equivalence does not
by itself exclude an evaluator chosen from the sources: the evaluator of the
tables whose rules determine their right sides respects it
(`determinedRunProbe`), and those are exactly the theories given by a table
that such an evaluator hosts through the run rewrite
(`exists_respecting_hostOf_iff_determinedTabular`).  That evaluator answers
the run premise whatever the space is
(`determinedEvaluator_not_rulesFromSpace`); an evaluator that takes its rules
from the space answers nothing where the space stores no atom
(`RulesFromSpace`), as the matching evaluator does
(`matchingEvaluator_rulesFromSpace`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.TuringMachine (Machine Configuration configurationGSLT)
open Mettapedia.GSLT.Dedukti (Theory)
open Mettapedia.GSLT.Dedukti.Language (Presents)

/-! ## Presented candidates -/

/-- **A presented candidate**: a presentation together with the evaluator of
its premises, which respects its static equivalence. -/
structure PresentedCandidate where
  /-- The presentation. -/
  presentation : ValidatedLanguageDef
  /-- The evaluator of the premises of its rewrites. -/
  evaluator : BasePremiseEvaluator
  respects : RespectsStatics evaluator presentation.language

namespace PresentedCandidate

/-- The theory of a presented candidate, with all its contexts. -/
def theory (candidate : PresentedCandidate) : ContextTheory.{0} :=
  contextTheory candidate.evaluator candidate.presentation

/-- **The hosting sentence, with the evaluator named.** -/
def Hosts (candidate : PresentedCandidate) (sources : ContextTheory.{0} → Prop) (level : Level)
    (demand : Demand) : Prop :=
  HostOf candidate.theory sources level demand

end PresentedCandidate

/-! ## A fixed evaluator: the matching evaluator -/

/-- **The candidate of the route by a fixed evaluator**: the probe with a
run constructor, a space that is a term and a variable atom, under the
matching evaluator. -/
def matchingProbe : PresentedCandidate where
  presentation := spacePresentation
  evaluator := matchingEvaluator
  respects := matchingEvaluator_respectsStatics probeWithSpace_quoteDropOnly probeWithSpace_rewrites

/-- **Positive**: it is a host of the theories of first-order rule
instances, on terms. -/
theorem matchingProbe_hosts_firstOrderInstances :
    matchingProbe.Hosts FirstOrderInstances .terms .hosting :=
  matchingCandidate_hostOf_firstOrderInstances

/-- One step of the source is one step of the candidate. -/
theorem matchingProbe_steps {table : Dedukti.RuleTable}
    (firstOrder : Dedukti.FirstOrderTable table) (bound : BoundTable table) {count : Nat}
    {first final : LF.Term}
    (steps : (instanceTheory table).termsAlone.Steps (interface := PUnit.unit) count first final) :
    matchingProbe.theory.Steps count (runTermOf table.toList first)
      (runTermOf table.toList final) :=
  (matchingMap table).steps_of_preserves (matchingMap_hosting firstOrder bound).preserves steps

/-- **Negative**: it is no host of the theories given by a table, on
terms. -/
theorem matchingProbe_not_hosts_tabular : ¬ matchingProbe.Hosts TabularTheory .terms .hosting :=
  matchingCandidate_not_hostOf_tabular_terms

/-! ## Rewrites of the candidate's own: the universal Turing theory -/

/-- **The candidates of the route by own rewrites**: the probe together
with the universal Turing theory, under an evaluator that respects the static
equivalence. -/
def turingProbe (base : BasePremiseEvaluator) (respects : RespectsStatics base probeWithTuring) :
    PresentedCandidate where
  presentation := turingPresentation
  evaluator := base
  respects := respects

/-- **Positive**: each of them is a host of the Turing machines, on terms,
whatever its evaluator. -/
theorem turingProbe_hosts_machines (candidate : PresentedCandidate)
    (union : candidate.presentation = turingPresentation) :
    candidate.Hosts MachineTheory .terms .hosting := by
  obtain ⟨presentation, evaluator, respects⟩ := candidate
  subst union
  exact turingPresentation_hostOf_machineTheory evaluator

/-- In particular under the evaluator that answers nothing. -/
theorem silentTuringProbe_hosts_machines :
    (turingProbe silentEvaluator (silentEvaluator_respectsStatics _)).Hosts MachineTheory .terms
      .hosting :=
  turingProbe_hosts_machines _ rfl

/-! ## Rewrites of the candidate's own: a theory of the λΠ-calculus modulo -/

/-- **The candidates of the route by own rewrites, with the rules in the
presentation**: the probe together with the language of a theory of the
λΠ-calculus modulo, under an evaluator that respects the static equivalence. -/
def lambdaPiProbe (names : List String) (rules : List Dedukti.RewriteRule)
    (valid : (probeWithLambdaPi names rules).validate = []) (base : BasePremiseEvaluator)
    (respects : RespectsStatics base (probeWithLambdaPi names rules)) : PresentedCandidate where
  presentation := lambdaPiPresentation names rules valid
  evaluator := base
  respects := respects

/-- **Positive**: each of them is a host of the scopes of its theory, on
terms, whatever its evaluator. -/
theorem lambdaPiProbe_hosts_scopes {theory : Theory} {names : List String}
    {rules : List Dedukti.RewriteRule} (presents : Presents theory rules)
    {valid : (probeWithLambdaPi names rules).validate = []} (candidate : PresentedCandidate)
    (union : candidate.presentation = lambdaPiPresentation names rules valid) :
    candidate.Hosts (ScopesOf theory names rules) .terms .hosting := by
  obtain ⟨presentation, evaluator, respects⟩ := candidate
  subst union
  exact (probeWithLambdaPi_carries names rules).hostOf_scopes presents valid evaluator

/-- In particular the probe together with the pure calculus, under the
evaluator that answers nothing: beta, hosted by a rewrite of the candidate. -/
theorem silentPureProbe_hosts_scopes :
    (lambdaPiProbe [] [] pureUnion_validate silentEvaluator
      (silentEvaluator_respectsStatics _)).Hosts (ScopesOf Theory.empty [] []) .terms .hosting :=
  lambdaPiProbe_hosts_scopes pure_presents _ rfl

/-- **Negative**: the candidate of the route by a fixed evaluator is a host
of the scopes of no theory of the λΠ-calculus modulo. -/
theorem matchingProbe_not_hosts_scopes (theory : Theory) (names : List String)
    (rules : List Dedukti.RewriteRule) :
    ¬ matchingProbe.Hosts (ScopesOf theory names rules) .terms .hosting :=
  matchingCandidate_not_hostOf_scopes theory names rules

/-! ## Both in one candidate -/

/-- **One candidate with both**: the probe with a run constructor and a space
that is a term, together with the language of a theory of the λΠ-calculus
modulo, under the matching evaluator. -/
def combinedProbe (names : List String) (rules : List Dedukti.RewriteRule)
    (valid : (spaceWithLambdaPi names rules).validate = []) : PresentedCandidate where
  presentation := ⟨spaceWithLambdaPi names rules, valid⟩
  evaluator := matchingEvaluator
  respects := matchingEvaluator_respectsStatics_spaceWithLambdaPi

/-- **Positive**: it is a host of the theories of first-order rule instances,
by matching against its space, and of the scopes of its theory, by its own
rewrites; both on terms. -/
theorem combinedProbe_hosts_both {theory : Theory} {names : List String}
    {rules : List Dedukti.RewriteRule} (presents : Presents theory rules)
    (valid : (spaceWithLambdaPi names rules).validate = []) :
    (combinedProbe names rules valid).Hosts FirstOrderInstances .terms .hosting ∧
      (combinedProbe names rules valid).Hosts (ScopesOf theory names rules) .terms .hosting :=
  ⟨spaceWithLambdaPi_hostOf_firstOrderInstances presents.leftAlgebraic valid,
    (spaceWithLambdaPi_carries names rules).hostOf_scopes presents valid matchingEvaluator⟩

/-- **Negative**: with all its contexts it is no host of the theories given
by a table. -/
theorem combinedProbe_not_hosts_tabular_contexts (names : List String)
    (rules : List Dedukti.RewriteRule) (valid : (spaceWithLambdaPi names rules).validate = []) :
    ¬ (combinedProbe names rules valid).Hosts TabularTheory .contexts .hosting :=
  QuoteDropOnly.not_hostOf_tabular_contexts ⟨spaceWithLambdaPi names rules, valid⟩
    spaceWithLambdaPi_quoteDropOnly matchingEvaluator

/-! ## The negative example: an evaluator chosen from the sources -/

/-- **The probe with the run constructor under the evaluator that runs the
rule-table evaluator is no presented candidate.** -/
theorem tableRunEvaluator_no_candidate :
    ¬ ∃ candidate : PresentedCandidate,
      candidate.presentation = runPresentation ∧ candidate.evaluator = tableRunEvaluator := by
  rintro ⟨⟨presentation, evaluator, respects⟩, rfl, rfl⟩
  exact tableRunEvaluator_not_respectsStatics respects

/-- **No presented candidate over the probe with the run constructor is a
host of the theories given by a table, on terms.** -/
theorem runProbe_not_hosts_tabular (candidate : PresentedCandidate)
    (run : candidate.presentation = runPresentation) :
    ¬ candidate.Hosts TabularTheory .terms .hosting := by
  obtain ⟨presentation, evaluator, respects⟩ := candidate
  subst run
  exact not_hostOf_tabular_terms_of_respectsStatics respects

/-- The probe with the run constructor under the evaluator of the tables
whose rules determine their right sides: a presented candidate whose
evaluator is chosen from the sources. -/
noncomputable def determinedRunProbe : PresentedCandidate where
  presentation := runPresentation
  evaluator := determinedEvaluator
  respects := determinedEvaluator_respectsStatics

/-- It is a host of those theories: respecting the static equivalence does
not exclude an evaluator chosen from the sources. -/
theorem determinedRunProbe_hosts :
    determinedRunProbe.Hosts DeterminedTabularTheory .terms .hosting :=
  runPresentation_hostOf_determinedTabular_terms

/-- **An evaluator takes its rules from the space**: where the space of the
run premise stores no atom, it answers nothing. -/
def RulesFromSpace (evaluator : BasePremiseEvaluator) : Prop :=
  ∀ (lang : LanguageDef) (bindings : Bindings),
    storedAtoms (contract (applyBindings bindings (.fvar "space"))) = [] →
      evaluator lang bindings runPremise = []

/-- **Positive**: the matching evaluator. -/
theorem matchingEvaluator_rulesFromSpace : RulesFromSpace matchingEvaluator := by
  intro lang bindings empty
  show (matchResults (contract (applyBindings bindings (.fvar "space")))
    (contract (applyBindings bindings (.fvar "subject")))).map _ = []
  rw [matchResults, empty]
  rfl

/-- **Negative**: the evaluator of a listing answers whatever the space is.
Where the listed theory has a step, the evaluator answers at the empty
space. -/
theorem stepEvaluator_not_rulesFromSpace {source : GSLT.{0}} (listing : StepListing source)
    {term reduct : source.Term} (step : source.rewrites term reduct) :
    ¬ RulesFromSpace (stepEvaluator listing.code listing.next) := by
  intro fromSpace
  have silent := fromSpace probeWithSpace
    [("subject", numeral (listing.code term)), ("space", emptySpace)]
    (by
      rw [show applyBindings [("subject", numeral (listing.code term)), ("space", emptySpace)]
        (.fvar "space") = emptySpace by simp [applyBindings]]
      decide)
  have answered : (("answer", numeral (listing.code reduct)) ::
      [("subject", numeral (listing.code term)), ("space", emptySpace)]) ∈
      stepEvaluator listing.code listing.next probeWithSpace
        [("subject", numeral (listing.code term)), ("space", emptySpace)] runPremise := by
    show _ ∈ stepAnswers listing.code listing.next _ (.fvar "subject") "answer"
    rw [stepAnswers_eq listing.injective listing.next "answer" (term := term)
      (by
        rw [show applyBindings [("subject", numeral (listing.code term)), ("space", emptySpace)]
          (.fvar "subject") = numeral (listing.code term) by simp [applyBindings],
          contract_numeral])]
    exact List.mem_map.mpr ⟨reduct, (listing.branches term reduct).mp step, rfl⟩
  rw [silent] at answered
  cases answered

/-- **The evaluator of the tables whose rules determine their right sides
does not take its rules from the space**: it respects the static equivalence
and is chosen from the sources. -/
theorem determinedEvaluator_not_rulesFromSpace : ¬ RulesFromSpace determinedEvaluator :=
  stepEvaluator_not_rulesFromSpace (unionListing determinedListing)
    (term := ⟨0, selfIdentity⟩) (reduct := ⟨0, identityTerm⟩)
    (UnionStep.member (selfIdentity_step _))

#print axioms matchingProbe
#print axioms matchingProbe_hosts_firstOrderInstances
#print axioms matchingProbe_steps
#print axioms matchingProbe_not_hosts_tabular
#print axioms turingProbe_hosts_machines
#print axioms silentTuringProbe_hosts_machines
#print axioms lambdaPiProbe_hosts_scopes
#print axioms silentPureProbe_hosts_scopes
#print axioms matchingProbe_not_hosts_scopes
#print axioms combinedProbe_hosts_both
#print axioms combinedProbe_not_hosts_tabular_contexts
#print axioms tableRunEvaluator_no_candidate
#print axioms runProbe_not_hosts_tabular
#print axioms determinedRunProbe_hosts
#print axioms matchingEvaluator_rulesFromSpace
#print axioms stepEvaluator_not_rulesFromSpace
#print axioms determinedEvaluator_not_rulesFromSpace

end Mettapedia.Logic.HostingStyles.PrimeCandidate
