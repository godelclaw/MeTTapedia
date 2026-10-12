import Mettapedia.Logic.HostingStyles.TopDegreeAnchors
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ChoiceExtension
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ProbeData
import Mettapedia.Logic.HostingStyles.PrimeCandidate.KernelReading
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ProofCodes

/-!
# A candidate as a host: one sentence, and its first instances

`HostOf candidate sources level demand` says that a candidate theory is a
host of a class of theories.  It has the three parameters of a hosting
statement:

* the **class** of sources;
* the **level** (`Level`): the sources with all their contexts, or by their
  terms alone;
* the **demand** (`Demand`): hosting, or hosting and exhausting.

At the level of contexts and for hosting it is the existing `HostsEvery`
(`hostOf_contexts_hosting_iff`).  Hosting with all contexts implies hosting
on terms (`HostOf.terms`); the converse fails (`guestKernel_terms_not_contexts`).

## The existing candidate, in two readings

* (P) `presentedReading base`: the contexts of the presented candidate, for
  an evaluator of its premises;
* (K) `kernelReading model`: the kernel assembled over a model, given by its
  terms alone.

| | (P) | (K) |
|---|---|---|
| the rule-table evaluator, with all contexts | no map at all: `presented_isEmpty_contextMap_tableEvaluator` | no map at all: `kernel_isEmpty_contextMap_tableEvaluator` |
| theories given by a table, on terms | refuted, at single steps and at nonempty reductions: `presented_not_hostOf_tabular_terms`, `presented_not_simulates_tableEvaluator` | refuted for the query-first models and for every model whose base has a rank: `queryFirstKernel_not_hostOf_tabular_terms`, `kernel_not_hostOf_tabular_terms_of_baseRank`; proved for a model that carries the evaluator beside its base: `guestKernel_hostOf_tabular_terms` |
| the framework with rules as constants, with all contexts | no map at all: `presented_isEmpty_contextMap_framework` | no map at all: `kernel_isEmpty_contextMap_framework` |
| numbered proof systems, on terms | proved: `presented_hostOf_numberedProofSystem_terms` | proved: `kernel_hostOf_numberedProofSystem_terms` |
| the framework over a countable signature, on terms, at every type | proved: `presented_hostOf_countableFramework_terms` | proved: `kernel_hostOf_countableFramework_terms` |
| exhausting | not onto the atoms (`presentedAtoms_not_exhausting`); onto the region of the image (`hostsExhaustively_imageRegion`) | not onto the kernel (`kernelNumerals_not_exhausting`, `guestMap_not_exhausting`); onto the region of the image |

The extension of the probe with choice changes none of the refutations
(`choice_isEmpty_contextMap_tableEvaluator`, `choice_not_hostOf_tabular_terms`).
The extension with a run constructor and one rewrite whose premise is
delegated changes the second row, and how it changes it depends on the
evaluator of the premises: see `RunExtension`, `DeterminedTables` and
`SpellingEvaluator`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti
  (Theory rewritingTheory tableEvaluator Tabled TermContext loadMap loadMap_hosting empty_tabular
    omega_step tableEvaluator_cycle)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef (language queryFirstCandidatePresentation)
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language (Model QueryFirstModel kernelGSLT)
open Framework

/-! ## The sentence -/

/-- **How much of its sources a hosting statement keeps.** -/
inductive Level where
  /-- Each source with all its contexts. -/
  | contexts
  /-- Each source by the terms of each of its interfaces: the hole is the
  only observer. -/
  | terms

/-- **What is asked of the map into the candidate.** -/
inductive Demand where
  /-- No distinction of the source is lost. -/
  | hosting
  /-- No distinction is lost, and the candidate adds nothing between the
  images. -/
  | exhausting

/-- The readings of a class of theories at a level. -/
def Level.readings (level : Level) (sources : ContextTheory.{0} → Prop)
    (reading : ContextTheory.{0}) : Prop :=
  match level with
  | .contexts => sources reading
  | .terms => ∃ source, sources source ∧
      ∃ interface : source.Interface, reading = (source.gslt interface).termsAlone

/-- What a demand asks of a candidate for one theory. -/
def Demand.Met (demand : Demand) (candidate reading : ContextTheory.{0}) : Prop :=
  match demand with
  | .hosting => HostedBy reading candidate
  | .exhausting => HostsExhaustively candidate reading

/-- **A candidate is a host of a class of theories, at a level, for a
demand**: every reading of the class at that level has a map into the
candidate that meets the demand. -/
def HostOf (candidate : ContextTheory.{0}) (sources : ContextTheory.{0} → Prop) (level : Level)
    (demand : Demand) : Prop :=
  ∀ reading, level.readings sources reading → demand.Met candidate reading

/-- At the level of contexts and for hosting, the sentence is `HostsEvery`. -/
theorem hostOf_contexts_hosting_iff {candidate : ContextTheory.{0}}
    {sources : ContextTheory.{0} → Prop} :
    HostOf candidate sources .contexts .hosting ↔ HostsEvery candidate sources :=
  Iff.rfl

/-- The stronger demand implies the weaker. -/
theorem HostOf.hosting {candidate : ContextTheory.{0}} {sources : ContextTheory.{0} → Prop}
    {level : Level} (hosts : HostOf candidate sources level .exhausting) :
    HostOf candidate sources level .hosting := by
  intro reading member
  obtain ⟨map, hosting, _⟩ := hosts reading member
  exact ⟨map, hosting⟩

/-- **Hosting with all contexts implies hosting on terms.** -/
theorem HostOf.terms {candidate : ContextTheory.{0}} {sources : ContextTheory.{0} → Prop}
    (hosts : HostOf candidate sources .contexts .hosting) :
    HostOf candidate sources .terms .hosting := by
  rintro reading ⟨source, member, interface, rfl⟩
  obtain ⟨map, hosting⟩ := hosts source member
  exact ⟨map.onTerms interface, hosting.onTerms interface⟩

/-- A host of a class is a host of every smaller class. -/
theorem HostOf.mono {candidate : ContextTheory.{0}} {larger smaller : ContextTheory.{0} → Prop}
    {level : Level} {demand : Demand} (hosts : HostOf candidate larger level demand)
    (subclass : ∀ source, smaller source → larger source) :
    HostOf candidate smaller level demand := by
  intro reading member
  cases level with
  | contexts => exact hosts reading (subclass reading member)
  | terms =>
      obtain ⟨source, inClass, interface, rfl⟩ := member
      exact hosts _ ⟨source, subclass source inClass, interface, rfl⟩

/-- A host that is itself hosted passes its class on. -/
theorem HostOf.trans {candidate larger : ContextTheory.{0}} {sources : ContextTheory.{0} → Prop}
    {level : Level} (hosts : HostOf candidate sources level .hosting)
    (into : HostedBy candidate larger) : HostOf larger sources level .hosting :=
  fun reading member => HostedBy.trans (hosts reading member) into

/-- **Positive**: the rule-table evaluator is a host of the theories given by
a table, with all their contexts. -/
theorem tableEvaluator_hostOf_tabular : HostOf tableEvaluator TabularTheory .contexts .hosting :=
  tableEvaluator_hostsEvery

/-- **Positive**, for the stronger demand: the framework over the rules of a
finitary proof system hosts that system with nothing added. -/
theorem framework_hostOf_exhausting {J : Type} {P : RuleSignature J} (finitary : P.Finitary) :
    HostOf (frameworkTheory finitary.signature)
      (fun source => source = P.proofTheory (RuleSignature.ProofCongruence.identity P))
      .contexts .exhausting := by
  rintro reading rfl
  exact ⟨finitary.encodingMap, finitary.encodingMap_hosting, finitary.encodingMap_exhausting⟩

/-! ## The two readings of the candidate -/

/-- **The presented reading** of the candidate: the contexts of its
presentation, for an evaluator of its premises. -/
abbrev presentedReading (base : BasePremiseEvaluator) : ContextTheory.{0} :=
  contextTheory base queryFirstCandidatePresentation

/-- **The kernel reading** of the candidate: the kernel assembled over a
model, given by its terms alone. -/
abbrev kernelReading (model : Model) : ContextTheory.{0} :=
  (kernelGSLT model).termsAlone

/-- The contexts of the presented reading have a linear size. -/
def presentedLinearSize (base : BasePremiseEvaluator) : (presentedReading base).LinearSize :=
  QuoteDropOnly.linearSize queryFirstCandidatePresentation language_quoteDropOnly base

/-- The pure calculus is a theory given by a table. -/
theorem pure_tabular : TabularTheory (rewritingTheory Theory.empty) :=
  ⟨Theory.empty, ∅, empty_tabular, rfl⟩

/-! ## The rule-table evaluator, with all contexts -/

/-- **(P) No map of theories goes from the rule-table evaluator to the
presented reading**: the evaluator discards, and the contexts of a
presentation use each hole once. -/
theorem presented_isEmpty_contextMap_tableEvaluator (base : BasePremiseEvaluator) :
    IsEmpty (ContextMap tableEvaluator (presentedReading base)) :=
  (presentedLinearSize base).isEmpty_contextMap_of_discards tableEvaluator_discards
    ⟨(⟨∅, .srt .type⟩ : Tabled)⟩

/-- (P) Nor from any theory given by a table. -/
theorem presented_isEmpty_contextMap_tabular (base : BasePremiseEvaluator)
    {source : ContextTheory.{0}} (tabular : TabularTheory source) :
    IsEmpty (ContextMap source (presentedReading base)) := by
  obtain ⟨theory, table, _, rfl⟩ := tabular
  exact (presentedLinearSize base).isEmpty_contextMap_of_discards (rewritingTheory_discards theory)
    ⟨(.srt .type : LF.Term)⟩

theorem presented_not_hostOf_tabular_contexts (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base) TabularTheory .contexts .hosting :=
  fun hosts =>
    let ⟨map, _⟩ := hosts _ pure_tabular
    (presented_isEmpty_contextMap_tabular base pure_tabular).false map

/-- **(K) No map of theories goes from the rule-table evaluator to the kernel
reading**, for any model: the kernel reading has no context of two holes. -/
theorem kernel_isEmpty_contextMap_tableEvaluator (model : Model) :
    IsEmpty (ContextMap tableEvaluator (kernelReading model)) :=
  isEmpty_contextMap_into_termsAlone (kernelGSLT model) (holes := fun _ : Bool => ())
    (result := ()) (Dedukti.tabledShape.hole false)

/-- (K) Nor from any theory given by a table. -/
theorem kernel_isEmpty_contextMap_tabular (model : Model) {source : ContextTheory.{0}}
    (tabular : TabularTheory source) : IsEmpty (ContextMap source (kernelReading model)) := by
  obtain ⟨theory, table, _, rfl⟩ := tabular
  exact isEmpty_contextMap_into_termsAlone (kernelGSLT model) (holes := fun _ : Bool => ())
    (result := ()) (TermContext.hole false)

theorem kernel_not_hostOf_tabular_contexts (model : Model) :
    ¬ HostOf (kernelReading model) TabularTheory .contexts .hosting :=
  fun hosts =>
    let ⟨map, _⟩ := hosts _ pure_tabular
    (kernel_isEmpty_contextMap_tabular model pure_tabular).false map

/-! ## Theories given by a table, on terms -/

/-- The pure calculus, on its terms, has the cyclic reduction. -/
theorem pureTerms_cycle :
    Relation.TransGen (((rewritingTheory Theory.empty).gslt ()).termsAlone.rewrites
      (interface := PUnit.unit)) Dedukti.omega Dedukti.omega :=
  .single (omega_step _)

/-- The rule-table evaluator, on its terms, has the cyclic reduction. -/
theorem evaluatorTerms_cycle :
    Relation.TransGen ((tableEvaluator.gslt ()).termsAlone.rewrites (interface := PUnit.unit))
      (⟨∅, Dedukti.omega⟩ : Tabled) ⟨∅, Dedukti.omega⟩ :=
  tableEvaluator_cycle ∅

/-- **A candidate with a rank is no host of the theories given by a table,
on terms.** -/
theorem not_hostOf_tabular_terms_of_rank {candidate : ContextTheory.{0}} (ranked : candidate.Rank) :
    ¬ HostOf candidate TabularTheory .terms .hosting := by
  intro hosts
  obtain ⟨map, hosting⟩ := hosts _ ⟨_, pure_tabular, (), rfl⟩
  exact map.not_preserves_of_cycle_of_rank ranked pureTerms_cycle hosting.preserves

/-- **A candidate with a rank hosts no theory given by a table, on terms**:
each of them has the cyclic reduction. -/
theorem not_hostedBy_tabular_terms_of_rank {candidate : ContextTheory.{0}} (ranked : candidate.Rank)
    {source : ContextTheory.{0}} (tabular : TabularTheory source) (interface : source.Interface) :
    ¬ HostedBy (source.gslt interface).termsAlone candidate := by
  obtain ⟨theory, table, _, rfl⟩ := tabular
  rintro ⟨map, hosting⟩
  exact map.not_preserves_of_cycle_of_rank ranked (interface := PUnit.unit) (term := Dedukti.omega)
    (.single (omega_step theory)) hosting.preserves

/-- **Nor when a nonempty reduction of the candidate is counted as one
step.** -/
theorem not_hostOf_tabular_terms_of_rank_nonempty {candidate : ContextTheory.{0}}
    (ranked : candidate.Rank) :
    ¬ HostOf candidate.nonemptyReduction TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank ranked.nonempty

/-- **(P) The presented reading is no host of the theories given by a table,
on terms**, for any evaluator of its premises. -/
theorem presented_not_hostOf_tabular_terms (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base) TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank (probeRank base)

/-- (P) Nor at the profile of nonempty reductions. -/
theorem presented_not_hostOf_tabular_terms_nonempty (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base).nonemptyReduction TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank_nonempty (probeRank base)

/-- **(P) No map sends each step of the rule-table evaluator to a nonempty
reduction of the presented reading**: the clause that is lost is the
preservation of transitions, before any reflection is asked. -/
theorem presented_not_simulates_tableEvaluator (base : BasePremiseEvaluator)
    (map : ContextMap (tableEvaluator.gslt ()).termsAlone (presentedReading base).nonemptyReduction) :
    ¬ map.PreservesTransitions :=
  map.not_simulates_of_cycle_of_rank (probeRank base) evaluatorTerms_cycle

/-- **(K) The kernel over a query-first model is no host of the theories
given by a table, on terms.** -/
theorem queryFirstKernel_not_hostOf_tabular_terms (model : QueryFirstModel) :
    ¬ HostOf (kernelReading model.toAssemblyModel) TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank (queryFirstKernelRank model)

/-- (K) Nor at the profile of nonempty reductions. -/
theorem queryFirstKernel_not_hostOf_tabular_terms_nonempty (model : QueryFirstModel) :
    ¬ HostOf (kernelReading model.toAssemblyModel).nonemptyReduction TabularTheory .terms
      .hosting :=
  not_hostOf_tabular_terms_of_rank_nonempty (queryFirstKernelRank model)

/-- (K) No map sends each step of the rule-table evaluator to a nonempty
reduction of the kernel over a query-first model. -/
theorem queryFirstKernel_not_simulates_tableEvaluator (model : QueryFirstModel)
    (map : ContextMap (tableEvaluator.gslt ()).termsAlone
      (kernelReading model.toAssemblyModel).nonemptyReduction) :
    ¬ map.PreservesTransitions :=
  map.not_simulates_of_cycle_of_rank (queryFirstKernelRank model) evaluatorTerms_cycle

/-- **(K) For every model: a kernel whose base has a rank that its static
equivalence keeps is no host of the theories given by a table, on terms.**
What hosts a cyclic reduction in the kernel is its base. -/
theorem kernel_not_hostOf_tabular_terms_of_baseRank (model : Model)
    (baseRank : model.base.host.Term → Nat)
    (lowers : ∀ {term next : model.base.host.Term}, model.base.host.Step term next →
      baseRank next < baseRank term)
    (respects : ∀ {first second : model.base.host.Term}, model.base.host.Equiv first second →
      baseRank first = baseRank second) :
    ¬ HostOf (kernelReading model) TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank (kernelRankOfBaseRank model baseRank lowers respects)

/-- **What a host of the evaluator has to have**: a term that reduces to
itself. -/
theorem cycle_of_preserves_tableEvaluator {candidate : ContextTheory.{0}}
    (map : ContextMap (tableEvaluator.gslt ()).termsAlone candidate)
    (preserves : map.PreservesTransitions) :
    ∃ (interface : candidate.Interface) (term : candidate.Term interface),
      Relation.TransGen candidate.rewrites term term :=
  ⟨_, _, map.cycle_of_preserves preserves evaluatorTerms_cycle⟩

/-- **(K) The kernel of a model that carries the rule-table evaluator beside
its base is a host of the theories given by a table, on terms.** -/
theorem guestKernel_hostOf_tabular_terms (model : Model) :
    HostOf (kernelReading (withGuest model (tableEvaluator.gslt ()))) TabularTheory .terms
      .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, rfl⟩, interface, rfl⟩
  exact ⟨(guestMap model (tableEvaluator.gslt ())).comp ((loadMap theory table).betweenTerms interface),
    (guestMap_hosting model (tableEvaluator.gslt ())).comp
      ((loadMap_hosting tabular).betweenTerms interface)⟩

/-- **Negative**: hosting on terms does not give hosting with all contexts. -/
theorem guestKernel_terms_not_contexts (model : Model) :
    HostOf (kernelReading (withGuest model (tableEvaluator.gslt ()))) TabularTheory .terms .hosting ∧
      ¬ HostOf (kernelReading (withGuest model (tableEvaluator.gslt ()))) TabularTheory .contexts
        .hosting :=
  ⟨guestKernel_hostOf_tabular_terms model, kernel_not_hostOf_tabular_contexts _⟩

/-! ## The proof-system side -/

/-- **(P) No map of theories goes from the framework with rules as constants
to the presented reading**, as soon as the framework has a type. -/
theorem presented_isEmpty_contextMap_framework (base : BasePremiseEvaluator) {B : Type}
    (signature : Signature B) (type : Ty B) :
    IsEmpty (ContextMap (frameworkTheory signature) (presentedReading base)) :=
  (presentedLinearSize base).isEmpty_contextMap_of_discards
    (frameworkTheory_discards signature (.arrow type type)) ⟨Tm.lam (Tm.var .zero)⟩

/-- **(K) Nor to the kernel reading**, for any model. -/
theorem kernel_isEmpty_contextMap_framework (model : Model) {B : Type} (signature : Signature B)
    (type : Ty B) : IsEmpty (ContextMap (frameworkTheory signature) (kernelReading model)) :=
  isEmpty_contextMap_into_termsAlone (kernelGSLT model) (holes := fun _ : Bool => type)
    (result := type) (Tm.hole (holes := fun _ : Bool => type) false)

/-- (P) No map of theories goes from a proof system with a derivation to the
presented reading. -/
theorem presented_isEmpty_contextMap_proofTheory (base : BasePremiseEvaluator) {J : Type}
    (P : RuleSignature J) (congruence : P.ProofCongruence) {j : J} (proof : P.Proof j) :
    IsEmpty (ContextMap (P.proofTheory congruence) (presentedReading base)) :=
  (presentedLinearSize base).isEmpty_contextMap_of_discards (proofTheory_discards P congruence j)
    ⟨proof⟩

/-- (K) Nor from any proof system with a judgment to the kernel reading. -/
theorem kernel_isEmpty_contextMap_proofTheory (model : Model) {J : Type} (P : RuleSignature J)
    (congruence : P.ProofCongruence) (j : J) :
    IsEmpty (ContextMap (P.proofTheory congruence) (kernelReading model)) :=
  isEmpty_contextMap_into_termsAlone (kernelGSLT model) (holes := fun _ : Bool => j) (result := j)
    (P.assume (holes := fun _ : Bool => j) false)

/-- **(P) The presented reading is a host of the numbered proof systems, on
terms**: a derivation is kept as a numeral atom. -/
theorem presented_hostOf_numberedProofSystem_terms (base : BasePremiseEvaluator) :
    HostOf (presentedReading base) NumberedProofSystem .terms .hosting := by
  rintro reading ⟨source, ⟨J, P, finitary, numbering, rfl⟩, j, rfl⟩
  exact hostsEvery_numberedDerivations_of_inertData (probeAtoms base) _
    ⟨J, P, finitary, numbering, j, rfl⟩

/-- (P) The same at the sort of names: a derivation is kept as a quoted
numeral. -/
theorem presented_hostsEvery_numberedDerivations_names (base : BasePremiseEvaluator) :
    HostsEvery (presentedReading base) NumberedDerivations :=
  hostsEvery_numberedDerivations_of_inertData (probeNames base)

/-- **(P) The presented reading hosts the terms of the type of each judgment
of the framework**, up to its conversion. -/
theorem presented_hostsEvery_frameworkJudgments (base : BasePremiseEvaluator) :
    HostsEvery (presentedReading base) NumberedFrameworkJudgments :=
  hostsEvery_numberedFrameworkJudgments_of_inertData (probeNames base)

/-- The quoted numerals of the kernel reading: inert data indexed by the
natural numbers. -/
def kernelNumerals (model : Model) : (kernelReading model).InertData Nat :=
  (kernelNames model).reindex numeral numeral_injective

/-- **(K) The kernel reading is a host of the numbered proof systems, on
terms**, for every model: a derivation is kept as a quoted name. -/
theorem kernel_hostOf_numberedProofSystem_terms (model : Model) :
    HostOf (kernelReading model) NumberedProofSystem .terms .hosting := by
  rintro reading ⟨source, ⟨J, P, finitary, numbering, rfl⟩, j, rfl⟩
  exact hostsEvery_numberedDerivations_of_inertData (kernelNumerals model) _
    ⟨J, P, finitary, numbering, j, rfl⟩

/-- **(K) The kernel reading hosts the terms of the type of each judgment of
the framework**, up to its conversion. -/
theorem kernel_hostsEvery_frameworkJudgments (model : Model) :
    HostsEvery (kernelReading model) NumberedFrameworkJudgments :=
  hostsEvery_numberedFrameworkJudgments_of_inertData (kernelNumerals model)

/-- **(P) The presented reading is a host of the frameworks over countable
signatures, on terms**: at every type, a term is kept as the quoted numeral
of the number of its conversion class. -/
theorem presented_hostOf_countableFramework_terms (base : BasePremiseEvaluator) :
    HostOf (presentedReading base) CountableFramework .terms .hosting := by
  rintro reading ⟨source, ⟨B, countable, signature, constants, rfl⟩, type, rfl⟩
  exact hostsEvery_countableFrameworkTerms_of_inertData (probeNames base) _
    ⟨B, countable, signature, constants, type, rfl⟩

/-- **(K) So is the kernel reading**, for every model. -/
theorem kernel_hostOf_countableFramework_terms (model : Model) :
    HostOf (kernelReading model) CountableFramework .terms .hosting := by
  rintro reading ⟨source, ⟨B, countable, signature, constants, rfl⟩, type, rfl⟩
  exact hostsEvery_countableFrameworkTerms_of_inertData (kernelNumerals model) _
    ⟨B, countable, signature, constants, type, rfl⟩

/-- **Negative**: neither reading is a host of the frameworks over countable
signatures with all their contexts. -/
theorem not_hostOf_countableFramework_contexts (base : BasePremiseEvaluator) (model : Model) :
    ¬ HostOf (presentedReading base) CountableFramework .contexts .hosting ∧
      ¬ HostOf (kernelReading model) CountableFramework .contexts .hosting :=
  ⟨fun hosts =>
      let ⟨map, _⟩ := hosts _ twoAxioms_countableFramework
      (presented_isEmpty_contextMap_framework base _ (.base ())).false map,
    fun hosts =>
      let ⟨map, _⟩ := hosts _ twoAxioms_countableFramework
      (kernel_isEmpty_contextMap_framework model _ (.base ())).false map⟩

/-- **Negative**: neither reading is a host of the numbered proof systems
with all their contexts. -/
theorem not_hostOf_numberedProofSystem_contexts (base : BasePremiseEvaluator) (model : Model) :
    ¬ HostOf (presentedReading base) NumberedProofSystem .contexts .hosting ∧
      ¬ HostOf (kernelReading model) NumberedProofSystem .contexts .hosting :=
  ⟨fun hosts =>
      let ⟨map, _⟩ := hosts _ twoAxioms_numberedProofSystem
      (presented_isEmpty_contextMap_proofTheory base twoAxioms _ (chosenAxiom true)).false map,
    fun hosts =>
      let ⟨map, _⟩ := hosts _ twoAxioms_numberedProofSystem
      (kernel_isEmpty_contextMap_proofTheory model twoAxioms _ ()).false map⟩

/-! ## Where exhausting holds -/

/-- **A hosting map on terms is hosting and exhausting onto the region of the
candidate that its image spans.** -/
theorem hostsExhaustively_imageRegion {source : GSLT.{0}} {candidate : ContextTheory.{0}}
    (point : candidate.Interface) (term : source.Term → candidate.Term point)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      (candidate.equations point).r (term first) (term second))
    (hosting : (ContextMap.ofTerms point term term_resp).Hosting) :
    HostsExhaustively ((candidate.gslt point).region (ContextMap.ImageClass point term)).termsAlone
      source.termsAlone :=
  ⟨ContextMap.ontoImage point term term_resp, ContextMap.ontoImage_hosting point term term_resp hosting,
    ContextMap.ontoImage_exhausting point term term_resp⟩

/-- **(P) No coding by numeral atoms exhausts the atoms**: the dropping of
the quoted unit atom is outside every image. -/
theorem presentedAtoms_not_exhausting (base : BasePremiseEvaluator) {source : GSLT.{0}}
    (code : source.Term → Nat)
    (respects : ∀ {first second : source.Term}, source.equations.r first second →
      code first = code second) :
    ¬ ((probeAtoms base).codeMap code respects).Exhausting := by
  intro exhausting
  obtain ⟨preimage, related⟩ :=
    ContextMap.Exhausting.term_surjective _ exhausting (origin := PUnit.unit) droppedAtom
  exact droppedAtom_not_numeral base (code preimage) related

/-- **(K) No coding by quoted numerals exhausts the kernel**: a value of the
reflection layer is outside every image. -/
theorem kernelNumerals_not_exhausting (model : Model) {source : GSLT.{0}}
    (code : source.Term → Nat)
    (respects : ∀ {first second : source.Term}, source.equations.r first second →
      code first = code second) :
    ¬ ((kernelNumerals model).codeMap code respects).Exhausting := by
  intro exhausting
  obtain ⟨preimage, related⟩ :=
    ContextMap.Exhausting.term_surjective _ exhausting (origin := PUnit.unit)
      (kernelValue model unitAtom)
  cases related with
  | right runtimeRelated =>
      cases runtimeRelated with
      | left reflectionRelated => cases reflectionRelated

/-! ## What the pinned defects of the presentation cost -/

/-- **Reduction is in a separate sort**: no constructor of the sort `Process`
takes a process, so a term that reduces has no part that reduces. -/
theorem language_process_takes_no_process :
    ∀ rule ∈ language.terms, rule.category = "Process" →
      ∀ parameter ∈ rule.params, parameter.typeExpr ≠ .base "Process" := by
  decide

/-- **The extension with choice lifts neither refutation.**  With all
contexts: no map from the rule-table evaluator. -/
theorem choice_isEmpty_contextMap_tableEvaluator (base : BasePremiseEvaluator) :
    IsEmpty (ContextMap tableEvaluator (contextTheory base choicePresentation)) :=
  (choiceLinearSize base).isEmpty_contextMap_of_discards tableEvaluator_discards
    ⟨(⟨∅, .srt .type⟩ : Tabled)⟩

/-- On terms: the extension is no host of the theories given by a table. -/
theorem choice_not_hostOf_tabular_terms (base : BasePremiseEvaluator) :
    ¬ HostOf (contextTheory base choicePresentation) TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank (choiceRank base)

/-- Nor at the profile of nonempty reductions. -/
theorem choice_not_hostOf_tabular_terms_nonempty (base : BasePremiseEvaluator) :
    ¬ HostOf (contextTheory base choicePresentation).nonemptyReduction TabularTheory .terms
      .hosting :=
  not_hostOf_tabular_terms_of_rank_nonempty (choiceRank base)

/-- The proof-system side with all contexts is not lifted either. -/
theorem choice_isEmpty_contextMap_framework (base : BasePremiseEvaluator) {B : Type}
    (signature : Signature B) (type : Ty B) :
    IsEmpty (ContextMap (frameworkTheory signature) (contextTheory base choicePresentation)) :=
  (choiceLinearSize base).isEmpty_contextMap_of_discards
    (frameworkTheory_discards signature (.arrow type type)) ⟨Tm.lam (Tm.var .zero)⟩

#print axioms HostOf.terms
#print axioms tableEvaluator_hostOf_tabular
#print axioms framework_hostOf_exhausting
#print axioms presented_isEmpty_contextMap_tableEvaluator
#print axioms presented_not_hostOf_tabular_contexts
#print axioms kernel_isEmpty_contextMap_tableEvaluator
#print axioms kernel_not_hostOf_tabular_contexts
#print axioms not_hostedBy_tabular_terms_of_rank
#print axioms presented_not_hostOf_tabular_terms
#print axioms presented_not_hostOf_tabular_terms_nonempty
#print axioms presented_not_simulates_tableEvaluator
#print axioms queryFirstKernel_not_hostOf_tabular_terms
#print axioms queryFirstKernel_not_simulates_tableEvaluator
#print axioms kernel_not_hostOf_tabular_terms_of_baseRank
#print axioms cycle_of_preserves_tableEvaluator
#print axioms guestKernel_hostOf_tabular_terms
#print axioms guestKernel_terms_not_contexts
#print axioms presented_isEmpty_contextMap_framework
#print axioms kernel_isEmpty_contextMap_framework
#print axioms presented_hostOf_numberedProofSystem_terms
#print axioms presented_hostsEvery_frameworkJudgments
#print axioms kernel_hostOf_numberedProofSystem_terms
#print axioms kernel_hostsEvery_frameworkJudgments
#print axioms presented_hostOf_countableFramework_terms
#print axioms kernel_hostOf_countableFramework_terms
#print axioms not_hostOf_countableFramework_contexts
#print axioms not_hostOf_numberedProofSystem_contexts
#print axioms hostsExhaustively_imageRegion
#print axioms presentedAtoms_not_exhausting
#print axioms kernelNumerals_not_exhausting
#print axioms language_process_takes_no_process
#print axioms choice_isEmpty_contextMap_tableEvaluator
#print axioms choice_not_hostOf_tabular_terms
#print axioms choice_isEmpty_contextMap_framework

end Mettapedia.Logic.HostingStyles.PrimeCandidate
