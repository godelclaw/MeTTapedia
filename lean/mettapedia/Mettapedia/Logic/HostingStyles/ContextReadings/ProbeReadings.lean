import Mettapedia.Logic.HostingStyles.PrimeCandidate.HostSentence
import Mettapedia.Logic.HostingStyles.PrimeCandidate.RunExtension
import Mettapedia.Logic.HostingStyles.ContextReadings.PresentedReadings

/-!
# The three readings of the candidate presentation

The presented candidate with its contexts as they are (`presentedReading`)
is its linear reading.  This module puts beside it

* the **cartesian reading** `cartesianProbe`: every hole may be used any
  number of times;
* the **reading with regions** `regionProbe`: atoms and names (`probeData`)
  may be discarded and copied, a process and every other term is used once.

## Where each discards and copies

| | linear | regions | cartesian |
|---|---|---|---|
| atoms, names | no (`presented_not_discards`) | yes (`regionProbe_discards_iff`) | yes |
| processes | no | no (`cartesian_has_region_lacks`) | yes |

The context of two atoms that returns the first is in the reading with regions
and in no way a linear context (`region_has_linear_lacks`); the context of two
processes that returns the first is in the cartesian reading and not in the
reading with regions (`cartesian_has_region_lacks`).

## What each receives a map from

*The linear reading* receives no map from a theory that discards or copies
(existing `presented_isEmpty_contextMap_tableEvaluator`,
`presented_isEmpty_contextMap_framework`).

*The cartesian reading* and *the reading with regions* receive a map from
every theory, the constant map at a datum (`intoCartesianProbe`,
`intoRegionProbe`), so the question moves to hosting.

*From the linear reading into the reading with regions* no map is the
identity on the closed atoms and on the closed processes
(`presented_not_identity_into_regions`): the contexts at an interface without
terms send all interfaces to data, or none.

* **The framework with rules as constants is not hosted** as soon as one of
  its types has two closed terms that are not convertible
  (`cartesianProbe_not_hosting_framework`,
  `cartesianProbe_not_hostOf_countableFramework_contexts`).  The framework
  applies (`frameworkTheory_applies`): the context that applies its first hole
  to its second returns the second for the identity and a fixed term for a
  constant function.  A context of the reading places its fillings in a
  pattern and the static equivalence keeps a weight; it cannot do that.
* **The rule-table evaluator is not hosted**: the candidate has a rank, and a
  rank is about terms (`cartesianProbe_not_preserves_tableEvaluator`,
  `cartesianProbe_not_hostOf_tabular_contexts`).

*The reading with regions* sends every interface at which its source discards
to data (`regionProbe_data_of_tableEvaluator`,
`regionProbe_data_of_framework`).  Data does not reduce (`probeData_static`),
so a map from the rule-table evaluator preserves no step
(`regionProbe_not_preserves_tableEvaluator`).  The same holds of the candidate
extended with a run constructor, **under every evaluator of its premises**
(`regionRun_not_preserves_tableEvaluator`), although on terms that extension
hosts every theory given by a table under a suitable evaluator: with regions
the obstruction is where reduction lives, not how much of it there is.

The two negative statements about the cartesian reading hold also of the
kernel over a model read with all holes free
(`cartesianKernel_not_hosting_framework`,
`cartesianKernel_not_preserves_tableEvaluator`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory tableEvaluator Tabled omega_step)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef (language queryFirstCandidatePresentation)
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language (Model QueryFirstModel kernelGSLT)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Framework

/-! ## The readings -/

/-- **The data of the candidate presentation**: its atoms and its names,
beneath any binders. -/
def probeData : Contexts.Interface → Prop := ofSorts ["Atom", "CandidateName"]

/-- **Positive**: the closed atoms and the closed names. -/
theorem probeData_closedAtom : probeData closedAtom := ofSorts_base (by decide) []

/-- The closed names are data. -/
theorem probeData_closedName : probeData closedName := ofSorts_base (by decide) []

/-- **Negative**: the closed processes. -/
theorem not_probeData_closedProcess : ¬ probeData closedProcess := not_ofSorts_base (by decide) []

/-- **The cartesian reading of the candidate presentation.** -/
abbrev cartesianProbe (base : BasePremiseEvaluator) : ContextTheory.{0} :=
  (presentedReading base).cartesianReading

/-- **The reading with regions of the candidate presentation**: atoms and
names may be discarded and copied; a process, a space and a receipt are used
once. -/
abbrev regionProbe (base : BasePremiseEvaluator) : ContextTheory.{0} :=
  (presentedReading base).regionReading probeData

/-- The unit atom, a closed atom. -/
def unitTerm : Contexts.Term language closedAtom := ⟨numeral 0, numeral_wellSorted 0⟩

/-- The size of the cartesian reading: the weight, each hole counted as often
as it is used. -/
def cartesianProbeSize (base : BasePremiseEvaluator) : (cartesianProbe base).MultiplicitySize :=
  (presentedLinearSize base).regionReading
    (contextTheory_finiteHoles base queryFirstCandidatePresentation) fun _ => True

/-- The size of the reading with regions. -/
def regionProbeSize (base : BasePremiseEvaluator) : (regionProbe base).MultiplicitySize :=
  (presentedLinearSize base).regionReading
    (contextTheory_finiteHoles base queryFirstCandidatePresentation) probeData

/-- The rank of the candidate is a rank of its cartesian reading. -/
def cartesianProbeRank (base : BasePremiseEvaluator) : (cartesianProbe base).Rank :=
  (probeRank base).regionReading fun _ => True

/-- The rewrites of the candidate presentation are headed by constructors of
processes. -/
theorem language_headedIn_process : rewritesHeadedIn language ["Process"] = true := by
  decide

/-- **Data does not reduce**: no atom and no name has a step. -/
theorem probeData_static (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (data : probeData interface) (term next : (presentedReading base).Term interface) :
    ¬ (presentedReading base).rewrites term next := by
  intro step
  obtain ⟨sort, member, same⟩ := data
  obtain ⟨other, listed, type⟩ := termStep_ofSorts language_headedIn_process step
  obtain rfl : sort = other := TypeExpr.base.inj (same.symm.trans type)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member listed
  subst listed
  rcases member with impossible | impossible <;> exact absurd impossible (by decide)

/-! ## Where each reading discards and copies -/

/-- **The linear reading discards at no inhabited interface.** -/
theorem presented_not_discards (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (term : (presentedReading base).Term interface) : ¬ (presentedReading base).Discards interface :=
  (presentedLinearSize base).not_discards term

/-- **Nor does it copy.** -/
theorem presented_not_copies (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (term : (presentedReading base).Term interface) : ¬ (presentedReading base).Copies interface :=
  (presentedLinearSize base).not_copies term

/-- **The reading with regions discards exactly at data**, among the
inhabited interfaces. -/
theorem regionProbe_discards_iff (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (term : (presentedReading base).Term interface) :
    (regionProbe base).Discards interface ↔ probeData interface :=
  (ContextTheory.regionReading_discards_iff (theory := presentedReading base)
    (declared := probeData)).trans
    ⟨fun either => either.elim id fun discards =>
      (presented_not_discards base term discards).elim, .inl⟩

/-- **It copies exactly at data.** -/
theorem regionProbe_copies_iff (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (term : (presentedReading base).Term interface) :
    (regionProbe base).Copies interface ↔ probeData interface :=
  (ContextTheory.regionReading_copies_iff (theory := presentedReading base)
    (declared := probeData)).trans
    ⟨fun either => either.elim id fun copies =>
      (presented_not_copies base term copies).elim, .inl⟩

/-- The context of two atoms that returns the first. -/
def firstOfTwoAtoms (base : BasePremiseEvaluator) :
    (regionProbe base).Context (fun _ : Bool => closedAtom) closedAtom :=
  ContextTheory.RegionContext.project (theory := presentedReading base) (declared := probeData)
    (fun _ : Bool => closedAtom) false fun _ => probeData_closedAtom

@[simp] theorem fill_firstOfTwoAtoms (base : BasePremiseEvaluator)
    (filling : Bool → Contexts.Term language closedAtom) :
    (regionProbe base).fill (firstOfTwoAtoms base) filling = filling false :=
  rfl

/-- **A context that the reading with regions has and the linear reading
lacks**: no linear context returns the first of two atoms. -/
theorem region_has_linear_lacks (base : BasePremiseEvaluator) :
    ¬ ∃ context : (presentedReading base).Context (fun _ : Bool => closedAtom) closedAtom,
      ∀ filling : Bool → Contexts.Term language closedAtom,
        ((presentedReading base).equations closedAtom).r
          ((presentedReading base).fill context filling)
          ((regionProbe base).fill (firstOfTwoAtoms base) filling) :=
  fun ⟨context, agrees⟩ => presented_not_discards base unitTerm ⟨context, agrees⟩

/-- The context of two processes that returns the first. -/
def firstOfTwoProcesses (base : BasePremiseEvaluator) :
    (cartesianProbe base).Context (fun _ : Bool => closedProcess) closedProcess :=
  ContextTheory.cartesianFirst (presentedReading base) closedProcess

/-- **A context that the cartesian reading has and the reading with regions
lacks**: no context of the reading with regions returns the first of two
processes. -/
theorem cartesian_has_region_lacks (base : BasePremiseEvaluator) :
    ¬ ∃ context : (regionProbe base).Context (fun _ : Bool => closedProcess) closedProcess,
      ∀ filling : Bool → Contexts.Term language closedProcess,
        ((regionProbe base).equations closedProcess).r ((regionProbe base).fill context filling)
          ((cartesianProbe base).fill (firstOfTwoProcesses base) filling) :=
  fun ⟨context, agrees⟩ => not_probeData_closedProcess
    ((regionProbe_discards_iff base needAnswerTerm).mp ⟨context, agrees⟩)

/-- **The cartesian reading adds contexts to the linear one**: the identity
on terms from the candidate into its cartesian reading is hosting and not
exhausting. -/
theorem presented_toCartesian_not_exhausting (base : BasePremiseEvaluator) :
    (presentedReading base).toCartesianReading.Hosting ∧
      ¬ (presentedReading base).toCartesianReading.Exhausting :=
  ⟨(presentedReading base).toCartesianReading_hosting, fun exhausting =>
    presented_not_discards base unitTerm
      (ContextTheory.discards_of_toCartesianReading_exhausting (presentedReading base) exhausting
        closedAtom)⟩

/-- **It adds contexts to the reading with regions too**: the identity on
terms from that reading into the cartesian one is hosting and not
exhausting. -/
theorem regionProbe_toCartesian_not_exhausting (base : BasePremiseEvaluator) :
    ((presentedReading base).regionToCartesian probeData).Hosting ∧
      ¬ ((presentedReading base).regionToCartesian probeData).Exhausting :=
  ⟨(presentedReading base).regionToCartesian_hosting probeData, fun exhausting =>
    not_probeData_closedProcess ((regionProbe_discards_iff base needAnswerTerm).mp
      (ContextTheory.discards_of_regionToCartesian_exhausting (presentedReading base) probeData
        exhausting closedProcess))⟩

/-- **Negative**, for `rewritesHeadedIn`: no rewrite of the candidate is
headed by a constructor of atoms. -/
theorem language_not_headedIn_atom : rewritesHeadedIn language ["Atom"] = false := by
  decide

/-! ## Maps exist into the cartesian reading and into the regions; hosting is the question -/

/-- **Every theory maps into the cartesian reading of the candidate**: every
term to the unit atom. -/
def intoCartesianProbe (base : BasePremiseEvaluator) (source : ContextTheory.{0}) :
    ContextMap source (cartesianProbe base) :=
  ContextTheory.intoCartesianReading source (presentedReading base) unitTerm

/-- **Every theory maps into the reading with regions of the candidate**:
every term to the unit atom, which is data. -/
def intoRegionProbe (base : BasePremiseEvaluator) (source : ContextTheory.{0}) :
    ContextMap source (regionProbe base) :=
  ContextTheory.intoRegionReading (theory := presentedReading base) (declared := probeData)
    source probeData_closedAtom unitTerm

/-- **No map from the candidate into its reading with regions is the identity
on the closed atoms and on the closed processes.**  A map that sends the
closed atoms to data sends every interface to data: the contexts at an
interface without terms join every interface to every other. -/
theorem presented_not_identity_into_regions (base : BasePremiseEvaluator)
    (map : ContextMap (presentedReading base) (regionProbe base))
    (atoms : map.interface closedAtom = closedAtom)
    (processes : map.interface closedProcess = closedProcess) : False :=
  not_probeData_closedProcess
    ((congrArg probeData processes).mp
      (contextMap_declared_all_or_none base queryFirstCandidatePresentation map
        ((congrArg probeData atoms).mpr probeData_closedAtom) closedProcess))

/-- The context of the framework that applies what fills its first hole to
what fills its second. -/
def applicationContext {B : Type} (signature : Signature B) (type : Ty B) :
    Tm signature (fun index : Bool => bif index then type else Ty.arrow type type) [] type :=
  Tm.app (Tm.hole false) (Tm.hole true)

/-- Filling the applying context applies. -/
theorem fill_applicationContext {B : Type} (signature : Signature B) {type : Ty B}
    (applied : Closed signature (.arrow type type)) (operand : Closed signature type) :
    (applicationContext signature type).fill
        (ContextTheory.applicationFilling (theory := frameworkTheory signature) applied operand) =
      Tm.app applied operand := by
  show Tm.app (applied.rename _) (operand.rename _) = Tm.app applied operand
  rw [Tm.rename_closed, Tm.rename_closed]

/-- **The framework applies** at every type with two closed terms that are
not convertible: the application of the first hole to the second returns the
second for the identity and the other term for a constant function. -/
theorem frameworkTheory_applies {B : Type} (signature : Signature B) {type : Ty B}
    {first second : Closed signature type} (apart : ¬ Conv first second) :
    (frameworkTheory signature).Applies (.arrow type type) type := by
  refine ⟨applicationContext signature type, Tm.lam (Tm.var .zero),
    Tm.lam (second.rename (Renaming.weaken [] type)), first, second, apart, ?_, ?_, ?_⟩
  · exact .trans _ _ _ (Conv.of_eq (fill_applicationContext signature _ first))
      (.rel _ _ (Step.beta (Tm.var .zero) first))
  · exact .trans _ _ _ (Conv.of_eq (fill_applicationContext signature _ second))
      (.rel _ _ (Step.beta (Tm.var .zero) second))
  · have step := Step.beta (second.rename (Renaming.weaken [] type)) first
    rw [Tm.inst_weaken] at step
    exact .trans _ _ _ (Conv.of_eq (fill_applicationContext signature _ first)) (.rel _ _ step)

/-- **No theory with a multiplicity size hosts a framework one of whose types
has two closed terms that are not convertible.** -/
theorem not_hosting_framework_of_multiplicitySize {target : ContextTheory.{0}}
    (sized : target.MultiplicitySize) {B : Type} (signature : Signature B) {type : Ty B}
    {first second : Closed signature type} (apart : ¬ Conv first second)
    (map : ContextMap (frameworkTheory signature) target) : ¬ map.Hosting :=
  sized.not_hosting_of_applies map (frameworkTheory_applies signature apart)

/-- **The cartesian reading of the candidate hosts no such framework.** -/
theorem cartesianProbe_not_hosting_framework (base : BasePremiseEvaluator) {B : Type}
    (signature : Signature B) {type : Ty B} {first second : Closed signature type}
    (apart : ¬ Conv first second)
    (map : ContextMap (frameworkTheory signature) (cartesianProbe base)) : ¬ map.Hosting :=
  not_hosting_framework_of_multiplicitySize (cartesianProbeSize base) signature apart map

/-- The two axioms of one judgment are not convertible in their framework. -/
theorem twoAxioms_apart :
    ¬ Conv (twoAxiomsFinitary.encodeTerm (chosenAxiom true))
      (twoAxiomsFinitary.encodeTerm (chosenAxiom false)) :=
  fun convertible => chosenAxiom_code_ne
    (congrArg (twoAxiomsFinitary.proofCode twoAxiomsNumbering)
      ((twoAxiomsFinitary.encodeTerm_conv_iff _ _).mp convertible))

/-- **Negative**, for `MultiplicitySize`: the framework over two axioms of
one judgment has none; it applies. -/
theorem twoAxiomsFramework_not_multiplicitySize :
    IsEmpty (frameworkTheory twoAxiomsFinitary.signature).MultiplicitySize :=
  ContextTheory.isEmpty_multiplicitySize_of_applies
    (frameworkTheory_applies twoAxiomsFinitary.signature twoAxioms_apart)

/-- **Negative**, for `Applies`: the candidate presentation applies nowhere;
its contexts have a linear size. -/
theorem presented_not_applies (base : BasePremiseEvaluator)
    (function argument : Contexts.Interface) :
    ¬ (presentedReading base).Applies function argument :=
  (presentedLinearSize base).multiplicitySize.not_applies function argument

/-- **Negative**: the cartesian reading is no host of the frameworks over
countable signatures with all their contexts. -/
theorem cartesianProbe_not_hostOf_countableFramework_contexts (base : BasePremiseEvaluator) :
    ¬ HostOf (cartesianProbe base) CountableFramework .contexts .hosting := by
  intro hosts
  obtain ⟨map, hosting⟩ := hosts _ twoAxioms_countableFramework
  exact cartesianProbe_not_hosting_framework base twoAxiomsFinitary.signature twoAxioms_apart
    map hosting

/-- **No map from the rule-table evaluator into the cartesian reading
preserves transitions**: the candidate has a rank. -/
theorem cartesianProbe_not_preserves_tableEvaluator (base : BasePremiseEvaluator)
    (map : ContextMap tableEvaluator (cartesianProbe base)) : ¬ map.PreservesTransitions :=
  Dedukti.tableEvaluator_not_preserves_into_rank (cartesianProbeRank base) map

/-- **The cartesian reading hosts no theory given by a table.** -/
theorem cartesianProbe_not_hostedBy_tabular (base : BasePremiseEvaluator)
    {source : ContextTheory.{0}} (tabular : TabularTheory source) :
    ¬ HostedBy source (cartesianProbe base) := by
  obtain ⟨theory, table, -, rfl⟩ := tabular
  rintro ⟨map, hosting⟩
  exact map.not_preserves_of_cycle_of_rank (cartesianProbeRank base)
    (Dedukti.rewritingTheory_cycle theory) hosting.preserves

/-- **Negative**: the cartesian reading is no host of the theories given by a
table, with all their contexts. -/
theorem cartesianProbe_not_hostOf_tabular_contexts (base : BasePremiseEvaluator) :
    ¬ HostOf (cartesianProbe base) TabularTheory .contexts .hosting :=
  fun hosts => not_hostOf_tabular_terms_of_rank (cartesianProbeRank base) hosts.terms

/-! ## The reading with regions: what discards is received as data -/

/-- **Every map from the rule-table evaluator into the reading with regions
sends its terms to data.** -/
theorem regionProbe_data_of_tableEvaluator (base : BasePremiseEvaluator)
    (map : ContextMap tableEvaluator (regionProbe base)) : probeData (map.interface ()) :=
  (presentedLinearSize base).declared_of_discards map tableEvaluator_discards
    (⟨∅, .srt .type⟩ : Tabled)

/-- **So it preserves no step**: data does not reduce. -/
theorem regionProbe_not_preserves_tableEvaluator (base : BasePremiseEvaluator)
    (map : ContextMap tableEvaluator (regionProbe base)) : ¬ map.PreservesTransitions :=
  (language_quoteDropOnly.keptWeight base).regions_not_preserves
    (presentation := queryFirstCandidatePresentation) (data := ["Atom", "CandidateName"])
    (active := ["Process"]) language_headedIn_process (by decide) map
    tableEvaluator_discards (term := (⟨∅, Dedukti.omega⟩ : Tabled))
    (next := (⟨∅, Dedukti.omega⟩ : Tabled)) ⟨rfl, omega_step _⟩

/-- **Every map from a framework into the reading with regions sends each
type that has a closed term to data.** -/
theorem regionProbe_data_of_framework (base : BasePremiseEvaluator) {B : Type}
    (signature : Signature B) (map : ContextMap (frameworkTheory signature) (regionProbe base))
    {type : Ty B} (term : Closed signature type) : probeData (map.interface type) :=
  (presentedLinearSize base).declared_of_discards map (frameworkTheory_discards signature type) term

/-- **The reading with regions hosts no framework one of whose types has two
closed terms that are not convertible.** -/
theorem regionProbe_not_hosting_framework (base : BasePremiseEvaluator) {B : Type}
    (signature : Signature B) {type : Ty B} {first second : Closed signature type}
    (apart : ¬ Conv first second)
    (map : ContextMap (frameworkTheory signature) (regionProbe base)) : ¬ map.Hosting :=
  not_hosting_framework_of_multiplicitySize (regionProbeSize base) signature apart map

/-! ## The candidate with a run constructor, read with regions -/

/-- The reading with regions of the candidate extended with a run
constructor. -/
abbrev regionRun (base : BasePremiseEvaluator) : ContextTheory.{0} :=
  (contextTheory base runPresentation).regionReading probeData

/-- The rewrites of the extension are headed by constructors of processes. -/
theorem probeWithRun_headedIn_process : rewritesHeadedIn probeWithRun ["Process"] = true := by
  decide

/-- **Under every evaluator of its premises, no map from the rule-table
evaluator into the reading with regions of the extension preserves
transitions.**  The extension computes in the sort of processes; the
evaluator discards, so its terms are sent to data. -/
theorem regionRun_not_preserves_tableEvaluator (base : BasePremiseEvaluator)
    (map : ContextMap tableEvaluator (regionRun base)) : ¬ map.PreservesTransitions :=
  (probeWithRun_quoteDropOnly.keptWeight base).regions_not_preserves
    (presentation := runPresentation) (data := ["Atom", "CandidateName"])
    (active := ["Process"]) probeWithRun_headedIn_process (by decide) map
    tableEvaluator_discards (term := (⟨∅, Dedukti.omega⟩ : Tabled))
    (next := (⟨∅, Dedukti.omega⟩ : Tabled)) ⟨rfl, omega_step _⟩

/-- **Negative**: so that reading is no host of the theories given by a
table, with all their contexts, under any evaluator. -/
theorem regionRun_not_hostedBy_tableEvaluator (base : BasePremiseEvaluator) :
    ¬ HostedBy tableEvaluator (regionRun base) :=
  fun ⟨map, hosting⟩ => regionRun_not_preserves_tableEvaluator base map hosting.preserves

/-! ## The kernel over a model, with every hole free -/

/-- **The cartesian reading of the kernel over a model hosts no framework one
of whose types has two closed terms that are not convertible.**  Its contexts
are the projections and the terms. -/
theorem cartesianKernel_not_hosting_framework (model : Model) {B : Type}
    (signature : Signature B) {type : Ty B} {first second : Closed signature type}
    (apart : ¬ Conv first second)
    (map : ContextMap (frameworkTheory signature) (kernelReading model).cartesianReading) :
    ¬ map.Hosting :=
  not_hosting_framework_of_multiplicitySize
    (ContextTheory.termsAloneCartesianSize (kernelGSLT model)) signature apart map

/-- **Nor does the cartesian reading of the kernel over a query-first model
receive a transition-preserving map from the rule-table evaluator.** -/
theorem cartesianKernel_not_preserves_tableEvaluator (model : QueryFirstModel)
    (map : ContextMap tableEvaluator (kernelReading model.toAssemblyModel).cartesianReading) :
    ¬ map.PreservesTransitions :=
  Dedukti.tableEvaluator_not_preserves_into_rank
    ((queryFirstKernelRank model).regionReading fun _ => True) map

#print axioms probeData_static
#print axioms presented_toCartesian_not_exhausting
#print axioms regionProbe_toCartesian_not_exhausting
#print axioms twoAxiomsFramework_not_multiplicitySize
#print axioms presented_not_applies
#print axioms presented_not_discards
#print axioms regionProbe_discards_iff
#print axioms regionProbe_copies_iff
#print axioms region_has_linear_lacks
#print axioms cartesian_has_region_lacks
#print axioms intoCartesianProbe
#print axioms intoRegionProbe
#print axioms presented_not_identity_into_regions
#print axioms frameworkTheory_applies
#print axioms not_hosting_framework_of_multiplicitySize
#print axioms cartesianProbe_not_hosting_framework
#print axioms cartesianProbe_not_hostOf_countableFramework_contexts
#print axioms cartesianProbe_not_preserves_tableEvaluator
#print axioms cartesianProbe_not_hostedBy_tabular
#print axioms cartesianProbe_not_hostOf_tabular_contexts
#print axioms regionProbe_data_of_tableEvaluator
#print axioms regionProbe_not_preserves_tableEvaluator
#print axioms regionProbe_data_of_framework
#print axioms regionProbe_not_hosting_framework
#print axioms regionRun_not_preserves_tableEvaluator
#print axioms regionRun_not_hostedBy_tableEvaluator
#print axioms cartesianKernel_not_hosting_framework
#print axioms cartesianKernel_not_preserves_tableEvaluator

end Mettapedia.Logic.HostingStyles.ContextReadings
