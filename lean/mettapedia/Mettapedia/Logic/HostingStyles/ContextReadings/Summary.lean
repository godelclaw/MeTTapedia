import Mettapedia.Logic.HostingStyles.ContextReadings.ProofSystemsAsData
import Mettapedia.Logic.HostingStyles.ContextReadings.SeparateSort
import Mettapedia.Logic.HostingStyles.ContextReadings.RawPatterns

/-!
# The linear, the cartesian and the region reading of the candidate: one table

The candidate presentation is read three ways (`ProbeReadings`): with its
contexts as they are, each hole used once; with every hole free to be used
any number of times; and with regions, where atoms and names are free and
everything else is used once.  Each row names the theorem that is the
conjunction of its three cells.  The rows on discarding and copying are stated
at the closed atoms and the closed processes; their general statements, among
the inhabited interfaces, are `presented_not_discards`,
`regionProbe_discards_iff`, `ContextTheory.cartesianReading_discards` and
their companions for copying.

| | linear | regions (atoms, names free) | cartesian |
|---|---|---|---|
| discards (`probe_discards_row`) | at no inhabited interface | at atoms and names, not at processes | everywhere |
| copies (`probe_copies_row`) | at no inhabited interface | at atoms and names, not at processes | everywhere |
| proof systems with their derived rules (`numberedProofSystems_separate_readings`) | no map from a system with a derivation | hosted, as atoms | hosted, as atoms |
| the framework with rules as constants (`probe_framework_row`) | no map at all | a map exists; every type with a term goes to data; not hosted when a type has two terms that are not convertible | a map exists; not hosted when a type has two terms that are not convertible |
| the rule-table evaluator (`probe_tableEvaluator_row`) | no map at all | a map exists; its terms go to data, so no step is preserved | a map exists; no step is preserved, the candidate has a rank |
| the same, the candidate with a run constructor, under every evaluator (`run_tableEvaluator_row`) | no map at all | not hosted | not hosted |
| what filling conserves (`linear_fill_tokens`, `reading_fill_tokens`) | every count of tokens: each filling once | each filling of a hole that is not data once | each filling as often as its hole occurs |

Between the readings themselves: the identity on terms goes from the linear
reading and from the reading with regions into the cartesian one, hosting and
not exhausting (`presented_toCartesian_not_exhausting`,
`regionProbe_toCartesian_not_exhausting`).  From the linear reading into the
reading with regions no map is the identity on the closed atoms and the closed
processes (`presented_not_identity_into_regions`).

What decides each cell:

* a context that discards or copies comes from the static equivalence: an
  erasing or a copying equation gives one, and a weight that every generator
  keeps excludes both (`EquationShapes`);
* a reading may use a hole of a declared interface any number of times, and a
  context into a declared interface has declared holes only (`Readings`);
* a context of a reading places its fillings in a pattern, so it cannot apply
  one filling to another (`Multiplicity`): that excludes the framework, whose
  conversion computes;
* data does not reduce, and a source that discards is received as data
  (`PresentedReadings`): that excludes the evaluator from the regions;
* no constructor takes a process, so a context cannot hold two terms that
  reduce (`SeparateSort`): that excludes the evaluator from every reading of
  the candidate with a run constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti (tableEvaluator Tabled)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Framework

/-- **Where the three readings discard.** -/
theorem probe_discards_row (base : BasePremiseEvaluator) :
    (¬ (presentedReading base).Discards closedAtom ∧
        ¬ (presentedReading base).Discards closedProcess) ∧
      ((regionProbe base).Discards closedAtom ∧ ¬ (regionProbe base).Discards closedProcess) ∧
        ((cartesianProbe base).Discards closedAtom ∧ (cartesianProbe base).Discards closedProcess) :=
  ⟨⟨presented_not_discards base unitTerm, presented_not_discards base needAnswerTerm⟩,
    ⟨(regionProbe_discards_iff base unitTerm).mpr probeData_closedAtom,
      fun discards => not_probeData_closedProcess
        ((regionProbe_discards_iff base needAnswerTerm).mp discards)⟩,
    ⟨ContextTheory.cartesianReading_discards (presentedReading base) closedAtom,
      ContextTheory.cartesianReading_discards (presentedReading base) closedProcess⟩⟩

/-- **Where the three readings copy.** -/
theorem probe_copies_row (base : BasePremiseEvaluator) :
    (¬ (presentedReading base).Copies closedAtom ∧
        ¬ (presentedReading base).Copies closedProcess) ∧
      ((regionProbe base).Copies closedAtom ∧ ¬ (regionProbe base).Copies closedProcess) ∧
        ((cartesianProbe base).Copies closedAtom ∧ (cartesianProbe base).Copies closedProcess) :=
  ⟨⟨presented_not_copies base unitTerm, presented_not_copies base needAnswerTerm⟩,
    ⟨(regionProbe_copies_iff base unitTerm).mpr probeData_closedAtom,
      fun copies => not_probeData_closedProcess
        ((regionProbe_copies_iff base needAnswerTerm).mp copies)⟩,
    ⟨ContextTheory.cartesianReading_copies (presentedReading base) closedAtom,
      ContextTheory.cartesianReading_copies (presentedReading base) closedProcess⟩⟩

/-- **What the three readings receive from a framework** one of whose types
has two closed terms that are not convertible. -/
theorem probe_framework_row (base : BasePremiseEvaluator) {B : Type} (signature : Signature B)
    {type : Ty B} {first second : Closed signature type} (apart : ¬ Conv first second) :
    IsEmpty (ContextMap (frameworkTheory signature) (presentedReading base)) ∧
      (Nonempty (ContextMap (frameworkTheory signature) (regionProbe base)) ∧
        ∀ map : ContextMap (frameworkTheory signature) (regionProbe base),
          probeData (map.interface type) ∧ ¬ map.Hosting) ∧
        (Nonempty (ContextMap (frameworkTheory signature) (cartesianProbe base)) ∧
          ∀ map : ContextMap (frameworkTheory signature) (cartesianProbe base), ¬ map.Hosting) :=
  ⟨presented_isEmpty_contextMap_framework base signature type,
    ⟨⟨intoRegionProbe base (frameworkTheory signature)⟩,
      fun map => ⟨regionProbe_data_of_framework base signature map first,
        regionProbe_not_hosting_framework base signature apart map⟩⟩,
    ⟨⟨intoCartesianProbe base (frameworkTheory signature)⟩,
      fun map => cartesianProbe_not_hosting_framework base signature apart map⟩⟩

/-- **What the three readings receive from the rule-table evaluator.** -/
theorem probe_tableEvaluator_row (base : BasePremiseEvaluator) :
    IsEmpty (ContextMap tableEvaluator (presentedReading base)) ∧
      (Nonempty (ContextMap tableEvaluator (regionProbe base)) ∧
        ∀ map : ContextMap tableEvaluator (regionProbe base),
          probeData (map.interface ()) ∧ ¬ map.PreservesTransitions) ∧
        (Nonempty (ContextMap tableEvaluator (cartesianProbe base)) ∧
          ∀ map : ContextMap tableEvaluator (cartesianProbe base), ¬ map.PreservesTransitions) :=
  ⟨presented_isEmpty_contextMap_tableEvaluator base,
    ⟨⟨intoRegionProbe base tableEvaluator⟩,
      fun map => ⟨regionProbe_data_of_tableEvaluator base map,
        regionProbe_not_preserves_tableEvaluator base map⟩⟩,
    ⟨⟨intoCartesianProbe base tableEvaluator⟩,
      fun map => cartesianProbe_not_preserves_tableEvaluator base map⟩⟩

/-- **The same for the candidate with a run constructor, under every
evaluator of its premises**: its hosting of the theories given by a table on
terms lifts to contexts under none of the three readings. -/
theorem run_tableEvaluator_row (base : BasePremiseEvaluator) :
    IsEmpty (ContextMap tableEvaluator (contextTheory base runPresentation)) ∧
      (∀ map : ContextMap tableEvaluator (regionRun base), ¬ map.Hosting) ∧
        ∀ map : ContextMap tableEvaluator (contextTheory base runPresentation).cartesianReading,
          ¬ map.Hosting :=
  ⟨(runLinearSize base).isEmpty_contextMap_of_discards tableEvaluator_discards
      ⟨(⟨∅, .srt .type⟩ : Tabled)⟩,
    fun map => readingRun_not_hosting_tableEvaluator base probeData map,
    fun map => readingRun_not_hosting_tableEvaluator base (fun _ => True) map⟩

#print axioms probe_discards_row
#print axioms probe_copies_row
#print axioms probe_framework_row
#print axioms probe_tableEvaluator_row
#print axioms run_tableEvaluator_row

end Mettapedia.Logic.HostingStyles.ContextReadings
