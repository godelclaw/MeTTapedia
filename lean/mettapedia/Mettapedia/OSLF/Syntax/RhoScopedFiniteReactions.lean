import Mettapedia.OSLF.Syntax.RhoScopedReactionReadout
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite endpoint readings of original scoped rho reactions

The source is the complete sorted equation quotient, with open continuations
and the separate reflection rule. Communication arguments occur in its finite
parallel inventory. Every reflected name has at most two process origins.
These facts earn finiteness of all inventory-bounded endpoint readings;
finiteness of the original authored receipt fibre is not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedFiniteReactions

open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoEquationConstructorControls
open RhoIntrinsicCanonicalBag RhoScopedParallelInventory RhoScopedConstructorInventory
open RhoScopedReactionReadout RhoCanonicalNamePairs

def fits {context : Ctx sig} (whole : Process context) (reading : Reading context) : Prop :=
  read reading.source ≤ read whole

/-- Independently formed finite constructor and quotation-origin candidates. -/
def candidates {context : Ctx sig} (whole : Process context) : Set (Reading context) :=
  (fun pair : Input context × Output context =>
    Reading.communication pair.1.1 pair.2.2 pair.1.2) '' (inputs whole ×ˢ outputs whole) ∪
  ⋃ name ∈ drops whole,
    Reading.reflection '' (RhoFiniteQuotationOrigins.origins name : Set (Process context))

theorem candidates_finite {context : Ctx sig} (whole : Process context) :
    (candidates whole).Finite := by
  apply Set.Finite.union
  · exact ((inputs_finite whole).prod (outputs_finite whole)).image _
  · exact (drops_finite whole).biUnion (fun name _ =>
      (RhoFiniteQuotationOrigins.origins name).finite_toSet.image _)

theorem fits_mem_candidates {context : Ctx sig} (whole : Process context)
    (reading : Reading context) (included : fits whole reading) :
    reading ∈ candidates whole := by
  have patternInclusion := components_le included
  cases reading with
  | communication channel payload continuation =>
      change components (join (outputClass channel payload) (inputClass channel continuation)) ≤
        components whole at patternInclusion
      rw [join_components, output_components, input_components] at patternInclusion
      have outputMember : (channel, payload) ∈ outputs whole :=
        Multiset.mem_of_le patternInclusion (by simp)
      have inputMember : (channel, continuation) ∈ inputs whole :=
        Multiset.mem_of_le patternInclusion (by simp)
      exact Or.inl ⟨((channel, continuation), (channel, payload)),
        ⟨inputMember, outputMember⟩, rfl⟩
  | reflection payload =>
      change components (drop (quote payload)) ≤ components whole at patternInclusion
      rw [drop_components] at patternInclusion
      have nameMember : quote payload ∈ drops whole :=
        Multiset.mem_of_le patternInclusion (by simp [dropPattern])
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨quote payload, Set.mem_iUnion.mpr
        ⟨nameMember, ⟨payload,
          (RhoFiniteQuotationOrigins.quotation_fibre_iff (quote payload) payload).mp rfl, rfl⟩⟩⟩

/-- No restriction on the ambient scope or quotation safety is needed. -/
theorem readings_finite {context : Ctx sig} (whole : Process context) :
    {reading | fits whole reading}.Finite :=
  (candidates_finite whole).subset (fun _ included => fits_mem_candidates whole _ included)

def admittedReadings {context : Ctx sig} (admitted : RhoScopedParallelEvents.SourceRule → Prop)
    (whole : Process context) : Set (Reading context) :=
  {reading | fits whole reading ∧ admitted reading.rule}

theorem admittedReadings_finite {context : Ctx sig}
    (admitted : RhoScopedParallelEvents.SourceRule → Prop) (whole : Process context) :
    (admittedReadings admitted whole).Finite :=
  (readings_finite whole).subset (fun _ included => included.1)

/-- The catalogue is exact on reading classes; original assignments remain
in the corresponding `Receipt` fibres. -/
noncomputable def catalogue {context : Ctx sig}
    (admitted : RhoScopedParallelEvents.SourceRule → Prop) (whole : Process context) :
    Finset (Reading context) := (admittedReadings_finite admitted whole).toFinset

theorem mem_catalogue {context : Ctx sig}
    (admitted : RhoScopedParallelEvents.SourceRule → Prop) (whole : Process context)
    (reading : Reading context) :
    reading ∈ catalogue admitted whole ↔ fits whole reading ∧ admitted reading.rule :=
  Set.Finite.mem_toFinset _

theorem supplied_root_mem_catalogue {context : Ctx sig}
    {admitted : RhoScopedParallelEvents.SourceRule → Prop} (whole : Process context)
    (root : RhoScopedParallelEvents.Root RhoScopedParallelEvents.sourceRules admitted context)
    (included : read root.source ≤ read whole) :
    rootReading root ∈ catalogue admitted whole := by
  rw [mem_catalogue]
  constructor
  · simpa only [fits, rootReading_source] using included
  · rw [rootReading_rule]
    exact root.1.property

theorem catalogue_realization {context : Ctx sig}
    (admitted : RhoScopedParallelEvents.SourceRule → Prop) (whole : Process context)
    (reading : Reading context) (member : reading ∈ catalogue admitted whole) :
    ∃ root : RhoScopedParallelEvents.Root RhoScopedParallelEvents.sourceRules admitted context,
      rootReading root = reading ∧ read root.source ≤ read whole := by
  obtain ⟨included, allowed⟩ := (mem_catalogue admitted whole reading).mp member
  refine ⟨realize admitted reading allowed, rootReading_realize _ _ _, ?_⟩
  simpa only [fits, realize_source] using included

end Mettapedia.OSLF.Binding.RhoScopedFiniteReactions
