import Mettapedia.OSLF.Syntax.RhoScopedFiniteSuccessors

/-!
# Exact reflection outcomes and the communication-only boundary

An isolated dropped name admits precisely its complete quotation-origin
fibre when reflection is permitted. It admits no communication reaction.
In particular name eta creates a self outcome for every dropped open name;
an exposed quoted body supplies the other, distinct process outcome.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedDropSuccessors

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoIntrinsicCanonicalBag RhoScopedParallelInventory RhoScopedConstructorInventory
open RhoScopedReactionReadout RhoScopedFiniteReactions RhoScopedFiniteSuccessors
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoCanonicalNamePairs

local instance (context : Ctx sig) : DecidableEq (Reading context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

theorem fits_drop_iff {context : Ctx sig} (name : Name context) (reading : Reading context) :
    fits (drop name) reading ↔
      ∃ payload : Process context, reading = .reflection payload ∧ quote payload = name := by
  constructor
  · intro included
    have patterns := components_le included
    rw [drop_components] at patterns
    cases reading with
    | communication channel payload continuation =>
        change components (join (outputClass channel payload) (inputClass channel continuation)) ≤ _
          at patterns
        rw [join_components, output_components, input_components] at patterns
        have count := Multiset.card_le_card patterns
        simp only [Multiset.card_add, Multiset.card_singleton] at count
        omega
    | reflection payload =>
        change components (drop (quote payload)) ≤ _ at patterns
        rw [drop_components] at patterns
        have same : dropPattern (quote payload) = dropPattern name :=
          Multiset.mem_singleton.mp (Multiset.mem_of_le patterns (by simp [dropPattern]))
        exact ⟨payload, rfl, dropPattern_injective context same⟩
  · rintro ⟨payload, rfl, nameRead⟩
    change read (drop (quote payload)) ≤ read (drop name)
    rw [nameRead]

theorem reflection_outcome {context : Ctx sig} (name : Name context) (payload : Process context)
    (nameRead : quote payload = name) :
    missing (drop name) (.reflection payload) = zero context ∧
      outcome (drop name) (.reflection payload) = payload := by
  simp only [missing, outcome, RhoScopedFiniteSuccessors.residual, Reading.source,
    Reading.target, nameRead, tsub_self, write_zero, join_zero_right, and_self]

theorem mem_drop_successors {context : Ctx sig} (admitted : SourceRule → Prop)
    (name : Name context) (second : Process context) :
    second ∈ successors admitted (drop name) (zero context) ↔
      admitted .reflection ∧ second ∈ RhoFiniteQuotationOrigins.origins name := by
  classical
  rw [successors, Finset.mem_image]
  constructor
  · rintro ⟨reading, member, targetRead⟩
    obtain ⟨catalogued, _least⟩ := Finset.mem_filter.mp member
    obtain ⟨included, allowed⟩ := (mem_catalogue admitted _ reading).mp catalogued
    rw [join_zero_right] at included
    obtain ⟨payload, rfl, nameRead⟩ := (fits_drop_iff name reading).mp included
    have target : payload = second := (reflection_outcome name payload nameRead).2.symm.trans targetRead
    rw [← target]
    exact ⟨allowed, (RhoFiniteQuotationOrigins.quotation_fibre_iff name payload).mp nameRead⟩
  · rintro ⟨allowed, member⟩
    have nameRead := (RhoFiniteQuotationOrigins.quotation_fibre_iff name second).mpr member
    refine ⟨.reflection second, ?_, (reflection_outcome name second nameRead).2⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_catalogue admitted _ _).mpr ⟨?_, allowed⟩,
      (reflection_outcome name second nameRead).1⟩
    rw [join_zero_right]
    exact (fits_drop_iff name _).mpr ⟨second, rfl, nameRead⟩

theorem reflection_successors {context : Ctx sig} (name : Name context) :
    successors withReflection (drop name) (zero context) =
      RhoFiniteQuotationOrigins.origins name := by
  classical
  ext second
  simp only [mem_drop_successors, withReflection, true_and]

theorem core_drop_successors_empty {context : Ctx sig} (name : Name context) :
    successors core (drop name) (zero context) = ∅ := by
  classical
  ext second
  simp only [mem_drop_successors, core, false_and, Finset.notMem_empty]

theorem original_eta_self_outcome {context : Ctx sig} (name : Name context) :
    drop name ∈ successors withReflection (drop name) (zero context) := by
  rw [reflection_successors]
  exact (RhoFiniteQuotationOrigins.quotation_fibre_iff name (drop name)).mp (quote_drop name)

theorem original_reflection_at_most_two {context : Ctx sig} (name : Name context) :
    (successors withReflection (drop name) (zero context)).card ≤ 2 := by
  rw [reflection_successors]
  exact RhoFiniteQuotationOrigins.origins_card_le_two name

end Mettapedia.OSLF.Binding.RhoScopedDropSuccessors
