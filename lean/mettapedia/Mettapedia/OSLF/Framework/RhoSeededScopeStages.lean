import Mettapedia.OSLF.Syntax.RhoCanonicalNamePairs
import Mettapedia.OSLF.Framework.RhoScopeSeedReadings
import Mettapedia.OSLF.Framework.GeneratorLength
import Mathlib.Data.Finset.Sym

/-!
# Actual finite strata of the seeded rho scope

The two distinct atomic name seeds and the injective unordered-pair constructor
form finite sets of actual source equation classes. Seed names are disjoint
from compound names. Their earned finite-set cardinality obeys the manuscript
recurrence, including repeated unordered pairs. Arithmetic is read from these
sets by proof; the large strata need not be enumerated to establish the counts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeStages

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoCanonicalNamePairs

local instance nameClassDecision : DecidableEq (Name []) := equationClassDecision [] Srt.nm

def seeds : Finset (Name []) := {quote (zero []), quote visible}

theorem mem_seeds (name : Name []) :
    name ∈ seeds ↔ name = quote (zero []) ∨ name = quote visible := by simp [seeds]

theorem seeds_card : seeds.card = 2 :=
  Finset.card_pair (Ne.symm RhoScopeQuotientControls.quoted_output_not_null)

def products (names : Finset (Name [])) : Finset (Name []) := names.sym2.image pairConstructor

theorem pair_not_mem_seeds (pair : Sym2 (Name [])) : pairConstructor pair ∉ seeds := by
  refine Sym2.inductionOn pair ?_
  intro first second
  rw [pairConstructor_mk, mem_seeds]
  exact fun member => member.elim (combine_ne_null first second) (combine_ne_output first second)

theorem seeds_disjoint_products (names : Finset (Name [])) : Disjoint seeds (products names) := by
  apply Finset.disjoint_left.mpr
  intro name seeded produced
  obtain ⟨pair, _, readout⟩ := Finset.mem_image.mp produced
  have excluded := pair_not_mem_seeds pair
  rw [readout] at excluded
  exact excluded seeded

theorem products_card (names : Finset (Name [])) :
    (products names).card = Nat.choose (names.card + 1) 2 := by
  rw [products, Finset.card_image_of_injective _ (pairConstructor_injective []), Finset.card_sym2]

theorem products_mono {first second : Finset (Name [])} (included : first ⊆ second) :
    products first ⊆ products second := Finset.image_subset_image (Finset.sym2_mono included)

def stage : Nat → Finset (Name [])
  | 0 => seeds
  | depth + 1 => seeds ∪ products (stage depth)

theorem stage_zero_card : (stage 0).card = 2 := seeds_card

theorem stage_succ_card (depth : Nat) :
    (stage (depth + 1)).card = 2 + Nat.choose ((stage depth).card + 1) 2 := by
  rw [stage, Finset.card_union_of_disjoint (seeds_disjoint_products _), seeds_card, products_card]

theorem stage_step_subset (depth : Nat) : stage depth ⊆ stage (depth + 1) := by
  induction depth with
  | zero => exact Finset.subset_union_left
  | succ depth ih => exact Finset.union_subset_union (Finset.Subset.refl seeds) (products_mono ih)

theorem stage_monotone : Monotone stage := monotone_nat_of_le_succ stage_step_subset

theorem stage_card_eq_manuscript (depth : Nat) : (stage depth).card = GeneratorLength.stratum depth := by
  induction depth with
  | zero => exact stage_zero_card
  | succ depth ih =>
    rw [stage_succ_card, GeneratorLength.stratum_succ_eq_choose, ih]

theorem actual_first_six_cardinalities :
    (List.range 6).map (fun depth => (stage depth).card) = [2, 5, 17, 155, 12092, 73114280] := by
  have readout : (fun depth => (stage depth).card) = GeneratorLength.stratum :=
    funext stage_card_eq_manuscript
  rw [readout]
  exact GeneratorLength.stratum_values

theorem mem_products (names : Finset (Name [])) (name : Name []) :
    name ∈ products names ↔ ∃ first second,
      first ∈ names ∧ second ∈ names ∧ combine first second = name := by
  constructor
  · intro member
    obtain ⟨pair, admitted, readout⟩ := Finset.mem_image.mp member
    revert admitted readout
    refine Sym2.inductionOn pair ?_
    intro first second admitted readout
    exact ⟨first, second, (Finset.mk_mem_sym2_iff.mp admitted).1,
      (Finset.mk_mem_sym2_iff.mp admitted).2, readout⟩
  · rintro ⟨first, second, firstMember, secondMember, rfl⟩
    exact Finset.mem_image.mpr ⟨Sym2.mk first second,
      Finset.mk_mem_sym2_iff.mpr ⟨firstMember, secondMember⟩, rfl⟩

theorem mem_stage_succ (depth : Nat) (name : Name []) :
    name ∈ stage (depth + 1) ↔
      name = quote (zero []) ∨ name = quote visible ∨
        ∃ first second, first ∈ stage depth ∧ second ∈ stage depth ∧ combine first second = name := by
  rw [stage, Finset.mem_union, mem_seeds, mem_products]
  exact or_assoc

end Mettapedia.OSLF.Framework.RhoSeededScopeStages
