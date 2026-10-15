import Mettapedia.GSLT.Weighting.ConfiguredFundingRates
import Mettapedia.GSLT.Weighting.DynamicWeights

/-!
# Actual configuration funding distinguishes rates from prices

The existing two-update example reaches one term with rates four and three.
Both supplied events have an actual paid history under a common unit price.
A map-sensitive price admits just one of them at budget three. A zero rate
does not remove the paid history, while an empty purse removes its funding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.ConfiguredFundingControls

open ConfiguredFunding DynamicWeights

noncomputable section

def fixedPrice : (Σ site, keys.Key site) → WeightMap keys ℚ → Nat := fun _ _ => 1

def mapPrice : (Σ site, keys.Key site) → WeightMap keys ℚ → Nat :=
  fun _ weights => if weights aKey = 4 then 4 else 3

def firstFiring : Firing keys ℚ lastRedex.site := firingOf aThenB lastRedex

def secondFiring : Firing keys ℚ lastRedex.site := firingOf bThenA lastRedex

theorem first_paid : Nonempty (PaidHistory augmented fixedPrice firstFiring 1) := by
  apply (paid_history_iff augmented fixedPrice firstFiring 1).mpr
  exact le_rfl

theorem second_paid : Nonempty (PaidHistory augmented fixedPrice secondFiring 1) := by
  apply (paid_history_iff augmented fixedPrice secondFiring 1).mpr
  exact le_rfl

theorem actual_paid_rates :
    fundedRate augmented fixedPrice aThenB 1 lastRedex = 4 ∧
      fundedRate augmented fixedPrice bThenA 1 lastRedex = 3 := by
  obtain ⟨first⟩ := first_paid
  obtain ⟨second⟩ := second_paid
  constructor
  · rw [fundedRate_of_paid augmented first]
    change aThenB aKey * 1 = 4
    rw [mul_one, aThenB_a]
  · rw [fundedRate_of_paid augmented second]
    change bThenA aKey * 1 = 3
    rw [mul_one, bThenA_a]

theorem same_program_different_actual_funding :
    (before firstFiring).1 = (before secondFiring).1 ∧
    (after augmented firstFiring).1 = (after augmented secondFiring).1 ∧
    ¬ Nonempty (PaidHistory augmented mapPrice firstFiring 3) ∧
    Nonempty (PaidHistory augmented mapPrice secondFiring 3) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [paid_history_iff]
    change ¬ (if aThenB aKey = 4 then 4 else 3) ≤ 3
    simp only [aThenB_a]
    decide
  · rw [paid_history_iff]
    change (if bThenA aKey = 4 then 4 else 3) ≤ 3
    rw [bThenA_a]
    norm_num

theorem distinct_configured_origins : firstFiring ≠ secondFiring := by
  intro same
  have equal : aThenB aKey = bThenA aKey :=
    congrArg (fun firing : Firing keys ℚ lastRedex.site => firing.weights aKey) same
  rw [aThenB_a, bThenA_a] at equal
  norm_num at equal

theorem empty_purse_blocks_positive_rates :
    ¬ Nonempty (PaidHistory augmented fixedPrice firstFiring 0) ∧
    fundedRate augmented fixedPrice aThenB 0 lastRedex = 0 := by
  have noFunding : ¬ Nonempty (PaidHistory augmented fixedPrice firstFiring 0) := by
    rw [paid_history_iff]
    change ¬ (1 ≤ 0)
    decide
  exact ⟨noFunding, fundedRate_of_unfunded augmented noFunding⟩

def zeroMap : WeightMap keys ℚ := fun _ => 0

theorem zero_rate_retains_a_funded_history :
    Nonempty (PaidHistory augmented fixedPrice (firingOf zeroMap lastRedex) 1) ∧
    fundedRate augmented fixedPrice zeroMap 1 lastRedex = 0 := by
  have funding : Nonempty (PaidHistory augmented fixedPrice (firingOf zeroMap lastRedex) 1) :=
    (paid_history_iff augmented fixedPrice _ _).mpr (le_refl 1)
  refine ⟨funding, ?_⟩
  obtain ⟨paid⟩ := funding
  rw [fundedRate_of_paid augmented paid]
  exact zero_mul _

end

end Mettapedia.GSLT.Weighting.ConfiguredFundingControls
