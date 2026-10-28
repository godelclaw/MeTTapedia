import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite-coin postprocessing: signed-bias accounting

Signed fiber-bias, preimage-sum, collision, and opposite-bias accounting lemmas
for deterministic postprocessing.
-/

namespace Mettapedia.Computability.PNP

/-- A constant output is always balanced: this is the degenerate many-to-one
postprocessing endpoint that erases all finite-coin source information. -/
theorem finiteCoinRecodingFiberBalanced_constant
    {Coin β : Type*} [Fintype Coin] [DecidableEq β] (z : β) :
    FiniteCoinRecodingFiberBalanced (fun _b (_c : Coin) => z) := by
  intro y
  rfl

/-- The true-side fiber count after postprocessing is the sum of the true-side
counts over the original outputs merged into that postprocessed value. -/
theorem coinTrueFiberCount_postcompose_eq_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinTrueFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinTrueFiberCount r y := by
  classical
  simpa [finiteOutputPreimageFiber, coinTrueFiberCount] using
    (finiteEventCount_comp_eq_sum_fibers_of_mapsTo
      (fun c : Coin => r true c)
      (Finset.univ : Finset α)
      (fun y : α => g y = z)
      (by intro c; simp))

/-- The false-side fiber count after postprocessing is the sum of the false-side
counts over the original outputs merged into that postprocessed value. -/
theorem coinFalseFiberCount_postcompose_eq_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinFalseFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinFalseFiberCount r y := by
  classical
  simpa [finiteOutputPreimageFiber, coinFalseFiberCount] using
    (finiteEventCount_comp_eq_sum_fibers_of_mapsTo
      (fun c : Coin => r false c)
      (Finset.univ : Finset α)
      (fun y : α => g y = z)
      (by intro c; simp))

/-- The signed true-minus-false finite-coin fiber bias.  Balance is exactly the
vanishing of this integer-valued bias at every output. -/
def finiteCoinSignedFiberBias {Coin α : Type*} [Fintype Coin]
    [DecidableEq α] (r : Bool → Coin → α) (y : α) : Int :=
  (coinTrueFiberCount r y : Int) - (coinFalseFiberCount r y : Int)

/-- The signed bias of a postprocessed output is the sum of the signed biases
of the original outputs merged into it. -/
theorem finiteCoinSignedFiberBias_postcompose_eq_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinSignedFiberBias (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y := by
  classical
  unfold finiteCoinSignedFiberBias
  rw [coinTrueFiberCount_postcompose_eq_sum_preimage r g z,
    coinFalseFiberCount_postcompose_eq_sum_preimage r g z]
  simp [Nat.cast_sum, Finset.sum_sub_distrib]

/-- Balanced finite-coin fibers are exactly the outputs with zero signed bias. -/
theorem finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      ∀ y : α, finiteCoinSignedFiberBias r y = 0 := by
  constructor
  · intro h y
    simp [finiteCoinSignedFiberBias, h y]
  · intro h y
    have hz := h y
    unfold finiteCoinSignedFiberBias at hz
    omega

/-- If deterministic postprocessing has balanced fibers, then every
postprocessed fiber has exact zero total signed original bias. -/
theorem finiteCoinSignedFiberBias_sum_preimage_eq_zero_of_postcompose_fiberBalanced
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) (z : β) :
    (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) = 0 := by
  rw [← finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z]
  exact
    (finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
      (fun b c => g (r b c))).mp hbal z

/-- Deterministic postprocessing creates balanced finite-coin fibers exactly
when every postprocessed fiber has zero total signed original bias.  Any repair
via coarsening must therefore supply exact cancellation in every merged fiber,
not merely a collision. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_forall_sum_signedFiberBias_preimage_eq_zero
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 := by
  rw [finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
    (fun b c => g (r b c))]
  constructor
  · intro h z
    have hz := h z
    rw [finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z] at hz
    exact hz
  · intro h z
    rw [finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z]
    exact h z

/-- If a true-heavy original output becomes part of a balanced postprocessed
fiber, that same postprocessed fiber must contain a false-heavy original
output.  Thus a successful coarsening repair cannot use only same-bias
collisions. -/
theorem exists_falseHeavy_output_in_postprocessedFiber_of_trueHeavy
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yTrue : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue) :
    ∃ yFalse : α,
      g yFalse = g yTrue ∧ yFalse ≠ yTrue ∧
        coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  classical
  let s := finiteOutputPreimageFiber g (g yTrue)
  by_contra hnone
  have hle :
      ∀ y ∈ s, coinFalseFiberCount r y ≤ coinTrueFiberCount r y := by
    intro y hy
    by_cases hyEq : y = yTrue
    · subst y
      exact Nat.le_of_lt hheavy
    · exact le_of_not_gt (fun hgt => by
        have hgy : g y = g yTrue := by
          simpa [s, finiteOutputPreimageFiber] using hy
        exact hnone ⟨y, hgy, hyEq, hgt⟩)
  have hyTrueMem : yTrue ∈ s := by
    simp [s, finiteOutputPreimageFiber]
  have hsum_lt :
      (∑ y ∈ s, coinFalseFiberCount r y) <
        ∑ y ∈ s, coinTrueFiberCount r y := by
    exact Finset.sum_lt_sum hle ⟨yTrue, hyTrueMem, hheavy⟩
  have htrue := coinTrueFiberCount_postcompose_eq_sum_preimage r g (g yTrue)
  have hfalse := coinFalseFiberCount_postcompose_eq_sum_preimage r g (g yTrue)
  have hsum_eq :
      (∑ y ∈ s, coinTrueFiberCount r y) =
        ∑ y ∈ s, coinFalseFiberCount r y := by
    calc
      (∑ y ∈ s, coinTrueFiberCount r y)
          = coinTrueFiberCount (fun b c => g (r b c)) (g yTrue) := by
            simpa [s] using htrue.symm
      _ = coinFalseFiberCount (fun b c => g (r b c)) (g yTrue) :=
            hbal (g yTrue)
      _ = ∑ y ∈ s, coinFalseFiberCount r y := by
            simpa [s] using hfalse
  rw [hsum_eq] at hsum_lt
  exact (Nat.lt_irrefl _) hsum_lt

/-- The symmetric form: if a false-heavy original output becomes part of a
balanced postprocessed fiber, that same postprocessed fiber must contain a
true-heavy original output. -/
theorem exists_trueHeavy_output_in_postprocessedFiber_of_falseHeavy
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yFalse : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse) :
    ∃ yTrue : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue := by
  classical
  let s := finiteOutputPreimageFiber g (g yFalse)
  by_contra hnone
  have hle :
      ∀ y ∈ s, coinTrueFiberCount r y ≤ coinFalseFiberCount r y := by
    intro y hy
    by_cases hyEq : y = yFalse
    · subst y
      exact Nat.le_of_lt hheavy
    · exact le_of_not_gt (fun hgt => by
        have hgy : g y = g yFalse := by
          simpa [s, finiteOutputPreimageFiber] using hy
        exact hnone ⟨y, hgy, hyEq, hgt⟩)
  have hyFalseMem : yFalse ∈ s := by
    simp [s, finiteOutputPreimageFiber]
  have hsum_lt :
      (∑ y ∈ s, coinTrueFiberCount r y) <
        ∑ y ∈ s, coinFalseFiberCount r y := by
    exact Finset.sum_lt_sum hle ⟨yFalse, hyFalseMem, hheavy⟩
  have htrue := coinTrueFiberCount_postcompose_eq_sum_preimage r g (g yFalse)
  have hfalse := coinFalseFiberCount_postcompose_eq_sum_preimage r g (g yFalse)
  have hsum_eq :
      (∑ y ∈ s, coinTrueFiberCount r y) =
        ∑ y ∈ s, coinFalseFiberCount r y := by
    calc
      (∑ y ∈ s, coinTrueFiberCount r y)
          = coinTrueFiberCount (fun b c => g (r b c)) (g yFalse) := by
            simpa [s] using htrue.symm
      _ = coinFalseFiberCount (fun b c => g (r b c)) (g yFalse) :=
            hbal (g yFalse)
      _ = ∑ y ∈ s, coinFalseFiberCount r y := by
            simpa [s] using hfalse
  rw [hsum_eq] at hsum_lt
  exact (Nat.lt_irrefl _) hsum_lt

/-- If postprocessing balances an originally unbalanced finite-coin recoding,
then some postprocessed fiber must merge a true-heavy original output with a
false-heavy original output.  This is stronger than mere non-injectivity: the
repair must cancel opposite source biases inside one postprocessed value. -/
theorem exists_oppositeBias_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  have hnotall :
      ¬ ∀ y : α, coinTrueFiberCount r y = coinFalseFiberCount r y := hnot
  rcases not_forall.mp hnotall with ⟨y, hne⟩
  rcases lt_or_gt_of_ne hne with htf | hft
  · rcases exists_trueHeavy_output_in_postprocessedFiber_of_falseHeavy
      r g hbal htf with ⟨yTrue, hgy, hne', htrueHeavy⟩
    exact ⟨yTrue, y, hgy, hne', htrueHeavy, htf⟩
  · rcases exists_falseHeavy_output_in_postprocessedFiber_of_trueHeavy
      r g hbal hft with ⟨yFalse, hgy, hne', hfalseHeavy⟩
    exact ⟨y, yFalse, hgy.symm, (fun h => hne' h.symm), hft, hfalseHeavy⟩

/-- A postprocessed fiber's unsigned imbalance is bounded by the sum of the
unsigned imbalances of the original fibers merged into it. -/
theorem finiteCoinFiberImbalance_postcompose_le_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinFiberImbalance (fun b c => g (r b c)) z ≤
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y := by
  classical
  let s := finiteOutputPreimageFiber g z
  have htrue := coinTrueFiberCount_postcompose_eq_sum_preimage r g z
  have hfalse := coinFalseFiberCount_postcompose_eq_sum_preimage r g z
  have hleft :
      (∑ y ∈ s, coinTrueFiberCount r y) -
          (∑ y ∈ s, coinFalseFiberCount r y) ≤
        ∑ y ∈ s, finiteCoinFiberImbalance r y := by
    have hsum :
        (∑ y ∈ s, coinTrueFiberCount r y) ≤
          (∑ y ∈ s, coinFalseFiberCount r y) +
            ∑ y ∈ s, finiteCoinFiberImbalance r y := by
      calc
        (∑ y ∈ s, coinTrueFiberCount r y)
            ≤ ∑ y ∈ s,
                (coinFalseFiberCount r y + finiteCoinFiberImbalance r y) := by
              refine Finset.sum_le_sum ?_
              intro y _hy
              have hgap :
                  coinTrueFiberCount r y - coinFalseFiberCount r y ≤
                    finiteCoinFiberImbalance r y := by
                exact le_max_left _ _
              omega
        _ = (∑ y ∈ s, coinFalseFiberCount r y) +
              ∑ y ∈ s, finiteCoinFiberImbalance r y := by
            rw [Finset.sum_add_distrib]
    omega
  have hright :
      (∑ y ∈ s, coinFalseFiberCount r y) -
          (∑ y ∈ s, coinTrueFiberCount r y) ≤
        ∑ y ∈ s, finiteCoinFiberImbalance r y := by
    have hsum :
        (∑ y ∈ s, coinFalseFiberCount r y) ≤
          (∑ y ∈ s, coinTrueFiberCount r y) +
            ∑ y ∈ s, finiteCoinFiberImbalance r y := by
      calc
        (∑ y ∈ s, coinFalseFiberCount r y)
            ≤ ∑ y ∈ s,
                (coinTrueFiberCount r y + finiteCoinFiberImbalance r y) := by
              refine Finset.sum_le_sum ?_
              intro y _hy
              have hgap :
                  coinFalseFiberCount r y - coinTrueFiberCount r y ≤
                    finiteCoinFiberImbalance r y := by
                exact le_max_right _ _
              omega
        _ = (∑ y ∈ s, coinTrueFiberCount r y) +
              ∑ y ∈ s, finiteCoinFiberImbalance r y := by
            rw [Finset.sum_add_distrib]
    omega
  unfold finiteCoinFiberImbalance
  rw [htrue, hfalse]
  exact max_le hleft hright

end Mettapedia.Computability.PNP
