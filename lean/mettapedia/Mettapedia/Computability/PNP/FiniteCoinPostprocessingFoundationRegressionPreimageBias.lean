import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# Preimage and signed-bias regression checks for finite-coin postprocessing foundations
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression

open Mettapedia.Computability.PNP

theorem fiber_balanced_constant_regression
    {Coin β : Type*} [Fintype Coin] [DecidableEq β] (z : β) :
    FiniteCoinRecodingFiberBalanced (fun _b (_c : Coin) => z) := by
  exact finiteCoinRecodingFiberBalanced_constant z

theorem true_fiber_count_postcompose_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinTrueFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinTrueFiberCount r y := by
  exact coinTrueFiberCount_postcompose_eq_sum_preimage r g z

theorem false_fiber_count_postcompose_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinFalseFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinFalseFiberCount r y := by
  exact coinFalseFiberCount_postcompose_eq_sum_preimage r g z

theorem signed_fiber_bias_postcompose_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinSignedFiberBias (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y := by
  exact finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z

theorem fiber_balanced_iff_signed_bias_zero_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      ∀ y : α, finiteCoinSignedFiberBias r y = 0 := by
  exact finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero r

theorem signed_fiber_bias_sum_preimage_zero_of_postcompose_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) (z : β) :
    (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) = 0 := by
  exact finiteCoinSignedFiberBias_sum_preimage_eq_zero_of_postcompose_fiberBalanced
    r g hbal z

theorem fiber_balanced_postcompose_iff_signed_bias_sum_preimage_zero_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 := by
  exact
    finiteCoinRecodingFiberBalanced_postcompose_iff_forall_sum_signedFiberBias_preimage_eq_zero
      r g

theorem fiber_imbalance_postcompose_le_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinFiberImbalance (fun b c => g (r b c)) z ≤
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y := by
  exact finiteCoinFiberImbalance_postcompose_le_sum_preimage r g z

theorem output_tolerance_postcompose_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m τ : Nat}
    (hbound : finiteOutputMapFiberCardBound g m)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) := by
  exact countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    r g hbound happrox

theorem output_tolerance_postcompose_card_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (Fintype.card α * τ) := by
  exact countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_card
    r g happrox

theorem output_defect_postcompose_le_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m : Nat}
    (hbound : finiteOutputMapFiberCardBound g m) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    m *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le
    r g hbound

theorem output_defect_postcompose_le_card_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    Fintype.card α *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le_card
    r g

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression
