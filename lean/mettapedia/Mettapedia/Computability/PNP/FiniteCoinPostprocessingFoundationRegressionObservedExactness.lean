import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# Observed-injective exactness regression checks for finite-coin postprocessing foundations
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression

open Mettapedia.Computability.PNP

theorem true_fiber_count_postcompose_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  exact coinTrueFiberCount_postcompose_observedInjective r g hinjObs hobs

theorem false_fiber_count_postcompose_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  exact coinFalseFiberCount_postcompose_observedInjective r g hinjObs hobs

theorem output_tolerance_postcompose_iff_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      r g τ hinjObs

theorem output_tolerance_postcompose_iff_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α) (τ : Nat)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedLeftInverse
      r g recover τ hrecover

theorem output_defect_postcompose_eq_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
    r g hinjObs

theorem output_defect_postcompose_eq_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedLeftInverse
    r g recover hrecover

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression
