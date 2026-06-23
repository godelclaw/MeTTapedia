import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# Bool-pair counterexample regressions for observed support postprocessing
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression

open Mettapedia.Computability.PNP

def boolPairObservedSupportRecoding : Bool → Unit → Bool × Bool
  | true, () => (true, false)
  | false, () => (false, false)

def boolPairFirstProjection : Bool × Bool → Bool :=
  fun p => p.1

def boolPairObservedSupportRecover : Bool → Bool × Bool :=
  fun b => (b, false)

theorem boolPairFirstProjection_not_injective_regression :
    ¬ Function.Injective boolPairFirstProjection := by
  intro hinj
  have hEq :
      ((false, false) : Bool × Bool) = (false, true) := by
    apply hinj
    rfl
  have hNeq : ((false, false) : Bool × Bool) ≠ (false, true) := by
    decide
  exact hNeq hEq

theorem boolPairObservedSupportRecoding_firstProjection_observed_injective_regression :
    ∀ b1 c1 b2 c2,
      boolPairFirstProjection (boolPairObservedSupportRecoding b1 c1) =
        boolPairFirstProjection (boolPairObservedSupportRecoding b2 c2) →
      boolPairObservedSupportRecoding b1 c1 =
        boolPairObservedSupportRecoding b2 c2 := by
  intro b1 c1 b2 c2 hEq
  cases b1 <;> cases c1 <;> cases b2 <;> cases c2 <;>
    simp [boolPairObservedSupportRecoding, boolPairFirstProjection] at hEq ⊢

theorem boolPairObservedSupportRecoding_firstProjection_left_inverse_regression :
    ∀ b c,
      boolPairObservedSupportRecover
          (boolPairFirstProjection (boolPairObservedSupportRecoding b c)) =
        boolPairObservedSupportRecoding b c := by
  intro b c
  cases b <;> cases c <;>
    rfl

theorem output_tolerance_postcompose_iff_observed_injective_not_global_injective_regression
    (τ : Nat) :
    ¬ Function.Injective boolPairFirstProjection ∧
      (CountIndependentWithinToleranceOutput (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput
          (fun b c => boolPairFirstProjection (boolPairObservedSupportRecoding b c))) τ ↔
      CountIndependentWithinToleranceOutput (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput boolPairObservedSupportRecoding) τ) := by
  refine ⟨boolPairFirstProjection_not_injective_regression, ?_⟩
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      boolPairObservedSupportRecoding boolPairFirstProjection τ
      boolPairObservedSupportRecoding_firstProjection_observed_injective_regression

theorem output_defect_postcompose_eq_observed_left_inverse_not_global_injective_regression :
    ¬ Function.Injective boolPairFirstProjection ∧
      countIndependentWithinOutputDefect (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput
          (fun b c => boolPairFirstProjection (boolPairObservedSupportRecoding b c))) =
      countIndependentWithinOutputDefect (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput boolPairObservedSupportRecoding) := by
  refine ⟨boolPairFirstProjection_not_injective_regression, ?_⟩
  exact
    countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedLeftInverse
      boolPairObservedSupportRecoding
      boolPairFirstProjection
      boolPairObservedSupportRecover
      boolPairObservedSupportRecoding_firstProjection_left_inverse_regression

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression
