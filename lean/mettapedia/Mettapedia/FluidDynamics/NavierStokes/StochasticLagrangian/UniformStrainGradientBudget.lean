import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalStrainGradientDensity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherDerivativeMoments

/-!
# A cutoff-uniform envelope for the actual strain gradient

Filters bounded by one and arbitrary finite mode sets share a majorant
given by the full second velocity moment. The moment is an explicit
smooth-field cost; no bound uniform up to a possible singular time is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.UniformStrainGradientBudget

open PeriodicFourierTriad PancakeCurlOutputTail PancakeFourierStrainGradient
open PancakeFilteredStrainDynamics PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)

def envelope (u : FourierVelocity) : ℝ :=
  9 * ‖unitTorusDerivativePhase‖ ^ 2 * ∑' q, fourierMoment 2 u q

theorem envelope_nonneg (u : FourierVelocity) : 0 ≤ envelope u := by
  unfold envelope
  exact mul_nonneg (by positivity) (tsum_nonneg (fourierMoment_nonneg 2 u))

theorem strainGradientAmplitude_le_envelope (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1) (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    strainGradientAmplitude modes chi u ≤ envelope u := by
  have hterm (q : Wavevector) (hq : q ∈ modes) :
      strainGradientWeight chi q * ‖coefficientVec (u q)‖ ≤
        (9 * ‖unitTorusDerivativePhase‖ ^ 2) * fourierMoment 2 u q := by
    have hf : ‖frequencyVec q‖ ^ 2 ≤ (1 + ‖frequencyVec q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    have hc := mul_le_mul (hchi q hq) hf (sq_nonneg _) zero_le_one
    simp only [one_mul] at hc
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (show 0 ≤ 9 * ‖unitTorusDerivativePhase‖ ^ 2 by positivity))
      (norm_nonneg (coefficientVec (u q)))
    simpa only [strainGradientWeight, fourierMoment, mul_assoc] using h
  calc
    _ ≤ ∑ q ∈ modes, (9 * ‖unitTorusDerivativePhase‖ ^ 2) * fourierMoment 2 u q :=
      Finset.sum_le_sum hterm
    _ = (9 * ‖unitTorusDerivativePhase‖ ^ 2) * ∑ q ∈ modes, fourierMoment 2 u q :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hu.sum_le_tsum modes (fun q _ ↦ fourierMoment_nonneg 2 u q)) (by positivity)

theorem norm_strainGradient_le_envelope (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1) (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (x : T3) (j : Fin 3) :
    ‖strainGradient modes (filteredVelocity chi u) x j‖ ≤ envelope u :=
  (norm_strainGradient_le_amplitude modes chi u x j).trans
    (strainGradientAmplitude_le_envelope chi modes hchi u hu)

theorem sum_norm_strainGradient_sq_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1) (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (x : T3) :
    (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) ≤ 3 * envelope u ^ 2 := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_strainGradient_le_envelope chi modes hchi u hu x j) 2)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using h

end Mettapedia.FluidDynamics.NavierStokes.UniformStrainGradientBudget
