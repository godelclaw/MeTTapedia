import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxSymbol

/-!
# Exact active-flux coefficient energy and viscous pair cancellation

The projected coefficient energy is the output-divergence contraction
energy divided by the squared output frequency. At each viscous pair,
input incompressibility exposes the cross-frequency directional factor.
These are exact identities, not a bound on their time-integrated sum.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxPair

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakePeriodicVorticityEquation
open PeriodicGradientFluxSymbol

theorem sum_norm_projectedCoeff_sq (n : Wavevector) (J : Fin 3 → VelocityCoefficient) :
    (∑ j, ‖coefficientVec (projectedCoeff n J j)‖ ^ 2) =
      ‖coefficientVec (contraction n J)‖ ^ 2 / ‖frequencyVec n‖ ^ 2 := by
  have he (j : Fin 3) : coefficientVec (projectedCoeff n J j) =
      ((n j : ℂ) / modeSquare n) • coefficientVec (contraction n J) := rfl
  have hn (j : Fin 3) : ‖(n j : ℂ)‖ ^ 2 = (n j : ℝ) ^ 2 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hm : ‖modeSquare n‖ = ‖frequencyVec n‖ ^ 2 := by
    rw [modeSquare_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  simp only [he, norm_smul, norm_div, mul_pow, div_pow, hn, hm]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_mul, ← norm_frequencyVec_sq]
  by_cases hz : ‖frequencyVec n‖ = 0
  · simp [hz]
  · field_simp

theorem contraction_smul (n : Wavevector) (c : ℂ) (J : Fin 3 → VelocityCoefficient) :
    contraction n (fun j ↦ c • J j) = c • contraction n J := by
  simp only [contraction, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem projectedCoeff_smul (n : Wavevector) (c : ℂ) (J : Fin 3 → VelocityCoefficient) (j : Fin 3) :
    projectedCoeff n (fun l ↦ c • J l) j = c • projectedCoeff n J j := by
  simp only [projectedCoeff, contraction_smul, smul_smul]
  rw [mul_comm]

def frequencyPairing (k l : Wavevector) : ℂ := ∑ r, (k r : ℂ) * (l r : ℂ)

/-- The coefficient of `sum_r (partial_r omega)_j partial_r omega`
at the ordered input pair `(k,l)`, retaining both derivative phases. -/
def viscousPairCoeff (k l : Wavevector) (a b : VelocityCoefficient) (j : Fin 3) : VelocityCoefficient :=
  ∑ r, (unitTorusDerivativePhase * (k r : ℂ) * a j) •
    ((unitTorusDerivativePhase * (l r : ℂ)) • b)

theorem viscousPairCoeff_eq (k l : Wavevector) (a b : VelocityCoefficient) (j : Fin 3) :
    viscousPairCoeff k l a b j =
      (unitTorusDerivativePhase ^ 2 * frequencyPairing k l) • (a j • b) := by
  simp only [viscousPairCoeff, frequencyPairing, smul_smul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

theorem projected_viscousPair_of_transverse (k l : Wavevector) (a b : VelocityCoefficient)
    (ha : modeDot k a = 0) (j : Fin 3) :
    projectedCoeff (k + l) (viscousPairCoeff k l a b) j =
      (unitTorusDerivativePhase ^ 2 * frequencyPairing k l *
        (((k + l) j : ℂ) / modeSquare (k + l) * modeDot l a)) • b := by
  have he : viscousPairCoeff k l a b =
      fun m ↦ (unitTorusDerivativePhase ^ 2 * frequencyPairing k l) • (a m • b) :=
    funext (viscousPairCoeff_eq k l a b)
  rw [he, projectedCoeff_smul, projectedCoeff_rankOne_of_transverse k l a b ha, smul_smul]

theorem projected_viscousPair_eq_zero_of_cross_transverse (k l : Wavevector)
    (a b : VelocityCoefficient) (hk : modeDot k a = 0) (hl : modeDot l a = 0) :
    projectedCoeff (k + l) (viscousPairCoeff k l a b) = 0 := by
  funext j
  simp only [projected_viscousPair_of_transverse k l a b hk, hl, mul_zero, zero_smul, Pi.zero_apply]

end Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxPair
