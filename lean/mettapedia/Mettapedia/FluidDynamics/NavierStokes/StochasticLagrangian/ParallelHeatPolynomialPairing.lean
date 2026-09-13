import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatPolynomial

/-!
# Exact finite sums for the actual parallel-flow octic correlation

The spatial eighth moment and each correlation entry are identified with
collected finite Fourier sums. The regularized multiplier is the coefficient
of the actual constructed radial kernel. Its limit is the ordinary Riesz
multiplier. No particular sign is asserted for the resulting finite sums.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped BigOperators Topology
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open PancakeQuadraticFourierSupport FourierPolynomialRealAlgebra LocalLowDiffusionBudget
open Mettapedia.Analysis UnitTorusFourierUniqueness UnitTorusPolynomialPairing
open UnitTorusConvolutionEnergy UnitAddTorus
local notation "T3" => UnitAddTorus (Fin 3)
local instance polynomialCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance polynomialCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance polynomialCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem meanEnergy_eq_coefficient_sum (a : FourierCoeff (Fin 3)) :
    LocalVorticityEighthMoment.meanEnergy (fun q ↦ vertical (a q)) =
      (∑ k ∈ (quarticAmplitudeCoeff a).support,
        quarticAmplitudeCoeff a k * quarticAmplitudeCoeff a (-k)).re := by
  let r := quarticAmplitudeCoeff a
  have h := integral_polynomial_mul r.support r (fourierPolynomial r) (fourierPolynomial r).continuous
  rw [← fourierPolynomial_eq_polynomial] at h
  simp_rw [mFourierCoeff_fourierPolynomial] at h
  have he (x : T3) : fourierPolynomial r x * fourierPolynomial r x =
      (‖fullVorticity (fun q ↦ vertical (a q)) x‖ ^ 8 : ℝ) := by
    dsimp only [r]
    rw [fourierPolynomial_quarticAmplitudeCoeff]
    push_cast
    ring
  simp_rw [he] at h
  have hh := congrArg Complex.re h
  simpa only [integral_complex_ofReal, Complex.ofReal_re,
    LocalVorticityEighthMoment.meanEnergy, LocalVorticityEighthMoment.energy_eq_norm_pow, r] using hh

def correlationEntryCoefficientSum (N : ℕ) (a : FourierCoeff (Fin 3)) (i j : Fin 3) : ℂ :=
  ∑ k ∈ (quarticTensorCoeff a i j).support,
    quarticTensorCoeff a i j k * (mFourierCoeff (PeriodicRadialRiesz.entry N i j) (-k) *
      quarticAmplitudeCoeff a (-k))

theorem correlationEntry_eq_coefficient_sum (N : ℕ) (a : FourierCoeff (Fin 3)) (i j : Fin 3) :
    PeriodicRadialRiesz.correlationEntry N (fullVorticity (fun q ↦ vertical (a q))) i j =
      (correlationEntryCoefficientSum N a i j).re := by
  let q := quarticTensorCoeff a i j
  let r := quarticAmplitudeCoeff a
  have hq (x : T3) :
      (PeriodicRadialRiesz.quarticTensorEntry (fullVorticity (fun k ↦ vertical (a k)) x) i j : ℂ) =
        polynomial q.support q x := by
    rw [← fourierPolynomial_eq_polynomial]
    exact (fourierPolynomial_quarticTensorCoeff a i j x).symm
  have hr : (fun x : T3 ↦ ((‖fullVorticity (fun k ↦ vertical (a k)) x‖ ^ 4 : ℝ) : ℂ)) =
      fourierPolynomial r := by
    funext x
    simpa using (fourierPolynomial_quarticAmplitudeCoeff a x).symm
  change (∫ x : T3, PeriodicRadialRiesz.quarticTensorEntry
    (fullVorticity (fun k ↦ vertical (a k)) x) i j *
    realConvolution (fun h ↦ (PeriodicRadialRiesz.entry N i j h).re)
      (fun y ↦ ‖fullVorticity (fun k ↦ vertical (a k)) y‖ ^ 4) x) = _
  rw [PeriodicRadialRiesz.real_pairing_eq_re_polynomial_pairing q.support q _ _ hq, hr,
    integral_polynomial_mul_convolution q.support q
      (fun h ↦ ((PeriodicRadialRiesz.entry N i j h).re : ℂ)) (fourierPolynomial r)
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (PeriodicRadialRiesz.continuous_entry N i j)))
      (fourierPolynomial r).continuous]
  simp only [mFourierCoeff_fourierPolynomial, PeriodicRadialRiesz.mFourierCoeff_re_entry,
    correlationEntryCoefficientSum, PeriodicRadialRiesz.mFourierCoeff_entry, q, r]

theorem correlation_eq_coefficient_sum (N : ℕ) (a : FourierCoeff (Fin 3)) :
    LocalOcticCorrelation.correlation N (fun q ↦ vertical (a q)) =
      ∑ i : Fin 3, ∑ j : Fin 3, (correlationEntryCoefficientSum N a i j).re := by
  simp only [LocalOcticCorrelation.correlation, PeriodicRadialRiesz.octicCorrelation,
    correlationEntry_eq_coefficient_sum]

def limitingCorrelationEntry (a : FourierCoeff (Fin 3)) (i j : Fin 3) : ℂ :=
  ∑ k ∈ (quarticTensorCoeff a i j).support,
    quarticTensorCoeff a i j k * ((AnnularRieszKernel.rieszEntry i j (UnitTorusLattice.frequency (-k)) : ℂ) *
      quarticAmplitudeCoeff a (-k))

theorem tendsto_correlationEntryCoefficientSum (a : FourierCoeff (Fin 3)) (i j : Fin 3) :
    Filter.Tendsto (fun N ↦ correlationEntryCoefficientSum N a i j)
      Filter.atTop (𝓝 (limitingCorrelationEntry a i j)) := by
  apply tendsto_finsetSum
  intro k _
  exact ((PeriodicRadialRiesz.tendsto_mFourierCoeff_entry i j (-k)).mul_const _).const_mul _

theorem tendsto_correlation (a : FourierCoeff (Fin 3)) :
    Filter.Tendsto (fun N ↦ LocalOcticCorrelation.correlation N (fun q ↦ vertical (a q)))
      Filter.atTop (𝓝 (∑ i : Fin 3, ∑ j : Fin 3, (limitingCorrelationEntry a i j).re)) := by
  simp_rw [correlation_eq_coefficient_sum]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact Complex.continuous_re.continuousAt.tendsto.comp (tendsto_correlationEntryCoefficientSum a i j)

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
