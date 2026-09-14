import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RationalStretchingFlux
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxFiniteVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxSpectralEvolution

/-!
# Exact rational coefficients of the physical heat variation

The heat symbol is summed over the three input frequencies. This gives the
actual product-rule variation of the cubic flux, with factor `(2 pi)^5`,
and its divergence, with factor `i (2 pi)^6`. No output-frequency damping
is substituted for the three input symbols.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFluxHeat

open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakePeriodicComplexStretch PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation PancakeInfiniteFourierDerivative
open PancakeBlockReality
open PancakeInfiniteSpatialLaplacian PancakeDyadicDirectionEvolution
open PeriodicGradientFluxTriple PeriodicGradientFluxSymbol PeriodicTensorParseval
open StretchingFluxCoefficients StretchingFluxFiniteCoefficients StretchingFluxMixedCoefficients
open StretchingFluxFiniteVariation RationalStretchingFlux StretchingFluxSpectralEvolution

def rationalModeSquare (q : Wavevector) : ℚ := ∑ j, (q j : ℚ) * (q j : ℚ)

theorem cast_rationalModeSquare (q : Wavevector) :
    (rationalModeSquare q : ℂ) = modeSquare q := by
  simp [rationalModeSquare, modeSquare]

def tripleHeatWeight (p : TripleIndex) : ℚ :=
  -(rationalModeSquare p.1 + rationalModeSquare p.2.1 + rationalModeSquare p.2.2)

theorem sum_heat_symbols (p : TripleIndex) :
    unitTorusDerivativePhase ^ 2 * modeSquare p.1 +
      unitTorusDerivativePhase ^ 2 * modeSquare p.2.1 +
      unitTorusDerivativePhase ^ 2 * modeSquare p.2.2 =
    (((2 * Real.pi : ℝ) : ℂ) ^ 2) * (tripleHeatWeight p : ℂ) := by
  simp only [tripleHeatWeight, Rat.cast_neg, Rat.cast_add, cast_rationalModeSquare,
    unitTorusDerivativePhase]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

def rationalHeatFluxCoefficient (s : Finset Wavevector) (a : RationalVelocity)
    (q : Wavevector) (j : Fin 3) : RationalCoefficient :=
  fun i ↦ ∑ k ∈ s, ∑ l ∈ s,
    tripleHeatWeight (k, (l, q - k - l)) * rationalInteraction a j (k, (l, q - k - l)) i

def rationalHeatDivergenceCoefficient (s : Finset Wavevector) (a : RationalVelocity)
    (q : Wavevector) : RationalCoefficient :=
  fun i ↦ ∑ j, (q j : ℚ) * rationalHeatFluxCoefficient s a q j i

theorem heat_variation_imaginaryLift (s : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0) (q : Wavevector) (j i : Fin 3) :
    variationCoefficients (imaginaryLift a) (laplacianCoeff (imaginaryLift a)) j q i =
      (((2 * Real.pi : ℝ) : ℂ) ^ 5) * (rationalHeatFluxCoefficient s a q j i : ℂ) := by
  have hs' (k : Wavevector) (hk : k ∉ s) : imaginaryLift a k = 0 := by
    ext l
    simp [imaginaryLift, hs k hk]
  rw [show laplacianCoeff (imaginaryLift a) =
    (fun k ↦ (unitTorusDerivativePhase ^ 2 * modeSquare k) • imaginaryLift a k) from rfl,
    variationCoefficients_multiplier_eq_double_sum _ _ s hs' j q]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    interaction_imaginaryLift,
    rationalHeatFluxCoefficient, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [sum_heat_symbols (k, (l, q - k - l))]
  ring

theorem heat_divergence_imaginaryLift (s : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0) (q : Wavevector) (i : Fin 3) :
    divergenceCoeff q
        (fun j ↦ variationCoefficients (imaginaryLift a) (laplacianCoeff (imaginaryLift a)) j q) i =
      Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 6) *
        (rationalHeatDivergenceCoefficient s a q i : ℂ) := by
  simp only [divergenceCoeff, contraction, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    heat_variation_imaginaryLift s a hs, rationalHeatDivergenceCoefficient,
    Fin.sum_univ_three, unitTorusDerivativePhase]
  push_cast
  ring

theorem normalized_rational_heat_pair (a b : RationalCoefficient) (q : Wavevector) :
    (coefficientHermitian
        (fun i ↦ Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 4) * (a i : ℂ))
        (fun i ↦ Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 6) * (b i : ℂ)) /
      (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re =
      (2 * Real.pi) ^ 8 * (((∑ i, a i * b i) / rationalModeSquare q : ℚ) : ℝ) := by
  have hh : coefficientHermitian
      (fun i ↦ Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 4) * (a i : ℂ))
      (fun i ↦ Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 6) * (b i : ℂ)) =
      (((2 * Real.pi : ℝ) : ℂ) ^ 2) *
        ((((2 * Real.pi : ℝ) : ℂ) ^ 8) * ((∑ i, a i * b i : ℚ) : ℂ)) := by
    simp only [coefficientHermitian, map_mul, map_pow, Complex.conj_I,
      Complex.conj_ofReal, map_ratCast, Fin.sum_univ_three]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hc : ((2 * Real.pi : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity))
  rw [hh, mul_div_mul_left _ _ hc, mul_div_assoc,
    ← cast_rationalModeSquare, ← Rat.cast_div]
  norm_cast

/-- Full signed inverse-Laplacian work, collected at every possible output mode. -/
def rationalHeatWork (s : Finset Wavevector) (a : RationalVelocity) : ℚ :=
  ∑ q ∈ outputModes s,
    (∑ i, rationalDivergenceCoefficient s a q i * rationalHeatDivergenceCoefficient s a q i) /
      rationalModeSquare q

theorem spectral_heat_work_eq_rational (s : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0)
    (hr : ∀ q, imaginaryLift a (-q) = coefficientConjugate (imaginaryLift a q)) :
    spectralVariationWork (imaginaryLift a) (laplacianCoeff (imaginaryLift a)) =
      (2 * Real.pi) ^ 8 * (rationalHeatWork s a : ℝ) := by
  have hs' (k : Wavevector) (hk : k ∉ s) : imaginaryLift a k = 0 := by
    ext l
    simp [imaginaryLift, hs k hk]
  have hu := FourierFiniteSupport.summable_fourierMoment s (imaginaryLift a) hs' 1
  have hv := summable_fourierMoment_laplacian 1 (imaginaryLift a)
    (FourierFiniteSupport.summable_fourierMoment s (imaginaryLift a) hs' 3)
  have hrv := laplacianCoeff_reality (imaginaryLift a) hr
  rw [← physical_variation_work _ _ hu hv hr hrv,
    projected_variation_work_eq_tsum _ _ hu hv hr hrv]
  have hfinite : (∑' q, (coefficientHermitian
        (divergenceCoeff q (fun j ↦ coefficients (imaginaryLift a) j q))
        (divergenceCoeff q
          (fun j ↦ variationCoefficients (imaginaryLift a) (laplacianCoeff (imaginaryLift a)) j q)) /
        (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re) =
      ∑ q ∈ outputModes s, (coefficientHermitian
        (divergenceCoeff q (fun j ↦ coefficients (imaginaryLift a) j q))
        (divergenceCoeff q
          (fun j ↦ variationCoefficients (imaginaryLift a) (laplacianCoeff (imaginaryLift a)) j q)) /
        (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re := by
    apply tsum_eq_sum
    intro q hq
    simp [coefficients_eq_zero_of_not_mem _ s hs' _ q hq,
      divergenceCoeff, contraction, coefficientHermitian]
  rw [hfinite]
  simp only [rationalHeatWork, Rat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have h1 := funext (divergence_imaginaryLift s a hs q)
  have h2 := funext (heat_divergence_imaginaryLift s a hs q)
  rw [h1, h2]
  exact normalized_rational_heat_pair _ _ q

end Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFluxHeat
