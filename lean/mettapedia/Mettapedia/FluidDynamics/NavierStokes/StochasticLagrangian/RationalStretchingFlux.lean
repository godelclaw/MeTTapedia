import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxFiniteCoefficients

/-!
# Rational normalization of imaginary Fourier velocity data

For `u_hat = i a` with rational `a`, curl and first derivatives have real
coefficients. The cubic flux has one common factor `(2 pi)^3`, and its
divergence has `i (2 pi)^4`. These identities remove physical constants
before exact finite arithmetic; they do not approximate the coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFlux

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakeInfiniteFourierDerivative PancakeDyadicDirectionEvolution
open PeriodicGradientFluxTriple PeriodicGradientFluxSymbol PeriodicTensorParseval
open StretchingFluxCoefficients StretchingFluxFiniteCoefficients

abbrev RationalCoefficient := Fin 3 → ℚ
abbrev RationalVelocity := Wavevector → RationalCoefficient

def imaginaryLift (a : RationalVelocity) : FourierVelocity := fun q i ↦ Complex.I * (a q i : ℂ)

/-- Negative wavevector cross product, because both the derivative and
the velocity supply a factor of `i`. -/
def rationalCurl (a : RationalVelocity) (q : Wavevector) : RationalCoefficient :=
  ![(q 2 : ℚ) * a q 1 - (q 1 : ℚ) * a q 2,
    (q 0 : ℚ) * a q 2 - (q 2 : ℚ) * a q 0,
    (q 1 : ℚ) * a q 0 - (q 0 : ℚ) * a q 1]

theorem curl_imaginaryLift (a : RationalVelocity) (q : Wavevector) :
    fourierCurl (imaginaryLift a) q =
      ((2 * Real.pi : ℝ) : ℂ) • (fun i ↦ (rationalCurl a q i : ℂ)) := by
  ext i
  fin_cases i <;> simp [fourierCurl, coefficientCross, wavevectorCoefficient,
    unitTorusDerivativePhase, imaginaryLift, rationalCurl] <;> ring_nf <;>
      simp only [Complex.I_sq] <;> ring

theorem derivative_imaginaryLift (a : RationalVelocity) (r : Fin 3) (q : Wavevector) (i : Fin 3) :
    indexedDerivativeCoeff id r (imaginaryLift a) q i =
      -((2 * Real.pi : ℝ) : ℂ) * ((q r : ℚ) * a q i : ℚ) := by
  simp [indexedDerivativeCoeff, unitTorusDerivativePhase, imaginaryLift]
  ring_nf
  simp only [Complex.I_sq]
  ring

def rationalInteraction (a : RationalVelocity) (j : Fin 3) (p : TripleIndex) : RationalCoefficient :=
  fun i ↦ ∑ r, rationalCurl a p.1 j * rationalCurl a p.2.1 r *
    (p.2.2 r : ℚ) * a p.2.2 i

theorem interaction_imaginaryLift (a : RationalVelocity) (j : Fin 3) (p : TripleIndex) (i : Fin 3) :
    interaction (imaginaryLift a) j p i =
      (((2 * Real.pi : ℝ) : ℂ) ^ 3) * (rationalInteraction a j p i : ℂ) := by
  simp only [interaction, term, tripleCoeff, indexedProductCoeff,
    curl_imaginaryLift, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    derivative_imaginaryLift, rationalInteraction, Fin.sum_univ_three]
  push_cast
  ring

def rationalFluxCoefficient (s : Finset Wavevector) (a : RationalVelocity)
    (q : Wavevector) (j : Fin 3) : RationalCoefficient :=
  fun i ↦ ∑ k ∈ s, ∑ l ∈ s, rationalInteraction a j (k, (l, q - k - l)) i

theorem coefficients_imaginaryLift (s : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0) (q : Wavevector) (j i : Fin 3) :
    coefficients (imaginaryLift a) j q i =
      (((2 * Real.pi : ℝ) : ℂ) ^ 3) * (rationalFluxCoefficient s a q j i : ℂ) := by
  have hs' (k : Wavevector) (hk : k ∉ s) : imaginaryLift a k = 0 := by
    ext l
    simp [imaginaryLift, hs k hk]
  rw [coefficients_eq_double_sum _ s hs' j q]
  simp only [Finset.sum_apply, interaction_imaginaryLift, rationalFluxCoefficient,
    Rat.cast_sum, Finset.mul_sum]

def rationalDivergenceCoefficient (s : Finset Wavevector) (a : RationalVelocity)
    (q : Wavevector) : RationalCoefficient :=
  fun i ↦ ∑ j, (q j : ℚ) * rationalFluxCoefficient s a q j i

theorem divergence_imaginaryLift (s : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0) (q : Wavevector) (i : Fin 3) :
    divergenceCoeff q (fun j ↦ coefficients (imaginaryLift a) j q) i =
      Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 4) * (rationalDivergenceCoefficient s a q i : ℂ) := by
  simp only [divergenceCoeff, contraction, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    coefficients_imaginaryLift s a hs, rationalDivergenceCoefficient, Fin.sum_univ_three,
    unitTorusDerivativePhase]
  push_cast
  ring

end Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFlux
