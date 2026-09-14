import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteSupport

/-!
# Exact finite evaluation of the physical cubic-flux coefficients

Finite support is an input property, not an invariant-subspace assumption
for Navier--Stokes. Output frequencies are all triple sums of input modes.
The formulas retain every interaction with a common output frequency.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxFiniteCoefficients

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeCurlOutputTail
open PancakeBlockReality PancakePeriodicVorticityEquation
open PeriodicGradientFluxTriple PeriodicFourierCollection PeriodicTensorParseval
open StretchingFluxCoefficients

def inputTriples (s : Finset Wavevector) : Finset TripleIndex := s ×ˢ (s ×ˢ s)

def outputModes (s : Finset Wavevector) : Finset Wavevector :=
  (inputTriples s).image tripleFrequency

theorem term_eq_zero_of_not_mem (u : FourierVelocity) (s : Finset Wavevector)
    (hs : ∀ q, q ∉ s → u q = 0) (r j : Fin 3) (p : TripleIndex)
    (hp : p ∉ inputTriples s) : term u r j p = 0 := by
  have hw := FourierFiniteSupport.fourierCurl_eq_zero s u hs
  by_cases h1 : p.1 ∈ s
  · by_cases h2 : p.2.1 ∈ s
    · have h3 : p.2.2 ∉ s := by
        intro h3
        exact hp (by simpa [inputTriples] using And.intro h1 (And.intro h2 h3))
      simp [term, tripleCoeff, indexedProductCoeff, indexedDerivativeCoeff, hs _ h3]
    · simp [term, tripleCoeff, indexedProductCoeff, hw _ h2]
  · simp [term, tripleCoeff, indexedProductCoeff, hw _ h1]

theorem interaction_eq_zero_of_not_mem (u : FourierVelocity) (s : Finset Wavevector)
    (hs : ∀ q, q ∉ s → u q = 0) (j : Fin 3) (p : TripleIndex)
    (hp : p ∉ inputTriples s) : interaction u j p = 0 := by
  simp only [interaction, term_eq_zero_of_not_mem u s hs _ j p hp,
    Finset.sum_const_zero, neg_zero]

theorem coefficients_eq_sum (u : FourierVelocity) (s : Finset Wavevector)
    (hs : ∀ q, q ∉ s → u q = 0) (j : Fin 3) (q : Wavevector) :
    coefficients u j q = ∑ p ∈ inputTriples s,
      if tripleFrequency p = q then interaction u j p else 0 :=
  collect_eq_sum tripleFrequency _ (inputTriples s)
    (interaction_eq_zero_of_not_mem u s hs j) q

theorem coefficients_eq_zero_of_not_mem (u : FourierVelocity) (s : Finset Wavevector)
    (hs : ∀ q, q ∉ s → u q = 0) (j : Fin 3) (q : Wavevector)
    (hq : q ∉ outputModes s) : coefficients u j q = 0 :=
  collect_eq_zero_of_not_mem_image tripleFrequency _ (inputTriples s)
    (interaction_eq_zero_of_not_mem u s hs j) q hq

/-- The third input is determined by the output. This reduces the exact
coefficient computation from three finite input sums to two. -/
theorem coefficients_eq_double_sum (u : FourierVelocity) (s : Finset Wavevector)
    (hs : ∀ q, q ∉ s → u q = 0) (j : Fin 3) (q : Wavevector) :
    coefficients u j q = ∑ k ∈ s, ∑ l ∈ s, interaction u j (k, (l, q - k - l)) := by
  classical
  rw [coefficients_eq_sum u s hs j q]
  simp only [inputTriples, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have he (m : Wavevector) : tripleFrequency (k, (l, m)) = q ↔ m = q - k - l := by
    simp only [tripleFrequency]
    constructor <;> intro h <;> subst_vars <;> abel
  simp only [he, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · symm
    apply interaction_eq_zero_of_not_mem u s hs j
    simpa only [inputTriples, Finset.mem_product, not_and] using
      (fun (_ : k ∈ s) (_ : l ∈ s) ↦ hm)

theorem spectralPair_eq_sum (u v : FourierVelocity) (s : Finset Wavevector)
    (hs : ∀ q, q ∉ s → u q = 0) :
    spectralPair u v = ∑ q ∈ outputModes s, (coefficientHermitian
      (divergenceCoeff q (fun j ↦ coefficients u j q))
      (divergenceCoeff q (fun j ↦ coefficients v j q)) /
        (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re := by
  apply tsum_eq_sum
  intro q hq
  simp [coefficients_eq_zero_of_not_mem u s hs _ q hq, divergenceCoeff,
    PeriodicGradientFluxSymbol.contraction, coefficientHermitian]

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxFiniteCoefficients
