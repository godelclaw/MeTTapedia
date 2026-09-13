import Mettapedia.Analysis.UnitTorusPolynomialPairing
import Mettapedia.Analysis.PeriodicRadialCorrelationEnergy

/-!
# Finite Fourier pairing limits for the actual radial Riesz kernels

Polynomial source factors permit passage from the constructed regularized
kernels to their limiting multipliers. Strict inequalities in the resulting
finite sum persist for all sufficiently large cutoffs. This does not supply
the polynomial expansion or the sign of any particular proposed witness.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRadialRiesz

open MeasureTheory UnitAddTorus UnitTorusFourierUniqueness
open UnitTorusPolynomialPairing UnitTorusConvolutionEnergy UnitTorusLattice
open scoped BigOperators Topology
variable {d : ℕ}
local notation "Td" => UnitAddTorus (Fin d)
local instance polynomialPairingCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance polynomialPairingCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance polynomialPairingCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def polynomialPairingLimit (P : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (f : Td → ℂ) (i j : Fin d) : ℂ :=
  ∑ k ∈ P, a k * ((AnnularRieszKernel.rieszEntry i j (frequency (-k)) : ℂ) *
    mFourierCoeff f (-k))

theorem tendsto_polynomial_re_entry_pairing
    (P : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (f : Td → ℂ) (hf : Continuous f) (i j : Fin d) :
    Filter.Tendsto (fun N ↦ ∫ x : Td, polynomial P a x *
      convolution (fun h ↦ ((entry N i j h).re : ℂ)) f x)
      Filter.atTop (𝓝 (polynomialPairingLimit P a f i j)) := by
  have hm (k : Fin d → ℤ) :
      Filter.Tendsto (fun N ↦ mFourierCoeff (fun h ↦ ((entry N i j h).re : ℂ)) k)
        Filter.atTop (𝓝 (AnnularRieszKernel.rieszEntry i j (frequency k) : ℂ)) := by
    simpa only [mFourierCoeff_re_entry, mFourierCoeff_entry] using tendsto_mFourierCoeff_entry i j k
  exact tendsto_integral_polynomial_mul_convolution P a
    (fun N h ↦ ((entry N i j h).re : ℂ))
    (fun N ↦ Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_entry N i j)))
    f hf (fun k ↦ (AnnularRieszKernel.rieszEntry i j (frequency k) : ℂ)) hm

theorem real_pairing_eq_re_polynomial_pairing
    (P : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (q f : Td → ℝ) (hq : ∀ x, (q x : ℂ) = polynomial P a x) (N : ℕ) (i j : Fin d) :
    (∫ x : Td, q x * realConvolution (fun h ↦ (entry N i j h).re) f x) =
      (∫ x : Td, polynomial P a x *
        convolution (fun h ↦ ((entry N i j h).re : ℂ)) (fun y ↦ (f y : ℂ)) x).re := by
  simp_rw [← hq, ← ofReal_realConvolution, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_re]

theorem tendsto_real_polynomial_entry_pairing
    (P : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (q f : Td → ℝ) (hq : ∀ x, (q x : ℂ) = polynomial P a x)
    (hf : Continuous f) (i j : Fin d) :
    Filter.Tendsto (fun N ↦ ∫ x : Td, q x * realConvolution (fun h ↦ (entry N i j h).re) f x)
      Filter.atTop (𝓝 (polynomialPairingLimit P a (fun y ↦ (f y : ℂ)) i j).re) := by
  simp_rw [real_pairing_eq_re_polynomial_pairing P a q f hq]
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_polynomial_re_entry_pairing P a _ (Complex.continuous_ofReal.comp hf) i j)

theorem eventually_lt_real_polynomial_entry_pairing
    (P : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (q f : Td → ℝ) (hq : ∀ x, (q x : ℂ) = polynomial P a x)
    (hf : Continuous f) (i j : Fin d) (c : ℝ)
    (hc : c < (polynomialPairingLimit P a (fun y ↦ (f y : ℂ)) i j).re) :
    ∀ᶠ N in Filter.atTop,
      c < ∫ x : Td, q x * realConvolution (fun h ↦ (entry N i j h).re) f x :=
  (tendsto_real_polynomial_entry_pairing P a q f hq hf i j).eventually (eventually_gt_nhds hc)

end Mettapedia.Analysis.PeriodicRadialRiesz
