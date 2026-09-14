import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxFiniteCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxMixedCoefficients

/-!
# Finite coefficients of the actual three-slot flux variation

A Fourier multiplier differentiates the three input slots separately.
Its symbol in the cubic variation is the sum of the three input symbols,
not the symbol at their sum. All collisions at an output mode are retained.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxFiniteVariation

open PeriodicFourierTriad PancakePeriodicComplexStretch PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation PancakeInfiniteFourierDerivative
open PeriodicGradientFluxTriple PeriodicFourierCollection
open StretchingFluxCoefficients StretchingFluxFiniteCoefficients StretchingFluxMixedCoefficients

theorem mixedTerm_eq_zero_of_not_mem (a b c : FourierVelocity) (s : Finset Wavevector)
    (ha : ∀ q, q ∉ s → a q = 0) (hb : ∀ q, q ∉ s → b q = 0)
    (hc : ∀ q, q ∉ s → c q = 0) (r j : Fin 3) (p : TripleIndex)
    (hp : p ∉ inputTriples s) : mixedTerm a b c r j p = 0 := by
  have hwa := FourierFiniteSupport.fourierCurl_eq_zero s a ha
  have hwb := FourierFiniteSupport.fourierCurl_eq_zero s b hb
  by_cases h1 : p.1 ∈ s
  · by_cases h2 : p.2.1 ∈ s
    · have h3 : p.2.2 ∉ s := by
        intro h3
        exact hp (by simpa [inputTriples] using And.intro h1 (And.intro h2 h3))
      simp [mixedTerm, tripleCoeff, indexedProductCoeff, indexedDerivativeCoeff, hc _ h3]
    · simp [mixedTerm, tripleCoeff, indexedProductCoeff, hwb _ h2]
  · simp [mixedTerm, tripleCoeff, indexedProductCoeff, hwa _ h1]

theorem mixedInteraction_eq_zero_of_not_mem (a b c : FourierVelocity) (s : Finset Wavevector)
    (ha : ∀ q, q ∉ s → a q = 0) (hb : ∀ q, q ∉ s → b q = 0)
    (hc : ∀ q, q ∉ s → c q = 0) (j : Fin 3) (p : TripleIndex)
    (hp : p ∉ inputTriples s) : mixedInteraction a b c j p = 0 := by
  simp only [mixedInteraction, mixedTerm_eq_zero_of_not_mem a b c s ha hb hc _ j p hp,
    Finset.sum_const_zero, neg_zero]

theorem mixedCoefficients_eq_double_sum (a b c : FourierVelocity) (s : Finset Wavevector)
    (ha : ∀ q, q ∉ s → a q = 0) (hb : ∀ q, q ∉ s → b q = 0)
    (hc : ∀ q, q ∉ s → c q = 0) (j : Fin 3) (q : Wavevector) :
    mixedCoefficients a b c j q =
      ∑ k ∈ s, ∑ l ∈ s, mixedInteraction a b c j (k, (l, q - k - l)) := by
  classical
  rw [mixedCoefficients, collect_eq_sum tripleFrequency _ (inputTriples s)
    (mixedInteraction_eq_zero_of_not_mem a b c s ha hb hc j) q]
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
    apply mixedInteraction_eq_zero_of_not_mem a b c s ha hb hc j
    simpa only [inputTriples, Finset.mem_product, not_and] using
      (fun (_ : k ∈ s) (_ : l ∈ s) ↦ hm)

theorem mixedInteraction_multipliers (a b c : Wavevector → ℂ) (u : FourierVelocity)
    (j : Fin 3) (p : TripleIndex) :
    mixedInteraction (fun q ↦ a q • u q) (fun q ↦ b q • u q) (fun q ↦ c q • u q) j p =
      (a p.1 * b p.2.1 * c p.2.2) • interaction u j p := by
  ext i
  simp only [mixedInteraction, mixedTerm, interaction, term, tripleCoeff, indexedProductCoeff,
    fourierCurl, coefficientCross_smul_right, indexedDerivativeCoeff,
    Pi.smul_apply, Pi.neg_apply, Pi.add_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem variationCoefficients_multiplier_eq_double_sum (w : Wavevector → ℂ)
    (u : FourierVelocity) (s : Finset Wavevector) (hs : ∀ q, q ∉ s → u q = 0)
    (j : Fin 3) (q : Wavevector) :
    variationCoefficients u (fun k ↦ w k • u k) j q =
      ∑ k ∈ s, ∑ l ∈ s,
        (w k + w l + w (q - k - l)) • interaction u j (k, (l, q - k - l)) := by
  have hw (k : Wavevector) (hk : k ∉ s) : w k • u k = 0 := by simp [hs k hk]
  have h1 (p : TripleIndex) : mixedInteraction (fun k ↦ w k • u k) u u j p =
      w p.1 • interaction u j p := by
    simpa using mixedInteraction_multipliers w (fun _ ↦ 1) (fun _ ↦ 1) u j p
  have h2 (p : TripleIndex) : mixedInteraction u (fun k ↦ w k • u k) u j p =
      w p.2.1 • interaction u j p := by
    simpa using mixedInteraction_multipliers (fun _ ↦ 1) w (fun _ ↦ 1) u j p
  have h3 (p : TripleIndex) : mixedInteraction u u (fun k ↦ w k • u k) j p =
      w p.2.2 • interaction u j p := by
    simpa using mixedInteraction_multipliers (fun _ ↦ 1) (fun _ ↦ 1) w u j p
  simp only [variationCoefficients, Pi.add_apply,
    mixedCoefficients_eq_double_sum _ _ _ s hw hs hs,
    mixedCoefficients_eq_double_sum _ _ _ s hs hw hs,
    mixedCoefficients_eq_double_sum _ _ _ s hs hs hw,
    h1, h2, h3, add_smul, Finset.sum_add_distrib]

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxFiniteVariation
