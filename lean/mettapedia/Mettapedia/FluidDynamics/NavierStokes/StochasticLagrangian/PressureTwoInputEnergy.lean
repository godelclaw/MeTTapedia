import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTwoInputLocalization

/-!
# Two-input pressure localization with explicit Fourier costs

Both derivative costs are paid at original input frequencies. The estimates
retain the cutoffs' Fourier l1 norms and are not uniform as the Fourier
approximation tolerance tends to zero. They do not require a pointwise bound
on the cutoffs or a zero-mode condition on either localized input.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputEnergy

open scoped BigOperators
open PeriodicFourierTriad PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open ComplexPressureConvolution PressureBilinearLocalization FiniteCutoffAlgebra
open PressureTwoInputLocalization FourierEllipticProductEnergy
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def twoInputCost (A D P K : Finset Wavevector) (c d : Wavevector → ℂ)
    (w v : FourierVelocity) : ℝ :=
  288 * ((∑ a ∈ A, ‖c a‖) ^ 2 *
      (∑ p ∈ P, ‖coefficientVec (w p)‖ / ‖frequencyVec p‖) ^ 2 *
      (∑ k ∈ K, ‖coefficientVec (v k)‖) ^ 2 * coordinateEnergy D d +
    (∑ b ∈ D, ‖d b‖) ^ 2 * (∑ p ∈ P, ‖coefficientVec (w p)‖) ^ 2 *
      (∑ k ∈ K, ‖coefficientVec (v k)‖ / ‖frequencyVec k‖) ^ 2 * coordinateEnergy A c)

theorem twoInputCommutator_energy_le (e : R3) (he : ‖e‖ = 1)
    (A D P K Q : Finset Wavevector) (c d : Wavevector → ℂ) (w v : FourierVelocity)
    (hw : w 0 = 0) (hv : v 0 = 0)
    (hQ : ∀ a ∈ A, ∀ b ∈ D, ∀ p ∈ P, ∀ k ∈ K, a + (b + (p + k)) ∈ Q) :
    (∑ q ∈ Q, ‖twoInputCommutator e A D P K c d w v q‖ ^ 2) ≤
      twoInputCost A D P K c d w v := by
  let T := finiteCutoffOutputModes D (finiteCutoffOutputModes P K)
  let L := finiteCutoffOutputModes D P
  let dw := finiteCutoffConvolutionCoeff D P d w
  let E₁ := vectorConvolution A T c
    (PressureBilinearLocalization.commutatorCoefficient e D P K d w v)
  let E₂ := PressureBilinearLocalization.commutatorCoefficient e A K L c v dw
  have hT : ∀ p ∈ P, ∀ k ∈ K, ∀ b ∈ D, p + k + b ∈ T := by
    intro p hp k hk b hb
    exact (mem_finiteCutoffOutputModes_iff D _ _).mpr
      ⟨b, hb, p + k, (mem_finiteCutoffOutputModes_iff P K _).mpr ⟨p, hp, k, hk, rfl⟩,
        add_comm _ _⟩
  have hQT : ∀ a ∈ A, ∀ t ∈ T, a + t ∈ Q := by
    intro a ha t ht
    obtain ⟨b, hb, pk, hpk, rfl⟩ := (mem_finiteCutoffOutputModes_iff D _ _).mp ht
    obtain ⟨p, hp, k, hk, rfl⟩ := (mem_finiteCutoffOutputModes_iff P K _).mp hpk
    exact hQ a ha b hb p hp k hk
  have hQL : ∀ k ∈ K, ∀ l ∈ L, ∀ a ∈ A, k + l + a ∈ Q := by
    intro k hk l hl a ha
    obtain ⟨b, hb, p, hp, rfl⟩ := (mem_finiteCutoffOutputModes_iff D P _).mp hl
    rw [show k + (b + p) + a = a + (b + (p + k)) by abel]
    exact hQ a ha b hb p hp k hk
  have h₁ := sum_norm_vectorConvolution_sq_le A T Q c
    (PressureBilinearLocalization.commutatorCoefficient e D P K d w v) hQT
  have h₁' := mul_le_mul_of_nonneg_left
    (PressureBilinearLocalization.commutator_energy_le e he D P K T d w v hw hT)
    (sq_nonneg (∑ a ∈ A, ‖c a‖))
  have hfirst : (∑ q ∈ Q, ‖E₁ q‖ ^ 2) ≤
      (∑ a ∈ A, ‖c a‖) ^ 2 *
        (144 * (∑ p ∈ P, ‖coefficientVec (w p)‖ / ‖frequencyVec p‖) ^ 2 *
          (∑ k ∈ K, ‖coefficientVec (v k)‖) ^ 2 * coordinateEnergy D d) := h₁.trans h₁'
  have h₂ := PressureBilinearLocalization.commutator_energy_le e he A K L Q c v dw hv hQL
  have hl := sum_norm_cutoff_le D P d w
  have hl0 : 0 ≤ ∑ l ∈ L, ‖coefficientVec (dw l)‖ := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hlsq := pow_le_pow_left₀ hl0 hl 2
  have hG : 0 ≤ coordinateEnergy A c := by unfold coordinateEnergy scalarEnergy; positivity
  have hm := mul_le_mul_of_nonneg_right hlsq
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 144)
      (sq_nonneg (∑ k ∈ K, ‖coefficientVec (v k)‖ / ‖frequencyVec k‖))) hG)
  have hsecond : (∑ q ∈ Q, ‖E₂ q‖ ^ 2) ≤
      144 * (∑ k ∈ K, ‖coefficientVec (v k)‖ / ‖frequencyVec k‖) ^ 2 *
        ((∑ b ∈ D, ‖d b‖) * (∑ p ∈ P, ‖coefficientVec (w p)‖)) ^ 2 * coordinateEnergy A c := by
    nlinarith only [h₂, hm]
  have hp (q : Wavevector) : ‖E₁ q + E₂ q‖ ^ 2 ≤ 2 * ‖E₁ q‖ ^ 2 + 2 * ‖E₂ q‖ ^ 2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (E₁ q) (E₂ q)) 2
    nlinarith only [hn, sq_nonneg (‖E₁ q‖ - ‖E₂ q‖)]
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ Q) ↦ hp q)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  change (∑ q ∈ Q, ‖E₁ q + E₂ q‖ ^ 2) ≤ _
  unfold twoInputCost
  nlinarith only [hs, hfirst, hsecond]

/-- The localized pressure retains both actual misalignment channels,
including the divergence created by multiplication by a cutoff. -/
theorem doublyLocalizedOutput_energy_le (e : R3) (he : ‖e‖ = 1)
    (A D P K Q : Finset Wavevector) (c d : Wavevector → ℂ) (w v : FourierVelocity)
    (hw : w 0 = 0) (hv : v 0 = 0)
    (hQ : ∀ a ∈ A, ∀ b ∈ D, ∀ p ∈ P, ∀ k ∈ K, a + (b + (p + k)) ∈ Q) :
    let W := finiteCutoffConvolutionCoeff D P d w
    let V := finiteCutoffConvolutionCoeff A K c v
    (∑ q ∈ Q, ‖doublyLocalizedOutput e A D P K c d w v q‖ ^ 2) ≤
      16 * (∑ p ∈ finiteCutoffOutputModes D P, localizationDefect e p (W p)) ^ 2 *
        (∑ k ∈ finiteCutoffOutputModes A K, ‖coefficientVec (V k)‖ ^ 2) +
      16 * (∑ p ∈ finiteCutoffOutputModes D P, ‖coefficientVec (W p)‖) ^ 2 *
        (∑ k ∈ finiteCutoffOutputModes A K, localizationDefect e k (V k) ^ 2) +
      2 * twoInputCost A D P K c d w v := by
  dsimp only
  have hmain := sum_norm_pairConvolution_sq_le e he
    (finiteCutoffOutputModes D P) (finiteCutoffOutputModes A K) Q
    (finiteCutoffConvolutionCoeff D P d w) (finiteCutoffConvolutionCoeff A K c v) (by
      intro l hl r hr
      obtain ⟨b, hb, p, hp, rfl⟩ := (mem_finiteCutoffOutputModes_iff D P _).mp hl
      obtain ⟨a, ha, k, hk, rfl⟩ := (mem_finiteCutoffOutputModes_iff A K _).mp hr
      rw [show b + p + (a + k) = a + (b + (p + k)) by abel]
      exact hQ a ha b hb p hp k hk)
  have herr := twoInputCommutator_energy_le e he A D P K Q c d w v hw hv hQ
  have hp (q : Wavevector) : ‖doublyLocalizedOutput e A D P K c d w v q‖ ^ 2 ≤
      2 * ‖localizedInputs e A D P K c d w v q‖ ^ 2 +
        2 * ‖twoInputCommutator e A D P K c d w v q‖ ^ 2 := by
    have heq : doublyLocalizedOutput e A D P K c d w v q =
        localizedInputs e A D P K c d w v q + twoInputCommutator e A D P K c d w v q := by
      rw [← doublyLocalizedOutput_sub_localizedInputs]
      abel
    rw [heq]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_add_le (localizedInputs e A D P K c d w v q) (twoInputCommutator e A D P K c d w v q)) 2
    nlinarith only [hn, sq_nonneg (‖localizedInputs e A D P K c d w v q‖ -
      ‖twoInputCommutator e A D P K c d w v q‖)]
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ Q) ↦ hp q)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, localizedInputs] at hs
  linarith only [hs, hmain, herr]

end Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputEnergy
