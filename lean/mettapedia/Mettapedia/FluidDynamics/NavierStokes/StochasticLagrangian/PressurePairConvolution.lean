import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairMisalignment
import Mettapedia.Analysis.FiniteTwoChannelConvolutionEnergy

/-!
# Finite real pressure-pair convolutions retaining both misalignment channels

The estimate is uniform in the input frequency ratio and finite support
sizes. It retains an l1 source norm and an l2 receiver norm. These are
real bilinear pair convolutions in a fixed frame; complex Fourier phases,
adaptive physical localization, and dynamical summation are separate steps.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePairConvolution

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad FourierPressureCommutator PancakeAnisotropyDepletion
open CoherentPressurePair PressurePairMisalignment
open Mettapedia.Analysis.FiniteConvolutionEnergy

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def pairConvolution (e : E3) (P K : Finset Wavevector) (w v : Wavevector → E3) (q : Wavevector) : E3 :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q,
    tiltPair e (realFrequency pk.1) (realFrequency pk.2) (w pk.1) (v pk.2)

/-- Transverse vorticity error plus half the normalized divergence
defect. The latter need not vanish for spatially localized amplitudes. -/
def localizationDefect (e : E3) (k : Wavevector) (w : E3) : ℝ :=
  ‖lineRemainder e w‖ + |⟪realFrequency k, w⟫| / (2 * ‖realFrequency k‖)

theorem localizationDefect_nonneg (e : E3) (k : Wavevector) (w : E3) :
    0 ≤ localizationDefect e k w := by unfold localizationDefect; positivity

theorem sum_norm_pairConvolution_sq_le_with_divergence (e : E3) (he : ‖e‖ = 1)
    (P K Q : Finset Wavevector) (w v : Wavevector → E3)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    (∑ q ∈ Q, ‖pairConvolution e P K w v q‖ ^ 2) ≤
      8 * (∑ p ∈ P, localizationDefect e p (w p)) ^ 2 * (∑ k ∈ K, ‖v k‖ ^ 2) +
        8 * (∑ p ∈ P, ‖w p‖) ^ 2 * (∑ k ∈ K, localizationDefect e k (v k) ^ 2) := by
  have h := sum_norm_sq_le_two_channels P K Q
    (fun p ↦ 2 * localizationDefect e p (w p)) (fun p ↦ 2 * ‖w p‖)
    (fun k ↦ ‖v k‖) (fun k ↦ localizationDefect e k (v k))
    (fun p k ↦ tiltPair e (realFrequency p) (realFrequency k) (w p) (v k))
    (fun p _ ↦ mul_nonneg (by norm_num) (localizationDefect_nonneg e p (w p)))
    (fun _ _ ↦ by positivity) (fun _ _ ↦ norm_nonneg _)
    (fun k _ ↦ localizationDefect_nonneg e k (v k))
    (fun p _ k _ ↦ by
      have h := norm_tiltPair_le_misalignment_add_divergence e (realFrequency p) (realFrequency k) (w p) (v k) he
      unfold localizationDefect
      simp only [div_eq_mul_inv, mul_inv_rev] at h ⊢
      norm_num only at h ⊢
      nlinarith only [h]) hQ
  simp only [← Finset.mul_sum] at h
  unfold pairConvolution
  nlinarith only [h]

theorem sum_norm_pairConvolution_sq_le (e : E3) (he : ‖e‖ = 1)
    (P K Q : Finset Wavevector) (w v : Wavevector → E3)
    (hw : ∀ p ∈ P, ⟪realFrequency p, w p⟫ = 0)
    (hv : ∀ k ∈ K, ⟪realFrequency k, v k⟫ = 0)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    (∑ q ∈ Q, ‖pairConvolution e P K w v q‖ ^ 2) ≤
      8 * (∑ p ∈ P, ‖lineRemainder e (w p)‖) ^ 2 * (∑ k ∈ K, ‖v k‖ ^ 2) +
        8 * (∑ p ∈ P, ‖w p‖) ^ 2 * (∑ k ∈ K, ‖lineRemainder e (v k)‖ ^ 2) := by
  have h := sum_norm_sq_le_two_channels P K Q
    (fun p ↦ 2 * ‖lineRemainder e (w p)‖) (fun p ↦ 2 * ‖w p‖)
    (fun k ↦ ‖v k‖) (fun k ↦ ‖lineRemainder e (v k)‖)
    (fun p k ↦ tiltPair e (realFrequency p) (realFrequency k) (w p) (v k))
    (fun _ _ ↦ by positivity) (fun _ _ ↦ by positivity)
    (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ norm_nonneg _)
    (fun p hp k hk ↦ by
      have h := norm_tiltPair_le_misalignment e (realFrequency p) (realFrequency k) (w p) (v k) he (hw p hp) (hv k hk)
      nlinarith only [h]) hQ
  simp only [← Finset.mul_sum] at h
  unfold pairConvolution
  nlinarith only [h]

theorem pairConvolution_eq_zero_of_aligned (e : E3) (he : ‖e‖ = 1)
    (P K : Finset Wavevector) (w v : Wavevector → E3)
    (hw : ∀ p ∈ P, ⟪realFrequency p, w p⟫ = 0)
    (hv : ∀ k ∈ K, ⟪realFrequency k, v k⟫ = 0)
    (hwz : ∀ p ∈ P, lineRemainder e (w p) = 0)
    (hvz : ∀ k ∈ K, lineRemainder e (v k) = 0) (q : Wavevector) :
    pairConvolution e P K w v q = 0 := by
  apply Finset.sum_eq_zero
  intro pk hpk
  have hp := (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).1
  have hk := (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).2
  have h := norm_tiltPair_le_misalignment e (realFrequency pk.1) (realFrequency pk.2)
    (w pk.1) (v pk.2) he (hw pk.1 hp) (hv pk.2 hk)
  rw [hwz pk.1 hp, hvz pk.2 hk, norm_zero, zero_mul, mul_zero, add_zero, mul_zero] at h
  exact norm_le_zero_iff.mp h

end Mettapedia.FluidDynamics.NavierStokes.PressurePairConvolution
