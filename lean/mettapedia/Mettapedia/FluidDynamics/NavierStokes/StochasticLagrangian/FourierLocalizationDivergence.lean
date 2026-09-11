import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressureConvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierResolventSmoothing
import Mettapedia.Analysis.FiniteConvolutionEnergy

/-!
# Divergence created by actual finite Fourier localization

Multiplication by a scalar patch commutes with a fixed transverse projection
but not with divergence. For divergence-free input the entire divergence is
the convolution with the patch gradient. Its energy is controlled by the
patch's actual first-derivative Fourier energy and the field's Fourier l1
norm. On an output band above radius R the normalized defect gains R^(-2).
No scale-uniform control of the remaining l1 norm is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFiniteFourierLocalization PancakeLowPressureBudget PancakeFourierPressureStrain
open ComplexTransverseMatrix ComplexPressureMisalignment ComplexPressurePair
open FourierResolventSmoothing FourierEllipticProductEnergy
open Mettapedia.Analysis.FiniteConvolutionEnergy

theorem modeDot_finiteCutoffConvolutionCoeff (P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (q : Wavevector) :
    modeDot q (finiteCutoffConvolutionCoeff P K c w q) =
      ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q,
        c pk.1 * (modeDot pk.1 (w pk.2) + modeDot pk.2 (w pk.2)) := by
  rw [finiteCutoffConvolutionCoeff, modeDot_sum]
  apply Finset.sum_congr rfl
  intro pk hpk
  rw [modeDot_smul, ← (Finset.mem_filter.mp hpk).2, modeDot_add_wavevector]

theorem modeDot_localized_of_divergenceFree (P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity)
    (hw : ∀ k ∈ K, modeDot k (w k) = 0) (q : Wavevector) :
    modeDot q (finiteCutoffConvolutionCoeff P K c w q) =
      ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, c pk.1 * modeDot pk.1 (w pk.2) := by
  rw [modeDot_finiteCutoffConvolutionCoeff]
  apply Finset.sum_congr rfl
  intro pk hpk
  rw [hw _ (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).2, add_zero]

theorem transverse_localized (e : EuclideanSpace ℝ (Fin 3)) (P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (q : Wavevector) :
    transverse e (coefficientVec (finiteCutoffConvolutionCoeff P K c w q)) =
      coefficientVec (finiteCutoffConvolutionCoeff P K c (fun k ↦ transverseCoefficient e (w k)) q) := by
  simp only [finiteCutoffConvolutionCoeff, coefficientVec, WithLp.toLp_sum, WithLp.toLp_smul]
  change transverse e (∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q,
    c pk.1 • coefficientVec (w pk.2)) =
      ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, c pk.1 • transverse e (coefficientVec (w pk.2))
  rw [transverse_sum]
  apply Finset.sum_congr rfl
  intro pk _
  exact transverse_smul e _ _

theorem sum_norm_divergence_sq_le (P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity)
    (hw : ∀ k ∈ K, modeDot k (w k) = 0) :
    (∑ q ∈ finiteCutoffOutputModes P K, ‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ ^ 2) ≤
      (∑ k ∈ K, ‖coefficientVec (w k)‖) ^ 2 * coordinateEnergy P c := by
  have hswap (q : Wavevector) : modeDot q (finiteCutoffConvolutionCoeff P K c w q) =
      ∑ kp ∈ K ×ˢ P with kp.1 + kp.2 = q, c kp.2 * modeDot kp.2 (w kp.1) := by
    rw [modeDot_localized_of_divergenceFree P K c w hw q]
    apply Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector)
    · intro pk
      simp only [Finset.mem_filter, Finset.mem_product, Equiv.prodComm_apply,
        Prod.fst_swap, Prod.snd_swap, add_comm, and_comm]
    · intros
      rfl
  have h := sum_norm_sq_le K P (finiteCutoffOutputModes P K)
    (fun k ↦ ‖coefficientVec (w k)‖) (fun p ↦ ‖frequencyVec p‖ * ‖c p‖)
    (fun k p ↦ c p * modeDot p (w k)) (fun _ _ ↦ norm_nonneg _)
    (fun k _ p _ ↦ by
      rw [norm_mul]
      calc
        _ ≤ ‖c p‖ * (‖frequencyVec p‖ * ‖coefficientVec (w k)‖) :=
          mul_le_mul_of_nonneg_left (norm_modeDot_le p (w k)) (norm_nonneg _)
        _ = _ := by ring)
    (fun k hk p hp ↦ (mem_finiteCutoffOutputModes_iff P K (k + p)).mpr ⟨p, hp, k, hk, add_comm _ _⟩)
  simpa only [← hswap, coordinateEnergy_eq, mul_pow, norm_frequencyVec_eq] using h

/-- Output zero contributes no normalized divergence. An arbitrary finite
output band pays its actual inverse radius, not the input frequency. -/
theorem sum_normalized_divergence_sq_le (P K Q : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity)
    (hw : ∀ k ∈ K, modeDot k (w k) = 0)
    (hQ : Q ⊆ finiteCutoffOutputModes P K) (R : ℝ) (hR : 0 ≤ R)
    (hband : ∀ q ∈ Q, q ≠ 0 → R ≤ ‖frequencyVec q‖) :
    R ^ 2 * (∑ q ∈ Q,
      (‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ / ‖frequencyVec q‖) ^ 2) ≤
      (∑ k ∈ K, ‖coefficientVec (w k)‖) ^ 2 * coordinateEnergy P c := by
  have hp (q : Wavevector) (hq : q ∈ Q) :
      R ^ 2 * (‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ / ‖frequencyVec q‖) ^ 2 ≤
        ‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ ^ 2 := by
    by_cases hz : q = 0
    · subst q
      simp [modeDot]
    have hn := norm_pos_iff.mpr (frequencyVec_ne_zero hz)
    calc
      _ ≤ ‖frequencyVec q‖ ^ 2 *
          (‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ / ‖frequencyVec q‖) ^ 2 := by
        gcongr
        exact hband q hq hz
      _ = _ := by field_simp
  calc
    _ = ∑ q ∈ Q, R ^ 2 *
        (‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ / ‖frequencyVec q‖) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ q ∈ Q, ‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ ^ 2 := Finset.sum_le_sum hp
    _ ≤ ∑ q ∈ finiteCutoffOutputModes P K, ‖modeDot q (finiteCutoffConvolutionCoeff P K c w q)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ _ := sum_norm_divergence_sq_le P K c w hw

end Mettapedia.FluidDynamics.NavierStokes.FourierLocalizationDivergence
