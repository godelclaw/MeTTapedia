import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConvectionPathLimit

/-!
# Identification of the limiting convolution with finite Galerkin convection

Finite support eliminates the infinite tail exactly. Source transversality
then transfers the receiver derivative to the fixed output frequency.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeConvectionFiberIdentity

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeSobolevFiberEnvelope PancakeConvectionPathLimit
open PancakeSignedTransportEnergy PancakeGalerkinCoefficientLimit
open PancakeCoefficientLimitProperties PancakeSobolevVelocityRate
open PancakeLocalVelocityExistence

theorem convectionConvolution_eq_outputFiber (M : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ M → u k = 0)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) (i : Fin 3) :
    convectionConvolution M u q i = ∑ k ∈ M, outputFiber q u k i := by
  classical
  simp only [convectionConvolution, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hdot : modeDot (q-k) (u k) = modeDot q (u k) := by
    rw [modeDot_sub_left, hd k hk, sub_zero]
  by_cases hm : q-k ∈ M
  · rw [Finset.sum_eq_single (q-k)]
    · simp [orderedConvection, outputFiber, hdot]
    · intro l hl hne
      have he : k+l ≠ q := by
        intro h
        exact hne (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h))
      simp [he]
    · exact fun hn ↦ (hn hm).elim
  · have hz : outputFiber q u k i = 0 := by simp [outputFiber, hs (q-k) hm]
    rw [hz]
    apply Finset.sum_eq_zero
    intro l hl
    have he : k+l ≠ q := by
      intro h
      have hlq : l = q-k := eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)
      exact hm (hlq ▸ hl)
    simp [he]

theorem tsum_outputFiber_eq_convectionConvolution (M : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ M → u k = 0)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) (i : Fin 3) :
    (∑' k, outputFiber q u k i) = convectionConvolution M u q i := by
  rw [convectionConvolution_eq_outputFiber M u hs hd]
  apply tsum_eq_sum
  intro k hk
  simp [outputFiber, hs k hk, modeDot]

theorem solution_convectionPath_apply {nu T : ℝ} {u₀ : FourierVelocity}
    {M : Finset Wavevector} (s : LocalVelocitySolution M nu u₀ T)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ t, t ∈ Set.Icc (0 : ℝ) T → sobolevEnergy M (s.coefficients t) ≤ B)
    (q : Wavevector) (i : Fin 3) (t : Set.Icc (0 : ℝ) T) :
    convectionPath q (solutionPaths s) i t =
      convectionConvolution M (s.coefficients t) q i := by
  rw [convectionPath_apply q (solutionPaths s) B hB]
  · exact tsum_outputFiber_eq_convectionConvolution M _ (s.support t) (s.transverse t) q i
  · intro τ F
    exact (sobolevEnergy_of_support_le M F _ (s.support τ)).trans (hE τ τ.2)

end Mettapedia.FluidDynamics.NavierStokes.PancakeConvectionFiberIdentity
