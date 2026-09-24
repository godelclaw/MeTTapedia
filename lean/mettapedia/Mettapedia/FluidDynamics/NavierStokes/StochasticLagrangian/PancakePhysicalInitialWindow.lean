import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeUniformLocalSobolev
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalFieldReconstruction

/-!
# Uniform a priori window from physical initial derivatives

The initial Fourier envelope is constructed from the actual coordinate
derivatives of the input field. No regularity bound on a future trajectory
is assumed. The remaining extension-to-the-window task is explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalInitialWindow

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet PancakeCompactJetEnvelope
open PancakePhysicalFieldReconstruction PancakeUniformLocalSobolev PancakeSobolevVelocityRate
open PancakeLocalVelocityExistence PancakeCurlOutputTail

local notation "T3" => UnitAddTorus (Fin 3)

theorem exists_physical_initialEnvelope (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i)) :
    ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ k, fourierMoment 2 (torusFourierVelocity f) k ≤ g k := by
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) :=
    (hf i).1 0 0 (by norm_num)
  obtain ⟨g, hg, hSum, hu⟩ := exists_common_secondMoment_envelope
    (fun _ : Unit ↦ f) (fun _ ↦ hf)
    (fun i ↦ (hc i).comp continuous_snd)
    (fun i j ↦ ((hf i).1 j 6 le_rfl).comp continuous_snd)
  exact ⟨g, hg, hSum, hu ()⟩

/-- Construct the common a priori window from physical initial regularity,
and construct a local solution at every cutoff. The time bound applies on
each solution's overlap with the common window; it does not extend it. -/
theorem exists_physical_uniform_aPriori_window (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ k, modeDot k (torusFourierVelocity f k) = 0) :
    ∃ tau > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∀ M : Finset Wavevector,
      (∀ k, -k ∈ M ↔ k ∈ M) → (∀ k ∈ M, frequencyVec k ≠ 0) →
      ∃ T > (0 : ℝ), ∃ s : LocalVelocitySolution M nu (torusFourierVelocity f) T,
        ∀ t ∈ Set.Icc (0 : ℝ) T, t ≤ tau → sobolevEnergy M (s.coefficients t) ≤ B := by
  obtain ⟨g, hg, hSum, hu⟩ := exists_physical_initialEnvelope f hf
  obtain ⟨tau, htau, B, hB, hb⟩ := exists_uniform_initialEnvelope_window nu hnu
    (torusFourierVelocity f) g hg hSum hu
  refine ⟨tau, htau, B, hB, fun M hs hk ↦ ?_⟩
  obtain ⟨T, hT, ⟨s⟩⟩ := exists_localVelocitySolution M nu (torusFourierVelocity f) hs hk
    (torusFourierVelocity_conjugate f hr) (fun k _ ↦ hd k)
  exact ⟨T, hT, s, hb M T s hk⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalInitialWindow
