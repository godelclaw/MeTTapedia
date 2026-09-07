import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteVelocityContinuation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalInitialWindow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalL2Velocity

/-!
# Constructed Galerkin solutions on one common positive interval

Finite-dimensional continuation closes the lifespan quantifier gap in
the uniform local Sobolev estimate. The physical initial derivative
hypothesis supplies the initial envelope, while the future trajectories
are constructed rather than assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCommonGalerkinWindow

open scoped BigOperators ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet
open PancakePhysicalFieldReconstruction PancakePhysicalInitialWindow
open PancakeUniformLocalSobolev PancakeSobolevVelocityRate PancakeCurlOutputTail
open PancakeLocalVelocityExistence PancakeLocalVelocityEnergy PancakeLocalL2Velocity
open PancakeFiniteVelocityContinuation PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy
open PancakeViscousMisalignmentAbsorption

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- All cutoffs now exist on the same interval, with the same second-order
energy bound. There is no cutoff-dependent lifespan in the conclusion. -/
theorem exists_common_initialEnvelope_solution (nu : ℝ) (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 2 u₀ k ≤ g k) :
    ∃ tau > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∀ M : Finset Wavevector,
      (∀ k, -k ∈ M ↔ k ∈ M) → (∀ k ∈ M, frequencyVec k ≠ 0) →
      ∃ s : LocalVelocitySolution M nu u₀ tau,
        ∀ t ∈ Set.Icc (0 : ℝ) tau, sobolevEnergy M (s.coefficients t) ≤ B := by
  obtain ⟨tau, htau, B, hB, hb⟩ :=
    exists_uniform_initialEnvelope_window nu hnu u₀ g hg hSum hu
  refine ⟨tau, htau, B, hB, fun M hs hk ↦ ?_⟩
  obtain ⟨s⟩ := exists_finiteHorizon_velocitySolution M nu hnu.le u₀ hs hk hr
    (fun q _ ↦ hd q) tau htau.le
  exact ⟨s, fun t ht ↦ hb M tau s hk t ht ht.2⟩

/-- The common interval and bound are constructed from the original
physical initial field, using its order-six coordinate derivatives. -/
theorem exists_common_physical_solution (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ k, modeDot k (torusFourierVelocity f k) = 0) :
    ∃ tau > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∀ M : Finset Wavevector,
      (∀ k, -k ∈ M ↔ k ∈ M) → (∀ k ∈ M, frequencyVec k ≠ 0) →
      ∃ s : LocalVelocitySolution M nu (torusFourierVelocity f) tau,
        ∀ t ∈ Set.Icc (0 : ℝ) tau, sobolevEnergy M (s.coefficients t) ≤ B := by
  obtain ⟨g, hg, hSum, hu⟩ := exists_physical_initialEnvelope f hf
  exact exists_common_initialEnvelope_solution nu hnu (torusFourierVelocity f)
    (torusFourierVelocity_conjugate f hr) hd g hg hSum hu

/-- For merely physical L2 initial data, all finite cutoffs exist on any
prescribed finite horizon with the same physical kinetic-energy payment.
This asserts no uniform high-regularity estimate for L2 data. -/
theorem exists_finiteHorizon_L2_solution (nu : ℝ) (hnu : 0 ≤ nu)
    (u₀ : TorusL2Velocity) (hr : ∀ i, ∀ᵐ x : T3, conj (u₀ i x) = u₀ i x)
    (hd : ∀ q, modeDot q (l2FourierVelocity u₀ q) = 0)
    (T : ℝ) (hT : 0 ≤ T) (M : Finset Wavevector)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0) :
    ∃ s : LocalVelocitySolution M nu (l2FourierVelocity u₀) T,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        fullEnergy M (s.coefficients t) ≤ totalL2VelocityEnergy u₀ ∧
        2 * nu * (∫ tau in (0 : ℝ)..t, fullEnergy M (fourierCurl (s.coefficients tau))) ≤
          totalL2VelocityEnergy u₀ := by
  obtain ⟨s⟩ := exists_finiteHorizon_velocitySolution M nu hnu (l2FourierVelocity u₀)
    hs hk (l2FourierVelocity_conjugate u₀ hr) (fun q _ ↦ hd q) T hT
  exact ⟨s, fun t ht ↦
    ⟨(kinetic_bound s hnu hs t ht).trans (fullEnergy_l2_le M u₀),
      (integrated_enstrophy_bound s hs t ht).trans (fullEnergy_l2_le M u₀)⟩⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeCommonGalerkinWindow
