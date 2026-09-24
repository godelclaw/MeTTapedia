import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityUnique

/-!
# Local retained evolution from physical L2 data

The initial coefficients are the Fourier integrals of actual L2 fields.
Almost-everywhere reality gives conjugate symmetry; incompressibility is
stated as the Fourier divergence condition. Parseval pays both kinetic
energy and integrated enstrophy with the same physical initial energy for
every retained set. The individual local lifespans are not yet uniform.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalL2Velocity

open scoped BigOperators ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeArbitraryDataBlocks PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeLocalVelocityExistence PancakeLocalVelocityEnergy
open PancakeViscousMisalignmentAbsorption

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem l2FourierVelocity_conjugate (u₀ : TorusL2Velocity)
    (hr : ∀ i, ∀ᵐ x : T3, conj (u₀ i x) = u₀ i x) (k : Wavevector) :
    l2FourierVelocity u₀ (-k) = coefficientConjugate (l2FourierVelocity u₀ k) := by
  funext i
  simp only [l2FourierVelocity, coefficientConjugate, UnitAddTorus.mFourierCoeff, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [hr i] with x hx
  simp [map_mul, UnitAddTorus.mFourier_neg, hx]

theorem fullEnergy_l2_le (M : Finset Wavevector) (u₀ : TorusL2Velocity) :
    fullEnergy M (l2FourierVelocity u₀) ≤ totalL2VelocityEnergy u₀ := by
  have hs := hasSum_coefficientEnergy_l2FourierVelocity u₀
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum M (fun k _ ↦
    Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg _))

/-- The same physical L2 energy pays every constructed cutoff solution.
This quantifier order does not assert a common positive lifespan. -/
theorem exists_localL2Velocity (nu : ℝ) (hnu : 0 ≤ nu) (u₀ : TorusL2Velocity)
    (hr : ∀ i, ∀ᵐ x : T3, conj (u₀ i x) = u₀ i x)
    (hd : ∀ q, modeDot q (l2FourierVelocity u₀ q) = 0)
    (M : Finset Wavevector) (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0) :
    ∃ T > (0 : ℝ), ∃ s : LocalVelocitySolution M nu (l2FourierVelocity u₀) T,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        fullEnergy M (s.coefficients t) ≤ totalL2VelocityEnergy u₀ ∧
        2 * nu * (∫ tau in (0 : ℝ)..t, fullEnergy M (fourierCurl (s.coefficients tau))) ≤
          totalL2VelocityEnergy u₀ := by
  obtain ⟨T, hT, ⟨s⟩⟩ := exists_localVelocitySolution M nu (l2FourierVelocity u₀)
    hs hk (l2FourierVelocity_conjugate u₀ hr) (fun q _ ↦ hd q)
  refine ⟨T, hT, s, fun t ht ↦ ?_⟩
  exact ⟨(kinetic_bound s hnu hs t ht).trans (fullEnergy_l2_le M u₀),
    (integrated_enstrophy_bound s hs t ht).trans (fullEnergy_l2_le M u₀)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalL2Velocity
