import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeDissipativeFiniteODE
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityUnique

/-!
# Continuation of the actual finite retained velocity equation

The exact kinetic cancellation makes the physical finite-dimensional
vector field dissipative. The generic cutoff construction consequently
produces the original equation on every prescribed finite forward interval.
This is finite-dimensional continuation, not continuum global regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteVelocityContinuation

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeGalerkinKineticEnergy PancakeFiniteLocalizedEvolution
open PancakeFiniteVelocitySmooth PancakeFiniteVelocityInvariant
open PancakeFrequencyProjectorCommutator PancakeViscousMisalignmentAbsorption
open PancakeLocalVelocityExistence PancakeLocalVelocityEnergy PancakeLocalVelocityUnique
open PancakeDissipativeFiniteODE

theorem physicalVelocityRHS_inner (M : Finset Wavevector) (nu : ℝ)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (v : physicalSubspace M) :
    2 * ⟪v, physicalVelocityRHS M nu v⟫ =
      -2 * nu * fullEnergy M (fourierCurl (extendCoefficients M v)) := by
  change 2 * ⟪(v : FiniteField M), (physicalVelocityRHS M nu v : FiniteField M)⟫ = _
  rw [physicalVelocityRHS_coe M nu hs hk, finiteVelocityRHS]
  nth_rw 1 [← restrict_extend M (v : FiniteField M)]
  rw [inner_restrictCoefficients]
  apply velocityRHS_energy_balance M (extendCoefficients M v) nu hs v.2.2
  intro q hq
  simpa [modeDot, extendCoefficients, hq] using v.2.1 ⟨q, hq⟩

theorem physicalVelocityRHS_dissipative (M : Finset Wavevector) (nu : ℝ)
    (hnu : 0 ≤ nu) (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0) (v : physicalSubspace M) :
    ⟪v, physicalVelocityRHS M nu v⟫ ≤ 0 := by
  have he := physicalVelocityRHS_inner M nu hs hk v
  have hn := mul_nonneg hnu (fullEnergy_nonneg M (fourierCurl (extendCoefficients M v)))
  nlinarith

/-- Construct a solution on any prescribed finite horizon. This does not
assume a prior local solution or an extension hypothesis. -/
theorem exists_finiteHorizon_velocitySolution (M : Finset Wavevector) (nu : ℝ)
    (hnu : 0 ≤ nu) (u₀ : FourierVelocity)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q ∈ M, modeDot q (u₀ q) = 0) (T : ℝ) (hT : 0 ≤ T) :
    Nonempty (LocalVelocitySolution M nu u₀ T) := by
  let v₀ : physicalSubspace M :=
    ⟨restrictCoefficients M u₀, restrictCoefficients_mem_physical M u₀ hs hr hd⟩
  obtain ⟨a, ha0, ha, _⟩ := exists_dissipative_solution (physicalVelocityRHS M nu)
    (contDiff_physicalVelocityRHS M nu)
    (physicalVelocityRHS_dissipative M nu hnu hs hk) v₀ T hT
  refine ⟨{
    coefficients := fun t ↦ extendCoefficients M (a t)
    initial := ?_
    support := ?_
    reality := fun t ↦ (a t).2.2
    transverse := ?_
    equation := fun t ht q hq i ↦
      hasDerivAt_extended_physical_curve M nu hs hk a t (ha t ht) q hq i
  }⟩
  · intro q hq
    rw [ha0]
    ext i
    simp [v₀, extendCoefficients, hq]
  · intro t q hq
    ext i
    simp [extendCoefficients, hq]
  · intro t q hq
    simpa [modeDot, extendCoefficients, hq] using (a t).2.1 ⟨q, hq⟩

/-- Restrict only the validity interval; the coefficient function is unchanged. -/
def restrictHorizon {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (S : ℝ) (hS : S ≤ T) :
    LocalVelocitySolution M nu u₀ S where
  coefficients := s.coefficients
  initial := s.initial
  support := s.support
  reality := s.reality
  transverse := s.transverse
  equation := fun t ht ↦ s.equation t ⟨ht.1, ht.2.trans hS⟩

/-- Any previously constructed local trajectory agrees with the new
longer-horizon trajectory wherever both equations are valid. -/
theorem finiteHorizon_agreement {M : Finset Wavevector} {nu T S : ℝ}
    {u₀ : FourierVelocity} (s : LocalVelocitySolution M nu u₀ T)
    (r : LocalVelocitySolution M nu u₀ S) (hnu : 0 ≤ nu)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) :
    Set.EqOn s.coefficients r.coefficients (Set.Icc (0 : ℝ) (min T S)) :=
  localVelocitySolution_unique (restrictHorizon s (min T S) (min_le_left _ _))
    (restrictHorizon r (min T S) (min_le_right _ _)) hnu hs

theorem exists_finiteHorizon_velocitySolution_with_energy (M : Finset Wavevector)
    (nu : ℝ) (hnu : 0 ≤ nu) (u₀ : FourierVelocity)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q ∈ M, modeDot q (u₀ q) = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ s : LocalVelocitySolution M nu u₀ T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      fullEnergy M (s.coefficients t) +
        2 * nu * (∫ tau in (0 : ℝ)..t, fullEnergy M (fourierCurl (s.coefficients tau))) =
        fullEnergy M u₀ := by
  obtain ⟨s⟩ := exists_finiteHorizon_velocitySolution M nu hnu u₀ hs hk hr hd T hT
  exact ⟨s, kinetic_balance s hs⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteVelocityContinuation
