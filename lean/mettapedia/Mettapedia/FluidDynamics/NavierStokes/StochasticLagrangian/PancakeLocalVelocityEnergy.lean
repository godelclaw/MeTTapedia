import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityExistence

/-!
# Energy and vorticity of the constructed local evolution

The local existence output is connected to the exact kinetic balance and
the existing finite vorticity equation. Energy constants have no mode-count
factor, while the constructed lifespan is not yet uniform in the cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityEnergy

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeGalerkinVorticityBridge PancakeFiniteLocalizedEvolution
open PancakeLocalVelocityExistence PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption

variable {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}

theorem initial_fullEnergy (s : LocalVelocitySolution M nu u₀ T) :
    fullEnergy M (s.coefficients 0) = fullEnergy M u₀ := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [s.initial q hq]

theorem mean_zero (s : LocalVelocitySolution M nu u₀ T)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0) (t : ℝ) : s.coefficients t 0 = 0 := by
  apply s.support
  intro h0
  exact hk 0 h0 (by ext i; simp [frequencyVec, coefficientVec,
    PancakePeriodicComplexStretch.wavevectorCoefficient])

theorem continuousOn_coefficients (s : LocalVelocitySolution M nu u₀ T) (q : Wavevector)
    (i : Fin 3) : ContinuousOn (fun t ↦ s.coefficients t q i) (Set.Icc (0 : ℝ) T) := by
  by_cases hq : q ∈ M
  · exact fun t ht ↦ (s.equation t ht q hq i).continuousAt.continuousWithinAt
  · have he : (fun t ↦ s.coefficients t q i) = fun _ ↦ (0 : ℂ) := by
      funext t
      rw [s.support t q hq]
      rfl
    rw [he]
    exact continuousOn_const

theorem hasDerivAt_vorticity (s : LocalVelocitySolution M nu u₀ T)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (q : Wavevector) (hq : q ∈ M) (i : Fin 3) :
    HasDerivAt (fun tau ↦ fourierCurl (s.coefficients tau) q i)
      (finiteUnitTorusVorticityRHS M M (fourierCurl (s.coefficients t))
        (fourierCurl (s.coefficients t)) nu q i) t :=
  hasDerivAt_vorticity_of_velocityRHS M s.coefficients nu t q hk (s.transverse t)
    (s.equation t ht q hq) i

theorem kinetic_balance (s : LocalVelocitySolution M nu u₀ T)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    fullEnergy M (s.coefficients t) +
      2 * nu * (∫ tau in (0 : ℝ)..t, fullEnergy M (fourierCurl (s.coefficients tau))) =
      fullEnergy M u₀ := by
  rw [← initial_fullEnergy s]
  apply integrated_kineticEnergy_identity M s.coefficients nu t ht.1 hs
  · exact fun tau _ ↦ s.reality tau
  · exact fun tau _ ↦ s.transverse tau
  · exact fun tau hτ ↦ s.equation tau ⟨hτ.1, hτ.2.trans ht.2⟩

theorem kinetic_bound (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 ≤ nu)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    fullEnergy M (s.coefficients t) ≤ fullEnergy M u₀ := by
  rw [← initial_fullEnergy s]
  exact kineticEnergy_le_initial M s.coefficients nu t hnu ht.1 hs
    (fun tau _ ↦ s.reality tau) (fun tau _ ↦ s.transverse tau)
    (fun tau hτ ↦ s.equation tau ⟨hτ.1, hτ.2.trans ht.2⟩)

theorem integrated_enstrophy_bound (s : LocalVelocitySolution M nu u₀ T)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    2 * nu * (∫ tau in (0 : ℝ)..t, fullEnergy M (fourierCurl (s.coefficients tau))) ≤
      fullEnergy M u₀ := by
  have h := kinetic_balance s hs t ht
  linarith [fullEnergy_nonneg M (s.coefficients t)]

/-- Local existence together with its exact balance, without an input
coefficient path or a supplied energy inequality. -/
theorem exists_localVelocitySolution_with_energy (M : Finset Wavevector) (nu : ℝ)
    (u₀ : FourierVelocity) (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q ∈ M, modeDot q (u₀ q) = 0) :
    ∃ T > (0 : ℝ), ∃ s : LocalVelocitySolution M nu u₀ T,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        fullEnergy M (s.coefficients t) +
          2 * nu * (∫ tau in (0 : ℝ)..t, fullEnergy M (fourierCurl (s.coefficients tau))) =
          fullEnergy M u₀ := by
  obtain ⟨T, hT, ⟨s⟩⟩ := exists_localVelocitySolution M nu u₀ hs hk hr hd
  exact ⟨T, hT, s, kinetic_balance s hs⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityEnergy
