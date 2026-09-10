import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltOrigin
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity

/-!
# Local Navier–Stokes evolution from the pressure-tilt datum

Finite Fourier support supplies every coordinate jet required by the
physical local-solution constructor. The solution has the prescribed
initial coefficients and a common summable moment envelope. It is not
an affine curve with an assigned tangent.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltLocalSolution

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeInfiniteFourierDerivative
open PancakeArbitraryDataBlocks PancakeHigherLocalVelocity PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PressureTiltDatum PressureTiltOrigin FourierFiniteJets

theorem torusFourierVelocity_fullVelocity (epsilon : ℝ) :
    torusFourierVelocity (fullFourierField id (velocity epsilon)) = velocity epsilon := by
  funext q i
  exact fullVelocity_fourierCoeff epsilon q i

/-- Every positive viscosity and every parameter give an actual local solution. -/
theorem exists_localMomentEnvelope (epsilon nu : ℝ) (hnu : 0 < nu) (p : ℕ) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity epsilon) T B,
      ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
        ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment p (s.coefficients t) k ≤ g k := by
  have hr (x : UnitAddTorus (Fin 3)) (i : Fin 3) :
      conj (fullFourierField id (velocity epsilon) x i) =
        fullFourierField id (velocity epsilon) x i := by
    apply Complex.ext <;> simp [fullVelocity_real]
  have h := exists_physical_localMomentEnvelope p nu hnu
    (fullFourierField id (velocity epsilon))
    (hasContinuousCoordinateJet_component modes _ (velocity_eq_zero_of_not_mem epsilon) (p + 6))
    hr
    (by rw [torusFourierVelocity_fullVelocity]; exact velocity_transverse epsilon)
    (by rw [torusFourierVelocity_fullVelocity]; exact velocity_zero epsilon)
  rw [torusFourierVelocity_fullVelocity epsilon] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltLocalSolution
