import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialCoefficientRecovery

/-!
# Actual local Navier–Stokes solutions from finite Fourier data

Finite support supplies every required spatial jet. Reality and
transversality are checked on the prescribed coefficients; the physical
local-solution constructor recovers those same initial coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierFiniteLocalSolution

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeInfiniteFourierDerivative PancakeSpatialCoefficientRecovery
open PancakeArbitraryDataBlocks PancakeHigherLocalVelocity PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail FourierFiniteJets FourierFiniteSupport

theorem exists_localMomentEnvelope (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0)
    (hm : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hd : ∀ q, modeDot q (u q) = 0) (hzero : u 0 = 0)
    (ν : ℝ) (hν : 0 < ν) (p : ℕ) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν u T B,
      ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
        ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment p (s.coefficients t) k ≤ g k := by
  have hf : torusFourierVelocity (fullFourierField id u) = u := by
    funext q i
    apply mFourierCoeff_fullFourierField_component
    exact summable_of_ne_finset_zero (s := modes) (fun k hk ↦ by rw [hs k hk, norm_zero])
  have hreal (x : UnitAddTorus (Fin 3)) (i : Fin 3) :
      (fullFourierField id u x i).im = 0 := by
    rw [fullFourierField_eq_sum modes u hs]
    exact finiteFourierReconstruction_im_eq_zero_of_neg_closed modes u hm hr x i
  have h := exists_physical_localMomentEnvelope p ν hν (fullFourierField id u)
    (hasContinuousCoordinateJet_component modes u hs (p + 6))
    (fun x i ↦ by apply Complex.ext <;> simp [hreal])
    (by rw [hf]; exact hd) (by rw [hf]; exact hzero)
  rwa [hf] at h

end Mettapedia.FluidDynamics.NavierStokes.FourierFiniteLocalSolution
