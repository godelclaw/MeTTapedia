import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalNonlinearReconstruction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSignedTransportForcing

/-!
# The full-retained vorticity forcing is the discarded nonlinear output

The nonviscous forcing for transport by the full retained velocity is
exactly the negative reconstruction of nonlinear output frequencies
outside the retained set. It is not zero in general. The reduced
low-strain forcing consequently separates high-strain action from this
explicit projection defect.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeRetainedProjectionDefect

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakePhysicalNonlinearReconstruction PancakePhysicalSpectralDefect PancakeFilteredStrainDynamics
open PancakeVorticityTransportSplit PancakeFourierMaterialPaths PancakeSignedTransportForcing
open PancakeFrequencyProjectorCommutator PancakeBlockReality PancakeDyadicDirectionEvolution
open PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def nonlinearVorticityCoeff (modes : Finset Wavevector) (u : FourierVelocity) : FourierVelocity :=
  finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) 0

def discardedNonlinearField (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (finiteFourierReconstruction (outputs \ modes) (nonlinearVorticityCoeff modes u) x)

theorem reconstruction_sub_of_subset (modes outputs : Finset Wavevector) (a : FourierVelocity)
    (x : T3) (hsub : modes ⊆ outputs) :
    finiteFourierReconstruction modes a x - finiteFourierReconstruction outputs a x =
      -finiteFourierReconstruction (outputs \ modes) a x := by
  have h := Finset.sum_sdiff hsub (f := fun q ↦ UnitAddTorus.mFourier q x • a q)
  change finiteFourierReconstruction (outputs \ modes) a x + finiteFourierReconstruction modes a x =
    finiteFourierReconstruction outputs a x at h
  rw [← h]
  abel

theorem forcing_full_eq_reconstruction_difference
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spatialVorticityForcing (fun _ ↦ 1) modes u 0 x =
      complexRealPartEuclideanCLM (finiteFourierReconstruction modes (nonlinearVorticityCoeff modes u) x) -
        complexRealPartEuclideanCLM (finiteFourierReconstruction outputs (nonlinearVorticityCoeff modes u) x) := by
  have hf : filteredVelocity (fun _ ↦ 1) u = u := by funext q i; simp [filteredVelocity]
  rw [spatialVorticityForcing, spatialVorticityMaterialRate_transport_split (fun _ ↦ 1)
    modes u 0 x hs hr (fun _ ↦ by simp), hf]
  rw [nonlinearVorticityCoeff, reconstruction_nonlinear_physical modes outputs u x hout hk hu hs hr]
  abel

theorem forcing_full_eq_negative_discarded
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spatialVorticityForcing (fun _ ↦ 1) modes u 0 x = -discardedNonlinearField modes outputs u x := by
  rw [forcing_full_eq_reconstruction_difference modes outputs u x hout hk hu hs hr,
    ← map_sub, reconstruction_sub_of_subset modes outputs _ x hsub, map_neg]
  rfl

theorem reducedForcing_eq_highStrain_sub_discarded
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    reducedVorticityForcing chi modes u 0 x =
      ((spatialStrain modes u x).1 - (spatialStrain modes (filteredVelocity chi u) x).1)
        (spatialVorticity modes u x) - discardedNonlinearField modes outputs u x := by
  have hf : filteredVelocity (fun _ ↦ 1) u = u := by funext q i; simp [filteredVelocity]
  rw [reducedVorticityForcing, forcing_full_eq_negative_discarded modes outputs u x hsub hout hk hu hs hr, hf]
  abel

theorem continuous_discardedNonlinearField (modes outputs : Finset Wavevector) (u : FourierVelocity) :
    Continuous (discardedNonlinearField modes outputs u) :=
  complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)

end Mettapedia.FluidDynamics.NavierStokes.PancakeRetainedProjectionDefect
