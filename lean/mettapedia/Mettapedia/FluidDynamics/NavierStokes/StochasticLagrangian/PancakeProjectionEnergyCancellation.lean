import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRetainedProjectionDefect
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierOrthogonality

/-!
# Signed energy cancellation of the actual projection defect

The discarded nonlinear outputs have zero unweighted pairing with the
retained physical vorticity. Consequently their spectral-gap-weighted
pairing is independent of the regularizing scalar identity. Spatial
variation of the remaining weight is not discarded or estimated here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeProjectionEnergyCancellation

open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeRetainedProjectionDefect PancakeFiniteFourierOrthogonality PancakePhysicalSpectralDefect
open PancakeFourierMaterialPaths PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeSignedTransportForcing PancakePhysicalWeightedTransport PancakeMaterialDiffusionBudget
open PancakeRegularizedDiffusion PancakeFrequencyProjectorCommutator

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierCurl_conjugate (u : FourierVelocity)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) :
    fourierCurl u (-q) = coefficientConjugate (fourierCurl u q) := by
  ext i
  fin_cases i <;> simp [fourierCurl, coefficientCross, wavevectorCoefficient,
    coefficientConjugate, hr, unitTorusDerivativePhase, map_ofNat] <;> ring

theorem integral_vorticity_discarded_zero (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ⟪spatialVorticity modes u x, discardedNonlinearField modes outputs u x⟫) = 0 := by
  apply integral_real_vector_inner_disjoint modes (outputs \ modes) (fourierCurl u) (nonlinearVorticityCoeff modes u)
  · exact Finset.disjoint_left.mpr (fun q hq ho ↦ (Finset.mem_sdiff.mp ho).2 hq)
  · intro x i
    exact finiteFourierReconstruction_im_eq_zero_of_neg_closed modes (fourierCurl u) hs
      (fourierCurl_conjugate u hr) x i

theorem integral_vorticity_fullForcing_zero
    (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ⟪spatialVorticity modes u x, spatialVorticityForcing (fun _ ↦ 1) modes u 0 x⟫) = 0 := by
  simp only [forcing_full_eq_negative_discarded modes outputs u _ hsub hout hk hu hs hr,
    inner_neg_right, integral_neg, integral_vorticity_discarded_zero modes outputs u hs hr, neg_zero]

theorem gapForcingPairing_delta_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (f : T3 → R3) (x : T3) :
    gapForcingPairing chi modes u delta f x = gapForcingPairing chi modes u 0 f x +
      (2 * delta) * ⟪spatialVorticity modes u x, f x⟫ := by
  simp only [gapForcingPairing, physicalGapWeight, regularizedGap, sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_left, real_inner_smul_left, add_zero]
  ring

theorem integral_projection_pairing_delta_independent
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta : ℝ)
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x) =
      ∫ x : T3, gapForcingPairing chi modes u 0 (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x := by
  have hf := continuous_vorticityForcing (fun _ ↦ 1) modes u 0
  have hi := (continuous_gapForcingPairing chi modes u 0 _ hf).integrable_of_hasCompactSupport
    (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hwc : Continuous (fun x : T3 ↦
      ⟪spatialVorticity modes u x, spatialVorticityForcing (fun _ ↦ 1) modes u 0 x⟫) :=
    (continuous_vorticity modes u).inner hf
  have hw := hwc.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have he : gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) =
      fun x ↦ gapForcingPairing chi modes u 0 (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x +
        (2 * delta) * ⟪spatialVorticity modes u x, spatialVorticityForcing (fun _ ↦ 1) modes u 0 x⟫ :=
    funext (gapForcingPairing_delta_split chi modes u delta _)
  rw [he]
  rw [integral_add hi (hw.const_mul _), integral_const_mul,
    integral_vorticity_fullForcing_zero modes outputs u hsub hout hk hu hs hr, mul_zero, add_zero]

end Mettapedia.FluidDynamics.NavierStokes.PancakeProjectionEnergyCancellation
