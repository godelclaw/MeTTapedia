import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalClusterAnisotropy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentRegularization

/-!
# The actual alignment rate with a joint cluster source

The joint remainder envelope preserves cancellation at spectral collisions.
Full-vorticity diffusion stays in the signed residual pairing and in the
regularizer rate. The resulting source is spatially integrable under the
actual third-moment regularity. It is not a diffusion-paid global bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalClusterMaterialRate

open scoped Topology RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeFilteredStrainDynamics PancakeFourierMaterialPaths PancakeRegularizedMaterialRate
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakePhysicalLaplacian
open PancakeDyadicDirectionEvolution PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments
open PancakeGalerkinKineticEnergy
open LocalAlignmentForcing LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentRegularization LocalSignedAlignmentBudget LocalClusterAnisotropy

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def clusterSource (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  jointEnvelope chi modes outputs u nu x +
    2 * ⟪residual chi modes u x, strainMismatch chi modes u x + nu • fullVorticityLaplacian u x⟫ +
    delta * vorticityNormRate u nu x

theorem materialRate_add_residual_eq_joint (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    materialRate chi modes outputs u delta nu x + ‖residual chi modes u x‖ ^ 2 =
      remainderAnisotropy (jointRemainder chi modes outputs u nu x)
        (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x) +
      2 * ⟪residual chi modes u x, strainMismatch chi modes u x + nu • fullVorticityLaplacian u x⟫ +
      delta * vorticityNormRate u nu x := by
  have h := linearRate_strainSquare (spatialStrain modes (filteredVelocity chi u) x) delta
    (fullVorticity u x) (jointRemainder chi modes outputs u nu x)
    (strainMismatch chi modes u x + nu • fullVorticityLaplacian u x)
  simp only [jointRemainder, ← add_assoc] at h
  unfold materialRate
  rw [h]
  simp only [LocalAlignmentForcing.residual, vorticityNormRate, jointRemainder, resolved_add_strainMismatch]
  ring

theorem continuous_fullVorticityLaplacian (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (fullVorticityLaplacian u) := by
  change Continuous (fun x : T3 ↦ fullVorticityLaplacian u x)
  simp_rw [← sum_fullCurlSecond u hu]
  exact continuous_finsetSum _ (fun j _ ↦ complexRealPartEuclideanCLM.continuous.comp
    (fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j (fourierCurl u)))).continuous)

theorem integrable_clusterSource (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (delta nu : ℝ) :
    Integrable (clusterSource chi modes outputs u delta nu) := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  have hL := continuous_fullVorticityLaplacian u hu
  have hR : Continuous (fun x : T3 ↦ 2 * ⟪residual chi modes u x,
      strainMismatch chi modes u x + nu • fullVorticityLaplacian u x⟫) :=
    continuous_const.mul ((continuous_residual chi modes u hu1).inner
      ((continuous_strainMismatch chi modes u hu1).add (continuous_const.smul hL)))
  have hV : Continuous (vorticityNormRate u nu) :=
    continuous_const.mul (hw.inner (((continuous_fullStrainOperator u hu1).clm_apply hw).add
      (continuous_const.smul hL)))
  exact ((integrable_jointEnvelope chi modes outputs u hu1 nu).add
    (hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).add
    ((hV.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul delta)

theorem ae_ae_materialRate_add_residual_le_clusterSource
    {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hB : 0 ≤ B) (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) (delta : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      materialRate chi modes outputs (s.coefficients t) delta nu x +
        ‖residual chi modes (s.coefficients t) x‖ ^ 2 ≤
      clusterSource chi modes outputs (s.coefficients t) delta nu x := by
  filter_upwards [ae_ae_abs_jointAnisotropy_le_clusterEnvelope s chi C hchi modes outputs hcut hchir
    hsub hout hs hk hB a b hab hI] with t ht
  exact ht.mono (fun x hx ↦ by
    rw [materialRate_add_residual_eq_joint]
    have h := (le_abs_self _).trans (hx (fullVorticity (s.coefficients t) x))
    unfold clusterSource jointEnvelope
    linarith)

end Mettapedia.FluidDynamics.NavierStokes.LocalClusterMaterialRate
