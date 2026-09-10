import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralClusterEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAESpectralDifferentiability

/-!
# Cluster-aware anisotropy of the actual local strain equation

The full nonviscous remainder and filtered strain Laplacian are kept
together. The actual strain derivative and almost-everywhere scalar
spectral differentiability justify the cluster envelope. No measurable
eigenvector is assumed, and no all-scale diffusion payment is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalClusterAnisotropy

open scoped Topology RealInnerProductSpace ComplexConjugate Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeMeasurableMaterialRate PancakeLocalSpatialVelocity PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakePhysicalLaplacian
open PancakePhysicalDiffusionLimit PancakeMappedFourierDiffusion
open LocalAlignmentForcing LocalLowDiffusionBudget LocalMeanAlignmentBalance
open LocalFilteredViscousDefect LocalFrozenAlignmentRate LocalAESpectralDifferentiability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def jointRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : R3 →L[ℝ] R3 :=
  nonviscousRemainder chi modes outputs u x + nu • strainLaplacian modes (filteredVelocity chi u) x

def jointEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  SpectralClusterEnvelope.envelope (spatialStrain modes (filteredVelocity chi u) x)
    (jointRemainder chi modes outputs u nu x) (fullVorticity u x)

theorem continuous_jointRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) : Continuous (jointRemainder chi modes outputs u nu) := by
  exact (continuous_nonviscousRemainder chi modes outputs u).add
    (continuous_const.smul (continuous_finsetSum _ (fun _ _ ↦ by
      unfold strainSecond PancakeMappedFourierDiffusion.mappedSecond
      exact continuous_mappedField _ _ _)))

theorem measurable_jointEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (nu : ℝ) :
    Measurable (jointEnvelope chi modes outputs u nu) :=
  SpectralClusterEnvelope.measurable_envelope _ _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_jointRemainder chi modes outputs u nu) (continuous_fullVorticity u hu)

theorem integrable_jointEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (nu : ℝ) :
    Integrable (jointEnvelope chi modes outputs u nu) := by
  have hc : Continuous (fun x : T3 ↦ 2 * ‖jointRemainder chi modes outputs u nu x‖ * ‖fullVorticity u x‖ ^ 2) :=
    (continuous_const.mul (continuous_jointRemainder chi modes outputs u nu).norm).mul
    ((continuous_fullVorticity u hu).norm.pow 2)
  refine (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    (measurable_jointEnvelope chi modes outputs u hu nu).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x ↦ by
    unfold jointEnvelope
    rw [Real.norm_eq_abs, abs_of_nonneg (SpectralClusterEnvelope.envelope_nonneg _ _ _)]
    exact SpectralClusterEnvelope.envelope_le_coarse _ _ _)

def frozenStrain (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) : SymmetricStrain :=
  spatialStrain modes (filteredVelocity chi (u (t + h))) (x + materialShift (velocity (u t) x) h)

theorem frozenStrain_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) :
    frozenStrain chi modes u t x 0 = spatialStrain modes (filteredVelocity chi (u t)) x := by
  have hs : materialShift (velocity (u t) x) 0 = 0 := by
    ext i
    simp [materialShift, torusPoint]
  simp only [frozenStrain, add_zero, hs]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)

include hchi hcut hchir hsub hout hs hk

theorem hasDerivAt_frozenStrain (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun h ↦ (frozenStrain chi modes s.coefficients t x h).1)
      (-(spatialStrain modes (filteredVelocity chi (s.coefficients t)) x).1 *
          (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x).1 +
        jointRemainder chi modes outputs (s.coefficients t) nu x) 0 := by
  obtain ⟨r, rfl⟩ := torusPoint_surjective x
  let v := velocity (s.coefficients t) (torusPoint r)
  let X : ℝ → X3 := fun τ i ↦ r i + (τ - t) * v i
  have hXt : X t = r := by funext i; simp only [X, sub_self, zero_mul, add_zero]
  have hX : HasDerivAt X (liftedVelocity s t (X t)) t := by
    rw [hXt]
    apply hasDerivAt_pi.mpr
    intro i
    have h := (((hasDerivAt_id t).sub_const t).mul_const (v i)).const_add (r i)
    simpa only [X, id_eq, one_mul, v, velocity, liftedVelocity, spatialField,
      complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, PiLp.toLp_apply] using h
  have hS := LocalFilteredStrain.hasDerivAt_strainAlong s chi C hchi modes outputs
    hcut hchir hsub hout hs hk X t ht hX
  rw [remainderAlong_viscous_split s chi modes outputs hsub hcut X t] at hS
  have hS' : HasDerivAt (fun τ ↦ (LocalFilteredStrain.strainAlong s chi modes X τ).1)
      (-(spatialStrain modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t))).1 *
          (spatialStrain modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t))).1 +
        jointRemainder chi modes outputs (s.coefficients t) nu (torusPoint (X t))) t := hS
  rw [hXt] at hS'
  have h' := hS'.scomp_of_eq 0 (h := fun h : ℝ ↦ t + h)
    ((hasDerivAt_id (0 : ℝ)).const_add t) (add_zero t).symm
  simpa only [frozenStrain, Function.comp_def, LocalFilteredStrain.strainAlong,
    id_eq, add_zero, one_smul, X, add_sub_cancel_left, torusPoint_line, v] using h'

theorem abs_jointAnisotropy_le_clusterEnvelope (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3)
    (hL : SpectralDifferentiable chi modes s.coefficients t x) (w : R3) :
    |remainderAnisotropy (jointRemainder chi modes outputs (s.coefficients t) nu x)
      (topVector (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) w| ≤
      SpectralClusterEnvelope.envelope (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)
        (jointRemainder chi modes outputs (s.coefficients t) nu x) w := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk t ht x
  have h := SpectralClusterEnvelope.abs_remainderAnisotropy_le_envelope
    (frozenStrain chi modes s.coefficients t x) (jointRemainder chi modes outputs (s.coefficients t) nu x) 0
    (by simpa only [frozenStrain_zero] using hS) hL w
  simpa only [frozenStrain_zero] using h

/-- The actual field estimate holds simultaneously for every vector,
including full vorticity, almost everywhere in time and space. -/
theorem ae_ae_abs_jointAnisotropy_le_clusterEnvelope (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3, ∀ w : R3,
    |remainderAnisotropy (jointRemainder chi modes outputs (s.coefficients t) nu x)
      (topVector (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) w| ≤
      SpectralClusterEnvelope.envelope (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)
        (jointRemainder chi modes outputs (s.coefficients t) nu x) w := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_spectralDifferentiable s a b hab hI chi modes hB] with t ht hL
  exact hL.mono (fun x hx w ↦ abs_jointAnisotropy_le_clusterEnvelope s chi C hchi modes outputs
    hcut hchir hsub hout hs hk t (hI (Set.Ioo_subset_Icc_self ht)) x hx w)

end Mettapedia.FluidDynamics.NavierStokes.LocalClusterAnisotropy
