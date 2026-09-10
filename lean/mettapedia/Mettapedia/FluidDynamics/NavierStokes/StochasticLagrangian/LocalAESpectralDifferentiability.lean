import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFrozenAlignmentRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicMaterialDifferentiability

/-!
# Actual spectral differentiability almost everywhere in space-time

The largest filtered-strain eigenvalue is locally Lipschitz in real
space-time on compact interior intervals of the actual local solution.
Its derivative in the full material direction therefore exists almost
everywhere. This is a scalar statement, with no chosen eigenframe
measurability or eigenvalue separation hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAESpectralDifferentiability

open scoped Topology
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFilteredStrainDynamics
open PancakeLocalInfiniteVelocity PancakeFrequencyProjectorCommutator PancakeFourierMaterialPaths
open PancakeMeasurableMaterialRate PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeTopEigenvalueDerivative
open LocalFrozenAlignmentRate LocalMeanAlignmentBalance LocalSpaceTimeExtension
open PeriodicMaterialDifferentiability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "ST" => ℝ × (Fin 3 → ℝ)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (chi : Wavevector → ℂ) (modes : Finset Wavevector)

include hI in
theorem ae_ae_extended_spectralDifferentiable (hB : 0 ≤ B) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T3, SpectralDifferentiable chi modes (coefficients s a b hab) t x := by
  have hS := continuous_parametric_strain modes chi (coefficients s a b hab)
    (fun q _ i ↦ (locallyLipschitz_coefficients s a b hab hI hB q i).continuous)
  have hSc : LocallyLipschitz (fun z : ST ↦
      spatialStrain modes (filteredVelocity chi (coefficients s a b hab z.1)) (torusPoint z.2)) :=
    locallyLipschitz_strain s a b hab hI hB chi modes
  exact ae_ae_differentiableAt_materialPath
    (fun t x ↦ topEigenvalue (spatialStrain modes (filteredVelocity chi (coefficients s a b hab t)) x))
    (fun t ↦ velocity (coefficients s a b hab t))
    (lipschitzWith_topEigenvalue.continuous.comp hS) (fun _ ↦ continuous_velocity _)
    (lipschitzWith_topEigenvalue.locallyLipschitz.comp hSc)

theorem spectralDifferentiable_of_extension (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (h : SpectralDifferentiable chi modes (coefficients s a b hab) t x) :
    SpectralDifferentiable chi modes s.coefficients t x := by
  unfold SpectralDifferentiable at h ⊢
  rw [coefficients_eq s a b hab t (Set.Ioo_subset_Icc_self ht)] at h
  apply h.congr_of_eventuallyEq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [coefficients_eq s a b hab (t + h) hh]

include hab hI in
/-- Spectral differentiability is derived for the original local solution,
not just for the auxiliary constant extension. -/
theorem ae_ae_spectralDifferentiable (hB : 0 ≤ B) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      SpectralDifferentiable chi modes s.coefficients t x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (ae_ae_extended_spectralDifferentiable s a b hab hI chi modes hB)] with t ht hx
  exact hx.mono (fun x h ↦ spectralDifferentiable_of_extension s a b hab chi modes t ht x h)

end Mettapedia.FluidDynamics.NavierStokes.LocalAESpectralDifferentiability
