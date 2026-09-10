import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalClusterAnisotropy

/-!
# Material differentiability of Lipschitz scalar functions of strain

The periodic real-space differentiability argument applies to any
Lipschitz scalar strain functional, not just the largest eigenvalue.
The constant time extension is used only to invoke the global theorem;
the conclusion is transferred back to the actual local solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralFunctionDifferentiability

open scoped Topology NNReal
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFilteredStrainDynamics
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeSpectralProjectorRegularity
open PancakeMeasurableMaterialRate
open LocalClusterAnisotropy LocalMeanAlignmentBalance LocalSpaceTimeExtension
open PeriodicMaterialDifferentiability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "ST" => ℝ × (Fin 3 → ℝ)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def ScalarDifferentiable (phi : SymmetricStrain → ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : Prop :=
  DifferentiableAt ℝ (fun h ↦ phi (frozenStrain chi modes u t x h)) 0

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (chi : Wavevector → ℂ) (modes : Finset Wavevector)

include hI in
theorem ae_ae_extended_scalarDifferentiable (hB : 0 ≤ B)
    (phi : SymmetricStrain → ℝ) (K : ℝ≥0) (hphi : LipschitzWith K phi) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T3, ScalarDifferentiable phi chi modes (coefficients s a b hab) t x := by
  have hS := continuous_parametric_strain modes chi (coefficients s a b hab)
    (fun q _ i ↦ (locallyLipschitz_coefficients s a b hab hI hB q i).continuous)
  have hSc : LocallyLipschitz (fun z : ST ↦
      spatialStrain modes (filteredVelocity chi (coefficients s a b hab z.1)) (torusPoint z.2)) :=
    locallyLipschitz_strain s a b hab hI hB chi modes
  exact ae_ae_differentiableAt_materialPath
    (fun t x ↦ phi (spatialStrain modes (filteredVelocity chi (coefficients s a b hab t)) x))
    (fun t ↦ velocity (coefficients s a b hab t))
    (hphi.continuous.comp hS) (fun _ ↦ continuous_velocity _) (hphi.locallyLipschitz.comp hSc)

theorem scalarDifferentiable_of_extension (phi : SymmetricStrain → ℝ)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (h : ScalarDifferentiable phi chi modes (coefficients s a b hab) t x) :
    ScalarDifferentiable phi chi modes s.coefficients t x := by
  unfold ScalarDifferentiable frozenStrain at h ⊢
  rw [coefficients_eq s a b hab t (Set.Ioo_subset_Icc_self ht)] at h
  apply h.congr_of_eventuallyEq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [coefficients_eq s a b hab (t + h) hh]

include hab hI in
theorem ae_ae_scalarDifferentiable (hB : 0 ≤ B)
    (phi : SymmetricStrain → ℝ) (K : ℝ≥0) (hphi : LipschitzWith K phi) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      ScalarDifferentiable phi chi modes s.coefficients t x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (ae_ae_extended_scalarDifferentiable s a b hab hI chi modes hB phi K hphi)] with t ht hx
  exact hx.mono (fun x h ↦ scalarDifferentiable_of_extension s a b hab chi modes phi t ht x h)

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralFunctionDifferentiability
