import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialMeanRegularity

/-!
# Spatially averaged signed balance for the actual radial source

Incompressibility removes the product-torus transport after integration.
The remaining rate is the explicit derivative of the actual periodic kernel
pairing, not a prescribed budget. Time weighting preserves its sign.
These are local identities at fixed cutoff, not cutoff-uniform estimates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance

open scoped Topology
open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity
open Mettapedia.Analysis UnitTorusMaterialBalance
open LocalRadialMeanRegularity

local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem absolutelyContinuousOnInterval_mean (n N : ℕ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x : T6, density n N (s.coefficients t) x) a b := by
  have hac := UnitTorusMaterialBalance.absolutelyContinuousOnInterval_mean
    (fun t ↦ density n N (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu n N)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu n N) a b
  apply AbsolutelyContinuousComposition.congr hac
  intro t ht
  dsimp only
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab t (by simpa only [uIcc_of_le hab] using ht)]

theorem ae_hasDerivAt_mean (n N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b →
      Integrable (explicitRate n N nu (s.coefficients t)) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6, density n N (s.coefficients τ) x)
        (meanRate n N nu (s.coefficients t)) t := by
  have hd := ae_hasDerivAt_mean_materialRate
    (fun t ↦ density n N (LocalSpaceTimeExtension.coefficients s a b hab t))
    (fun t ↦ LocalAnnularMeanBalance.productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu n N)
    (fun _ ↦ LocalAnnularMeanBalance.continuous_productVelocity _)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu n N)
    (LocalAnnularMeanBalance.locallyLipschitz_extendedProductVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall
      (LocalAnnularMeanBalance.divergence_extendedProductVelocity s a b hab hI g hSum hu t))
  filter_upwards [hd] with t ht hmem
  have he : scalarMaterialRate
      (fun τ ↦ density n N (LocalSpaceTimeExtension.coefficients s a b hab τ))
      (LocalAnnularMeanBalance.productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t)) t =
      explicitRate n N nu (s.coefficients t) := by
    funext x
    exact (frozenMaterialRate_extension_eq s a b hab n N t hmem x).trans
      (frozenMaterialRate_eq s a b hab hI g hg hSum hu n N t hmem x)
  rw [he] at ht
  refine ⟨ht.1, ht.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with τ hτ
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab τ hτ]

theorem absolutelyContinuousOnInterval_source (n N : ℕ) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ VorticityRadialSource.source (2 * (n + 1)) N (s.coefficients t)) a b := by
  apply AbsolutelyContinuousComposition.congr
    (absolutelyContinuousOnInterval_mean s a b hab hI g hg hSum hu n N)
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  exact (integral_density_eq n N _
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI ht'))))))

theorem ae_hasDerivAt_source (n N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun τ ↦ VorticityRadialSource.source (2 * (n + 1)) N (s.coefficients τ))
        (meanRate n N nu (s.coefficients t)) t := by
  filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu n N] with t ht hmem
  apply (ht hmem).2.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with τ hτ
  exact (integral_density_eq n N _
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (Ioo_subset_Icc_self (hI hτ)))))).symm

theorem integral_source_eq_initial_add_weighted_rate (n N : ℕ) :
    IntervalIntegrable (fun t ↦ (b - t) * meanRate n N nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, VorticityRadialSource.source (2 * (n + 1)) N (s.coefficients t)) =
        (b - a) * VorticityRadialSource.source (2 * (n + 1)) N (s.coefficients a) +
          ∫ t in a..b, (b - t) * meanRate n N nu (s.coefficients t) :=
  AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (absolutelyContinuousOnInterval_source s a b hab hI g hg hSum hu n N)
    (ae_hasDerivAt_source s a b hab hI g hg hSum hu n N)

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance
