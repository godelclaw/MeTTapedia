import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSmoothMeanRegularity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularExplicitRate

/-!
# Signed spatial-mean evolution of the smooth retained source

The material rate is identified pointwise by paths tangent to the actual
velocity. Incompressible product transport and local spacetime regularity
justify the spatial mean derivative. Absolute continuity gives the exact
signed time-weighted identity, not a cutoff-uniform estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothMeanBalance

open scoped Topology
open MeasureTheory Set
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeCurlOutputTail
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget
open Mettapedia.Analysis SmoothAmplitudePairing UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalSmoothMeanRegularity
open LocalAnnularMeanBalance (productVelocity continuous_productVelocity
  locallyLipschitz_extendedProductVelocity divergence_extendedProductVelocity)
open LocalAnnularExplicitRate (tangentPath tangentPath_self hasDerivAt_tangentPath
  leftPoint_frozenShift rightPoint_frozenShift liftedVelocity_eq)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def explicitRate (n N : ℕ) (L nu : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * LocalSmoothSourceEvolution.materialRate n L N u nu (leftPoint x) (rightPoint x)
    (fun j ↦ LocalMeanAlignmentBalance.velocity u (leftPoint x) j)
    (fun j ↦ LocalMeanAlignmentBalance.velocity u (rightPoint x) j)

def meanRate (n N : ℕ) (L nu : ℝ) (u : FourierVelocity) : ℝ := ∫ x : T6, explicitRate n N L nu u x

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem frozenMaterialRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : t ∈ Ioo a b) (x : T6) :
    frozenMaterialRate (n + 1) N L s.coefficients t x = explicitRate n N L nu (s.coefficients t) x := by
  obtain ⟨r, hr, _⟩ := torusPoint_bounded_rep (leftPoint x)
  obtain ⟨q, hq, _⟩ := torusPoint_bounded_rep (rightPoint x)
  let X := tangentPath s t r
  let Y := tangentPath s t q
  have hX : HasDerivAt X (liftedVelocity s t (X t)) t := hasDerivAt_tangentPath s t r
  have hY : HasDerivAt Y (liftedVelocity s t (Y t)) t := hasDerivAt_tangentPath s t q
  have hleft (h : ℝ) := leftPoint_frozenShift s t x r hr h
  have hright (h : ℝ) := rightPoint_frozenShift s t x q hq h
  have hp := LocalSmoothSourceEvolution.hasDerivAt_retainedStretch_path
    s g hg hSum hu a b hab hI X Y t ht hX hY n L hL N
  have hp' := (hp.const_mul (1 / 2 : ℝ)).comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).const_add t) (by simp)
  have htorus : PancakeFourierMaterialPaths.torusPoint = (torusPoint : X3 → T3) := rfl
  have hf : HasDerivAt (fun h ↦ density (n + 1) N L (s.coefficients (t + h))
      (x + materialShift (productVelocity (s.coefficients t) x) h))
      (explicitRate n N L nu (s.coefficients t) x) 0 := by
    simpa only [htorus, Function.comp_def, id_eq, density, hleft, hright,
      X, Y, tangentPath_self, add_zero, mul_one, explicitRate, liftedVelocity_eq, hr, hq] using hp'
  exact hf.deriv

theorem ae_hasDerivAt_mean (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → Integrable (explicitRate n N L nu (s.coefficients t)) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6, density (n + 1) N L (s.coefficients τ) x)
        (meanRate n N L nu (s.coefficients t)) t := by
  have h := ae_hasDerivAt_mean_materialRate
    (fun t ↦ density (n + 1) N L (LocalSpaceTimeExtension.coefficients s a b hab t))
    (fun t ↦ productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu (n + 1) N L hL)
    (fun _ ↦ continuous_productVelocity _)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu (n + 1) N L hL)
    (locallyLipschitz_extendedProductVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall (divergence_extendedProductVelocity s a b hab hI g hSum hu t))
  filter_upwards [h] with t hd ht
  have he : frozenMaterialRate (n + 1) N L (LocalSpaceTimeExtension.coefficients s a b hab) t =
      explicitRate n N L nu (s.coefficients t) := by
    funext x
    rw [frozenMaterialRate_extension_eq s a b hab (n + 1) N L t ht x,
      frozenMaterialRate_eq s a b hab hI g hg hSum hu n N L hL t ht x]
  change Integrable (frozenMaterialRate (n + 1) N L (LocalSpaceTimeExtension.coefficients s a b hab) t) ∧
    HasDerivAt _ (∫ x : T6, frozenMaterialRate (n + 1) N L
      (LocalSpaceTimeExtension.coefficients s a b hab) t x) t at hd
  rw [he] at hd
  refine ⟨hd.1, hd.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab τ hτ]

theorem integral_explicitRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ meanRate n N L nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, meanRate n N L nu (s.coefficients t)) =
        VorticitySmoothAmplitudeSource.retainedSource (2 * (n + 1)) L N (s.coefficients b) -
          VorticitySmoothAmplitudeSource.retainedSource (2 * (n + 1)) L N (s.coefficients a) := by
  let f := fun t ↦ ∫ x : T6, density (n + 1) N L (s.coefficients t) x
  have hac : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_mean s a b hab hI g hg hSum hu (n + 1) N L hL
  have heq : deriv f =ᵐ[volume.restrict (uIoc a b)] (fun t ↦ meanRate n N L nu (s.coefficients t)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu n N L hL,
      (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t ht he hm
    have hm' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hm
    exact (ht (he.mpr hm')).2.deriv
  refine ⟨hac.intervalIntegrable_deriv.congr_ae heq, ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict heq, hac.integral_deriv_eq_sub]
  have hm (t : ℝ) (ht : t ∈ Icc a b) : f t =
      VorticitySmoothAmplitudeSource.retainedSource (2 * (n + 1)) L N (s.coefficients t) :=
    integral_density_eq (n + 1) N L hL _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI ht)))))
  rw [hm b ⟨hab, le_rfl⟩, hm a ⟨le_rfl, hab⟩]

theorem integral_source_eq_initial_add_weighted_rate (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ (b - t) * meanRate n N L nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, VorticitySmoothAmplitudeSource.retainedSource
        (2 * (n + 1)) L N (s.coefficients t)) =
        (b - a) * VorticitySmoothAmplitudeSource.retainedSource
          (2 * (n + 1)) L N (s.coefficients a) +
            ∫ t in a..b, (b - t) * meanRate n N L nu (s.coefficients t) := by
  have h := AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (absolutelyContinuousOnInterval_mean s a b hab hI g hg hSum hu (n + 1) N L hL)
    ((ae_hasDerivAt_mean s a b hab hI g hg hSum hu n N L hL).mono (fun t ht hmem ↦ (ht hmem).2))
  have hm (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x : T6, density (n + 1) N L (s.coefficients t) x) =
        VorticitySmoothAmplitudeSource.retainedSource (2 * (n + 1)) L N (s.coefficients t) :=
    integral_density_eq (n + 1) N L hL _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI ht)))))
  have hi : (∫ t in a..b, ∫ x : T6, density (n + 1) N L (s.coefficients t) x) =
      ∫ t in a..b, VorticitySmoothAmplitudeSource.retainedSource
        (2 * (n + 1)) L N (s.coefficients t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hm t (by simpa only [uIcc_of_le hab] using ht)
  exact ⟨h.1, by simpa only [hi, hm a ⟨le_rfl, hab⟩] using h.2⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothMeanBalance
