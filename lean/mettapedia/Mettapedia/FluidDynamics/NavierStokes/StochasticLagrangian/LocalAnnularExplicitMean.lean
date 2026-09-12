import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularExplicitRate

/-!
# Signed spatial and time balances with the explicit Navier–Stokes source

Spatial integrability of the expanded material rate follows from its almost-
everywhere identification with the actual derivative. Incompressibility then
gives the mean evolution and its time-weighted identity. All statements are
local on a compact interior time interval; they provide no cutoff-uniform
nonlinear budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitMean

open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity
open LocalAnnularMeanBalance LocalAnnularExplicitRate

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

theorem ae_hasDerivAt_mean (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b →
      Integrable (explicitRate n N L nu (s.coefficients t)) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6, density (n + 1) N L (s.coefficients τ) x)
        (∫ x : T6, explicitRate n N L nu (s.coefficients t) x) t := by
  filter_upwards [LocalAnnularMeanBalance.ae_hasDerivAt_mean
      s a b hab hI g hg hSum hu (n + 1) N L hL,
    ae_ae_frozenMaterialRate_eq s a b hab hI g hg hSum hu n N L hL] with t hd he ht
  have hm := integral_congr_ae (he ht)
  exact ⟨(hd ht).1.congr (he ht), hm ▸ (hd ht).2⟩

theorem ae_meanRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ uIcc a b →
      (∫ x : T6, frozenMaterialRate (n + 1) N L s.coefficients t x) =
        ∫ x : T6, explicitRate n N L nu (s.coefficients t) x := by
  filter_upwards [ae_ae_frozenMaterialRate_eq s a b hab hI g hg hSum hu n N L hL,
    (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t hd he ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  exact integral_congr_ae (hd (he.mpr ht'))

theorem integral_explicitRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ ∫ x : T6, explicitRate n N L nu (s.coefficients t) x) volume a b ∧
      (∫ t in a..b, ∫ x : T6, explicitRate n N L nu (s.coefficients t) x) =
        VorticityAnnularPolynomialSource.highAmplitudeSource (2 * (n + 1)) L N (s.coefficients b) -
          VorticityAnnularPolynomialSource.highAmplitudeSource (2 * (n + 1)) L N (s.coefficients a) := by
  have h := integral_frozenMaterialRate_eq s a b hab hI g hg hSum hu (n + 1) N L hL
  have he := ae_meanRate_eq s a b hab hI g hg hSum hu n N L hL
  refine ⟨h.1.congr_ae ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [he] with t ht hmem
    exact ht (uIoc_subset_uIcc hmem)
  · refine (intervalIntegral.integral_congr_ae ?_).symm.trans h.2
    filter_upwards [he] with t ht hmem
    exact ht (uIoc_subset_uIcc hmem)

/-- Exact signed time-integrated source with all material channels explicit. -/
theorem integral_source_eq_initial_add_weighted_rate (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ (b - t) *
      ∫ x : T6, explicitRate n N L nu (s.coefficients t) x) volume a b ∧
      (∫ t in a..b, VorticityAnnularPolynomialSource.highAmplitudeSource
        (2 * (n + 1)) L N (s.coefficients t)) =
        (b - a) * VorticityAnnularPolynomialSource.highAmplitudeSource
          (2 * (n + 1)) L N (s.coefficients a) +
            ∫ t in a..b, (b - t) * ∫ x : T6, explicitRate n N L nu (s.coefficients t) x := by
  have h := LocalAnnularMeanBalance.integral_source_eq_initial_add_weighted_rate
    s a b hab hI g hg hSum hu (n + 1) N L hL
  have he := ae_meanRate_eq s a b hab hI g hg hSum hu n N L hL
  have hw : ∀ᵐ t : ℝ, t ∈ uIcc a b →
      (b - t) * (∫ x : T6, frozenMaterialRate (n + 1) N L s.coefficients t x) =
        (b - t) * ∫ x : T6, explicitRate n N L nu (s.coefficients t) x :=
    he.mono (fun t ht hmem ↦ congrArg ((b - t) * ·) (ht hmem))
  refine ⟨h.1.congr_ae ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [hw] with t ht hmem
    exact ht (uIoc_subset_uIcc hmem)
  · rw [h.2]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hw] with t ht hmem
    exact ht (uIoc_subset_uIcc hmem)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitMean
