import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSmoothMeanBalance

/-!
# Joint signed mean rate with the complete viscous curvature

Strain and relative kernel transport stay grouped. Their spatial
integrability follows from the actual material rate minus the continuous
viscosity channel. The exact time-weighted identity therefore does not
require separate absolute envelopes or a sign for any channel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothMeanChannels

open MeasureTheory Set
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeCurlOutputTail
open LocalLowDiffusionBudget LocalAlignmentForcing VorticityAnnularKernelTransport
open Mettapedia.Analysis SmoothAmplitudePairing UnitTorusProductTransport
open LocalSmoothMeanBalance

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def nonviscousRate (n N : ℕ) (L : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) *
    (retainedStrainRate (n + 1) L (fullStrainOperator u (leftPoint x))
      (fullStrainOperator u (rightPoint x))
      (PeriodicRieszPolynomial.kernel N (leftPoint x - rightPoint x))
      (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x)) +
    retainedStretch (2 * (n + 2)) L
      (kernelDirectionalRate N (leftPoint x - rightPoint x)
        ((fun j ↦ LocalMeanAlignmentBalance.velocity u (leftPoint x) j) -
          (fun j ↦ LocalMeanAlignmentBalance.velocity u (rightPoint x) j)))
      (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x)))

def diffusionRate (n N : ℕ) (L : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * LocalSmoothAnnularDiffusion.diffusionDensity n L N u (leftPoint x) (rightPoint x)

def jointRate (n N : ℕ) (L nu : ℝ) (u : FourierVelocity) : ℝ :=
  (∫ x : T6, nonviscousRate n N L u x) - nu * LocalSmoothAnnularDiffusion.curvatureSource n L N u

theorem explicitRate_eq (n N : ℕ) (L nu : ℝ) (u : FourierVelocity) (x : T6) :
    explicitRate (n + 1) N L nu u x = nonviscousRate n N L u x + nu * diffusionRate n N L u x := by
  rw [explicitRate, LocalSmoothSourceEvolution.materialRate_eq_channels]
  simp only [nonviscousRate, diffusionRate, LocalSmoothAnnularDiffusion.diffusionDensity,
    show n + 1 + 1 = n + 2 by omega]
  ring

theorem continuous_diffusionRate (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Continuous (diffusionRate n N L u) :=
  ((LocalSmoothAnnularDiffusion.continuous_diffusionDensity n L hL N u hu).comp
    (continuous_leftPoint.prodMk continuous_rightPoint)).const_mul (1 / 2 : ℝ)

theorem integral_diffusionRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T6, diffusionRate n N L u x) = LocalSmoothAnnularDiffusion.diffusionSource n L N u := by
  simp only [diffusionRate]
  rw [integral_const_mul, UnitTorusProductTransport.integral_pair _
    ((LocalSmoothAnnularDiffusion.continuous_diffusionDensity n L hL N u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  rfl

theorem integrable_nonviscousRate (n N : ℕ) (L : ℝ) (hL : 0 < L) (nu : ℝ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hm : Integrable (explicitRate (n + 1) N L nu u)) :
    Integrable (nonviscousRate n N L u) := by
  have hd := (continuous_diffusionRate n N L hL u hu).integrable_of_hasCompactSupport
    (μ := (volume : Measure T6)) (HasCompactSupport.of_compactSpace _)
  apply (hm.sub (hd.const_mul nu)).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.sub_apply, explicitRate_eq]
  ring

theorem meanRate_eq_jointRate (n N : ℕ) (L : ℝ) (hL : 0 < L) (nu : ℝ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hm : Integrable (explicitRate (n + 1) N L nu u)) :
    meanRate (n + 1) N L nu u = jointRate n N L nu u := by
  have hd := (continuous_diffusionRate n N L hL u hu).integrable_of_hasCompactSupport
    (μ := (volume : Measure T6)) (HasCompactSupport.of_compactSpace _)
  have hn := integrable_nonviscousRate n N L hL nu u hu hm
  simp only [meanRate, explicitRate_eq]
  rw [integral_add hn (hd.const_mul nu), integral_const_mul, integral_diffusionRate_eq n N L hL u hu,
    LocalSmoothAnnularDiffusion.diffusionSource_eq_neg_curvatureSource n L hL N u hu]
  simp only [jointRate]
  ring

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem ae_meanRate_eq_jointRate (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → Integrable (nonviscousRate n N L (s.coefficients t)) ∧
      meanRate (n + 1) N L nu (s.coefficients t) = jointRate n N L nu (s.coefficients t) := by
  filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu (n + 1) N L hL] with t hd ht
  have hmoment := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Ioo_subset_Icc_self (hI (Ioo_subset_Icc_self ht))))
  exact ⟨integrable_nonviscousRate n N L hL nu _ hmoment (hd ht).1,
    meanRate_eq_jointRate n N L hL nu _ hmoment (hd ht).1⟩

theorem ae_hasDerivAt_source (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun τ ↦ VorticitySmoothAmplitudeSource.retainedSource
        (2 * (n + 2)) L N (s.coefficients τ)) (jointRate n N L nu (s.coefficients t)) t := by
  filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu (n + 1) N L hL,
    ae_meanRate_eq_jointRate s a b hab hI g hg hSum hu n N L hL] with t hd he ht
  have h := (hd ht).2
  rw [(he ht).2] at h
  simp only [show n + 1 + 1 = n + 2 by omega] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  exact (LocalSmoothMeanRegularity.integral_density_eq (n + 2) N L hL _
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (Ioo_subset_Icc_self (hI hτ)))))).symm

/-- The signed rate is integrated as a whole; no componentwise payment is assumed. -/
theorem integral_source_eq_initial_add_weighted_channels (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ (b - t) * jointRate n N L nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, VorticitySmoothAmplitudeSource.retainedSource
        (2 * (n + 2)) L N (s.coefficients t)) =
        (b - a) * VorticitySmoothAmplitudeSource.retainedSource
          (2 * (n + 2)) L N (s.coefficients a) +
            ∫ t in a..b, (b - t) * jointRate n N L nu (s.coefficients t) := by
  have h := integral_source_eq_initial_add_weighted_rate s a b hab hI g hg hSum hu (n + 1) N L hL
  have he : (fun t ↦ (b - t) * meanRate (n + 1) N L nu (s.coefficients t)) =ᵐ[
      volume.restrict (uIoc a b)] (fun t ↦ (b - t) * jointRate n N L nu (s.coefficients t)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [ae_meanRate_eq_jointRate s a b hab hI g hg hSum hu n N L hL,
      (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t hd he ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
    exact congrArg ((b - t) * ·) (hd (he.mpr ht')).2
  refine ⟨h.1.congr_ae he, ?_⟩
  simpa only [show n + 1 + 1 = n + 2 by omega,
    intervalIntegral.integral_congr_ae_restrict he] using h.2

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothMeanChannels
