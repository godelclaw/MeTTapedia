import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialSourceIntegral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedKernelDiffusion
import Mettapedia.Analysis.RadialPancakeCurvature

/-!
# Joint radial deformation, transport, and viscous curvature balance

The radial kernel is the actual periodized operator. Common-translation
integration by parts replaces its endpoint viscosity by signed curvature
without differentiating the kernel. Deformation and relative transport
remain grouped. The complete signed time integral has a local cutoff limit;
no separate absolute envelope or curvature sign is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels

open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget LocalAlignmentForcing
open Mettapedia.Analysis SignedCrossKernel UnitTorusProductTransport
open LocalRadialMeanRegularity LocalRadialPeriodicEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Viscosity set to zero in the instantaneous rate, not a different solution. -/
def nonviscousRate (n N : ℕ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * fieldRate (n + 1) N u 0 (leftPoint x) (rightPoint x)

def diffusionRate (n N : ℕ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * LocalPairedKernelDiffusion.diffusionDensity n (PeriodicRadialRiesz.tensor N) u
    (leftPoint x) (rightPoint x)

def curvatureSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  LocalPairedKernelDiffusion.curvatureSource n (PeriodicRadialRiesz.tensor N) u

def jointRate (n N : ℕ) (nu : ℝ) (u : FourierVelocity) : ℝ :=
  (∫ x : T6, nonviscousRate n N u x) - nu * curvatureSource n N u

/-- The image series stays inside each spatial curvature density. -/
theorem curvatureDensity_eq_images (n N : ℕ) (u : FourierVelocity) (x y : T3) (hxy : x ≠ y) :
    LocalPairedKernelDiffusion.curvatureDensity n (PeriodicRadialRiesz.tensor N) u x y =
      ∑ j : Fin 3, ∑' z : UnitTorusLattice.LatticeSubmodule (ι := Fin 3),
        RadialRieszRegularization.radialCoefficient N (EuclideanSpace.single 0 1)
            (UnitTorusSchwartzLattice.displacement (x - y) z) *
          RadialPancakeCurvature.radialCurvature n (fullVorticity u x) (fullVorticity u y)
            (UnitTorusSchwartzLattice.displacement (x - y) z)
            (LocalSpatialVorticityJets.fullCurlGradient u j x)
            (LocalSpatialVorticityJets.fullCurlGradient u j y) := by
  apply Finset.sum_congr rfl
  intro j _
  exact (RadialPancakeCurvature.hasSum_radialCurvature_images N n (EuclideanSpace.single 0 1)
    (by simp) (sub_ne_zero.mpr hxy) _ _ _ _).tsum_eq.symm

theorem explicitRate_eq (n N : ℕ) (nu : ℝ) (u : FourierVelocity) (x : T6) :
    explicitRate (n + 1) N nu u x = nonviscousRate n N u x + nu * diffusionRate n N u x := by
  simp only [explicitRate, nonviscousRate, fieldRate, pairedMaterialRate_add_smul_endpoint,
    zero_smul, add_zero, diffusionRate, LocalPairedKernelDiffusion.diffusionDensity]
  ring

theorem continuous_diffusionRate (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (diffusionRate n N u) :=
  ((LocalPairedKernelDiffusion.continuous_diffusionDensity n (PeriodicRadialRiesz.tensor N)
    (PeriodicRadialRiesz.continuous_tensor N) u hu).comp
    (continuous_leftPoint.prodMk continuous_rightPoint)).const_mul (1 / 2 : ℝ)

theorem integral_diffusionRate_eq_neg_curvatureSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T6, diffusionRate n N u x) = -curvatureSource n N u := by
  simp only [diffusionRate]
  rw [integral_const_mul, UnitTorusProductTransport.integral_pair _
    ((LocalPairedKernelDiffusion.continuous_diffusionDensity n (PeriodicRadialRiesz.tensor N)
      (PeriodicRadialRiesz.continuous_tensor N) u hu).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  exact LocalPairedKernelDiffusion.diffusionSource_eq_neg_curvatureSource n
    (PeriodicRadialRiesz.tensor N) (PeriodicRadialRiesz.continuous_tensor N) u hu

theorem integrable_nonviscousRate (n N : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hm : Integrable (explicitRate (n + 1) N nu u)) :
    Integrable (nonviscousRate n N u) := by
  have hd := (continuous_diffusionRate n N u hu).integrable_of_hasCompactSupport
    (μ := (volume : Measure T6)) (HasCompactSupport.of_compactSpace _)
  apply (hm.sub (hd.const_mul nu)).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.sub_apply, explicitRate_eq]
  ring

theorem meanRate_eq_jointRate (n N : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hm : Integrable (explicitRate (n + 1) N nu u)) :
    meanRate (n + 1) N nu u = jointRate n N nu u := by
  have hd := (continuous_diffusionRate n N u hu).integrable_of_hasCompactSupport
    (μ := (volume : Measure T6)) (HasCompactSupport.of_compactSpace _)
  have hn := integrable_nonviscousRate n N nu u hu hm
  simp only [meanRate, explicitRate_eq]
  rw [integral_add hn (hd.const_mul nu), integral_const_mul,
    integral_diffusionRate_eq_neg_curvatureSource n N u hu]
  simp only [jointRate]
  ring

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem ae_meanRate_eq_jointRate (n N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → Integrable (nonviscousRate n N (s.coefficients t)) ∧
      meanRate (n + 1) N nu (s.coefficients t) = jointRate n N nu (s.coefficients t) := by
  filter_upwards [LocalRadialMeanBalance.ae_hasDerivAt_mean s a b hab hI g hg hSum hu (n + 1) N]
    with t hd ht
  have hmoment := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Ioo_subset_Icc_self (hI (Ioo_subset_Icc_self ht))))
  exact ⟨integrable_nonviscousRate n N nu _ hmoment (hd ht).1,
    meanRate_eq_jointRate n N nu _ hmoment (hd ht).1⟩

theorem ae_hasDerivAt_source (n N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun τ ↦ VorticityRadialSource.source (2 * (n + 2)) N (s.coefficients τ))
        (jointRate n N nu (s.coefficients t)) t := by
  filter_upwards [LocalRadialMeanBalance.ae_hasDerivAt_source s a b hab hI g hg hSum hu (n + 1) N,
    ae_meanRate_eq_jointRate s a b hab hI g hg hSum hu n N] with t hd he ht
  simpa only [show n + 1 + 1 = n + 2 by omega, (he ht).2] using hd ht

theorem integral_source_eq_initial_add_weighted_channels (n N : ℕ) :
    IntervalIntegrable (fun t ↦ (b - t) * jointRate n N nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, VorticityRadialSource.source (2 * (n + 2)) N (s.coefficients t)) =
        (b - a) * VorticityRadialSource.source (2 * (n + 2)) N (s.coefficients a) +
          ∫ t in a..b, (b - t) * jointRate n N nu (s.coefficients t) :=
  AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (by simpa only [show n + 1 + 1 = n + 2 by omega] using
      LocalRadialMeanBalance.absolutelyContinuousOnInterval_source s a b hab hI g hg hSum hu (n + 1) N)
    (ae_hasDerivAt_source s a b hab hI g hg hSum hu n N)

/-- Only the complete signed integral is passed to the limit. -/
theorem tendsto_integral_weighted_jointRate :
    Filter.Tendsto (fun N : ℕ ↦ ∫ τ in a..b, (b - τ) * jointRate 1 N nu (s.coefficients τ))
      Filter.atTop (nhds ((∫ τ in a..b, LocalVorticityEighthMoment.stretching (s.coefficients τ)) -
        (b - a) * LocalVorticityEighthMoment.stretching (s.coefficients a))) := by
  have he (N : ℕ) : (∫ τ in a..b, (b - τ) * jointRate 1 N nu (s.coefficients τ)) =
      (∫ τ in a..b, VorticityRadialSource.source 6 N (s.coefficients τ)) -
        (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) := by
    have h := (integral_source_eq_initial_add_weighted_channels s a b hab hI g hg hSum hu 1 N).2
    change _ = (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) + _ at h
    linarith only [h]
  have hm (N : ℕ) : (∫ τ in a..b, (b - τ) * meanRate 2 N nu (s.coefficients τ)) =
      (∫ τ in a..b, VorticityRadialSource.source 6 N (s.coefficients τ)) -
        (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) := by
    have h := (LocalRadialMeanBalance.integral_source_eq_initial_add_weighted_rate
      s a b hab hI g hg hSum hu 2 N).2
    change _ = (b - a) * VorticityRadialSource.source 6 N (s.coefficients a) + _ at h
    linarith only [h]
  have h := LocalRadialSourceIntegral.tendsto_integral_weighted_meanRate s a b hab hI g hg hSum hu
  simpa only [he, hm] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels
