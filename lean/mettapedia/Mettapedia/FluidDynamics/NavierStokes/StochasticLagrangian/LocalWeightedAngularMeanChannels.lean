import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedAngularMeanBalance

/-!
# Joint angular evolution with the complete signed viscosity contribution

The nonviscous term includes amplitude growth, unequal endpoint strain and
relative kernel transport. Subtracting the complete spatial curvature gives
the actual mean rate. The time identity retains this joint signed quantity;
no sign or global bound is assumed for its individual channels.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularMeanChannels

open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalJointDiffusionBudget
open Mettapedia.Analysis WeightedCrossProduct EuclideanCrossProduct UnitTorusProductTransport
open LocalWeightedAngularMeanRegularity LocalWeightedAngularMeanBalance
open LocalWeightedAngularEvolution (pairEnergy materialPairRate symmetricAngularIntegral)
open LocalWeightedAngularDiffusion (curvatureIntegral)
open scoped RealInnerProductSpace

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def diffusionRate (N : ℕ) (u : FourierVelocity) (x : T6) : ℝ :=
  kernelDensity N x * rate 2 (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x))
    (fullVorticityLaplacian u (leftPoint x)) (fullVorticityLaplacian u (rightPoint x))

def jointRate (N : ℕ) (nu : ℝ) (u : FourierVelocity) : ℝ :=
  (∫ x : T6, explicitRate N 0 u x) - nu * curvatureIntegral N u

theorem explicitRate_eq (N : ℕ) (nu : ℝ) (u : FourierVelocity) (x : T6) :
    explicitRate N nu u x = explicitRate N 0 u x + nu * diffusionRate N u x := by
  simp only [explicitRate, materialPairRate, diffusionRate, perturbationRate,
    amplitudeRate, symmetricPairForcing_eq, rate, cross_smul_left, cross_smul_right,
    zero_smul, zero_cross, cross_zero, inner_zero_right, inner_add_right,
    real_inner_smul_right]
  ring

theorem continuous_diffusionPair (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Continuous (fun p : T3 × T3 ↦ kernelWeight N (p.1 - p.2) *
      rate 2 (fullVorticity u p.1) (fullVorticity u p.2)
        (fullVorticityLaplacian u p.1) (fullVorticityLaplacian u p.2)) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  exact ((continuous_kernelWeight N).comp (continuous_fst.sub continuous_snd)).mul
    (continuous_rate 2 (hw.comp continuous_fst) (hw.comp continuous_snd)
      (hl.comp continuous_fst) (hl.comp continuous_snd))

theorem continuous_diffusionRate (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (diffusionRate N u) :=
  (continuous_diffusionPair N u hu).comp
    (f := fun x : T6 ↦ (leftPoint x, rightPoint x)) (continuous_leftPoint.prodMk continuous_rightPoint)

theorem integral_diffusionRate_eq (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T6, diffusionRate N u x) = -curvatureIntegral N u := by
  have hc := continuous_diffusionPair N u hu
  unfold diffusionRate kernelDensity
  rw [UnitTorusProductTransport.integral_pair (fun x y : T3 ↦ kernelWeight N (x - y) *
    rate 2 (fullVorticity u x) (fullVorticity u y)
      (fullVorticityLaplacian u x) (fullVorticityLaplacian u y))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    UnitTorusPairIntegration.integral_pair_eq_separation _ hc]
  have he : (∫ h : T3, ∫ x : T3, kernelWeight N (x - (x - h)) *
      rate 2 (fullVorticity u x) (fullVorticity u (x - h))
        (fullVorticityLaplacian u x) (fullVorticityLaplacian u (x - h))) =
      LocalWeightedAngularDiffusion.diffusionIntegral N u := by
    apply integral_congr_ae
    filter_upwards [PeriodicRieszPolynomial.kernel_ae_eq (d := 3) N] with h hh
    simp only [kernelWeight, sub_sub_cancel, hh, LocalWeightedAngularDiffusion.diffusionDensity]
  rw [he, LocalWeightedAngularDiffusion.diffusionIntegral_eq_neg_curvatureIntegral N u hu]

theorem meanRate_eq_jointRate (N : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hm : Integrable (explicitRate N nu u)) :
    meanRate N nu u = jointRate N nu u := by
  have hd := (continuous_diffusionRate N u hu).integrable_of_hasCompactSupport
    (μ := (volume : Measure T6)) (HasCompactSupport.of_compactSpace _)
  have hn : Integrable (explicitRate N 0 u) := by
    apply (hm.sub (hd.const_mul nu)).congr
    apply Filter.Eventually.of_forall
    intro x
    simp only [Pi.sub_apply, explicitRate_eq N nu]
    ring
  have he : (fun x ↦ explicitRate N nu u x) =
      (fun x ↦ explicitRate N 0 u x + nu * diffusionRate N u x) :=
    funext (explicitRate_eq N nu u)
  rw [meanRate, he, integral_add hn (hd.const_mul nu), integral_const_mul,
    integral_diffusionRate_eq N u hu]
  simp only [jointRate, mul_neg, sub_eq_add_neg]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem ae_meanRate_eq_jointRate (N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → meanRate N nu (s.coefficients t) = jointRate N nu (s.coefficients t) := by
  filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu N] with t ht hmem
  exact meanRate_eq_jointRate N nu _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI (Ioo_subset_Icc_self hmem)))))
    (ht hmem).1

theorem integral_angular_eq_initial_add_weighted_channels (N : ℕ) :
    IntervalIntegrable (fun t ↦ (b - t) * jointRate N nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, symmetricAngularIntegral N (s.coefficients t)) =
        (b - a) * symmetricAngularIntegral N (s.coefficients a) +
          ∫ t in a..b, (b - t) * jointRate N nu (s.coefficients t) := by
  have h := integral_angular_eq_initial_add_weighted_rate s a b hab hI g hg hSum hu N
  have he : (fun t ↦ (b - t) * meanRate N nu (s.coefficients t)) =ᵐ[
      volume.restrict (uIoc a b)] (fun t ↦ (b - t) * jointRate N nu (s.coefficients t)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [ae_meanRate_eq_jointRate s a b hab hI g hg hSum hu N,
      (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t hd he ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
    exact congrArg ((b - t) * ·) (hd (he.mpr ht'))
  exact ⟨h.1.congr_ae he, by simpa only [intervalIntegral.integral_congr_ae_restrict he] using h.2⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularMeanChannels
