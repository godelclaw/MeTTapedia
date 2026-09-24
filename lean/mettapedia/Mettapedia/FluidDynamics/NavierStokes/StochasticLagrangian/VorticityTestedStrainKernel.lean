import Mettapedia.Analysis.PolarizedCrossKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityWeightedStretching
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteSupport

/-!
# The actual Biot--Savart strain paired with a nonradial test

Polarizing the quadratic kernel identity identifies the same physical
strain against an arbitrary continuous test field. Exchanging endpoints
then gives a factor one quarter and three signed terms. The infinite
strain limit uses the actual Fourier series, not an assumed kernel limit
or a bound intended to remain uniform along an unknown lifespan.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityTestedStrainKernel

open scoped RealInnerProductSpace Topology Matrix.Norms.Elementwise
open Filter MeasureTheory Mettapedia.Analysis PolarizedCrossKernel EuclideanCrossProduct
open PeriodicFourierTriad PancakeCurlOutputTail PancakeBlockReality PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths LocalLowDiffusionBudget LocalAlignmentForcing
open PancakeMaterialDiffusionBudget
open VorticityStretchingKernel FullStrainFourierSeries FourierFiniteSupport
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_kernel_polarizedStretch (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a f : R3) :
    (∫ y : T3, polarizedStretch (kernel modes (x - y)) a (fullVorticity u y) f) =
      2 * ⟪f, (spatialStrain modes u x).1 a⟫ := by
  have hi (v : R3) : Integrable (fun y : T3 ↦
      ⟪cross v (fullVorticity u y), kernel modes (x - y) v⟫) :=
    ((SignedCrossKernel.continuous_cross.comp
      (continuous_const.prodMk (continuous_fullVorticity u hu))).inner
      (((continuous_kernel modes).comp (continuous_const.sub continuous_id)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [polarizedStretch_eq_quadratic_difference]
  have hdiff := integral_sub ((hi (a + f)).sub (hi a)) (hi f)
  simp only [Pi.sub_apply] at hdiff
  rw [hdiff, integral_sub (hi (a + f)) (hi a),
    integral_kernel_stretch modes u hu hr hd x (a + f),
    integral_kernel_stretch modes u hu hr hd x a,
    integral_kernel_stretch modes u hu hr hd x f]
  simp only [map_add, inner_add_left, inner_add_right]
  have hsym : ⟪a, (spatialStrain modes u x).1 f⟫ = ⟪f, (spatialStrain modes u x).1 a⟫ :=
    ((spatialStrain modes u x).2 a f).trans (real_inner_comm _ _)
  rw [hsym]
  ring

def finiteWork (modes : Finset Wavevector) (u : FourierVelocity) (f : T3 → R3) : ℝ :=
  ∫ x : T3, ⟪f x, (spatialStrain modes u x).1 (fullVorticity u x)⟫

def fullWork (u : FourierVelocity) (f : T3 → R3) : ℝ :=
  ∫ x : T3, ⟪f x, fullStrainOperator u x (fullVorticity u x)⟫

def pairedWork (modes : Finset Wavevector) (u : FourierVelocity) (f : T3 → R3) : ℝ :=
  (1 / 4 : ℝ) * ∫ x : T3, ∫ y : T3,
    pairedTest (kernel modes (x - y)) (fullVorticity u x) (fullVorticity u y) (f x) (f y)

theorem finiteWork_eq_pair (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (f : T3 → R3) (hf : Continuous f) :
    finiteWork modes u f = pairedWork modes u f := by
  have h := integral_polarizedStretch_eq_half_pair (volume : Measure T3)
    (fun x y ↦ kernel modes (x - y)) (fullVorticity u) f
    ((continuous_kernel modes).comp (continuous_fst.sub continuous_snd))
    (continuous_fullVorticity u hu) hf (kernel_sub_swap modes)
  simp_rw [integral_kernel_polarizedStretch modes u hu hr hd] at h
  rw [integral_const_mul] at h
  change 2 * finiteWork modes u f = _ at h
  unfold pairedWork
  linarith only [h]

theorem fullWork_eq_pair_of_supported (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (f : T3 → R3) (hf : Continuous f) :
    fullWork u f = pairedWork P u f := by
  have h := finiteWork_eq_pair P u (summable_fourierMoment P u hs 1) hr hd f hf
  simpa only [fullWork, finiteWork, ← fullStrainOperator_eq_spatialStrain P u hs] using h

theorem tendsto_finiteWork (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (f : T3 → R3) (hf : Continuous f) :
    Tendsto (fun modes : Finset Wavevector ↦ finiteWork modes u f) atTop (𝓝 (fullWork u f)) := by
  have hw := continuous_fullVorticity u hu
  let C : ℝ := 9 * ∑' k, ‖PancakeFourierPressureStrain.strainCoeff u k‖
  let bound : T3 → ℝ := fun x ↦ ‖f x‖ * (C * ‖fullVorticity u x‖)
  have hb : Integrable bound :=
    (hf.norm.mul (continuous_const.mul hw.norm)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall (fun modes ↦ (hf.inner
      ((continuous_subtype_val.comp (continuous_strain modes u)).clm_apply hw)).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro modes
    filter_upwards with x
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (((spatialStrain modes u x).1.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_spatialStrain_le modes u hu x) (norm_nonneg _)))
      (norm_nonneg _))
  · exact hb
  · filter_upwards with x
    exact tendsto_const_nhds.inner
      ((ContinuousLinearMap.apply ℝ R3 (fullVorticity u x)).continuous.tendsto _ |>.comp
        (tendsto_spatialStrain u hu x))

theorem tendsto_pairedWork (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (f : T3 → R3) (hf : Continuous f) :
    Tendsto (fun modes : Finset Wavevector ↦ pairedWork modes u f) atTop (𝓝 (fullWork u f)) := by
  simpa only [← finiteWork_eq_pair _ u hu hr hd f hf] using tendsto_finiteWork u hu f hf

end Mettapedia.FluidDynamics.NavierStokes.VorticityTestedStrainKernel
