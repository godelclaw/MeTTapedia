import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityStretchingKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullStrainFourierSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy

/-!
# Signed two-point representation of the actual weighted stretching source

The finite strain reconstruction pairs with the full vorticity at both
points. Exchanging source and receiver leaves a cross product and a signed
radial-power difference. The limit over all finite frequency sets recovers
the actual full strain, and at weight six it recovers the source in the
eighth-moment energy identity. No direction modulus or uniform absolute
kernel bound is assumed or concluded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching

open scoped RealInnerProductSpace Topology Matrix.Norms.Elementwise
open Filter MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakePeriodicComplexStretch PancakeFourierMaterialPaths
open PancakeMaterialDiffusionBudget
open LocalLowDiffusionBudget LocalAlignmentForcing FullStrainFourierSeries VorticityStretchingKernel
open Mettapedia.Analysis.SignedCrossKernel

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fullStretching (n : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ n *
    ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

def finiteStretching (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ n *
    ⟪fullVorticity u x, (spatialStrain modes u x).1 (fullVorticity u x)⟫

def pairedIntegral (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    pairedStretch n (kernel modes (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem fullStretching_six (u : FourierVelocity) :
    fullStretching 6 u = LocalVorticityEighthMoment.stretching u := rfl

theorem finiteStretching_eq_pair (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    finiteStretching n modes u = pairedIntegral n modes u := by
  have h := integral_weightedStretch_eq_half_pair (volume : Measure T3)
    (fun x y ↦ kernel modes (x - y)) (fullVorticity u)
    ((continuous_kernel modes).comp (continuous_fst.sub continuous_snd))
    (continuous_fullVorticity u hu) n (kernel_sub_swap modes)
  change _ = pairedIntegral n modes u at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [weightedStretch, integral_const_mul, integral_kernel_stretch modes u hu hr hd]

theorem tendsto_finiteStretching (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Tendsto (fun modes : Finset Wavevector ↦ finiteStretching n modes u)
      atTop (𝓝 (fullStretching n u)) := by
  have hw := continuous_fullVorticity u hu
  let C : ℝ := 9 * ∑' k, ‖PancakeFourierPressureStrain.strainCoeff u k‖
  let bound : T3 → ℝ := fun x ↦
    ‖fullVorticity u x‖ ^ n * (‖fullVorticity u x‖ * (C * ‖fullVorticity u x‖))
  have hb : Integrable bound :=
    ((hw.norm.pow n).mul (hw.norm.mul (continuous_const.mul hw.norm))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply tendsto_integral_filter_of_dominated_convergence bound
  · apply Eventually.of_forall
    intro modes
    exact ((hw.norm.pow n).mul (hw.inner
      ((continuous_subtype_val.comp (continuous_strain modes u)).clm_apply hw))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro modes
    filter_upwards [] with x
    simp only [norm_mul, norm_pow, norm_norm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact ((spatialStrain modes u x).1.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_spatialStrain_le modes u hu x) (norm_nonneg _))
  · exact hb
  · filter_upwards [] with x
    have he : Tendsto (fun modes : Finset Wavevector ↦
        (spatialStrain modes u x).1 (fullVorticity u x))
        atTop (𝓝 (fullStrainOperator u x (fullVorticity u x))) :=
      (ContinuousLinearMap.apply ℝ R3 (fullVorticity u x)).continuous.tendsto _ |>.comp
        (tendsto_spatialStrain u hu x)
    exact tendsto_const_nhds.mul (tendsto_const_nhds.inner he)

/-- No interchange of an infinite singular kernel and the double integral is required. -/
theorem tendsto_pairedIntegral (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun modes : Finset Wavevector ↦ pairedIntegral n modes u)
      atTop (𝓝 (fullStretching n u)) := by
  simpa only [← finiteStretching_eq_pair n _ u hu hr hd] using tendsto_finiteStretching n u hu

/-- The signed paired expression converges to the actual eighth-moment stretching source. -/
theorem tendsto_eighthMoment_pair (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun modes : Finset Wavevector ↦ pairedIntegral 6 modes u)
      atTop (𝓝 (LocalVorticityEighthMoment.stretching u)) :=
  tendsto_pairedIntegral 6 u hu hr hd

/-- Fixed-line alignment kills the actual source; arbitrary data need not have this property. -/
theorem fullStretching_eq_zero_of_collinear (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0)
    (a : R3) (r : T3 → ℝ) (hw : ∀ x, fullVorticity u x = r x • a) :
    fullStretching n u = 0 := by
  have hzero (modes : Finset Wavevector) : pairedIntegral n modes u = 0 := by
    simp only [pairedIntegral, hw, pairedStretch_collinear, integral_zero, mul_zero]
  have h := tendsto_pairedIntegral n u hu hr hd
  simp only [hzero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching
