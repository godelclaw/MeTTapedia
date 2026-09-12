import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedQuadratic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Limit of the regularized actual stretching source

The constructed integrable kernels act on the full vorticity. Their
contractive annular weights tend to one on every nonzero lattice mode,
so their quadratic action and weighted source recover the actual strain.
The domination below justifies a fixed-snapshot limit; it is not a
time-integrated bound on the nonlinear source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource

open MeasureTheory Filter PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakeGalerkinKineticEnergy LocalLowDiffusionBudget
open VorticityStretchingKernel VorticityRegularizedQuadratic VorticityWeightedStretching
open PancakePeriodicComplexStretch PancakePeriodicVorticityEquation ComplexPressurePair
open PancakeFourierMaterialPaths PancakeFourierPressureStrain
open PancakeFourierStrainGradient
open PancakeMaterialDiffusionBudget LocalAlignmentForcing FullStrainFourierSeries
open Mettapedia.Analysis
open scoped RealInnerProductSpace Topology Matrix.Norms.Elementwise
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def strainTerm (u : FourierVelocity) (k : Wavevector) (x : T3) (a : R3) : ℝ :=
  ⟪a, realMatrixOperator (UnitAddTorus.mFourier k x • strainCoeff u k) a⟫

theorem strainTerm_eq_re (u : FourierVelocity) (k : Wavevector) (x : T3) (a : R3) :
    strainTerm u k x a = (UnitAddTorus.mFourier k x *
      coefficientDot (realCoefficient a) ((strainCoeff u k).mulVec (realCoefficient a))).re := by
  rw [strainTerm, ← real_quadratic_form]
  simp only [Matrix.smul_mulVec, coefficientDot_smul_right]

theorem hasSum_strainTerm (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (x : T3) (a : R3) :
    HasSum (fun k ↦ strainTerm u k x a) ⟪a, fullStrainOperator u x a⟫ := by
  have h := (innerSL ℝ a).hasSum ((ContinuousLinearMap.apply ℝ R3 a).hasSum
    (realMatrixOperatorCLM.hasSum (hasSum_strain_matrix u hu x)))
  exact h

theorem norm_strainTerm_le (u : FourierVelocity) (k : Wavevector) (x : T3) (a : R3) :
    ‖strainTerm u k x a‖ ≤ 9 * ‖strainCoeff u k‖ * ‖a‖ ^ 2 := by
  have hc : ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
    simpa only [UnitAddTorus.mFourier_norm] using (UnitAddTorus.mFourier k).norm_coe_le_norm x
  have hm : ‖realMatrixOperator (UnitAddTorus.mFourier k x • strainCoeff u k)‖ ≤
      9 * ‖strainCoeff u k‖ := by
    apply (norm_realMatrixOperator_le _).trans
    rw [norm_smul]
    nlinarith [norm_nonneg (strainCoeff u k)]
  apply (norm_inner_le_norm _ _).trans
  have h := (realMatrixOperator (UnitAddTorus.mFourier k x • strainCoeff u k)).le_opNorm a
  have hh := mul_le_mul_of_nonneg_right hm (norm_nonneg a)
  have hb := mul_le_mul_of_nonneg_left (h.trans hh) (norm_nonneg a)
  convert hb using 1
  ring

theorem hasSum_weighted_strainTerm (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    HasSum (fun k ↦ AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) * strainTerm u k x a)
      (quadraticStretch N u x a) := by
  have h := RCLike.hasSum_re ℂ (hasSum_quadraticStretch N u hu hr hd x a)
  simpa only [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, RCLike.re_to_complex, strainTerm_eq_re, mul_assoc] using h

theorem norm_weighted_strainTerm_le (N : ℕ) (u : FourierVelocity) (k : Wavevector) (x : T3) (a : R3) :
    ‖AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) * strainTerm u k x a‖ ≤
      9 * ‖strainCoeff u k‖ * ‖a‖ ^ 2 := by
  rw [norm_mul, Real.norm_of_nonneg (AnnularRieszKernel.weight_nonneg _ _)]
  exact (mul_le_mul_of_nonneg_right (AnnularRieszKernel.weight_le_one _ _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_strainTerm_le u k x a)

theorem tendsto_quadraticStretch (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    Tendsto (fun N : ℕ ↦ quadraticStretch N u x a) atTop (𝓝 ⟪a, fullStrainOperator u x a⟫) := by
  have hb := ((summable_norm_strainCoeff u hu).mul_left 9).mul_right (‖a‖ ^ 2)
  have ht (k : Wavevector) : Tendsto
      (fun N : ℕ ↦ AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) * strainTerm u k x a)
      atTop (𝓝 (strainTerm u k x a)) := by
    by_cases hk : k = 0
    · subst k
      have hz : strainTerm u 0 x a = 0 := by
        have hc : strainCoeff u 0 = 0 := by
          ext i j
          simp [strainCoeff, PancakeFourierPressureStrain.gradientCoeff]
        simp only [strainTerm, hc, smul_zero]
        change ⟪a, realMatrixOperatorCLM 0 a⟫ = 0
        rw [map_zero]
        simp only [zero_apply, inner_zero_right]
      simp only [hz, mul_zero]
      exact tendsto_const_nhds
    · simpa only [one_mul] using (AnnularRieszKernel.tendsto_weight _
        (PeriodicRieszKernel.one_le_norm_frequency k hk)).mul_const (strainTerm u k x a)
  have h := tendsto_tsum_of_dominated_convergence hb ht
    (Eventually.of_forall (fun N k ↦ norm_weighted_strainTerm_le N u k x a))
  simp only [(hasSum_weighted_strainTerm _ u hu hr hd x a).tsum_eq,
    (hasSum_strainTerm u hu x a).tsum_eq] at h
  exact h

def source (n N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ n * quadraticStretch N u x (fullVorticity u x)

theorem continuous_strainTerm (u : FourierVelocity) (k : Wavevector) :
    Continuous (fun p : T3 × R3 ↦ strainTerm u k p.1 p.2) := by
  have hM : Continuous (fun p : T3 × R3 ↦
      realMatrixOperatorCLM (UnitAddTorus.mFourier k p.1 • strainCoeff u k)) :=
    realMatrixOperatorCLM.continuous.comp
    (((UnitAddTorus.mFourier k).continuous.comp continuous_fst).smul continuous_const)
  exact continuous_snd.inner (hM.clm_apply continuous_snd)

theorem norm_quadraticStretch_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    ‖quadraticStretch N u x a‖ ≤ (9 * ∑' k, ‖strainCoeff u k‖) * ‖a‖ ^ 2 := by
  have hs := hasSum_weighted_strainTerm N u hu hr hd x a
  have hb := ((summable_norm_strainCoeff u hu).mul_left 9).mul_right (‖a‖ ^ 2)
  have hsn := hb.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_weighted_strainTerm_le N u k x a)
  rw [← hs.tsum_eq]
  calc
    _ ≤ ∑' k, ‖AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) * strainTerm u k x a‖ :=
      norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' k, 9 * ‖strainCoeff u k‖ * ‖a‖ ^ 2 :=
      hsn.tsum_le_tsum (fun k ↦ norm_weighted_strainTerm_le N u k x a) hb
    _ = _ := by rw [tsum_mul_right, tsum_mul_left]

theorem aestronglyMeasurable_sourceDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    AEStronglyMeasurable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ n *
      quadraticStretch N u x (fullVorticity u x)) volume := by
  have hw := continuous_fullVorticity u hu
  have hm : StronglyMeasurable (fun x : T3 ↦ ∑' k : Wavevector,
      AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) * strainTerm u k x (fullVorticity u x)) :=
    StronglyMeasurable.tsum (fun k ↦
      (continuous_const.mul ((continuous_strainTerm u k).comp (continuous_id.prodMk hw))).stronglyMeasurable)
  simp only [(hasSum_weighted_strainTerm N u hu hr hd _ _).tsum_eq] at hm
  exact (hw.norm.pow n).aestronglyMeasurable.mul hm.aestronglyMeasurable

theorem tendsto_source (n : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun N : ℕ ↦ source n N u) atTop (𝓝 (fullStretching n u)) := by
  have hw := continuous_fullVorticity u hu
  let b : T3 → ℝ := fun x ↦ ‖fullVorticity u x‖ ^ n *
    ((9 * ∑' k, ‖strainCoeff u k‖) * ‖fullVorticity u x‖ ^ 2)
  have hb : Integrable b :=
    ((hw.norm.pow n).mul (continuous_const.mul (hw.norm.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply tendsto_integral_filter_of_dominated_convergence b
  · exact Eventually.of_forall (fun N ↦ aestronglyMeasurable_sourceDensity n N u hu hr hd)
  · apply Eventually.of_forall
    intro N
    filter_upwards [] with x
    simp only [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul_of_nonneg_left (norm_quadraticStretch_le N u hu hr hd x (fullVorticity u x))
      (by positivity)
  · exact hb
  · filter_upwards [] with x
    exact tendsto_const_nhds.mul (tendsto_quadraticStretch u hu hr hd x (fullVorticity u x))

theorem tendsto_eighthMoment_source (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun N : ℕ ↦ source 6 N u) atTop (𝓝 (LocalVorticityEighthMoment.stretching u)) :=
  tendsto_source 6 u hu hr hd

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource
