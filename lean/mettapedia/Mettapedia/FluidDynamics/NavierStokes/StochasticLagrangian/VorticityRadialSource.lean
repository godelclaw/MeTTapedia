import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRadialQuadratic
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedSource

/-!
# The radial regularized source recovers actual vorticity stretching

Contractive radial weights recover every nonzero Fourier mode. Dominated
convergence identifies the spatial source limit, including the eighth
moment alignment functional. The fixed-snapshot Fourier majorant below
is not an a priori time budget up to a possible singularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSource

open MeasureTheory Filter PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakeGalerkinKineticEnergy LocalLowDiffusionBudget
open VorticityStretchingKernel VorticityWeightedStretching VorticityRegularizedSource
open PancakePeriodicComplexStretch PancakePeriodicVorticityEquation ComplexPressurePair
open PancakeFourierMaterialPaths PancakeFourierPressureStrain PancakeFourierStrainGradient
open PancakeMaterialDiffusionBudget LocalAlignmentForcing FullStrainFourierSeries
open Mettapedia.Analysis
open scoped RealInnerProductSpace Topology Matrix.Norms.Elementwise
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Q" => VorticityRadialQuadratic.quadraticStretch
local notation "W" => RadialRieszRegularization.weight
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_weighted_strainTerm (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    HasSum (fun k ↦ W N (UnitTorusLattice.frequency k) * strainTerm u k x a) (Q N u x a) := by
  have h := RCLike.hasSum_re ℂ (VorticityRadialQuadratic.hasSum_quadraticStretch N u hu hr hd x a)
  simpa only [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, RCLike.re_to_complex, strainTerm_eq_re, mul_assoc] using h

theorem norm_weighted_strainTerm_le (N : ℕ) (u : FourierVelocity) (k : Wavevector) (x : T3) (a : R3) :
    ‖W N (UnitTorusLattice.frequency k) * strainTerm u k x a‖ ≤ 9 * ‖strainCoeff u k‖ * ‖a‖ ^ 2 := by
  rw [norm_mul, Real.norm_of_nonneg (RadialRieszRegularization.weight_nonneg _ _)]
  exact (mul_le_mul_of_nonneg_right (RadialRieszRegularization.weight_le_one _ _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_strainTerm_le u k x a)

theorem tendsto_quadraticStretch (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    Tendsto (fun N : ℕ ↦ Q N u x a) atTop (𝓝 ⟪a, fullStrainOperator u x a⟫) := by
  have hb := ((summable_norm_strainCoeff u hu).mul_left 9).mul_right (‖a‖ ^ 2)
  have ht (k : Wavevector) : Tendsto
      (fun N : ℕ ↦ W N (UnitTorusLattice.frequency k) * strainTerm u k x a)
      atTop (𝓝 (strainTerm u k x a)) := by
    by_cases hk : k = 0
    · subst k
      have hc : strainCoeff u 0 = 0 := by
        ext i j
        simp [strainCoeff, PancakeFourierPressureStrain.gradientCoeff]
      have hz : strainTerm u 0 x a = 0 := by
        simp only [strainTerm, hc, smul_zero]
        change ⟪a, realMatrixOperatorCLM 0 a⟫ = 0
        rw [map_zero]
        simp only [zero_apply, inner_zero_right]
      simp only [hz, mul_zero]
      exact tendsto_const_nhds
    · simpa only [one_mul] using (RadialRieszRegularization.tendsto_weight _
        (PeriodicRieszKernel.one_le_norm_frequency k hk)).mul_const (strainTerm u k x a)
  have h := tendsto_tsum_of_dominated_convergence hb ht
    (Eventually.of_forall (fun N k ↦ norm_weighted_strainTerm_le N u k x a))
  simpa only [(hasSum_weighted_strainTerm _ u hu hr hd x a).tsum_eq,
    (hasSum_strainTerm u hu x a).tsum_eq] using h

def source (n N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ n * Q N u x (fullVorticity u x)

theorem norm_quadraticStretch_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    ‖Q N u x a‖ ≤ (9 * ∑' k, ‖strainCoeff u k‖) * ‖a‖ ^ 2 := by
  have hs := hasSum_weighted_strainTerm N u hu hr hd x a
  have hb := ((summable_norm_strainCoeff u hu).mul_left 9).mul_right (‖a‖ ^ 2)
  have hn := hb.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_weighted_strainTerm_le N u k x a)
  rw [← hs.tsum_eq]
  calc
    _ ≤ ∑' k, ‖W N (UnitTorusLattice.frequency k) * strainTerm u k x a‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, 9 * ‖strainCoeff u k‖ * ‖a‖ ^ 2 :=
      hn.tsum_le_tsum (fun k ↦ norm_weighted_strainTerm_le N u k x a) hb
    _ = _ := by rw [tsum_mul_right, tsum_mul_left]

theorem aestronglyMeasurable_sourceDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    AEStronglyMeasurable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ n * Q N u x (fullVorticity u x)) volume := by
  have hw := continuous_fullVorticity u hu
  have hm : StronglyMeasurable (fun x : T3 ↦ ∑' k : Wavevector,
      W N (UnitTorusLattice.frequency k) * strainTerm u k x (fullVorticity u x)) :=
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

end Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSource
