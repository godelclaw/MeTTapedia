import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierStrainGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalSpectralDefect
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePressureAnisotropyBudget
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fixed-low strain-gradient cost paid by the physical velocity energy

The actual spatial strain-gradient cost is integrated against the full
reconstructed vorticity. Parseval avoids a receiver-cardinality loss.
The retained velocity ODE supplies the time-integrated energy payment.
The low-cutoff fourth moment and positive regularization parameter remain
explicit. This is not the missing all-scale estimate or a weak diffusion
chain rule for the nonsmooth largest eigenvalue.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLowDiffusionBudget

open scoped BigOperators Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFourierPressureStrain PancakeFilteredStrainDynamics
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakePhysicalSpectralDefect
open PancakeFrequencyProjectorCommutator PancakeViscousMisalignmentAbsorption
open PancakePressureAnisotropyBudget PancakeGalerkinKineticEnergy
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PancakeRegularizedDiffusion PancakeSpatialStrainEvolution

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def lowDiffusionDensity (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : ℝ :=
  (∑ j : Fin 3, ‖strainGradient outputs (filteredVelocity chi u) x j‖ ^ 2) *
    ‖spatialVorticity modes u x‖ ^ 2

theorem spatialStrain_filtered_subset (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) (hsub : outputs ⊆ modes)
    (hchi : ∀ q, q ∉ outputs → chi q = 0) :
    spatialStrain modes (filteredVelocity chi u) x = spatialStrain outputs (filteredVelocity chi u) x := by
  apply Subtype.ext
  change realMatrixOperator (matrixReconstruction modes (strainCoeff (filteredVelocity chi u)) x) =
    realMatrixOperator (matrixReconstruction outputs (strainCoeff (filteredVelocity chi u)) x)
  exact congrArg realMatrixOperator (matrixReconstruction_subset outputs modes _ x hsub
    (filtered_strain_zero_of_not_mem chi outputs u hchi))

theorem strainGradient_filtered_subset (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) (j : Fin 3) (hsub : outputs ⊆ modes)
    (hchi : ∀ q, q ∉ outputs → chi q = 0) :
    strainGradient modes (filteredVelocity chi u) x j =
      strainGradient outputs (filteredVelocity chi u) x j := by
  unfold strainGradient
  rw [matrixReconstruction_subset outputs modes _ x hsub (fun q hq ↦ by
    rw [strainDerivativeCoeff, filtered_strain_zero_of_not_mem chi outputs u hchi q hq, smul_zero])]

/-- The paid gradient algebra is specialized to the actual low strain
and full reconstructed vorticity. `v` can be their actual curl gradients. -/
theorem regularizedGradientRate_paid (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) (v : Fin 3 → R3) (delta nu : ℝ)
    (hd : 0 < delta) (hnu : 0 ≤ nu) :
    let S := spatialStrain outputs (filteredVelocity chi u) x
    nu * (∑ j, gradientProduction S delta
      (gapDerivative S (strainGradient outputs (filteredVelocity chi u) x j))
        (spatialVorticity modes u x) (v j)) + nu * delta * (∑ j, ‖v j‖ ^ 2) ≤
      (16 * nu / delta) * lowDiffusionDensity outputs modes chi u x := by
  dsimp only
  have h := gradientProduction_sum_paid Finset.univ
    (spatialStrain outputs (filteredVelocity chi u) x) delta nu
    (strainGradient outputs (filteredVelocity chi u) x) (spatialVorticity modes u x) v hd hnu
  simpa only [lowDiffusionDensity, mul_assoc] using h

theorem lowDiffusionDensity_nonneg (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : 0 ≤ lowDiffusionDensity outputs modes chi u x := by
  unfold lowDiffusionDensity
  positivity

theorem norm_realPart_sq_le (w : VelocityCoefficient) :
    ‖complexRealPartEuclidean w‖ ^ 2 ≤ ‖coefficientVec w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm (w i)) 2

theorem lowDiffusionDensity_le (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) (hsub : outputs ⊆ modes) :
    lowDiffusionDensity outputs modes chi u x ≤
      (strainGradientCutoffWeight outputs chi * fullEnergy modes u) *
        ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2 := by
  apply mul_le_mul (sum_norm_strainGradient_sq_le outputs modes chi u x hsub)
    (norm_realPart_sq_le _) (sq_nonneg _) ?_
  exact mul_nonneg (strainGradientCutoffWeight_nonneg outputs chi) (fullEnergy_nonneg _ _)

theorem integral_lowDiffusionDensity_le (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (hsub : outputs ⊆ modes) :
    (∫ x : T3, lowDiffusionDensity outputs modes chi u x) ≤
      strainGradientCutoffWeight outputs chi * fullEnergy modes u * fullEnergy modes (fourierCurl u) := by
  have hi : Integrable (fun x : T3 ↦
      (strainGradientCutoffWeight outputs chi * fullEnergy modes u) *
        ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2) :=
    (continuous_const.mul ((continuous_coefficientReconstruction modes (fourierCurl u)).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (lowDiffusionDensity_nonneg outputs modes chi u)) hi
    (Filter.Eventually.of_forall (fun x ↦ lowDiffusionDensity_le outputs modes chi u x hsub))
  rw [integral_const_mul, integral_norm_coefficientReconstruction_sq] at h
  exact h

section Continuity

variable {P : Type*} [TopologicalSpace P]

theorem continuous_parametric_strainGradient (outputs : Finset Wavevector)
    (chi : Wavevector → ℂ) (u : P → FourierVelocity) (j : Fin 3)
    (hu : ∀ q ∈ outputs, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ strainGradient outputs (filteredVelocity chi (u z.1)) z.2 j) := by
  apply realMatrixOperatorCLM.continuous.comp
  refine continuous_pi (fun a ↦ continuous_pi (fun b ↦ ?_))
  simp only [matrixReconstruction_apply]
  apply continuous_finsetSum
  intro q hq
  have ha := (hu q hq a).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  have hb := (hu q hq b).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  simp only [strainDerivativeCoeff, strainCoeff, gradientCoeff, filteredVelocity,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

theorem continuous_parametric_spatialVorticity (modes : Finset Wavevector)
    (u : P → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ spatialVorticity modes (u z.1) z.2) := by
  apply complexRealPartEuclideanCLM.continuous.comp
  change Continuous (fun z : P × T3 ↦ finiteFourierReconstruction modes (fourierCurl (u z.1)) z.2)
  refine continuous_pi (fun i ↦ ?_)
  simp only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro q hq
  have h0 := (hu q hq 0).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  have h1 := (hu q hq 1).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  have h2 := (hu q hq 2).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
  fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop

theorem continuous_parametric_lowDiffusionDensity (outputs modes : Finset Wavevector)
    (chi : Wavevector → ℂ) (u : P → FourierVelocity) (hsub : outputs ⊆ modes)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ lowDiffusionDensity outputs modes chi (u z.1) z.2) := by
  apply Continuous.mul _ ((continuous_parametric_spatialVorticity modes u hu).norm.pow 2)
  apply continuous_finsetSum
  intro j _
  exact (continuous_parametric_strainGradient outputs chi u j (fun q hq ↦ hu q (hsub hq))).norm.pow 2

theorem continuous_parametric_integral_lowDiffusionDensity
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : P → FourierVelocity)
    (hsub : outputs ⊆ modes)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun p ↦ ∫ x : T3, lowDiffusionDensity outputs modes chi (u p) x) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun p x ↦ lowDiffusionDensity outputs modes chi (u p) x)
    (continuous_parametric_lowDiffusionDensity outputs modes chi u hsub hu) isCompact_univ
  simpa only [Measure.restrict_univ] using h

end Continuity

theorem spacetime_lowDiffusionDensity_of_velocityRHS
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : ℝ → FourierVelocity) (nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hsub : outputs ⊆ modes)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k,
      u t (-k) = PancakeBlockReality.coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    IntervalIntegrable (fun t ↦ ∫ x : T3, lowDiffusionDensity outputs modes chi (u t) x) volume 0 T ∧
    (∫ t in (0 : ℝ)..T, ∫ x : T3, lowDiffusionDensity outputs modes chi (u t) x) ≤
      strainGradientCutoffWeight outputs chi * fullEnergy modes (u 0) ^ 2 / (2 * nu) := by
  have hc := continuousOn_coefficients_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hcont : ContinuousOn
      (fun t ↦ ∫ x : T3, lowDiffusionDensity outputs modes chi (u t) x) (Set.Icc (0 : ℝ) T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact continuous_parametric_integral_lowDiffusionDensity outputs modes chi
      (fun t : Set.Icc (0 : ℝ) T ↦ u t) hsub (fun q hq i ↦ (hc q hq i).restrict)
  have hDI : IntervalIntegrable
      (fun t ↦ ∫ x : T3, lowDiffusionDensity outputs modes chi (u t) x) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT hcont
  have hO := continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hOI : IntervalIntegrable (fun t ↦ fullEnergy modes (fourierCurl (u t))) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT hO
  have hU := kineticEnergy_le_initial_on modes u nu T hnu.le hs hr hu he
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ x : T3, lowDiffusionDensity outputs modes chi (u t) x) ≤
        (strainGradientCutoffWeight outputs chi * fullEnergy modes (u 0)) *
          fullEnergy modes (fourierCurl (u t)) := by
    intro t ht
    apply (integral_lowDiffusionDensity_le outputs modes chi (u t) hsub).trans
    gcongr
    · exact fullEnergy_nonneg _ _
    · exact strainGradientCutoffWeight_nonneg outputs chi
    · exact hU t ht
  refine ⟨hDI, ?_⟩
  have hm := intervalIntegral.integral_mono_on hT hDI (hOI.const_mul _) hp
  rw [intervalIntegral.integral_const_mul] at hm
  apply hm.trans
  apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
  have hE := enstrophy_integral_le_initial modes u nu T hT hs hr hu he
  have h := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (strainGradientCutoffWeight_nonneg outputs chi) (fullEnergy_nonneg modes (u 0)))
  nlinarith

theorem regularized_lowDiffusion_payment_of_velocityRHS
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : ℝ → FourierVelocity) (delta nu T : ℝ) (hd : 0 < delta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hsub : outputs ⊆ modes)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k,
      u t (-k) = PancakeBlockReality.coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    (16 * nu / delta) *
      (∫ t in (0 : ℝ)..T, ∫ x : T3, lowDiffusionDensity outputs modes chi (u t) x) ≤
        8 * strainGradientCutoffWeight outputs chi * fullEnergy modes (u 0) ^ 2 / delta := by
  have h := (spacetime_lowDiffusionDensity_of_velocityRHS outputs modes chi u nu T hnu hT
    hsub hs hr hu he).2
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 16 * nu / delta)
  convert hh using 1 <;> first | rfl | field_simp; ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeLowDiffusionBudget
