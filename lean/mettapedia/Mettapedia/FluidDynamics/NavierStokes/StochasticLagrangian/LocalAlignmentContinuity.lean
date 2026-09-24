import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentForcing

/-!
# Space-time continuity of the all-input alignment remainder

A common absolute Fourier moment supplies uniform convergence. The subgrid
fiber is controlled before its infinite sum is reconstructed, so its two
unresolved input frequencies are not replaced by finite-mode data.

Continuity on a local existence window gives genuine integrability there;
it is not a uniform estimate at a maximal existence time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentContinuity

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeIndexedFourierMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeHigherDerivativeMoments
open PancakeInfiniteVelocityEnvelope PancakeSobolevFiberEnvelope PancakePeriodicVorticityEquation
open PancakeFilteredStrainDynamics PancakeFourierPressureStrain PancakeFourierMaterialPaths
open PancakeLocalGradientEquation PancakeDyadicDirectionEvolution PancakeSpatialStrainEvolution
open PancakeMeasurableMaterialRate PancakeLocalInfiniteVelocity PancakeGalerkinKineticEnergy
open PancakeRegularizedDiffusion PancakeSpectralFiniteDifference
open PancakePhysicalViscousSplit
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeTopEigenvalueDerivative
open LocalVorticityDiffusion LocalLowDiffusionBudget LocalAlignmentForcing LocalAlignmentTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Parametric

variable {P : Type*} [TopologicalSpace P]

private theorem continuous_matrix_eval (modes : Finset Wavevector)
    (A : P → FourierMatrix) (x : P → T3)
    (hA : ∀ q ∈ modes, ∀ i j, Continuous (fun z ↦ A z q i j)) (hx : Continuous x) :
    Continuous (fun z ↦ matrixReconstruction modes (A z) (x z)) := by
  refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
  simp only [matrixReconstruction_apply]
  exact continuous_finsetSum _ (fun q hq ↦ ((UnitAddTorus.mFourier q).continuous.comp hx).mul
    (hA q hq i j))

/-- Uniform absolute convergence applies to the weighted all-input fiber. -/
theorem continuous_subgridConvection (u : P → FourierVelocity)
    (hc : ∀ q i, Continuous (fun z ↦ u z q i))
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ z q, fourierMoment 2 (u z) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun z ↦ InfiniteFilteredEquation.subgridConvection chi (u z) q i) := by
  have hC : 0 ≤ C := (norm_nonneg (chi 0)).trans (hchi 0)
  unfold InfiniteFilteredEquation.subgridConvection
  refine continuous_tsum ?_
    (((summable_pairEnvelope g hg hSum).prod_factor q).mul_left (C + C * C)) ?_
  · intro k
    simp only [outputFiber, modeDot]
    fun_prop
  · intro k z
    rw [norm_mul]
    apply mul_le_mul _ (norm_outputFiber_le_momentEnvelope (u z) g hg (hu z) q k i)
      (norm_nonneg _) (by positivity)
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    gcongr <;> exact hchi _

theorem continuous_subgridForce (u : P → FourierVelocity)
    (hc : ∀ q i, Continuous (fun z ↦ u z q i))
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ z q, fourierMoment 2 (u z) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun z ↦ InfiniteFilteredEquation.subgridForce chi (u z) q i) := by
  have hs := continuous_subgridConvection u hc g hg hSum hu chi C hchi q
  simp only [InfiniteFilteredEquation.subgridForce, lerayMode]
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, modeDot] <;> fun_prop

theorem continuous_fullStrainOperator_parametric (u : P → FourierVelocity)
    (hc : ∀ q i, Continuous (fun z ↦ u z q i))
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ z q, fourierMoment 2 (u z) q ≤ g q) :
    Continuous (fun z : P × T3 ↦ fullStrainOperator (u z.1) z.2) := by
  have hm (z : P) : Summable (indexedFirstMoment id (u z)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu z))
  have hd (j : Fin 3) : Continuous (fun z : P ↦ fullFourierField id
      (indexedDerivativeCoeff id j (u z))) := by
    refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * g q)
      (hSum.mul_left _) ?_
    · intro q i
      simp only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul]
      exact continuous_const.mul (hc q i)
    · intro z q
      calc
        _ ≤ fourierMoment 0 (indexedDerivativeCoeff id j (u z)) q := by
          simpa only [fourierMoment, pow_zero, one_mul] using
            norm_coefficient_sup_le_euclidean (indexedDerivativeCoeff id j (u z) q)
        _ ≤ (2 * Real.pi) * fourierMoment 1 (u z) q := fourierMoment_derivative_le 0 _ j q
        _ ≤ (2 * Real.pi) * g q := mul_le_mul_of_nonneg_left
          ((firstMoment_le_second _ q).trans (hu z q)) (by positivity)
  have hgrad : Continuous (fun z : P × T3 ↦ spatialVelocityGradient (fullFourierField id (u z.1)) z.2) := by
    refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
    simp only [spatialVelocityGradient, coordinateDerivative_fullFourierField id _ (hm _)]
    exact (continuous_apply i).comp (continuous_eval.comp
      (((hd j).comp continuous_fst).prodMk continuous_snd))
  apply realMatrixOperatorCLM.continuous.comp
  refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
  change Continuous (fun z : P × T3 ↦ (1 / 2 : ℂ) * (_ + _))
  exact continuous_const.mul
    (((continuous_apply j).comp ((continuous_apply i).comp hgrad)).add
      ((continuous_apply i).comp ((continuous_apply j).comp hgrad)))

theorem continuous_nonviscousRemainder_parametric (u : P → FourierVelocity)
    (hc : ∀ q i, Continuous (fun z ↦ u z q i))
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ z q, fourierMoment 2 (u z) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) :
    Continuous (fun z : P × T3 ↦ nonviscousRemainder chi modes outputs (u z.1) z.2) := by
  have hv (q : Wavevector) (i : Fin 3) :
      Continuous (fun z : P ↦ filteredVelocity chi (u z) q i) := continuous_const.mul (hc q i)
  have hrec := continuous_parametric_reconstruction modes (fun z ↦ filteredVelocity chi (u z))
    (fun q _ i ↦ hv q i)
  have hU := continuous_fullFourierField_of_norm_le u hc g hSum (fun z q ↦
    (norm_coefficient_le_indexedFirstMoment id (u z) q).trans (by
      simpa only [indexedFirstMoment_id] using (firstMoment_le_second _ q).trans (hu z q)))
  have hvel : Continuous (fun z : P × T3 ↦ fullFourierField id (u z.1) z.2) :=
    continuous_eval.comp ((hU.comp continuous_fst).prodMk continuous_snd)
  have hspin (q : Wavevector) (i j : Fin 3) :
      Continuous (fun z : P × T3 ↦ spinCoeff (filteredVelocity chi (u z.1)) q i j) := by
    have hi := (hv q i).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
    have hj := (hv q j).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
    simp only [spinCoeff, gradientCoeff, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.transpose_apply, smul_eq_mul]
    fun_prop
  have hstrain (q : Wavevector) (i j : Fin 3) :
      Continuous (fun z : P × T3 ↦ strainCoeff (filteredVelocity chi (u z.1)) q i j) := by
    have hi := (hv q i).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
    have hj := (hv q j).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
    simp only [strainCoeff, gradientCoeff, Matrix.smul_apply, Matrix.add_apply,
      Matrix.transpose_apply, smul_eq_mul]
    fun_prop
  have hconv (q : Wavevector) (i : Fin 3) :
      Continuous (fun z : P ↦ convectionConvolution modes (filteredVelocity chi (u z)) q i) := by
    simp only [convectionConvolution, Finset.sum_apply]
    apply continuous_finsetSum
    intro k _
    apply continuous_finsetSum
    intro l _
    split_ifs <;> simp only [orderedConvection, Pi.smul_apply, smul_eq_mul, modeDot, Pi.zero_apply] <;>
      fun_prop
  have hp (q : Wavevector) :
      Continuous (fun z : P ↦ pressureCoeff modes (filteredVelocity chi (u z)) q) := by
    simp only [pressureCoeff, modeDot]
    fun_prop
  have hf (q : Wavevector) (i j : Fin 3) :
      Continuous (fun z : P × T3 ↦ LocalFilteredStrain.forcingCoeff chi modes (u z.1) 0 q i j) := by
    have hpi := (hp q).comp (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
    have hs (k : Fin 3) := (continuous_subgridForce u hc g hg hSum hu chi C hchi q k).comp
      (continuous_fst : Continuous (fun z : P × T3 ↦ z.1))
    simp only [LocalFilteredStrain.forcingCoeff, viscousStrainCoeff_zero, add_zero,
      pressureHessianCoeff, strainCoeff, gradientCoeff, Matrix.add_apply, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    fun_prop
  have hcorr (q : Wavevector) (i j : Fin 3) : Continuous (fun z : P × T3 ↦
      LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi (u z.1))
        (fun k ↦ InfiniteFourierTransport.velocityComponent (u z.1) k z.2) z.2 q i j) := by
    have hvc (k : Fin 3) := Complex.continuous_re.comp ((continuous_apply k).comp hvel)
    have hfc (k : Fin 3) := Complex.continuous_re.comp ((continuous_apply k).comp hrec)
    simp only [LocalFilteredStrain.transportCorrectionCoeff, realModeDot,
      InfiniteFourierTransport.velocityComponent, Pi.sub_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hW := realMatrixOperatorCLM.continuous.comp
    (continuous_matrix_eval modes _ Prod.snd (fun q _ ↦ hspin q) continuous_snd)
  have hF := realMatrixOperatorCLM.continuous.comp
    (continuous_matrix_eval outputs _ Prod.snd (fun q _ ↦ hf q) continuous_snd)
  have hC := realMatrixOperatorCLM.continuous.comp
    (continuous_matrix_eval outputs _ Prod.snd (fun q _ ↦ hcorr q) continuous_snd)
  exact ((hW.mul hW).neg.add hF).add hC

end Parametric

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)

include hSum hu

theorem continuous_strainMismatch_spaceTime (chi : Wavevector → ℂ) (modes : Finset Wavevector) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ strainMismatch chi modes (s.coefficients z.1) z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hS := continuous_subtype_val.comp
    (continuous_parametric_strain modes chi (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
      (fun q _ i ↦ hc q i))
  exact ((continuous_fullStrainOperator_parametric _ hc g hSum (fun t ↦ hu t t.2)).sub hS).clm_apply
    (continuous_fullVorticity_spaceTime s g hSum hu)

theorem continuous_residual_spaceTime (chi : Wavevector → ℂ) (modes : Finset Wavevector) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ residual chi modes (s.coefficients z.1) z.2) := by
  have hS := continuous_parametric_strain modes chi
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q _ i ↦ (s.continuous q i).comp continuous_subtype_val)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  exact ((lipschitzWith_topEigenvalue.continuous.comp hS).smul hw).sub
    ((continuous_subtype_val.comp hS).clm_apply hw)

theorem continuous_alignmentEnergy_spaceTime (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ alignmentEnergy chi modes (s.coefficients z.1) delta z.2) := by
  have hS := continuous_parametric_strain modes chi
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q _ i ↦ (s.continuous q i).comp continuous_subtype_val)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hL := lipschitzWith_topEigenvalue.continuous.comp hS
  simp only [alignmentEnergy, regularizedEnergy, regularizedGap, sub_apply, smul_apply,
    one_apply_eq_self]
  exact hw.inner (((hL.add continuous_const).smul hw).sub
    ((continuous_subtype_val.comp hS).clm_apply hw))

include hg in
theorem continuous_forcingEnvelope_spaceTime (chi : Wavevector → ℂ)
    (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C) (modes outputs : Finset Wavevector) (delta : ℝ) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      forcingEnvelope chi modes outputs (s.coefficients z.1) delta z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hS := continuous_subtype_val.comp
    (continuous_parametric_strain modes chi (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
      (fun q _ i ↦ hc q i))
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hR := continuous_nonviscousRemainder_parametric _ hc g hg hSum (fun t ↦ hu t t.2)
    chi C hchi modes outputs
  have hf := continuous_strainMismatch_spaceTime s g hSum hu chi modes
  exact (((continuous_const.mul hR.norm).mul (hw.norm.pow 2)).add
    (continuous_const.mul (hf.norm.pow 2))).add
      (continuous_const.mul (hw.inner ((hS.clm_apply hw).add hf)))

omit hSum hu in
/-- A continuous local space-time field has a continuous spatial mean. -/
theorem continuousOn_spatialIntegral (f : ℝ → T3 → ℝ)
    (hf : Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ f z.1 z.2)) :
    ContinuousOn (fun t ↦ ∫ x : T3, f t x) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun t : Set.Icc (0 : ℝ) T ↦ ∫ x : T3, f t x)
  have hi := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun t : Set.Icc (0 : ℝ) T ↦ fun x ↦ f t x) hf isCompact_univ
  simpa only [Measure.restrict_univ] using hi

include hg in
theorem intervalIntegrable_forcingEnvelope (chi : Wavevector → ℂ)
    (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C) (modes outputs : Finset Wavevector) (delta : ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3, forcingEnvelope chi modes outputs (s.coefficients τ) delta x)
      volume 0 t :=
  ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_spatialIntegral _
      (continuous_forcingEnvelope_spaceTime s g hg hSum hu chi C hchi modes outputs delta)).mono
        (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))

theorem intervalIntegrable_residual_sq (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) volume 0 t :=
  ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_spatialIntegral _
      ((continuous_residual_spaceTime s g hSum hu chi modes).norm.pow 2)).mono
        (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentContinuity
