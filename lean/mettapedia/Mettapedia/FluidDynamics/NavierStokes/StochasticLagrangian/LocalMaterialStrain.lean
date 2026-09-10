import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialStrain
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalPressureContinuity

/-!
# Real strain evolution and regularity on actual material paths

The real operator equation `S' = -S² + R` is derived from the constructed
unforced local solution. Its remainder retains spin, the actual pressure
Hessian, and viscous diffusion. A common third Fourier moment suffices for
continuous differentiability on the open existence interval.

No uniform estimate towards a possible terminal singularity is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMaterialStrain

open scoped RealInnerProductSpace Matrix.Norms.Elementwise ContDiff
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeLocalMaterialGradient PancakeLocalMaterialStrain PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalGradientEquation PancakeMatrixDifferentialSymmetry
open PancakeSpatialGradientRegularity PancakeFilteredStrainDynamics PancakeLocalStrainEquation
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian PancakeLocalStrainReality
open PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian PancakeInfiniteFourierDerivative
open PancakeIndexedFourierMoments PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeIncomingLowSourceEnergy PancakeTransverseEnergyFreezing
open PancakeLocalPressureContinuity LocalMaterialVorticity LocalVorticityDiffusion
open PancakeSpectralProjectorRegularity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- The actual material strain, with symmetry recorded in its type. -/
def symmetricStrainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : SymmetricStrain :=
  ⟨strainAlong s X t, realMatrixOperator_symmetric _
    (spatialStrain_symmetric (spatialField s t) (torusPoint (X t)))⟩

/-- The physical remainder in the strain Riccati equation. This is not an
external body force: all three terms are present in the unforced equation. -/
def strainRemainderAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 →L[ℝ] R3 :=
  realMatrixOperator
    (-PancakeLocalStrainEquation.spatialSpin (spatialField s t) (torusPoint (X t)) *
        PancakeLocalStrainEquation.spatialSpin (spatialField s t) (torusPoint (X t)) -
      spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) +
      (nu : ℂ) • matrixLaplacian
        (PancakeLocalStrainEquation.spatialStrain (spatialField s t)) (torusPoint (X t)))

theorem hasDerivAt_strainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (strainAlong s X)
      (-strainAlong s X t * strainAlong s X t + strainRemainderAlong s X t) t := by
  have hm := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
  have hr (i j : Fin 3) :
      (PancakeLocalStrainEquation.spatialStrain (spatialField s t) (torusPoint (X t)) i j).im = 0 := by
    have h := congrArg Complex.im (spatialStrain_reality _ hm (s.reality t) (torusPoint (X t)) i j)
    simp only [Complex.conj_im] at h
    dsimp [spatialField]
    linarith
  have h := hasDerivAt_realMatrixOperator _ _ t (strain_material s g hg hSum hu X hX t ht)
  simp only [realMatrixOperator_add, realMatrixOperator_sub, realMatrixOperator_neg,
    realMatrixOperator_mul _ _ hr, neg_add_rev] at h
  convert! h using 1
  simp only [strainAlong, strainRemainderAlong, realMatrixOperator_add,
    realMatrixOperator_sub, neg_mul, realMatrixOperator_neg]
  ext v
  simp only [add_apply, sub_apply, neg_apply, mul_apply_eq_comp]
  abel_nf

/-- Evaluate a jointly continuous field on a material path. -/
theorem continuousOn_material_eval {E : Type*} [TopologicalSpace E]
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (f : ℝ → T3 → E)
    (hf : Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ f z.1 z.2))
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    {K : Set ℝ} (hK : K ⊆ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun t ↦ f t (torusPoint (X t))) K := by
  have hcX : Continuous (fun τ : K ↦ X τ) :=
    ContinuousOn.restrict (fun τ hτ ↦ (hX τ (hK hτ)).continuousAt.continuousWithinAt)
  have hcpoint : Continuous (fun τ : K ↦ torusPoint (X τ)) :=
    continuous_pi (fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp hcX))
  let time : K → Set.Icc (0 : ℝ) T :=
    fun τ ↦ ⟨τ, Set.Ioo_subset_Icc_self (hK τ.2)⟩
  have hctime : Continuous time := continuous_subtype_val.subtype_mk _
  exact continuousOn_iff_continuous_restrict.mpr (hf.comp (hctime.prodMk hcpoint))

theorem norm_laplacianDerivativeCoeff_le (u : FourierVelocity) (j : Fin 3) (q : Wavevector) :
    ‖laplacianCoeff (indexedDerivativeCoeff id j u) q‖ ≤
      (2 * Real.pi)^3 * fourierMoment 3 u q := by
  calc
    _ ≤ fourierMoment 0 (laplacianCoeff (indexedDerivativeCoeff id j u)) q := by
      simpa only [fourierMoment, pow_zero, one_mul] using
        norm_coefficient_sup_le_euclidean (laplacianCoeff (indexedDerivativeCoeff id j u) q)
    _ ≤ (2 * Real.pi)^2 * fourierMoment 2 (indexedDerivativeCoeff id j u) q :=
      fourierMoment_laplacian_le 0 _ q
    _ ≤ (2 * Real.pi)^2 * ((2 * Real.pi) * fourierMoment 3 u q) :=
      mul_le_mul_of_nonneg_left (fourierMoment_derivative_le 2 u j q) (sq_nonneg _)
    _ = _ := by ring

variable (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hSum hu

theorem continuous_laplacianGradient_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      matrixLaplacian (spatialVelocityGradient (spatialField s z.1)) z.2) := by
  have hc (j : Fin 3) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (laplacianCoeff (indexedDerivativeCoeff id j (s.coefficients t)))) := by
    refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi)^3 * g q)
      (hSum.mul_left _) ?_
    · intro q i
      have hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
        (s.continuous q i).comp continuous_subtype_val
      simp only [laplacianCoeff, indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul]
      fun_prop
    · intro t q
      exact (norm_laplacianDerivativeCoeff_le _ j q).trans
        (mul_le_mul_of_nonneg_left (hu t t.2 q) (by positivity))
  have he (t : Set.Icc (0 : ℝ) T) (j : Fin 3) :
      spatialLaplacian (fun y ↦ coordinateDerivative (spatialField s t) j y) =
        fullFourierField id (laplacianCoeff (indexedDerivativeCoeff id j (s.coefficients t))) := by
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2)
    rw [spatialField, coordinateDerivative_fullFourierField_eq _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hm) j,
      spatialLaplacian_fullFourierField _ (summable_fourierMoment_derivative 2 _ hm j)]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [matrixLaplacian, spatialVelocityGradient, he]
  exact (continuous_apply i).comp (continuous_eval.comp
    (((hc j).comp continuous_fst).prodMk continuous_snd))

theorem continuous_laplacianStrain_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      matrixLaplacian (PancakeLocalStrainEquation.spatialStrain (spatialField s z.1)) z.2) := by
  have he (t : Set.Icc (0 : ℝ) T) (x : T3) :
      matrixLaplacian (PancakeLocalStrainEquation.spatialStrain (spatialField s t)) x =
        symmetrize (matrixLaplacian (spatialVelocityGradient (spatialField s t)) x) := by
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2)
    have hm2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hm
    apply matrixLaplacian_symmetrize
    · intro y m
      exact HasDerivAt.differentiableAt (F := M3)
        (hasDerivAt_velocityGradient_shift _ hm2 m y)
    · intro y m n
      exact HasDerivAt.differentiableAt (F := M3)
        (hasDerivAt_matrixDerivative_gradient_shift _ hm m n y)
  simp_rw [he]
  have hc := continuous_laplacianGradient_spaceTime s g hSum hu
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z ↦ (1 / 2 : ℂ) * (_ + _))
  exact continuous_const.mul (((continuous_apply j).comp ((continuous_apply i).comp hc)).add
    ((continuous_apply i).comp ((continuous_apply j).comp hc)))

include hg

theorem continuousOn_strainRemainderAlong (hB : 0 ≤ B) (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ) :
    ContinuousOn (strainRemainderAlong s X) (Set.Ioo (0 : ℝ) T) := by
  have hA : ContinuousOn
      (fun t ↦ spatialVelocityGradient (spatialField s t) (torusPoint (X t))) (Set.Ioo (0 : ℝ) T) :=
    fun t ht ↦ (velocityGradient_material s g hg hSum hu X hX t ht).continuousAt.continuousWithinAt
  have hW : ContinuousOn
      (fun t ↦ PancakeLocalStrainEquation.spatialSpin (spatialField s t) (torusPoint (X t)))
      (Set.Ioo (0 : ℝ) T) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    change ContinuousOn (fun t ↦ (1 / 2 : ℂ) * (_ - _)) _
    exact continuousOn_const.mul
      (((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)).sub
        ((continuous_apply i).comp_continuousOn ((continuous_apply j).comp_continuousOn hA)))
  have hu2 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  have hP := continuousOn_material_eval s
    (fun t x ↦ spatialHessian (spatialPressure (s.coefficients t)) x)
    (by convert! continuous_spatialHessian_pressure_spaceTime s hB g hg hSum hu2 using 1)
    X hX Set.Subset.rfl
  have hL := continuousOn_material_eval s
    (fun t x ↦ matrixLaplacian (PancakeLocalStrainEquation.spatialStrain (spatialField s t)) x)
    (continuous_laplacianStrain_spaceTime s g hSum hu) X hX Set.Subset.rfl
  exact realMatrixOperatorCLM.continuous.comp_continuousOn
    (((hW.neg.mul hW).sub hP).add (hL.const_smul (nu : ℂ)))

omit hg hSum hu in
private theorem contDiffOn_one_of_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f d : ℝ → E} {K : Set ℝ} (hK : IsOpen K)
    (hd : ∀ t ∈ K, HasDerivAt f (d t) t) (hc : ContinuousOn d K) :
    ContDiffOn ℝ 1 f K := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hK]
  refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · rw [contDiffOn_zero]
    exact hc.congr (fun t ht ↦ (hd t ht).deriv)

theorem contDiffOn_strainAlong (hB : 0 ≤ B) (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ) :
    ContDiffOn ℝ 1 (strainAlong s X) (Set.Ioo (0 : ℝ) T) := by
  have hd := hasDerivAt_strainAlong s g hg hSum hu X hX
  have hc : ContinuousOn (strainAlong s X) (Set.Ioo (0 : ℝ) T) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  exact contDiffOn_one_of_hasDerivAt isOpen_Ioo hd
    ((hc.neg.mul hc).add (continuousOn_strainRemainderAlong s g hg hSum hu hB X hX))

theorem contDiffOn_vorticityAlong (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ) :
    ContDiffOn ℝ 1 (vorticityAlong s X) (Set.Ioo (0 : ℝ) T) := by
  have hd := hasDerivAt_vorticityAlong s g hg hSum hu X hX
  have hw : ContinuousOn (vorticityAlong s X) (Set.Ioo (0 : ℝ) T) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hS : ContinuousOn (strainAlong s X) (Set.Ioo (0 : ℝ) T) :=
    fun t ht ↦ (hasDerivAt_strainAlong s g hg hSum hu X hX t ht).continuousAt.continuousWithinAt
  have hf : ContinuousOn (diffusionAlong s X) (Set.Ioo (0 : ℝ) T) := by
    have h := continuousOn_material_eval s
      (fun t x ↦ nu • PancakeDyadicDirectionEvolution.complexRealPartEuclideanCLM
        (spatialLaplacian (spatialCurl (spatialField s t)) x))
      (by convert! continuous_diffusion_spaceTime s g hSum hu using 1) X hX Set.Subset.rfl
    convert! h using 1
  exact contDiffOn_one_of_hasDerivAt isOpen_Ioo hd ((hS.clm_apply hw).add hf)

end Mettapedia.FluidDynamics.NavierStokes.LocalMaterialStrain
