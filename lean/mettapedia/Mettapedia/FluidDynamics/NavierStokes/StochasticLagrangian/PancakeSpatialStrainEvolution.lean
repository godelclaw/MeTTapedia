import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierMaterialPaths

/-!
# Reconstruction of the filtered strain equation along material paths

Finite convolution is reconstructed as the actual matrix product.
Output sets include both retained modes and every nonlinear pair output;
no projection of the product is silently omitted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialStrainEvolution

open scoped BigOperators ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierPressureStrain PancakeFilteredStrainDynamics PancakeBlockReality
open PancakeFrequencyProjectorCommutator PancakeLowPressureBudget PancakeFourierMaterialPaths
open PancakeGalerkinKineticEnergy PancakeFiniteFourierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

/-- A concrete output set carrying both linear and quadratic dynamics. -/
def materialOutputModes (modes : Finset Wavevector) : Finset Wavevector :=
  modes ∪ finiteCutoffOutputModes modes modes

theorem subset_materialOutputModes (modes : Finset Wavevector) :
    modes ⊆ materialOutputModes modes := Finset.subset_union_left

theorem add_mem_materialOutputModes (modes : Finset Wavevector)
    (k : Wavevector) (hk : k ∈ modes) (l : Wavevector) (hl : l ∈ modes) :
    k + l ∈ materialOutputModes modes :=
  Finset.mem_union_right _ ((mem_finiteCutoffOutputModes_iff modes modes (k + l)).mpr
    ⟨k, hk, l, hl, rfl⟩)

theorem matrixReconstruction_add (modes : Finset Wavevector) (A B : FourierMatrix) (x : T3) :
    matrixReconstruction modes (fun q ↦ A q + B q) x =
      matrixReconstruction modes A x + matrixReconstruction modes B x := by
  simp [matrixReconstruction, smul_add, Finset.sum_add_distrib]

theorem matrixReconstruction_sub (modes : Finset Wavevector) (A B : FourierMatrix) (x : T3) :
    matrixReconstruction modes (fun q ↦ A q - B q) x =
      matrixReconstruction modes A x - matrixReconstruction modes B x := by
  simp [matrixReconstruction, smul_sub, Finset.sum_sub_distrib]

theorem matrixReconstruction_neg (modes : Finset Wavevector) (A : FourierMatrix) (x : T3) :
    matrixReconstruction modes (fun q ↦ -A q) x = -matrixReconstruction modes A x := by
  simp [matrixReconstruction]

theorem spatialGradient_eq_strain_add_spin (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    realMatrixOperator (matrixReconstruction modes (gradientCoeff u) x) =
      (spatialStrain modes u x).1 + spatialSpin modes u x := by
  have h : gradientCoeff u = fun q ↦ strainCoeff u q + spinCoeff u q :=
    funext (gradientCoeff_eq_strain_add_spin u)
  rw [h, matrixReconstruction_add, realMatrixOperator_add]
  rfl

theorem matrixReconstruction_subset (modes outputs : Finset Wavevector) (A : FourierMatrix)
    (x : T3) (hsub : modes ⊆ outputs) (hA : ∀ q, q ∉ modes → A q = 0) :
    matrixReconstruction outputs A x = matrixReconstruction modes A x := by
  symm
  apply Finset.sum_subset hsub
  intro q _ hq
  rw [hA q hq, smul_zero]

/-- Regrouping finite nonlinear terms by output frequency is lossless once
every pair output is included. -/
theorem matrixReconstruction_pairSum
    (modes outputs : Finset Wavevector) (F : Wavevector → Wavevector → MatrixCoefficient)
    (x : T3) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    matrixReconstruction outputs
      (fun q ↦ ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then F k l else 0) x =
        ∑ k ∈ modes, ∑ l ∈ modes, UnitAddTorus.mFourier (k + l) x • F k l := by
  classical
  simp only [matrixReconstruction, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp [smul_ite, hout k hk l hl]

theorem matrixReconstruction_product (modes outputs : Finset Wavevector)
    (A B : FourierMatrix) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    matrixReconstruction outputs
      (fun q ↦ ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then A l * B k else 0) x =
        matrixReconstruction modes A x * matrixReconstruction modes B x := by
  rw [matrixReconstruction_pairSum modes outputs _ x hout]
  simp only [matrixReconstruction, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [UnitAddTorus.mFourier_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm]

theorem matrixReconstruction_strainSpinSquare (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    matrixReconstruction outputs (strainSpinSquareCoeff modes u) x =
      matrixReconstruction modes (strainCoeff u) x * matrixReconstruction modes (strainCoeff u) x +
        matrixReconstruction modes (spinCoeff u) x * matrixReconstruction modes (spinCoeff u) x := by
  have he : strainSpinSquareCoeff modes u = fun q ↦
      (∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then strainCoeff u l * strainCoeff u k else 0) +
      (∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then spinCoeff u l * spinCoeff u k else 0) := by
    funext q
    simp only [strainSpinSquareCoeff, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp
  rw [he, matrixReconstruction_add, matrixReconstruction_product modes outputs _ _ x hout,
    matrixReconstruction_product modes outputs _ _ x hout]

theorem filteredVelocity_conjugate (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hchi : ∀ q, chi (-q) = conj (chi q))
    (hu : ∀ q, u (-q) = coefficientConjugate (u q)) :
    ∀ q, filteredVelocity chi u (-q) = coefficientConjugate (filteredVelocity chi u q) := by
  intro q
  ext i
  simp [filteredVelocity, coefficientConjugate, hchi, hu]

theorem filtered_strain_zero_of_not_mem (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hchi : ∀ q, q ∉ modes → chi q = 0)
    (q : Wavevector) (hq : q ∉ modes) : strainCoeff (filteredVelocity chi u) q = 0 := by
  ext i j
  simp [strainCoeff, gradientCoeff, filteredVelocity, hchi q hq]

theorem realMatrixOperator_strainSpinSquare (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hu : ∀ q, u (-q) = coefficientConjugate (u q))
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    realMatrixOperator (matrixReconstruction outputs (strainSpinSquareCoeff modes u) x) =
      (spatialStrain modes u x).1 * (spatialStrain modes u x).1 +
        spatialSpin modes u x * spatialSpin modes u x := by
  rw [matrixReconstruction_strainSpinSquare modes outputs u x hout, realMatrixOperator_add,
    realMatrixOperator_mul _ _ (matrixReconstruction_real modes _ hs (strainCoeff_conjugate u hu) x),
    realMatrixOperator_mul _ _ (matrixReconstruction_real modes _ hs (spinCoeff_conjugate u hu) x)]
  rfl

theorem strainAdvectionCoeff_pairSum (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    strainAdvectionCoeff modes u q =
      ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then
        (unitTorusDerivativePhase * modeDot l (u k)) • strainCoeff u l else 0 := by
  simp only [strainAdvectionCoeff, gradientAdvectionCoeff, map_sum, apply_ite,
    map_smul, symmetrize_gradient, map_zero]

/-- Reconstructed strain advection is exactly the character-motion term
generated by the reconstructed velocity. -/
theorem matrixReconstruction_strainAdvection (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    matrixReconstruction outputs (strainAdvectionCoeff modes u) x =
      ∑ q ∈ modes, finiteVelocityCharacterRate modes u q x • strainCoeff u q := by
  change matrixReconstruction outputs (fun q ↦ strainAdvectionCoeff modes u q) x = _
  simp_rw [strainAdvectionCoeff_pairSum]
  rw [matrixReconstruction_pairSum modes outputs _ x hout]
  simp only [finiteVelocityCharacterRate, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem matrixReconstruction_material_advection
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hu : ∀ q, u (-q) = coefficientConjugate (u q))
    (hA : ∀ q, q ∉ modes → strainCoeff u q = 0) :
    matrixReconstruction outputs (fun q ↦
      (unitTorusDerivativePhase *
        (realModeDot q (fun i ↦ (finiteFourierReconstruction modes u x i).re) : ℂ)) •
        strainCoeff u q) x = matrixReconstruction outputs (strainAdvectionCoeff modes u) x := by
  rw [matrixReconstruction_subset modes outputs _ x hsub (fun q hq ↦ by rw [hA q hq, smul_zero]),
    matrixReconstruction_strainAdvection modes outputs u x hout]
  simp only [matrixReconstruction, smul_smul]
  apply Finset.sum_congr rfl
  intro q _
  rw [ofReal_realModeDot_reconstruction modes u q x hs hu, finiteVelocityCharacterRate_eq]
  rw [mul_comm]

def strainForcingCoeff (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (q : Wavevector) : MatrixCoefficient :=
  -(chi q • pressureHessianCoeff modes u q) +
    viscousStrainCoeff nu (filteredVelocity chi u) q + subgridStrainCoeff chi modes u q

/-- The full complex matrix equation along the real trajectory is derived
from retained velocity dynamics. Neither its phase rate nor its material
strain derivative is supplied independently. -/
theorem hasDerivAt_filtered_strain_matrix_material
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (nu t : ℝ)
    (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u t (-q) = coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes (filteredVelocity chi (u t)) (torusPoint (X t)) i).re t) :
    HasDerivAt (fun tau ↦ matrixReconstruction outputs
      (strainCoeff (filteredVelocity chi (u tau))) (torusPoint (X tau)))
      (-matrixReconstruction outputs (strainSpinSquareCoeff modes (filteredVelocity chi (u t)))
        (torusPoint (X t)) +
        matrixReconstruction outputs (strainForcingCoeff chi modes (u t) nu) (torusPoint (X t))) t := by
  let v := filteredVelocity chi (u t)
  let x := torusPoint (X t)
  let rate : FourierMatrix := fun q ↦
    -strainSpinSquareCoeff modes v q - chi q • pressureHessianCoeff modes (u t) q +
      viscousStrainCoeff nu v q + subgridStrainCoeff chi modes (u t) q - strainAdvectionCoeff modes v q
  have hrate : ∀ q ∈ outputs, ∀ i j,
      HasDerivAt (fun tau ↦ strainCoeff (filteredVelocity chi (u tau)) q i j) (rate q i j) t :=
    fun q _ i j ↦ hasDerivAt_filtered_strain_of_retained_velocityRHS chi modes u nu t q i j
      hchi hk hu hd
  have h := hasDerivAt_matrixReconstruction_moving outputs
    (fun tau ↦ strainCoeff (filteredVelocity chi (u tau))) rate X _ t hrate hX
  apply h.congr_deriv
  rw [matrixReconstruction_add]
  have hadv := matrixReconstruction_material_advection modes outputs v x hsub hout hs
    (filteredVelocity_conjugate chi (u t) hchir hr) (filtered_strain_zero_of_not_mem chi modes (u t) hchi)
  rw [hadv]
  have hrates : rate = fun q ↦
      -strainSpinSquareCoeff modes v q + strainForcingCoeff chi modes (u t) nu q -
        strainAdvectionCoeff modes v q := by
    funext q
    dsimp [rate, strainForcingCoeff, v]
    abel
  rw [hrates, matrixReconstruction_sub, matrixReconstruction_add, matrixReconstruction_neg]
  abel

/-- Constructed pressure/viscous/subgrid part of the real material strain
forcing. The spin-square contribution is kept separately. -/
def spatialStrainForcing (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction outputs (strainForcingCoeff chi modes u nu) x)

def spatialStrainRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : R3 →L[ℝ] R3 :=
  -(spatialSpin modes (filteredVelocity chi u) x * spatialSpin modes (filteredVelocity chi u) x) +
    spatialStrainForcing chi modes outputs u nu x

theorem realMatrixOperator_adjoint (A : MatrixCoefficient) :
    ContinuousLinearMap.adjoint (realMatrixOperator A) = realMatrixOperator A.transpose := by
  change star (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (realMatrix A)) =
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (realMatrix A.transpose)
  rw [← map_star]
  congr 1

theorem spatialSpin_skew (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    ∀ v w : R3, ⟪spatialSpin modes u x v, w⟫ = -⟪v, spatialSpin modes u x w⟫ := by
  have ht : (matrixReconstruction modes (spinCoeff u) x).transpose =
      -matrixReconstruction modes (spinCoeff u) x := by
    rw [matrixReconstruction_transpose]
    simp only [spinCoeff_transpose, matrixReconstruction_neg]
  have ha := realMatrixOperator_adjoint (matrixReconstruction modes (spinCoeff u) x)
  rw [ht, realMatrixOperator_neg] at ha
  intro v w
  have h := ContinuousLinearMap.adjoint_inner_right (spatialSpin modes u x) v w
  rw [show ContinuousLinearMap.adjoint (spatialSpin modes u x) = -spatialSpin modes u x from ha] at h
  simpa only [neg_apply, inner_neg_right] using h.symm

/-- The spin contribution keeps both terms for a filtered strain and an
arbitrary receiver. In particular `W_low w_high = 0` is not presumed. -/
theorem spatialStrainRemainder_anisotropy (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (nu : ℝ) (x : T3) (e w : R3) :
    PancakeSpectralDefectEvolution.remainderAnisotropy
      (spatialStrainRemainder chi modes outputs u nu x) e w =
        ‖spatialSpin modes (filteredVelocity chi u) x e‖ ^ 2 * ‖w‖ ^ 2 -
          ‖spatialSpin modes (filteredVelocity chi u) x w‖ ^ 2 +
          PancakeSpectralDefectEvolution.remainderAnisotropy
            (spatialStrainForcing chi modes outputs u nu x) e w := by
  let W := spatialSpin modes (filteredVelocity chi u) x
  have hm : -(W * W) = -W * W := by ext v; rfl
  unfold spatialStrainRemainder
  rw [PancakeSpectralDefectEvolution.remainderAnisotropy_add, hm]
  rw [PancakeSpectralDefectEvolution.remainderAnisotropy_negative_skew_square W e w
    (spatialSpin_skew modes (filteredVelocity chi u) x)]

/-- The real self-adjoint strain along a material path obeys the equation
needed by the spectral-defect identity. Its remainder is the constructed
spin/pressure/viscous/subgrid expression, not an assumed strain ODE. -/
theorem hasDerivAt_spatialStrain_material
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (nu t : ℝ)
    (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u t (-q) = coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes (filteredVelocity chi (u t)) (torusPoint (X t)) i).re t) :
    HasDerivAt (fun tau ↦ (spatialStrain modes (filteredVelocity chi (u tau))
      (torusPoint (X tau))).1)
      (-(spatialStrain modes (filteredVelocity chi (u t)) (torusPoint (X t))).1 *
        (spatialStrain modes (filteredVelocity chi (u t)) (torusPoint (X t))).1 +
        spatialStrainRemainder chi modes outputs (u t) nu (torusPoint (X t))) t := by
  have hdM := hasDerivAt_filtered_strain_matrix_material chi modes outputs u X nu t
    hsub hout hchi hchir hs hr hk hu hd hX
  have hdR := hasDerivAt_realMatrixOperator _ _ t hdM
  have hfun : (fun tau ↦ realMatrixOperator (matrixReconstruction outputs
      (strainCoeff (filteredVelocity chi (u tau))) (torusPoint (X tau)))) =
      fun tau ↦ (spatialStrain modes (filteredVelocity chi (u tau)) (torusPoint (X tau))).1 := by
    funext tau
    change realMatrixOperator _ = realMatrixOperator _
    rw [matrixReconstruction_subset modes outputs _ _ hsub
      (filtered_strain_zero_of_not_mem chi modes (u tau) hchi)]
  rw [hfun] at hdR
  apply hdR.congr_deriv
  rw [realMatrixOperator_add, realMatrixOperator_neg,
    realMatrixOperator_strainSpinSquare modes outputs _ _ hs
      (filteredVelocity_conjugate chi (u t) hchir hr) hout]
  simp only [spatialStrainRemainder, spatialStrainForcing]
  ext v
  simp only [add_apply, neg_apply, mul_apply_eq_comp]
  abel_nf

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialStrainEvolution
