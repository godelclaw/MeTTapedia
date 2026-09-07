import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFilteredStrainDynamics
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowPressureBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMovingBlockEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectBudget
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real material paths and Fourier matrix reconstruction

Fourier character rates are derived from differentiable real coordinate
paths. Matrix-valued reconstruction keeps the coefficient product rule
and real operator identification explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFourierMaterialPaths

open scoped BigOperators ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierPressureStrain PancakeFilteredStrainDynamics PancakeBlockReality
open PancakeFrequencyProjectorCommutator PancakeLowPressureBudget

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

def torusPoint (x : Fin 3 → ℝ) : T3 := fun i ↦ (x i : UnitAddCircle)

def realModeDot (q : Wavevector) (v : Fin 3 → ℝ) : ℝ := ∑ i, (q i : ℝ) * v i

theorem mFourier_torusPoint (q : Wavevector) (x : Fin 3 → ℝ) :
    UnitAddTorus.mFourier q (torusPoint x) =
      Complex.exp (unitTorusDerivativePhase * (realModeDot q x : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusPoint,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [realModeDot, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Finset.mul_sum, unitTorusDerivativePhase]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasDerivAt_realModeDot (q : Wavevector) (X : ℝ → Fin 3 → ℝ)
    (v : Fin 3 → ℝ) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i) (v i) t) :
    HasDerivAt (fun tau ↦ realModeDot q (X tau)) (realModeDot q v) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hX i).const_mul (q i : ℝ))

/-- The character derivative is a consequence of the real path derivative,
not an independent hypothesis on the phase. -/
theorem hasDerivAt_mFourier_torusPoint (q : Wavevector) (X : ℝ → Fin 3 → ℝ)
    (v : Fin 3 → ℝ) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i) (v i) t) :
    HasDerivAt (fun tau ↦ UnitAddTorus.mFourier q (torusPoint (X tau)))
      (unitTorusDerivativePhase * (realModeDot q v : ℂ) *
        UnitAddTorus.mFourier q (torusPoint (X t))) t := by
  simp_rw [mFourier_torusPoint]
  have h := (((hasDerivAt_realModeDot q X v t hX).ofReal_comp).const_mul
    unitTorusDerivativePhase).cexp
  simpa only [mul_comm] using h

def finiteVelocityCharacterRate (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) (x : T3) : ℂ :=
  ∑ k ∈ modes, unitTorusDerivativePhase * modeDot q (u k) * UnitAddTorus.mFourier (k + q) x

theorem finiteVelocityCharacterRate_eq (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (x : T3) :
    finiteVelocityCharacterRate modes u q x =
      unitTorusDerivativePhase * modeDot q (finiteFourierReconstruction modes u x) *
        UnitAddTorus.mFourier q x := by
  simp only [finiteVelocityCharacterRate, finiteFourierReconstruction,
    modeDot_sum, modeDot_smul, UnitAddTorus.mFourier_add, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ofReal_realModeDot_reconstruction (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (x : T3)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hu : ∀ k, u (-k) = coefficientConjugate (u k)) :
    (realModeDot q (fun i ↦ (finiteFourierReconstruction modes u x i).re) : ℂ) =
      modeDot q (finiteFourierReconstruction modes u x) := by
  simp only [realModeDot, modeDot, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact (finiteFourierReconstruction_im_eq_zero_of_neg_closed modes u hs hu x i).symm

/-- The fluid-generated phase rate follows from the coordinate trajectory
ODE and physical conjugate symmetry of the reconstructed velocity. -/
theorem hasDerivAt_mFourier_of_materialPath (modes : Finset Wavevector)
    (u : FourierVelocity) (X : ℝ → Fin 3 → ℝ) (q : Wavevector) (t : ℝ)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hu : ∀ k, u (-k) = coefficientConjugate (u k))
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes u (torusPoint (X t)) i).re t) :
    HasDerivAt (fun tau ↦ UnitAddTorus.mFourier q (torusPoint (X tau)))
      (finiteVelocityCharacterRate modes u q (torusPoint (X t))) t := by
  rw [finiteVelocityCharacterRate_eq,
    ← ofReal_realModeDot_reconstruction modes u q (torusPoint (X t)) hs hu]
  exact hasDerivAt_mFourier_torusPoint q X _ t hX

def matrixReconstruction (modes : Finset Wavevector) (A : FourierMatrix)
    (x : T3) : MatrixCoefficient := ∑ q ∈ modes, UnitAddTorus.mFourier q x • A q

theorem matrixReconstruction_apply (modes : Finset Wavevector)
    (A : FourierMatrix) (x : T3) (i j : Fin 3) :
    matrixReconstruction modes A x i j =
      ∑ q ∈ modes, UnitAddTorus.mFourier q x * A q i j := by
  simp [matrixReconstruction, Matrix.sum_apply, Matrix.smul_apply]

theorem matrixReconstruction_real (modes : Finset Wavevector) (A : FourierMatrix)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hA : ∀ q i j, A (-q) i j = conj (A q i j)) (x : T3) (i j : Fin 3) :
    (matrixReconstruction modes A x i j).im = 0 := by
  have h := finiteFourierReconstruction_im_eq_zero_of_neg_closed modes
    (fun q i ↦ A q i j) hs (fun q ↦ funext (fun i ↦ hA q i j)) x i
  simpa only [matrixReconstruction_apply, finiteFourierReconstruction,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

theorem gradientCoeff_conjugate (u : FourierVelocity)
    (hu : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) (i j : Fin 3) :
    gradientCoeff u (-q) i j = conj (gradientCoeff u q i j) := by
  simp [gradientCoeff, hu, coefficientConjugate, unitTorusDerivativePhase, map_ofNat]

theorem strainCoeff_conjugate (u : FourierVelocity)
    (hu : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) (i j : Fin 3) :
    strainCoeff u (-q) i j = conj (strainCoeff u q i j) := by
  simp [strainCoeff, Matrix.transpose_apply, gradientCoeff_conjugate u hu, map_ofNat]

theorem spinCoeff_conjugate (u : FourierVelocity)
    (hu : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) (i j : Fin 3) :
    spinCoeff u (-q) i j = conj (spinCoeff u q i j) := by
  simp [spinCoeff, Matrix.transpose_apply, gradientCoeff_conjugate u hu, map_ofNat]

def realMatrix (A : MatrixCoefficient) : Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦ (A i j).re

def realMatrixOperator (A : MatrixCoefficient) : R3 →L[ℝ] R3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (realMatrix A)

theorem realMatrixOperator_apply (A : MatrixCoefficient) (v : R3) (i : Fin 3) :
    realMatrixOperator A v i = ∑ j, (A i j).re * v j := rfl

def realMatrixOperatorLinear : MatrixCoefficient →ₗ[ℝ] (R3 →L[ℝ] R3) where
  toFun := realMatrixOperator
  map_add' A B := by
    ext v i
    simp [realMatrixOperator_apply, Matrix.add_apply, Complex.add_re,
      add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext v i
    simp [realMatrixOperator_apply, Matrix.smul_apply, Finset.mul_sum, mul_assoc]

def realMatrixOperatorCLM : MatrixCoefficient →L[ℝ] (R3 →L[ℝ] R3) :=
  realMatrixOperatorLinear.toContinuousLinearMap

@[simp] theorem realMatrixOperatorCLM_apply (A : MatrixCoefficient) :
    realMatrixOperatorCLM A = realMatrixOperator A := rfl

theorem realMatrixOperator_add (A B : MatrixCoefficient) :
    realMatrixOperator (A + B) = realMatrixOperator A + realMatrixOperator B :=
  realMatrixOperatorLinear.map_add A B

theorem realMatrixOperator_sub (A B : MatrixCoefficient) :
    realMatrixOperator (A - B) = realMatrixOperator A - realMatrixOperator B :=
  realMatrixOperatorLinear.map_sub A B

theorem realMatrixOperator_neg (A : MatrixCoefficient) :
    realMatrixOperator (-A) = -realMatrixOperator A := realMatrixOperatorLinear.map_neg A

/-- Products of reconstructed real matrices become products of the actual
real spatial operators. No multiplicativity of real part is presumed. -/
theorem realMatrixOperator_mul (A B : MatrixCoefficient)
    (hA : ∀ i j, (A i j).im = 0) :
    realMatrixOperator (A * B) = realMatrixOperator A * realMatrixOperator B := by
  have hr : realMatrix (A * B) = realMatrix A * realMatrix B := by
    ext i j
    simp [realMatrix, Matrix.mul_apply, Complex.re_sum, Complex.mul_re, hA]
  change Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (realMatrix (A * B)) = _
  rw [hr, map_mul]
  rfl

theorem realMatrixOperator_symmetric (A : MatrixCoefficient) (hA : A.transpose = A) :
    ∀ v w : R3, ⟪v, realMatrixOperator A w⟫ = ⟪realMatrixOperator A v, w⟫ := by
  have hh : (realMatrix A).IsHermitian := by
    ext i j
    exact congrArg Complex.re (congrFun (congrFun hA i) j)
  intro v w
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hh v w).symm

theorem hasDerivAt_realMatrixOperator (A : ℝ → MatrixCoefficient)
    (dA : MatrixCoefficient) (t : ℝ) (hA : HasDerivAt A dA t) :
    HasDerivAt (fun tau ↦ realMatrixOperator (A tau)) (realMatrixOperator dA) t :=
  realMatrixOperatorCLM.hasFDerivAt.comp_hasDerivAt t hA

theorem matrixReconstruction_transpose (modes : Finset Wavevector) (A : FourierMatrix)
    (x : T3) :
    (matrixReconstruction modes A x).transpose =
      matrixReconstruction modes (fun q ↦ (A q).transpose) x := by
  simp [matrixReconstruction, Matrix.transpose_sum]

theorem matrixReconstruction_strain_symmetric (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    (matrixReconstruction modes (strainCoeff u) x).transpose =
      matrixReconstruction modes (strainCoeff u) x := by
  rw [matrixReconstruction_transpose]
  simp only [strainCoeff_transpose]

def spatialStrain (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    PancakeSpectralProjectorRegularity.SymmetricStrain :=
  ⟨realMatrixOperator (matrixReconstruction modes (strainCoeff u) x),
    realMatrixOperator_symmetric _ (matrixReconstruction_strain_symmetric modes u x)⟩

def spatialSpin (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction modes (spinCoeff u) x)

theorem hasDerivAt_matrixReconstruction_moving
    (modes : Finset Wavevector) (A : ℝ → FourierMatrix) (dA : FourierMatrix)
    (X : ℝ → Fin 3 → ℝ) (v : Fin 3 → ℝ) (t : ℝ)
    (hA : ∀ q ∈ modes, ∀ i j, HasDerivAt (fun tau ↦ A tau q i j) (dA q i j) t)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i) (v i) t) :
    HasDerivAt (fun tau ↦ matrixReconstruction modes (A tau) (torusPoint (X tau)))
      (matrixReconstruction modes (fun q ↦ dA q +
        (unitTorusDerivativePhase * (realModeDot q v : ℂ)) • A t q) (torusPoint (X t))) t := by
  change HasDerivAt (fun tau i j ↦ matrixReconstruction modes (A tau) (torusPoint (X tau)) i j)
    (fun i j ↦ matrixReconstruction modes (fun q ↦ dA q +
      (unitTorusDerivativePhase * (realModeDot q v : ℂ)) • A t q) (torusPoint (X t)) i j) t
  refine hasDerivAt_pi.mpr (fun i ↦ hasDerivAt_pi.mpr (fun j ↦ ?_))
  simp only [matrixReconstruction_apply]
  have hh := HasDerivAt.fun_sum (u := modes) (fun q hq ↦
    (hasDerivAt_mFourier_torusPoint q X v t hX).mul (hA q hq i j))
  apply hh.congr_deriv
  apply Finset.sum_congr rfl
  intro q _
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- The reconstructed Fourier gradient is the directional derivative of
the actual real velocity field along every differentiable real path. -/
theorem hasDerivAt_reconstructedVelocity_along_realPath
    (modes : Finset Wavevector) (u : FourierVelocity)
    (X : ℝ → Fin 3 → ℝ) (v : Fin 3 → ℝ) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i) (v i) t) :
    HasDerivAt (fun tau ↦ PancakeDyadicDirectionEvolution.realFiniteFourierReconstruction
      modes u (torusPoint (X tau)))
      (realMatrixOperator (matrixReconstruction modes (gradientCoeff u) (torusPoint (X t)))
        (WithLp.toLp 2 v)) t := by
  let x := torusPoint (X t)
  let phase := fun q ↦ unitTorusDerivativePhase * (realModeDot q v : ℂ) * UnitAddTorus.mFourier q x
  have h := PancakeMovingBlockEvolution.hasDerivAt_real_moving_finiteFourierReconstruction
    modes (fun _ ↦ u) 0 (fun tau ↦ torusPoint (X tau)) phase t
    (fun q _ i ↦ hasDerivAt_const t (u q i))
    (fun q _ ↦ hasDerivAt_mFourier_torusPoint q X v t hX)
  have he : PancakeMovingBlockEvolution.movingFiniteFourierDerivative modes u 0 phase x =
      fun i ↦ ∑ j, matrixReconstruction modes (gradientCoeff u) x i j * (v j : ℂ) := by
    ext i
    simp only [PancakeMovingBlockEvolution.movingFiniteFourierDerivative, phase,
      Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      mul_zero, add_zero, matrixReconstruction_apply, gradientCoeff,
      realModeDot, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro q _
    ring
  apply h.congr_deriv
  rw [he]
  ext i
  change (∑ j, matrixReconstruction modes (gradientCoeff u) x i j * (v j : ℂ)).re = _
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, realMatrixOperator_apply]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.PancakeFourierMaterialPaths
