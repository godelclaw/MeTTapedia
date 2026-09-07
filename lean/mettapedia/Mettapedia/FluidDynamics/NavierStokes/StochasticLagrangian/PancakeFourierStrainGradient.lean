import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierMaterialPaths
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRegularizedDiffusion

/-!
# Actual spatial strain derivatives and a finite-cutoff energy envelope

The gradient below differentiates the reconstructed symmetric strain along
coordinate lines. Its bound is derived from the velocity coefficients.
The fourth frequency moment and the fixed finite-dimensional matrix-to-
operator bound remain explicit; no uniformity in the low cutoff is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFourierStrainGradient

open scoped BigOperators Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeFrequencyProjectorCommutator PancakeViscousMisalignmentAbsorption

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

def strainDerivativeCoeff (j : Fin 3) (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  (unitTorusDerivativePhase * (q j : ℂ)) • strainCoeff u q

def strainGradient (modes : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (j : Fin 3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction modes (strainDerivativeCoeff j u) x)

def coordinateLine (x : Fin 3 → ℝ) (j : Fin 3) (t : ℝ) : Fin 3 → ℝ :=
  fun i ↦ x i + t * if i = j then 1 else 0

theorem norm_realMatrixOperator_le (A : MatrixCoefficient) :
    ‖realMatrixOperator A‖ ≤ 9 * ‖A‖ := by
  apply (realMatrixOperator A).opNorm_le_bound (by positivity)
  intro v
  have hb : ∀ i, ‖realMatrixOperator A v i‖ ≤ 3 * ‖A‖ * ‖v‖ := by
    intro i
    rw [realMatrixOperator_apply]
    calc
      _ ≤ ∑ j : Fin 3, ‖(A i j).re * v j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖A‖ * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul ((show ‖(A i j).re‖ ≤ ‖A i j‖ from Complex.abs_re_le_norm _).trans
          (Matrix.norm_entry_le_entrywise_sup_norm A))
          (PiLp.norm_apply_le v j) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  have hs : (∑ i : Fin 3, ‖realMatrixOperator A v i‖ ^ 2) ≤
      3 * (3 * ‖A‖ * ‖v‖) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin 3, (3 * ‖A‖ * ‖v‖) ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hb i) 2)
      _ = _ := by simp
  rw [← EuclideanSpace.norm_sq_eq] at hs
  nlinarith [norm_nonneg (realMatrixOperator A v), mul_nonneg (norm_nonneg A) (norm_nonneg v)]

theorem hasDerivAt_strain_coordinateLine (modes : Finset Wavevector) (u : FourierVelocity)
    (x : Fin 3 → ℝ) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s ↦ (spatialStrain modes u (torusPoint (coordinateLine x j s))).1)
      (strainGradient modes u (torusPoint (coordinateLine x j t)) j) t := by
  have h := hasDerivAt_matrixReconstruction_moving modes (fun _ ↦ strainCoeff u) 0
    (coordinateLine x j) (fun i ↦ if i = j then 1 else 0) t
    (fun _ _ _ _ ↦ hasDerivAt_const _ _)
    (fun i ↦ by simpa only [coordinateLine, id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const (if i = j then 1 else 0)).const_add (x i))
  have heq : (fun q ↦ (0 : FourierMatrix) q +
      (unitTorusDerivativePhase * (realModeDot q (fun i ↦ if i = j then 1 else 0) : ℂ)) •
        strainCoeff u q) = strainDerivativeCoeff j u := by
    funext q
    simp [realModeDot, strainDerivativeCoeff]
  rw [heq] at h
  exact hasDerivAt_realMatrixOperator _ _ t h

theorem norm_gradientCoeff_le (u : FourierVelocity) (q : Wavevector) :
    ‖gradientCoeff u q‖ ≤
      ‖unitTorusDerivativePhase‖ * ‖frequencyVec q‖ * ‖coefficientVec (u q)‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  simp only [gradientCoeff, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_frequency_apply_le q j) (norm_nonneg _))
    (norm_coefficient_apply_le (u q) i) (norm_nonneg _) (by positivity)

theorem norm_strainCoeff_le (u : FourierVelocity) (q : Wavevector) :
    ‖strainCoeff u q‖ ≤
      ‖unitTorusDerivativePhase‖ * ‖frequencyVec q‖ * ‖coefficientVec (u q)‖ := by
  have h := norm_add_le (gradientCoeff u q) (gradientCoeff u q).transpose
  rw [Matrix.norm_transpose] at h
  unfold strainCoeff
  rw [norm_smul]
  norm_num
  nlinarith [norm_gradientCoeff_le u q]

theorem norm_strainDerivativeCoeff_le (j : Fin 3) (u : FourierVelocity) (q : Wavevector) :
    ‖strainDerivativeCoeff j u q‖ ≤
      ‖unitTorusDerivativePhase‖ ^ 2 * ‖frequencyVec q‖ ^ 2 * ‖coefficientVec (u q)‖ := by
  rw [strainDerivativeCoeff, norm_smul, norm_mul]
  calc
    _ ≤ (‖unitTorusDerivativePhase‖ * ‖frequencyVec q‖) *
      (‖unitTorusDerivativePhase‖ * ‖frequencyVec q‖ * ‖coefficientVec (u q)‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_frequency_apply_le q j) (norm_nonneg _))
          (norm_strainCoeff_le u q) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_matrixReconstruction_le (modes : Finset Wavevector) (A : FourierMatrix) (x : T3) :
    ‖matrixReconstruction modes A x‖ ≤ ∑ q ∈ modes, ‖A q‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_smul]
  have h := (UnitAddTorus.mFourier q).norm_coe_le_norm x
  rw [UnitAddTorus.mFourier_norm] at h
  nlinarith [norm_nonneg (A q)]

def strainGradientWeight (chi : Wavevector → ℂ) (q : Wavevector) : ℝ :=
  9 * ‖unitTorusDerivativePhase‖ ^ 2 * ‖chi q‖ * ‖frequencyVec q‖ ^ 2

def strainGradientAmplitude (outputs : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ :=
  ∑ q ∈ outputs, strainGradientWeight chi q * ‖coefficientVec (u q)‖

def strainGradientCutoffWeight (outputs : Finset Wavevector) (chi : Wavevector → ℂ) : ℝ :=
  3 * ∑ q ∈ outputs, strainGradientWeight chi q ^ 2

theorem strainGradientWeight_nonneg (chi : Wavevector → ℂ) (q : Wavevector) :
    0 ≤ strainGradientWeight chi q := by unfold strainGradientWeight; positivity

theorem strainGradientCutoffWeight_nonneg (outputs : Finset Wavevector) (chi : Wavevector → ℂ) :
    0 ≤ strainGradientCutoffWeight outputs chi := by unfold strainGradientCutoffWeight; positivity

theorem strainGradientCutoffWeight_fourth_moment (outputs : Finset Wavevector)
    (chi : Wavevector → ℂ) :
    strainGradientCutoffWeight outputs chi =
      243 * (2 * Real.pi) ^ 4 * ∑ q ∈ outputs, ‖chi q‖ ^ 2 * ‖frequencyVec q‖ ^ 4 := by
  have hp : ‖unitTorusDerivativePhase‖ = 2 * Real.pi := by
    simp [unitTorusDerivativePhase, Real.pi_pos.le]
  simp only [strainGradientCutoffWeight, strainGradientWeight, hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem norm_coefficientVec_filtered (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) :
    ‖coefficientVec (filteredVelocity chi u q)‖ = ‖chi q‖ * ‖coefficientVec (u q)‖ := by
  change ‖chi q • coefficientVec (u q)‖ = _
  rw [norm_smul]

theorem norm_strainGradient_le_amplitude (outputs : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) (j : Fin 3) :
    ‖strainGradient outputs (filteredVelocity chi u) x j‖ ≤
      strainGradientAmplitude outputs chi u := by
  have h0 := norm_realMatrixOperator_le
    (matrixReconstruction outputs (strainDerivativeCoeff j (filteredVelocity chi u)) x)
  apply h0.trans
  calc
    _ ≤ 9 *
      (∑ q ∈ outputs, ‖strainDerivativeCoeff j (filteredVelocity chi u) q‖) := by
        gcongr
        exact norm_matrixReconstruction_le _ _ _
    _ ≤ 9 * (∑ q ∈ outputs,
      ‖unitTorusDerivativePhase‖ ^ 2 * ‖frequencyVec q‖ ^ 2 *
        ‖coefficientVec (filteredVelocity chi u q)‖) := by
          gcongr with q hq
          exact norm_strainDerivativeCoeff_le j _ q
    _ = _ := by
      simp only [norm_coefficientVec_filtered, strainGradientAmplitude, strainGradientWeight,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

theorem strainGradientAmplitude_sq_le (outputs modes : Finset Wavevector)
    (chi : Wavevector → ℂ) (u : FourierVelocity) (hsub : outputs ⊆ modes) :
    strainGradientAmplitude outputs chi u ^ 2 ≤
      (∑ q ∈ outputs, strainGradientWeight chi q ^ 2) * fullEnergy modes u := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq outputs (strainGradientWeight chi)
    (fun q ↦ ‖coefficientVec (u q)‖)
  apply h.trans
  apply mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  simp only [norm_coefficientVec_sq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ ↦ by rw [← norm_coefficientVec_sq]; positivity)

theorem sum_norm_strainGradient_sq_le (outputs modes : Finset Wavevector)
    (chi : Wavevector → ℂ) (u : FourierVelocity) (x : T3) (hsub : outputs ⊆ modes) :
    (∑ j : Fin 3, ‖strainGradient outputs (filteredVelocity chi u) x j‖ ^ 2) ≤
      strainGradientCutoffWeight outputs chi * fullEnergy modes u := by
  calc
    _ ≤ ∑ _j : Fin 3, strainGradientAmplitude outputs chi u ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_strainGradient_le_amplitude outputs chi u x j) 2
    _ = 3 * strainGradientAmplitude outputs chi u ^ 2 := by simp
    _ ≤ _ := by
      have h := strainGradientAmplitude_sq_le outputs modes chi u hsub
      unfold strainGradientCutoffWeight
      nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeFourierStrainGradient
