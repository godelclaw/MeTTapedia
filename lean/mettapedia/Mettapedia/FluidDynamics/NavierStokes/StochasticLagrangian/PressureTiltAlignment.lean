import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltOrigin
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnisotropyDepletion

/-!
# Nonzero physical pressure action at perfect pointwise alignment

The pressure is determined by a real, transverse, mean-zero finite Fourier
velocity. Its action on the aligned vorticity direction is transverse and
nonzero. This tests pointwise closures only; it says nothing about blowup
or the availability of spatially nonlocal or time-integrated estimates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltAlignment

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open PressureTiltDatum PressureTiltOrigin
open PancakeFourierMaterialPaths PancakeInfinitePressureHessian PancakeInfiniteSpatialPressure
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution LocalLowDiffusionBudget
open PancakeStrainSpectralFrame PancakeAnisotropyDepletion

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def originStrain (epsilon : ℝ) : SymmetricStrain := spatialStrain modes (velocity epsilon) 0

def originPressure (epsilon : ℝ) : R3 →L[ℝ] R3 :=
  realMatrixOperator (spatialHessian (spatialPressure (velocity epsilon)) 0)

theorem strain_apply (epsilon : ℝ) (v : R3) :
    (originStrain epsilon).1 v =
      (2 * Real.pi) • (⟪diagonalDirection, v⟫ • diagonalDirection - v) := by
  change realMatrixOperator _ v = _
  rw [strain_matrix_origin]
  ext i
  fin_cases i <;>
    norm_num [realMatrixOperator_apply, diagonalDirection, PiLp.inner_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Fin.reduceFinMk] <;> ring!

theorem fullStrainOperator_origin (epsilon : ℝ) :
    LocalAlignmentForcing.fullStrainOperator (velocity epsilon) 0 = (originStrain epsilon).1 :=
  FourierFiniteSupport.fullStrainOperator_eq_spatialStrain modes (velocity epsilon)
    (velocity_eq_zero_of_not_mem epsilon) 0

theorem originStrain_eq (epsilon eta : ℝ) : originStrain epsilon = originStrain eta := by
  apply Subtype.ext
  ext v i
  simp only [strain_apply]

theorem diagonalDirection_norm_sq : ‖diagonalDirection‖ ^ 2 = 3 := by
  norm_num [EuclideanSpace.real_norm_sq_eq, diagonalDirection, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem strain_diagonalDirection (epsilon : ℝ) :
    (originStrain epsilon).1 diagonalDirection = (4 * Real.pi) • diagonalDirection := by
  rw [strain_apply, real_inner_self_eq_norm_sq, diagonalDirection_norm_sq]
  module

theorem strain_rayleigh_le (epsilon : ℝ) (v : R3) :
    ⟪v, (originStrain epsilon).1 v⟫ ≤ 4 * Real.pi * ‖v‖ ^ 2 := by
  rw [strain_apply]
  simp [diagonalDirection,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three]
  nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg (v 0 - v 1)),
    mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg (v 0 - v 2)),
    mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg (v 1 - v 2))]

theorem topEigenvalue_origin (epsilon : ℝ) : topEigenvalue (originStrain epsilon) = 4 * Real.pi := by
  apply le_antisymm
  · have h := strain_rayleigh_le epsilon (topVector (originStrain epsilon))
    simpa only [topVector_rayleigh, topVector_norm, one_pow, mul_one] using h
  · have h := PancakeSpectralClusterDichotomy.rayleigh_le_topEigenvalue_mul_norm_sq
      (originStrain epsilon).1 (originStrain epsilon).2 diagonalDirection
    change ⟪diagonalDirection, (originStrain epsilon).1 diagonalDirection⟫ ≤
      topEigenvalue (originStrain epsilon) * ‖diagonalDirection‖ ^ 2 at h
    rw [strain_diagonalDirection, real_inner_smul_right, real_inner_self_eq_norm_sq,
      diagonalDirection_norm_sq] at h
    linarith

theorem spectralResidual_origin (epsilon : ℝ) :
    spectralResidual (originStrain epsilon).1 (topEigenvalue (originStrain epsilon))
      (fullVorticity (velocity epsilon) 0) = 0 := by
  rw [fullVorticity_origin, topEigenvalue_origin]
  simp [spectralResidual, map_smul, strain_diagonalDirection]

theorem topSpectralDefect_origin (epsilon : ℝ) :
    topSpectralDefect (originStrain epsilon) (fullVorticity (velocity epsilon) 0) = 0 := by
  rw [topSpectralDefect, spectralDefect_eq_inner, spectralResidual_origin, inner_zero_right]

theorem pressure_diagonalDirection (epsilon : ℝ) :
    originPressure epsilon diagonalDirection =
      (48 * Real.pi ^ 2 * epsilon / 5) • (WithLp.toLp 2 ![1, -1, 0] : R3) := by
  unfold originPressure
  rw [pressureHessian_origin]
  ext i
  fin_cases i <;>
    norm_num [realMatrixOperator_apply, diagonalDirection, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, pow_two]

theorem pressure_diagonalDirection_perpendicular (epsilon : ℝ) :
    ⟪diagonalDirection, originPressure epsilon diagonalDirection⟫ = 0 := by
  rw [pressure_diagonalDirection]
  simp [diagonalDirection, PiLp.inner_apply, Fin.sum_univ_three]

theorem pressure_diagonalDirection_ne_zero (epsilon : ℝ) (he : epsilon ≠ 0) :
    originPressure epsilon diagonalDirection ≠ 0 := by
  rw [pressure_diagonalDirection]
  intro h
  have h0 := congrArg (fun v : R3 ↦ v 0) h
  norm_num at h0
  exact he h0

theorem topVector_diagonalDirection (epsilon : ℝ) :
    ⟪diagonalDirection, topVector (originStrain epsilon)⟫ • diagonalDirection =
      (3 : ℝ) • topVector (originStrain epsilon) := by
  let e := topVector (originStrain epsilon)
  have hh := (orderedEigenframe (originStrain epsilon).1
    (originStrain epsilon).2).apply_eigenbasis 0
  change (originStrain epsilon).1 e = topEigenvalue (originStrain epsilon) • e at hh
  rw [strain_apply, topEigenvalue_origin] at hh
  have hz : (2 * Real.pi) • (⟪diagonalDirection, e⟫ • diagonalDirection - (3 : ℝ) • e) = 0 := by
    calc
      _ = (2 * Real.pi) • (⟪diagonalDirection, e⟫ • diagonalDirection - e) -
          (4 * Real.pi) • e := by module
      _ = 0 := sub_eq_zero.mpr hh
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by positivity))

theorem inner_diagonalDirection_topVector_ne_zero (epsilon : ℝ) :
    ⟪diagonalDirection, topVector (originStrain epsilon)⟫ ≠ 0 := by
  intro h
  have hh := topVector_diagonalDirection epsilon
  rw [h, zero_smul] at hh
  have he : topVector (originStrain epsilon) = 0 :=
    (smul_eq_zero.mp hh.symm).resolve_left (by norm_num)
  have hn := topVector_norm (originStrain epsilon)
  rw [he, norm_zero] at hn
  norm_num at hn

theorem topVector_eq_smul_diagonalDirection (epsilon : ℝ) :
    topVector (originStrain epsilon) =
      (⟪diagonalDirection, topVector (originStrain epsilon)⟫ / 3) • diagonalDirection := by
  have hh := congrArg (fun v : R3 ↦ (1 / 3 : ℝ) • v) (topVector_diagonalDirection epsilon)
  convert hh.symm using 1 <;> module

theorem secondEigenvalue_origin (epsilon : ℝ) :
    secondEigenvalue (originStrain epsilon) = -2 * Real.pi := by
  let F := orderedEigenframe (originStrain epsilon).1 (originStrain epsilon).2
  have ho : ⟪topVector (originStrain epsilon), F.eigenbasis 1⟫ = 0 :=
    F.eigenbasis.inner_eq_zero (by decide)
  have hc := congrArg (fun v : R3 ↦ ⟪v, F.eigenbasis 1⟫) (topVector_diagonalDirection epsilon)
  simp only [real_inner_smul_left, ho, mul_zero] at hc
  have hd : ⟪diagonalDirection, F.eigenbasis 1⟫ = 0 :=
    (mul_eq_zero.mp hc).resolve_left (inner_diagonalDirection_topVector_ne_zero epsilon)
  have hh := F.apply_eigenbasis 1
  rw [strain_apply, hd, zero_smul, zero_sub, smul_neg] at hh
  have hi := congrArg (fun v : R3 ↦ ⟪F.eigenbasis 1, v⟫) hh
  simp only [inner_neg_right, real_inner_smul_right, F.eigenbasis.inner_eq_one, mul_one] at hi
  change F.eigenvalue 1 = -2 * Real.pi
  linarith

theorem topGap_origin (epsilon : ℝ) : topGap (originStrain epsilon) = 6 * Real.pi := by
  rw [topGap, topEigenvalue_origin, secondEigenvalue_origin]
  ring

theorem pressure_topVector_perpendicular (epsilon : ℝ) :
    ⟪topVector (originStrain epsilon), originPressure epsilon (topVector (originStrain epsilon))⟫ = 0 := by
  conv_lhs => rw [topVector_eq_smul_diagonalDirection epsilon]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right,
    pressure_diagonalDirection_perpendicular, mul_zero]

theorem pressureTilt_ne_zero (epsilon : ℝ) (he : epsilon ≠ 0) :
    lineRemainder (topVector (originStrain epsilon))
      (originPressure epsilon (topVector (originStrain epsilon))) ≠ 0 := by
  rw [lineRemainder, pressure_topVector_perpendicular, zero_smul, sub_zero]
  rw [topVector_eq_smul_diagonalDirection epsilon, map_smul]
  exact smul_ne_zero (div_ne_zero (inner_diagonalDirection_topVector_ne_zero epsilon) (by norm_num))
    (pressure_diagonalDirection_ne_zero epsilon he)

theorem inner_diagonalDirection_topVector_sq (epsilon : ℝ) :
    ⟪diagonalDirection, topVector (originStrain epsilon)⟫ ^ 2 = 3 := by
  have hh := congrArg (fun v : R3 ↦ ‖v‖ ^ 2) (topVector_diagonalDirection epsilon)
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, diagonalDirection_norm_sq,
    topVector_norm, mul_one] at hh
  nlinarith only [hh]

theorem norm_pressure_diagonalDirection_sq (epsilon : ℝ) :
    ‖originPressure epsilon diagonalDirection‖ ^ 2 =
      (4608 / 25 : ℝ) * Real.pi ^ 4 * epsilon ^ 2 := by
  rw [pressure_diagonalDirection, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

theorem norm_pressureTilt_sq (epsilon : ℝ) :
    ‖lineRemainder (topVector (originStrain epsilon))
      (originPressure epsilon (topVector (originStrain epsilon)))‖ ^ 2 =
      (1536 / 25 : ℝ) * Real.pi ^ 4 * epsilon ^ 2 := by
  rw [lineRemainder, pressure_topVector_perpendicular, zero_smul, sub_zero,
    topVector_eq_smul_diagonalDirection epsilon, map_smul,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow,
    inner_diagonalDirection_topVector_sq, norm_pressure_diagonalDirection_sq]
  ring

/-- No pointwise majorant vanishing at zero defect controls this pressure action. -/
theorem not_pressureTilt_le_of_defect (F : ℝ → ℝ) (hF : F 0 = 0) :
    ¬ ∀ epsilon : ℝ,
      ‖lineRemainder (topVector (originStrain epsilon))
        (originPressure epsilon (topVector (originStrain epsilon)))‖ ≤
      F (topSpectralDefect (originStrain epsilon) (fullVorticity (velocity epsilon) 0)) := by
  intro h
  have hh := h 1
  rw [topSpectralDefect_origin, hF, norm_le_zero_iff] at hh
  exact pressureTilt_ne_zero 1 (by norm_num) hh

/-- A positive top gap, perfect alignment, and nonzero physical pressure tilt coexist. -/
theorem positive_gap_zero_defect_nonzero_pressure (epsilon : ℝ) (he : epsilon ≠ 0) :
    0 < topGap (originStrain epsilon) ∧
      spectralResidual (originStrain epsilon).1 (topEigenvalue (originStrain epsilon))
        (fullVorticity (velocity epsilon) 0) = 0 ∧
      topSpectralDefect (originStrain epsilon) (fullVorticity (velocity epsilon) 0) = 0 ∧
      lineRemainder (topVector (originStrain epsilon))
        (originPressure epsilon (topVector (originStrain epsilon))) ≠ 0 := by
  refine ⟨?_, spectralResidual_origin epsilon, topSpectralDefect_origin epsilon,
    pressureTilt_ne_zero epsilon he⟩
  rw [topGap_origin]
  positivity

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltAlignment
