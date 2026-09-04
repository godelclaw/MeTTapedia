import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFrozenFrameKernelTransfer

/-!
# Physical vector conjugation for frozen pancake frames

The frozen-frame kernel rotates frequency variables into the reference chart.
A physical frame change must also rotate both complex input amplitudes and
rotate the output back.  This module constructs the complexification of the
real oriented frame and records uniform coordinate-norm bounds for it and its
inverse.  These bounds are dimension-only and therefore cannot destroy the
square-dyadic `1/N` gain.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakePhysicalFrameKernelTransfer

open MeasureTheory
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakeFiniteFourierBilinearTransfer
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeSquareDyadicFiniteTransfer
open PeriodicFourierTriad
open scoped BigOperators

/-- Standard coordinate vector in the algebraic real three-vector model. -/
def realCoordinateBasis (j : Fin 3) : RealVec3 :=
  match j with
  | 0 => ex
  | 1 => ey
  | 2 => ez

@[simp]
theorem coordinate_realCoordinateBasis (i j : Fin 3) :
    coordinate (realCoordinateBasis j) i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [realCoordinateBasis, coordinate, ex, ey, ez]

/-- Complexify a real linear equivalence by using its matrix in the standard
coordinate basis. -/
def complexifyRealLinearEquiv
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) : ComplexVec3 →ₗ[ℂ] ComplexVec3 where
  toFun u := fun i ↦
    ∑ j : Fin 3, (coordinate (L (realCoordinateBasis j)) i : ℂ) * u j
  map_add' u v := by
    ext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem complexifyRealLinearEquiv_apply
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (u : ComplexVec3) (i : Fin 3) :
    complexifyRealLinearEquiv L u i =
      ∑ j : Fin 3, (coordinate (L (realCoordinateBasis j)) i : ℂ) * u j :=
  rfl

/-- Complexification agrees with the original map on real vectors. -/
theorem complexifyRealLinearEquiv_realVec3ToComplexVec3
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (w : RealVec3) :
    complexifyRealLinearEquiv L (realVec3ToComplexVec3 w) =
      realVec3ToComplexVec3 (L w) := by
  have hw : w =
      w.1 • ex + w.2.1 • ey + w.2.2 • ez := by
    ext <;> simp [ex, ey, ez]
  rw [hw, L.map_add, L.map_add, L.map_smul, L.map_smul, L.map_smul]
  ext i
  fin_cases i <;>
    simp [complexifyRealLinearEquiv, realVec3ToComplexVec3,
      realCoordinateBasis, coordinate, Fin.sum_univ_three,
      ex, ey, ez] <;>
    ring

/-- Matrix expansion of the complexified map in the standard real basis. -/
theorem complexifyRealLinearEquiv_eq_sum
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (u : ComplexVec3) :
    complexifyRealLinearEquiv L u =
      ∑ j : Fin 3, u j • realVec3ToComplexVec3 (L (realCoordinateBasis j)) := by
  ext i
  simp only [complexifyRealLinearEquiv_apply, Finset.sum_apply, Pi.smul_apply,
    realVec3ToComplexVec3_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Recombination of a complex vector from the complexified standard real
basis. -/
theorem sum_smul_realCoordinateBasis_eq (u : ComplexVec3) :
    (∑ j : Fin 3, u j • realVec3ToComplexVec3 (realCoordinateBasis j)) = u := by
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, realVec3ToComplexVec3,
      realCoordinateBasis, ex, ey, ez]

/-- Complexification respects inverse composition. -/
theorem complexifyRealLinearEquiv_symm_apply_apply
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (u : ComplexVec3) :
    complexifyRealLinearEquiv L.symm (complexifyRealLinearEquiv L u) = u := by
  rw [complexifyRealLinearEquiv_eq_sum L u, map_sum]
  simp_rw [map_smul,
    complexifyRealLinearEquiv_realVec3ToComplexVec3,
    LinearEquiv.symm_apply_apply]
  exact sum_smul_realCoordinateBasis_eq u

/-- Reverse inverse law for complexification. -/
theorem complexifyRealLinearEquiv_apply_symm_apply
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (u : ComplexVec3) :
    complexifyRealLinearEquiv L (complexifyRealLinearEquiv L.symm u) = u := by
  simpa using complexifyRealLinearEquiv_symm_apply_apply L.symm u

/-- Every coordinate of a dot-product-preserving real frame matrix has
absolute value at most one. -/
theorem abs_coordinate_linearEquiv_basis_le_one
    (L : RealVec3 ≃ₗ[ℝ] RealVec3)
    (hLdot : ∀ u v, dot (L u) (L v) = dot u v)
    (i j : Fin 3) :
    |coordinate (L (realCoordinateBasis j)) i| ≤ 1 := by
  have hnorm : normSq (L (realCoordinateBasis j)) = 1 := by
    rw [show normSq (L (realCoordinateBasis j)) =
        normSq (realCoordinateBasis j) from hLdot _ _]
    fin_cases j <;> norm_num [realCoordinateBasis, normSq, dot, ex, ey, ez]
  apply (sq_le_one_iff_abs_le_one _).mp
  unfold normSq dot at hnorm
  fin_cases i
  · change (L (realCoordinateBasis j)).1 ^ 2 ≤ 1
    nlinarith [sq_nonneg (L (realCoordinateBasis j)).2.1,
      sq_nonneg (L (realCoordinateBasis j)).2.2]
  · change (L (realCoordinateBasis j)).2.1 ^ 2 ≤ 1
    nlinarith [sq_nonneg (L (realCoordinateBasis j)).1,
      sq_nonneg (L (realCoordinateBasis j)).2.2]
  · change (L (realCoordinateBasis j)).2.2 ^ 2 ≤ 1
    nlinarith [sq_nonneg (L (realCoordinateBasis j)).1,
      sq_nonneg (L (realCoordinateBasis j)).2.1]

/-- In the coordinate sup norm, complexification of any orthogonal
three-frame costs at most the dimension constant three. -/
theorem norm_complexifyRealLinearEquiv_le
    (L : RealVec3 ≃ₗ[ℝ] RealVec3)
    (hLdot : ∀ u v, dot (L u) (L v) = dot u v)
    (u : ComplexVec3) :
    ‖complexifyRealLinearEquiv L u‖ ≤ 3 * ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg u))]
  intro i
  calc
    ‖complexifyRealLinearEquiv L u i‖ ≤
        ∑ j : Fin 3,
          ‖(coordinate (L (realCoordinateBasis j)) i : ℂ) * u j‖ :=
      by rw [complexifyRealLinearEquiv_apply]; exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖u‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      calc
        ‖(coordinate (L (realCoordinateBasis j)) i : ℂ)‖ * ‖u j‖ ≤
            1 * ‖u‖ := by
          gcongr
          · simpa [Complex.norm_real, Real.norm_eq_abs] using
              abs_coordinate_linearEquiv_basis_le_one L hLdot i j
          · exact norm_le_pi_norm u j
        _ = ‖u‖ := one_mul _
    _ = 3 * ‖u‖ := by simp

/-- The inverse of an oriented frame preserves the same Euclidean dot
product. -/
theorem orientedFrameRealLinearEquiv_symm_map_dot
    (F : OrientedFrameEquiv) (u v : RealVec3) :
    dot ((orientedFrameRealLinearEquiv F).symm u)
        ((orientedFrameRealLinearEquiv F).symm v) = dot u v := by
  calc
    dot ((orientedFrameRealLinearEquiv F).symm u)
        ((orientedFrameRealLinearEquiv F).symm v) =
        dot (F.toFun ((orientedFrameRealLinearEquiv F).symm u))
          (F.toFun ((orientedFrameRealLinearEquiv F).symm v)) :=
      (F.map_dot _ _).symm
    _ = dot u v := by
      change dot
          (orientedFrameRealLinearEquiv F
            ((orientedFrameRealLinearEquiv F).symm u))
          (orientedFrameRealLinearEquiv F
            ((orientedFrameRealLinearEquiv F).symm v)) = dot u v
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Complex forward coordinate change for an oriented physical frame. -/
def orientedFrameComplexLinearMap (F : OrientedFrameEquiv) :
    ComplexVec3 →ₗ[ℂ] ComplexVec3 :=
  complexifyRealLinearEquiv (orientedFrameRealLinearEquiv F)

/-- Complex inverse coordinate change for an oriented physical frame. -/
def orientedFrameInverseComplexLinearMap (F : OrientedFrameEquiv) :
    ComplexVec3 →ₗ[ℂ] ComplexVec3 :=
  complexifyRealLinearEquiv (orientedFrameRealLinearEquiv F).symm

@[simp]
theorem orientedFrameInverseComplexLinearMap_apply
    (F : OrientedFrameEquiv) (u : ComplexVec3) :
    orientedFrameInverseComplexLinearMap F
        (orientedFrameComplexLinearMap F u) = u :=
  complexifyRealLinearEquiv_symm_apply_apply
    (orientedFrameRealLinearEquiv F) u

@[simp]
theorem orientedFrameComplexLinearMap_inverse_apply
    (F : OrientedFrameEquiv) (u : ComplexVec3) :
    orientedFrameComplexLinearMap F
        (orientedFrameInverseComplexLinearMap F u) = u :=
  complexifyRealLinearEquiv_apply_symm_apply
    (orientedFrameRealLinearEquiv F) u

theorem norm_orientedFrameComplexLinearMap_le
    (F : OrientedFrameEquiv) (u : ComplexVec3) :
    ‖orientedFrameComplexLinearMap F u‖ ≤ 3 * ‖u‖ :=
  norm_complexifyRealLinearEquiv_le _ F.map_dot u

theorem norm_orientedFrameInverseComplexLinearMap_le
    (F : OrientedFrameEquiv) (u : ComplexVec3) :
    ‖orientedFrameInverseComplexLinearMap F u‖ ≤ 3 * ‖u‖ :=
  norm_complexifyRealLinearEquiv_le _
    (orientedFrameRealLinearEquiv_symm_map_dot F) u

/-! ## Physically conjugated square-dyadic action -/

/-- Apply the frozen-frame kernel in frame coordinates: rotate both inputs
into the frame, apply the frequency-rotated kernel, and rotate the output
back. -/
def physicalOrientedFrameSquareDyadicKernelAction
    (F : OrientedFrameEquiv) (N : ℕ)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (torusBilinearKernelAction
      (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
        (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
      (fun y ↦ orientedFrameComplexLinearMap F (f y))
      (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)

/-- Complex frame changes commute exactly with finite Fourier
reconstruction. -/
theorem orientedFrameComplexLinearMap_finiteFourierReconstruction
    (F : OrientedFrameEquiv) (s : Finset Wavevector)
    (omega : FourierVelocity) (x : BilinearSpatialTorus) :
    orientedFrameComplexLinearMap F
        (finiteFourierReconstruction s omega x) =
      finiteFourierReconstruction s
        (fun k ↦ orientedFrameComplexLinearMap F (omega k)) x := by
  simp [finiteFourierReconstruction, orientedFrameComplexLinearMap]

/-- Exact finite-Fourier formula after physical input/output frame
conjugation. -/
theorem physicalOrientedFrameSquareDyadicKernelAction_finiteFourierReconstruction_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalOrientedFrameSquareDyadicKernelAction F N
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ s, ∑ l ∈ t,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              localizedCoherentProjectedNormalizedStretch
                explicitBufferedStretchCutoff ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F (omega k))
                (orientedFrameComplexLinearMap F (eta l)))) := by
  unfold physicalOrientedFrameSquareDyadicKernelAction
  simp_rw [orientedFrameComplexLinearMap_finiteFourierReconstruction]
  rw [unitTorusPeriodizedOrientedFrameSquareDyadicNormalizedStretch_action_finiteFourierReconstruction_eq_coherent
    F hN]

/-- **Physically conjugated frozen-frame endpoint.**  Input and output frame
changes incur only the explicit dimension constant `3 * 9 * 3 * 3 = 243`;
the square-dyadic `C/N` gain is unchanged and remains independent of Fourier
support cardinality. -/
theorem exists_uniform_physicalOrientedFrameFiniteFourierSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖finiteFourierReconstruction s omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction t eta y‖ ≤ P) →
        ‖physicalOrientedFrameSquareDyadicKernelAction F N
            (finiteFourierReconstruction s omega)
            (finiteFourierReconstruction t eta) x‖ ≤
          243 * (C / N) * M * P := by
  rcases
      exists_uniform_orientedFrameFiniteFourierSquareDyadicStretch_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN s t omega eta x M P homega heta
  have hM : 0 ≤ M :=
    (norm_nonneg (finiteFourierReconstruction s omega x)).trans (homega x)
  have hP : 0 ≤ P :=
    (norm_nonneg (finiteFourierReconstruction t eta x)).trans (heta x)
  have homegaFrame : ∀ y,
      ‖finiteFourierReconstruction s
          (fun k ↦ orientedFrameComplexLinearMap F (omega k)) y‖ ≤ 3 * M := by
    intro y
    rw [← orientedFrameComplexLinearMap_finiteFourierReconstruction]
    exact (norm_orientedFrameComplexLinearMap_le F _).trans
      (mul_le_mul_of_nonneg_left (homega y) (by norm_num))
  have hetaFrame : ∀ y,
      ‖finiteFourierReconstruction t
          (fun k ↦ orientedFrameComplexLinearMap F (eta k)) y‖ ≤ 3 * P := by
    intro y
    rw [← orientedFrameComplexLinearMap_finiteFourierReconstruction]
    exact (norm_orientedFrameComplexLinearMap_le F _).trans
      (mul_le_mul_of_nonneg_left (heta y) (by norm_num))
  have hkernel := hbound F N hN s t
    (fun k ↦ orientedFrameComplexLinearMap F (omega k))
    (fun k ↦ orientedFrameComplexLinearMap F (eta k))
    x (3 * M) (3 * P) homegaFrame hetaFrame
  have homegaEq :
      (fun y ↦ orientedFrameComplexLinearMap F
        (finiteFourierReconstruction s omega y)) =
      finiteFourierReconstruction s
        (fun k ↦ orientedFrameComplexLinearMap F (omega k)) := by
    funext y
    exact orientedFrameComplexLinearMap_finiteFourierReconstruction F s omega y
  have hetaEq :
      (fun y ↦ orientedFrameComplexLinearMap F
        (finiteFourierReconstruction t eta y)) =
      finiteFourierReconstruction t
        (fun k ↦ orientedFrameComplexLinearMap F (eta k)) := by
    funext y
    exact orientedFrameComplexLinearMap_finiteFourierReconstruction F t eta y
  unfold physicalOrientedFrameSquareDyadicKernelAction
  calc
    ‖orientedFrameInverseComplexLinearMap F
        (torusBilinearKernelAction
          (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (fun y ↦ orientedFrameComplexLinearMap F
            (finiteFourierReconstruction s omega y))
          (fun y ↦ orientedFrameComplexLinearMap F
            (finiteFourierReconstruction t eta y)) x)‖ ≤
        3 * ‖torusBilinearKernelAction
          (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (fun y ↦ orientedFrameComplexLinearMap F
            (finiteFourierReconstruction s omega y))
          (fun y ↦ orientedFrameComplexLinearMap F
            (finiteFourierReconstruction t eta y)) x‖ :=
      norm_orientedFrameInverseComplexLinearMap_le F _
    _ = 3 * ‖torusBilinearKernelAction
          (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (finiteFourierReconstruction s
            (fun k ↦ orientedFrameComplexLinearMap F (omega k)))
          (finiteFourierReconstruction t
            (fun k ↦ orientedFrameComplexLinearMap F (eta k))) x‖ := by
      rw [homegaEq, hetaEq]
    _ ≤ 3 * (9 * (C / N) * (3 * M) * (3 * P)) := by
      gcongr
    _ = 243 * (C / N) * M * P := by ring

/-- The physically conjugated endpoint for arbitrary continuous bounded
fields.  Finite Fourier support is needed for the exact multiplier identity,
but not for the kernel estimate itself. -/
theorem exists_uniform_physicalOrientedFrameSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖physicalOrientedFrameSquareDyadicKernelAction F N f g x‖ ≤
          243 * (C / N) * M * P := by
  rcases
      exists_uniform_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel_integral_norm with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN f g x M P hf hg hfb hgb
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hP : 0 ≤ P := (norm_nonneg (g x)).trans (hgb x)
  let K :=
    unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N
  have hKmass := hmass
    (orientedFrameFrequencyPairLinearIsometryEquiv F) N hN
  have hfFrame : Continuous (fun y ↦ orientedFrameComplexLinearMap F (f y)) :=
    (orientedFrameComplexLinearMap F).continuous_of_finiteDimensional.comp hf
  have hgFrame : Continuous (fun y ↦ orientedFrameComplexLinearMap F (g y)) :=
    (orientedFrameComplexLinearMap F).continuous_of_finiteDimensional.comp hg
  have hfbFrame : ∀ y,
      ‖orientedFrameComplexLinearMap F (f y)‖ ≤ 3 * M := by
    intro y
    exact (norm_orientedFrameComplexLinearMap_le F _).trans
      (mul_le_mul_of_nonneg_left (hfb y) (by norm_num))
  have hgbFrame : ∀ y,
      ‖orientedFrameComplexLinearMap F (g y)‖ ≤ 3 * P := by
    intro y
    exact (norm_orientedFrameComplexLinearMap_le F _).trans
      (mul_le_mul_of_nonneg_left (hgb y) (by norm_num))
  have hyoung := norm_torusBilinearKernelAction_le K
    (fun y ↦ orientedFrameComplexLinearMap F (f y))
    (fun y ↦ orientedFrameComplexLinearMap F (g y)) x
    (3 * M) (3 * P) hKmass.1
    (measurable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
    hfFrame hgFrame hfbFrame hgbFrame
  unfold physicalOrientedFrameSquareDyadicKernelAction
  change ‖orientedFrameInverseComplexLinearMap F
      (torusBilinearKernelAction K
        (fun y ↦ orientedFrameComplexLinearMap F (f y))
        (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)‖ ≤ _
  calc
    ‖orientedFrameInverseComplexLinearMap F
        (torusBilinearKernelAction K
          (fun y ↦ orientedFrameComplexLinearMap F (f y))
          (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)‖ ≤
        3 * ‖torusBilinearKernelAction K
          (fun y ↦ orientedFrameComplexLinearMap F (f y))
          (fun y ↦ orientedFrameComplexLinearMap F (g y)) x‖ :=
      norm_orientedFrameInverseComplexLinearMap_le F _
    _ ≤ 3 *
        (9 * (∫ q : FrequencyPairUnitTorus, ‖K q‖
          ∂frequencyPairUnitTorusMeasure) * (3 * M) * (3 * P)) := by
      gcongr
    _ ≤ 3 * (9 * (C / N) * (3 * M) * (3 * P)) := by
      gcongr
      exact hKmass.2
    _ = 243 * (C / N) * M * P := by ring

/-! ## Pointwise spatially varying frames -/

/-- Insert an arbitrary oriented frame field at the observation point.  No
spatial derivative of the frame enters this pointwise kernel action. -/
def variablePhysicalFrameSquareDyadicKernelAction
    (frame : BilinearSpatialTorus → OrientedFrameEquiv) (N : ℕ)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  physicalOrientedFrameSquareDyadicKernelAction (frame x) N f g x

/-- Exact coherent finite-Fourier identity for an arbitrary frame field,
pointwise at the observation point. -/
theorem variablePhysicalFrameSquareDyadicKernelAction_finiteFourierReconstruction_eq_coherent
    (frame : BilinearSpatialTorus → OrientedFrameEquiv)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    variablePhysicalFrameSquareDyadicKernelAction frame N
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      orientedFrameInverseComplexLinearMap (frame x)
        (∑ k ∈ s, ∑ l ∈ t,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              localizedCoherentProjectedNormalizedStretch
                explicitBufferedStretchCutoff ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv (frame x))
                  N k l)
                (orientedFrameComplexLinearMap (frame x) (omega k))
                (orientedFrameComplexLinearMap (frame x) (eta l)))) := by
  exact
    physicalOrientedFrameSquareDyadicKernelAction_finiteFourierReconstruction_eq_coherent
      (frame x) hN s t omega eta x

/-- **Variable-frame pointwise endpoint.**  Uniformity of the frozen kernel
family permits an arbitrary frame choice at every output point without a
frame-derivative or Fourier-cardinality loss. -/
theorem exists_uniform_variablePhysicalFrameFiniteFourierSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (frame : BilinearSpatialTorus → OrientedFrameEquiv)
        (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖finiteFourierReconstruction s omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction t eta y‖ ≤ P) →
        ‖variablePhysicalFrameSquareDyadicKernelAction frame N
            (finiteFourierReconstruction s omega)
            (finiteFourierReconstruction t eta) x‖ ≤
          243 * (C / N) * M * P := by
  rcases
      exists_uniform_physicalOrientedFrameFiniteFourierSquareDyadicStretch_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro frame N hN s t omega eta x M P homega heta
  exact hbound (frame x) N hN s t omega eta x M P homega heta

/-- The pointwise variable-frame endpoint for arbitrary continuous bounded
fields.  It follows by instantiating the frame-uniform frozen estimate at the
output point, so no regularity assumption on `frame` is required here. -/
theorem exists_uniform_variablePhysicalFrameSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (frame : BilinearSpatialTorus → OrientedFrameEquiv)
        (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖variablePhysicalFrameSquareDyadicKernelAction frame N f g x‖ ≤
          243 * (C / N) * M * P := by
  rcases
      exists_uniform_physicalOrientedFrameSquareDyadicStretch_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro frame N hN f g x M P hf hg hfb hgb
  exact hbound (frame x) N hN f g x M P hf hg hfb hgb

end PancakePhysicalFrameKernelTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
