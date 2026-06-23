import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions

/-!
# Vector Calculus R3: Laplacian

Concrete Laplacian identities for linear and heat-shear velocity fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped Gradient
open scoped Laplacian
open scoped BigOperators
open scoped ContDiff

section VectorCalculusR3

/-- The spatial Laplacian commutes with addition on twice continuously
differentiable slices. -/
theorem spatialLaplacian_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : ContDiffAt ℝ 2 (fun y : NSSpace => u t y) x)
    (hv : ContDiffAt ℝ 2 (fun y : NSSpace => v t y) x) :
    spatialLaplacian (u + v) t x =
      spatialLaplacian u t x + spatialLaplacian v t x := by
  unfold spatialLaplacian
  change Δ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x = _
  simpa using hu.laplacian_add hv

/-- The spatial Laplacian commutes with constant scalar multiplication on twice
continuously differentiable slices. -/
theorem spatialLaplacian_const_smul
    (a : ℝ) {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : ContDiffAt ℝ 2 (fun y : NSSpace => u t y) x) :
    spatialLaplacian (a • u) t x = a • spatialLaplacian u t x := by
  unfold spatialLaplacian
  change Δ (a • fun y : NSSpace => u t y) x = a • Δ (fun y : NSSpace => u t y) x
  simpa using InnerProductSpace.laplacian_smul a hu

/-- The spatial Laplacian of a constant velocity field is zero. -/
theorem spatialLaplacian_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (constantVelocityField c) t x = 0 := by
  unfold spatialLaplacian constantVelocityField
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := NSSpace) (F := NSSpace) (n := 2)
    (by simp) c]
  simp

/-- Any continuous linear map on `ℝ^3` has zero Laplacian. -/
theorem laplacian_continuousLinearMap_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : NSSpace →L[ℝ] F) (x : NSSpace) :
    Δ (fun y : NSSpace => l y) x = 0 := by
  let m : NSSpace →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => NSSpace) F) :=
    ((continuousMultilinearCurryFin0 ℝ NSSpace F).symm : F ≃L[ℝ] _).toContinuousLinearMap.comp l
  have h1 : iteratedFDeriv ℝ 1 (fun y : NSSpace => l y) = fun _ =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => NSSpace) F).symm m := by
    funext z
    rw [iteratedFDeriv_succ_eq_comp_left]
    change ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => NSSpace) F).symm)
        (fderiv ℝ (((continuousMultilinearCurryFin0 ℝ NSSpace F).symm : F ≃L[ℝ] _) ∘
          fun y : NSSpace => l y) z) = _
    congr 1
    simpa [m] using m.fderiv (x := z)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [iteratedFDeriv_succ_eq_comp_left]
  simp [h1]

/-- The steady linear shear field has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearVelocityField a) t x = 0 := by
  simpa [spatialLaplacian, linearShearVelocityField, linearShearInitialVelocity] using
    (laplacian_continuousLinearMap_zero (F := NSSpace) (linearShearMap a) x)

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_linearShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearHorizontalDriftVelocityField a b) t x = 0 := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_linearShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The steady field `u(t,x) = (a * x₁, b, c)` has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearFullDriftVelocityField a b c) t x = 0 := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_linearShearHorizontalDriftVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The scalar Laplacian of the damped sinusoidal heat-shear profile is the
expected one-dimensional second derivative in the `x₁` direction. -/
theorem laplacian_heatShearScalar
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    Δ (fun y : NSSpace => heatShearScalar ν a k t y) x =
      -(k ^ (2 : ℕ)) *
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * s)
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id).const_smul k)).const_smul A
  have hlapx :
      Δ (fun y : NSSpace => heatShearScalar ν a k t y) x =
        ∑ i : Fin 3,
          (iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) x)
            ![(EuclideanSpace.basisFun (Fin 3) ℝ) i, (EuclideanSpace.basisFun (Fin 3) ℝ) i] := by
    simpa using congrArg (fun h : NSSpace → ℝ => h x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f := fun y : NSSpace => heatShearScalar ν a k t y)
        (v := EuclideanSpace.basisFun (Fin 3) ℝ))
  rw [hlapx]
  rw [Fin.sum_univ_three]
  have hcoord :
      iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) x =
        (iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
          (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) := by
    simpa [heatShearScalar, g, A, Function.comp, mul_assoc] using
      (ContinuousLinearMap.iteratedFDeriv_comp_right
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) hg x (i := 2) (by norm_num))
  rw [hcoord]
  have h0 :
      (fun i => (![(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (0 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = 0 := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have h1 :
      (fun i => (![(EuclideanSpace.single (1 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (1 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = fun _ => (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have h2 :
      (fun i => (![(EuclideanSpace.single (2 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = 0 := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have hz0 :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 0, (EuclideanSpace.basisFun (Fin 3) ℝ) 0] = 0 := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h0]
    simp
  have h1eval :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 1, (EuclideanSpace.basisFun (Fin 3) ℝ) 1] =
        iteratedDeriv 2 g (x nsCoord1) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h1]
    simp [iteratedDeriv_eq_iteratedFDeriv]
  have hz2 :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 2, (EuclideanSpace.basisFun (Fin 3) ℝ) 2] = 0 := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h2]
    simp
  rw [hz0, h1eval, hz2]
  simp [g, A, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul, Real.contDiff_sin]
  ring

/-- The damped sinusoidal heat-shear velocity field has the expected heat
Laplacian in the first velocity component. -/
theorem spatialLaplacian_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearVelocityField ν a k) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * s)
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id).const_smul k)).const_smul A
  have hscalar : ContDiffAt ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) x := by
    have hcont : ContDiff ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) := by
      simpa [heatShearScalar, g, A, Function.comp, mul_assoc] using
        hg.comp ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff)
    exact hcont.contDiffAt
  unfold spatialLaplacian
  rw [show (fun y : NSSpace => heatShearVelocityField ν a k t y) =
      coord0Embedding ∘ fun y : NSSpace => heatShearScalar ν a k t y by
      funext y
      rfl]
  rw [hscalar.laplacian_CLM_comp_left (l := coord0Embedding)]
  simp [laplacian_heatShearScalar]

/-- The spatial Laplacian of the general time-amplitude shear ansatz is the
same sine-mode Laplacian, with the sampled amplitude `A t`. -/
theorem spatialLaplacian_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (amplitudeShearVelocityField A k) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) * (A t * Real.sin (k * x nsCoord1))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialLaplacian_congr_at hslice]
  simpa [heatShearScalar]
    using spatialLaplacian_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift has the same spatial Laplacian
as pure heat shear. -/
theorem spatialLaplacian_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The heat-shear family with vertical drift has the same spatial Laplacian
as pure heat shear. -/
theorem spatialLaplacian_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearVerticalDriftVelocityField ν a k c) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The heat-shear family with full drift has the same spatial Laplacian as
pure heat shear. -/
theorem spatialLaplacian_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearFullDriftVelocityField ν a k d c) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearStreamwiseDriftVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
