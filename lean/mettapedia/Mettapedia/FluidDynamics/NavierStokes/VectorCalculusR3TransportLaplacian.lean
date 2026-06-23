import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives

/-!
# Vector Calculus R3: Transport Laplacian

This module contains scalar and vector Laplacian identities for transported
heat-shear fields and their full-drift variants.
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

/-- The scalar Laplacian of the transported heat-shear profile is the expected
one-dimensional second derivative in the `x₁` direction. -/
theorem laplacian_heatShearTransportScalar
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    Δ (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x =
      -(k ^ (2 : ℕ)) *
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * (s - b * t))
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id.sub contDiff_const).const_smul k)).const_smul A
  have hlapx :
      Δ (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x =
        ∑ i : Fin 3,
          (iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x)
            ![(EuclideanSpace.basisFun (Fin 3) ℝ) i, (EuclideanSpace.basisFun (Fin 3) ℝ) i] := by
    simpa using congrArg (fun h : NSSpace → ℝ => h x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f := fun y : NSSpace => heatShearTransportScalar ν a k b t y)
        (v := EuclideanSpace.basisFun (Fin 3) ℝ))
  rw [hlapx]
  rw [Fin.sum_univ_three]
  have hcoord :
      iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x =
        (iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
          (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) := by
    simpa [heatShearTransportScalar, g, A, Function.comp, mul_assoc] using
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
  have hshift :
      iteratedDeriv 2 (fun z : ℝ => Real.sin (k * (z - b * t))) (x nsCoord1) =
        iteratedDeriv 2 (fun z : ℝ => Real.sin (k * z)) (x nsCoord1 - b * t) := by
    simpa using congrArg (fun h : ℝ → ℝ => h (x nsCoord1))
      (iteratedDeriv_comp_sub_const (n := 2) (f := fun z : ℝ => Real.sin (k * z)) (s := b * t))
  have hsinBase :
      iteratedDeriv 2 Real.sin (k * (x nsCoord1 - b * t)) =
        -Real.sin (k * (x nsCoord1 - b * t)) := by
    have hs := congrArg (fun h : ℝ → ℝ => h (k * (x nsCoord1 - b * t)))
      (Real.iteratedDeriv_even_sin (n := 1))
    rw [pow_one, neg_one_mul] at hs
    exact hs
  have hsin2 :
      iteratedDeriv 2 (fun z : ℝ => Real.sin (k * z)) (x nsCoord1 - b * t) =
        -(k ^ (2 : ℕ)) * Real.sin (k * (x nsCoord1 - b * t)) := by
    have hcomp := congrArg (fun h : ℝ → ℝ => h (x nsCoord1 - b * t))
      (iteratedDeriv_comp_const_mul (n := 2) (f := Real.sin) Real.contDiff_sin k)
    have hcomp' :
        iteratedDeriv 2 (fun z : ℝ => Real.sin (k * z)) (x nsCoord1 - b * t) =
          k ^ (2 : ℕ) * iteratedDeriv 2 Real.sin (k * (x nsCoord1 - b * t)) := by
      simpa using hcomp
    rw [hsinBase] at hcomp'
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcomp'
  have hsecond :
      iteratedDeriv 2 g (x nsCoord1) =
        -(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) := by
    have hconst :
        iteratedDeriv 2 g (x nsCoord1) =
          A * iteratedDeriv 2 (fun z : ℝ => Real.sin (k * (z - b * t))) (x nsCoord1) := by
      simp [g, iteratedDeriv_const_mul_field]
    rw [hconst, hshift, hsin2]
    ring
  rw [hz0, h1eval, hz2, hsecond]
  simp

/-- The transported heat-shear velocity field has the expected advection-heat
Laplacian in the first velocity component. -/
theorem spatialLaplacian_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * (s - b * t))
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id.sub contDiff_const).const_smul k)).const_smul A
  have hscalar : ContDiffAt ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x := by
    have hcont : ContDiff ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) := by
      simpa [heatShearTransportScalar, g, A, Function.comp, mul_assoc] using
        hg.comp ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff)
    exact hcont.contDiffAt
  have hosc : ContDiffAt ℝ 2
      (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) x := by
    have hcont : ContDiff ℝ 2
        (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) := by
      simpa [heatShearTransportScalar, g, A, Function.comp, mul_assoc] using
        coord0Embedding.contDiff.comp
          (hg.comp ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff))
    exact hcont.contDiffAt
  have hcore :
      spatialLaplacian (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))) := by
    unfold spatialLaplacian
    rw [show (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) =
        coord0Embedding ∘ fun y : NSSpace => heatShearTransportScalar ν a k b t y by
        funext y
        rfl]
    rw [hscalar.laplacian_CLM_comp_left (l := coord0Embedding)]
    simp [laplacian_heatShearTransportScalar]
  rw [heatShearTransportVelocityField]
  rw [spatialLaplacian_add]
  · simp [hcore, spatialLaplacian_constantVelocityField]
  · exact hosc.of_le (by
      exact (show (2 : WithTop ℕ∞) ≤ 2 from le_rfl))
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The spatial Laplacian of transported arbitrary-amplitude shear is the
transported sine-mode Laplacian with sampled amplitude `A t`. -/
theorem spatialLaplacian_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (A t * Real.sin (k * (x nsCoord1 - b * t)))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialLaplacian_congr_at hslice]
  simpa [heatShearTransportScalar]
    using spatialLaplacian_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported full-drift heat-shear family has the same spatial
Laplacian as the transported branch without the additional constant drifts. -/
theorem spatialLaplacian_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearTransportVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
