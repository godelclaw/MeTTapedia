import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergyAntiProfile
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDivergenceFreeData
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions

/-!
# Localized Schwartz Stream-Function Data

This module gives the nonzero Schwartz lane a concrete divergence-free seed.
Every scalar Schwartz stream function `phi` produces a Schwartz initial
velocity `(partial_1 phi, -partial_0 phi, 0)`, and the mixed-partial symmetry
proof shows that this velocity has zero initial divergence.  A compactly
supported scalar `x_1 * bump(x)` then gives an explicit nonzero inhabitant of
the manuscript-style divergence-free Schwartz input class.

This is initial-data infrastructure.  It does not claim an exact nonzero
Navier-Stokes evolution or a continuum/global regularity result.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff LineDeriv SchwartzMap

/-- Scalar Schwartz functions on the concrete Navier-Stokes space. -/
abbrev NSSchwartzScalar : Type := 𝓢(NSSpace, ℝ)

/-- Embed a scalar into one chosen coordinate of `R^3`. -/
def coordEmbedding (i : Fin 3) : ℝ →L[ℝ] NSSpace :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single i (1 : ℝ))

theorem coordEmbedding_apply (i : Fin 3) (r : ℝ) :
    coordEmbedding i r = EuclideanSpace.single i r := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [coordEmbedding]
  · simp [coordEmbedding, hji]

/-- Stream-function velocity `u = (partial_1 phi, -partial_0 phi, 0)`. -/
def streamFunctionVelocity (φ : NSSchwartzScalar) : NSSchwartzInitialVelocity :=
  (∂_{EuclideanSpace.single nsCoord1 (1 : ℝ)} φ).postcompCLM (coordEmbedding nsCoord0) -
    (∂_{EuclideanSpace.single nsCoord0 (1 : ℝ)} φ).postcompCLM (coordEmbedding nsCoord1)

theorem fderiv_postcomp_coordEmbedding_component
    (i j : Fin 3) (f : NSSchwartzScalar) (x v : NSSpace) :
    (fderiv ℝ (fun y : NSSpace => coordEmbedding i (f y)) x v) j =
      (EuclideanSpace.single i (fderiv ℝ (fun y : NSSpace => f y) x v)) j := by
  change
    (fderiv ℝ ((coordEmbedding i) ∘ fun y : NSSpace => f y) x v) j =
      (EuclideanSpace.single i (fderiv ℝ (fun y : NSSpace => f y) x v)) j
  have h :=
    congrArg (fun L : NSSpace →L[ℝ] NSSpace => L v)
      (((coordEmbedding i).hasFDerivAt.comp x (f.hasFDerivAt x)).fderiv)
  simpa [ContinuousLinearMap.comp_apply, coordEmbedding_apply] using
    congrArg (fun z : NSSpace => z j) h

theorem lineDeriv_fderiv_eq_second_fderiv
    (φ : NSSchwartzScalar) (x v w : NSSpace) :
    fderiv ℝ (fun y : NSSpace => (∂_{w} φ) y) x v =
      fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x v w := by
  have hfdiff : DifferentiableAt ℝ
      (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x := by
    exact (((φ.smooth ⊤).contDiffAt (x := x)).fderiv_right (m := 1)
      two_le_contDiff_infty).differentiableAt one_ne_zero
  have hfun :
      (fun y : NSSpace => (∂_{w} φ) y) =
        fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y w := by
    funext y
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h :
      fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y w) x =
        (ContinuousLinearMap.apply ℝ ℝ w).comp
          (fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x) := by
    change
      fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ w) ∘
          fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x =
        (ContinuousLinearMap.apply ℝ ℝ w).comp
          (fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x)
    have hraw :=
      fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ w).differentiableAt hfdiff
    rw [(ContinuousLinearMap.apply ℝ ℝ w).fderiv] at hraw
    exact hraw
  rw [hfun, h]
  rfl

/-- Stream-function Schwartz velocities are divergence-free. -/
theorem initialSpatialDivergence_streamFunctionVelocity
    (φ : NSSchwartzScalar) (x : NSSpace) :
    initialSpatialDivergence (streamFunctionVelocity φ : NSInitialVelocity) x = 0 := by
  let e0 : NSSpace := EuclideanSpace.single nsCoord0 (1 : ℝ)
  let e1 : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
  let e2 : NSSpace := EuclideanSpace.single nsCoord2 (1 : ℝ)
  let u0 : NSSchwartzInitialVelocity :=
    (∂_{e1} φ).postcompCLM (coordEmbedding nsCoord0)
  let u1 : NSSchwartzInitialVelocity :=
    (∂_{e0} φ).postcompCLM (coordEmbedding nsCoord1)
  have hu : (streamFunctionVelocity φ : NSInitialVelocity) =
      fun y : NSSpace => u0 y - u1 y := by
    funext y
    rfl
  have hu_diff : DifferentiableAt ℝ (fun y : NSSpace => u0 y) x := u0.differentiableAt
  have hv_diff : DifferentiableAt ℝ (fun y : NSSpace => u1 y) x := u1.differentiableAt
  have hsymm : IsSymmSndFDerivAt ℝ (fun z : NSSpace => φ z) x := by
    exact (((φ.smooth ⊤).contDiffAt (x := x)).isSymmSndFDerivAt
      minSmoothness_two_le_contDiff_infty)
  have h00 :
      (fderiv ℝ (fun y : NSSpace => u0 y) x e0) nsCoord0 =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x e0 e1 := by
    calc
      (fderiv ℝ (fun y : NSSpace => u0 y) x e0) nsCoord0 =
          fderiv ℝ (fun y : NSSpace => (∂_{e1} φ) y) x e0 := by
        simpa [u0, e0, e1, coordEmbedding_apply, nsCoord0] using
          (fderiv_postcomp_coordEmbedding_component nsCoord0 nsCoord0
            (∂_{e1} φ) x e0)
      _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x e0 e1 := by
        exact lineDeriv_fderiv_eq_second_fderiv φ x e0 e1
  have h11 :
      (fderiv ℝ (fun y : NSSpace => u1 y) x e1) nsCoord1 =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x e1 e0 := by
    calc
      (fderiv ℝ (fun y : NSSpace => u1 y) x e1) nsCoord1 =
          fderiv ℝ (fun y : NSSpace => (∂_{e0} φ) y) x e1 := by
        simpa [u1, e0, e1, coordEmbedding_apply, nsCoord1] using
          (fderiv_postcomp_coordEmbedding_component nsCoord1 nsCoord1
            (∂_{e0} φ) x e1)
      _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x e1 e0 := by
        exact lineDeriv_fderiv_eq_second_fderiv φ x e1 e0
  have h01 :
      (fderiv ℝ (fun y : NSSpace => u0 y) x e1) nsCoord1 = 0 := by
    simpa [u0, e1, coordEmbedding_apply, nsCoord0, nsCoord1] using
      (fderiv_postcomp_coordEmbedding_component nsCoord0 nsCoord1
        (∂_{e1} φ) x e1)
  have h10 :
      (fderiv ℝ (fun y : NSSpace => u1 y) x e0) nsCoord0 = 0 := by
    simpa [u1, e0, coordEmbedding_apply, nsCoord0, nsCoord1] using
      (fderiv_postcomp_coordEmbedding_component nsCoord1 nsCoord0
        (∂_{e0} φ) x e0)
  have h02 :
      (fderiv ℝ (fun y : NSSpace => u0 y) x e2) nsCoord2 = 0 := by
    simpa [u0, e2, coordEmbedding_apply, nsCoord0, nsCoord2] using
      (fderiv_postcomp_coordEmbedding_component nsCoord0 nsCoord2
        (∂_{e1} φ) x e2)
  have h12 :
      (fderiv ℝ (fun y : NSSpace => u1 y) x e2) nsCoord2 = 0 := by
    simpa [u1, e2, coordEmbedding_apply, nsCoord1, nsCoord2] using
      (fderiv_postcomp_coordEmbedding_component nsCoord1 nsCoord2
        (∂_{e0} φ) x e2)
  have hmixed :
      fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x e0 e1 =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => φ z) y) x e1 e0 :=
    hsymm.eq e0 e1
  have hsub :
      fderiv ℝ (fun y : NSSpace => u0 y - u1 y) x =
        fderiv ℝ (fun y : NSSpace => u0 y) x -
          fderiv ℝ (fun y : NSSpace => u1 y) x := by
    change fderiv ℝ ((fun y : NSSpace => u0 y) - fun y : NSSpace => u1 y) x = _
    exact fderiv_sub hu_diff hv_diff
  rw [initialSpatialDivergence, hu, hsub, Fin.sum_univ_three]
  simp only [sub_apply]
  dsimp [e0, e1, e2, nsCoord0, nsCoord1, nsCoord2] at h00 h11 h01 h10 h02 h12 hmixed ⊢
  rw [h00, h10, h01, h11, h02, h12, hmixed]
  ring

/-- Compactly supported scalar stream function `x_1 * bump(x)`. -/
def nsLocalizedStreamFunctionScalarFun : NSSpace → ℝ :=
  fun x => x nsCoord1 * nsUnitBumpScalar x

/-- The scalar stream function as a Schwartz map. -/
def nsLocalizedStreamFunction : NSSchwartzScalar :=
  (nsUnitBumpScalar.hasCompactSupport.mul_left :
      HasCompactSupport nsLocalizedStreamFunctionScalarFun).toSchwartzMap <| by
    change ContDiff ℝ ∞ (fun x : NSSpace => x nsCoord1 * nsUnitBumpScalar x)
    exact
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.mul
        nsUnitBumpScalar.contDiff)

theorem nsLocalizedStreamFunction_apply (x : NSSpace) :
    nsLocalizedStreamFunction x = x nsCoord1 * nsUnitBumpScalar x := by
  rfl

theorem nsLocalizedStreamFunction_fderiv_origin_e1 :
    fderiv ℝ (fun z : NSSpace => nsLocalizedStreamFunction z) (0 : NSSpace)
        (EuclideanSpace.single nsCoord1 (1 : ℝ)) = 1 := by
  let coord : NSSpace → ℝ := fun z => z nsCoord1
  have hcoord :
      DifferentiableAt ℝ coord (0 : NSSpace) := by
    exact (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).differentiableAt
  have hbump :
      DifferentiableAt ℝ (fun z : NSSpace => nsUnitBumpScalar z) (0 : NSSpace) := by
    have hbumpCont : ContDiff ℝ ∞ (fun z : NSSpace => nsUnitBumpScalar z) :=
      nsUnitBumpScalar.contDiff
    exact hbumpCont.differentiable (by simp) (0 : NSSpace)
  have hbump0 : nsUnitBumpScalar (0 : NSSpace) = 1 := by
    exact nsUnitBumpScalar.one_of_mem_closedBall
      (Metric.mem_closedBall_self nsUnitBumpScalar.rIn_pos.le)
  have hcoord_fderiv :
      fderiv ℝ coord (0 : NSSpace) =
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) := by
    simpa [coord] using
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).fderiv (x := (0 : NSSpace)))
  change (fderiv ℝ (coord * fun z : NSSpace => nsUnitBumpScalar z) (0 : NSSpace))
      (EuclideanSpace.single nsCoord1 (1 : ℝ)) = 1
  rw [fderiv_mul hcoord hbump]
  rw [hcoord_fderiv]
  simp [coord, hbump0, nsCoord1]

theorem nsLocalizedStreamFunction_fderiv_origin_e0 :
    fderiv ℝ (fun z : NSSpace => nsLocalizedStreamFunction z) (0 : NSSpace)
        (EuclideanSpace.single nsCoord0 (1 : ℝ)) = 0 := by
  let coord : NSSpace → ℝ := fun z => z nsCoord1
  have hcoord :
      DifferentiableAt ℝ coord (0 : NSSpace) := by
    exact (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).differentiableAt
  have hbump :
      DifferentiableAt ℝ (fun z : NSSpace => nsUnitBumpScalar z) (0 : NSSpace) := by
    have hbumpCont : ContDiff ℝ ∞ (fun z : NSSpace => nsUnitBumpScalar z) :=
      nsUnitBumpScalar.contDiff
    exact hbumpCont.differentiable (by simp) (0 : NSSpace)
  have hbump0 : nsUnitBumpScalar (0 : NSSpace) = 1 := by
    exact nsUnitBumpScalar.one_of_mem_closedBall
      (Metric.mem_closedBall_self nsUnitBumpScalar.rIn_pos.le)
  have hcoord_fderiv :
      fderiv ℝ coord (0 : NSSpace) =
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) := by
    simpa [coord] using
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).fderiv (x := (0 : NSSpace)))
  change (fderiv ℝ (coord * fun z : NSSpace => nsUnitBumpScalar z) (0 : NSSpace))
      (EuclideanSpace.single nsCoord0 (1 : ℝ)) = 0
  rw [fderiv_mul hcoord hbump]
  rw [hcoord_fderiv]
  simp [coord, hbump0, nsCoord0, nsCoord1]

theorem nsLocalizedStreamVelocity_value_origin :
    streamFunctionVelocity nsLocalizedStreamFunction (0 : NSSpace) =
      EuclideanSpace.single nsCoord0 (1 : ℝ) := by
  have h1 :
      (∂_{EuclideanSpace.single nsCoord1 (1 : ℝ)} nsLocalizedStreamFunction) (0 : NSSpace) =
        1 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact nsLocalizedStreamFunction_fderiv_origin_e1
  have h0 :
      (∂_{EuclideanSpace.single nsCoord0 (1 : ℝ)} nsLocalizedStreamFunction) (0 : NSSpace) =
        0 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact nsLocalizedStreamFunction_fderiv_origin_e0
  simp [streamFunctionVelocity, coordEmbedding_apply, h1, h0]

theorem nsLocalizedStreamVelocity_nonzero :
    ∃ x : NSSpace, streamFunctionVelocity nsLocalizedStreamFunction x ≠ 0 := by
  refine ⟨0, ?_⟩
  rw [nsLocalizedStreamVelocity_value_origin]
  intro hzero
  have hcoord :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 = 1 := by
    simp [nsCoord0]
  have : (0 : NSSpace) nsCoord0 = 1 := by
    rw [← hcoord, hzero]
  norm_num at this

/-- A concrete nonzero divergence-free Schwartz initial velocity. -/
def nsLocalizedStreamDivergenceFreeInitialVelocity :
    NSSchwartzDivergenceFreeInitialVelocity where
  val := streamFunctionVelocity nsLocalizedStreamFunction
  property := initialSpatialDivergence_streamFunctionVelocity nsLocalizedStreamFunction

theorem nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero :
    ∃ x : NSSpace, nsLocalizedStreamDivergenceFreeInitialVelocity.1 x ≠ 0 :=
  nsLocalizedStreamVelocity_nonzero

end NavierStokes
end FluidDynamics
end Mettapedia
