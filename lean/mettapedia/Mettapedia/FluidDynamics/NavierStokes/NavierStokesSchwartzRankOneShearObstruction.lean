import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedStreamFunction
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum

/-!
# Rank-One Schwartz Shear Obstruction

This module rules out a tempting shortcut for the nonzero slice-Schwartz energy
canary.  A fixed-direction rank-one profile `u(x) = phi(x) v` cannot make its
Navier-Stokes convection term vanish pointwise unless the scalar Schwartz
profile itself is zero.

The proof uses the identity
`(u . grad) u = phi * D_v phi • v`; if this vanishes and `v` is nonzero, the
directional derivative of `phi^2` along `v` is zero.  Schwartz directional
rigidity then forces `phi^2`, and hence `phi`, to vanish.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff LineDeriv SchwartzMap

/-- Embed a scalar along a fixed spatial direction. -/
def rankOneEmbedding (v : NSSpace) : ℝ →L[ℝ] NSSpace :=
  (1 : ℝ →L[ℝ] ℝ).smulRight v

theorem rankOneEmbedding_apply (v : NSSpace) (r : ℝ) :
    rankOneEmbedding v r = r • v := by
  ext i
  simp [rankOneEmbedding]

/-- Rank-one Schwartz velocity profile `u(x) = phi(x) v`. -/
def rankOneSchwartzVelocity (φ : NSSchwartzScalar) (v : NSSpace) :
    NSSchwartzInitialVelocity :=
  φ.postcompCLM (rankOneEmbedding v)

theorem rankOneSchwartzVelocity_apply
    (φ : NSSchwartzScalar) (v x : NSSpace) :
    rankOneSchwartzVelocity φ v x = φ x • v := by
  simp [rankOneSchwartzVelocity, rankOneEmbedding_apply]

/-- Pointwise convection formula for rank-one Schwartz profiles. -/
theorem spatialConvection_timeIndependent_rankOneSchwartzVelocity
    (φ : NSSchwartzScalar) (v : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialConvection
        (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity)) t x =
      (φ x * fderiv ℝ (fun y : NSSpace => φ y) x v) • v := by
  unfold spatialConvection spatialFDeriv timeIndependentVelocity
  change
    fderiv ℝ ((rankOneEmbedding v) ∘ fun y : NSSpace => φ y) x
        (rankOneEmbedding v (φ x)) =
      (φ x * fderiv ℝ (fun y : NSSpace => φ y) x v) • v
  have hderiv :=
    congrArg (fun L : NSSpace →L[ℝ] NSSpace => L (rankOneEmbedding v (φ x)))
      (((rankOneEmbedding v).hasFDerivAt.comp x (φ.hasFDerivAt x)).fderiv)
  rw [hderiv]
  simp [ContinuousLinearMap.comp_apply, rankOneEmbedding_apply, smul_smul, mul_comm]

/-- The square of a scalar Schwartz profile, kept as a Schwartz map. -/
def schwartzSquare (φ : NSSchwartzScalar) : NSSchwartzScalar :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) φ.hasTemperateGrowth φ

theorem schwartzSquare_apply (φ : NSSchwartzScalar) (x : NSSpace) :
    schwartzSquare φ x = φ x * φ x := by
  simp [schwartzSquare, SchwartzMap.bilinLeftCLM_apply]

theorem fderiv_schwartzSquare_along
    (φ : NSSchwartzScalar) (x v : NSSpace) :
    fderiv ℝ (fun y : NSSpace => schwartzSquare φ y) x v =
      2 * φ x * fderiv ℝ (fun y : NSSpace => φ y) x v := by
  have hdiff : DifferentiableAt ℝ (fun y : NSSpace => φ y) x := φ.differentiableAt
  change fderiv ℝ ((fun y : NSSpace => φ y) * fun y : NSSpace => φ y) x v = _
  have hmul :=
    congrArg (fun L : NSSpace →L[ℝ] ℝ => L v) (fderiv_mul hdiff hdiff)
  calc
    fderiv ℝ ((fun y : NSSpace => φ y) * fun y : NSSpace => φ y) x v =
        φ x * fderiv ℝ (fun y : NSSpace => φ y) x v +
          φ x * fderiv ℝ (fun y : NSSpace => φ y) x v := by
      simpa [Pi.mul_apply] using hmul
    _ = 2 * φ x * fderiv ℝ (fun y : NSSpace => φ y) x v := by
      ring

/-- If a nonzero-direction rank-one Schwartz profile has zero convection at
one time, its scalar profile is zero. -/
theorem schwartzScalar_eq_zero_of_rankOne_spatialConvection_zero_at
    (φ : NSSchwartzScalar) {v : NSSpace} (hv : v ≠ 0) {t : NSTime}
    (hconv : ∀ x : NSSpace,
      spatialConvection
          (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity)) t x =
        0) :
    φ = 0 := by
  have hsquare_deriv_zero :
      ∀ x : NSSpace, fderiv ℝ (fun y : NSSpace => schwartzSquare φ y) x v = 0 := by
    intro x
    have hconvx := hconv x
    rw [spatialConvection_timeIndependent_rankOneSchwartzVelocity] at hconvx
    have hscalar : φ x * fderiv ℝ (fun y : NSSpace => φ y) x v = 0 := by
      exact (smul_eq_zero.mp hconvx).resolve_right hv
    rw [fderiv_schwartzSquare_along]
    nlinarith
  have hsquare_zero :
      schwartzSquare φ = 0 :=
    schwartzMap_eq_zero_of_fderiv_eq_zero_along (schwartzSquare φ) hv hsquare_deriv_zero
  ext x
  have hx :=
    congrArg (fun f : NSSchwartzScalar => f x) hsquare_zero
  rw [schwartzSquare_apply] at hx
  exact mul_self_eq_zero.mp hx

/-- Rank-one zero-convection Schwartz profiles along a nonzero direction are
the zero initial velocity. -/
theorem rankOneSchwartzVelocity_eq_zero_of_spatialConvection_zero_at
    (φ : NSSchwartzScalar) {v : NSSpace} (hv : v ≠ 0) {t : NSTime}
    (hconv : ∀ x : NSSpace,
      spatialConvection
          (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity)) t x =
        0) :
    (rankOneSchwartzVelocity φ v : NSInitialVelocity) = 0 := by
  have hφ := schwartzScalar_eq_zero_of_rankOne_spatialConvection_zero_at φ hv hconv
  funext x
  rw [rankOneSchwartzVelocity_apply, congrArg (fun f : NSSchwartzScalar => f x) hφ]
  simp

/-- There is no nonzero rank-one Schwartz initial velocity along a nonzero
direction whose time-independent convection term vanishes pointwise. -/
theorem not_exists_nonzero_rankOneSchwartzVelocity_with_zero_spatialConvection
    {v : NSSpace} (hv : v ≠ 0) {t : NSTime} :
    ¬ ∃ φ : NSSchwartzScalar,
      (rankOneSchwartzVelocity φ v : NSInitialVelocity) ≠ 0 ∧
        ∀ x : NSSpace,
          spatialConvection
              (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity))
              t x = 0 := by
  rintro ⟨φ, hnonzero, hconv⟩
  exact hnonzero (rankOneSchwartzVelocity_eq_zero_of_spatialConvection_zero_at φ hv hconv)

end NavierStokes
end FluidDynamics
end Mettapedia
