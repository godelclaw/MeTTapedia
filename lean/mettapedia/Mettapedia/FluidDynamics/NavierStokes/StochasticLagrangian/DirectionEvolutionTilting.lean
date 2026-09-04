import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MisalignmentRefinedPin
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Vorticity-direction evolution and the pressure-Hessian tilting gap

This module opens the dynamical stage of the direction-coherence repair of the
pancake pin.  It records two exact pieces of the mechanism, without claiming a
Navier--Stokes regularity estimate.

First, a nonzero vorticity vector decomposed as `omega = r * xi`, with `xi`
unit, changes direction only through the component of its forcing transverse
to `xi`.  The material vorticity equation therefore splits its direction rate
into transverse strain and transverse diffusion.  The same identity gives the
exact production law for the squared misalignment of two differentiable
direction paths.

Second, differentiating a strain eigenpair gives the eigenframe angular rate
as an off-diagonal torque divided by the corresponding eigenvalue gap.  The
anisotropic pressure Hessian contributes to that torque, but a bounded torque
alone gives no gap-free bound on tilting: the checked family with unit torque
and gap `1 / (C + 1)` defeats every proposed nonnegative constant `C`.

Consequently a pressure-Hessian attack on `MisalignmentStrainBudget` must also
control inverse strain-eigenvalue gaps (or prove a time-integrated cancellation
or residence-time estimate across near-degenerate intervals).  Pressure
Hessian size by itself is not the missing envelope.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace DirectionEvolutionTilting

open scoped RealInnerProductSpace

/-- Three-dimensional coordinate space used by the stochastic-Lagrangian
layer. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-! ## Exact vorticity-direction kinematics -/

/-- The component of `v` transverse to the proposed unit direction `xi`. -/
def transverseComponent (xi v : R3) : R3 :=
  v - ⟪xi, v⟫ • xi

/-- The direction rate carried by a forcing vector at vorticity magnitude
`r`.  For an actual decomposition `omega = r * xi`, this is `D_t xi`. -/
def vorticityDirectionRate (r : ℝ) (xi forcing : R3) : R3 :=
  r⁻¹ • transverseComponent xi forcing

/-- A transverse component is orthogonal to a unit direction. -/
theorem inner_transverseComponent_eq_zero {xi v : R3}
    (hunit : ⟪xi, xi⟫ = 1) :
    ⟪xi, transverseComponent xi v⟫ = 0 := by
  rw [transverseComponent, inner_sub_right, real_inner_smul_right, hunit]
  ring

/-- The direction rate is tangent to the unit sphere. -/
theorem inner_vorticityDirectionRate_eq_zero {r : ℝ} {xi forcing : R3}
    (hunit : ⟪xi, xi⟫ = 1) :
    ⟪xi, vorticityDirectionRate r xi forcing⟫ = 0 := by
  rw [vorticityDirectionRate, real_inner_smul_right,
    inner_transverseComponent_eq_zero hunit]
  simp

/-- If a forcing is decomposed into radial and tangent parts, the transverse
formula recovers the tangent direction rate exactly. -/
theorem vorticityDirectionRate_eq_of_radial_tangent_decomposition
    {r radialRate : ℝ} {xi eta forcing : R3}
    (hr : r ≠ 0) (hunit : ⟪xi, xi⟫ = 1)
    (htangent : ⟪xi, eta⟫ = 0)
    (hforcing : forcing = radialRate • xi + r • eta) :
    vorticityDirectionRate r xi forcing = eta := by
  have hnorm : ‖xi‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hunit]
  simp [vorticityDirectionRate, transverseComponent, hforcing,
    inner_add_right, inner_smul_right, hnorm, htangent, hr]

/-- The derivative of a unit-vector path is tangent to the unit sphere. -/
theorem inner_directionDerivative_eq_zero
    {xi : ℝ → R3} {eta : R3} {t : ℝ}
    (hxi : HasDerivAt xi eta t)
    (hunit : ∀ s, ⟪xi s, xi s⟫ = 1) :
    ⟪xi t, eta⟫ = 0 := by
  have hinner := hxi.inner ℝ hxi
  have hzero : HasDerivAt (fun s => ⟪xi s, xi s⟫) 0 t := by
    simpa only [hunit] using (hasDerivAt_const (x := t) (c := (1 : ℝ)))
  have hrate := hinner.unique hzero
  rw [real_inner_comm eta (xi t)] at hrate
  have heta : ⟪eta, xi t⟫ = 0 := by linarith
  calc
    ⟪xi t, eta⟫ = ⟪eta, xi t⟫ := real_inner_comm _ _
    _ = 0 := heta

/-- For a differentiable factorization `omega = r * xi` with unit `xi`, the
abstract transverse formula is the actual derivative of `xi`. -/
theorem vorticityDirectionRate_eq_deriv_of_factorization
    {omega : ℝ → R3} {r : ℝ → ℝ} {xi : ℝ → R3}
    {forcing eta : R3} {radialRate t : ℝ}
    (homega : HasDerivAt omega forcing t)
    (hr : HasDerivAt r radialRate t)
    (hxi : HasDerivAt xi eta t)
    (hfactor : omega = fun s => r s • xi s)
    (hunit : ∀ s, ⟪xi s, xi s⟫ = 1)
    (hrne : r t ≠ 0) :
    vorticityDirectionRate (r t) (xi t) forcing = eta := by
  have hproduct : HasDerivAt (fun s => r s • xi s)
      (r t • eta + radialRate • xi t) t := hr.smul hxi
  rw [hfactor] at homega
  have hforcing : forcing = radialRate • xi t + r t • eta := by
    have h := homega.unique hproduct
    rw [h]
    abel
  exact vorticityDirectionRate_eq_of_radial_tangent_decomposition hrne
    (hunit t) (inner_directionDerivative_eq_zero hxi hunit) hforcing

/-- Transverse projection distributes over addition. -/
theorem transverseComponent_add (xi v w : R3) :
    transverseComponent xi (v + w) =
      transverseComponent xi v + transverseComponent xi w := by
  simp only [transverseComponent, inner_add_right]
  module

/-- Transverse projection commutes with real scalar multiplication. -/
theorem transverseComponent_smul (a : ℝ) (xi v : R3) :
    transverseComponent xi (a • v) = a • transverseComponent xi v := by
  simp only [transverseComponent, real_inner_smul_right]
  module

/-- Exact split of the vorticity-direction rate under stretching plus a
diffusive remainder.  If `forcing = r * (S xi) + diffusion`, then the strain
turns `xi` through its transverse component and diffusion contributes after
division by the vorticity magnitude. -/
theorem vorticityDirectionRate_stretching_diffusion
    (S : R3 →L[ℝ] R3) {r : ℝ} (hr : r ≠ 0)
    (xi diffusion : R3) :
    vorticityDirectionRate r xi (r • S xi + diffusion) =
      transverseComponent xi (S xi) +
        r⁻¹ • transverseComponent xi diffusion := by
  rw [vorticityDirectionRate, transverseComponent_add,
    transverseComponent_smul, smul_add, smul_smul]
  rw [inv_mul_cancel₀ hr, one_smul]

/-- Route-facing form of the direction equation.  A differentiable nonzero
vorticity factorization whose forcing is stretching plus diffusion has the
displayed transverse direction derivative. -/
theorem directionDerivative_eq_stretching_diffusion_of_factorization
    {omega : ℝ → R3} {r : ℝ → ℝ} {xi : ℝ → R3}
    (S : R3 →L[ℝ] R3) {diffusion eta : R3} {radialRate t : ℝ}
    (homega : HasDerivAt omega (r t • S (xi t) + diffusion) t)
    (hr : HasDerivAt r radialRate t)
    (hxi : HasDerivAt xi eta t)
    (hfactor : omega = fun s => r s • xi s)
    (hunit : ∀ s, ⟪xi s, xi s⟫ = 1)
    (hrne : r t ≠ 0) :
    eta = transverseComponent (xi t) (S (xi t)) +
      (r t)⁻¹ • transverseComponent (xi t) diffusion := by
  rw [← vorticityDirectionRate_stretching_diffusion S hrne]
  exact (vorticityDirectionRate_eq_deriv_of_factorization homega hr hxi
    hfactor hunit hrne).symm

/-! ## Pairwise direction-misalignment production -/

/-- Squared chordal misalignment of two direction vectors. -/
def directionMisalignmentEnergy (xi₁ xi₂ : R3) : ℝ :=
  ⟪xi₁ - xi₂, xi₁ - xi₂⟫

/-- The exact derivative of squared pairwise direction misalignment. -/
theorem hasDerivAt_directionMisalignmentEnergy
    {xi₁ xi₂ : ℝ → R3} {eta₁ eta₂ : R3} {t : ℝ}
    (h₁ : HasDerivAt xi₁ eta₁ t) (h₂ : HasDerivAt xi₂ eta₂ t) :
    HasDerivAt (fun s => directionMisalignmentEnergy (xi₁ s) (xi₂ s))
      (2 * ⟪xi₁ t - xi₂ t, eta₁ - eta₂⟫) t := by
  have hsub : HasDerivAt (fun s => xi₁ s - xi₂ s) (eta₁ - eta₂) t :=
    h₁.sub h₂
  simpa only [directionMisalignmentEnergy, real_inner_comm, two_mul] using
    (hsub.inner ℝ hsub)

/-- Total direction turning bounds the instantaneous production of pairwise
misalignment.  Closing the refined pin requires a scale-critical integrated
version tied to actual Navier--Stokes blocks, not merely this kinematic bound. -/
theorem abs_directionMisalignmentProduction_le
    (xi₁ xi₂ eta₁ eta₂ : R3) :
    |2 * ⟪xi₁ - xi₂, eta₁ - eta₂⟫| ≤
      2 * ‖xi₁ - xi₂‖ * (‖eta₁‖ + ‖eta₂‖) := by
  have hinner : |⟪xi₁ - xi₂, eta₁ - eta₂⟫| ≤
      ‖xi₁ - xi₂‖ * ‖eta₁ - eta₂‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (xi₁ - xi₂) (eta₁ - eta₂))
  have hsub : ‖eta₁ - eta₂‖ ≤ ‖eta₁‖ + ‖eta₂‖ := norm_sub_le _ _
  calc
    |2 * ⟪xi₁ - xi₂, eta₁ - eta₂⟫|
        = 2 * |⟪xi₁ - xi₂, eta₁ - eta₂⟫| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (‖xi₁ - xi₂‖ * ‖eta₁ - eta₂‖) := by
          exact mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ ≤ 2 * (‖xi₁ - xi₂‖ * (‖eta₁‖ + ‖eta₂‖)) := by
          gcongr
    _ = 2 * ‖xi₁ - xi₂‖ * (‖eta₁‖ + ‖eta₂‖) := by ring

/-! ## Pressure-Hessian torque and the strain spectral gap -/

/-- Scalar eigenframe rotation rate produced by an off-diagonal torque across
an eigenvalue gap. -/
def eigenframeRotationRate (torque gap : ℝ) : ℝ := torque / gap

/-- Differentiating `S e_i = lambda_i e_i` and pairing with a distinct
eigenvector gives `torque + lambda_j * theta = lambda_i * theta`; hence the
angular rate is torque divided by the eigenvalue gap. -/
theorem eigenframeRotationRate_of_differentiated_eigenpair
    {lambdaI lambdaJ torque theta : ℝ} (hgap : lambdaI ≠ lambdaJ)
    (hpair : torque + lambdaJ * theta = lambdaI * theta) :
    theta = eigenframeRotationRate torque (lambdaI - lambdaJ) := by
  unfold eigenframeRotationRate
  rw [eq_div_iff (sub_ne_zero.mpr hgap)]
  linarith

/-- The naive pressure-Hessian tilting claim: unit off-diagonal torque has a
uniform angular-rate bound independent of the strain eigenvalue gap. -/
def UniformGapFreePressureTiltingBound (C : ℝ) : Prop :=
  ∀ gap : ℝ, 0 < gap → eigenframeRotationRate 1 gap ≤ C

/-- **Gap obstruction.**  No nonnegative constant uniformly controls
pressure-Hessian-driven eigenframe tilting without a lower eigenvalue-gap
bound.  Unit torque and gaps tending to zero have unbounded angular rate. -/
theorem no_uniformGapFreePressureTiltingBound (C : ℝ) (hC : 0 ≤ C) :
    ¬ UniformGapFreePressureTiltingBound C := by
  intro hbound
  have hCp : 0 < C + 1 := by linarith
  have hgap : 0 < (1 / (C + 1) : ℝ) := one_div_pos.mpr hCp
  have h := hbound (1 / (C + 1)) hgap
  have hne : C + 1 ≠ 0 := ne_of_gt hCp
  simp [eigenframeRotationRate] at h
  linarith

end DirectionEvolutionTilting
end NavierStokes
end FluidDynamics
end Mettapedia
