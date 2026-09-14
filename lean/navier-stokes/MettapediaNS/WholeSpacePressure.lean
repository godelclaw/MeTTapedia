import Euler.OrdinaryHelmholtzField
import MettapediaNS.WholeSpaceBKM

/-!
# Constructed pressure in the whole-space viscous right-hand side

The pressure gradient is OpenAI's Helmholtz construction. Its scalar
potential and gradient-space membership are supplied by the upstream
potential theorem, not assumed. The actual viscous right-hand side then
inherits the already imported nonlinear energy estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousEnergy

open MeasureTheory EulerSmoothLimit EulerLpTranslation EulerOrdinarySobolev
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVectorCalculus
open scoped ContDiff

/-- The upstream normalized radial potential of the constructed pressure gradient. -/
abbrev pressurePotential (A : SmoothL2Field Space) : Space → ℝ :=
  EulerCanonicalGraphPotential.radialPotential (pressureField A).field

theorem pressurePotential_spec (A : SmoothL2Field Space) :
    ContDiff ℝ ∞ (pressurePotential A) ∧ pressurePotential A 0 = 0 ∧
      ∀ x, _root_.gradient (pressurePotential A) x = (pressureField A).field x :=
  EulerMeanPressure.gradientSpace_radial_potential (pressureField A).toLp
    (pressureField_mem_gradient A) (pressureField A).field
    (pressureField A).toLp_ae (pressureField A).smooth

/-- No independently supplied pressure field enters this right-hand side. -/
abbrev projectedNavierStokesRhs (ν : ℝ) (A : SmoothL2Field Space) : SmoothL2Field Space :=
  navierStokesRhs ν A (pressureField A)

theorem projectedNavierStokesRhs_field (ν : ℝ) (A : SmoothL2Field Space) (x : Space) :
    (projectedNavierStokesRhs ν A).field x =
      -fderiv ℝ A.field x (A.field x) - _root_.gradient (pressurePotential A) x +
        ν • Laplacian.laplacian A.field x := by
  rw [(pressurePotential_spec A).2.2 x]
  exact navierStokesRhs_field ν A (pressureField A) x

/-- Spatial derivatives preserve the upstream closed solenoidal space. -/
theorem laplacianField_mem_solenoidal (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) : (laplacianField A).toLp ∈ solenoidalSpace := by
  rw [laplacianField, toLp_sumField]
  apply solenoidalSpace.sum_mem
  intro i _
  change (wordField A (fun _ : Fin 2 ↦ i)).toLp ∈ solenoidalSpace
  exact word_solenoidal A hA _

theorem projectedNavierStokesRhs_eq (ν : ℝ) (A : SmoothL2Field Space) :
    projectedNavierStokesRhs ν A =
      addField (projectedRhs A) (scaleField ν (laplacianField A)) := by
  have he : eulerRhs A (pressureField A) = projectedRhs A := by
    apply field_ext
    funext x
    rw [eulerRhs_field, projectedRhs_field]
  change addField (eulerRhs A (pressureField A)) _ = _
  rw [he]

theorem projectedNavierStokesRhs_mem_solenoidal (ν : ℝ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    (projectedNavierStokesRhs ν A).toLp ∈ solenoidalSpace := by
  rw [projectedNavierStokesRhs_eq, toLp_addField, projectedRhs_toLp, scaleField_toLp]
  exact solenoidalSpace.add_mem (solenoidalSpace.neg_mem (solenoidalProjection_mem _))
    (solenoidalSpace.smul_mem ν (laplacianField_mem_solenoidal A hA))

/-- The constructed pressure makes the actual viscous right-hand side
divergence-free; no Navier–Stokes trajectory is presumed in this identity. -/
theorem divergence_projectedNavierStokesRhs_eq_zero (ν : ℝ) (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (x : Space) :
    divergence (projectedNavierStokesRhs ν A).field x = 0 :=
  EulerMeanClassical.solenoidal_representative_divergence _
    (projectedNavierStokesRhs_mem_solenoidal ν A
      (smooth_mem_solenoidal A.field A.smooth A.memLp hdiv)) _
    (projectedNavierStokesRhs ν A).smooth (projectedNavierStokesRhs ν A).toLp_ae x

/-- Actual solenoidality and the constructed pressure discharge both
closed-subspace hypotheses of the imported energy theorem. -/
theorem h3_projectedProduction_add_dissipation_le
    (ν : ℝ) (A : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K)
    (hdiv : ∀ x, divergence A.field x = 0) :
    integerEnergyProduction 3 A (projectedNavierStokesRhs ν A) +
        2 * ν * wordDissipation 3 A ≤
      gradientEnergyConstant * K * wordEnergy 3 A :=
  h3_energyProduction_add_dissipation_le ν A (pressureField A) K hK hdiv
    (smooth_mem_solenoidal A.field A.smooth A.memLp hdiv) (pressureField_mem_gradient A)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousEnergy
