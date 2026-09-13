import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityProjectionDiffusion

/-!
# Material evolution of the actual curl-projection energy

The regularized moving minimum cancels the explicit derivative of its
optimizing coefficient. It does not cancel the nonlinear source paired
with the residual, nor the strain action on that residual. This file
retains both contributions and the full signed diffusion curvature.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityProjectionEvolution

open scoped RealInnerProductSpace
open Mettapedia.Analysis RegularizedProjectionParabolic
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories
open PancakeFourierMaterialPaths LocalMaterialVorticity LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalVorticitySeparation LocalVariableHelicityCenter
open LocalHelicitySourceEvolution LocalHelicityProjectionDiffusion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def projectionResidual (δ : ℝ) (u : FourierVelocity) (x : T3) : R3 :=
  RegularizedProjection.residual δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)

def projectionInviscidRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  2 * ⟪projectionResidual δ u x,
    -gradient u x (fullVorticity (fourierCurl u) x) + source u x -
      regularizedCenter δ u x • fullStrainOperator u x (fullVorticity u x)⟫

theorem projectionInviscidRate_eq (δ : ℝ) (u : FourierVelocity) (x : T3) :
    projectionInviscidRate δ u x =
      -2 * ⟪projectionResidual δ u x, fullStrainOperator u x (projectionResidual δ u x)⟫ -
      4 * regularizedCenter δ u x *
        ⟪projectionResidual δ u x, fullStrainOperator u x (fullVorticity u x)⟫ +
      2 * ⟪projectionResidual δ u x, source u x⟫ := by
  have hb : gradient u x (fullVorticity (fourierCurl u) x) =
      gradient u x (projectionResidual δ u x) +
        regularizedCenter δ u x • fullStrainOperator u x (fullVorticity u x) := by
    simp only [projectionResidual, RegularizedProjection.residual, map_sub, map_smul,
      gradient_vorticity, regularizedCenter, RegularizedProjection.coefficient]
    abel
  have hs := LocalRadialCoherentBound.inner_gradient_add_inner_gradient u x
    (projectionResidual δ u x) (projectionResidual δ u x)
  have he : ⟪projectionResidual δ u x, gradient u x (projectionResidual δ u x)⟫ =
      ⟪projectionResidual δ u x, fullStrainOperator u x (projectionResidual δ u x)⟫ := by
    linarith only [hs, real_inner_comm (gradient u x (projectionResidual δ u x)) (projectionResidual δ u x),
      real_inner_comm (fullStrainOperator u x (projectionResidual δ u x)) (projectionResidual δ u x)]
  simp only [projectionInviscidRate, hb, neg_add, inner_sub_right, inner_add_right,
    inner_neg_right, real_inner_smul_right, he]
  ring

/-- Isolating a scalar coherent strain exposes its favorable feedback
when the scalar is positive. The normal defect is the actual difference
`S omega - sigma omega`; no alignment hypothesis is imposed. -/
theorem projectionInviscidRate_eq_coherent (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (x : T3) (σ : ℝ) :
    projectionInviscidRate δ u x =
      -2 * ⟪projectionResidual δ u x, fullStrainOperator u x (projectionResidual δ u x)⟫ -
      4 * δ * regularizedCenter δ u x ^ 2 * σ -
      4 * regularizedCenter δ u x * ⟪projectionResidual δ u x,
        LocalRadialCoherentBound.normalDefect u x σ (fullVorticity u x)⟫ +
      2 * ⟪projectionResidual δ u x, source u x⟫ := by
  have hi : ⟪projectionResidual δ u x, fullVorticity u x⟫ = δ * regularizedCenter δ u x := by
    rw [real_inner_comm (fullVorticity u x) (projectionResidual δ u x)]
    exact RegularizedProjection.inner_residual δ hδ _ _
  rw [projectionInviscidRate_eq]
  simp only [LocalRadialCoherentBound.normalDefect, inner_sub_right, real_inner_smul_right, hi]
  ring

/-- The coherent term and signed residual strain are retained on the
left; only the cross-feedback defect is bounded in absolute value. -/
theorem projectionInviscidRate_add_coherent_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (x : T3) (σ : ℝ) :
    projectionInviscidRate δ u x +
      2 * ⟪projectionResidual δ u x, fullStrainOperator u x (projectionResidual δ u x)⟫ +
      4 * δ * regularizedCenter δ u x ^ 2 * σ ≤
      4 * |regularizedCenter δ u x| * ‖projectionResidual δ u x‖ *
        ‖LocalRadialCoherentBound.normalDefect u x σ (fullVorticity u x)‖ +
      2 * ⟪projectionResidual δ u x, source u x⟫ := by
  rw [projectionInviscidRate_eq_coherent δ hδ u x σ]
  have h1 := neg_le_abs (regularizedCenter δ u x * ⟪projectionResidual δ u x,
    LocalRadialCoherentBound.normalDefect u x σ (fullVorticity u x)⟫)
  rw [abs_mul] at h1
  have h2 := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (projectionResidual δ u x)
    (LocalRadialCoherentBound.normalDefect u x σ (fullVorticity u x)))
      (abs_nonneg (regularizedCenter δ u x))
  nlinarith only [h1, h2]

theorem energyRate_eq (δ ν : ℝ) (u : FourierVelocity) (x : T3) :
    energyRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
      (fullStrainOperator u x (fullVorticity u x) + ν • fullVorticityLaplacian u x)
      (-gradient u x (fullVorticity (fourierCurl u) x) + source u x +
        ν • fullVorticityLaplacian (fourierCurl u) x) =
      projectionInviscidRate δ u x + ν * projectionViscousRate δ u x := by
  simp only [energyRate, projectionInviscidRate, projectionViscousRate, projectionResidual,
    regularizedCenter, RegularizedProjection.coefficient, smul_add, smul_smul,
    inner_sub_right, inner_add_right, real_inner_smul_right]
  ring

/-- This is the derivative along an actual material path of an unforced
periodic solution, not an assumed evolution for an independent defect. -/
theorem hasDerivAt_projectionEnergy {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ projectionEnergy δ (s.coefficients τ) (torusPoint (X τ)))
      (projectionInviscidRate δ (s.coefficients t) (torusPoint (X t)) +
        ν * projectionViscousRate δ (s.coefficients t) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  have hb := hasDerivAt_curlVorticity_source s g hg hSum hu X hX t ht
  have h := RegularizedProjection.hasDerivAt_energy δ hδ ha hb
  change HasDerivAt (fun τ ↦ projectionEnergy δ (s.coefficients τ) (torusPoint (X τ)))
    (energyRate δ (fullVorticity (s.coefficients t) (torusPoint (X t)))
      (fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t)))
      (fullStrainOperator (s.coefficients t) (torusPoint (X t))
        (fullVorticity (s.coefficients t) (torusPoint (X t))) +
          ν • fullVorticityLaplacian (s.coefficients t) (torusPoint (X t)))
      (-gradient (s.coefficients t) (torusPoint (X t))
        (fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t))) +
        source (s.coefficients t) (torusPoint (X t)) +
        ν • fullVorticityLaplacian (fourierCurl (s.coefficients t)) (torusPoint (X t)))) t at h
  rwa [energyRate_eq] at h

theorem hasDerivAt_projectionEnergy_parabolic {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ projectionEnergy δ (s.coefficients τ) (torusPoint (X τ)))
      (projectionInviscidRate δ (s.coefficients t) (torusPoint (X t)) +
        ν * (projectionLaplacian δ (s.coefficients t) (torusPoint (X t)) -
          projectionCurvature δ (s.coefficients t) (torusPoint (X t)))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  simpa only [projectionViscousRate_eq δ hδ _ hm] using
    hasDerivAt_projectionEnergy s g hg hSum hu X hX δ hδ t ht

/-- The actual material derivative is bounded by diffusion and two
explicit costs. Neither right-hand cost is an initial-data estimate. -/
theorem deriv_projectionEnergy_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 ≤ ν)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ projectionEnergy δ (s.coefficients τ) (torusPoint (X τ))) t ≤
      projectionInviscidRate δ (s.coefficients t) (torusPoint (X t)) +
        ν * (projectionLaplacian δ (s.coefficients t) (torusPoint (X t)) +
          (2 / δ) * residualGradientPairing δ (s.coefficients t) (torusPoint (X t))) := by
  rw [(hasDerivAt_projectionEnergy s g hg hSum hu X hX δ hδ t ht).deriv]
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (projectionViscousRate_le δ hδ _ hm _) hν)

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityProjectionEvolution
