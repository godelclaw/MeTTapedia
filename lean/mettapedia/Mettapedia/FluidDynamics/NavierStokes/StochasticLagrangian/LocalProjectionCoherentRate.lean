import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionInviscidWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicityAngularSource

/-!
# Coherent sign in the weighted projection material rate

Since the projection correction is subtracted from the octic energy, a
lower bound on its material rate is useful. For a nonnegative scalar
upper bound on strain, the coherent part below is nonnegative. The exact
normal-alignment defect and actual angular derivative source remain
signed. Neither their time budget nor global alignment is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionCoherentRate

open scoped RealInnerProductSpace
open Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail PancakeBlockReality
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalAlignmentForcing
open LocalHelicityProjectionDiffusion LocalHelicityProjectionEvolution LocalVariableHelicityCenter
open LocalWeightedProjectionEvolution LocalProjectionInviscidWork LocalRadialCoherentBound
open LocalHelicitySourceEvolution HelicityAngularSource EuclideanCrossProduct

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def coherentRate (δ : ℝ) (u : FourierVelocity) (x : T3) (σ : ℝ) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 *
    (4 * σ * ‖projectionResidual δ u x‖ ^ 2 +
      2 * δ * regularizedCenter δ u x ^ 2 * σ +
      2 * ⟪projectionResidual δ u x,
        σ • projectionResidual δ u x - fullStrainOperator u x (projectionResidual δ u x)⟫)

def normalRate (δ : ℝ) (u : FourierVelocity) (x : T3) (σ : ℝ) : ℝ :=
  6 * ‖fullVorticity u x‖ ^ 4 *
      ⟪fullVorticity u x, normalDefect u x σ (fullVorticity u x)⟫ * projectionEnergy δ u x -
    4 * regularizedCenter δ u x * ‖fullVorticity u x‖ ^ 6 *
      ⟪projectionResidual δ u x, normalDefect u x σ (fullVorticity u x)⟫

def sourceRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  2 * ‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, source u x⟫

theorem projectionMaterialRate_eq_split (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (x : T3) (σ : ℝ) :
    projectionMaterialRate δ u x = coherentRate δ u x σ + normalRate δ u x σ + sourceRate δ u x := by
  have he : projectionEnergy δ u x = ‖projectionResidual δ u x‖ ^ 2 +
      δ * regularizedCenter δ u x ^ 2 := rfl
  rw [projectionMaterialRate_eq, projectionInviscidRate_eq_coherent δ hδ u x σ]
  simp only [amplitudeStrainRate, coherentRate, normalRate, sourceRate, he,
    normalDefect, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem coherentRate_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (u : FourierVelocity) (x : T3)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hmax : ∀ z : R3, ⟪z, fullStrainOperator u x z⟫ ≤ σ * ‖z‖ ^ 2) :
    0 ≤ coherentRate δ u x σ := by
  have hq : 0 ≤ ⟪projectionResidual δ u x,
      σ • projectionResidual δ u x - fullStrainOperator u x (projectionResidual δ u x)⟫ := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (hmax _)
  unfold coherentRate
  positivity

/-- This is the direction needed for the negative projection correction.
Only the coherent part has been discarded, using its proved sign. -/
theorem normalRate_add_sourceRate_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hmax : ∀ z : R3, ⟪z, fullStrainOperator u x z⟫ ≤ σ * ‖z‖ ^ 2) :
    normalRate δ u x σ + sourceRate δ u x ≤ projectionMaterialRate δ u x := by
  rw [projectionMaterialRate_eq_split δ hδ u x σ]
  linarith only [coherentRate_nonneg δ hδ.le u x σ hσ hmax]

theorem normalRate_eq_zero_of_aligned (δ : ℝ) (u : FourierVelocity) (x : T3) (σ : ℝ)
    (halign : fullStrainOperator u x (fullVorticity u x) = σ • fullVorticity u x) :
    normalRate δ u x σ = 0 := by
  simp [normalRate, normalDefect, halign]

/-- Source-free perfect alignment tests the favorable sign; it is not a
claim that an arbitrary solution satisfies these hypotheses. -/
theorem projectionMaterialRate_nonneg_of_aligned (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (x : T3) (σ : ℝ) (hσ : 0 ≤ σ)
    (hmax : ∀ z : R3, ⟪z, fullStrainOperator u x z⟫ ≤ σ * ‖z‖ ^ 2)
    (halign : fullStrainOperator u x (fullVorticity u x) = σ • fullVorticity u x)
    (hsource : ⟪projectionResidual δ u x, source u x⟫ = 0) :
    0 ≤ projectionMaterialRate δ u x := by
  have h := normalRate_add_sourceRate_le δ hδ u x σ hσ hmax
  simpa only [normalRate_eq_zero_of_aligned δ u x σ halign, sourceRate,
    hsource, mul_zero, zero_add] using h

/-- The surviving source is paired before any absolute value is taken.
The vectors on both legs are reconstructed from the same velocity. -/
theorem sourceRate_eq_angular (δ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    sourceRate δ u x = 4 * ‖fullVorticity u x‖ ^ 6 *
      ∑ j : Fin 3, ⟪realComponentGradient u j x,
        cross (projectionResidual δ u x) (fullCurlGradient u j x)⟫ := by
  have hc (j : Fin 3) :
      ⟪projectionResidual δ u x, cross (realComponentGradient u j x) (fullCurlGradient u j x)⟫ =
        -⟪realComponentGradient u j x, cross (projectionResidual δ u x) (fullCurlGradient u j x)⟫ := by
    rw [inner_cross_cycle, cross_swap (fullCurlGradient u j x), inner_neg_right]
    ring
  simp only [sourceRate, source_eq_cross u hu hd hr, inner_neg_right, two_smul,
    inner_add_right, inner_sum, hc, Finset.sum_neg_distrib]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionCoherentRate
