import Mettapedia.Analysis.VorticityStrainProduction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedProjectionEvolution

/-!
# Scalar-reference cancellation for the actual weighted projection

The changing amplitude weight is combined with the actual symmetric
curl-vorticity source before taking absolute values. Only a regularization
term remains from the scalar reference strain. The shifted strain,
rotation flux, and weighted viscosity all remain in the material equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalCoherentStrainProduction

open scoped RealInnerProductSpace
open Mettapedia.Analysis VorticityJetSource VorticityStrainProduction
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeBlockReality PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories
open PancakeFourierMaterialPaths LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalAlignmentForcing LocalVariableHelicityCenter LocalWeightedCurlCancellation
open HelicityAngularSource HelicitySourceStrainSplit LocalHelicityRotationFlux
open LocalHelicityProjectionEvolution LocalHelicityProjectionDiffusion LocalWeightedProjectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem rowAction_actualStrain (u : FourierVelocity) (x : T3) (a : R3) :
    rowAction (strainRows (fun m ↦ realComponentGradient u m x)) a = fullStrainOperator u x a := by
  ext i
  fin_cases i <;>
    simp [rowAction, strainRows, realComponentGradient, componentGradient,
      fullStrainOperator, realMatrixOperator_apply,
      PancakeLocalStrainEquation.spatialStrain, PancakeFilteredStrainDynamics.symmetrize,
      PancakeLocalGradientEquation.spatialVelocityGradient, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three] <;> ring

def coherentRemainder (σ δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  weightedProduction δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fun j ↦ fullCurlGradient u j x)
    (scalarShift σ (strainRows (fun m ↦ realComponentGradient u m x)))

theorem combinedStrain_eq_weightedProduction (δ : ℝ) (u : FourierVelocity) (x : T3) :
    amplitudeStrainRate δ u x + ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x =
      weightedProduction δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
        (fun j ↦ fullCurlGradient u j x) (strainRows (fun m ↦ realComponentGradient u m x)) := by
  simp only [weightedProduction, rowAction_actualStrain, amplitudeStrainRate, strainProjectionRate,
    projectionResidual, projectionEnergy, regularizedCenter, RegularizedProjection.coefficient,
    strainSource]

/-- The common scalar part cancels without any assumption that the
deviation from it is small. Curl compatibility is reconstructed from u. -/
theorem combinedStrain_eq_coherent (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) (σ : ℝ) :
    amplitudeStrainRate δ u x + ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x =
      coherentRemainder σ δ u x - 2 * σ * δ * regularizedCenter δ u x ^ 2 * ‖fullVorticity u x‖ ^ 6 := by
  rw [combinedStrain_eq_weightedProduction]
  exact weightedProduction_eq_shift δ hδ _ _ _ _ (fullVorticity_curl_eq_curlJet u hu x) σ

theorem combinedInviscid_eq_coherent (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (σ : ℝ) :
    amplitudeStrainRate δ u x + ‖fullVorticity u x‖ ^ 6 * projectionInviscidRate δ u x =
      coherentRemainder σ δ u x - 2 * σ * δ * regularizedCenter δ u x ^ 2 * ‖fullVorticity u x‖ ^ 6 +
        2 * ‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, rotationSource u x⟫ := by
  rw [projectionInviscidRate_eq_strain_add_rotation δ u hu hd hr x]
  calc
    _ = (amplitudeStrainRate δ u x + ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x) +
        2 * ‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, rotationSource u x⟫ := by ring
    _ = _ := by rw [combinedStrain_eq_coherent δ hδ u
      (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu) x σ]

theorem hasDerivAt_weightedProjectionDensity_coherent {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (σ : ℝ) :
    HasDerivAt (fun τ ↦ weightedProjectionDensity δ (s.coefficients τ) (torusPoint (X τ)))
      (coherentRemainder σ δ (s.coefficients t) (torusPoint (X t)) -
        2 * σ * δ * regularizedCenter δ (s.coefficients t) (torusPoint (X t)) ^ 2 *
          ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ ^ 6 +
        2 * ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ ^ 6 *
          ⟪projectionResidual δ (s.coefficients t) (torusPoint (X t)),
            rotationSource (s.coefficients t) (torusPoint (X t))⟫ +
        ν * weightedViscousRate δ (s.coefficients t) (torusPoint (X t))) t := by
  have hm := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
  simpa only [combinedInviscid_eq_coherent δ hδ _ hm (s.transverse t) (s.reality t) _ σ] using
    hasDerivAt_weightedProjectionDensity s g hg hSum hu X hX δ hδ t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalCoherentStrainProduction
