import Mettapedia.Analysis.WeightedProjectionVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandProjectionEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredVorticity

/-!
# Actual finite-filter vorticity variations

Both the resolved nonlinear rate and the all-input subgrid rate are
restricted on the output. Their sum, not either alone, is the derivative
of the actual filtered solution. No Galerkin evolution is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityVariation

open scoped RealInnerProductSpace
open Mettapedia.Analysis WeightedProjectionParabolic WeightedProjectionVariation
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeGalerkinKineticEnergy
open PancakeGalerkinVorticityBridge PancakePhysicalSpectralDefect PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing LocalLowDiffusionBudget FourierFiniteSupport
open PancakeFilteredStrainDynamics InfiniteFilteredEquation LocalFilteredVorticity
open LocalWeightedProjectionEvolution LocalHelicityProjectionEvolution
open PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation
local notation "T3" => UnitAddTorus (Fin 3)

def restrictVelocity (P : Finset Wavevector) (u : FourierVelocity) : FourierVelocity :=
  filteredVelocity (sharpFilter P) u

theorem restrictVelocity_eq_zero (P : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) (hq : q ∉ P) : restrictVelocity P u q = 0 := by
  simp [restrictVelocity, filteredVelocity, sharpFilter, hq]

theorem fourierCurl_restrictVelocity (P : Finset Wavevector) (u : FourierVelocity) :
    fourierCurl (restrictVelocity P u) = restrictVelocity P (fourierCurl u) :=
  fourierCurl_filteredVelocity _ _

theorem fullVorticity_restrictVelocity (P : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    fullVorticity (restrictVelocity P u) x = spatialVorticity P u x := by
  rw [fullVorticity_eq_spatialVorticity P _ (restrictVelocity_eq_zero P u)]
  simp only [spatialVorticity, fourierCurl_restrictVelocity, finiteFourierReconstruction]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp [restrictVelocity, filteredVelocity, sharpFilter, hq]

theorem spatialVorticity_add (P : Finset Wavevector) (u v : FourierVelocity) (x : T3) :
    spatialVorticity P (u + v) x = spatialVorticity P u x + spatialVorticity P v x := by
  ext i
  simp [spatialVorticity, fourierCurl_add, finiteFourierReconstruction, smul_add,
    Finset.sum_add_distrib, complexRealPartEuclidean]

theorem hasDerivAt_finiteReconstruction (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (v : FourierVelocity) (t : ℝ) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ finiteFourierReconstruction P (u τ) x)
      (finiteFourierReconstruction P v x) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    HasDerivAt.fun_sum (fun q hq ↦ (hd q hq i).const_mul (UnitAddTorus.mFourier q x))

theorem hasDerivAt_spatialVorticity (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (v : FourierVelocity) (t : ℝ) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ spatialVorticity P (u τ) x) (spatialVorticity P v x) t := by
  exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_finiteReconstruction P (fun τ ↦ fourierCurl (u τ)) (fourierCurl v) t x
      (fun q hq ↦ hasDerivAt_fourierCurl u v t q (hd q hq)))

theorem hasDerivAt_fullVorticity (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hs : ∀ τ q, q ∉ P → u τ q = 0) (v : FourierVelocity) (t : ℝ) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ fullVorticity (u τ) x) (fullVorticity (restrictVelocity P v) x) t := by
  simp_rw [fullVorticity_eq_spatialVorticity P _ (hs _), fullVorticity_restrictVelocity]
  exact hasDerivAt_spatialVorticity P u v t x hd

def densityRate (δ : ℝ) (u v : FourierVelocity) (x : T3) : ℝ :=
  weightedRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullVorticity v x) (fullVorticity (fourierCurl v) x)

theorem hasDerivAt_weightedDensity (δ : ℝ) (hδ : 0 < δ)
    (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hs : ∀ τ q, q ∉ P → u τ q = 0) (v : FourierVelocity) (t : ℝ) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ weightedProjectionDensity δ (u τ) x)
      (densityRate δ (u t) (restrictVelocity P v) x) t := by
  have ha := hasDerivAt_fullVorticity P u hs v t x hd
  have hb := hasDerivAt_fullVorticity P (fun τ ↦ fourierCurl (u τ))
    (fun τ ↦ fourierCurl_eq_zero P (u τ) (hs τ)) (fourierCurl v) t x
    (fun q hq ↦ hasDerivAt_fourierCurl u v t q (hd q hq))
  rw [← fourierCurl_restrictVelocity] at hb
  exact hasDerivAt_weightedEnergy δ hδ ha hb

theorem densityRate_restrict_add (δ : ℝ) (P : Finset Wavevector)
    (u v w : FourierVelocity) (x : T3) :
    densityRate δ u (restrictVelocity P (v + w)) x =
      densityRate δ u (restrictVelocity P v) x + densityRate δ u (restrictVelocity P w) x := by
  simp only [densityRate, fourierCurl_restrictVelocity, fullVorticity_restrictVelocity,
    fourierCurl_add, spatialVorticity_add, weightedRate_add]

/-- This derivative is derived from the full infinite coefficient equation.
Output restriction is applied to both summands of its exact decomposition. -/
theorem hasDerivAt_filteredWeightedDensity {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (δ : ℝ) (hδ : 0 < δ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ weightedProjectionDensity δ (filteredVelocity χ (s.coefficients τ)) x)
      (densityRate δ (filteredVelocity χ (s.coefficients t))
        (restrictVelocity P (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)))) x +
      densityRate δ (filteredVelocity χ (s.coefficients t))
        (restrictVelocity P (subgridForce χ (s.coefficients t))) x) t := by
  have h := hasDerivAt_weightedDensity δ hδ P (fun τ ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ q hq ↦ by simp [filteredVelocity, hcut q hq])
    (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)) + subgridForce χ (s.coefficients t))
    t x (fun q _ i ↦ hasDerivAt_filtered_coefficients s χ C hχ t ht q i)
  rwa [densityRate_restrict_add] at h

def correctedDensity (δ κ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 8 / 8 - 3 / κ * weightedProjectionDensity δ u x

def correctedDensityRate (δ κ : ℝ) (u v : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullVorticity v x⟫ - 3 / κ * densityRate δ u v x

theorem hasDerivAt_correctedDensity (δ : ℝ) (hδ : 0 < δ) (κ : ℝ)
    (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hs : ∀ τ q, q ∉ P → u τ q = 0) (v : FourierVelocity) (t : ℝ) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ correctedDensity δ κ (u τ) x)
      (correctedDensityRate δ κ (u t) (restrictVelocity P v) x) t := by
  have ha := hasDerivAt_fullVorticity P u hs v t x hd
  have hK := hasDerivAt_weightedDensity δ hδ P u hs v t x hd
  have h := ((ha.norm_sq.fun_pow 4).div_const 8).sub (hK.const_mul (3 / κ))
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] at h
  apply h.congr_deriv
  unfold correctedDensityRate
  ring

theorem correctedDensityRate_restrict_add (δ κ : ℝ) (P : Finset Wavevector)
    (u v w : FourierVelocity) (x : T3) :
    correctedDensityRate δ κ u (restrictVelocity P (v + w)) x =
      correctedDensityRate δ κ u (restrictVelocity P v) x +
        correctedDensityRate δ κ u (restrictVelocity P w) x := by
  simp only [correctedDensityRate, densityRate_restrict_add, fullVorticity_restrictVelocity,
    spatialVorticity_add, inner_add_right]
  ring

theorem hasDerivAt_filteredCorrectedDensity {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (δ : ℝ) (hδ : 0 < δ) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ correctedDensity δ κ (filteredVelocity χ (s.coefficients τ)) x)
      (correctedDensityRate δ κ (filteredVelocity χ (s.coefficients t))
        (restrictVelocity P (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)))) x +
      correctedDensityRate δ κ (filteredVelocity χ (s.coefficients t))
        (restrictVelocity P (subgridForce χ (s.coefficients t))) x) t := by
  have h := hasDerivAt_correctedDensity δ hδ κ P (fun τ ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ q hq ↦ by simp [filteredVelocity, hcut q hq])
    (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)) + subgridForce χ (s.coefficients t))
    t x (fun q _ i ↦ hasDerivAt_filtered_coefficients s χ C hχ t ht q i)
  rwa [correctedDensityRate_restrict_add] at h

end Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityVariation
