import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicVectorWeakDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootEnergy

/-!
# The actual weak divergence of root-localized vorticity

The vector field, not its potentially singular scalar root factor, is
differentiated. Its weak coordinate derivatives and divergence are in L².
The existing fourth-power partition budget bounds the summed weighted
divergence energy with only the fixed three-coordinate factor. Gaussian
temperature, logarithmic cardinality, and projector/gap-gradient costs
remain explicit and are not asserted to be affordable in time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeCurlOutputTail LocalLowDiffusionBudget
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeHigherDerivativeMoments GaussianRootVorticity GaussianRootPartition
open LocalSquaredGapPressure LocalSpatialVorticityJets
open Mettapedia.Analysis.EuclideanOperatorCoordinates
open FourierPressureTraceSymbol (complexifyVector)
open PancakePeriodicVorticityEquation (unitTorusDerivativePhase)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def coordinateDerivative (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (j : Fin 3) : T3 → R3 :=
  PeriodicVectorWeakDerivative.coordinateRate (rootVorticity gamma chi modes u centers tau i) j

def divergence (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) : T3 → ℝ :=
  PeriodicVectorWeakDerivative.divergence (rootVorticity gamma chi modes u centers tau i)

theorem ae_hasDerivAt_coordinateDerivative (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (j : Fin 3) :
    ∀ᵐ x : T3, HasDerivAt
      (fun h ↦ rootVorticity gamma chi modes u centers tau i (x + coordinateShift j h))
      (coordinateDerivative gamma chi modes u centers tau i j x) 0 :=
  PeriodicVectorWeakDerivative.ae_hasDerivAt_coordinateRate _ j
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i)

theorem memLp_coordinateDerivative (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (j : Fin 3) :
    MemLp (coordinateDerivative gamma chi modes u centers tau i j) 2 :=
  PeriodicVectorWeakDerivative.memLp_coordinateRate _ j
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i)

theorem memLp_divergence (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) : MemLp (divergence gamma chi modes u centers tau i) 2 :=
  PeriodicVectorWeakDerivative.memLp_divergence _
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i)

theorem mFourierCoeff_divergence (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (divergence gamma chi modes u centers tau i x : ℂ)) q =
      unitTorusDerivativePhase * ∑ j : Fin 3, (q j : ℂ) * UnitAddTorus.mFourierCoeff
        (fun x ↦ complexifyVector (rootVorticity gamma chi modes u centers tau i x)) q j :=
  PeriodicVectorWeakDerivative.mFourierCoeff_divergence _
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i) q

def coordinateBudget (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (j : Fin 3) (k : ↑centers) (x : T3) : ℝ :=
  let b := fun y : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) y)
  let M := fun y : T3 ↦ coordinates (localProjector gamma chi modes u y)
  2 * b x ^ 2 * deriv (fun h ↦ b (x + coordinateShift j h)) 0 ^ 2 * ‖fullVorticity u x‖ ^ 4 +
    b x ^ 4 * (‖M x - M k.1‖ ^ 2 + tau * Real.log (Fintype.card ↑centers)) *
      ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j x)‖ ^ 2 *
        ‖fullVorticity u x‖ ^ 4 / (2 * tau ^ 2) +
    8 * b x ^ 4 * ‖fullVorticity u x‖ ^ 2 * ‖fullCurlGradient u j x‖ ^ 2

theorem ae_weighted_coordinate_energy_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (ht : 0 < tau) :
    ∀ᵐ x : T3, ∀ j : Fin 3, ∀ k : ↑centers,
      (∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
        ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2) ≤
          coordinateBudget gamma chi modes u centers tau j k x := by
  have hd (i : ↑centers) (j : Fin 3) := ae_hasDerivAt_coordinateDerivative gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) centers hc tau i j
  have hb (j : Fin 3) := GaussianRootEnergy.ae_coordinate_weighted_rootVorticity_energy_le
    gamma hg chi modes u hu centers hc tau ht j
  filter_upwards [ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (hd i)), ae_all_iff.mpr hb] with x hx hbx j k
  have heq (i : ↑centers) := (hx i j).deriv
  simpa only [heq, coordinateBudget] using hbx j k

theorem weighted_divergence_le_coordinate_energy (gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (x : T3) :
      (∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
        divergence gamma chi modes u centers tau i x ^ 2) ≤
        3 * ∑ j : Fin 3, ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
          ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2 := by
  calc
    _ ≤ ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
        (3 * ∑ j : Fin 3, ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (PeriodicVectorWeakDerivative.divergence_sq_le _ x) (sq_nonneg _)
    _ = 3 * ∑ j : Fin 3, ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
        ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem ae_weighted_divergence_energy_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (ht : 0 < tau) :
    ∀ᵐ x : T3, ∀ k : ↑centers,
      (∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
        divergence gamma chi modes u centers tau i x ^ 2) ≤
          3 * ∑ j : Fin 3, coordinateBudget gamma chi modes u centers tau j k x := by
  filter_upwards [ae_weighted_coordinate_energy_le gamma hg chi modes u hu centers hc tau ht]
    with x hx k
  exact (weighted_divergence_le_coordinate_energy gamma chi modes u centers tau x).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hx j k)) (by norm_num))

theorem integrable_weighted_divergence_energy (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    Integrable (fun x : T3 ↦ ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
      divergence gamma chi modes u centers tau i x ^ 2) := by
  apply integrable_finsetSum
  intro i _
  have h := PancakePeriodicWeakDerivative.integrable_mul_continuous _ _
    (memLp_divergence gamma hg chi modes u hu centers hc tau i).integrable_sq
    ((continuous_rootPatch gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i).pow 2)
  simpa only [mul_comm] using h

theorem integrable_weighted_coordinate_energy (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) :
    Integrable (fun x : T3 ↦ ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
      ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2) := by
  apply integrable_finsetSum
  intro i _
  have h := PancakePeriodicWeakDerivative.integrable_mul_continuous _ _
    (memLp_coordinateDerivative gamma hg chi modes u hu centers hc tau i j).norm.integrable_sq
    ((continuous_rootPatch gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i).pow 2)
  simpa only [mul_comm] using h

theorem integral_weighted_divergence_le_coordinate_energy (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    (∫ x : T3, ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
      divergence gamma chi modes u centers tau i x ^ 2) ≤
        3 * ∑ j : Fin 3, ∫ x : T3, ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
          ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2 := by
  have hi := integrable_weighted_coordinate_energy gamma hg chi modes u hu centers hc tau
  have h := integral_mono (integrable_weighted_divergence_energy gamma hg chi modes u hu centers hc tau)
    ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul 3)
    (weighted_divergence_le_coordinate_energy gamma chi modes u centers tau)
  rwa [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hi j)] at h

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence
