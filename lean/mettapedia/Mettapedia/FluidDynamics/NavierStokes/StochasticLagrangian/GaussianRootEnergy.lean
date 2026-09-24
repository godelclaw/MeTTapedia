import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootDifference
import Mettapedia.Analysis.RootPartitionEnergy

/-!
# Summed weighted derivative energy of the actual root vorticities

Fourth-power normalization controls the patch sum without an additional
cardinality multiplier. The Gaussian temperature, coordinate-projector
derivative, and common gap-factor derivative remain explicit costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnergy

open scoped BigOperators
open MeasureTheory
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.RootPartitionEnergy
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalSpatialVorticityJets
open PancakeHigherDerivativeMoments GaussianRootVorticity GaussianRootDifference

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ae_coordinate_weighted_rootVorticity_energy_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (ht : 0 < tau) (j : Fin 3) :
    let b := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
    let M := fun x : T3 ↦ coordinates (localProjector gamma chi modes u x)
    ∀ᵐ x : T3, ∀ k : ↑centers,
      (∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 2 *
        ‖deriv (fun h ↦ rootVorticity gamma chi modes u centers tau i (x + coordinateShift j h)) 0‖ ^ 2) ≤
      2 * b x ^ 2 * deriv (fun h ↦ b (x + coordinateShift j h)) 0 ^ 2 * ‖fullVorticity u x‖ ^ 4 +
      b x ^ 4 * (‖M x - M k.1‖ ^ 2 + tau * Real.log (Fintype.card ↑centers)) *
        ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j x)‖ ^ 2 *
          ‖fullVorticity u x‖ ^ 4 / (2 * tau ^ 2) +
      8 * b x ^ 4 * ‖fullVorticity u x‖ ^ 2 * ‖fullCurlGradient u j x‖ ^ 2 := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hlS : LocallyLipschitz
      (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  have hb := PancakePeriodicWeakDerivative.ae_coordinate_differentiable
    (fun x ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)) j
    ((locallyLipschitz_rootGapFactor gamma hg).continuous.comp hS)
    ((locallyLipschitz_rootGapFactor gamma hg).comp hlS)
  have hM := LocalSquaredGapGradient.ae_coordinate_differentiable gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) j
  filter_upwards [hb, hM] with x hbx hMx
  intro k
  have hcoord := (coordinates (ι := Fin 3)).hasFDerivAt.comp_hasDerivAt 0 hMx.hasDerivAt
  have hw := hasDerivAt_fullVorticity_shift u hu j x 0
  have h := sum_weighted_rootVorticity_deriv_sq_le
    (fun k : ↑centers ↦ coordinates (localProjector gamma chi modes u k.1)) tau ht
    hbx.hasDerivAt hcoord hw k
  simpa only [rootPatch_eq_factor, rootVorticity_eq_factor, rootFieldFactor, rootAmplitude,
    gaussianFactor, Function.comp_def, PancakeHaarTransportRate.coordinateShift_zero,
    add_zero, LocalSquaredGapGradient.coordinateDerivative] using h

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnergy
