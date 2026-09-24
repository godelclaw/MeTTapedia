import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedPressureAngularBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedPressurePatch

/-!
# The angular pressure budget for the actual vorticity and strain

The scalar weight, expanding lines and pressure all come from the same
velocity. A single constructed patch family works for every finite
negation-closed pressure truncation and every angular threshold.
Spectral collisions, angular tails and commutators are not assumed away.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPressureAngularBudget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeFourierMaterialPaths
open PancakeHigherDerivativeMoments PancakeSpectralFiniteDifference
open PancakeCurlOutputTail
open PancakeFilteredStrainDynamics PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeAnisotropyDepletion SpectralGapTiltWeight LocalWeightedPressurePatch
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressureLocalization PressureTracePatchEnergy
open LocalPressureCommutator LocalLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_local_pressure_angular_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    let a := localTiltWeight gamma chi modes u
    let e := fun x ↦ topVector (spatialStrain modes (filteredVelocity chi u) x)
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ (outputs : Finset Wavevector), (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        ∀ eta : ℝ, 0 ≤ eta →
        (∫ x : T3, a x *
          ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
            4 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi outputs u x ^ 2) +
              4 * (∑ i, tiltTailTraceEnergy (c i) chi outputs u (e i.1) eta) +
              4 * (∑ i, tiltCommutatorEnergy (c i) chi outputs u (e i.1)) +
              (32 * rho ^ 2 + 2 * delta + 4 * eta ^ 2 * delta) * hessianEnergy chi outputs u := by
  dsimp only
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hw := continuous_fullVorticity u hu
  obtain ⟨centers, c, hmass, henergy⟩ :=
    WeightedPressureAngularBudget.exists_weighted_pressure_angular_budget
      (localTiltWeight gamma chi modes u) (continuous_localTiltWeight gamma hg chi modes u hu)
      (fun _ ↦ tiltWeight_nonneg _ _ _) _ (fun _ ↦ topVector_norm _)
      (continuous_weighted_projector gamma hg _ _ hS hw) rho delta hr hd
  exact ⟨centers, c, hmass, fun outputs hs eta heta ↦ henergy chi outputs u hs eta heta⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalPressureAngularBudget
