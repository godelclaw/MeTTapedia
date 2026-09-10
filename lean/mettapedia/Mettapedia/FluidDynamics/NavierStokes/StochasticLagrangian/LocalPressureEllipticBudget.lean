import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierEllipticProductEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSquaredGapPressure

/-!
# Physical pressure-patch budgets with explicit derivative costs

The pressure potential and its first coordinate multipliers have actual
continuous-field supremum norms. Substituting them in the elliptic
commutator estimate removes its cutoff Wiener moment. The resulting
first- and second-coordinate cutoff energies remain unpaid dynamical
costs. No uniform bound in the pressure truncation or gap threshold is
claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPressureEllipticBudget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeCurlOutputTail PancakeAnisotropyDepletion
open FourierPressureEllipticCommutator FourierEllipticProductCoefficients FourierEllipticProductEnergy
open FourierPressureLocalization FourierPressureTiltEnergy PressureTracePatchEnergy LocalSquaredGapPressure

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def potentialField (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) : C(T3, ℂ) :=
  ⟨finiteScalarFourierReconstruction K (potentialAmplitude chi u),
    continuous_finiteScalarFourierReconstruction _ _⟩

def potentialCoordinateField (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) : C(T3, ℂ) :=
  ⟨finiteScalarFourierReconstruction K (coordinateMultiplier (potentialAmplitude chi u) j),
    continuous_finiteScalarFourierReconstruction _ _⟩

def potentialCoordinateBound (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∑ j : Fin 3, ‖potentialCoordinateField chi K u j‖

theorem norm_potentialCoordinateField_apply_le (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    ‖potentialCoordinateField chi K u j x‖ ≤ potentialCoordinateBound chi K u :=
  ((potentialCoordinateField chi K u j).norm_coe_le_norm x).trans
    (Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j))

theorem tiltCommutatorEnergy_le_derivative_cost (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (K : Finset Wavevector) (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1) :
    tiltCommutatorEnergy c chi K u e ≤
      192 * potentialCoordinateBound chi K u ^ 2 * coordinateEnergy c.support c +
        36 * ‖potentialField chi K u‖ ^ 2 * secondCoordinateEnergy c.support c :=
  FourierEllipticProductEnergy.tiltCommutatorEnergy_le c chi K u e he _ _
    (fun x ↦ (potentialField chi K u).norm_coe_le_norm x)
    (norm_potentialCoordinateField_apply_le chi K u)

theorem exists_pressure_elliptic_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    let a := localWeight gamma chi modes u
    let e := fun x ↦ topVector (spatialStrain modes (filteredVelocity chi u) x)
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ (K : Finset Wavevector), (∀ q, -q ∈ K ↔ q ∈ K) →
        ∀ eta : ℝ, 0 ≤ eta →
        (∫ x : T3, a x *
          ‖lineRemainder (e x) (LocalPressureCommutator.filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
            4 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
              4 * (∑ i, tiltTailTraceEnergy (c i) chi K u (e i.1) eta) +
              768 * potentialCoordinateBound chi K u ^ 2 * (∑ i, coordinateEnergy (c i).support (c i)) +
              144 * ‖potentialField chi K u‖ ^ 2 * (∑ i, secondCoordinateEnergy (c i).support (c i)) +
              (32 * rho ^ 2 + 2 * delta + 4 * eta ^ 2 * delta) * hessianEnergy chi K u := by
  dsimp only
  obtain ⟨centers, c, hcover, hbudget⟩ := exists_pressure_angular_budget gamma hg chi modes u hu rho delta hr hd
  refine ⟨centers, c, hcover, ?_⟩
  intro K hK eta heta
  have h := hbudget K hK eta heta
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ↑centers)) ↦
    tiltCommutatorEnergy_le_derivative_cost (c i) chi K u
      (topVector (spatialStrain modes (filteredVelocity chi u) i.1)) (topVector_norm _))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hc
  linarith only [h, hc]

end Mettapedia.FluidDynamics.NavierStokes.LocalPressureEllipticBudget
