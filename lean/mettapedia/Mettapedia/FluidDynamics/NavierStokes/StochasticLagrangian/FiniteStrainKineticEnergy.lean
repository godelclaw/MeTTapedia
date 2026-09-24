import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierStrainGradient

/-!
# Fixed-output strain bounds from full kinetic energy

The strain operator and its first spatial derivative are bounded by explicit
finite frequency weights and the full input kinetic energy. The input need
not have finite support. These constants depend on the fixed source modes,
not on a separate retained vorticity cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy

open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFourierStrainGradient
open PancakeFilteredStrainDynamics PancakeIncomingLowSourceEnergy InfiniteConvectionEnergy
open PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)

def strainWeight (q : Wavevector) : ℝ :=
  9 * ‖unitTorusDerivativePhase‖ * ‖frequencyVec q‖

def strainEnergyBound (Q : Finset Wavevector) (E : ℝ) : ℝ :=
  Real.sqrt ((∑ q ∈ Q, strainWeight q ^ 2) * E)

def strainGradientEnergyBound (Q : Finset Wavevector) (E : ℝ) : ℝ :=
  Real.sqrt ((∑ q ∈ Q, strainGradientWeight (fun _ ↦ 1) q ^ 2) * E)

theorem strainEnergyBound_nonneg (Q : Finset Wavevector) (E : ℝ) :
    0 ≤ strainEnergyBound Q E := Real.sqrt_nonneg _

theorem strainGradientEnergyBound_nonneg (Q : Finset Wavevector) (E : ℝ) :
    0 ≤ strainGradientEnergyBound Q E := Real.sqrt_nonneg _

theorem sum_weight_norm_le_sqrt_kineticEnergy (Q : Finset Wavevector) (w : Wavevector → ℝ)
    (u : FourierVelocity) (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E) :
    (∑ q ∈ Q, w q * ‖coefficientVec (u q)‖) ≤ Real.sqrt ((∑ q ∈ Q, w q ^ 2) * E) := by
  have hw : 0 ≤ ∑ q ∈ Q, w q ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Q w (fun q ↦ ‖coefficientVec (u q)‖)
  have hsum := mul_le_mul_of_nonneg_left
    ((hu.sum_le_tsum Q (fun _ _ ↦ sq_nonneg _)).trans hE) hw
  have hnonneg : 0 ≤ E := (LocalKineticEnergy.kineticEnergy_nonneg u).trans hE
  have hsqrt := Real.sq_sqrt (mul_nonneg hw hnonneg)
  have hpos := Real.sqrt_nonneg ((∑ q ∈ Q, w q ^ 2) * E)
  nlinarith only [hsq, hsum, hsqrt, hpos]

theorem norm_spatialStrain_le_weighted_sum (Q : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    ‖(spatialStrain Q u x).1‖ ≤ ∑ q ∈ Q, strainWeight q * ‖coefficientVec (u q)‖ := by
  apply (norm_realMatrixOperator_le (matrixReconstruction Q (strainCoeff u) x)).trans
  calc
    _ ≤ 9 * (∑ q ∈ Q, ‖strainCoeff u q‖) := by
      gcongr
      exact norm_matrixReconstruction_le _ _ _
    _ ≤ 9 * (∑ q ∈ Q,
        ‖unitTorusDerivativePhase‖ * ‖frequencyVec q‖ * ‖coefficientVec (u q)‖) := by
      gcongr with q hq
      exact norm_strainCoeff_le u q
    _ = _ := by
      simp only [Finset.mul_sum, strainWeight]
      apply Finset.sum_congr rfl
      intro q _
      ring

theorem norm_spatialStrain_le_energyBound (Q : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E) (x : T3) :
    ‖(spatialStrain Q u x).1‖ ≤ strainEnergyBound Q E :=
  (norm_spatialStrain_le_weighted_sum Q u x).trans
    (sum_weight_norm_le_sqrt_kineticEnergy Q strainWeight u hu E hE)

theorem norm_strainGradient_le_energyBound (Q : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E) (x : T3) (j : Fin 3) :
    ‖strainGradient Q u x j‖ ≤ strainGradientEnergyBound Q E := by
  have hb := norm_strainGradient_le_amplitude Q (fun _ ↦ 1) u x j
  have he : filteredVelocity (fun _ ↦ 1) u = u := by
    funext q
    exact one_smul ℂ (u q)
  rw [he] at hb
  exact hb.trans (sum_weight_norm_le_sqrt_kineticEnergy Q
    (strainGradientWeight (fun _ ↦ 1)) u hu E hE)

end Mettapedia.FluidDynamics.NavierStokes.FiniteStrainKineticEnergy
