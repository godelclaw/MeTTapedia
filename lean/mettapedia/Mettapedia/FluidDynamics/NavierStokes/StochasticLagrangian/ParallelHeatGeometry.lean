import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatWitness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteSupport

/-!
# Physical vorticity and signed correlation channels of parallel flows

Finite Fourier reconstruction identifies the actual spatial velocity gradient
and curl. The strain annihilates vorticity pointwise. The stationary
zero-viscosity solution then shows that the complete nonviscous correlation
mean, including relative kernel transport, vanishes. The remaining corrected
residual is exactly the pure viscous curvature cost.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped BigOperators ComplexConjugate RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakePeriodicVorticityEquation PancakeLocalGradientEquation PancakeLocalStrainEquation
open PancakeDyadicDirectionEvolution PancakeFourierMaterialPaths LocalAlignmentForcing
open PancakeTransverseEnergyFreezing
open LocalLowDiffusionBudget LocalOcticMeanBalance LocalOcticCorrectedEnergy
open FourierFiniteSupport
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem vertical_supported (a : Wavevector →₀ ℂ) (q : Wavevector) (hq : q ∉ a.support) :
    vertical (a q) = 0 := by
  have hz : a q = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hq
  simp [hz]

/-- The finite Fourier polynomial for an ordinary derivative of the scalar profile. -/
def scalarGradient (a : Wavevector →₀ ℂ) (j : Fin 3) (x : T3) : ℂ :=
  ∑ q ∈ a.support, UnitAddTorus.mFourier q x *
    (unitTorusDerivativePhase * (q j : ℂ) * a q)

theorem coordinateDerivative_vertical (a : Wavevector →₀ ℂ) (j i : Fin 3) (x : T3) :
    coordinateDerivative (fullFourierField id (fun q ↦ vertical (a q))) j x i =
      if i = 2 then scalarGradient a j x else 0 := by
  rw [coordinateDerivative_eq_sum a.support _ (vertical_supported a) j x]
  by_cases hi : i = 2 <;>
    simp [indexedDerivativeCoeff, vertical, hi, scalarGradient, mul_assoc]

theorem scalarGradient_vertical_eq_zero (a : Wavevector →₀ ℂ) (ha : IsHorizontal a) (x : T3) :
    scalarGradient a 2 x = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q 2 = 0
  · simp [hq]
  · simp [ha q hq]

/-- The receiver is the ordinary spatial curl of the actual Fourier field. -/
theorem fullVorticity_vertical (a : Wavevector →₀ ℂ) (x : T3) :
    fullVorticity (fun q ↦ vertical (a q)) x =
      WithLp.toLp 2 ![(scalarGradient a 1 x).re, -(scalarGradient a 0 x).re, 0] := by
  ext i
  fin_cases i <;>
    simp [fullVorticity, spatialCurl, coordinateDerivative_vertical,
      complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]

theorem fullStrain_apply_vorticity_eq_zero (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (x : T3) :
    fullStrainOperator (fun q ↦ vertical (a q)) x
      (fullVorticity (fun q ↦ vertical (a q)) x) = 0 := by
  rw [fullVorticity_vertical]
  ext i
  rw [fullStrainOperator, realMatrixOperator_apply]
  fin_cases i <;>
    simp [PancakeLocalStrainEquation.spatialStrain, PancakeFilteredStrainDynamics.symmetrize,
      spatialVelocityGradient, coordinateDerivative_vertical, Fin.sum_univ_three,
      scalarGradient_vertical_eq_zero a ha, Complex.mul_re]
  all_goals ring

theorem stretching_eq_zero (a : Wavevector →₀ ℂ) (ha : IsHorizontal a) :
    LocalVorticityEighthMoment.stretching (fun q ↦ vertical (a q)) = 0 := by
  simp [LocalVorticityEighthMoment.stretching, LocalVorticityEighthMoment.stretchingDensity,
    fullStrain_apply_vorticity_eq_zero a ha]

/-- The evolved finite scalar coefficients, without enlarging the input support. -/
def heatData (ν : ℝ) (a : Wavevector →₀ ℂ) (t : ℝ) : Wavevector →₀ ℂ :=
  Finsupp.onFinset a.support (fun q ↦ (Real.exp (-decayRate ν q * t) : ℂ) * a q)
    (fun q hq ↦ Finsupp.mem_support_iff.mpr (by intro hz; exact hq (by simp [hz])))

@[simp] theorem heatData_apply (ν : ℝ) (a : Wavevector →₀ ℂ) (t : ℝ) (q : Wavevector) :
    heatData ν a t q = (Real.exp (-decayRate ν q * t) : ℂ) * a q := rfl

theorem coefficients_eq_vertical_heatData (ν : ℝ) (a : Wavevector →₀ ℂ) (t : ℝ) :
    coefficients ν a t = fun q ↦ vertical (heatData ν a t q) := rfl

theorem heatData_horizontal (ν : ℝ) (a : Wavevector →₀ ℂ) (ha : IsHorizontal a) (t : ℝ) :
    IsHorizontal (heatData ν a t) := coefficients_horizontal ha ν t

theorem stretching_coefficients_eq_zero (ν : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (t : ℝ) :
    LocalVorticityEighthMoment.stretching (coefficients ν a t) = 0 :=
  stretching_eq_zero (heatData ν a t) (heatData_horizontal ν a ha t)

@[simp] theorem coefficients_zero_viscosity (a : Wavevector → ℂ) (t : ℝ) :
    coefficients 0 a t = fun q ↦ vertical (a q) := by
  ext q i
  simp [coefficients, decayRate]

/-- Both endpoint stretching and the complete relative kernel transport have
zero spatial mean. This follows from the checked balance on the stationary
Euler member of the same exact solution family, not by dropping transport. -/
theorem nonviscousMeanRate_eq_zero (a : Wavevector →₀ ℂ) (ha : IsHorizontal a)
    (hr : ∀ q, a (-q) = conj (a q)) (hz : a 0 = 0) (N : ℕ) :
    meanRate N 0 (fun q ↦ vertical (a q)) = 0 := by
  let s := solution (ν := 0) le_rfl a ha hr hz 3
  have hI : Set.Icc (1 : ℝ) 2 ⊆ Set.Ioo (0 : ℝ) 3 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have h := (integral_meanRate_eq s 1 2 (by norm_num) hI
    (fourierMoment 3 (fun q ↦ vertical (a q))) (fourierMoment_nonneg _ _)
    (summable_initial_fourierMoment 3 a)
    (fun _ hτ ↦ fourierMoment_le_initial (ν := 0) le_rfl hτ.1 3 a) N).2
  norm_num [s, solution, coefficients_zero_viscosity] at h
  exact h

theorem residual_eq_neg_pure_curvature (a : Wavevector →₀ ℂ) (ha : IsHorizontal a)
    (hr : ∀ q, a (-q) = conj (a q)) (hz : a 0 = 0) (N : ℕ) (ν ε : ℝ) :
    LocalOcticCorrectedEnergy.residual N ν ε (fun q ↦ vertical (a q)) =
      -(ε * ν) * LocalOcticDiffusion.pureContribution N (fun q ↦ vertical (a q)) := by
  rw [LocalOcticCorrectedEnergy.residual, stretching_eq_zero a ha,
    nonviscousMeanRate_eq_zero a ha hr hz]
  ring

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
