import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicityAngularSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatGeometry

/-!
# Tests for the actual helicity source and its angular cancellation

Finite horizontal parallel flows test the full Fourier source, not an
independently prescribed vector. The separate algebra tests distinguish
parallel and transverse derivatives without claiming to construct a solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.HelicitySourceTests

open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch PancakeGalerkinKineticEnergy
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open LocalSpatialVorticityJets LocalLowDiffusionBudget LocalWeightedCurlCancellation
open HelicityAngularSource ParallelHeatFlow
open Mettapedia.Analysis.EuclideanCrossProduct

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem parallel_componentGradient_zero (a : Wavevector →₀ ℂ) (x : T3)
    (m : Fin 3) (hm : m ≠ 2) : realComponentGradient (fun q ↦ vertical (a q)) m x = 0 := by
  have he : componentGradient (fun q ↦ vertical (a q)) m x = 0 := by
    ext j
    simp [componentGradient, coordinateDerivative_vertical, hm]
  unfold realComponentGradient
  rw [he]
  exact map_zero _

theorem parallel_verticalCurlGradient_zero (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (x : T3) : fullCurlGradient (fun q ↦ vertical (a q)) 2 x = 0 := by
  have he : indexedDerivativeCoeff id 2 (fourierCurl (fun q ↦ vertical (a q))) = 0 := by
    ext q i
    by_cases hq : q 2 = 0
    · simp [indexedDerivativeCoeff, hq]
    · fin_cases i <;> simp [indexedDerivativeCoeff, fourierCurl, ha q hq, coefficientCross]
  have hF : fullFourierField id (0 : FourierVelocity) = 0 := by
    have hm (q : Wavevector) : PancakeFourierTranslationCurve.modeField q (0 : VelocityCoefficient) = 0 := by
      ext y i
      simp [PancakeFourierTranslationCurve.modeField]
    change (∑' q : Wavevector, PancakeFourierTranslationCurve.modeField q (0 : VelocityCoefficient)) = 0
    simp only [hm, tsum_zero]
  unfold fullCurlGradient
  rw [he, hF]
  exact map_zero _

/-- This vanishing applies to the exact parallel heat-flow family. It is
not a universal vanishing claim for the material helicity source. -/
theorem source_parallel_eq_zero (a : Wavevector →₀ ℂ) (ha : IsHorizontal a)
    (hr : ∀ q, a (-q) = conj (a q)) (x : T3) :
    LocalHelicitySourceEvolution.source (fun q ↦ vertical (a q)) x = 0 := by
  have hre (q : Wavevector) : vertical (a (-q)) = PancakeBlockReality.coefficientConjugate (vertical (a q)) := by
    rw [hr, vertical_conj]
  rw [source_eq_cross _ (summable_initial_fourierMoment 2 a) (transverse ha) hre]
  simp only [Fin.sum_univ_three, parallel_componentGradient_zero a x 0 (by decide),
    parallel_componentGradient_zero a x 1 (by decide), parallel_verticalCurlGradient_zero a ha,
    zero_cross, cross_zero, add_zero, smul_zero, neg_zero]

theorem source_heatCoefficients_eq_zero (ν : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) (t : ℝ) (x : T3) :
    LocalHelicitySourceEvolution.source (coefficients ν a t) x = 0 := by
  rw [coefficients_eq_vertical_heatData]
  apply source_parallel_eq_zero _ (heatData_horizontal ν a ha t)
  intro q
  simp only [heatData_apply, decayRate_neg, map_mul, Complex.conj_ofReal, hr]

theorem parallel_angular_pairing_zero (a g : R3) (c : ℝ) :
    ⟪g, cross a (c • a)⟫ = 0 := by
  simp [cross_smul_right]

/-- The angular pairing has no universal sign, even at the algebraic level. -/
theorem angular_pairing_both_signs :
    ∃ a g d : R3, ⟪g, cross a d⟫ = 1 ∧ ⟪g, cross a (-d)⟫ = -1 := by
  refine ⟨WithLp.toLp 2 ![1, 0, 0], WithLp.toLp 2 ![0, 0, 1], WithLp.toLp 2 ![0, 1, 0], ?_⟩
  norm_num [cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  change (1 : ℝ) * 1 = 1 ∧ (-1 : ℝ) * 1 = -1
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.HelicitySourceTests
