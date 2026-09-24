import Mettapedia.Analysis.HilbertSynthesisBound
import Mettapedia.Analysis.UnitTorusPolynomialEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjoint

/-!
# The actual projected tensor Fourier frame

Finite Fourier synthesis is contractive from the coefficient square norm
to real tensor L², including the gradient projection. Consequently the
square sum of the constructed output-frequency adjoints is bounded by
one spatial energy, with no frequency-count factor.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorFourierFrame

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFourierTranslationCurve PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PeriodicGradientFluxSymbol ExchangedFluxModeDynamics

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => TensorL2 (Fin 3) R3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev TensorCoefficientSpace := EuclideanSpace ℂ (Fin 3 × Fin 3)

def tensorOfVecCLM : TensorCoefficientSpace →L[ℂ] (Fin 3 → VelocityCoefficient) :=
  ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj (j, i)))

def synthesis (n : Wavevector) : TensorCoefficientSpace →L[ℝ] H :=
  (tensorModeCLM n).comp (tensorOfVecCLM.restrictScalars ℝ)

def outputCoefficient (F : H) (n : Wavevector) : TensorCoefficientSpace := (synthesis n).adjoint F

theorem realMode_sum_coordinate (P : Finset Wavevector) (a : Wavevector → VelocityCoefficient)
    (x : T3) (i : Fin 3) :
    (∑ n ∈ P, realMode n (a n) x) i =
      (UnitTorusFourierUniqueness.polynomial P (fun n ↦ a n i) x).re := by
  change (EuclideanSpace.proj i : R3 →L[ℝ] ℝ) (∑ n ∈ P, realMode n (a n) x) = _
  rw [map_sum]
  change (∑ n ∈ P, (realMode n (a n) x) i) = _
  simp [realMode_apply, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    modeField, UnitTorusFourierUniqueness.polynomial_apply]

theorem integral_norm_realMode_sum_sq_le (P : Finset Wavevector)
    (a : Wavevector → VelocityCoefficient) :
    (∫ x : T3, ‖∑ n ∈ P, realMode n (a n) x‖ ^ 2) ≤
      ∑ n ∈ P, ∑ i : Fin 3, ‖a n i‖ ^ 2 := by
  let f : Fin 3 → C(T3, ℂ) := fun i ↦ UnitTorusFourierUniqueness.polynomial P (fun n ↦ a n i)
  have h (x : T3) : ‖∑ n ∈ P, realMode n (a n) x‖ ^ 2 ≤ ∑ i, ‖f i x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i hi
    rw [realMode_sum_coordinate]
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (f i x)) 2
  have hf (i : Fin 3) : Integrable (fun x : T3 ↦ ‖f i x‖ ^ 2) :=
    ((f i).continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun x : T3 ↦ ‖∑ n ∈ P, realMode n (a n) x‖ ^ 2) :=
    ((continuous_finsetSum _ (fun n _ ↦ (realMode n (a n)).continuous)).norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : T3, ∑ i, ‖f i x‖ ^ 2 := integral_mono hl (integrable_finsetSum _ (fun i _ ↦ hf i)) h
    _ = ∑ i, ∫ x : T3, ‖f i x‖ ^ 2 := integral_finsetSum _ (fun i _ ↦ hf i)
    _ = ∑ i : Fin 3, ∑ n ∈ P, ‖a n i‖ ^ 2 := by
      exact Finset.sum_congr rfl (fun i _ ↦ UnitTorusPolynomialEnergy.integral_norm_polynomial_sq P _)
    _ = _ := Finset.sum_comm

theorem sum_synthesis_eq (P : Finset Wavevector) (a : Wavevector → TensorCoefficientSpace) :
    (∑ n ∈ P, synthesis n (a n)) =
      gradientProjection (toTensorL2 (fun j ↦ ∑ n ∈ P, realMode n (tensorOfVecCLM (a n) j))) := by
  change (∑ n ∈ P, (gradientProjectionCLM (d := Fin 3) (E := R3))
    ((tensorEmbedding (d := Fin 3) (E := R3))
      (fun j ↦ realMode n (tensorOfVecCLM (a n) j)))) = _
  rw [← map_sum, ← map_sum]
  apply congrArg (gradientProjectionCLM (d := Fin 3) (E := R3))
  apply congrArg (tensorEmbedding (d := Fin 3) (E := R3))
  funext j
  exact Finset.sum_apply _ _ _

theorem norm_sum_synthesis_sq_le (P : Finset Wavevector) (a : Wavevector → TensorCoefficientSpace) :
    ‖∑ n ∈ P, synthesis n (a n)‖ ^ 2 ≤ ∑ n ∈ P, ‖a n‖ ^ 2 := by
  rw [sum_synthesis_eq]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_gradientProjection_le _) 2).trans
  rw [norm_toTensorL2_sq]
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦
      ‖(∑ n ∈ P, realMode n (tensorOfVecCLM (a n) j)) x‖ ^ 2) :=
    (((∑ n ∈ P, realMode n (tensorOfVecCLM (a n) j))).continuous.norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  calc
    _ ≤ ∑ j : Fin 3, ∑ n ∈ P, ∑ i : Fin 3, ‖tensorOfVecCLM (a n) j i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [ContinuousMap.sum_apply] using integral_norm_realMode_sum_sq_le P
        (fun n ↦ tensorOfVecCLM (a n) j)
    _ = ∑ n ∈ P, ‖a n‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
      rfl

theorem sum_norm_outputCoefficient_sq_le (F : H) (P : Finset Wavevector) :
    (∑ n ∈ P, ‖outputCoefficient F n‖ ^ 2) ≤ ‖F‖ ^ 2 := by
  simpa only [outputCoefficient, one_mul] using HilbertSynthesisBound.sum_norm_adjoint_sq_le synthesis P 1
    (by norm_num) (fun a ↦ (norm_sum_synthesis_sq_le P a).trans_eq (one_mul _).symm) F

theorem summable_norm_outputCoefficient_sq (F : H) :
    Summable (fun n ↦ ‖outputCoefficient F n‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_norm_outputCoefficient_sq_le F)

theorem tsum_norm_outputCoefficient_sq_le (F : H) :
    (∑' n, ‖outputCoefficient F n‖ ^ 2) ≤ ‖F‖ ^ 2 :=
  (summable_norm_outputCoefficient_sq F).tsum_le_of_sum_le (sum_norm_outputCoefficient_sq_le F)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorFourierFrame
