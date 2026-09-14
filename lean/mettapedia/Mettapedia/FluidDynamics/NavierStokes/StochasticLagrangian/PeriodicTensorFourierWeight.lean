import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorFourierFrame

/-!
# Even weights on the projected real Fourier frame

Real Fourier modes interact only at equal or opposite frequencies.
Consequently an even frequency weight commutes with the actual frame
coefficients of an absolutely convergent, possibly repeated-frequency
series. Bessel's inequality then controls the weighted coefficient sum
by the norm of the constructed weighted field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorFourierWeight

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFourierTranslationCurve PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PeriodicGradientFluxSymbol ExchangedFluxModeDynamics PeriodicTensorFourierFrame
open PancakeMisalignmentEnergyBridge

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => TensorL2 (Fin 3) R3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_real_character_mul_eq_zero (n m : Wavevector) (a b : ℂ)
    (hn : n ≠ m) (hm : n ≠ -m) :
    (∫ x : T3, (UnitAddTorus.mFourier n x * a).re *
      (UnitAddTorus.mFourier m x * b).re) = 0 := by
  let f := fun x : T3 ↦ (a * conj b) *
    (UnitAddTorus.mFourier n x * conj (UnitAddTorus.mFourier m x))
  let g := fun x : T3 ↦ (a * b) *
    (UnitAddTorus.mFourier n x * conj (UnitAddTorus.mFourier (-m) x))
  have hf : Integrable f := (by fun_prop : Continuous f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g := (by fun_prop : Continuous g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : (UnitAddTorus.mFourier n x * a).re *
      (UnitAddTorus.mFourier m x * b).re = (f x + g x).re / 2 := by
    simp [f, g, UnitAddTorus.mFourier_neg, Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [he]
  rw [integral_div]
  have hire : (∫ x : T3, (f x + g x).re) = (∫ x : T3, f x + g x).re :=
    integral_re (hf.add hg)
  rw [hire, integral_add hf hg]
  have hf0 : (∫ x, f x) = 0 := by
    simp only [f, integral_const_mul, integral_mFourier_mul_conj_mFourier,
      if_neg hn.symm, mul_zero]
  have hg0 : (∫ x, g x) = 0 := by
    simp only [g, integral_const_mul, integral_mFourier_mul_conj_mFourier,
      if_neg hm.symm, mul_zero]
  rw [hf0, hg0]
  norm_num

theorem integral_inner_realMode_eq_zero (n m : Wavevector) (a b : VelocityCoefficient)
    (hn : n ≠ m) (hm : n ≠ -m) :
    (∫ x : T3, ⟪realMode n a x, realMode m b x⟫) = 0 := by
  have he (x : T3) : ⟪realMode n a x, realMode m b x⟫ =
      ∑ i : Fin 3, (UnitAddTorus.mFourier n x * a i).re *
        (UnitAddTorus.mFourier m x * b i).re := by
    change (∑ i : Fin 3, (realMode m b x) i * (realMode n a x) i) = _
    simp [realMode_apply, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
      modeField, mul_comm]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ ↦
    (by fun_prop : Continuous (fun x : T3 ↦ (UnitAddTorus.mFourier n x * a i).re *
      (UnitAddTorus.mFourier m x * b i).re)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp only [integral_real_character_mul_eq_zero n m _ _ hn hm, Finset.sum_const_zero]

theorem inner_tensorMode_eq_zero (n m : Wavevector) (a b : Fin 3 → VelocityCoefficient)
    (hn : n ≠ m) (hm : n ≠ -m) :
    ⟪tensorModeCLM n a, tensorModeCLM m b⟫ = 0 := by
  rw [tensorModeCLM_apply, tensorModeCLM_apply, inner_toTensorL2]
  rw [integral_finsetSum _ (fun j _ ↦
    ((realMode n (projectedCoeff n a j)).continuous.inner
      (realMode m (projectedCoeff m b j)).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp only [integral_inner_realMode_eq_zero n m _ _ hn hm, Finset.sum_const_zero]

theorem outputCoefficient_tensorMode_eq_zero (n m : Wavevector)
    (a : Fin 3 → VelocityCoefficient) (hn : n ≠ m) (hm : n ≠ -m) :
    outputCoefficient (tensorModeCLM m a) n = 0 := by
  apply ext_inner_left ℝ
  intro b
  rw [inner_zero_right]
  change ⟪b, (synthesis n).adjoint (tensorModeCLM m a)⟫ = 0
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_tensorMode_eq_zero n m (tensorOfVecCLM b) a hn hm

theorem outputCoefficient_weighted_mode (w : Wavevector → ℝ) (hw : ∀ n, w (-n) = w n)
    (n m : Wavevector) (a : Fin 3 → VelocityCoefficient) :
    outputCoefficient (w m • tensorModeCLM m a) n =
      w n • outputCoefficient (tensorModeCLM m a) n := by
  change (synthesis n).adjoint (w m • tensorModeCLM m a) = _
  rw [map_smul]
  by_cases hn : n = m
  · subst n; rfl
  by_cases hm : n = -m
  · subst n; rw [hw]; rfl
  change w m • outputCoefficient (tensorModeCLM m a) n = _
  rw [outputCoefficient_tensorMode_eq_zero n m a hn hm, smul_zero, smul_zero]

theorem outputCoefficient_weighted_series {ι : Type*} (freq : ι → Wavevector)
    (a : ι → Fin 3 → VelocityCoefficient) (w : Wavevector → ℝ)
    (hw : ∀ n, w (-n) = w n)
    (ha : Summable (fun i ↦ tensorModeCLM (freq i) (a i)))
    (hwa : Summable (fun i ↦ w (freq i) • tensorModeCLM (freq i) (a i))) (n : Wavevector) :
    outputCoefficient (∑' i, w (freq i) • tensorModeCLM (freq i) (a i)) n =
      w n • outputCoefficient (∑' i, tensorModeCLM (freq i) (a i)) n := by
  simp only [outputCoefficient, (synthesis n).adjoint.map_tsum hwa,
    (synthesis n).adjoint.map_tsum ha]
  change (∑' i, outputCoefficient (w (freq i) • tensorModeCLM (freq i) (a i)) n) = _
  simp_rw [outputCoefficient_weighted_mode w hw]
  exact tsum_const_smul'' (f := fun i ↦ outputCoefficient (tensorModeCLM (freq i) (a i)) n) (w n)

theorem summable_weighted_outputCoefficient_sq {ι : Type*} (freq : ι → Wavevector)
    (a : ι → Fin 3 → VelocityCoefficient) (w : Wavevector → ℝ)
    (hw : ∀ n, w (-n) = w n)
    (ha : Summable (fun i ↦ tensorModeCLM (freq i) (a i)))
    (hwa : Summable (fun i ↦ w (freq i) • tensorModeCLM (freq i) (a i))) :
    Summable (fun n ↦ ‖w n • outputCoefficient (∑' i, tensorModeCLM (freq i) (a i)) n‖ ^ 2) := by
  simp_rw [← outputCoefficient_weighted_series freq a w hw ha hwa]
  exact summable_norm_outputCoefficient_sq _

theorem tsum_weighted_outputCoefficient_sq_le {ι : Type*} (freq : ι → Wavevector)
    (a : ι → Fin 3 → VelocityCoefficient) (w : Wavevector → ℝ)
    (hw : ∀ n, w (-n) = w n)
    (ha : Summable (fun i ↦ tensorModeCLM (freq i) (a i)))
    (hwa : Summable (fun i ↦ w (freq i) • tensorModeCLM (freq i) (a i))) :
    (∑' n, ‖w n • outputCoefficient (∑' i, tensorModeCLM (freq i) (a i)) n‖ ^ 2) ≤
      ‖∑' i, w (freq i) • tensorModeCLM (freq i) (a i)‖ ^ 2 := by
  simp_rw [← outputCoefficient_weighted_series freq a w hw ha hwa]
  exact tsum_norm_outputCoefficient_sq_le _

end Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorFourierWeight
