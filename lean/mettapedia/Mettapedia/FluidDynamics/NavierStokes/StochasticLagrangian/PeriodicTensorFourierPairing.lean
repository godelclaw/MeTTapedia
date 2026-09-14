import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorFourierWeight

/-!
# Exact pairings of projected real Fourier tensor modes

Equal and opposite outputs are retained separately, including the zero
mode where both conditions hold. This reduces the actual Hilbert-space
pairing to finite coefficient algebra, without a norm relaxation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorFourierPairing

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFourierTranslationCurve PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PeriodicGradientFluxSymbol ExchangedFluxModeDynamics PeriodicTensorFourierFrame
open PancakeMisalignmentEnergyBridge

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_real_character_mul (n m : Wavevector) (a b : ℂ) :
    (∫ x : T3, (UnitAddTorus.mFourier n x * a).re *
      (UnitAddTorus.mFourier m x * b).re) =
      ((if n = m then (a * conj b).re else 0) +
        (if n = -m then (a * b).re else 0)) / 2 := by
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
  simp only [f, g, integral_const_mul, integral_mFourier_mul_conj_mFourier]
  simp only [mul_one, mul_zero, Complex.add_re, apply_ite, Complex.zero_re,
    eq_comm]

theorem integral_inner_realMode (n m : Wavevector) (a b : VelocityCoefficient) :
    (∫ x : T3, ⟪realMode n a x, realMode m b x⟫) =
      ∑ i : Fin 3, ((if n = m then (a i * conj (b i)).re else 0) +
        (if n = -m then (a i * b i).re else 0)) / 2 := by
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
  simp only [integral_real_character_mul]

theorem inner_tensorMode (n m : Wavevector) (a b : Fin 3 → VelocityCoefficient) :
    ⟪tensorModeCLM n a, tensorModeCLM m b⟫ =
      ∑ j : Fin 3, ∑ i : Fin 3,
        ((if n = m then (projectedCoeff n a j i * conj (projectedCoeff m b j i)).re else 0) +
          (if n = -m then (projectedCoeff n a j i * projectedCoeff m b j i).re else 0)) / 2 := by
  rw [tensorModeCLM_apply, tensorModeCLM_apply, inner_toTensorL2]
  rw [integral_finsetSum _ (fun j _ ↦
    ((realMode n (projectedCoeff n a j)).continuous.inner
      (realMode m (projectedCoeff m b j)).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp only [integral_inner_realMode]

end Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorFourierPairing
