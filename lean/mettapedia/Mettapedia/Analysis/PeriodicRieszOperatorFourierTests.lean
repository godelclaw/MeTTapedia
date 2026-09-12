import Mettapedia.Analysis.PeriodicRieszOperatorFourier
import Mettapedia.Analysis.UnitTorusIntegrableConvolution
import Mettapedia.Analysis.SignedCrossKernelIntegrable

/-! Real-even coefficients, zero modes, and integrable-kernel regression checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszOperatorFourierTests

open MeasureTheory UnitAddTorus Mettapedia.Analysis
open scoped ComplexConjugate
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (i j : Fin 3) (N : ℕ) :
    mFourierCoeff (fun x ↦ (PeriodicRieszOperator.entryKernel i j N x : ℂ)) 0 = 0 := by
  simp [PeriodicRieszOperator.mFourierCoeff_entryKernel,
    UnitTorusLattice.frequency, AnnularRieszKernel.rieszEntry]

example {d : ℕ} (N : ℕ) (x : UnitAddTorus (Fin d)) (a : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (PeriodicRieszOperator.kernel N x a) i =
      ∑ j : Fin d, PeriodicRieszOperator.entryKernel i j N x * a j :=
  PeriodicRieszOperator.kernel_apply_component N x a i

example (f : T3 → ℂ) (hf : Integrable f) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x ↦ ((f x).re : ℂ)) k =
      (mFourierCoeff f k + conj (mFourierCoeff f (-k))) / 2 :=
  UnitTorusFourierReal.mFourierCoeff_realPart f hf k

example (K : T3 → ℂ) (hK : Integrable K) (f : C(T3, ℂ))
    (a : (Fin 3 → ℤ) → ℂ) (ha : HasSum (fun k ↦ a k • mFourier k) f) (x : T3) :
    HasSum (fun k ↦ mFourierCoeff K k * mFourier k x * a k)
      (∫ h : T3, K h * f (x - h)) :=
  UnitTorusIntegrableConvolution.hasSum_convolution K hK f a ha x

#print axioms Mettapedia.Analysis.IntegrableKernelPairing.integrable_mul
#print axioms Mettapedia.Analysis.IntegrableKernelPairing.norm_pairingLinear_le
#print axioms Mettapedia.Analysis.UnitTorusFourierReal.mFourierCoeff_conj
#print axioms Mettapedia.Analysis.UnitTorusFourierReal.mFourierCoeff_comp_neg
#print axioms Mettapedia.Analysis.UnitTorusFourierReal.mFourierCoeff_realPart
#print axioms Mettapedia.Analysis.UnitTorusFourierReal.mFourierCoeff_realEvenPart_of_coefficients
#print axioms Mettapedia.Analysis.UnitTorusIntegrableConvolution.hasSum_convolution
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.mFourierCoeff_entryKernel
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.kernel_eq_sum_entryKernel
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.kernel_apply_component
#print axioms Mettapedia.Analysis.SignedCrossKernel.integral_weightedStretch_eq_half_pair_of_integrable
#print axioms Mettapedia.Analysis.SignedCrossKernel.abs_integral_paired_sub_high_le_of_integrable

end Mettapedia.Analysis.PeriodicRieszOperatorFourierTests
