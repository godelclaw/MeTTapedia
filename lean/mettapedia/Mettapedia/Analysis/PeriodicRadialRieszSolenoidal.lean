import Mettapedia.Analysis.PeriodicRadialRieszEvolution
import Mettapedia.Analysis.UnitTorusIntegrableConvolution

/-!
# Solenoidal cancellation for the regularized radial Riesz tensor

The tensor multiplier is longitudinal. It annihilates a field with transverse
Fourier coefficients, including the real part of a complex Fourier series.
The result concerns the complete periodic tensor, not an angular truncation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRadialRiesz

open MeasureTheory UnitTorusLattice
open scoped RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem tensor_neg (N : ℕ) (q : Td) : tensor N (-q) = tensor N q :=
  congrFun (Measure.eq_of_ae_eq (tensor_neg_ae N)
    ((continuous_tensor N).comp continuous_neg) (continuous_tensor N)) q

theorem integral_re_entry_eq_zero (N : ℕ) (i j : Fin d) :
    (∫ q : Td, (entry N i j q).re) = 0 := by
  have h := mFourierCoeff_re_entry N i j (0 : Fin d → ℤ)
  simp only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul, integral_complex_ofReal] at h
  simpa [frequency, AnnularRieszKernel.rieszEntry] using congrArg Complex.re h

theorem integral_tensor_eq_zero (N : ℕ) : (∫ q : Td, tensor N q) = 0 := by
  have hi (i j : Fin d) : Integrable (fun q : Td ↦ (entry N i j q).re •
      PeriodicRieszOperator.basisOperator i j) :=
    ((integrable_entry N i j).re).smul_const _
  simp only [tensor]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j), integral_smul_const,
    integral_re_entry_eq_zero, zero_smul, Finset.sum_const_zero]

theorem sum_symbol_mul_eq_zero (N : ℕ) (i : Fin d) (k : Fin d → ℤ)
    (a : Fin d → ℂ) (ha : ∑ j : Fin d, (k j : ℂ) * a j = 0) :
    (∑ j : Fin d,
      ((RadialRieszRegularization.weight N (frequency k) *
        AnnularRieszKernel.rieszEntry i j (frequency k) : ℝ) : ℂ) * a j) = 0 := by
  calc
    _ = ((RadialRieszRegularization.weight N (frequency k) : ℂ) * (k i : ℂ) /
        (‖frequency k‖ ^ 2 : ℝ)) * ∑ j : Fin d, (k j : ℂ) * a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [AnnularRieszKernel.rieszEntry, frequency,
        Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast]
      ring
    _ = 0 := by rw [ha, mul_zero]

theorem integral_tensor_realPart_eq_zero (N : ℕ) (f : Fin d → C(Td, ℂ))
    (a : (Fin d → ℤ) → Fin d → ℂ)
    (ha : ∀ j, HasSum (fun k ↦ a k j • UnitAddTorus.mFourier k) (f j))
    (hd : ∀ k, ∑ j : Fin d, (k j : ℂ) * a k j = 0)
    (g : Td → Rd) (hg : Continuous g) (hr : ∀ j x, (f j x).re = g x j) (x : Td) :
    (∫ h : Td, tensor N h (g (x - h))) = 0 := by
  have hs (i j : Fin d) := UnitTorusIntegrableConvolution.hasSum_convolution
    (fun h ↦ ((entry N i j h).re : ℂ)) (integrable_entry N i j).re.ofReal
    (f j) (fun k ↦ a k j) (ha j) x
  have hz (i : Fin d) : (∑ j : Fin d,
      ∫ h : Td, ((entry N i j h).re : ℂ) * f j (x - h)) = 0 := by
    have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin d))) (fun j _ ↦ hs i j)
    have he (k : Fin d → ℤ) :
        (∑ j : Fin d, UnitAddTorus.mFourierCoeff
          (fun h ↦ ((entry N i j h).re : ℂ)) k * UnitAddTorus.mFourier k x * a k j) = 0 := by
      simp only [mFourierCoeff_re_entry]
      calc
        _ = (∑ j : Fin d, ((RadialRieszRegularization.weight N (frequency k) *
            AnnularRieszKernel.rieszEntry i j (frequency k) : ℝ) : ℂ) * a k j) *
              UnitAddTorus.mFourier k x := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [sum_symbol_mul_eq_zero N i k (a k) (hd k), zero_mul]
    simp_rw [he] at hsum
    exact hsum.unique (hasSum_zero)
  have hi : Integrable (fun h : Td ↦ tensor N h (g (x - h))) := by
    have hc : Continuous (fun h : Td ↦ tensor N h (g (x - h))) :=
      (continuous_tensor N).clm_apply (hg.comp (continuous_const.sub continuous_id))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hij (i j : Fin d) : Integrable (fun h : Td ↦ ((entry N i j h).re : ℂ) * f j (x - h)) :=
    IntegrableKernelPairing.integrable_mul volume _ (integrable_entry N i j).re.ofReal
      ⟨fun h ↦ f j (x - h), (f j).continuous.comp (continuous_const.sub continuous_id)⟩
  ext i
  have hp := (EuclideanSpace.proj i).integral_comp_comm hi
  change (∫ h : Td, (tensor N h (g (x - h))) i) =
    (∫ h : Td, tensor N h (g (x - h))) i at hp
  rw [← hp]
  have he := congrArg Complex.re (hz i)
  have hre (j : Fin d) :
      (∫ h : Td, ((entry N i j h).re : ℂ) * f j (x - h)).re =
        ∫ h : Td, (entry N i j h).re * g (x - h) j := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hr] using
      (Complex.reCLM.integral_comp_comm (hij i j)).symm
  simp only [Complex.re_sum, Complex.zero_re, hre] at he
  simp only [tensor_apply_component]
  rw [integral_finsetSum _ (fun j _ ↦ by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hr] using
      Complex.reCLM.integrable_comp (hij i j))]
  exact he

end Mettapedia.Analysis.PeriodicRadialRiesz
