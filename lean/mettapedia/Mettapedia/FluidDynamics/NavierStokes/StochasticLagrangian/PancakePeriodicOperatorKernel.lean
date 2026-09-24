import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicCoherentSplit
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Periodic operator kernels for the coherent pancake multiplier

This module supplies the exact torus-side transference interface missing from
the Euclidean anisotropic kernel calculation.  An operator kernel on the unit
three-torus acts by convolution, preserves the receiver `L∞` endpoint with
its operator-norm `L¹` mass, and acts on a Fourier monomial by its genuine
multivariate Fourier coefficient.

Consequently a kernel whose Fourier coefficients equal a proposed receiver
symbol realizes that multiplier exactly on every finite Fourier field.  The
lower-bound section also shows that a projection fixing a unit mode cannot
itself have aperture-small `L¹` mass.  The route's small factor must therefore
be built into the bilinear stretching symbol before the endpoint kernel
estimate is invoked.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakePeriodicOperatorKernel

open MeasureTheory
open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Torus3 := UnitAddTorus (Fin 3)

/-- Convolution action of a complex-linear operator kernel on the unit
three-torus. -/
def torusOperatorKernelAction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (K : Torus3 → (E →L[ℂ] E)) (f : Torus3 → E) (x : Torus3) : E :=
  ∫ y, K y (f (x - y))

/-- Periodic endpoint Young inequality. -/
theorem norm_torusOperatorKernelAction_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Torus3 → (E →L[ℂ] E)) (f : Torus3 → E) (x : Torus3) (M : ℝ)
    (hK : Integrable K) (hKc : Continuous K)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M) :
    ‖torusOperatorKernelAction K f x‖ ≤ (∫ y, ‖K y‖) * M := by
  have hcont : Continuous (fun y : Torus3 ↦ K y (f (x - y))) := by
    fun_prop
  have hdom : Integrable (fun y : Torus3 ↦ ‖K y‖ * M) :=
    hK.norm.mul_const M
  have hint : Integrable (fun y : Torus3 ↦ K y (f (x - y))) := by
    apply hdom.mono' hcont.aestronglyMeasurable
    filter_upwards with y
    exact (K y).le_opNorm_of_le (hfb _)
  unfold torusOperatorKernelAction
  calc
    ‖∫ y : Torus3, K y (f (x - y))‖ ≤
        ∫ y : Torus3, ‖K y (f (x - y))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : Torus3, ‖K y‖ * M := by
      apply integral_mono hint.norm hdom
      intro y
      exact (K y).le_opNorm_of_le (hfb _)
    _ = (∫ y : Torus3, ‖K y‖) * M := integral_mul_const M _

theorem mFourier_sub_apply (k : Wavevector) (x y : Torus3) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.sub_apply,
    fourier_apply, zsmul_sub]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Circle.coe_mul, ← AddCircle.toCircle_add]
  congr 2
  rw [Pi.neg_apply, neg_zsmul, sub_eq_add_neg]

/-- Integral orthogonality of the multivariate torus characters against the
constant character. -/
theorem integral_mFourier (k : Wavevector) :
    (∫ x : Torus3, UnitAddTorus.mFourier k x) = if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 3))) (0 : Wavevector) k
  simpa only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, map_one, one_mul, mul_one, eq_comm] using h

/-- An operator kernel acts on one Fourier monomial by evaluation of its
operator-valued Fourier coefficient. -/
theorem torusOperatorKernelAction_monomial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : Torus3 → (E →L[ℂ] E)) (hK : Integrable K)
    (k : Wavevector) (v : E) (x : Torus3) :
    torusOperatorKernelAction K
        (fun z ↦ UnitAddTorus.mFourier k z • v) x =
      UnitAddTorus.mFourier k x • (UnitAddTorus.mFourierCoeff K k) v := by
  have hweighted : Integrable
      (fun y : Torus3 ↦ UnitAddTorus.mFourier (-k) y • K y) := by
    change Integrable ((fun y : Torus3 ↦
      UnitAddTorus.mFourier (-k) y) • K)
    apply hK.bdd_smul 1
    · exact (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    · filter_upwards with y
      simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
        norm_prod, Circle.norm_coe, Finset.prod_const_one, le_rfl]
  unfold torusOperatorKernelAction UnitAddTorus.mFourierCoeff
  simp_rw [mFourier_sub_apply, mul_smul, map_smul]
  rw [integral_smul]
  congr 1
  exact (ContinuousLinearMap.integral_apply hweighted v).symm

/-- A torus kernel together with the exact operator multiplier symbol carried
by its Fourier coefficients and a quantitative `L¹` mass bound. -/
structure PeriodicKernelRealization {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (symbol : Wavevector → (E →L[ℂ] E)) (mass : ℝ) where
  kernel : Torus3 → (E →L[ℂ] E)
  kernel_integrable : Integrable kernel
  kernel_continuous : Continuous kernel
  fourierCoeff_eq : ∀ k, UnitAddTorus.mFourierCoeff kernel k = symbol k
  norm_integral_le : (∫ y, ‖kernel y‖) ≤ mass

/-- Trigonometric-polynomial operator kernel associated with a finite
multiplier symbol. -/
def finiteSymbolKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E))
    (x : Torus3) : E →L[ℂ] E :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x • symbol k

theorem continuous_finiteSymbolKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E)) :
    Continuous (finiteSymbolKernel s symbol) := by
  unfold finiteSymbolKernel
  fun_prop

theorem integrable_finiteSymbolKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E)) :
    Integrable (finiteSymbolKernel s symbol) := by
  simpa only [integrableOn_univ] using
    (continuous_finiteSymbolKernel s symbol).continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (Set.univ : Set Torus3))

/-- Exact Fourier coefficients of a finite symbol kernel. -/
theorem mFourierCoeff_finiteSymbolKernel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E))
    (l : Wavevector) :
    UnitAddTorus.mFourierCoeff (finiteSymbolKernel s symbol) l =
      if l ∈ s then symbol l else 0 := by
  classical
  unfold UnitAddTorus.mFourierCoeff finiteSymbolKernel
  simp_rw [Finset.smul_sum, smul_smul, ← UnitAddTorus.mFourier_add]
  rw [integral_finsetSum s]
  · simp_rw [integral_smul_const, integral_mFourier]
    by_cases hl : l ∈ s
    · rw [if_pos hl]
      rw [Finset.sum_eq_single l]
      · simp only [neg_add_cancel, if_pos, one_smul]
      · intro k hk hne
        have hzero : -l + k ≠ 0 := by
          intro hz
          apply hne
          have hlk : l = k := by simpa only [neg_add_eq_zero] using hz
          exact hlk.symm
        rw [if_neg hzero, zero_smul]
      · exact fun hnot ↦ (hnot hl).elim
    · rw [if_neg hl]
      apply Finset.sum_eq_zero
      intro k hk
      have hzero : -l + k ≠ 0 := by
        intro hz
        apply hl
        have hlk : l = k := by simpa only [neg_add_eq_zero] using hz
        simpa only [hlk] using hk
      rw [if_neg hzero, zero_smul]
  · intro k hk
    have hm : Integrable (fun x : Torus3 ↦
        UnitAddTorus.mFourier (-l + k) x) := by
      simpa only [integrableOn_univ] using
        (UnitAddTorus.mFourier (-l + k)).continuous.continuousOn.integrableOn_compact
          (isCompact_univ : IsCompact (Set.univ : Set Torus3))
    exact hm.smul_const (symbol k)

/-- The finite symbol, extended by zero away from its retained frequencies. -/
def finiteSupportedSymbol {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E))
    (k : Wavevector) : E →L[ℂ] E :=
  if k ∈ s then symbol k else 0

/-- Actual `L¹` mass of the finite periodic operator kernel. -/
def finiteSymbolL1Mass {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E)) : ℝ :=
  ∫ x : Torus3, ‖finiteSymbolKernel s symbol x‖

/-- Every finite symbol has an exact periodic kernel realization. -/
def finiteSymbolRealization {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E)) :
    PeriodicKernelRealization (finiteSupportedSymbol s symbol)
      (finiteSymbolL1Mass s symbol) where
  kernel := finiteSymbolKernel s symbol
  kernel_integrable := integrable_finiteSymbolKernel s symbol
  kernel_continuous := continuous_finiteSymbolKernel s symbol
  fourierCoeff_eq := mFourierCoeff_finiteSymbolKernel s symbol
  norm_integral_le := le_rfl

theorem norm_finiteSymbolKernel_le_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E))
    (x : Torus3) :
    ‖finiteSymbolKernel s symbol x‖ ≤ ∑ k ∈ s, ‖symbol k‖ := by
  unfold finiteSymbolKernel
  calc
    ‖∑ k ∈ s, UnitAddTorus.mFourier k x • symbol k‖ ≤
        ∑ k ∈ s, ‖UnitAddTorus.mFourier k x • symbol k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ s, ‖symbol k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul]
      simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
        norm_prod, Circle.norm_coe, Finset.prod_const_one, one_mul]

/-- Crude but unconditional mass bound for the finite periodic realization.
Smooth localization can improve coefficient counting uniformly, but an
aperture-small bound is impossible for an unattenuated projection fixing a
unit mode; see the lower-bound theorem below. -/
theorem finiteSymbolL1Mass_le_sum_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Wavevector → (E →L[ℂ] E)) :
    finiteSymbolL1Mass s symbol ≤ ∑ k ∈ s, ‖symbol k‖ := by
  unfold finiteSymbolL1Mass
  have hleft : Integrable (fun x : Torus3 ↦
      ‖finiteSymbolKernel s symbol x‖) :=
    (integrable_finiteSymbolKernel s symbol).norm
  have hright : Integrable (fun _x : Torus3 ↦ ∑ k ∈ s, ‖symbol k‖) :=
    integrable_const _
  calc
    (∫ x : Torus3, ‖finiteSymbolKernel s symbol x‖) ≤
        ∫ _x : Torus3, ∑ k ∈ s, ‖symbol k‖ :=
      integral_mono hleft hright (norm_finiteSymbolKernel_le_sum s symbol)
    _ = ∑ k ∈ s, ‖symbol k‖ := by simp

/-- A periodic kernel realization acts exactly as its multiplier symbol on a
finite Fourier field. -/
theorem kernelAction_finiteFourier_eq_multiplier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (symbol : Wavevector → (E →L[ℂ] E)) (mass : ℝ)
    (R : PeriodicKernelRealization symbol mass)
    (s : Finset Wavevector) (coeff : Wavevector → E) (x : Torus3) :
    torusOperatorKernelAction R.kernel
        (fun z ↦ ∑ k ∈ s, UnitAddTorus.mFourier k z • coeff k) x =
      ∑ k ∈ s, UnitAddTorus.mFourier k x • symbol k (coeff k) := by
  have hint : ∀ k ∈ s, Integrable
      (fun y : Torus3 ↦ R.kernel y
        (UnitAddTorus.mFourier k (x - y) • coeff k)) := by
    intro k hk
    have hcont : Continuous
        (fun y : Torus3 ↦ R.kernel y
          (UnitAddTorus.mFourier k (x - y) • coeff k)) := by
      exact R.kernel_continuous.clm_apply (by fun_prop)
    exact (R.kernel_integrable.norm.mul_const ‖coeff k‖).mono'
      hcont.aestronglyMeasurable (by
        filter_upwards with y
        calc
          ‖R.kernel y (UnitAddTorus.mFourier k (x - y) • coeff k)‖ ≤
              ‖R.kernel y‖ * ‖UnitAddTorus.mFourier k (x - y) • coeff k‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ = ‖R.kernel y‖ * ‖coeff k‖ := by
            rw [norm_smul]
            simp only [UnitAddTorus.mFourier, fourier_apply,
              ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
              Finset.prod_const_one, one_mul])
  calc
    torusOperatorKernelAction R.kernel
        (fun z ↦ ∑ k ∈ s, UnitAddTorus.mFourier k z • coeff k) x =
        ∫ y, ∑ k ∈ s, R.kernel y
          (UnitAddTorus.mFourier k (x - y) • coeff k) := by
      unfold torusOperatorKernelAction
      congr 1
      funext y
      rw [map_sum]
    _ = ∑ k ∈ s, ∫ y, R.kernel y
          (UnitAddTorus.mFourier k (x - y) • coeff k) :=
      integral_finsetSum s hint
    _ = ∑ k ∈ s, UnitAddTorus.mFourier k x • symbol k (coeff k) := by
      apply Finset.sum_congr rfl
      intro k hk
      change torusOperatorKernelAction R.kernel
        (fun z ↦ UnitAddTorus.mFourier k z • coeff k) x = _
      rw [torusOperatorKernelAction_monomial R.kernel R.kernel_integrable,
        R.fourierCoeff_eq]

/-- The multiplier realized by a periodic kernel retains the receiver
`L∞` endpoint with the certified kernel mass. -/
theorem norm_kernelAction_le_mass {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (symbol : Wavevector → (E →L[ℂ] E)) {mass M : ℝ}
    (R : PeriodicKernelRealization symbol mass)
    (f : Torus3 → E) (x : Torus3)
    (hf : Continuous f) (hfb : ∀ y, ‖f y‖ ≤ M)
    (hmass : 0 ≤ M) :
    ‖torusOperatorKernelAction R.kernel f x‖ ≤ mass * M := by
  have hyoung := norm_torusOperatorKernelAction_le R.kernel f x M
    R.kernel_integrable R.kernel_continuous hf hfb
  exact hyoung.trans (mul_le_mul_of_nonneg_right R.norm_integral_le hmass)

/-! ## A lower bound forbidding aperture-small projection kernels -/

/-- Every operator-valued Fourier coefficient is bounded by the `L¹` mass
of its kernel. -/
theorem norm_mFourierCoeff_le_kernelL1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Torus3 → (E →L[ℂ] E)) (k : Wavevector) :
    ‖UnitAddTorus.mFourierCoeff K k‖ ≤ ∫ y, ‖K y‖ := by
  unfold UnitAddTorus.mFourierCoeff
  calc
    ‖∫ y : Torus3, UnitAddTorus.mFourier (-k) y • K y‖ ≤
        ∫ y : Torus3, ‖UnitAddTorus.mFourier (-k) y • K y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Torus3, ‖K y‖ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_smul]
      simp only [UnitAddTorus.mFourier, fourier_apply,
        ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
        Finset.prod_const_one, one_mul]

/-- If one multiplier coefficient fixes a unit vector, every exact periodic
kernel realizing it has `L¹` mass at least one.  Consequently the receiver
projection itself cannot acquire a uniform `O(delta)` endpoint norm as
`delta → 0`; any aperture gain must already be present in the bilinear
stretching symbol or another cancellation. -/
theorem one_le_kernelL1_of_fourierCoeff_fixes_unit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Torus3 → (E →L[ℂ] E)) (k : Wavevector)
    (v : E) (hv : ‖v‖ = 1)
    (hfix : (UnitAddTorus.mFourierCoeff K k) v = v) :
    1 ≤ ∫ y, ‖K y‖ := by
  have hop : 1 ≤ ‖UnitAddTorus.mFourierCoeff K k‖ := by
    have hbound := ContinuousLinearMap.le_opNorm
      (UnitAddTorus.mFourierCoeff K k) v
    rw [hfix, hv, mul_one] at hbound
    exact hbound
  exact hop.trans (norm_mFourierCoeff_le_kernelL1 K k)

/-- The same obstruction in terms of a certified periodic realization. -/
theorem one_le_realization_mass_of_symbol_fixes_unit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (symbol : Wavevector → (E →L[ℂ] E)) (mass : ℝ)
    (R : PeriodicKernelRealization symbol mass)
    (k : Wavevector) (v : E) (hv : ‖v‖ = 1)
    (hfix : symbol k v = v) :
    1 ≤ mass := by
  have hcoeff : (UnitAddTorus.mFourierCoeff R.kernel k) v = v := by
    rw [R.fourierCoeff_eq]
    exact hfix
  exact (one_le_kernelL1_of_fourierCoeff_fixes_unit
    R.kernel k v hv hcoeff).trans R.norm_integral_le

/-- Quantitative no-go form: an exact multiplier fixing a unit mode cannot
have a certified mass `C * delta < 1`. -/
theorem not_realization_mass_le_aperture_of_symbol_fixes_unit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (symbol : Wavevector → (E →L[ℂ] E)) (mass C delta : ℝ)
    (R : PeriodicKernelRealization symbol mass)
    (k : Wavevector) (v : E) (hv : ‖v‖ = 1)
    (hfix : symbol k v = v) (hsmall : C * delta < 1) :
    ¬ mass ≤ C * delta := by
  intro hmass
  have hone := one_le_realization_mass_of_symbol_fixes_unit
    symbol mass R k v hv hfix
  linarith

end PancakePeriodicOperatorKernel
end NavierStokes
end FluidDynamics
end Mettapedia
