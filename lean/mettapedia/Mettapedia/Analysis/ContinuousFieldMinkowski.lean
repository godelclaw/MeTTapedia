import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Minkowski's integral inequality for continuous fields

An integrable family of continuous fields on a compact measured space can
be integrated before or after its continuous linear inclusion into `L²`.
The norm triangle inequality then controls the spatial `L²` norm of the
integrated field by the integral of its spatial norms. A finite family is
bundled with the `ℓ²` norm, so this step has no cardinality multiplier.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ContinuousFieldMinkowski

open MeasureTheory

variable {A X E : Type*} [MeasurableSpace A]
variable [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (ν : Measure X) [IsFiniteMeasure ν] {μ : Measure A}

omit [T2Space X] [CompleteSpace E] in
theorem norm_toL2_sq (f : C(X, E)) :
    ‖f.toLp 2 ν ℝ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℝ) ν] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

omit [T2Space X] [CompleteSpace E] in
theorem norm_toL2 (f : C(X, E)) :
    ‖f.toLp 2 ν ℝ‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂ν) := by
  rw [← norm_toL2_sq, Real.sqrt_sq (norm_nonneg _)]

omit [T2Space X] in
theorem integral_spatial_norm_le (f : A → C(X, E)) (hf : Integrable f μ) :
    Real.sqrt (∫ x, ‖∫ a, f a x ∂μ‖ ^ 2 ∂ν) ≤
      ∫ a, Real.sqrt (∫ x, ‖f a x‖ ^ 2 ∂ν) ∂μ := by
  have he (x : X) := ContinuousMap.integral_apply hf x
  calc
    _ = ‖(ContinuousMap.toLp 2 ν ℝ) (∫ a, f a ∂μ)‖ := by
      rw [norm_toL2]
      simp only [he]
    _ = ‖∫ a, (f a).toLp 2 ν ℝ ∂μ‖ := by
      rw [(ContinuousMap.toLp 2 ν ℝ).integral_comp_comm hf]
    _ ≤ ∫ a, ‖(f a).toLp 2 ν ℝ‖ ∂μ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_toL2]

variable {ι : Type*} [Fintype ι]

def bundle (f : ι → C(X, E)) : C(X, PiLp 2 (fun _ : ι ↦ E)) :=
  ⟨fun x ↦ WithLp.toLp 2 (fun i ↦ f i x),
    (PiLp.continuous_toLp 2 (fun _ : ι ↦ E)).comp (continuous_pi (fun i ↦ (f i).continuous))⟩

def bundleLinear : (ι → C(X, E)) →L[ℝ] C(X, PiLp 2 (fun _ : ι ↦ E)) where
  toFun := bundle
  map_add' f g := by ext x i; rfl
  map_smul' c f := by ext x i; rfl
  cont := by
    apply ContinuousMap.continuous_of_continuous_uncurry _
    apply (PiLp.continuous_toLp 2 (fun _ : ι ↦ E)).comp
    apply continuous_pi
    intro i
    exact continuous_eval.comp
      (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)

omit [T2Space X] in
theorem integral_finite_spatial_norm_le (f : A → ι → C(X, E))
    (hf : ∀ i, Integrable (fun a ↦ f a i) μ) :
    Real.sqrt (∫ x, ∑ i, ‖∫ a, f a i x ∂μ‖ ^ 2 ∂ν) ≤
      ∫ a, Real.sqrt (∫ x, ∑ i, ‖f a i x‖ ^ 2 ∂ν) ∂μ := by
  have hi : Integrable (fun a ↦ bundle (f a)) μ :=
    bundleLinear.integrable_comp (integrable_pi_iff.mpr hf)
  have h := integral_spatial_norm_le ν (fun a ↦ bundle (f a)) hi
  have he (x : X) (i : ι) : (∫ a, bundle (f a) x ∂μ) i = ∫ a, f a i x ∂μ := by
    rw [← ContinuousMap.integral_apply hi x]
    have hp : (∫ a, bundle (f a) ∂μ) = bundle (fun i ↦ ∫ a, f a i ∂μ) := by
      change (∫ a, bundleLinear (f a) ∂μ) = bundleLinear (fun i ↦ ∫ a, f a i ∂μ)
      rw [bundleLinear.integral_comp_comm (integrable_pi_iff.mpr hf)]
      congr 1
      exact funext (eval_integral hf)
    rw [hp]
    exact ContinuousMap.integral_apply (hf i) x
  simp only [PiLp.norm_sq_eq_of_L2] at h
  simp_rw [he] at h
  exact h

omit [T2Space X] [CompleteSpace E] in
theorem norm_bundle_toL2 (f : ι → C(X, E)) :
    ‖(bundle f).toLp 2 ν ℝ‖ = Real.sqrt (∫ x, ∑ i, ‖f i x‖ ^ 2 ∂ν) := by
  simp only [norm_toL2, PiLp.norm_sq_eq_of_L2, bundle, ContinuousMap.coe_mk]

omit [T2Space X] [CompleteSpace E] in
/-- The spatial norm of a convergent field series is bounded by the sum of
its spatial norms, with all finite components kept in one Hilbert norm. -/
theorem hasSum_finite_spatial_norm_le {J : Type*} (f : J → ι → C(X, E))
    (g : ι → C(X, E)) (hf : ∀ i, HasSum (fun n ↦ f n i) (g i))
    (hs : Summable (fun n ↦ Real.sqrt (∫ x, ∑ i, ‖f n i x‖ ^ 2 ∂ν))) :
    Real.sqrt (∫ x, ∑ i, ‖g i x‖ ^ 2 ∂ν) ≤
      ∑' n, Real.sqrt (∫ x, ∑ i, ‖f n i x‖ ^ 2 ∂ν) := by
  have hp : HasSum f g := Pi.hasSum.mpr hf
  have hb := (ContinuousMap.toLp 2 ν ℝ).hasSum (bundleLinear.hasSum hp)
  have hn (n : J) : ‖(bundle (f n)).toLp 2 ν ℝ‖ ≤
      Real.sqrt (∫ x, ∑ i, ‖f n i x‖ ^ 2 ∂ν) := (norm_bundle_toL2 ν (f n)).le
  have h := hb.norm_le_of_bounded hs.hasSum hn
  simpa only [bundleLinear, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, norm_bundle_toL2] using h

end Mettapedia.Analysis.ContinuousFieldMinkowski
