import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous test functions determine integrable densities

Uniformly bounded continuous approximations to closed-set indicators let us
test an `L¹` density without assuming that the density itself is continuous
or square integrable.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.IntegralContinuousTest

open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {f : X → ℂ}

theorem integrable_mul (hf : Integrable f μ) (g : C(X, ℂ)) :
    Integrable (fun x ↦ g x * f x) μ :=
  hf.bdd_mul g.continuous.aestronglyMeasurable
    (Eventually.of_forall g.norm_coe_le_norm)

def pairing (hf : Integrable f μ) : C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ ∫ x, g x * f x ∂μ
      map_add' := fun g h ↦ by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_mul hf g) (integrable_mul hf h)
      map_smul' := fun c g ↦ by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
          integral_const_mul, RingHom.id_apply] }
    (∫ x, ‖f x‖ ∂μ) (fun g ↦ by
      change ‖∫ x, g x * f x ∂μ‖ ≤ _
      calc
        _ ≤ ∫ x, ‖g‖ * ‖f x‖ ∂μ :=
          norm_integral_le_of_norm_le (hf.norm.const_mul ‖g‖)
            (Eventually.of_forall (fun x ↦ by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)))
        _ = _ := by rw [integral_const_mul, mul_comm])

@[simp] theorem pairing_apply (hf : Integrable f μ) (g : C(X, ℂ)) :
    pairing hf g = ∫ x, g x * f x ∂μ := rfl

omit [CompactSpace X] in
theorem ae_eq_zero_of_integral_mul_eq_zero [HasOuterApproxClosed X] (hf : Integrable f μ)
    (h : ∀ g : C(X, ℂ), ∫ x, g x * f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf
  intro s hs
  let g : ℕ → C(X, ℂ) := fun n ↦
    ⟨fun x ↦ ((hs.apprSeq n x : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hs.apprSeq n).continuous)⟩
  have hbound (n : ℕ) (x : X) : ‖g n x‖ ≤ 1 := by
    change ‖((hs.apprSeq n x : ℝ) : ℂ)‖ ≤ 1
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hs.apprSeq n x).coe_nonneg]
      using (show (hs.apprSeq n x : ℝ) ≤ 1 from
        HasOuterApproxClosed.apprSeq_apply_le_one hs n x)
  have hlim : Tendsto (fun n ↦ ∫ x, g n x * f x ∂μ) atTop
      (𝓝 (∫ x, s.indicator f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    · intro n
      exact (g n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · exact hf.norm
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hbound n x)
    · filter_upwards with x
      have ht := tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hs) x
      have ht' := ((Complex.continuous_ofReal.tendsto _).comp
        (NNReal.continuous_coe.tendsto _ |>.comp ht)).mul_const (f x)
      by_cases hx : x ∈ s <;> simpa [g, hx] using ht'
  simp only [h, tendsto_const_nhds_iff] at hlim
  rw [← integral_indicator hs.measurableSet]
  exact hlim.symm

end Mettapedia.Analysis.IntegralContinuousTest
