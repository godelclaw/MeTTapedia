import Mettapedia.Analysis.UnitTorusPairIntegration

/-!
# Endpoint dependence in periodic kernel correlations

Integrating a separation-only operator against a fixed endpoint vector
retains just its mean. A mean-zero kernel therefore requires receiver
dependence to produce a nontrivial quadratic correlation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusKernelCorrelation

open MeasureTheory
open scoped RealInnerProductSpace
variable {d : Type*} [Fintype d]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_quadratic_eq_mean (K : T → E →L[ℝ] E) (hK : Continuous K) (x : T) (a : E) :
    (∫ y : T, ⟪a, K (x - y) a⟫) = ⟪a, (∫ h : T, K h) a⟫ := by
  rw [integral_sub_left_eq_self (fun h : T ↦ ⟪a, K h a⟫) volume x]
  have hi : Integrable K := hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hia : Integrable (fun h : T ↦ K h a) :=
    (hK.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := (innerSL ℝ a).integral_comp_comm hia
  simpa only [innerSL_apply_apply, ContinuousLinearMap.integral_apply hi] using he

theorem integral_weighted_quadratic_eq_increment (K : T → E →L[ℝ] E) (hK : Continuous K)
    (hmean : (∫ h : T, K h) = 0) (w : T → ℝ) (hw : Continuous w) (x : T) (a : E) :
    (∫ y : T, w y * ⟪a, K (x - y) a⟫) =
      ∫ y : T, (w y - w x) * ⟪a, K (x - y) a⟫ := by
  have hq : Continuous (fun y : T ↦ ⟪a, K (x - y) a⟫) :=
    continuous_const.inner ((hK.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)
  have hi : Integrable (fun y : T ↦ w y * ⟪a, K (x - y) a⟫) :=
    (hw.mul hq).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqi : Integrable (fun y : T ↦ ⟪a, K (x - y) a⟫) :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [sub_mul]
  rw [integral_sub hi (hqi.const_mul _), integral_const_mul,
    integral_quadratic_eq_mean K hK x a, hmean]
  simp

end Mettapedia.Analysis.UnitTorusKernelCorrelation
