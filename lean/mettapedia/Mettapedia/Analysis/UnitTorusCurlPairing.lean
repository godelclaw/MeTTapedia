import Mettapedia.Analysis.UnitTorusContinuousRate
import Mettapedia.Analysis.WeightedCurlCancellation
import Mettapedia.Analysis.CrossProductEvolution

/-! # Self-adjoint curl pairing for actual periodic derivatives -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusCurlPairing

open scoped RealInnerProductSpace
open MeasureTheory EuclideanCrossProduct WeightedCurlCancellation UnitTorusWeakDerivative
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem divergence_cross (a b : R3) (D E : Fin 3 → R3) :
    (∑ j : Fin 3, (cross (D j) b + cross a (E j)) j) =
      ⟪curlJet D, b⟫ - ⟪a, curlJet E⟫ := by
  simp [cross, cross_apply, curlJet, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

theorem integral_inner_curl (a b : T3 → R3) (D E : Fin 3 → T3 → R3)
    (ha : Continuous a) (hb : Continuous b)
    (hD : ∀ j, Continuous (D j)) (hE : ∀ j, Continuous (E j))
    (hda : ∀ j x h, HasDerivAt (fun t ↦ a (x + coordinateShift j t)) (D j (x + coordinateShift j h)) h)
    (hdb : ∀ j x h, HasDerivAt (fun t ↦ b (x + coordinateShift j t)) (E j (x + coordinateShift j h)) h) :
    (∫ x : T3, ⟪a x, curlJet (fun j ↦ E j x)⟫) =
      ∫ x : T3, ⟪curlJet (fun j ↦ D j x), b x⟫ := by
  have hcross {f g : T3 → R3} (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ cross (f x) (g x)) := by
    exact (contDiff_cross.continuous.comp (hf.prodMk hg))
  have hc (j : Fin 3) : Continuous (fun x ↦ (cross (D j x) (b x) + cross (a x) (E j x)) j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp
      ((hcross (hD j) hb).add (hcross ha (hE j)))
  have hz (j : Fin 3) :
      (∫ x : T3, (cross (D j x) (b x) + cross (a x) (E j x)) j) = 0 := by
    apply UnitTorusContinuousRate.integral_rate_eq_zero _ _ (coordinateShift j)
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp (hcross ha hb))
      (hc j) (continuous_coordinateShift j) (coordinateShift_zero j)
    intro x h
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) j).hasFDerivAt.comp_hasDerivAt h
      (hasDerivAt_cross (hda j x h) (hdb j x h))
  have hsum : (∫ x : T3, ∑ j : Fin 3, (cross (D j x) (b x) + cross (a x) (E j x)) j) = 0 := by
    rw [integral_finsetSum _ (fun j _ ↦ (hc j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp only [hz, Finset.sum_const_zero]
  have hcurlD : Continuous (fun x ↦ curlJet (fun j ↦ D j x)) := by
    unfold curlJet
    fun_prop
  have hcurlE : Continuous (fun x ↦ curlJet (fun j ↦ E j x)) := by
    unfold curlJet
    fun_prop
  simp_rw [divergence_cross] at hsum
  rw [integral_sub ((hcurlD.inner hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((ha.inner hcurlE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hsum
  linarith only [hsum]

end Mettapedia.Analysis.UnitTorusCurlPairing
