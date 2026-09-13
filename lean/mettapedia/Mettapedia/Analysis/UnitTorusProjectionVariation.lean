import Mettapedia.Analysis.WeightedProjectionVariation
import Mettapedia.Analysis.UnitTorusCurlPairing

/-!
# Variational source work of a curl-coupled projection energy

Periodic curl integration by parts moves the derivative off an additional
source. The resulting signed pairing is exact, not a bound for that source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusProjectionVariation

open scoped RealInnerProductSpace
open MeasureTheory WeightedProjectionVariation WeightedProjectionParabolic WeightedCurlCancellation
open UnitTorusWeakDerivative
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def variationalGradient (δ : ℝ) (a b : R3) (D E : Fin 3 → R3) : R3 :=
  firstGradient δ a b + curlJet (fun j ↦ secondGradientRate δ a b (D j) (E j))

theorem continuous_variationalGradient (δ : ℝ) (hδ : 0 < δ)
    {a b : T3 → R3} {D E : Fin 3 → T3 → R3}
    (ha : Continuous a) (hb : Continuous b) (hD : ∀ j, Continuous (D j)) (hE : ∀ j, Continuous (E j)) :
    Continuous (fun x ↦ variationalGradient δ (a x) (b x) (fun j ↦ D j x) (fun j ↦ E j x)) := by
  have hc := fun j ↦ continuous_secondGradientRate δ hδ ha hb (hD j) (hE j)
  have hfirst := continuous_firstGradient δ hδ ha hb
  unfold variationalGradient curlJet
  fun_prop

theorem integral_weightedRate_eq (δ : ℝ) (hδ : 0 < δ)
    (a b f : T3 → R3) (D E F : Fin 3 → T3 → R3)
    (ha : Continuous a) (hb : Continuous b) (hf : Continuous f)
    (hD : ∀ j, Continuous (D j)) (hE : ∀ j, Continuous (E j)) (hF : ∀ j, Continuous (F j))
    (hda : ∀ j x h, HasDerivAt (fun t ↦ a (x + coordinateShift j t)) (D j (x + coordinateShift j h)) h)
    (hdb : ∀ j x h, HasDerivAt (fun t ↦ b (x + coordinateShift j t)) (E j (x + coordinateShift j h)) h)
    (hdf : ∀ j x h, HasDerivAt (fun t ↦ f (x + coordinateShift j t)) (F j (x + coordinateShift j h)) h) :
    (∫ x : T3, weightedRate δ (a x) (b x) (f x) (curlJet (fun j ↦ F j x))) =
      ∫ x : T3, ⟪variationalGradient δ (a x) (b x) (fun j ↦ D j x) (fun j ↦ E j x), f x⟫ := by
  have hcB := continuous_secondGradient δ hδ ha hb
  have hcD := fun j ↦ continuous_secondGradientRate δ hδ ha hb (hD j) (hE j)
  have hi := UnitTorusCurlPairing.integral_inner_curl
    (fun x ↦ secondGradient δ (a x) (b x)) f
    (fun j x ↦ secondGradientRate δ (a x) (b x) (D j x) (E j x)) F
    hcB hf hcD hF (fun j x h ↦ hasDerivAt_secondGradient δ hδ (hda j x h) (hdb j x h)) hdf
  have hcF : Continuous (fun x ↦ curlJet (fun j ↦ F j x)) := by unfold curlJet; fun_prop
  have hcG : Continuous (fun x ↦ curlJet (fun j ↦ secondGradientRate δ (a x) (b x) (D j x) (E j x))) := by
    unfold curlJet
    fun_prop
  have hA : Integrable (fun x ↦ ⟪firstGradient δ (a x) (b x), f x⟫) :=
    ((continuous_firstGradient δ hδ ha hb).inner hf).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun x ↦ ⟪secondGradient δ (a x) (b x), curlJet (fun j ↦ F j x)⟫) :=
    (hcB.inner hcF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (fun x ↦ ⟪curlJet (fun j ↦ secondGradientRate δ (a x) (b x) (D j x) (E j x)), f x⟫) :=
    (hcG.inner hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [weightedRate_eq, variationalGradient, inner_add_left]
  rw [integral_add hA hB, integral_add hA hG, hi]

end Mettapedia.Analysis.UnitTorusProjectionVariation
