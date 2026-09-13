import Mettapedia.Analysis.AngularCurlVariation
import Mettapedia.Analysis.UnitTorusContinuousRate

/-!
# Signed spatial first variation of angular curl energy

Integration by parts moves the first derivative off the varied field.
The variational gradient is the explicit polynomial in the value, first
jet and second jet. No bound on that gradient or on the source is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open MeasureTheory
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The first index of the second jet is the differentiation direction. -/
def variationalGradient (a : R3) (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3) : R3 :=
  valueGradient a D - ∑ j : Fin 3, jetGradientRate a D (D j) (E j) j

theorem continuous_variationalGradient {X : Type*} [TopologicalSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (E : Fin 3 → Fin 3 → X → R3)
    (ha : Continuous a) (hD : ∀ j, Continuous (D j)) (hE : ∀ j k, Continuous (E j k)) :
    Continuous (fun x ↦ variationalGradient (a x) (fun j ↦ D j x) (fun j k ↦ E j k x)) :=
  (continuous_valueGradient a D ha hD).sub (continuous_finsetSum _ (fun j _ ↦
    continuous_jetGradientRate a (D j) D (E j) ha (hD j) hD (hE j) j))

theorem integral_angularCurlDensityRate_eq (a f : T3 → R3)
    (D F : Fin 3 → T3 → R3) (E : Fin 3 → Fin 3 → T3 → R3)
    (shift : Fin 3 → ℝ → T3)
    (ha : Continuous a) (hf : Continuous f) (hD : ∀ j, Continuous (D j))
    (hF : ∀ j, Continuous (F j)) (hE : ∀ j k, Continuous (E j k))
    (hs : ∀ j, Continuous (shift j)) (hs0 : ∀ j, shift j 0 = 0)
    (hda : ∀ j x h, HasDerivAt (fun t ↦ a (x + shift j t)) (D j (x + shift j h)) h)
    (hdf : ∀ j x h, HasDerivAt (fun t ↦ f (x + shift j t)) (F j (x + shift j h)) h)
    (hdD : ∀ j k x h, HasDerivAt (fun t ↦ D k (x + shift j t)) (E j k (x + shift j h)) h) :
    (∫ x : T3, angularCurlDensityRate (a x) (fun j ↦ D j x) (f x) (fun j ↦ F j x)) =
      ∫ x : T3, ⟪variationalGradient (a x) (fun j ↦ D j x) (fun j k ↦ E j k x), f x⟫ := by
  let J (j : Fin 3) (x : T3) := jetGradient (a x) (fun k ↦ D k x) j
  let dJ (j : Fin 3) (x : T3) := jetGradientRate (a x) (fun k ↦ D k x) (D j x) (fun k ↦ E j k x) j
  have hJ (j : Fin 3) : Continuous (J j) := continuous_jetGradient a D ha hD j
  have hdJ (j : Fin 3) : Continuous (dJ j) :=
    continuous_jetGradientRate a (D j) D (E j) ha (hD j) hD (hE j) j
  have hi₁ (j : Fin 3) : Integrable (fun x : T3 ↦ ⟪dJ j x, f x⟫) :=
    ((hdJ j).inner hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₂ (j : Fin 3) : Integrable (fun x : T3 ↦ ⟪J j x, F j x⟫) :=
    ((hJ j).inner (hF j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb (j : Fin 3) : (∫ x : T3, ⟪J j x, F j x⟫) = -(∫ x : T3, ⟪dJ j x, f x⟫) := by
    have hz := UnitTorusContinuousRate.integral_rate_eq_zero (fun x ↦ ⟪J j x, f x⟫)
      (fun x ↦ ⟪J j x, F j x⟫ + ⟪dJ j x, f x⟫) (shift j) ((hJ j).inner hf)
      (((hJ j).inner (hF j)).add ((hdJ j).inner hf)) (hs j) (hs0 j)
      (fun x h ↦ (hasDerivAt_jetGradient (hda j x h) (fun k ↦ hdD j k x h) j).inner ℝ (hdf j x h))
    rw [integral_add (hi₂ j) (hi₁ j)] at hz
    linarith only [hz]
  have hiA : Integrable (fun x : T3 ↦ ⟪valueGradient (a x) (fun j ↦ D j x), f x⟫) :=
    ((continuous_valueGradient a D ha hD).inner hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [angularCurlDensityRate_eq_pairing, variationalGradient, inner_sub_left, sum_inner]
  rw [integral_add hiA (integrable_finsetSum _ (fun j _ ↦ hi₂ j)),
    integral_sub hiA (integrable_finsetSum _ (fun j _ ↦ hi₁ j)),
    integral_finsetSum _ (fun j _ ↦ hi₂ j), integral_finsetSum _ (fun j _ ↦ hi₁ j)]
  simp only [hb, Finset.sum_neg_distrib, sub_eq_add_neg]

end Mettapedia.Analysis.AngularCurlDecomposition
