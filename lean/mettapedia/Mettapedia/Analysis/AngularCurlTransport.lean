import Mettapedia.Analysis.AngularCurlSpatialVariation
import Mettapedia.Analysis.UnitTorusDivergenceFreeTransport

/-!
# Angular transport and its deformation stress

Incompressible transport removes the scalar density flux but not the
commutator between transport and differentiation. The remaining stress
is signed and annihilates radial first-jet components. No sign or global
budget is assigned to that stress.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open MeasureTheory WeightedCurlCancellation EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def deformationStress (a : R3) (D : Fin 3 → R3) (j k : Fin 3) : ℝ :=
  ⟪jetGradient a D j, D k⟫

def deformationWork (a : R3) (D : Fin 3 → R3) (B : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3, B j k * deformationStress a D j k

theorem inner_curlJetAdjoint (a b : R3) (j : Fin 3) :
    ⟪curlJetAdjoint b j, a⟫ = cross a b j := by
  fin_cases j <;> simp [curlJetAdjoint, cross, cross_apply, PiLp.inner_apply,
    Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

theorem inner_jetGradient_value (a : R3) (D : Fin 3 → R3) (j : Fin 3) :
    ⟪jetGradient a D j, a⟫ = 0 := by
  simp only [jetGradient, inner_sub_left, real_inner_smul_left, inner_curlJetAdjoint,
    real_inner_self_eq_norm_sq]
  ring

/-- Radial derivatives cancel before taking absolute values. -/
theorem deformationStress_eq_angularJet (a : R3) (D : Fin 3 → R3) (j k : Fin 3) :
    deformationStress a D j k =
      2 * ‖a‖ ^ 2 * ⟪curlJetAdjoint (angularCurl a D) j, angularJet a D k⟫ := by
  simp only [deformationStress, jetGradient, angularJet, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, inner_curlJetAdjoint]
  ring

def transportVector (D : Fin 3 → R3) (b : Fin 3 → ℝ) : R3 := ∑ k : Fin 3, b k • D k

/-- The first index of `E` is the differentiation direction. This formula
uses commuting mixed derivatives when interpreted as a transported jet. -/
def transportJet (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3)
    (b : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (j : Fin 3) : R3 :=
  ∑ k : Fin 3, (B j k • D k + b k • E k j)

theorem transportDensityRate_eq (a : R3) (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3)
    (b : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    angularCurlDensityRate a D (transportVector D b) (transportJet D E b B) =
      (∑ k : Fin 3, b k * angularCurlDensityRate a D (D k) (E k)) + deformationWork a D B := by
  simp only [angularCurlDensityRate_eq_pairing, transportVector, transportJet,
    deformationWork, deformationStress, inner_add_right, real_inner_smul_right,
    Fin.sum_univ_three]
  ring

theorem integral_variationalGradient_transport (a : T3 → R3) (D : Fin 3 → T3 → R3)
    (E : Fin 3 → Fin 3 → T3 → R3) (b : Fin 3 → T3 → ℝ) (B : Fin 3 → Fin 3 → T3 → ℝ)
    (shift : Fin 3 → ℝ → T3)
    (ha : Continuous a) (hD : ∀ j, Continuous (D j)) (hE : ∀ j k, Continuous (E j k))
    (hb : ∀ j, Continuous (b j)) (hB : ∀ j k, Continuous (B j k))
    (hs : ∀ j, Continuous (shift j)) (hs0 : ∀ j, shift j 0 = 0)
    (hda : ∀ j x h, HasDerivAt (fun t ↦ a (x + shift j t)) (D j (x + shift j h)) h)
    (hdD : ∀ j k x h, HasDerivAt (fun t ↦ D k (x + shift j t)) (E j k (x + shift j h)) h)
    (hdb : ∀ j k x h, HasDerivAt (fun t ↦ b k (x + shift j t)) (B j k (x + shift j h)) h)
    (hcomm : ∀ j k x, E j k x = E k j x) (hdiv : ∀ x, ∑ j : Fin 3, B j j x = 0) :
    (∫ x : T3, ⟪variationalGradient (a x) (fun j ↦ D j x) (fun j k ↦ E j k x),
      transportVector (fun j ↦ D j x) (fun j ↦ b j x)⟫) =
      ∫ x : T3, deformationWork (a x) (fun j ↦ D j x) (fun j k ↦ B j k x) := by
  let f (x : T3) := transportVector (fun j ↦ D j x) (fun j ↦ b j x)
  let F (j : Fin 3) (x : T3) := transportJet (fun k ↦ D k x) (fun k l ↦ E k l x)
    (fun k ↦ b k x) (fun k l ↦ B k l x) j
  let dK (j : Fin 3) (x : T3) := angularCurlDensityRate (a x) (fun k ↦ D k x)
    (D j x) (fun k ↦ E j k x)
  have hf : Continuous f := continuous_finsetSum _ (fun k _ ↦ (hb k).smul (hD k))
  have hF (j : Fin 3) : Continuous (F j) := continuous_finsetSum _ (fun k _ ↦
    ((hB j k).smul (hD k)).add ((hb k).smul (hE k j)))
  have hdK (j : Fin 3) : Continuous (dK j) :=
    continuous_angularCurlDensityRate a (D j) D (E j) ha (hD j) hD (hE j)
  have hdf (j : Fin 3) (x : T3) (h : ℝ) :
      HasDerivAt (fun t ↦ f (x + shift j t)) (F j (x + shift j h)) h := by
    apply HasDerivAt.fun_sum
    intro k _
    have hh := (hdb j k x h).smul (hdD j k x h)
    apply hh.congr_deriv
    rw [hcomm j k]
    module
  have hvar := integral_angularCurlDensityRate_eq a f D F E shift ha hf hD hF hE hs hs0 hda hdf hdD
  have hz := UnitTorusContinuousRate.integral_sum_mul_rate_eq_zero
    (fun x ↦ angularCurlDensity (a x) (fun j ↦ D j x)) dK b (fun j ↦ B j j) shift
    (continuous_angularCurlDensity a D ha hD) hdK hb (fun j ↦ hB j j) hs hs0
    (fun j x h ↦ hasDerivAt_angularCurlDensity (hda j x h) (fun k ↦ hdD j k x h))
    (fun j ↦ hdb j j) hdiv
  have hiK : Integrable (fun x : T3 ↦ ∑ k : Fin 3, b k x * dK k x) :=
    (continuous_finsetSum _ (fun k _ ↦ (hb k).mul (hdK k))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiB : Integrable (fun x : T3 ↦ deformationWork (a x) (fun j ↦ D j x) (fun j k ↦ B j k x)) :=
    (continuous_finsetSum _ (fun j _ ↦ continuous_finsetSum _ (fun k _ ↦
      (hB j k).mul ((continuous_jetGradient a D ha hD j).inner (hD k))))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [← hvar]
  simp_rw [show ∀ x : T3, angularCurlDensityRate (a x) (fun j ↦ D j x) (f x) (fun j ↦ F j x) =
    (∑ k : Fin 3, b k x * dK k x) + deformationWork (a x) (fun j ↦ D j x) (fun j k ↦ B j k x)
    from fun x ↦ transportDensityRate_eq _ _ _ _ _]
  rw [integral_add hiK hiB, hz, zero_add]

end Mettapedia.Analysis.AngularCurlDecomposition
