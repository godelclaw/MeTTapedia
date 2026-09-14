import Mettapedia.Analysis.UnitTorusGradientProjection

/-!
# Transport across the periodic gradient projection

For a divergence-free velocity, transport work against the gradient
part of a tensor is exactly an off-diagonal deformation pairing.
Derivatives of the tensor disappear by integration by parts; the
velocity gradient and the orthogonal residual remain.

The inputs are actual continuous translation jets. Application to a
projected field must construct its jets and prove their curl symmetry.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusGradientTransport

open scoped RealInnerProductSpace
open MeasureTheory UnitTorusWeakDerivative UnitTorusGradientProjection

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def transport (b : d → TranslationJet d ℝ) (f : TranslationJet d E) : C(T, E) :=
  ∑ k, (b k).value • f.gradient k

def deformation (b : d → TranslationJet d ℝ) (F : d → TranslationJet d E) (j : d) : C(T, E) :=
  ∑ k, (b k).gradient j • (F k).value

omit [CompleteSpace E] in
theorem inner_transport_skew (b : d → TranslationJet d ℝ) (f g : TranslationJet d E)
    (hb : ∀ x, ∑ k, (b k).gradient k x = 0) :
    (∫ x : T, ⟪f.value x, transport b g x⟫) =
      -(∫ x : T, ⟪transport b f x, g.value x⟫) := by
  simpa only [transport, ContinuousMap.sum_apply, ContinuousMap.smul_apply'] using
    UnitTorusTransportPairing.integral_inner_transport f.value g.value
      (fun k ↦ f.gradient k) (fun k ↦ g.gradient k)
      (fun k ↦ (b k).value) (fun k ↦ (b k).gradient k) coordinateShift
      f.value.continuous g.value.continuous (fun k ↦ (f.gradient k).continuous)
      (fun k ↦ (g.gradient k).continuous) (fun k ↦ (b k).value.continuous)
      (fun k ↦ ((b k).gradient k).continuous) continuous_coordinateShift coordinateShift_zero
      f.hasDerivAt g.hasDerivAt (fun k ↦ (b k).hasDerivAt k) hb

omit [CompleteSpace E] in
theorem inner_tensor_transport_skew (b : d → TranslationJet d ℝ)
    (F J : d → TranslationJet d E) (hb : ∀ x, ∑ k, (b k).gradient k x = 0) :
    ⟪toTensorL2 (fun j ↦ (F j).value), toTensorL2 (fun j ↦ transport b (J j))⟫ =
      -⟪toTensorL2 (fun j ↦ transport b (F j)), toTensorL2 (fun j ↦ (J j).value)⟫ := by
  rw [inner_toTensorL2, inner_toTensorL2]
  rw [integral_finsetSum _ (fun j _ ↦
    (((F j).value.continuous).inner (transport b (J j)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  rw [integral_finsetSum _ (fun j _ ↦
    ((transport b (F j)).continuous.inner (J j).value.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp_rw [inner_transport_skew b _ _ hb]
  rw [Finset.sum_neg_distrib]

def contractedJet (b : d → TranslationJet d ℝ) (F : d → TranslationJet d E)
    (hcurl : ∀ j k, (F k).gradient j = (F j).gradient k) : TranslationJet d E where
  value := ∑ k, (b k).value • (F k).value
  gradient j := deformation b F j + transport b (F j)
  hasDerivAt j x h := by
    have hd := HasDerivAt.sum (fun k (_ : k ∈ (Finset.univ : Finset d)) ↦
      ((b k).hasDerivAt j x h).smul ((F k).hasDerivAt j x h))
    convert! hd using 1
    · funext t
      simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply', Finset.sum_apply, Pi.smul_apply']
    · simp only [deformation, transport, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply', hcurl, Finset.sum_add_distrib]
      abel

/-- The transport work has no derivative on the tensor after the
projection residual is used against an actual gradient. -/
theorem inner_projected_transport_eq_deformation
    (b : d → TranslationJet d ℝ) (F J : d → TranslationJet d E)
    (hb : ∀ x, ∑ k, (b k).gradient k x = 0)
    (hcurl : ∀ j k, (F k).gradient j = (F j).gradient k)
    (hP : gradientProjection (toTensorL2 (fun j ↦ (J j).value)) =
      toTensorL2 (fun j ↦ (F j).value)) :
    ⟪toTensorL2 (fun j ↦ (F j).value), toTensorL2 (fun j ↦ transport b (J j))⟫ =
      ⟪toTensorL2 (deformation b F),
        toTensorL2 (fun j ↦ (J j).value) - toTensorL2 (fun j ↦ (F j).value)⟫ := by
  have hg := inner_gradient_projection (contractedJet b F hcurl)
    (toTensorL2 (fun j ↦ (J j).value))
  rw [hP] at hg
  have he : toTensorL2 (contractedJet b F hcurl).gradient =
      toTensorL2 (deformation b F) + toTensorL2 (fun j ↦ transport b (F j)) := by
    change (tensorEmbedding (d := d) (E := E)) (deformation b F + fun j ↦ transport b (F j)) = _
    exact map_add _ _ _
  rw [he, inner_add_left, inner_add_left] at hg
  have hself := inner_tensor_transport_skew b F F hb
  rw [real_inner_comm (toTensorL2 (fun j ↦ (F j).value))] at hself
  have hskew := inner_tensor_transport_skew b F J hb
  rw [real_inner_comm (toTensorL2 (fun j ↦ (F j).value))
    (toTensorL2 (fun j ↦ transport b (F j)))] at hg
  rw [inner_sub_right]
  linarith

end Mettapedia.Analysis.UnitTorusGradientTransport
