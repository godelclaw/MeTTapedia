import Mettapedia.Analysis.ContinuousFieldInnerProduct
import Mettapedia.Analysis.UnitTorusTransportPairing
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projection onto the closed space of periodic gradients

Continuous translation jets generate a closed subspace of tensor-valued
`L²`. The orthogonal projection preserves pairing with every actual
gradient, is contractive, and annihilates divergence-free tensors.
No Fourier cutoff or cardinality factor enters the construction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusGradientProjection

open scoped RealInnerProductSpace
open MeasureTheory UnitTorusWeakDerivative

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A continuous field and its actual coordinate translation derivatives. -/
structure TranslationJet (d E : Type*) [Fintype d] [DecidableEq d]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  value : C(UnitAddTorus d, E)
  gradient : d → C(UnitAddTorus d, E)
  hasDerivAt : ∀ j x h, HasDerivAt (fun t ↦ value (x + coordinateShift j t))
    (gradient j (x + coordinateShift j h)) h

abbrev TensorL2 (d E : Type*) [Fintype d] [NormedAddCommGroup E] :=
  Lp (PiLp 2 (fun _ : d ↦ E)) 2 (volume : Measure (UnitAddTorus d))

def tensorEmbedding : (d → C(T, E)) →L[ℝ] TensorL2 d E :=
  (ContinuousMap.toLp 2 (volume : Measure T) ℝ).comp ContinuousFieldMinkowski.bundleLinear

def toTensorL2 (F : d → C(T, E)) : TensorL2 d E := tensorEmbedding (d := d) (E := E) F

omit [DecidableEq d] [CompleteSpace E] in
theorem inner_toTensorL2 (F G : d → C(T, E)) :
    ⟪toTensorL2 F, toTensorL2 G⟫ = ∫ x : T, ∑ j, ⟪F j x, G j x⟫ := by
  simp only [toTensorL2, tensorEmbedding, ContinuousLinearMap.comp_apply,
    ContinuousFieldInnerProduct.inner_toLp]
  rfl

omit [DecidableEq d] [CompleteSpace E] in
theorem norm_toTensorL2_sq (F : d → C(T, E)) :
    ‖toTensorL2 F‖ ^ 2 = ∫ x : T, ∑ j, ‖F j x‖ ^ 2 := by
  rw [toTensorL2, tensorEmbedding, ContinuousLinearMap.comp_apply, ContinuousFieldMinkowski.norm_toL2_sq]
  simp only [PiLp.norm_sq_eq_of_L2]
  rfl

def gradientSpace : ClosedSubmodule ℝ (TensorL2 d E) :=
  Submodule.closure (Submodule.span ℝ
    (Set.range (fun f : TranslationJet d E ↦ toTensorL2 f.gradient)))

def gradientProjectionCLM : TensorL2 d E →L[ℝ] TensorL2 d E :=
  (gradientSpace (d := d) (E := E)).toSubmodule.starProjection

def gradientProjection (J : TensorL2 d E) : TensorL2 d E :=
  gradientProjectionCLM (d := d) (E := E) J

omit [CompleteSpace E] in
theorem gradient_mem (f : TranslationJet d E) :
    toTensorL2 f.gradient ∈ (gradientSpace (d := d) (E := E)).toSubmodule :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)

theorem inner_gradient_projection (f : TranslationJet d E) (J : TensorL2 d E) :
    ⟪toTensorL2 f.gradient, gradientProjection J⟫ = ⟪toTensorL2 f.gradient, J⟫ := by
  have h := (gradientSpace (d := d) (E := E)).toSubmodule.starProjection_inner_eq_zero J _ (gradient_mem f)
  have hz := inner_eq_zero_symm.mp h
  rw [inner_sub_right] at hz
  exact (sub_eq_zero.mp hz).symm

theorem norm_gradientProjection_le (J : TensorL2 d E) :
    ‖gradientProjection J‖ ≤ ‖J‖ :=
  (gradientSpace (d := d) (E := E)).toSubmodule.norm_starProjection_apply_le J

theorem inner_gradientProjection_gradientProjection (J K : TensorL2 d E) :
    ⟪gradientProjection J, gradientProjection K⟫ = ⟪gradientProjection J, K⟫ := by
  have h := (gradientSpace (d := d) (E := E)).toSubmodule.starProjection_inner_eq_zero K _
    ((gradientSpace (d := d) (E := E)).toSubmodule.starProjection_apply_mem J)
  have hz := inner_eq_zero_symm.mp h
  change ⟪gradientProjection J, K - gradientProjection K⟫ = 0 at hz
  rw [inner_sub_right] at hz
  exact (sub_eq_zero.mp hz).symm

theorem norm_sq_projection_add_remainder (J : TensorL2 d E) :
    ‖gradientProjection J‖ ^ 2 + ‖J - gradientProjection J‖ ^ 2 = ‖J‖ ^ 2 := by
  have h := (gradientSpace (d := d) (E := E)).toSubmodule.sub_starProjection_mem_orthogonal J
  have hinner := Submodule.inner_right_of_mem_orthogonal
    ((gradientSpace (d := d) (E := E)).toSubmodule.starProjection_apply_mem J) h
  change ⟪gradientProjection J, J - gradientProjection J⟫ = 0 at hinner
  have he := norm_add_sq_real (gradientProjection J) (J - gradientProjection J)
  rw [show gradientProjection J + (J - gradientProjection J) = J by abel] at he
  simpa only [hinner, mul_zero, add_zero] using he.symm

omit [CompleteSpace E] in
theorem mem_orthogonal_of_pairing_zero (J : TensorL2 d E)
    (hJ : ∀ f : TranslationJet d E, ⟪toTensorL2 f.gradient, J⟫ = 0) :
    J ∈ (gradientSpace (d := d) (E := E)).toSubmoduleᗮ := by
  change J ∈ (Submodule.span ℝ (Set.range (fun f : TranslationJet d E ↦
    toTensorL2 f.gradient))).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨f, rfl⟩ := hv; exact hJ f
  | zero => exact inner_zero_left _
  | add x y hx hy hxx hyy => simp only [inner_add_left, hxx, hyy, add_zero]
  | smul c x hx hxx => simp only [real_inner_smul_left, hxx, mul_zero]

theorem gradientProjection_eq_zero_of_pairing_zero (J : TensorL2 d E)
    (hJ : ∀ f : TranslationJet d E, ⟪toTensorL2 f.gradient, J⟫ = 0) :
    gradientProjection J = 0 := by
  have hm := mem_orthogonal_of_pairing_zero J hJ
  apply (gradientSpace (d := d) (E := E)).toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.zero_mem _)
  intro w hw
  simpa only [sub_zero] using Submodule.inner_left_of_mem_orthogonal hw hm

theorem gradientProjection_sub_of_pairing_zero (J K : TensorL2 d E)
    (hK : ∀ f : TranslationJet d E, ⟪toTensorL2 f.gradient, K⟫ = 0) :
    gradientProjection (J - K) = gradientProjection J := by
  change gradientProjectionCLM (d := d) (E := E) (J - K) = _
  rw [map_sub]
  change gradientProjection J - gradientProjection K = _
  rw [gradientProjection_eq_zero_of_pairing_zero K hK, sub_zero]

theorem norm_gradientProjection_le_sub (J K : TensorL2 d E)
    (hK : ∀ f : TranslationJet d E, ⟪toTensorL2 f.gradient, K⟫ = 0) :
    ‖gradientProjection J‖ ≤ ‖J - K‖ := by
  rw [← gradientProjection_sub_of_pairing_zero J K hK]
  exact norm_gradientProjection_le _

omit [CompleteSpace E] in
theorem inner_gradient_eq_zero_of_divergence_zero (f : TranslationJet d E)
    (J dJ : d → C(T, E))
    (hdJ : ∀ j x h, HasDerivAt (fun t ↦ J j (x + coordinateShift j t))
      (dJ j (x + coordinateShift j h)) h)
    (hdiv : ∀ x, ∑ j, dJ j x = 0) :
    ⟪toTensorL2 f.gradient, toTensorL2 J⟫ = 0 := by
  have hi (j : d) : Integrable (fun x : T ↦ ⟪f.gradient j x, J j x⟫) :=
    ((f.gradient j).continuous.inner (J j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (j : d) : Integrable (fun x : T ↦ ⟪f.value x, dJ j x⟫) :=
    (f.value.continuous.inner (dJ j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (j : d) : (∫ x : T, ⟪f.gradient j x, J j x⟫) = -(∫ x : T, ⟪f.value x, dJ j x⟫) := by
    have h := UnitTorusTransportPairing.integral_inner_rate f.value (J j) (f.gradient j) (dJ j)
      (coordinateShift j) f.value.continuous (J j).continuous (f.gradient j).continuous (dJ j).continuous
      (continuous_coordinateShift j) (coordinateShift_zero j) (f.hasDerivAt j) (hdJ j)
    linarith
  rw [inner_toTensorL2, integral_finsetSum _ (fun j _ ↦ hi j)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ ↦ hj j)]
  simp only [← inner_sum, hdiv, inner_zero_right, integral_zero, neg_zero]

theorem gradientProjection_eq_zero_of_divergence_zero (J dJ : d → C(T, E))
    (hdJ : ∀ j x h, HasDerivAt (fun t ↦ J j (x + coordinateShift j t))
      (dJ j (x + coordinateShift j h)) h)
    (hdiv : ∀ x, ∑ j, dJ j x = 0) :
    gradientProjection (toTensorL2 J) = 0 :=
  gradientProjection_eq_zero_of_pairing_zero _
    (fun f ↦ inner_gradient_eq_zero_of_divergence_zero f J dJ hdJ hdiv)

end Mettapedia.Analysis.UnitTorusGradientProjection
