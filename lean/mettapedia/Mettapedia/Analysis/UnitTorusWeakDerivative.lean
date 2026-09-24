import Mettapedia.Analysis.CompactMeanDerivative
import Mettapedia.Analysis.LocallyLipschitz
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Weak differentiation on a finite-dimensional unit torus

Periodic locally Lipschitz scalar fields have integrable coordinate derivatives.
The fundamental cube transfers real Rademacher differentiability to Haar measure;
translation invariance then gives integration by parts and incompressible
transport cancellation. The index type may describe several spatial endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusWeakDerivative

open scoped Topology NNReal
open MeasureTheory Measure Filter Set
open CompactMeanDerivative

variable {d : Type*} [Fintype d] [DecidableEq d]

local notation "T" => UnitAddTorus d
local notation "X" => d → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusPoint (r : X) : T := fun i ↦ (r i : UnitAddCircle)

omit [DecidableEq d] in
theorem lipschitzWith_torusPoint : LipschitzWith 1 (torusPoint : X → T) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  rw [dist_eq_norm]
  change ‖((x i - y i : ℝ) : UnitAddCircle)‖ ≤ dist x y
  exact (QuotientAddGroup.norm_mk_le_norm).trans (by
    simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (x - y) i)

def coordinateLine (r : X) (j : d) (h : ℝ) : X :=
  fun i ↦ r i + h * if i = j then 1 else 0

def coordinateShift (j : d) (h : ℝ) : T := torusPoint (coordinateLine 0 j h)

theorem measurableSet_differentiableAt_zero
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    (f : P → ℝ → ℝ) (hf : Continuous f.uncurry) :
    MeasurableSet {p | DifferentiableAt ℝ (f p) 0} := by
  have hm := measurableSet_of_differentiableAt_with_param ℝ hf
  exact hm.preimage (show Measurable (fun p : P ↦ (p, (0 : ℝ))) from
    measurable_id.prodMk measurable_const)

omit [DecidableEq d] in
theorem measurePreserving_torusPoint :
    MeasurePreserving torusPoint
      (Measure.pi (fun _ : d ↦ (volume : Measure ℝ).restrict (Ioc 0 1)))
      (volume : Measure T) := by
  have hcircle : MeasurePreserving (fun r : ℝ ↦ (r : UnitAddCircle))
      ((volume : Measure ℝ).restrict (Ioc 0 1)) AddCircle.haarAddCircle := by
    simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
      using UnitAddCircle.measurePreserving_mk 0
  exact measurePreserving_pi _ _ (fun _ : d ↦ hcircle)

omit [DecidableEq d] in
/-- Transfer an AE statement from all real representatives to normalized
periodic Haar measure, through an explicit measured fundamental cube. -/
theorem ae_torus_of_ae_real (P : T → Prop) (hP : MeasurableSet {x | P x})
    (h : ∀ᵐ r : X, P (torusPoint r)) : ∀ᵐ x : T, P x := by
  have hc : ∀ᵐ r ∂Measure.pi (fun _ : d ↦ (volume : Measure ℝ).restrict (Ioc 0 1)),
      P (torusPoint r) := by
    rw [← Measure.restrict_pi_pi]
    exact ae_restrict_of_ae h
  rw [← measurePreserving_torusPoint.map_eq]
  exact (ae_map_iff measurePreserving_torusPoint.aemeasurable hP).mpr hc

omit [DecidableEq d] in
theorem ae_ae_torus_of_ae_real (P : ℝ → T → Prop)
    (hP : MeasurableSet {z : ℝ × T | P z.1 z.2})
    (h : ∀ᵐ z : ℝ × X, P z.1 (torusPoint z.2)) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T, P t x := by
  have hreal : ∀ᵐ t : ℝ, ∀ᵐ r : X, P t (torusPoint r) :=
    ae_ae_of_ae_prod h
  filter_upwards [hreal] with t ht
  have hinc : Measurable (fun x : T ↦ (t, x)) := measurable_const.prodMk measurable_id
  exact ae_torus_of_ae_real (P t) (hP.preimage hinc) ht

def shiftRate (f : T → ℝ) (s : ℝ → T) (x : T) : ℝ :=
  deriv (fun h ↦ f (x + s h)) 0

omit [Fintype d] [DecidableEq d] in
theorem continuous_shiftFamily (f : T → ℝ) (s : ℝ → T)
    (hf : Continuous f) (hs : Continuous s) :
    Continuous (fun z : ℝ × T ↦ f (z.2 + s z.1)) :=
  hf.comp (continuous_snd.add (hs.comp continuous_fst))

omit [DecidableEq d] in
theorem measurable_shiftRate (f : T → ℝ) (s : ℝ → T)
    (hf : Continuous f) (hs : Continuous s) : Measurable (shiftRate f s) :=
  measurable_parameterRate (fun h x ↦ f (x + s h)) (continuous_shiftFamily f s hf hs) 0

omit [DecidableEq d] in
theorem integral_shiftRate_zero (f : T → ℝ) (s : ℝ → T)
    (hf : Continuous f) (hs : Continuous s) (J : Set ℝ) (hJ : J ∈ 𝓝 (0 : ℝ)) (C : ℝ≥0)
    (hlip : ∀ x, LipschitzOnWith C (fun h ↦ f (x + s h)) J)
    (hd : ∀ᵐ x : T, DifferentiableAt ℝ (fun h ↦ f (x + s h)) 0) :
    Integrable (shiftRate f s) ∧ (∫ x : T, shiftRate f s x) = 0 := by
  obtain ⟨hi, hm⟩ := hasDerivAt_mean_of_uniform_lipschitz
    (fun h x ↦ f (x + s h)) (continuous_shiftFamily f s hf hs) 0 J hJ C hlip hd
  have he : (fun h ↦ ∫ x : T, f (x + s h)) = (fun _ : ℝ ↦ ∫ x : T, f x) := by
    funext h
    exact integral_add_right_eq_self f (s h)
  rw [he] at hm
  exact ⟨hi, hm.unique (hasDerivAt_const 0 _)⟩

omit [Fintype d] [DecidableEq d] in
theorem shiftRate_mul (f g : T → ℝ) (s : ℝ → T) (x : T) (hs0 : s 0 = 0)
    (hf : DifferentiableAt ℝ (fun h ↦ f (x + s h)) 0)
    (hg : DifferentiableAt ℝ (fun h ↦ g (x + s h)) 0) :
    shiftRate (fun y ↦ f y * g y) s x = shiftRate f s x * g x + f x * shiftRate g s x := by
  simpa only [shiftRate, hs0, add_zero] using (hf.hasDerivAt.fun_mul hg.hasDerivAt).deriv

omit [Fintype d] in
theorem continuous_coordinateShift (j : d) : Continuous (coordinateShift j) := by
  apply continuous_pi
  intro i
  change Continuous (fun h : ℝ ↦ ((coordinateLine 0 j h i : ℝ) : UnitAddCircle))
  apply continuous_quot_mk.comp
  by_cases hij : i = j
  · simp only [coordinateLine, hij, ite_true, Pi.zero_apply, zero_add, mul_one]
    fun_prop
  · simp only [coordinateLine, hij, ite_false, Pi.zero_apply, zero_add, mul_zero]
    fun_prop

omit [Fintype d] in
theorem coordinateShift_zero (j : d) : coordinateShift j 0 = 0 := by
  ext i
  by_cases hij : i = j <;> simp [coordinateShift, torusPoint, coordinateLine, hij]

omit [DecidableEq d] in
theorem torusPoint_bounded_rep (x : T) : ∃ r : X, torusPoint r = x ∧ ‖r‖ ≤ 1 := by
  let r : X := fun i ↦ (AddCircle.equivIoc 1 0 (x i)).1
  refine ⟨r, ?_, ?_⟩
  · funext i
    exact AddCircle.coe_equivIoc
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have hi := (AddCircle.equivIoc 1 0 (x i)).2
    change 0 < r i ∧ r i ≤ 0 + 1 at hi
    rw [Real.norm_eq_abs, abs_of_pos hi.1]
    simpa only [zero_add] using hi.2

omit [Fintype d] in
theorem coordinateLine_zero (r : X) (j : d) : coordinateLine r j 0 = r := by
  funext i
  simp [coordinateLine]

omit [Fintype d] in
theorem torusPoint_coordinateLine (r : X) (j : d) (h : ℝ) :
    torusPoint (coordinateLine r j h) = torusPoint r + coordinateShift j h := by
  ext i
  by_cases hij : i = j <;> simp [coordinateLine, torusPoint, coordinateShift, hij]

theorem lipschitzWith_coordinateLine (r : X) (j : d) :
    LipschitzWith 1 (coordinateLine r j) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  by_cases hij : i = j
  · simp [coordinateLine, hij]
  · simp [coordinateLine, hij, dist_nonneg]

theorem norm_coordinateLine_le (r : X) (j : d) (h : ℝ) :
    ‖coordinateLine r j h‖ ≤ ‖r‖ + |h| := by
  have hd := (lipschitzWith_coordinateLine r j).dist_le_mul h 0
  simp only [NNReal.coe_one, one_mul, coordinateLine_zero, Real.dist_eq, sub_zero] at hd
  have hn := dist_triangle (coordinateLine r j h) r 0
  rw [dist_zero_right, dist_zero_right] at hn
  linarith

omit [DecidableEq d] in
theorem exists_uniform_time_lipschitz (f : ℝ → T → ℝ)
    (hf : LocallyLipschitz (fun z : ℝ × X ↦ f z.1 (torusPoint z.2)))
    (J : Set ℝ) (hJ : IsCompact J) :
    ∃ C, ∀ x : T, LipschitzOnWith C (fun t ↦ f t x) J := by
  obtain ⟨C, hC⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hJ.prod (isCompact_closedBall (0 : X) 1))
  refine ⟨C, fun x ↦ ?_⟩
  obtain ⟨r, hr, hnr⟩ := torusPoint_bounded_rep x
  have hrB : r ∈ Metric.closedBall (0 : X) 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hnr
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have h := hC.dist_le_mul (a, r) ⟨ha, hrB⟩ (b, r) ⟨hb, hrB⟩
  simpa only [hr, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem exists_uniform_coordinate_lipschitz (f : T → ℝ)
    (hf : LocallyLipschitz (fun r : X ↦ f (torusPoint r))) :
    ∃ C, ∀ j : d, ∀ x : T,
      LipschitzOnWith C (fun h ↦ f (x + coordinateShift j h)) (Icc (-1) 1) := by
  obtain ⟨C, hC⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : X) 2)
  refine ⟨C, fun j x ↦ ?_⟩
  obtain ⟨r, hr, hnr⟩ := torusPoint_bounded_rep x
  have hmaps : MapsTo (coordinateLine r j) (Icc (-1) 1) (Metric.closedBall (0 : X) 2) := by
    intro h hh
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnh : |h| ≤ 1 := abs_le.mpr hh
    exact (norm_coordinateLine_le r j h).trans (by linarith)
  have h := hC.comp (lipschitzWith_coordinateLine r j).lipschitzOnWith hmaps
  simpa only [mul_one, Function.comp_def, torusPoint_coordinateLine, hr] using h

theorem ae_coordinate_differentiable (f : T → ℝ) (j : d)
    (hf : Continuous f) (hL : LocallyLipschitz (fun r : X ↦ f (torusPoint r))) :
    ∀ᵐ x : T, DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0 := by
  have hm := measurableSet_differentiableAt_zero
    (fun x : T ↦ fun h : ℝ ↦ f (x + coordinateShift j h))
    ((continuous_shiftFamily f (coordinateShift j) hf (continuous_coordinateShift j)).comp continuous_swap)
  apply ae_torus_of_ae_real _ hm
  have hreal := hL.ae_differentiableAt (volume : Measure X)
  filter_upwards [hreal] with r hr
  have hp : DifferentiableAt ℝ (coordinateLine r j) 0 := by
    change DifferentiableAt ℝ (fun h : ℝ ↦ fun i : d ↦ r i + h * if i = j then 1 else 0) 0
    fun_prop
  have hr' : DifferentiableAt ℝ (fun r : X ↦ f (torusPoint r)) (coordinateLine r j 0) := by
    rw [coordinateLine_zero]
    exact hr
  simpa only [Function.comp_def, torusPoint_coordinateLine] using hr'.comp 0 hp

theorem integral_coordinateRate_zero (f : T → ℝ) (j : d)
    (hf : Continuous f) (hL : LocallyLipschitz (fun r : X ↦ f (torusPoint r))) :
    Integrable (shiftRate f (coordinateShift j)) ∧
      (∫ x : T, shiftRate f (coordinateShift j) x) = 0 := by
  obtain ⟨C, hC⟩ := exists_uniform_coordinate_lipschitz f hL
  exact integral_shiftRate_zero f (coordinateShift j) hf (continuous_coordinateShift j)
    (Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num)) C (hC j)
    (ae_coordinate_differentiable f j hf hL)

omit [DecidableEq d] in
theorem integrable_mul_continuous (f g : T → ℝ) (hf : Integrable f) (hg : Continuous g) :
    Integrable (fun x ↦ f x * g x) := by
  rw [← integrableOn_univ] at hf ⊢
  exact hf.mul_continuousOn hg.continuousOn isCompact_univ

theorem integral_coordinateRate_mul (f g : T → ℝ) (j : d)
    (hf : Continuous f) (hg : Continuous g)
    (hfL : LocallyLipschitz (fun r : X ↦ f (torusPoint r)))
    (hgL : LocallyLipschitz (fun r : X ↦ g (torusPoint r))) :
    (∫ x : T, shiftRate f (coordinateShift j) x * g x) =
      -(∫ x : T, f x * shiftRate g (coordinateShift j) x) := by
  have hprodL := hfL.mul_algebra hgL
  have hzero := (integral_coordinateRate_zero (fun x ↦ f x * g x) j (hf.mul hg) hprodL).2
  have hif := integrable_mul_continuous _ g (integral_coordinateRate_zero f j hf hfL).1 hg
  have hig : Integrable (fun x ↦ f x * shiftRate g (coordinateShift j) x) := by
    simpa only [mul_comm] using integrable_mul_continuous _ f (integral_coordinateRate_zero g j hg hgL).1 hf
  have heq : (∫ x : T, shiftRate (fun y ↦ f y * g y) (coordinateShift j) x) =
      ∫ x : T, shiftRate f (coordinateShift j) x * g x + f x * shiftRate g (coordinateShift j) x := by
    apply integral_congr_ae
    filter_upwards [ae_coordinate_differentiable f j hf hfL, ae_coordinate_differentiable g j hg hgL]
      with x hfx hgx
    exact shiftRate_mul f g (coordinateShift j) x (coordinateShift_zero j) hfx hgx
  rw [heq, integral_add hif hig] at hzero
  linarith

def coordinateTransport (f : T → ℝ) (v : d → T → ℝ) (x : T) : ℝ :=
  ∑ j : d, shiftRate f (coordinateShift j) x * v j x

def coordinateDivergence (v : d → T → ℝ) (x : T) : ℝ :=
  ∑ j : d, shiftRate (v j) (coordinateShift j) x

theorem integral_coordinateTransport_zero
    (f : T → ℝ) (v : d → T → ℝ)
    (hf : Continuous f) (hv : ∀ j, Continuous (v j))
    (hfL : LocallyLipschitz (fun r : X ↦ f (torusPoint r)))
    (hvL : ∀ j, LocallyLipschitz (fun r : X ↦ v j (torusPoint r)))
    (hdiv : ∀ᵐ x : T, coordinateDivergence v x = 0) :
    Integrable (coordinateTransport f v) ∧ (∫ x : T, coordinateTransport f v x) = 0 := by
  have hA : ∀ j : d, Integrable (fun x : T ↦ shiftRate f (coordinateShift j) x * v j x) :=
    fun j ↦ integrable_mul_continuous _ _ (integral_coordinateRate_zero f j hf hfL).1 (hv j)
  have hB : ∀ j : d, Integrable (fun x : T ↦ f x * shiftRate (v j) (coordinateShift j) x) := by
    intro j
    simpa only [mul_comm] using
      integrable_mul_continuous _ f (integral_coordinateRate_zero (v j) j (hv j) (hvL j)).1 hf
  refine ⟨integrable_finsetSum Finset.univ (fun j _ ↦ hA j), ?_⟩
  unfold coordinateTransport
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hA j)]
  simp_rw [integral_coordinateRate_mul f (v _) _ hf (hv _) hfL (hvL _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun j _ ↦ hB j)]
  have he : (∫ x : T, ∑ j : d, f x * shiftRate (v j) (coordinateShift j) x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hdiv] with x hx
    rw [← Finset.mul_sum]
    change f x * coordinateDivergence v x = 0
    rw [hx, mul_zero]
  rw [he, neg_zero]

end Mettapedia.Analysis.UnitTorusWeakDerivative
