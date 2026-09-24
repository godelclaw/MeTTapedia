import Mettapedia.Analysis.UnitTorusWeakDerivative
import Mettapedia.Analysis.AbsolutelyContinuousTimeWeight
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Spatial mean balance for incompressible periodic transport

The material derivative of a locally Lipschitz scalar field splits almost
everywhere into its actual time and coordinate derivatives. Incompressibility
cancels the spatial transport after integration. Absolute continuity supplies
both the endpoint balance and the signed time-weighted source identity.

All dimensions are finite but arbitrary, including product index types for
two-point observables. Neither a smooth scalar field nor a measure-preserving
flow is an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusMaterialBalance

open scoped Topology NNReal
open MeasureTheory Set
open CompactMeanDerivative UnitTorusWeakDerivative

variable {d : Type*} [Fintype d] [DecidableEq d]

local notation "T" => UnitAddTorus d
local notation "X" => d → ℝ
local notation "ST" => ℝ × X

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsAddHaarMeasure (volume : Measure ST) :=
  inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure X)))

def materialShift (v : X) (h : ℝ) : T := torusPoint (fun i ↦ h * v i)

omit [Fintype d] [DecidableEq d] in
theorem torusPoint_line (r v : X) (h : ℝ) :
    torusPoint (fun i ↦ r i + h * v i) = torusPoint r + materialShift v h := by
  ext i
  simp [torusPoint, materialShift]

def scalarMaterialRate (f : ℝ → T → ℝ) (v : T → X) (t : ℝ) (x : T) : ℝ :=
  deriv (fun h ↦ f (t + h) (x + materialShift (v x) h)) 0

theorem linear_materialDirection (L : ST →L[ℝ] ℝ) (v : X) :
    L (1, fun j ↦ v j) = L (1, 0) + ∑ j : d, L (0, Pi.single j 1) * v j := by
  have he : ((1 : ℝ), fun j : d ↦ v j) = (1, 0) +
      ∑ j : d, v j • ((0 : ℝ), Pi.single j (1 : ℝ)) := by
    apply Prod.ext
    · change 1 = 1 + (AddMonoidHom.fst ℝ X) (∑ j, v j • ((0 : ℝ), Pi.single j 1))
      rw [map_sum]
      simp
    · change v = 0 + (AddMonoidHom.snd ℝ X) (∑ j, v j • ((0 : ℝ), Pi.single j 1))
      rw [map_sum]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
  rw [he, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul, smul_eq_mul, mul_comm]

omit [DecidableEq d] in
theorem hasDerivAt_real_material_path (t : ℝ) (r : X) (v : X) :
    HasDerivAt (fun h : ℝ ↦ (t + h, fun i : d ↦ r i + h * v i))
      ((1 : ℝ), fun i : d ↦ v i) 0 := by
  apply HasDerivAt.prodMk ((hasDerivAt_id (0 : ℝ)).const_add t)
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (r i)

theorem hasDerivAt_real_coordinate_path (t : ℝ) (r : X) (j : d) :
    HasDerivAt (fun h : ℝ ↦ (t, coordinateLine r j h))
      ((0 : ℝ), Pi.single j (1 : ℝ)) 0 := by
  apply HasDerivAt.prodMk (hasDerivAt_const 0 t)
  apply hasDerivAt_pi.mpr
  intro i
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (if i = j then 1 else 0 : ℝ)).const_add (r i)
  simpa only [coordinateLine, Pi.single_apply, eq_comm, id_eq, one_mul] using hd

omit [DecidableEq d] in
theorem hasDerivAt_materialLine_of_real_fderiv
    (f : ℝ → T → ℝ) (v : T → X) (t : ℝ) (r : X)
    (hf : DifferentiableAt ℝ (fun z : ST ↦ f z.1 (torusPoint z.2)) (t, r)) :
    HasDerivAt (fun h ↦ f (t + h) (torusPoint r + materialShift (v (torusPoint r)) h))
      (fderiv ℝ (fun z : ST ↦ f z.1 (torusPoint z.2)) (t, r)
        (1, v (torusPoint r))) 0 := by
  have hF : HasFDerivAt (fun z : ST ↦ f z.1 (torusPoint z.2))
      (fderiv ℝ (fun z : ST ↦ f z.1 (torusPoint z.2)) (t, r))
      (t + 0, fun i ↦ r i + 0 * v (torusPoint r) i) := by
    simpa only [add_zero, zero_mul] using hf.hasFDerivAt
  simpa only [Function.comp_def, torusPoint_line] using
    hF.comp_hasDerivAt 0 (hasDerivAt_real_material_path t r (v (torusPoint r)))

theorem materialRate_split_of_real_fderiv
    (f : ℝ → T → ℝ) (v : T → X) (t : ℝ) (r : X)
    (hf : DifferentiableAt ℝ (fun z : ST ↦ f z.1 (torusPoint z.2)) (t, r)) :
    DifferentiableAt ℝ (fun h ↦ f h (torusPoint r)) t ∧
      scalarMaterialRate f v t (torusPoint r) = parameterRate f t (torusPoint r) +
        coordinateTransport (f t) (fun j x ↦ v x j) (torusPoint r) := by
  let F : ST → ℝ := fun z ↦ f z.1 (torusPoint z.2)
  let L := fderiv ℝ F (t, r)
  have ht : HasDerivAt (fun h : ℝ ↦ f h (torusPoint r)) (L (1, 0)) t := by
    have hp := (hasDerivAt_id t).prodMk (hasDerivAt_const t r)
    exact hf.hasFDerivAt.comp_hasDerivAt t hp
  have hc : ∀ j : d, shiftRate (f t) (coordinateShift j) (torusPoint r) = L (0, Pi.single j 1) := by
    intro j
    have hF : HasFDerivAt F L (t, coordinateLine r j 0) := by
      rw [coordinateLine_zero]
      exact hf.hasFDerivAt
    have hd := hF.comp_hasDerivAt 0 (hasDerivAt_real_coordinate_path t r j)
    simpa only [shiftRate, Function.comp_def, F, torusPoint_coordinateLine] using hd.deriv
  have hm : scalarMaterialRate f v t (torusPoint r) = L (1, fun j ↦ v (torusPoint r) j) := by
    exact (hasDerivAt_materialLine_of_real_fderiv f v t r hf).deriv
  refine ⟨ht.differentiableAt, ?_⟩
  rw [hm, linear_materialDirection]
  change L (1, 0) + _ = deriv (fun h ↦ f h (torusPoint r)) t + _
  rw [ht.deriv]
  simp only [coordinateTransport, hc]

omit [Fintype d] [DecidableEq d] in
theorem continuous_scalarMaterialFamily (f : ℝ → T → ℝ) (v : T → X)
    (hf : Continuous f.uncurry) (hv : Continuous v) (t : ℝ) :
    Continuous (fun z : T × ℝ ↦ f (t + z.2) (z.1 + materialShift (v z.1) z.2)) := by
  have hs : Continuous (fun z : T × ℝ ↦ z.1 + materialShift (v z.1) z.2) := by
    apply Continuous.add continuous_fst
    apply continuous_pi
    intro i
    change Continuous (fun z : T × ℝ ↦ ((z.2 * v z.1 i : ℝ) : UnitAddCircle))
    have hvi : Continuous (fun z : T × ℝ ↦ v z.1 i) :=
      ((continuous_apply i).comp hv).comp continuous_fst
    exact continuous_quot_mk.comp (continuous_snd.mul hvi)
  exact hf.comp ((continuous_const.add continuous_snd).prodMk hs)

omit [DecidableEq d] in
theorem measurable_scalarMaterialRate (f : ℝ → T → ℝ) (v : T → X)
    (hf : Continuous f.uncurry) (hv : Continuous v) (t : ℝ) :
    Measurable (scalarMaterialRate f v t) :=
  ((continuous_scalarMaterialFamily f v hf hv t).stronglyMeasurable_deriv_const 0).measurable

theorem measurable_coordinateTransport (f : T → ℝ) (v : d → T → ℝ)
    (hf : Continuous f) (hv : ∀ j, Measurable (v j)) : Measurable (coordinateTransport f v) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_shiftRate f (coordinateShift j) hf (continuous_coordinateShift j)).mul (hv j)

omit [DecidableEq d] in
theorem measurableSet_timeDifferentiable (f : ℝ → T → ℝ)
    (hf : Continuous f.uncurry) (t : ℝ) :
    MeasurableSet {x : T | DifferentiableAt ℝ (fun h ↦ f h x) t} := by
  have hm := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x : T ↦ fun h : ℝ ↦ f h x) (hf.comp continuous_swap)
  exact hm.preimage (show Measurable (fun x : T ↦ (x, t)) from measurable_id.prodMk measurable_const)

theorem measurableSet_materialRate_split (f : ℝ → T → ℝ) (v : T → X)
    (hf : Continuous f.uncurry) (hv : Continuous v) (t : ℝ) :
    MeasurableSet {x : T | DifferentiableAt ℝ (fun h ↦ f h x) t ∧
      scalarMaterialRate f v t x = parameterRate f t x + coordinateTransport (f t) (fun j y ↦ v y j) x} := by
  have hft : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  have hvt : ∀ j, Measurable (fun x : T ↦ v x j) := fun j ↦
    ((continuous_apply j).comp hv).measurable
  exact (measurableSet_timeDifferentiable f hf t).inter
    (measurableSet_eq_fun (measurable_scalarMaterialRate f v hf hv t)
      ((measurable_parameterRate f hf t).add (measurable_coordinateTransport (f t) _ hft hvt)))

omit [DecidableEq d] in
/-- Differentiability is retained as a conclusion, for use with nonsmooth factors. -/
theorem ae_ae_differentiableAt_materialLine (f : ℝ → T → ℝ) (v : ℝ → T → X)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2))) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T,
      DifferentiableAt ℝ (fun h ↦ f (t + h) (x + materialShift (v t x) h)) 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod (hL.ae_differentiableAt (volume : Measure ST))]
    with t ht
  apply ae_torus_of_ae_real _ (measurableSet_differentiableAt_zero _
    (continuous_scalarMaterialFamily f (v t) hf (hv t) t))
  exact ht.mono (fun r hr ↦ (hasDerivAt_materialLine_of_real_fderiv f (v t) t r hr).differentiableAt)

theorem ae_ae_materialRate_split (f : ℝ → T → ℝ) (v : ℝ → T → X)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2))) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T, DifferentiableAt ℝ (fun h ↦ f h x) t ∧
      scalarMaterialRate f (v t) t x = parameterRate f t x +
        coordinateTransport (f t) (fun j y ↦ v t y j) x := by
  have hr := hL.ae_differentiableAt (volume : Measure ST)
  have ht := Measure.ae_ae_of_ae_prod hr
  filter_upwards [ht] with t htr
  apply ae_torus_of_ae_real _ (measurableSet_materialRate_split f (v t) hf (hv t) t)
  exact htr.mono (fun r hr ↦ materialRate_split_of_real_fderiv f (v t) t r hr)

theorem ae_hasDerivAt_mean_materialRate
    (f : ℝ → T → ℝ) (v : ℝ → T → X)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2)))
    (hvL : ∀ t j, LocallyLipschitz (fun r : X ↦ v t (torusPoint r) j))
    (hdiv : ∀ t, ∀ᵐ x : T, coordinateDivergence (fun j y ↦ v t y j) x = 0) :
    ∀ᵐ t : ℝ, Integrable (scalarMaterialRate f (v t) t) ∧
      HasDerivAt (fun s ↦ ∫ x : T, f s x) (∫ x : T, scalarMaterialRate f (v t) t x) t := by
  filter_upwards [ae_ae_materialRate_split f v hf hv hfL] with t ht
  obtain ⟨C, hC⟩ := exists_uniform_time_lipschitz f hfL (Icc (t - 1) (t + 1)) isCompact_Icc
  obtain ⟨hIp, hmean⟩ := hasDerivAt_mean_of_uniform_lipschitz f hf t _
    (Icc_mem_nhds (by linarith) (by linarith)) C hC (ht.mono (fun _ hx ↦ hx.1))
  have hft : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  have hvc : ∀ j, Continuous (fun x : T ↦ v t x j) := fun j ↦
    (continuous_apply j).comp (hv t)
  have hftL : LocallyLipschitz (fun r : X ↦ f t (torusPoint r)) :=
    hfL.comp (LipschitzWith.prodMk_left t).locallyLipschitz
  obtain ⟨hIt, hzero⟩ := integral_coordinateTransport_zero (f t) _ hft hvc hftL (hvL t) (hdiv t)
  have heq : scalarMaterialRate f (v t) t =ᵐ[volume]
      (fun x ↦ parameterRate f t x + coordinateTransport (f t) (fun j y ↦ v t y j) x) :=
    ht.mono (fun _ hx ↦ hx.2)
  have hIm : Integrable (scalarMaterialRate f (v t) t) := (hIp.add hIt).congr heq.symm
  have hei : (∫ x : T, scalarMaterialRate f (v t) t x) = ∫ x : T, parameterRate f t x := by
    rw [integral_congr_ae heq, integral_add hIp hIt, hzero, add_zero]
  rw [← hei] at hmean
  exact ⟨hIm, hmean⟩

omit [DecidableEq d] in
theorem absolutelyContinuousOnInterval_mean
    (f : ℝ → T → ℝ) (hf : Continuous f.uncurry)
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2))) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x : T, f t x) a b := by
  obtain ⟨C, hC⟩ := exists_uniform_time_lipschitz f hfL (uIcc a b) isCompact_Icc
  exact (lipschitzOnWith_mean f hf _ C hC).absolutelyContinuousOnInterval

theorem intervalIntegral_materialRate_eq
    (f : ℝ → T → ℝ) (v : ℝ → T → X)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2)))
    (hvL : ∀ t j, LocallyLipschitz (fun r : X ↦ v t (torusPoint r) j))
    (hdiv : ∀ t, ∀ᵐ x : T, coordinateDivergence (fun j y ↦ v t y j) x = 0) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ ∫ x : T, scalarMaterialRate f (v t) t x) volume a b ∧
      (∫ t in a..b, ∫ x : T, scalarMaterialRate f (v t) t x) =
        (∫ x : T, f b x) - ∫ x : T, f a x := by
  have hac := absolutelyContinuousOnInterval_mean f hf hfL a b
  have heq : (fun t ↦ ∫ x : T, scalarMaterialRate f (v t) t x) =ᵐ[volume]
      deriv (fun t ↦ ∫ x : T, f t x) :=
    (ae_hasDerivAt_mean_materialRate f v hf hv hfL hvL hdiv).mono (fun _ ht ↦ ht.2.deriv.symm)
  refine ⟨hac.intervalIntegrable_deriv.congr_ae (ae_restrict_of_ae heq.symm), ?_⟩
  rw [intervalIntegral.integral_congr_ae (heq.mono (fun _ ht _ ↦ ht))]
  exact hac.integral_deriv_eq_sub

/-- The accumulated spatial mean retains the sign of the material source. -/
theorem integral_mean_eq_initial_add_weighted_materialRate
    (f : ℝ → T → ℝ) (v : ℝ → T → X)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2)))
    (hvL : ∀ t j, LocallyLipschitz (fun r : X ↦ v t (torusPoint r) j))
    (hdiv : ∀ t, ∀ᵐ x : T, coordinateDivergence (fun j y ↦ v t y j) x = 0)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ (b - t) * ∫ x : T, scalarMaterialRate f (v t) t x) volume a b ∧
      (∫ t in a..b, ∫ x : T, f t x) =
        (b - a) * (∫ x : T, f a x) +
          ∫ t in a..b, (b - t) * ∫ x : T, scalarMaterialRate f (v t) t x := by
  apply AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (absolutelyContinuousOnInterval_mean f hf hfL a b)
  exact (ae_hasDerivAt_mean_materialRate f v hf hv hfL hvL hdiv).mono
    (fun _ ht _ ↦ ht.2)

end Mettapedia.Analysis.UnitTorusMaterialBalance
