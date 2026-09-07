import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicLipschitz

/-!
# Weak periodic derivatives of locally Lipschitz scalar fields

Real Rademacher differentiability is transferred through the measured
fundamental cube. The resulting coordinate derivatives are integrable
and have zero mean. Product differentiation gives periodic integration
by parts without assuming the scalar field is C¹.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicWeakDerivative

open scoped Topology NNReal
open MeasureTheory Filter Set
open PancakeHaarTransportRate PancakePeriodicLipschitz PancakeLocallyLipschitzEnergy
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeFourierTranslationCurve
open PancakeAEMaterialRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ae_differentiableAt_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [Measure.IsAddHaarMeasure mu]
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    ∀ᵐ z ∂mu, DifferentiableAt ℝ f z := by
  have hball : ∀ n : ℕ, ∀ᵐ z ∂mu, z ∈ Metric.ball (0 : E) (n + 1 : ℝ) →
      DifferentiableAt ℝ f z := by
    intro n
    obtain ⟨C, hC⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : E) (n + 1 : ℝ))
    filter_upwards [hC.ae_differentiableWithinAt_of_mem (μ := mu)] with z hz hzb
    exact (hz (Metric.ball_subset_closedBall hzb)).differentiableAt
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hzb) Metric.ball_subset_closedBall)
  filter_upwards [ae_all_iff.mpr hball] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  apply hz n
  simpa only [Metric.mem_ball, dist_zero_right] using hn.trans (by norm_num : (n : ℝ) < n + 1)

theorem ae_coordinate_differentiable (f : T3 → ℝ) (j : Fin 3)
    (hf : Continuous f) (hL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    ∀ᵐ x : T3, DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0 := by
  have hm := measurableSet_differentiableAt_zero
    (fun x : T3 ↦ fun h : ℝ ↦ f (x + coordinateShift j h))
    ((continuous_shiftFamily f (coordinateShift j) hf (continuous_coordinateShift j)).comp continuous_swap)
  apply ae_torus_of_ae_real _ hm
  have hreal := ae_differentiableAt_locallyLipschitz (volume : Measure X3) _ hL
  filter_upwards [hreal] with r hr
  have hp : DifferentiableAt ℝ (coordinateLine r j) 0 := by
    change DifferentiableAt ℝ (fun h : ℝ ↦ fun i : Fin 3 ↦ r i + h * if i = j then 1 else 0) 0
    fun_prop
  have hr' : DifferentiableAt ℝ (fun r : X3 ↦ f (torusPoint r)) (coordinateLine r j 0) := by
    rw [coordinateLine_zero]
    exact hr
  simpa only [Function.comp_def, torusPoint_coordinateLine] using hr'.comp 0 hp

theorem integral_coordinateRate_zero (f : T3 → ℝ) (j : Fin 3)
    (hf : Continuous f) (hL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    Integrable (shiftRate f (coordinateShift j)) ∧
      (∫ x : T3, shiftRate f (coordinateShift j) x) = 0 := by
  obtain ⟨C, hC⟩ := exists_uniform_coordinate_lipschitz f hL
  exact integral_shiftRate_zero f (coordinateShift j) hf (continuous_coordinateShift j)
    (Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num)) C (hC j)
    (ae_coordinate_differentiable f j hf hL)

theorem integrable_mul_continuous (f g : T3 → ℝ) (hf : Integrable f) (hg : Continuous g) :
    Integrable (fun x ↦ f x * g x) := by
  rw [← integrableOn_univ] at hf ⊢
  exact hf.mul_continuousOn hg.continuousOn isCompact_univ

theorem integral_coordinateRate_mul (f g : T3 → ℝ) (j : Fin 3)
    (hf : Continuous f) (hg : Continuous g)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r))) :
    (∫ x : T3, shiftRate f (coordinateShift j) x * g x) =
      -(∫ x : T3, f x * shiftRate g (coordinateShift j) x) := by
  have hprodL := locallyLipschitz_mul_real _ _ hfL hgL
  have hzero := (integral_coordinateRate_zero (fun x ↦ f x * g x) j (hf.mul hg) hprodL).2
  have hif := integrable_mul_continuous _ g (integral_coordinateRate_zero f j hf hfL).1 hg
  have hig : Integrable (fun x ↦ f x * shiftRate g (coordinateShift j) x) := by
    simpa only [mul_comm] using integrable_mul_continuous _ f (integral_coordinateRate_zero g j hg hgL).1 hf
  have heq : (∫ x : T3, shiftRate (fun y ↦ f y * g y) (coordinateShift j) x) =
      ∫ x : T3, shiftRate f (coordinateShift j) x * g x + f x * shiftRate g (coordinateShift j) x := by
    apply integral_congr_ae
    filter_upwards [ae_coordinate_differentiable f j hf hfL, ae_coordinate_differentiable g j hg hgL]
      with x hfx hgx
    exact shiftRate_mul f g (coordinateShift j) x (coordinateShift_zero j) hfx hgx
  rw [heq, integral_add hif hig] at hzero
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicWeakDerivative
