import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocallyLipschitzEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHaarTransportRate

/-!
# Uniform parameter bounds from bounded periodic representatives

Every torus point has a real representative of sup norm at most one.
Compactness of bounded real spacetime sets supplies uniform Lipschitz
constants for time sections and coordinate translations of periodic fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicLipschitz

open scoped Topology NNReal
open Set
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeFourierTranslationCurve
open PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem torusPoint_bounded_rep (x : T3) : ∃ r : X3, torusPoint r = x ∧ ‖r‖ ≤ 1 := by
  let r : X3 := fun i ↦ (AddCircle.equivIoc 1 0 (x i)).1
  refine ⟨r, ?_, ?_⟩
  · funext i
    exact AddCircle.coe_equivIoc
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have hi := (AddCircle.equivIoc 1 0 (x i)).2
    change 0 < r i ∧ r i ≤ 0 + 1 at hi
    rw [Real.norm_eq_abs, abs_of_pos hi.1]
    simpa only [zero_add] using hi.2

theorem coordinateLine_zero (r : X3) (j : Fin 3) : coordinateLine r j 0 = r := by
  funext i
  simp [coordinateLine]

theorem torusPoint_coordinateLine (r : X3) (j : Fin 3) (h : ℝ) :
    torusPoint (coordinateLine r j h) = torusPoint r + coordinateShift j h := by
  ext i
  by_cases hij : i = j <;> simp [coordinateLine, torusPoint, coordinateShift, hij]

theorem lipschitzWith_coordinateLine (r : X3) (j : Fin 3) :
    LipschitzWith 1 (coordinateLine r j) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  by_cases hij : i = j
  · simp [coordinateLine, hij]
  · simp [coordinateLine, hij, dist_nonneg]

theorem norm_coordinateLine_le (r : X3) (j : Fin 3) (h : ℝ) :
    ‖coordinateLine r j h‖ ≤ ‖r‖ + |h| := by
  have hd := (lipschitzWith_coordinateLine r j).dist_le_mul h 0
  simp only [NNReal.coe_one, one_mul, coordinateLine_zero, Real.dist_eq, sub_zero] at hd
  have hn := dist_triangle (coordinateLine r j h) r 0
  rw [dist_zero_right, dist_zero_right] at hn
  linarith

theorem exists_uniform_time_lipschitz (f : ℝ → T3 → ℝ)
    (hf : LocallyLipschitz (fun z : ℝ × X3 ↦ f z.1 (torusPoint z.2)))
    (J : Set ℝ) (hJ : IsCompact J) :
    ∃ C, ∀ x : T3, LipschitzOnWith C (fun t ↦ f t x) J := by
  obtain ⟨C, hC⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hJ.prod (isCompact_closedBall (0 : X3) 1))
  refine ⟨C, fun x ↦ ?_⟩
  obtain ⟨r, hr, hnr⟩ := torusPoint_bounded_rep x
  have hrB : r ∈ Metric.closedBall (0 : X3) 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hnr
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have h := hC.dist_le_mul (a, r) ⟨ha, hrB⟩ (b, r) ⟨hb, hrB⟩
  simpa only [hr, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem exists_uniform_coordinate_lipschitz (f : T3 → ℝ)
    (hf : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    ∃ C, ∀ j : Fin 3, ∀ x : T3,
      LipschitzOnWith C (fun h ↦ f (x + coordinateShift j h)) (Icc (-1) 1) := by
  obtain ⟨C, hC⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : X3) 2)
  refine ⟨C, fun j x ↦ ?_⟩
  obtain ⟨r, hr, hnr⟩ := torusPoint_bounded_rep x
  have hmaps : MapsTo (coordinateLine r j) (Icc (-1) 1) (Metric.closedBall (0 : X3) 2) := by
    intro h hh
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnh : |h| ≤ 1 := abs_le.mpr hh
    exact (norm_coordinateLine_le r j h).trans (by linarith)
  have h := hC.comp (lipschitzWith_coordinateLine r j).lipschitzOnWith hmaps
  simpa only [mul_one, Function.comp_def, torusPoint_coordinateLine, hr] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicLipschitz
