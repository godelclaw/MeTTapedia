import NavierStokes.R3.H3CandidateUniqueness
import MettapediaNS.PressureLocalizationDifference

/-!
# Initial kinetic energy as a pressure-localization resource

The unforced energy inequality is a specialization of the upstream weak-H³
energy theorem. Its pressure cancellation is also imported, with no pressure
normalization or compact support assumed. The resulting initial-energy bound
pays the actual velocity-tensor source in the second pressure difference.

The solution is the upstream ordinary H³ solution of the actual PDE on its
given lifespan. This file does not construct or extend that lifespan, and
does not pay the first pressure commutator or the adaptive test/cutoff norms.
-/

noncomputable section

open Set MeasureTheory
open NavierStokesR3.ProblemStatement NavierStokesR3.H3Comparison
open NavierStokesR3.Comparison
open NavierStokes.ProblemStatement (pressureGradient)
open scoped ENNReal InnerProductSpace

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceUnforcedEnergy

/-- Reuse the full upstream difference-energy estimate with transported
field and transport velocity both equal to `u`, and zero deformation term. -/
theorem energy_rate_nonpos {ν T : ℝ} {u : VelocityField} {p : PressureField}
    (s : StrongSolutionOnIcc ν (fun _ => 0) 0 T u p) (hν : 0 ≤ ν)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    2 * (∫ x, ⟪u (t, x), s.timeDerivative (t, x)⟫_ℝ) ≤ 0 := by
  let hw := s.curve.approximation t (Ioo_subset_Icc_self ht)
  have hc := s.curve.spatial_continuous t (Ioo_subset_Icc_self ht)
  have hpg := s.pressureGradient_memLp ht MemLp.zero'
  have hp := integral_inner_pressureGradient_zero hw.toH1Approximation
    (s.divergence_free t ht) (s.pressure_C1 t ht) hpg
  have he : ∀ᵐ x ∂volume, s.timeDerivative (t, x) =
      ν • (∑ i : Fin 3, s.curve.second i i (t, x)) -
        (0 : Space →L[ℝ] Space) (u (t, x)) -
        (∑ i : Fin 3, u (t, x) i • s.curve.first i (t, x)) - pressureGradient p t x := by
    filter_upwards [s.navier_stokes t ht] with x hx
    simp only [weakAdvection, weakLaplacian] at hx
    simp only [_root_.zero_apply, sub_zero]
    apply eq_of_sub_eq_zero
    calc
      _ = s.timeDerivative (t, x) + (∑ i : Fin 3, u (t, x) i • s.curve.first i (t, x)) -
          ν • (∑ i : Fin 3, s.curve.second i i (t, x)) + pressureGradient p t x := by module
      _ = 0 := hx
  have hb := difference_rate_le (G := 0) hw hw hc hc hpg hν (fun _ => 0)
    aestronglyMeasurable_const (fun _ => by simp)
    (s.divergence_free t ht) hp he
  simpa only [mul_zero, zero_mul] using hb

/-- The actual whole-space energy is bounded by its initial value on the
entire closed slab. No energy inequality is assumed in the solution class. -/
theorem l2Sq_le_initial {ν T : ℝ} {u : VelocityField} {p : PressureField}
    (s : StrongSolutionOnIcc ν (fun _ => 0) 0 T u p) (hν : 0 ≤ ν)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    l2Sq (fun x => u (t, x)) ≤ l2Sq (fun x => u (0, x)) := by
  let E : ℝ → ℝ := fun r => ‖s.curve.velocityLp r‖ ^ 2 - ‖s.curve.velocityLp 0‖ ^ 2
  have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) T) :
      HasDerivAt E (2 * ∫ x, ⟪u (r, x), s.timeDerivative (r, x)⟫_ℝ) r := by
    have hh := ((s.hasDerivAt_velocity r hr).norm_sq).sub_const (‖s.curve.velocityLp 0‖ ^ 2)
    rw [s.curve.velocityLp_eq (Ioo_subset_Icc_self hr), inner_toLp] at hh
    exact hh
  have hb := NavierStokesR3.ComparisonGronwall.le_exp_mul_of_deriv_le
    (K := 0) (ε := 0) s.time_lt.le le_rfl le_rfl
    ((s.curve.continuousOn_velocityLp.norm.pow 2).sub continuousOn_const)
    (by simp) hd (fun r hr => by
      simpa only [zero_mul, zero_add] using energy_rate_nonpos s hν hr) t ht
  have hn : ‖s.curve.velocityLp t‖ ^ 2 ≤ ‖s.curve.velocityLp 0‖ ^ 2 := by
    simpa only [Pi.sub_apply, Pi.pow_apply, zero_mul, Real.exp_zero, mul_one, sub_nonpos] using hb
  rw [s.curve.velocityLp_eq ht, s.curve.velocityLp_eq ⟨le_rfl, s.time_lt.le⟩,
    ← integral_norm_sq_eq_toLp, ← integral_norm_sq_eq_toLp] at hn
  exact hn

/-- One initial-energy bound works on every shorter interval of the actual
unforced H³ lifespan, with no dependence on the endpoint of that interval. -/
theorem classical_memLp_and_l2Sq_le_initial {ν T : ℝ} {u : VelocityField}
    {p : PressureField} {u₀ : Space → Space}
    (s : ClassicalH3Solution ν (fun _ => 0) u₀ T u p) (hν : 0 ≤ ν)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    MemLp (fun x => u (t, x)) 2 volume ∧ l2Sq (fun x => u (t, x)) ≤ l2Sq u₀ := by
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  let hS := s.on_shorter_interval S ⟨lt_of_le_of_lt ht.1 htS, hST⟩
  have htt : t ∈ Icc (0 : ℝ) S := ⟨ht.1, htS.le⟩
  refine ⟨(hS.curve.approximation t htt).memLp, ?_⟩
  have hi : (fun x => u (0, x)) = u₀ := funext s.initial_velocity
  simpa only [hi] using l2Sq_le_initial hS hν htt

/-- The second pressure difference is paid by the actual unforced initial
kinetic energy. The cutoff parameters and the test norm remain explicit. -/
theorem norm_secondPressureDifference_le_initial {ν T : ℝ} {u : VelocityField}
    {p : PressureField} {u₀ : Space → Space}
    (s : ClassicalH3Solution ν (fun _ => 0) u₀ T u p) (hν : 0 ≤ ν)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i j : Fin 3)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    ‖PressureLocalizationDifference.secondDifference i j φ
      (fun x => u (t, x) i * u (t, x) j) ψ ψh ψhh‖ ≤
      (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * l2Sq u₀ * comparisonLpNorm 2 (fun x => ψ x) := by
  obtain ⟨hu, he⟩ := classical_memLp_and_l2Sq_le_initial s hν ht
  have hC : 0 ≤ (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
      comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
      R ^ (-(3 / 2) : ℝ) := by
    apply mul_nonneg _ (Real.rpow_nonneg hR.le _)
    exact mul_nonneg (mul_nonneg heatKernelTimeConstant_pos.le (sq_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  exact (PressureLocalizationDifference.norm_secondDifference_velocityTensor_le i j
    hR hφm hφ hLip hu ψ ψh ψhh hψh hψhh).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC) ENNReal.toReal_nonneg)

/-- All nine tensor components of the canonical pressure are included.
The factor nine is the fixed spatial dimension, not a localization count. -/
theorem norm_sum_secondPressureDifference_le_initial {ν T : ℝ} {u : VelocityField}
    {p : PressureField} {u₀ : Space → Space}
    (s : ClassicalH3Solution ν (fun _ => 0) u₀ T u p) (hν : 0 ≤ ν)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh ψhh : ComplexTest)
    (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψhh : ∀ x, ψhh x = φ x ^ 2 • ψh x) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, PressureLocalizationDifference.secondDifference i j φ
      (fun x => u (t, x) i * u (t, x) j) ψ ψh ψhh‖ ≤
      9 * (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * l2Sq u₀ * comparisonLpNorm 2 (fun x => ψ x) := by
  let B := (heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
    comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
    R ^ (-(3 / 2) : ℝ) * l2Sq u₀ * comparisonLpNorm 2 (fun x => ψ x)
  have hb (i j : Fin 3) : ‖PressureLocalizationDifference.secondDifference i j φ
      (fun x => u (t, x) i * u (t, x) j) ψ ψh ψhh‖ ≤ B :=
    norm_secondPressureDifference_le_initial s hν ht i j hR hφm hφ hLip ψ ψh ψhh hψh hψhh
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, PressureLocalizationDifference.secondDifference i j φ
        (fun x => u (t, x) i * u (t, x) j) ψ ψh ψhh‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, B := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hb i j))
    _ = _ := by simp only [Fin.sum_univ_three]; dsimp [B]; ring

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceUnforcedEnergy
