import MettapediaNS.WholeSpacePressureRecovery
import NavierStokes.R3.PressureFlux

/-!
# Imported cutoff flux estimate for the constructed pressure

The Helmholtz pressure is identified with the upstream canonical flux using
the proved compact-test identity. The full cutoff estimate is then a direct
application of OpenAI's pressure-flux theorem. Constants are uniform in the
cutoff radius, not in arbitrary physical-time trajectories.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureRecovery

open MeasureTheory EulerLpTranslation EulerOrdinarySobolev
  EulerLpTranslation.SmoothL2Field WholeSpaceViscousEnergy
open EulerSmoothLimit (divergence divergence_eq_coordinate_sum)
open NavierStokes.ProblemStatement
open NavierStokesR3 Comparison PressureRecovery PressureFluxIdentity
open scoped ContDiff ENNReal

/-- The upstream Sobolev square estimate supplies the cubic integrability
needed by the imported pressure-flux theorem. -/
theorem memLp_three_field (A : SmoothL2Field Space) : MemLp A.field 3 := by
  have hs := square_memLp A.memLp (memLp_six A.field A.smooth A.memLp A.derivative.memLp)
  have hi := A.memLp.norm.integrable_mul hs
  have hc : MemLp (fun x ↦ ‖A.field x‖ ^ 3) 1 := by
    apply memLp_one_iff_integrable.mpr
    convert hi using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have h := (memLp_norm_rpow_iff (p := (3 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
    A.memLp.aestronglyMeasurable (by norm_num) (by norm_num)).mp
  rw [ENNReal.div_self (by norm_num) (by norm_num)] at h
  norm_num at h
  exact h hc

/-- The complete compact pressure flux identity is the upstream integration-
by-parts theorem applied to the constructed pressure gradient. -/
theorem integral_pressurePotential_flux_eq_rieszPair (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (χ : Space → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    (∫ x, pressurePotential A x * fderiv ℝ χ x (A.field x)) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (fun x ↦ A.field x i * A.field x j)
          (realTest (fun x ↦ fderiv ℝ χ x (A.field x))
            (fluxFunction_smooth hχ A.smooth) (fluxFunction_hasCompactSupport hcχ A.field))).re := by
  apply pressure_flux_eq_of_gradient_identification (g := fun i j x ↦ A.field x i * A.field x j)
    (pressurePotential_spec A).1 hχ A.smooth hcχ
    (fun i j ↦ (componentField A i).memLp.integrable_mul (componentField A j).memLp)
  · intro x
    exact (divergence_eq_coordinate_sum A.field x).symm.trans (hdiv x)
  · intro k ψ hψ hcψ
    simpa only [partialD, pressurePotential_partial, Complex.ofReal_re, Complex.neg_re] using
      congrArg Complex.re (integral_pressureField_mul_eq_rieszPair A hdiv ψ hψ hcψ k)

set_option backward.isDefEq.respectTransparency.types false in
theorem integral_pressurePotential_flux_eq_canonicalCutoffFlux (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) {R : ℝ} (hR : 0 < R) :
    (∫ x, pressurePotential A x * fderiv ℝ (ComparisonCutoffs.weight R) x (A.field x)) =
      (PressureFlux.canonicalCutoffFlux R hR (fun z ↦ A.field z.2) (fun _ ↦ 0) 0
        A.smooth contDiff_const).re := by
  have ht : tensorDiff (fun z ↦ A.field z.2) (fun _ ↦ 0) 0 =
      (fun i j x ↦ A.field x i * A.field x j) := by
    funext i j x
    simp [tensorDiff]
  unfold PressureFlux.canonicalCutoffFlux PressureFlux.canonicalFlux
  rw [ht]
  simp only [← Pi.zero_def, sub_zero]
  exact integral_pressurePotential_flux_eq_rieszPair A hdiv (ComparisonCutoffs.weight R)
    (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR)

/-- The complete upstream local-plus-commutator bound, now for the actual
constructed scalar pressure. No uniform-in-time norm bound is inferred. -/
theorem exists_uniform_cutoff_pressureFlux_bound (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      |∫ x, pressurePotential A x * fderiv ℝ (ComparisonCutoffs.weight R) x (A.field x)| ≤
        C * ((cutoffL6 (ComparisonCutoffs.cutoff R) (fun z ↦ A.field z.2) 0 ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (fun z ↦ A.field z.2) 0 / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (fun z ↦ A.field z.2) 0 ^ (3 / 4 : ℝ)) := by
  have hg (i j : Fin 3) : Integrable (tensorDiff (fun z ↦ A.field z.2) (fun _ ↦ 0) 0 i j) :=
    tensorDiff_integrable A.memLp MemLp.zero' i j
  have hG (i j : Fin 3) :
      comparisonLpNorm 1 (tensorDiff (fun z ↦ A.field z.2) (fun _ ↦ 0) 0 i j) ≤ l2Sq A.field := by
    rw [LpNormTools.lpNorm_one_eq_integral_norm (hg i j)]
    simpa only [l2Sq, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero, add_zero] using
      tensorDiff_norm_integral_le (u := fun z ↦ A.field z.2) (v := fun _ ↦ 0) (t := 0)
        A.memLp MemLp.zero' i j
  obtain ⟨C, hC, hb⟩ := PressureFlux.exists_uniform_canonicalCutoffFlux_bound
    (comparisonLpNorm 2 A.field) (comparisonLpNorm 3 A.field) (l2Sq A.field)
    (LpNormTools.lpNorm_nonneg _ _) (LpNormTools.lpNorm_nonneg _ _)
    (integral_nonneg (fun _ ↦ sq_nonneg _))
  refine ⟨C, hC, fun R hR ↦ ?_⟩
  rw [integral_pressurePotential_flux_eq_canonicalCutoffFlux A hdiv (zero_lt_one.trans_le hR)]
  refine (Complex.abs_re_le_norm _).trans ?_
  simpa only [← Pi.zero_def, Pi.sub_apply, sub_zero] using
    hb R hR (fun z ↦ A.field z.2) (fun _ ↦ 0) 0 A.smooth contDiff_const
      (by simpa only [Pi.sub_apply, sub_zero] using A.memLp)
      (memLp_three_field A) hg (by simp only [Pi.sub_apply, sub_zero]; exact le_rfl) le_rfl hG

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureRecovery
