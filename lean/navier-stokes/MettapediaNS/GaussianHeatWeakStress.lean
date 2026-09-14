import MettapediaNS.GaussianHeatPairing
import MettapediaNS.WholeSpaceStretchingFlux
import MettapediaNS.WholeSpaceStrain

/-!
# Actual projected weak action of the Gaussian stress

The weak action of `-div R` is `∫ R : D V`. Composing with OpenAI's actual
solenoidal projection gives the weak action of `-P div R`. Its sign, all
tensor indices, and the projected receiver's derivative are explicit.

No `L∞` boundedness of the Leray projection is asserted. The receiver is
projected first, and its actual bounded derivative norm remains on the
right-hand side. Matching this whole-space weak action to the existing
periodic Fourier nonlinear commutator is a separate representation step.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory EulerWholeSpaceGaussian EulerLpTranslation EulerOrdinarySobolev
open EulerMeanSobolevBoundedField
open EulerSmoothLimit (Space)
open scoped ENNReal

/-- Weak action of minus the stress divergence. -/
def stressAction (τ : ℝ) (u : Space → Space) (V : SmoothL2Field Space) : ℝ :=
  ∫ x, contraction τ u x (fderiv ℝ V.field x)

/-- The actual upstream Helmholtz projection is applied to the receiver. -/
def projectedStressAction (τ : ℝ) (u : Space → Space) (V : SmoothL2Field Space) : ℝ :=
  stressAction τ u (solenoidalField V)

theorem stressAction_integrable {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (V : SmoothL2Field Space) :
    Integrable (fun x => contraction τ u x (fderiv ℝ V.field x)) volume :=
  contraction_integrable hτ hu V.derivative.smooth.continuous ‖finiteField V.derivative‖
    (field_sup_bound V.derivative)

theorem projectedStressAction_integrable {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (V : SmoothL2Field Space) :
    Integrable (fun x => contraction τ u x (fderiv ℝ (solenoidalField V).field x)) volume :=
  stressAction_integrable hτ hu (solenoidalField V)

/-- The existing pancake symmetric-gradient operator is the exact receiver;
its antisymmetric derivative does not contribute to this stress action. -/
theorem stressAction_eq_strain {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (V : SmoothL2Field Space) :
    stressAction τ u V = ∫ x, contraction τ u x
      (WholeSpaceBiotSavart.strainOperator V.field x) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    (contraction_selfAdjointPart hτ hu x (fderiv ℝ V.field x)).symm)

theorem norm_stressAction_le_trace {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (V : SmoothL2Field Space) :
    ‖stressAction τ u V‖ ≤ ‖finiteField V.derivative‖ *
      (∫ x, ∑ i : Fin 3, stress τ u x i i) :=
  norm_integral_contraction_le hτ hu _ (field_sup_bound V.derivative)

/-- A potentially sharper receiver bound, with the symmetric derivative
kept explicit rather than replaced by a bound on the full gradient. -/
theorem norm_stressAction_le_of_strain_bound {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (V : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖WholeSpaceBiotSavart.strainOperator V.field x‖ ≤ K) :
    ‖stressAction τ u V‖ ≤ K * (∫ x, ∑ i : Fin 3, stress τ u x i i) := by
  rw [stressAction_eq_strain hτ hu]
  exact norm_integral_contraction_le hτ hu K hK

/-- Source energy and the actual projected receiver cost remain separate. -/
theorem norm_projectedStressAction_le_energy {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (V : SmoothL2Field Space) :
    ‖projectedStressAction τ u V‖ ≤ ‖finiteField (solenoidalField V).derivative‖ *
      (∫ x, ‖u x‖ ^ 2) :=
  (norm_stressAction_le_trace hτ hu (solenoidalField V)).trans
    (mul_le_mul_of_nonneg_left (integral_stress_trace_le_energy hτ hu) (norm_nonneg _))

/-- The heat-scale gain survives the complete projected weak tensor action. -/
theorem norm_projectedStressAction_le_derivative_energy {τ : ℝ} (hτ : 0 < τ)
    (A V : SmoothL2Field Space) :
    ‖projectedStressAction τ A.field V‖ ≤ ‖finiteField (solenoidalField V).derivative‖ *
      (((2 * τ) * (2 : ℝ) ^ (3 / 2 : ℝ)) * ‖A.derivative.toLp‖ ^ 2) :=
  (norm_stressAction_le_trace hτ A.memLp (solenoidalField V)).trans
    (mul_le_mul_of_nonneg_left (integral_stress_trace_le_derivative_energy hτ A) (norm_nonneg _))

theorem norm_projectedStressAction_le_initial
    {ν T : ℝ} {u : NavierStokesR3.ProblemStatement.VelocityField}
    {p : NavierStokesR3.ProblemStatement.PressureField} {u₀ : Space → Space}
    (s : NavierStokesR3.H3Comparison.ClassicalH3Solution ν (fun _ => 0) u₀ T u p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) {τ : ℝ} (hτ : 0 < τ)
    (V : SmoothL2Field Space) :
    ‖projectedStressAction τ (fun y => u (t, y)) V‖ ≤
      ‖finiteField (solenoidalField V).derivative‖ * NavierStokesR3.Comparison.l2Sq u₀ := by
  obtain ⟨hu, he⟩ := WholeSpaceUnforcedEnergy.classical_memLp_and_l2Sq_le_initial s hν ht
  exact (norm_projectedStressAction_le_energy hτ hu V).trans
    (mul_le_mul_of_nonneg_left he (norm_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
