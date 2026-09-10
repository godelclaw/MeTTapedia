import Mettapedia.Analysis.ODE.QuadraticFormBound
import Mettapedia.Analysis.ODE.AbsolutelyContinuousComparison
import Mettapedia.Analysis.ODE.VariableGronwall
import Mettapedia.Analysis.LogarithmicScaleBound
import Mettapedia.Analysis.SimpleImplicitRoot
import Mettapedia.Analysis.OperatorQuadraticForm
import Mettapedia.Analysis.IdempotentDerivatives

/-! Regression examples for the analysis estimates. -/

open Set MeasureTheory Mettapedia.Analysis Mettapedia.Analysis.ODE
open scoped ContDiff RealInnerProductSpace

-- The root -2 is simple even when the other two roots 1±x coincide.
example : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (-2 : ℝ)) 0 := by
  apply contDiffAt_of_simple_implicit_root
    (f := fun p : ℝ × ℝ ↦ ((p.2 - 1) ^ 2 - p.1 ^ 2) * (p.2 + 2)) (c := 9)
  · fun_prop
  · simp
  · fun_prop
  · exact Filter.Eventually.of_forall (fun _ ↦ by norm_num)
  · convert! (((hasDerivAt_id (-2 : ℝ)).sub_const 1).pow 2).mul
      ((hasDerivAt_id (-2 : ℝ)).add_const 2) using 1 <;> norm_num
    rfl
  · norm_num

-- The vector-gradient and mixed terms contribute: <t,t·t> = t³ has second derivative 6 at 1.
example : HasDerivAt (deriv (fun t : ℝ ↦
    OperatorQuadraticForm.value (t • ContinuousLinearMap.id ℝ ℝ) t)) 6 1 := by
  let P : ℝ → ℝ →L[ℝ] ℝ := fun t ↦ t • ContinuousLinearMap.id ℝ ℝ
  have hP : ContDiffAt ℝ 2 P 1 := by dsimp [P]; fun_prop
  have hDP : deriv P = fun _ ↦ ContinuousLinearMap.id ℝ ℝ := by
    funext t
    convert! ((hasDerivAt_id t).smul_const (ContinuousLinearMap.id ℝ ℝ)).deriv using 1
    simp only [one_smul]
  have hs : ∀ᶠ t in nhds (1 : ℝ), ∀ a b, inner ℝ (P t a) b = inner ℝ a (P t b) := by
    apply Filter.Eventually.of_forall
    intro t a b
    simp [P, mul_comm, mul_left_comm]
  have h := OperatorQuadraticForm.hasDerivAt_deriv_value hP
    (contDiffAt_id : ContDiffAt ℝ 2 (fun t : ℝ ↦ t) 1) hs
  convert! h using 1
  norm_num [hDP, P]

-- A Lipschitz path with a corner at zero: the differential equation is only
-- almost everywhere, and the derivative forcing need not be continuous.
example (a b : ℝ) (hab : a ≤ b) :
    |b| ≤ |a| + ∫ t in a..b, ‖deriv (fun τ : ℝ ↦ ‖τ‖) t‖ := by
  have hu : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ ‖t‖) a b :=
    absolutelyContinuousOnInterval_norm
      (contDiff_id.contDiffOn.absolutelyContinuousOnInterval :
        AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t) a b)
  have h := norm_le_initial_add_integral_of_ae_dissipative
    (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) hab hu hu.intervalIntegrable_deriv
    (by
      filter_upwards [hu.ae_differentiableAt] with t ht hmem
      simpa using (ht hmem).hasDerivAt)
    (by simp)
  simpa only [Real.norm_eq_abs, abs_abs] using h

-- A forced solution crosses zero inside the interval.
example : ∀ t ∈ Icc (0 : ℝ) 1, |t - 1 / 2| ≤ 1 / 2 + t := by
  have h := norm_le_initial_add_integral_of_dissipative
    (a := 0) (b := 1) (u := fun t : ℝ ↦ t - 1 / 2) (f := fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) (continuous_id.sub continuous_const).continuousOn
    continuous_const
    (fun t _ ↦ by simpa using ((hasDerivAt_id t).sub_const (1 / 2)).hasDerivWithinAt)
    (by simp)
  simpa using h

-- Variable Gronwall permits a negative growth coefficient without a sign
-- hypothesis on the compared function.
example {x x' : ℝ → ℝ} (hx : ContinuousOn x (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt x (x' t) (Icc (0 : ℝ) 1) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, x' t ≤ -x t) :
    ∀ t ∈ Icc (0 : ℝ) 1, x t ≤ x 0 * Real.exp (-t) := by
  have h := le_initial_mul_exp_integral_of_deriv_le_mul
    (g := fun _ ↦ -1) hx continuousOn_const hd (by simpa using hb)
  simpa using h

-- The scale estimate is not restricted to the source's quarter-power decay.
example {X C L W H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ C * (L + W * (-Real.log ε) + ε ^ (2 : ℝ) * H)) :
    X ≤ C * (L + W * (Real.log (Real.exp 1 + H) / 2) + 1) :=
  le_logarithmic_of_le_scale_bound hC hH (by norm_num) h

#print axioms Mettapedia.Analysis.ODE.norm_le_initial_add_integral_of_dissipative
#print axioms Mettapedia.Analysis.ODE.norm_le_initial_add_integral_of_ae_dissipative
#print axioms Mettapedia.Analysis.ODE.norm_div_le_initial_add_integral
#print axioms Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_integral_on
#print axioms Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_of_source_le
#print axioms Mettapedia.Analysis.ODE.le_initial_mul_exp_integral_of_deriv_le_mul
#print axioms Mettapedia.Analysis.exists_scale_rpow_mul_le_one
#print axioms Mettapedia.Analysis.le_logarithmic_of_le_scale_bound
#print axioms Mettapedia.Analysis.le_four_mul_logarithmic_of_le_quarter_scale_bound
